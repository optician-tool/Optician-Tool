open Core.Std
open Util1

(* Interfaces and implementations of dictionaries.  A dictionary
 * is used to associate a value with a key.  In our case, we will
 * be using a dictionary to build an index for the web, associating
 * a set of URLs with each word that we find as we crawl the web.
 *)
module type DICT = 
sig
  type key   
  type value 
  type dict

  (* An empty dictionary *)
  val empty : dict 

  (* Reduce the dictionary using the provided function f and base case u. 
   * Our reducing function f must have the type:
   *      key -> value -> 'a -> 'a
   * and our base case u has type 'a.
   * 
   * If our dictionary is the (key,value) pairs (in any order)
   *      (k1,v1), (k2,v2), (k3,v3), ... (kn,vn)
   * then fold should return:
   *      f k1 v1 (f k2 v2 (f k3 v3 (f ... (f kn vn u))))
   *)
  val fold : (key -> value -> 'a -> 'a) -> 'a -> dict -> 'a

  (* Returns as an option the value associated with the provided key. If
   * the key is not in the dictionary, return None. *)
  val lookup : dict -> key -> value option

  val lookup_exn : dict -> key -> value

  (* Returns true if and only if the key is in the dictionary. *)
  val member : dict -> key -> bool

  (* Inserts a (key,value) pair into our dictionary. If the key is already
   * in our dictionary, update the key to have the new value. *)
  val insert : dict -> key -> value -> dict

  (* Removes the given key from the dictionary. If the key is not present,
   * return the original dictionary. *)
  val remove : dict -> key -> dict

  (* Return an arbitrary key, value pair along with a new dict with that
   * pair removed. Return None if the input dict is empty *)
  val choose : dict -> (key * value * dict) option

  val compare : dict -> dict -> comparison

  val is_empty : dict -> bool

  val as_kvp_list : dict -> (key * value) list
  val from_kvp_list : (key * value) list -> dict

  (* functions to convert our types to strings for debugging and logging *)
  val to_string : dict -> string
end



(* Argument module signature to our DICT functors *)
module type DICT_ARG =
sig
  type key
  type value
  val compare_key : key -> key -> comparison
  val compare_value : value -> value -> comparison
  val key_to_string : key -> string
  val value_to_string : value -> string
end
(******************************************************************)
(* BTDict: a functor that implements our DICT signature           *)
(* using a balanced tree (2-3 trees)                              *)
(******************************************************************)
module BTDict(D:DICT_ARG) : (DICT with type key = D.key
with type value = D.value) =
struct
  type key = D.key
  type value = D.value

  (* A dictionary entry is a (key,value) pair. We compare two (key,value)
   * pairs with the provided key-comparison function D.compare. For example,
   * we may choose to keep a dictionary mapping links to their ranks. In this
   * case, our (key,value) pairs will be (link,rank) pairs, and we compare
   * links using string comparison. *)
  type pair = key * value

  (* Type definition for dictionary, which we choose to represent as a 2-3 Tree.
   * This is almost the same as the binary search tree definition from pset4 and
   * lecture, except we add one more case: a Three-node. 
   *
   * A Three-node contains two pairs and three subtrees: left, middle, and 
   * right, represented by the 3 dicts in the definition below. *)
  type dict = 
    | Leaf
    | Two of dict * pair * dict
    | Three of dict * pair * dict * pair * dict

  (* INVARIANTS: 
   * 2-node: Two(left,(k1,v1),right) 
   * (1) Every key k appearing in subtree left must be k < k1.
   * (2) Every key k appearing in subtree right must be k > k1. 
   * (3) The length of the path from the 2-node to
   *     every leaf in its two subtrees must be the same.  
   * 
   * 3-node: Three(left,(k1,v1),middle,(k2,v2),right) 
   * (1) k1 < k2.
   * (2) Every key k appearing in subtree left must be k < k1. 
   * (3) Every key k appearing in subtree right must be k > k2. 
   * (4) Every key k appearing in subtree middle must be k1 < k < k2.
   * (5) The length of the path from the 3-node to every leaf in its three 
   *     subtrees must be the same. 
   *)

  (* FOR INSERTION:
   * A kicked configuration returned by going downwards on insertion.
   * We can only kick up Two nodes, hence Up takes a dict * pair * dict *)
  type kicked =
    | Up of dict * pair * dict
    | Done of dict

  (* FOR REMOVAL:
   * A hole configuration returned by going downwards on removal. We
   * include a pair option whenever we remove the minimum of the right
   * subtree of the current pair in order the current pair *)
  type hole =
    | Hole of pair option * dict
    | Absorbed of pair option * dict

  (* FOR REMOVAL:
   * A direction will distinguish which configuration we came from in the
   * removal cases. We use direction2 for cases (1-2) on the handout, and
   * we use direction3 for cases (3-4) on the handout. *)
  type direction2 =
    | Left2
    | Right2

  type direction3 =
    | Left3
    | Mid3
    | Right3
        
  (* TODO:
   * How do we represent an empty dictionary with 2-3 trees? *)
  let empty : dict = Leaf

  (* TODO:
   * Implement fold. Read the specification in the DICT signature above. *)
  let rec fold (f: key -> value -> 'a -> 'a) (u: 'a) (d: dict) : 'a =
    match d with
      | Leaf -> u
      | Two(left,(k1,v1),right) ->
        f k1 v1 (fold f (fold f u left) right)
      | Three(left,(k1,v1),middle,(k2,v2),right) ->
        f k1 v1 
          (f k2 v2 
             (fold f 
                (fold f 
                   (fold f u left) middle) right))

  (* TODO:
   * Implement these to-string functions *)
  let string_of_key = D.key_to_string
  let string_of_value = D.value_to_string
  let to_string (d: dict) : string = 
    fold (fun k v rest -> 
      (string_of_key k) ^ " -> " ^ (string_of_value v) ^ "\n" ^ rest) 
      "" d

  (* Upward phase for w where its parent is a Two node whose (key,value) is x.
   * One of x's children is w, and the other child is x_other. This function
   * should return a kicked-up configuration containing the new tree as a
   * result of performing the upward phase on w. *)
  let insert_upward_two (w: pair) (w_left: dict) (w_right: dict) 
      (x: pair) (x_other: dict) : kicked = 
    let (w_key,_) = w in
    let (x_key,_) = x in
    match D.compare_key w_key x_key with
      | EQ -> Done(Two(w_left,w,w_right))
      | LT -> Done(Three(w_left,w,w_right,x,x_other))
      | GT -> Done(Three(x_other,x,w_left,w,w_right))

  (* Upward phase for w where its parent is a Three node whose (key,value) is x.
   * One of x's children is w, and of the two remaining children, 
   * other_left is the subtree more to the left and other_right is the 
   * subtree more to the right. 
   *
   * E.g. From our handout, for the first case where w's parent is a Three-tree,
   * other_left would be c and other_right would be d. For the second case,
   * other_left would be a and other_right would be d. For the third case,
   * other_left would be a and other_right would be b. 
   *
   * This function should return a kicked-up configuration containing the 
   * new tree as a result of performing the upward phase on w. *)
  let insert_upward_three (w: pair) (w_left: dict) (w_right: dict)
      (x: pair) (y: pair) (other_left: dict) (other_right: dict) : kicked =
    let (w_key,_) = w in
    let (x_key,_) = x in
    let (y_key,_) = y in
    match D.compare_key w_key x_key, D.compare_key w_key y_key with
      | EQ, _ -> Done(Three(w_left,x,other_left,y,other_right))
      | _, EQ -> Done(Three(w_left,x,other_left,y,other_right))
      | LT, _ -> 
        let left = Two(w_left,w,w_right) in
        let right = Two(other_left,y,other_right) in
        Up(left,x,right)
      | _, GT -> 
        let left = Two(other_left,x,other_right) in
        let right = Two(w_left,w,w_right) in
        Up(left,y,right)
      | GT, LT -> 
        let left = Two(other_left,x,w_left) in
        let right = Two(w_right,y,other_right) in
        Up(left,w,right)

  (* Downward phase for inserting (k,v) into our dictionary d. 
   * The downward phase returns a "kicked" up configuration, where
   * 
   * type kicked =
   *      | Up of dict * pair * dict
   *      | Done of dict
   * 
   * A kicked up configuration can only be a Two node, hence the Up
   * constructor takes the same parameters as the Two constructor. We return
   * Up(left,(k,v),right) if the Two-node represented by this Up needs to
   * be further kicked up in the upward phase (this is represented by an up
   * arrow on the 2-3 Tree handout). We return Done(d) if we have finished
   * our upward phase on the tree represented by d. 
   *
   * The functions insert_downward, insert_downward_two, and 
   * insert_downward_three are __mutually recursive__, hence the 
   * "let rec" and the "and" keywords. Here, we use three mutually recursive
   * functions to simplify our code into smaller pieces.
   *
   * Two functions f and g are __mutually recursive__ if in f's definition, 
   * f calls g, and in g's definition, g calls f. This definition of
   * mutually recursive definitions can be extended to more than two functions,
   * as follows: 
   * 
   * Functions f1, f2, f3, ..., fn are mutually recursive if for each of
   * these functions f, all of the other f_i's can be called on some execution 
   * of f. *)

  (* insert_downward should handle the base case when inserting into a Leaf,
   * and if our dictionary d is a Two-node or a Three-node, we call the 
   * corresponding functions insert_downward_two or insert_downward_three
   * with the appropriate arguments. *)
  let rec insert_downward (d: dict) (k: key) (v: value) : kicked =
    match d with
      | Leaf -> Up(Leaf,(k,v),Leaf)
      | Two(left,n,right) -> 
        insert_downward_two (k,v) n left right
      | Three(left,n1,middle,n2,right) -> 
        insert_downward_three (k,v) n1 n2 left middle right

  (* Downward phase on a Two node. (k,v) is the (key,value) we are inserting,
   * (k1,v1) is the (key,value) of the current Two node, and left and right
   * are the two subtrees of the current Two node. *)
  and insert_downward_two ((k,v): pair) ((k1,v1): pair) 
      (left: dict) (right: dict) : kicked = 
    match D.compare_key k k1 with
      | EQ -> Done(Two(left,(k1,v),right))
      | LT ->
        (match insert_downward left k v with
          | Up(l_kick,w,r_kick) -> 
            insert_upward_two w l_kick r_kick (k1,v1) right
          | Done new_left -> Done(Two(new_left,(k1,v1),right))
        )
      | GT ->
        (match insert_downward right k v with
          | Up(l_kick,w,r_kick) -> 
            insert_upward_two w l_kick r_kick (k1,v1) left
          | Done new_right -> Done(Two(left,(k1,v1),new_right))
        )

  (* Downward phase on a Three node. (k,v) is the (key,value) we are inserting,
   * (k1,v1) and (k2,v2) are the two (key,value) pairs in our Three node, and
   * left, middle, and right are the three subtrees of our current Three node *)
  and insert_downward_three ((k,v): pair) ((k1,v1): pair) ((k2,v2): pair) 
      (left: dict) (middle: dict) (right: dict) : kicked =
    match D.compare_key k k1, D.compare_key k k2 with
      | EQ, _ -> Done(Three(left,(k1,v),middle,(k2,v2),right))
      | _, EQ -> Done(Three(left,(k1,v1),middle,(k2,v),right))
      | LT, _ -> 
        (match insert_downward left k v with
          | Up(l_kick,w,r_kick) ->
            insert_upward_three w l_kick r_kick (k1,v1) (k2,v2) middle right
          | Done new_left -> Done(Three(new_left,(k1,v1),middle,(k2,v2),right))
        )
      | _, GT ->
        (match insert_downward right k v with
          | Up(l_kick,w,r_kick) ->
            insert_upward_three w l_kick r_kick (k1,v1) (k2,v2) left middle
          | Done new_right -> Done(Three(left,(k1,v1),middle,(k2,v2),new_right))
        )
      | GT, LT ->
        (match insert_downward middle k v with
          | Up(l_kick,w,r_kick) ->
            insert_upward_three w l_kick r_kick (k1,v1) (k2,v2) left right
          | Done new_mid -> Done(Three(left,(k1,v1),new_mid,(k2,v2),right))
        )   

  (* We insert (k,v) into our dict using insert_downward, which gives us
   * "kicked" up configuration. We return the tree contained in the "kicked"
   * configuration. *)
  let insert (d: dict) (k: key) (v: value) : dict =
    match insert_downward d k v with
      | Up(l,(k1,v1),r) -> Two(l,(k1,v1),r)
      | Done x -> x

  (* Upward phase for removal where the parent of the hole is a Two node. 
   * See cases (1-2) on the handout. n is the (key,value) pair contained in
   * the parent node; left and right are the subtrees of the parent node (our
   * hole is one of these subtrees); and dir indicates which subtree was
   * contained by the hole. *)
  let remove_upward_two (n: pair) (rem: pair option) 
      (left: dict) (right: dict) (dir: direction2) : hole =
    match dir,n,left,right with
      | Left2,x,l,Two(m,y,r) -> Hole(rem,Three(l,x,m,y,r))
      | Right2,y,Two(l,x,m),r -> Hole(rem,Three(l,x,m,y,r))
      | Left2,x,a,Three(b,y,c,z,d) -> Absorbed(rem,Two(Two(a,x,b),y,Two(c,z,d)))
      | Right2,z,Three(a,x,b,y,c),d -> Absorbed(rem,Two(Two(a,x,b),y,Two(c,z,d)))
      | Left2,_,_,_ | Right2,_,_,_ -> Absorbed(rem,Two(Leaf,n,Leaf))

  (* Upward phase for removal where the parent of the hole is a Three node.
   * See cases (3-4) on the handout. n1 and n2 are the (key,value) pairs
   * contained in the parent node; left, middle, and right are the subtrees
   * of the parent node (our hole is one of these subtrees); and dir indicates
   * which subtree was the tree contained by the hole. *)
  let remove_upward_three (n1: pair) (n2: pair) (rem: pair option)
      (left: dict) (middle: dict) (right: dict) (dir: direction3) : hole =
    match dir,n1,n2,left,middle,right with
      | Left3,x,z,a,Two(b,y,c),d -> Absorbed(rem,Two(Three(a,x,b,y,c),z,d))
      | Mid3,y,z,Two(a,x,b),c,d -> Absorbed(rem,Two(Three(a,x,b,y,c),z,d))
      | Mid3,x,y,a,b,Two(c,z,d) -> Absorbed(rem,Two(a,x,Three(b,y,c,z,d)))
      | Right3,x,z,a,Two(b,y,c),d -> Absorbed(rem,Two(a,x,Three(b,y,c,z,d)))
      | Left3,w,z,a,Three(b,x,c,y,d),e -> 
        Absorbed(rem,Three(Two(a,w,b),x,Two(c,y,d),z,e))
      | Mid3,y,z,Three(a,w,b,x,c),d,e -> 
        Absorbed(rem,Three(Two(a,w,b),x,Two(c,y,d),z,e))
      | Mid3,w,x,a,b,Three(c,y,d,z,e) ->
        Absorbed(rem,Three(a,w,Two(b,x,c),y,Two(d,z,e)))
      | Right3,w,z,a,Three(b,x,c,y,d),e ->
        Absorbed(rem,Three(a,w,Two(b,x,c),y,Two(d,z,e)))
      | Left3,_,_,_,_,_ | Mid3,_,_,_,_,_ | Right3,_,_,_,_,_ ->
        Absorbed(rem,Three(Leaf,n1,Leaf,n2,Leaf))

  (* DO NOT EDIT THIS *)
  let rec remove_downward (d: dict) (k: key) : hole =
    match d with
      | Leaf -> Absorbed(None,d)
      | Two(Leaf,(k1,v1),Leaf) ->
        (match D.compare_key k k1 with
          | EQ -> Hole(Some(k1,v1),Leaf)
          | LT | GT -> Absorbed(None,d)
        )
      | Three(Leaf,(k1,v1),Leaf,(k2,v2),Leaf) ->
        (match D.compare_key k k1, D.compare_key k k2 with
          | EQ, _ -> Absorbed(Some(k1,v1),Two(Leaf,(k2,v2),Leaf))
          | _, EQ -> Absorbed(Some(k2,v2),Two(Leaf,(k1,v1),Leaf))
          | _, _ -> Absorbed(None,d)
        )
      | Two(l,n,r) -> remove_downward_two k n l r
      | Three(l,n1,m,n2,r) -> remove_downward_three k n1 n2 l m r

  (* DO NOT EDIT THIS *)
  and remove_downward_two (k: key) ((k1,v1): pair) 
      (left: dict) (right: dict) : hole =
    match D.compare_key k k1 with
      | EQ ->
        (match remove_min right with
          | Hole(None,_) -> Hole(None,left)
          | Hole(Some n,new_right) -> 
            remove_upward_two n None left new_right Right2
          | Absorbed(None,_) -> Hole(None,left)
          | Absorbed(Some n,new_right) -> Absorbed(None,Two(left,n,new_right))
        )
      | LT -> 
        (match remove_downward left k with
          | Hole(rem,t) -> remove_upward_two (k1,v1) rem t right Left2
          | Absorbed(rem,t) -> Absorbed(rem,Two(t,(k1,v1),right))
        )
      | GT ->
        (match remove_downward right k with
          | Hole(rem,t) -> remove_upward_two (k1,v1) rem left t Right2
          | Absorbed(rem,t) -> Absorbed(rem,Two(left,(k1,v1),t))
        )

  (* DO NOT EDIT THIS *)
  and remove_downward_three (k: key) ((k1,v1): pair) ((k2,v2): pair)
      (left: dict) (middle: dict) (right: dict) : hole =
    match D.compare_key k k1, D.compare_key k k2 with
      | EQ, _ ->
        (match remove_min middle with
          | Hole(None,_) -> Hole(None,Two(left,(k2,v2),right))
          | Hole(Some n,new_middle) -> 
            remove_upward_three n (k2,v2) None left new_middle right Mid3
          | Absorbed(None,_) -> Absorbed(None,Two(left,(k1,v1),right))
          | Absorbed(Some n,new_middle) -> 
            Absorbed(None,Three(left,n,new_middle,(k2,v2),right))
        )
      | _ , EQ ->
        (match remove_min right with
          | Hole(None,_) -> Hole(None,Two(left,(k1,v1),middle))
          | Hole(Some n,new_right) -> 
            remove_upward_three (k1,v1) n None left middle new_right Right3
          | Absorbed(None,_) -> Absorbed(None,Two(left,(k1,v1),middle))
          | Absorbed(Some n,new_right) -> 
            Absorbed(None,Three(left,(k1,v1),middle,n,new_right))
        )
      | LT, _ ->
        (match remove_downward left k with
          | Hole(rem,t) -> 
            remove_upward_three (k1,v1) (k2,v2) rem t middle right Left3
          | Absorbed(rem,t) -> 
            Absorbed(rem,Three(t,(k1,v1),middle,(k2,v2),right))
        )
      | _, GT ->
        (match remove_downward right k with
          | Hole(rem,t) -> 
            remove_upward_three (k1,v1) (k2,v2) rem left middle t Right3
          | Absorbed(rem,t) -> 
            Absorbed(rem,Three(left,(k1,v1),middle,(k2,v2),t))
        )
      | GT, LT ->
        (match remove_downward middle k with
          | Hole(rem,t) -> 
            remove_upward_three (k1,v1) (k2,v2) rem left t right Mid3
          | Absorbed(rem,t) -> 
            Absorbed(rem,Three(left,(k1,v1),t,(k2,v2),right))
        )

  (* DO NOT EDIT THIS *)
  and remove_min (d: dict) : hole =
    match d with
      | Leaf -> Hole(None,Leaf)
      | Two(Leaf,n,_) -> Hole(Some n,Leaf)
      | Three(Leaf,n1,middle,n2,right) -> Absorbed(Some n1,Two(middle,n2,right))
      | Two(left,n,right) -> 
        (match remove_min left with
          | Hole(rem,t) -> remove_upward_two n rem t right Left2
          | Absorbed(rem,t) -> Absorbed(rem,Two(t,n,right))
        )
      | Three(left,n1,middle,n2,right) ->
        (match remove_min left with
          | Hole(rem,t) -> remove_upward_three n1 n2 rem t middle right Left3
          | Absorbed(rem,t) -> Absorbed(rem,Three(t,n1,middle,n2,right))
        )

  (* DO NOT EDIT THIS *)
  let remove (d: dict) (k: key) : dict =
    match remove_downward d k with
      | Hole(_,d') -> d'
      | Absorbed(_,d') -> d'

  (* TODO:
   * Write a lookup function that returns the value of the given key
   * in our dictionary and returns it as an option, or return None
   * if the key is not in our dictionary. *)
  let rec lookup (d: dict) (k: key) : value option =
    match d with
      | Leaf -> None
      | Two(left,(k1,v1),right) ->
        (match D.compare_key k k1 with
          | EQ -> Some v1
          | LT -> lookup left k
          | GT -> lookup right k)
      | Three(left,(k1,v1),middle,(k2,v2),right) ->
        (match D.compare_key k k1, D.compare_key k k2 with
          | EQ, _ -> Some v1
          | _, EQ -> Some v2
          | LT, _ -> lookup left k
          | _, GT -> lookup right k
          | GT, LT -> lookup middle k)

  let lookup_exn (d:dict) (k:key) : value =
    begin match lookup d k with
      | Some v -> v
      | None -> failwith "lookup_exn: key not found"
    end

  (* TODO:
   * Write a function to test if a given key is in our dictionary *)
  let member (d: dict) (k: key) : bool =
    lookup d k <> None

  (* TODO:
   * Write a function that removes any (key,value) pair from our 
   * dictionary (your choice on which one to remove), and returns
   * as an option this (key,value) pair along with the new dictionary. 
   * If our dictionary is empty, this should return None. *)
  let choose (d: dict) : (key * value * dict) option =
    match d with
      | Leaf -> None
      | Two(_,(k,v),_) -> Some (k,v,remove d k)
      | Three(_,(k,v),_,_,_) -> Some (k,v,remove d k)

  let from_kvp_list
      (l:(key * value) list)
    : dict =
    List.fold_left
      ~f:(fun d (k,v) ->
          insert d k v)
      ~init:empty
      l

  let is_empty
      (d:dict)
    : bool =
    begin match d with
      | Leaf -> true
      | _ -> false
    end

  let as_kvp_list
      (d:dict)
    : (key * value) list =
    fold
      (fun k v l -> (k,v)::l)
      []
      d

  let compare
      (d1:dict)
      (d2:dict)
    : comparison =
    let comparer = (pair_compare D.compare_key D.compare_value) in
    dictionary_order
      comparer
      (sort ~cmp:comparer (as_kvp_list d1))
      (sort ~cmp:comparer (as_kvp_list d2))
end




(******************************************************************)
(* Make: a functor that creates a DICT by calling our             *)
(* AssocListDict or BTDict functors                               *)
(******************************************************************)
module Make (D:DICT_ARG) : (DICT with type key = D.key
  with type value = D.value) = 
  (* Change this line to the BTDict implementation when you are
   * done implementing your 2-3 trees. *)
  (* AssocListDict(D) *)
  BTDict(D)

