open Util1
open Core.Std

(* An interface for set modules *)
module type COMPARISON_SET = 
sig
  type elt  (* type of elements in the set *)
  type set  (* abstract type for the set *)

  val empty : set

  val insert : elt -> set -> set

  val from_list : elt list -> set
  val as_list : set -> elt list

  (* same as insert x empty *)
  val singleton : elt -> set

  val union : set -> set -> set
  val intersect : set -> set -> set
  val minus : set -> set -> set

  (* remove an element from the set -- if the
   * element isn't present, does nothing. *)
  val remove : elt -> set -> set

  (* returns true iff the element is in the set *)
  val member : set -> elt -> bool

  val subset : set -> set -> bool

  (* chooses some member from the set, removes it 
   * and returns that element plus the new set.  
   * If the set is empty, returns None. *)
  val choose : set -> (elt * set) option

  (* fold a function across the elements of the set
   * in some unspecified order. *)
  val fold : (elt -> 'a -> 'a) -> 'a -> set -> 'a

  val is_empty : set -> bool

  val compare : set -> set -> comparison

  val po_compare : set -> set -> partial_order_comparison

  (* functions to convert our types to a string. useful for debugging. *)
  val to_string : set -> string
end



(* parameter to Set modules -- we must pass in some 
 * type for the elements of a set, a comparison
 * function, and a way to stringify it.
 *)
module type COMPARISON_SET_ARG = 
sig
  type element
  val compare : element -> element -> comparison
  val to_string : element -> string
end


(******************************************************************)
(* DictSet: a functor that creates a SET by calling our           *)
(* Dict.Make functor                                              *)
(******************************************************************)
module DictSet(C : COMPARISON_SET_ARG) : (COMPARISON_SET with type elt = C.element) = 
struct
  module D = Dict.Make(struct
    type key = C.element
    type value = unit
    let compare_key = C.compare
    let compare_value = comparison_compare
    let key_to_string = C.to_string
    let value_to_string = fun () -> "()"
  end)

  type elt = D.key
  type set = D.dict
  let empty = D.empty
  let insert x s = D.insert s x ()
  let singleton x = insert x empty
  let union s1 s2 = D.fold (fun x _ s -> insert x s) s2 s1
  let member = D.member
  let subset s1 s2 =
    D.fold (fun x _ acc -> acc && (member s2 x)) true s1
  let intersect s1 s2 = 
    D.fold (fun x _ s -> if member s2 x then insert x s else s) 
      empty s1
  let minus s1 s2 =
    D.fold (fun x _ s -> if not (member s2 x) then insert x s else s)
      empty s1
  let remove x s = D.remove s x
  let choose s = 
    match D.choose s with
      | None -> None
      | Some (k,_,s') -> Some (k,s')
  let fold f u s = D.fold (fun x _ a -> f x a) u s
  let to_string = D.to_string

  let from_list (es:elt list) : set =
    D.from_kvp_list
      (List.map
         ~f:(fun e -> (e,()))
         es)

  let as_list s =
    List.map ~f:fst (D.as_kvp_list s)

  let is_empty s = D.is_empty s

  let compare
      (s1:set)
      (s2:set)
    : comparison =
    dictionary_order
      C.compare
      (sort ~cmp:C.compare (as_list s1))
      (sort ~cmp:C.compare (as_list s2))

  let po_compare
      (s1:set)
      (s2:set)
    : partial_order_comparison =
    begin match (subset s1 s2, subset s2 s1) with
      | (true,true) -> PO_EQ
      | (true,false) -> PO_LT
      | (false,true) -> PO_GT
      | (false,false) -> PO_INCOMPARABLE
    end
end

module Make(S : COMPARISON_SET_ARG) : (COMPARISON_SET with type elt = S.element) = 
  (* Change this line to use our dictionary implementation when your are 
   * finished. *)
  (* ListSet (C) *)
  DictSet (S)

