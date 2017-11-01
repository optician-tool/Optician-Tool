(* Heavily using http://typeocaml.com/2015/03/12/heap-leftist-tree/ *)

open Core.Std
open Util1
open String_utilities

module type COMPARISON_HEAP =
sig
  type heap
  type element

  val empty : heap
  val push : heap -> element -> heap
  val pop : heap -> (element * heap) option
  val size : heap -> int
  val to_string : heap -> string
  val compare : heap -> heap -> comparison
end

module type COMPARISON_HEAP_ARG =
sig
  type element

  val compare : element -> element -> comparison
  val to_string : element -> string
end

module TreeHeap(H:COMPARISON_HEAP_ARG) : (COMPARISON_HEAP with type element = H.element) =
struct
  type element = H.element
  type heap =
    | Leaf
    | Node of heap * element * heap * int

  let empty : heap = Leaf

  let singleton (e:element) : heap =
    Node(Leaf,e,Leaf,1)

  let rank (h:heap) : int =
    begin match h with
      | Leaf -> 0
      | Node (_,_,_,r) -> r
    end
    
  let rec merge (h1:heap) (h2:heap) : heap =
    begin match (h1,h2) with
      | (Leaf,_) -> h2
      | (_,Leaf) -> h1
      | (Node(lh,e1,rh,_), Node(_,e2,_,_)) ->
        begin match H.compare e1 e2 with
          | GT ->
            merge h2 h1
          | _ ->
            let merged = merge rh h2 in
            let rank_left = rank lh in
            let rank_right = rank merged in
            if rank_left >= rank_right then
              Node (lh, e1, merged, rank_right+1)
            else
              Node (merged, e1, lh, rank_left+1)
        end
    end
    
  let push (h:heap) (e:element) : heap =
    merge h (singleton e)

  let pop (h:heap) : (element * heap) option =
    begin match h with
      | Leaf -> None
      | Node (lh, e, rh, _) -> Some (e, merge lh rh)
    end

  let rec to_string (h:heap) : string =
    begin match h with
      | Leaf -> "Leaf"
      | Node(lh,e,rh,rank) ->
        "Node" ^
        (string_of_quadruple
           to_string
           H.to_string
           to_string
           string_of_int
           (lh,e,rh,rank))
    end

  let rec size (h:heap) : int =
    begin match h with
      | Leaf -> 0
      | Node(lh,_,rh,_) -> 1 + (size lh) + (size rh)
    end

  let rec to_list (h:heap) : element list =
    begin match h with
      | Leaf -> []
      | Node(lh,e,rh,_) -> e::((to_list lh)@(to_list rh))
    end

  let compare (h1:heap) (h2:heap) : comparison =
    let h1es = sort ~cmp:H.compare (to_list h1) in
    let h2es = sort ~cmp:H.compare (to_list h2) in
    dictionary_order
      H.compare
      h1es
      h2es
end

module Make (H:COMPARISON_HEAP_ARG) : (COMPARISON_HEAP with type element = H.element) =
  TreeHeap(H)

