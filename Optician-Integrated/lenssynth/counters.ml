open Stdlib

module type Counters_Sig = sig
  type 'a t

  val create : ('a -> 'a -> comparison) -> 'a t

  val add : 'a t -> 'a -> 'a t

  val merge : (int -> int -> int) -> 'a t -> 'a t -> 'a t

  val multiply_merge : 'a t -> 'a t -> 'a t

  val as_ordered_assoc_list : 'a t -> ('a * int) list

  val pp : ('a -> string) -> ('a t) -> string
end

module Counters : Counters_Sig = struct
  type 'a t = (('a * int) list * ('a -> 'a -> comparison))

  let create (comparer:'a -> 'a -> comparison) : 'a t = ([],comparer)

  let add ((counts,comparer):'a t) (data:'a) : 'a t =
    let rec add_internal (counts:('a * int) list) : ('a * int) list =
      begin match counts with
        | (h,i)::t ->
          let cmp = comparer data h in
          if is_equal cmp then
            (h,i+1)::t
          else if is_lt cmp then
            (data,1)::counts
          else
            (h,i)::(add_internal t)
      | [] -> [data,1]
      end
    in
    (add_internal counts,comparer)

  let merge (combiner:int -> int -> int)
      ((counts1,comparer1):'a t) ((counts2,comparer2):'a t) : 'a t =
    let comparer = comparer1 in
    let rec merge_internal (counts1:('a * int) list)
                           (counts2:('a * int) list)
                           : ('a * int) list =
      begin match (counts1,counts2) with
        | ((h1,i1)::t1,(h2,i2)::t2) ->
          let cmp = comparer h1 h2 in
          if is_equal cmp then
            (h1,combiner i1 i2)::(merge_internal t1 t2)
          else if is_lt cmp then
            (h1,combiner i1 0)::(merge_internal t1 counts2)
          else
            (h2,combiner 0 i2)::(merge_internal counts1 t2)
      | (_,[]) -> List.map ~f:(fun (d,i) -> (d,combiner i 0)) counts1
      | ([],_) -> List.map ~f:(fun (d,i) -> (d,combiner 0 i)) counts2
      end
    in
    
    if phys_equal comparer1 comparer2 then
      (merge_internal counts1 counts2,comparer1)
    else
      failwith "inconsistent comparers"


  let multiply_merge ((counts1,comparer1):'a t) ((counts2,comparer2):'a t) : 'a t =
    let comparer = comparer1 in
    let rec merge_internal (counts1:('a * int) list)
                           (counts2:('a * int) list)
                           : ('a * int) list =
      begin match (counts1,counts2) with
        | ((h1,i1)::t1,(h2,i2)::t2) ->
          let cmp = comparer h1 h2 in
          if is_equal cmp then
            (h1,i1*i2)::(merge_internal t1 t2)
          else if is_lt cmp then
            (h1,i1)::(merge_internal t1 counts2)
          else
            (h2,i2)::(merge_internal counts1 t2)
      | (_,[]) -> counts1
      | ([],_) -> counts2
      end
    in
    
    if phys_equal comparer1 comparer2 then
      (merge_internal counts1 counts2,comparer1)
    else
      failwith "inconsistent comparers"

  let as_ordered_assoc_list ((counts,_):'a t) : ('a * int) list =
    counts

  let pp (f:'a -> string) ((counts,_):'a t) : string =
    "[" ^ (String.concat ~sep:" ; " (List.map ~f:(fun (x,c) -> (f x) ^ "->" ^
    (string_of_int c)) counts)) ^ "]"
end
