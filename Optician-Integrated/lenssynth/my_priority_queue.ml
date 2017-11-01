open Core
open Util2
open My_set
open My_heap

module type DataWithPriority =
sig
  type t
  val show : t shower
  val pp : t pper
  val compare : t comparer
  val hash : t hasher
  val hash_fold_t : t hash_folder
  val priority : t -> int
end

module PriorityQueueOf(D:DataWithPriority) =
struct
  module QueueHeap =
    HeapOf(
    struct
      type t = (D.t * int)
      [@@deriving show, hash]

      let compare =
        (fun (_,f1) (_,f2) ->
             (compare_int f1 f2))
      let to_string = fun _ -> "hi"
    end)

  module PushedSet =
    SetOf(D)

  type t = QueueHeap.t * PushedSet.t
  [@@deriving show, hash]

  type element = D.t

  let empty = (QueueHeap.empty, PushedSet.empty)

  let push ((h,s):t) (e:element) : t =
    if PushedSet.member s e then
      (h,s)
    else
      let s' = PushedSet.insert e s in
      let pri = D.priority e in
      let h' = QueueHeap.push h (e,pri) in
      (h',s')

  let push_all (q:t) (es:element list) : t =
    List.fold_left
      ~f:(fun q e -> push q e)
      ~init:q
      es

  let from_list (es:element list) : t =
    push_all empty es

  let singleton (e:element) : t =
    from_list [e]

  let pop ((h,s):t) : ('a * int * t) option =
    Option.map ~f:(fun ((e,p),h') -> (e,p,(h',s))) (QueueHeap.pop h)

  let pop_exn (q:t) : 'a * int * t =
    begin match pop q with
      | None -> failwith "failure: pop_exn"
      | Some e -> e
    end

  let all_remaining ((h,_):t) : ('a * int) list =
    QueueHeap.to_list h

  let rec pop_until_min_pri_greater_than
      (q:t)
      (f:int)
    : (element * int) list * t =
      begin match pop q with
        | None -> ([],q)
        | Some (e,f',q') ->
          if f' > f then
            ([],q)
          else
            let (efs,q'') = pop_until_min_pri_greater_than q' f in
            ((e,f')::efs,q'')
      end


  let length ((h,_):t) : int = QueueHeap.size h

  let compare
    : (QueueHeap.t * PushedSet.t) comparer =
    let real_heap_compare
        (qh1:QueueHeap.t)
        (qh2:QueueHeap.t)
      : comparison =
      let ordered_qhl1 =
        List.sort
          ~cmp:D.compare
          (List.map ~f:fst (QueueHeap.to_list qh1))
      in
      let ordered_qhl2 =
        List.sort
          ~cmp:D.compare
          (List.map ~f:fst (QueueHeap.to_list qh2))
      in
      compare_list
        ~cmp:D.compare
        ordered_qhl1
        ordered_qhl2
    in
    pair_compare
      real_heap_compare
      PushedSet.compare
end
