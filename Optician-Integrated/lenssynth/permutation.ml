open Stdlib

type swap_concat_compose_tree =
  | SCCTSwap of swap_concat_compose_tree * swap_concat_compose_tree
  | SCCTConcat of swap_concat_compose_tree * swap_concat_compose_tree
  | SCCTCompose of swap_concat_compose_tree * swap_concat_compose_tree
  | SCCTLeaf
[@@deriving ord, show, hash]

let rec size_scct (scct:swap_concat_compose_tree) : int =
  begin match scct with
  | SCCTSwap (s1,s2) -> (size_scct s1) + (size_scct s2)
  | SCCTConcat (s1,s2) -> (size_scct s1) + (size_scct s2)
  | SCCTCompose (s1,s2) -> max (size_scct s1) (size_scct s2)
  | SCCTLeaf -> 1
  end

let rec has_compose (scct:swap_concat_compose_tree) : bool =
  begin match scct with
    | SCCTSwap (s1,s2) -> (has_compose s1) || (has_compose s2)
    | SCCTConcat (s1,s2) -> (has_compose s1) || (has_compose s2)
    | SCCTCompose _ -> true
    | SCCTLeaf -> false
  end

let rec pp_swap_concat_compose_tree (scct:swap_concat_compose_tree)
  : string =
    begin match scct with
    | SCCTSwap (scct1,scct2) -> "swap ("
        ^ (pp_swap_concat_compose_tree scct1)
        ^ ","
        ^ (pp_swap_concat_compose_tree scct2)
        ^ ")"
    | SCCTConcat (scct1,scct2) -> "concat ("
        ^ (pp_swap_concat_compose_tree scct1)
        ^ ","
        ^ (pp_swap_concat_compose_tree scct2)
        ^ ")"
    | SCCTCompose (scct1,scct2) -> "compose ("
        ^ (pp_swap_concat_compose_tree scct1)
        ^ ","
        ^ (pp_swap_concat_compose_tree scct2)
        ^ ")"
    | SCCTLeaf -> "."
    end

module Permutation = struct
  type t = int list
  [@@deriving show]

  let create (mapping:int list) =
    let len = List.length mapping in
    List.rev
      (List.fold_left
      ~f:(fun acc x ->
        if ((List.mem ~equal:(=) acc x) || (x >= len) || (x < 0)) then
          failwith "Not Bijection"
        else
          x::acc)
      ~init:[]
      mapping)

  let create_from_doubles (mapping:(int*int) list) : t =
    let len = List.length mapping in
    let (mapping_ls,mapping_rs) = List.unzip mapping in
    let contains_dup_l = List.contains_dup
        ~compare:(fun x y -> x - y)
        mapping_ls in
    let contains_dup_r = List.contains_dup
        ~compare:(fun x y -> x - y)
        mapping_rs in
    let out_of_range = List.exists
        ~f:(fun (x,y) -> x >= len || x < 0 || y >= len || y < 0)
        mapping in
    if contains_dup_l || contains_dup_r || out_of_range then
      failwith "Not Bijection"
    else
      let sorted_by_second = List.sort
        ~cmp:(fun (_,x) (_,y) -> x - y)
        mapping in
      List.map ~f:(fun (x,_) -> x) sorted_by_second

  let create_from_doubles_unsafe (mapping:(int*int) list) : t =
    let sorted_by_second = List.sort
      ~cmp:(fun (_,x) (_,y) -> x - y)
      mapping in
    List.map ~f:(fun (x,_) -> x) sorted_by_second

  let create_from_constraints (len:int) (invalid_parts:(int*int) list)
                              (required_parts:(int*int) list)
                              : (t * ((int*int) list)) option =

    let rec create_from_constraints_internal (len:int)
                                             (invalid_parts:(int*int) list)
                                             (required_parts:(int*int) list)
                                             (unused_partsl:int list)
                                             (unused_partsr:int list)
                                             (guessed_parts:(int*int) list)
                                             (continuation:
                                               ((t * ((int*int) list)) option)
                                            -> ((t * ((int*int) list)) option))
                                             (unused_l:int)
                                           : (t * ((int*int) list)) option =
      begin match unused_partsl with
      | [] -> Some (create_from_doubles required_parts, guessed_parts)
      | hl::tl ->
          let choice = split_by_first_satisfying
            (fun x -> not (List.mem ~equal:(=) invalid_parts (hl,x)))
            unused_partsr in
          begin match choice with
          | None -> continuation None
          | Some (hr,tr) ->
              let ctn = (fun potential_solution ->
                begin match potential_solution with
              | None ->
                  create_from_constraints_internal
                          len
                          ((hl,hr)::invalid_parts)
                          required_parts
                          unused_partsl
                          unused_partsr
                          guessed_parts
                          continuation
                          unused_l
              | Some _ -> continuation(potential_solution)
              end) in
              create_from_constraints_internal
                len
                invalid_parts
                ((hl,hr)::required_parts)
                tl
                tr
                ((hl,hr)::guessed_parts)
                ctn
                (unused_l-1)
          end
      end in
  if (List.exists
        ~f:(fun invalid_part -> List.mem ~equal:(=) required_parts invalid_part)
        invalid_parts) then
    None
  else
    let available_parts = range 0 len in
    let (used_partsl,used_partsr) = List.unzip required_parts in
    let (unused_partsl,unused_partsr) = List.fold_left
      ~f:(fun (l,r) x ->
            let unused_in_left = not (List.mem ~equal:(=) used_partsl x) in
            let unused_in_right = not (List.mem ~equal:(=) used_partsr x) in
            let l' = if unused_in_left then x::l else l in
            let r' = if unused_in_right then x::r else r in
            (l',r'))
      ~init:([],[])
      available_parts in
    create_from_constraints_internal
      len
      invalid_parts
      required_parts
      unused_partsl
      unused_partsr
      []
      (fun x -> x)
      (List.length unused_partsl)

  let rm x l = List.filter ~f:((<>) x) l  

  let create_all (n:int) : t list =
    let rec permutations = function  
    | [] -> []
    | x::[] -> [[x]]
    | l -> List.fold_left ~f:(fun acc x -> acc @ List.map ~f:(fun p -> x::p)
             (permutations (rm x l))) ~init:[] l
    in
    permutations (range 0 n)

  let inverse (p:t) : t =
    let mapped_doubles =
      List.mapi
        ~f:(fun y x -> (x,y))
        p
    in
    let sorted_doubles =
      List.sort
        ~cmp:(fun (x1,_) (x2,_) -> x2 - x1)
        mapped_doubles
    in
    List.map ~f:snd sorted_doubles

  let apply (permutation:t) (n:int) =
    let rec find x lst =
      begin match lst with
      | [] -> failwith "out of range"
      | h::t -> if x = h then 0 else 1 + find x t
      end in
    find n permutation

  let apply_inverse (permutation:t) (n:int) =
    begin match (List.nth permutation n) with
    | None -> failwith "out of range"
    | Some i -> i
    end

  let apply_to_list_exn (permutation:t) (l:'a list) : 'a list =
    List.map
      ~f:(fun x -> List.nth_exn l x)
      permutation

  let apply_inverse_to_list_exn (permutation:t) (l:'a list) : 'a list =
    let permutation_list_combo = List.zip_exn permutation l in
    let sorted_by_perm = List.sort
      ~cmp:(fun (p1,_) (p2,_) -> p1 - p2)
      permutation_list_combo in
    let (_,l') = List.unzip sorted_by_perm in
    l'

  let pp (permutation:t) : string =
    String.concat
      (List.mapi
        ~f:(fun x y -> (string_of_int x) ^ "<-" ^ (string_of_int y))
        permutation)
      ~sep: " , "

  let rec to_swap_concat_compose_tree (l:t) : swap_concat_compose_tree =
    let stupidconcat (l:t) : swap_concat_compose_tree =
      let (_,t) = split_by_first_exn l in
      List.fold_left
        ~f:(fun acc _ ->
          SCCTConcat (acc,SCCTLeaf))
        ~init:SCCTLeaf
        t
    in
    if List.length l = 0 then
      failwith "bad input"
    else if List.length l = 1 then
      SCCTLeaf
    else
      let valid_split =
        List.fold_left
        ~f:(fun acc i ->
          begin match acc with
          | None ->
              let (l1,l2) = split_at_index_exn l i in
              if pairwise_maintain_invariant (<) l1 l2 then
                Some (i,true)
              else if pairwise_maintain_invariant (>) l1 l2 then
                Some (i,false)
              else
                None
          | _ -> acc
          end)
        ~init:None
        (range 1 (List.length l)) in
      begin match valid_split with
      | None ->
          let (_,i) =
            List.foldi
            ~f:(fun i' (acc,i) x ->
              if acc > x then
                (acc,i)
              else
                (x,i'))
            ~init:(-1,-1)
            l in
          let (l1,l2) = split_at_index_exn l i in
          let (h,t) = split_by_first_exn l2 in
          SCCTCompose
            (to_swap_concat_compose_tree (l1@t@[h])
            ,SCCTConcat
              (stupidconcat l1
              ,SCCTSwap
                (SCCTLeaf
                ,stupidconcat t)))
      | Some (i,b) ->
          let (l1,l2) = split_at_index_exn l i in
          if b then
            SCCTConcat
              (to_swap_concat_compose_tree l1
              ,to_swap_concat_compose_tree l2)
          else
            SCCTSwap
              (to_swap_concat_compose_tree l2
              ,to_swap_concat_compose_tree l1)
      end

  let to_int_list : t -> int list = inverse

  let hash (p:t) : int =
    let l = to_int_list p in
    List.foldi
      ~f:(fun i acc n ->
          (Int.hash n)
          lxor (Int.hash i)
          lxor acc)
      ~init:509223028
      l

  let compare : t -> t -> comparison =
    compare_list ~cmp:compare_int
end
