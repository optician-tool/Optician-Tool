open Stdlib
open Regexcontext
open Lenscontext
open Lang
open Lens_put

let find_in_table (tbl:('a, 'b) Hashtbl.t) (key:'a) : 'b option =
  Hashtbl.find tbl key

let fetch_or_calculate (tbl: ('a, 'b) Hashtbl.t) (key:'a) (f:unit -> 'b) : 'b =
  match find_in_table tbl key with
  | Some ans -> ans
  | None ->
      let ans = f () in begin
        Hashtbl.set tbl ~key:key ~data:ans; ans
      end

module RC_R_S : sig
  type t = (RegexContext.t * Regex.t * int)
  val make_key : RegexContext.t -> Regex.t -> int -> t
  include Hashable.S with type t := t
end = struct
  module T = struct
    type t = RegexContext.t * Regex.t * int
    let make_key (rc:RegexContext.t) (r:Regex.t) (s:int) = (rc,r,s)
    let hash = hash_triple RegexContext.hash Regex.hash Int.hash
    let compare k1 k2 =
        (triple_compare
           RegexContext.compare
           Regex.compare
           compare
           k1
           k2)
      
    let sexp_of_t (_:t) : Sexp.t = failwith "GTS.sexp_of_t unimplemented"
    let t_of_sexp (_:Sexp.t) : t = failwith "GTS.t_of_sexp unimplemented"
  end
  include T
  include Hashable.Make(T)
end

module RC_LC_R_R_S : sig
  type t = (RegexContext.t * LensContext.t * Regex.t * Regex.t * int)
  val make_key : RegexContext.t -> LensContext.t -> Regex.t -> Regex.t -> int -> t
  include Hashable.S with type t := t
end = struct
  module T = struct
    type t = RegexContext.t * LensContext.t * Regex.t * Regex.t * int
    let make_key
        (rc:RegexContext.t)
        (lc:LensContext.t)
        (r1:Regex.t)
        (r2:Regex.t)
        (s:int)
      = (rc,lc,r1,r2,s)
    let hash =
      hash_quintuple
        RegexContext.hash
        LensContext.hash
        Regex.hash
        Regex.hash
        Int.hash
    let compare k1 k2 =
        (quint_compare
           RegexContext.compare
           LensContext.compare
           Regex.compare
           Regex.compare
           compare
           k1
           k2)
      
    let sexp_of_t (_:t) : Sexp.t = failwith "GTS.sexp_of_t unimplemented"
    let t_of_sexp (_:Sexp.t) : t = failwith "GTS.t_of_sexp unimplemented"
  end
  include T
  include Hashable.Make(T)
end

type rewriter = RegexContext.t -> Regex.t -> int -> Regex.t list
type synthesizer = RegexContext.t -> LensContext.t -> Regex.t -> Regex.t -> int -> Lens.t list

let memo_rrw_tbl : (RC_R_S.t, Regex.t list) Hashtbl.t =
  Hashtbl.create ~hashable:RC_R_S.hashable ()

let memo_lenssynth_tbl : (RC_LC_R_R_S.t, Lens.t list) Hashtbl.t =
  Hashtbl.create ~hashable:RC_LC_R_R_S.hashable ()
let rec regexes_of_size
    (size:int)
  : Regex.t list =
  let make_or
      (r1:Regex.t)
      (r2:Regex.t)
    : Regex.t =
    Regex.RegExOr(r1,r2)
  in
  let make_concat
      (r1:Regex.t)
      (r2:Regex.t)
    : Regex.t =
    Regex.RegExConcat(r1,r2)
  in
  let make_star
      (r:Regex.t)
    : Regex.t =
    Regex.RegExStar(r)
  in
  if size = 0 then
    []
  else if size = 1 then
    [Regex.RegExBase "a";Regex.RegExEmpty]
  else
    let stars = List.map ~f:make_star (regexes_of_size (size-1)) in
    let ps = double_partitions size in
    let ps_regexs =
      List.map
        ~f:(fun (f,s) ->
            (regexes_of_size f, regexes_of_size s))
        ps
    in
    let ors =
      List.concat_map
        ~f:(fun (frs,srs) ->
            cartesian_map
              ~f:make_or
              frs
              srs)
        ps_regexs
    in
    let concats =
      List.concat_map
        ~f:(fun (frs,srs) ->
            cartesian_map
              ~f:make_concat
              frs
              srs)
        ps_regexs
    in
    stars@ors@concats

let expand_vars_lr
    (rc:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  if size = 1 then
    begin match r with
      | Regex.RegExVariable v ->
        [RegexContext.lookup_exn rc v]
      | _ ->
        []
    end
  else
    []

let combine_bases_lr
    (_:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  if size = 1 then
    begin match r with
      | Regex.RegExConcat(Regex.RegExBase s1, Regex.RegExBase s2) ->
        [Regex.RegExBase (s1^s2)]
      | _ ->
        []
    end
  else
    []

let combine_bases_rl
    (_:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  if size = 1 then
    begin match r with
      | Regex.RegExBase s ->
        let len = String.length s in
        if len < 2 then
          []
        else
          let split_locations = range 1 (len-1) in
          List.map
            ~f:(fun i ->
                let s1 = String.sub ~pos:0 ~len:i s in
                let s2 = String.sub ~pos:i ~len:(len-i) s in
                Regex.RegExConcat(Regex.RegExBase s1, Regex.RegExBase s2))
            split_locations
      | _ ->
        []
    end
  else
    []

let or_id_rewrites_lr
    (_:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  if size = 1 then
    begin match r with
      | Regex.RegExOr(r1,Regex.RegExEmpty) ->
        [r1]
      | _ ->
        []
    end
  else
    []

let or_id_rewrites_rl
    (_:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  if size = 1 then
    [Regex.RegExOr(r,Regex.RegExEmpty)]
  else
    []

let empty_proj_right_rewrites_lr
    (_:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  if size = 1 then
    begin match r with
      | Regex.RegExConcat(_,Regex.RegExEmpty) ->
        [Regex.RegExEmpty]
      | _ ->
        []
    end
  else
    []

let empty_proj_right_rewrites_rl
    (_:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  begin match r with
    | Regex.RegExEmpty ->
      let generated_regexes = regexes_of_size size in
      List.map
        ~f:(fun r' ->
            Regex.RegExConcat (r', Regex.RegExEmpty))
        generated_regexes
    | _ ->
      []
  end

let empty_proj_left_rewrites_lr
    (_:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  if size = 1 then
    begin match r with
      | Regex.RegExConcat(Regex.RegExEmpty,_) ->
        [Regex.RegExEmpty]
      | _ ->
        []
    end
  else
    []

let empty_proj_left_rewrites_rl
    (_:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  begin match r with
    | Regex.RegExEmpty ->
      let generated_regexes = regexes_of_size size in
      List.map
        ~f:(fun r' ->
            Regex.RegExConcat (Regex.RegExEmpty, r'))
        generated_regexes
    | _ ->
      []
  end

let concat_assoc_rewrites_lr
    (_:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  if size = 1 then
    begin match r with
      | Regex.RegExConcat(Regex.RegExConcat(r1,r2),r3) ->
        [Regex.RegExConcat(r1,Regex.RegExConcat(r2,r3))]
      | _ ->
        []
    end
  else
    []

let concat_assoc_rewrites_rl
    (_:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  if size = 1 then
    begin match r with
      | Regex.RegExConcat(r1,Regex.RegExConcat(r2,r3)) ->
        [Regex.RegExConcat(Regex.RegExConcat(r1,r2),r3)]
      | _ ->
        []
    end
  else
    []

let or_assoc_rewrites_lr
    (_:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  if size = 1 then
    begin match r with
      | Regex.RegExOr(Regex.RegExOr(r1,r2),r3) ->
        [Regex.RegExOr(r1,Regex.RegExOr(r2,r3))]
      | _ ->
        []
    end
  else
    []

let or_assoc_rewrites_rl
    (_:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  if size = 1 then
    begin match r with
      | Regex.RegExOr(r1,Regex.RegExOr(r2,r3)) ->
        [Regex.RegExOr(Regex.RegExOr(r1,r2),r3)]
      | _ ->
        []
    end
  else
    []

let or_commut_rewrites
    (_:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  if size = 1 then
    begin match r with
      | Regex.RegExOr(r1,r2) ->
        [Regex.RegExOr(r2,r1)]
      | _ -> []
    end
  else
    []

let distributivity_left_rewrites_lr
    (_:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  if size = 1 then
    begin match r with
      | Regex.RegExConcat(r1, Regex.RegExOr(r2,r3)) ->
        [Regex.RegExOr(Regex.RegExConcat(r1,r2),Regex.RegExConcat(r1,r3))]
      | _ -> []
    end
  else
    []

let distributivity_left_rewrites_rl
    (_:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  if size = 1 then
    begin match r with
      | Regex.RegExOr(Regex.RegExConcat(r1,r2),Regex.RegExConcat(r1',r3)) ->
        if r1 = r1' then
          [Regex.RegExConcat(r1, Regex.RegExOr(r2,r3))]
        else
          []
      | _ -> []
    end
  else
    []

let distributivity_right_rewrites_lr
    (_:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  if size = 1 then
    begin match r with
      | Regex.RegExConcat(Regex.RegExOr(r1,r2), r3) ->
        [Regex.RegExOr(Regex.RegExConcat(r1,r3),Regex.RegExConcat(r2,r3))]
      | _ -> []
    end
  else
    []

let distributivity_right_rewrites_rl
    (_:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  if size = 1 then
    begin match r with
      | Regex.RegExOr(Regex.RegExConcat(r1,r3),Regex.RegExConcat(r2,r3')) ->
        if r3 = r3' then
          [Regex.RegExConcat(Regex.RegExOr(r1,r2), r3)]
        else
          []
      | _ -> []
    end
  else
    []

let concat_id_left_rewrites_lr
    (_:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  if size = 1 then
    begin match r with
      | Regex.RegExConcat(Regex.RegExBase "", r1) ->
        [r1]
      | _ ->
        []
    end
  else
    []

let concat_id_left_rewrites_rl
    (_:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  if size = 1 then
    [Regex.RegExConcat(Regex.RegExBase "", r)]
  else
    []

let concat_id_right_rewrites_lr
    (_:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  if size = 1 then
    begin match r with
      | Regex.RegExConcat(r1, Regex.RegExBase "") ->
        [r1]
      | _ ->
        []
    end
  else
    []

let concat_id_right_rewrites_rl
    (_:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  if size = 1 then
    [Regex.RegExConcat(r, Regex.RegExBase "")]
  else
    []

let unrollstar_left_rewrites_lr
    (_:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  if size = 1 then
    begin match r with
      | Regex.RegExStar(r1) ->
        [Regex.RegExOr(Regex.RegExBase "", Regex.RegExConcat(r1,Regex.RegExStar(r1)))]
      | _ ->
        []
    end
  else
    []

let unrollstar_left_rewrites_rl
    (_:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  if size = 1 then
    begin match r with
      | Regex.RegExOr(Regex.RegExBase "", Regex.RegExConcat(r1,Regex.RegExStar(r1'))) ->
        if r1 = r1' then
          [Regex.RegExStar(r1)]
        else
          []
      | _ ->
        []
    end
  else
    []

let unrollstar_right_rewrites_lr
    (_:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  if size = 1 then
    begin match r with
      | Regex.RegExStar(r1) ->
        [Regex.RegExOr(Regex.RegExBase "", Regex.RegExConcat(Regex.RegExStar(r1),r1))]
      | _ ->
        []
    end
  else
    []

let unrollstar_right_rewrites_rl
    (_:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  if size = 1 then
    begin match r with
      | Regex.RegExOr(Regex.RegExBase "", Regex.RegExConcat(Regex.RegExStar(r1),r1')) ->
        if r1 = r1' then
          [Regex.RegExStar(r1)]
        else
          []
      | _ ->
        []
    end
  else
    []

let rec recursive_rewrites
    (rc:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  fetch_or_calculate
    memo_rrw_tbl
    (RC_R_S.make_key rc r size)
    begin fun _ ->
      begin match r with
        | Regex.RegExConcat (r1,r2) ->
          let r1_rewrites = apply_single_rewrite rc r1 size in
          let r2_rewrites = apply_single_rewrite rc r2 size in
          let r1_rewritten_combined =
            List.map
              ~f:(fun r1rw -> Regex.RegExConcat (r1rw,r2))
              r1_rewrites
          in
          let r2_rewritten_combined =
            List.map
              ~f:(fun r2rw -> Regex.RegExConcat (r1,r2rw))
              r2_rewrites
          in
          r1_rewritten_combined@r2_rewritten_combined
        | Regex.RegExOr (r1,r2) ->
          let r1_rewrites = apply_single_rewrite rc r1 size in
          let r2_rewrites = apply_single_rewrite rc r2 size in
          let r1_rewritten_combined =
            List.map
              ~f:(fun r1rw -> Regex.RegExOr (r1rw,r2))
              r1_rewrites
          in
          let r2_rewritten_combined =
            List.map
              ~f:(fun r2rw -> Regex.RegExOr (r1,r2rw))
              r2_rewrites
          in
          r1_rewritten_combined@r2_rewritten_combined
        | Regex.RegExStar r' ->
          let r_prime_rewrites = apply_single_rewrite rc r' size in
          List.map
            ~f:(fun r_p_rw -> Regex.RegExStar r_p_rw)
            r_prime_rewrites
        | _ -> []
      end
    end
      
and apply_single_rewrite
    (rc:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  let rewriters =
    [expand_vars_lr
    ;combine_bases_lr
    ;combine_bases_rl
    ;or_id_rewrites_lr
    ;or_id_rewrites_rl
    ;empty_proj_right_rewrites_lr
    ;empty_proj_right_rewrites_rl
    ;empty_proj_left_rewrites_lr
    ;empty_proj_left_rewrites_rl
    ;concat_assoc_rewrites_lr
    ;concat_assoc_rewrites_rl
    ;or_assoc_rewrites_lr
    ;or_assoc_rewrites_rl
    ;or_commut_rewrites
    ;distributivity_left_rewrites_lr
    ;distributivity_left_rewrites_rl
    ;distributivity_right_rewrites_lr
    ;distributivity_right_rewrites_rl
    ;concat_id_left_rewrites_lr
    ;concat_id_left_rewrites_rl
    ;concat_id_right_rewrites_lr
    ;concat_id_right_rewrites_rl
    ;unrollstar_left_rewrites_lr
    ;unrollstar_left_rewrites_rl
    ;unrollstar_right_rewrites_lr
    ;unrollstar_right_rewrites_rl
    ;recursive_rewrites]
  in

  List.concat_map
    ~f:(fun rw -> rw rc r size)
    rewriters

let rec apply_rewrite_of_size
    (rc:RegexContext.t)
    (r:Regex.t)
    (size:int)
  : Regex.t list =
  if size = 0 then
    [r]
  else
    let last_rewrites = apply_single_rewrite rc r size in
    let split_parts = double_partitions size in
    let iterative_rewrites =
      List.concat_map
        ~f:(fun (s1,s2) ->
            let rs = apply_single_rewrite rc r s1 in
            List.concat_map
              ~f:(fun r' -> apply_rewrite_of_size rc r' s2)
              rs)
        split_parts
    in
    last_rewrites@iterative_rewrites

let rec gen_concat_lens_naive_of_size
    (rc:RegexContext.t)
    (lc:LensContext.t)
    (r1:Regex.t)
    (r2:Regex.t)
    (size:int)
  : Lens.t list =
  begin match (r1,r2) with
    | (Regex.RegExConcat(r11,r12),Regex.RegExConcat(r21,r22)) ->
      let ps = double_partitions (size-1) in
      List.concat_map
        ~f:(fun (s1,s2) ->
            let l1s = gen_lens_naive_of_size rc lc r11 r21 s1 in
            let l2s = gen_lens_naive_of_size rc lc r12 r22 s2 in
            cartesian_map
              ~f:(fun l1 l2 -> Lens.LensConcat(l1,l2))
              l1s
              l2s)
        ps
    | _ ->
      []
  end

and gen_or_lens_naive_of_size
    (rc:RegexContext.t)
    (lc:LensContext.t)
    (r1:Regex.t)
    (r2:Regex.t)
    (size:int)
  : Lens.t list =
  begin match (r1,r2) with
    | (Regex.RegExOr(r11,r12),Regex.RegExOr(r21,r22)) ->
      let ps = double_partitions (size-1) in
      let x = List.concat_map
          ~f:(fun (s1,s2) ->
              let l1s = gen_lens_naive_of_size rc lc r11 r21 s1 in
              let l2s = gen_lens_naive_of_size rc lc r12 r22 s2 in
              cartesian_map
                ~f:(fun l1 l2 -> Lens.LensUnion(l1,l2))
                l1s
                l2s)
          ps
      in
      x
    | _ ->
      []
  end

and gen_iterate_lens_naive_of_size
    (rc:RegexContext.t)
    (lc:LensContext.t)
    (r1:Regex.t)
    (r2:Regex.t)
    (size:int)
  : Lens.t list =
  begin match (r1,r2) with
    | (Regex.RegExStar(r1'),Regex.RegExStar(r2')) ->
      let ls = gen_lens_naive_of_size rc lc r1' r2' (size-1) in
      List.map
        ~f:(fun l -> Lens.LensIterate(l))
        ls
    | _ ->
      []
  end

and gen_ud_mapping_lens_of_size
    (_:RegexContext.t)
    (lc:LensContext.t)
    (r1:Regex.t)
    (r2:Regex.t)
    (size:int)
  : Lens.t list =
  begin match (r1,r2) with
    | (Regex.RegExVariable s1, Regex.RegExVariable s2) ->
      if s1 = s2 then
        []
      else
        begin match LensContext.shortest_path lc s1 s2 with
          | None -> []
          | Some l ->
            if Lens.size l = size then
              [l]
            else
              []
        end
    | _ ->
      []
  end

and gen_const_lens_of_size
    (_:RegexContext.t)
    (_:LensContext.t)
    (r1:Regex.t)
    (r2:Regex.t)
    (size:int)
  : Lens.t list =
  if size = 1 then
    begin match (r1,r2) with
      | (Regex.RegExBase s1, Regex.RegExBase s2) ->
        [Lens.LensConst(s1,s2)]
      | _ ->
        []
    end
  else
    []

and gen_identity_lens_of_size
    (_:RegexContext.t)
    (_:LensContext.t)
    (r1:Regex.t)
    (r2:Regex.t)
    (size:int)
  : Lens.t list =
  if size = 1 then
    begin match make_matchable (Regex.compare r1 r2) with
      | EQ ->
        [Lens.LensIdentity r1]
      | _ ->
        []
    end
  else
    []

and gen_retype_lens_of_size
    (rc:RegexContext.t)
    (lc:LensContext.t)
    (r1:Regex.t)
    (r2:Regex.t)
    (size:int)
  : Lens.t list =
  let tps = triple_partitions (size-1) in
  let both_rewritten =
    List.concat_map
      ~f:(fun (s1,s2,s3) ->
          let r1s = apply_rewrite_of_size rc r1 s1 in
          let r2s = apply_rewrite_of_size rc r2 s2 in
          List.concat
            (cartesian_map
               ~f:(fun r1' r2' -> gen_lens_naive_of_size rc lc r1' r2' s3)
               r1s
               r2s))
      tps
  in
  let dps = double_partitions (size-1) in
  let left_rewritten =
    List.concat_map
      ~f:(fun (s1,s3) ->
          let r1s = apply_rewrite_of_size rc r1 s1 in
          let r2s = [r2] in
          List.concat
            (cartesian_map
               ~f:(fun r1' r2' -> gen_lens_naive_of_size rc lc r1' r2' s3)
               r1s
               r2s))
      dps
  in
  let right_rewritten =
    List.concat_map
      ~f:(fun (s2,s3) ->
          let r1s = [r1] in
          let r2s = apply_rewrite_of_size rc r2 s2 in
          List.concat
            (cartesian_map
               ~f:(fun r1' r2' ->
                  gen_lens_naive_of_size rc lc r1' r2' s3)
               r1s
               r2s))
      dps
  in
  left_rewritten@right_rewritten@both_rewritten

and gen_lens_naive_of_size
    (rc:RegexContext.t)
    (lc:LensContext.t)
    (r1:Regex.t)
    (r2:Regex.t)
    (size:int)
  : Lens.t list =
  fetch_or_calculate
    memo_lenssynth_tbl
    (RC_LC_R_R_S.make_key rc lc r1 r2 size)
    begin fun _ ->
      let synthesizers =
        [gen_const_lens_of_size
        ;gen_concat_lens_naive_of_size
        ;gen_or_lens_naive_of_size
        ;gen_iterate_lens_naive_of_size
        ;gen_ud_mapping_lens_of_size
        ;gen_identity_lens_of_size
        ;gen_retype_lens_of_size
        ]
      in
      
      List.concat_map
        ~f:(fun synth ->
            synth rc lc r1 r2 size)
        synthesizers
    end

let gen_lens_naive (rc:RegexContext.t) (lc:LensContext.t) (r1:Regex.t) (r2:Regex.t)
    (exs:examples) : Lens.t =

  let rec gen_lens_naive_of_increasing_size
      (size:int)
    : Lens.t =
    let ls = gen_lens_naive_of_size rc lc r1 r2 size in
    let satisfying_ls =
      List.filter
        ~f:(fun l ->
            List.for_all
              ~f:(fun (i,o) ->
                  lens_putr rc lc l i = o)
              exs)
        ls
    in
    begin match satisfying_ls with
      | [] ->
        gen_lens_naive_of_increasing_size (size + 1)
      | l::_ -> l
    end
  in

  gen_lens_naive_of_increasing_size 1
