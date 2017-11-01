open Core
open Util2

module Semiring =
struct 
  module type Sig =
  sig
    type t
    val apply_at_every_level : (t -> t) -> t -> t
    val applies_for_every_applicable_level : (t -> t option) -> t -> t list
    val zero : t
    val one : t
    val separate_plus : t -> (t * t) option
    val separate_times : t -> (t * t) option
    val make_plus : t -> t -> t
    val make_times : t -> t -> t
  end

  let maximally_factor_element
      (type t)
      (module S : Sig with type t = t)
    : S.t -> S.t =
    let rec separate_into_sum
        (r:S.t)
      : S.t list =
      begin match S.separate_plus r with
        | None -> [r]
        | Some (r1,r2) -> (separate_into_sum r1) @ (separate_into_sum r2)
      end
    in
    let rec separate_into_product
        (r:S.t)
      : S.t list =
      begin match S.separate_times r with
        | None -> [r]
        | Some (r1,r2) -> (separate_into_product r1) @ (separate_into_product r2)
      end
    in
    let combine_nonempty_list_exn
        (combiner:S.t -> S.t -> S.t)
        (rl:S.t list)
      : S.t =
      let (rlf,rll) = split_by_last_exn rl in
      List.fold_right
        ~f:(fun r acc ->
            combiner r acc)
        ~init:rll
        rlf
    in
    let combine_list
        (combiner:S.t -> S.t -> S.t)
        (rl:S.t list)
      : S.t option =
      begin match rl with
        | [] -> None
        | _ -> Some (combine_nonempty_list_exn combiner rl)
      end
    in
    let maximally_factor_current_level
        (product_splitter:S.t list -> (S.t * S.t list))
        (product_combiner:S.t -> S.t -> S.t)
        (he:S.t)
      : S.t =
      let sum_list = separate_into_sum he in
      let sum_product_list_list =
        List.map
          ~f:separate_into_product
          sum_list
      in
      let product_keyed_sum_list =
        List.map
          ~f:product_splitter
          sum_product_list_list
      in
      let grouped_assoc_list = group_by_keys product_keyed_sum_list in
      let keyed_sum_list =
        List.map
          ~f:(fun (k,all) ->
              let producted_elements =
                List.map
                  ~f:(fun pl ->
                      begin match combine_list S.make_times pl with
                        | None -> S.one
                        | Some he -> he
                      end)
                  all
              in
              (k,producted_elements))
          grouped_assoc_list
      in
      let ringed_list =
        List.map
          ~f:(fun (k,al) ->
              let factored_side = combine_nonempty_list_exn S.make_plus al in
              if factored_side = S.one then
                k
              else
                product_combiner
                  k
                  factored_side)
          keyed_sum_list
      in
      combine_nonempty_list_exn S.make_plus ringed_list
    in
    Fn.compose
      (fold_until_fixpoint
         (S.apply_at_every_level
            (maximally_factor_current_level
               (Fn.compose swap_double split_by_last_exn)
               (Fn.flip S.make_times))))
      (fold_until_fixpoint
         (S.apply_at_every_level
            (maximally_factor_current_level
               split_by_first_exn
               S.make_times)))
end

module StarSemiring =
struct
  module type Sig =
  sig
    type t
    val apply_at_every_level : (t -> t) -> t -> t
    val applies_for_every_applicable_level : (t -> t option) -> t -> t list
    val zero : t
    val one : t
    val separate_plus : t -> (t * t) option
    val separate_times : t -> (t * t) option
    val separate_star : t -> t option
    val make_plus : t -> t -> t
    val make_times : t -> t -> t
    val make_star : t -> t
  end

  let unfold_left_if_star
      (type t)
      (module S : Sig with type t = t)
      (v:S.t)
    : S.t option =
    Option.map
      ~f:(fun r' ->
          S.make_plus
            S.one
            (S.make_times
               r'
               (S.make_star r')))
      (S.separate_star v)

  let unfold_right_if_star
      (type t)
      (module S : Sig with type t = t)
      (v:S.t)
    : S.t option =
    Option.map
      ~f:(fun r' ->
          S.make_plus
            S.one
            (S.make_times
               (S.make_star r')
               r'))
      (S.separate_star v)

  let left_unfold_all_stars
      (type t)
      (module S : Sig with type t = t)
      (v:S.t)
    : S.t list =
    let ssr = (module S : Sig with type t = t) in
    S.applies_for_every_applicable_level
      (unfold_left_if_star ssr)
      v

  let right_unfold_all_stars
      (type t)
      (module S : Sig with type t = t)
      (v:S.t)
    : S.t list =
    let ssr = (module S : Sig with type t = t) in
    S.applies_for_every_applicable_level
      (unfold_right_if_star ssr)
      v
end
