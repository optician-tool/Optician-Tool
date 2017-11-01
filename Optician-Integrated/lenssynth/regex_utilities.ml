open Stdlib
open Lang
open Regexcontext

let rec make_regex_safe_in_smaller_context
    (rc_smaller:RegexContext.t)
    (rc_larger:RegexContext.t)
  : Regex.t -> Regex.t =
  fold_until_fixpoint
    (Regex.fold
       ~empty_f:Regex.zero
       ~concat_f:Regex.make_times
       ~or_f:Regex.make_plus
       ~star_f:Regex.make_star
       ~base_f:Regex.make_base
       ~var_f:(fun v ->
           begin match (RegexContext.lookup rc_smaller v) with
             | None ->
               RegexContext.lookup_exn rc_larger v
             | Some _ -> Regex.make_var v
           end))

let simplify_regex : Regex.t -> Regex.t =
  let maximally_factor_regex : Regex.t -> Regex.t =
    Semiring.maximally_factor_element
      regex_semiring
  in
  let rec clean_regex (r:Regex.t) : Regex.t =
    begin match r with
      | Regex.RegExConcat(x,y) ->
        let x = clean_regex x in
        let y = clean_regex y in
        begin match (x,y) with
          | (Regex.RegExBase "",_) -> y
          | (_,Regex.RegExBase "") -> x
          | (Regex.RegExEmpty,_) -> Regex.RegExEmpty
          | (_,Regex.RegExEmpty) -> Regex.RegExEmpty
          | _ -> Regex.RegExConcat(x,y)
        end
      | Regex.RegExOr(x,y) ->
        let x = clean_regex x in
        let y = clean_regex y in
        begin match (x,y) with
          | (Regex.RegExEmpty,_) -> y
          | (_,Regex.RegExEmpty) -> x
          | _ -> Regex.RegExOr(x,y)
        end
      | Regex.RegExStar(x) ->
        let x = clean_regex x in
        begin match x with
          | Regex.RegExEmpty -> Regex.RegExBase ""
          | _ -> Regex.RegExStar x
        end
      | _ -> r
    end
  in

  let merge_concated_bases : Regex.t -> Regex.t =
    let rec retrieve_rightmost_concated_base
        (r:Regex.t)
      : (Regex.t option * string option) =
      begin match r with
        | Regex.RegExConcat (r1,r2) ->
          begin match retrieve_rightmost_concated_base r2 with
            | (None, so) -> (Some r1, so)
            | (Some r2, so) -> (Some (Regex.RegExConcat (r1,r2)),so)
          end
        | Regex.RegExBase s -> (None, Some s)
        | _ -> (Some r, None)
      end
    in
    let rec try_insert_into_leftmost_concated_base
        (r:Regex.t)
        (s1:string)
      : Regex.t option =
      begin match r with
        | Regex.RegExConcat (r1,r2) ->
          Option.map
            ~f:(fun r1 -> Regex.RegExConcat (r1,r2))
            (try_insert_into_leftmost_concated_base r1 s1)
        | Regex.RegExBase s2 ->
          Some (Regex.RegExBase (s1^s2))
        | _ -> None
      end
    in
    let merge_concated_bases_current_level
        (r:Regex.t)
      : Regex.t =
      begin match r with
        | Regex.RegExConcat (r1,r2) ->
          begin match retrieve_rightmost_concated_base r1 with
            | (r1o,Some s1) ->
              begin match try_insert_into_leftmost_concated_base r2 s1 with
                | None -> r
                | Some r2 ->
                  begin match r1o with
                    | None -> r2
                    | Some r1 -> Regex.RegExConcat (r1,r2)
                  end
              end
            | (_, None) -> r
          end
        | _ -> r
      end
    in

    Regex.apply_at_every_level merge_concated_bases_current_level
  in

  fold_until_fixpoint
    (merge_concated_bases
     % clean_regex
     % maximally_factor_regex)


let rec iteratively_deepen (r:Regex.t) : Regex.t * RegexContext.t =
  begin match r with
  | Regex.RegExEmpty -> (r,RegexContext.empty)
  | Regex.RegExBase _ -> (r,RegexContext.empty)
  | Regex.RegExConcat (r1,r2) ->
      let (r1',c1) = iteratively_deepen r1 in
      let (r2',c2) = iteratively_deepen r2 in
      let context = RegexContext.merge_contexts_exn c1 c2 in
      let regex_definition = Regex.RegExConcat(r1',r2') in
      let regex_variable =
        RegexContext.autogen_id
          context
          regex_definition
      in
      let context =
        RegexContext.insert_exn
          context
          regex_variable
          regex_definition
          false
        in
      (Regex.RegExVariable regex_variable,context)
  | Regex.RegExOr (r1,r2) ->
      let (r1',c1) = iteratively_deepen r1 in
      let (r2',c2) = iteratively_deepen r2 in
      let context = RegexContext.merge_contexts_exn c1 c2 in
      let regex_definition = Regex.RegExOr(r1',r2') in
      let regex_variable =
        RegexContext.autogen_id
          context
          regex_definition
      in
      let context =
        RegexContext.insert_exn
          context
          regex_variable
          regex_definition
          false
        in
      (Regex.RegExVariable regex_variable,context)
  | Regex.RegExStar r' ->
      let (r'',c) = iteratively_deepen r' in
      let regex_definition = Regex.RegExStar r'' in
      let regex_variable =
        RegexContext.autogen_id
          c
          regex_definition
      in
      let context =
        RegexContext.insert_exn
          c
          regex_variable
          regex_definition
          false
        in
      (Regex.RegExVariable regex_variable,context)
  | Regex.RegExVariable _ ->
      (r,RegexContext.empty)
  end

(*let rec ordered_exampled_dnf_regex_to_regex
    (r:ordered_exampled_dnf_regex) : regex =
  dnf_regex_to_regex (ordered_exampled_dnf_regex_to_dnf_regex r)*)

