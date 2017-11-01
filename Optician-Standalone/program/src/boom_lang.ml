open Stdlib
open Lang
open Lenscontext
open Lens_utilities

type boom_typ =
  | BoomTypRegex
  | BoomTypLens of Regex.t * Regex.t

type boom_expression =
  | BoomExpRegex of Regex.t
  | BoomExpLens of Lens.t
  | BoomExpCut of boom_statement * boom_expression

and boom_statement =
  | BoomStmtDefinition of Id.t * boom_typ * boom_expression
  | BoomStmtTestRegex of Regex.t * string
  | BoomStmtTestLens of Lens.t * string * string

type boom_program = boom_statement list

let compare_boom_expression : boom_expression comparer = compare

let compare_boom_statement : boom_statement comparer = compare

let compare_boom_program : boom_program comparer =
  compare_list ~cmp:compare_boom_statement

let statement_of_decl (d:declaration) : boom_statement list =
  begin match d with
    | DeclRegexCreation(n,r,_) ->
      [BoomStmtDefinition (n,BoomTypRegex,BoomExpRegex r)]
    | DeclTestString (r,s) -> [BoomStmtTestRegex (r,s)]
    | DeclSynthesizeLens _ -> failwith "no boom functionality for this"
    | DeclLensCreation (n,r1,r2,l) ->
      [BoomStmtDefinition (n,BoomTypLens(r1,r2),BoomExpLens l)]
    | DeclTestLens (n,exs) ->
      List.map
        ~f:(fun (lex,rex) -> BoomStmtTestLens (Lens.LensVariable n, lex, rex))
        exs
  end

let retrieve_inverses_of_lens_variables_exn (p:program) : Id.t list =
  let rec retrieve_inverses_of_lens_variables_in_lens_exn
      (l:Lens.t)
    : Id.t list =
    begin match l with
      | Lens.LensConst _ -> []
      | Lens.LensConcat(l1,l2) ->
        let vs1 = retrieve_inverses_of_lens_variables_in_lens_exn l1 in
        let vs2 = retrieve_inverses_of_lens_variables_in_lens_exn l2 in
        vs1@vs2
      | Lens.LensSwap(l1,l2) ->
        let vs1 = retrieve_inverses_of_lens_variables_in_lens_exn l1 in
        let vs2 = retrieve_inverses_of_lens_variables_in_lens_exn l2 in
        vs1@vs2
      | Lens.LensUnion(l1,l2) ->
        let vs1 = retrieve_inverses_of_lens_variables_in_lens_exn l1 in
        let vs2 = retrieve_inverses_of_lens_variables_in_lens_exn l2 in
        vs1@vs2
      | Lens.LensCompose(l1,l2) ->
        let vs1 = retrieve_inverses_of_lens_variables_in_lens_exn l1 in
        let vs2 = retrieve_inverses_of_lens_variables_in_lens_exn l2 in
        vs1@vs2
      | Lens.LensIterate(l') ->
        retrieve_inverses_of_lens_variables_in_lens_exn l'
      | Lens.LensIdentity _ -> []
      | Lens.LensInverse(Lens.LensVariable n) -> [n]
      | Lens.LensInverse(l') ->
        retrieve_inverses_of_lens_variables_in_lens_exn l'
      | Lens.LensVariable _ -> []
      | Lens.LensPermute (_,ls) ->
        List.concat_map
          ~f:retrieve_inverses_of_lens_variables_in_lens_exn
          ls
    end
  in
  List.dedup
    (List.fold_left
       ~f:(fun acc d ->
           begin match d with
             | DeclLensCreation (_,_,_,l) ->
               acc @
               (retrieve_inverses_of_lens_variables_in_lens_exn l)
             | _ -> acc
           end)
       ~init:[]
       p)

let add_inverted_lenses_after_original_lenses
    (lc:LensContext.t)
    (p:program)
    (inverted_vars:Id.t list)
  : LensContext.t * program * (Id.t * Id.t) list =
  List.fold_right
    ~f:(fun d (lc,p,id_map) ->
        begin match d with
          | DeclLensCreation (n,r1,r2,l) ->
            if List.mem ~equal:(=) inverted_vars n then
              let l_inv = simplify_lens (Lens.LensInverse l) in
              let n_inv = LensContext.autogen_id_from_base lc ((Id.string_of_id n) ^ "_inv") in
              let d_inv = DeclLensCreation(n_inv,r2,r1,l_inv) in
              let lc = LensContext.insert_exn lc n_inv l_inv r2 r1 in
              (lc,d::d_inv::p,(n,n_inv)::id_map)
            else
              (lc,d::p,id_map)
          | _ -> (lc,d::p,id_map)
        end)
    ~init:(lc,[],[])
    p

let replace_inverted_lens_variables
    (inverted_map:(Id.t * Id.t) list)
    (p:program)
  : program =
  let replace_inverted_lens_variables_current_level_lens
      (l:Lens.t)
    : Lens.t =
    begin match l with
      | Lens.LensInverse(Lens.LensVariable n) ->
        begin match List.Assoc.find ~equal:(=) inverted_map n with
          | None ->
            l
          | Some v -> Lens.LensVariable v
        end
      | _ -> l
    end
  in
  let replace_inverted_lens_variables_lens =
    apply_at_every_level_lens
      replace_inverted_lens_variables_current_level_lens
  in
  List.fold_right
    ~f:(fun d acc ->
        let d =
          begin match d with
            | DeclLensCreation (n,r1,r2,l) ->
              let l = replace_inverted_lens_variables_lens l in
              DeclLensCreation (n,r1,r2,l)
            | _ -> d
          end
        in
        d::acc)
    ~init:[]
    p

let boom_program_of_program
    (lc:LensContext.t)
    (p:program)
  : boom_statement list =
  let p =
    fold_until_completion
      ~f:(fun (lc,p) ->
         let inversed_vars = retrieve_inverses_of_lens_variables_exn p in
         if inversed_vars = [] then
           Right p
         else
           let (lc,p,inverted_map) =
             add_inverted_lenses_after_original_lenses
               lc
               p
               inversed_vars
           in
           let p = replace_inverted_lens_variables inverted_map p in
           Left (lc,p))
      (lc,p)
  in
  List.concat_map ~f:statement_of_decl p
