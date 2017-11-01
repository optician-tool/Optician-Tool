open Stdlib
open String_utilities
open Lang
open Format
open Boom_lang

(***** Helpers  *****)

let fpf         = fprintf ;;
let ident ppf s = fpf ppf "%s" s ;;
let kwd   ppf s = fpf ppf "%s" s ;;
type pp_info = int * Regex.t * bool * bool

(*****  *****)

(***** Regexs  *****)

let prec_of_regex (r:Regex.t) =
  begin match r with
    | Regex.RegExEmpty      -> 150
    | Regex.RegExBase     _ -> 150
    | Regex.RegExVariable _ -> 150
    | Regex.RegExStar     _ -> 125
    | Regex.RegExConcat   _ -> 100
    | Regex.RegExOr       _ -> 75
  end

let prec_of_lens (l:Lens.t) =
  begin match l with
    | Lens.LensIdentity  _ -> 150
    | Lens.LensVariable  _ -> 150
    | Lens.LensInverse   _ -> 150(*failwith "TODO: inverse support"*)
    | Lens.LensIterate   _ -> 125
    | Lens.LensSwap      _ -> 112
    | Lens.LensCompose   _ -> 112
    | Lens.LensConst("",_) -> 112
    | Lens.LensConst(_,"") -> 112
    | Lens.LensPermute   _ -> 112
    | Lens.LensConcat    _ -> 100
    | Lens.LensConst     _ -> 100
    | Lens.LensUnion     _ -> 75
  end

let rec boom_fpf_regex
    (ppf:formatter)
    ((lvl, r, or_seq, conc_seq):pp_info)
  : unit =
  let this_lvl = prec_of_regex r in
  (if this_lvl < lvl then fpf ppf "(");
  begin match r with
    | Regex.RegExEmpty -> fpf ppf "AHHH" 
    | Regex.RegExBase s -> fpf ppf "\"%a\"" ident (delimit_string s)
    | Regex.RegExVariable n -> fpf ppf "%a" ident (Id.string_of_id n)
    | Regex.RegExStar r' -> fpf ppf "%a* " boom_fpf_regex (this_lvl, r', false, false)
    | Regex.RegExConcat (r1,r2) ->
      if conc_seq then
        fpf ppf "@[<hv -2>%a@ . %a@]"
          boom_fpf_regex (this_lvl, r1, false, true)
          boom_fpf_regex (this_lvl, r2, false, true)
      else
        fpf ppf "@[<hv 2>%a@ . %a@]"
          boom_fpf_regex (this_lvl, r1, false, true)
          boom_fpf_regex (this_lvl, r2, false, true)
    | Regex.RegExOr (r1,r2) ->
      if or_seq then
        fpf ppf "@[<hv -2>%a@ | %a@]"
          boom_fpf_regex (this_lvl, r1, true, false)
          boom_fpf_regex (this_lvl, r2, true, false)
      else
        fpf ppf "@[<hv 2>%a@ | %a@]"
          boom_fpf_regex (this_lvl, r1, true, false)
          boom_fpf_regex (this_lvl, r2, true, false)
  end;
  (if this_lvl < lvl then fpf ppf ")")

let rec boom_fpf_lens
    (ppf:formatter)
    ((lvl, l, or_seq, conc_seq):int * Lens.t * bool * bool)
  : unit =
  let this_lvl = prec_of_lens l in
  (if this_lvl < lvl then fpf ppf "(");
  begin match l with
    | Lens.LensConst (s1,s2) ->
      let s1 = delimit_string s1 in
      let s2 = delimit_string s2 in
      if s1 <> "" && s2 <> "" then
        fpf ppf "del \"%a\"@ . ins \"%a\""
          ident s1
          ident s2
      else if s1 = "" then
        fpf ppf "ins \"%a\""
          ident s2
      else if s2 = "" then
        fpf ppf "del \"%a\""
          ident s1
    | Lens.LensConcat(l1,l2) ->
      if conc_seq then
        fpf ppf "@[<hv -2>%a@ . %a@]"
          boom_fpf_lens (this_lvl, l1, false, true)
          boom_fpf_lens (this_lvl, l2, false, true)
      else
        fpf ppf "@[<hv 2>%a@ . %a@]"
          boom_fpf_lens (this_lvl, l1, false, false)
          boom_fpf_lens (this_lvl, l2, false, true)
    | Lens.LensSwap(l1,l2) ->
      fpf ppf "@[<hv 2>lens_swap@ %a@ %a@]"
        boom_fpf_lens (this_lvl+1, l1, false, false)
        boom_fpf_lens (this_lvl+1, l2, false, false)
    | Lens.LensUnion(l1,l2) ->
      if or_seq then
        fpf ppf "@[<hv -3>%a@ || %a@]"
          boom_fpf_lens (this_lvl, l1, true, false)
          boom_fpf_lens (this_lvl, l2, true, false)
      else
        fpf ppf "@[<hv 4>%a@ || %a@]"
          boom_fpf_lens (this_lvl, l1, false, false)
          boom_fpf_lens (this_lvl, l2, true, false)
    | Lens.LensCompose(l1,l2) ->
      fpf ppf "@[<hv 2>compose@ %a@ %a@]"
        boom_fpf_lens (this_lvl+1, l1, false, false)
        boom_fpf_lens (this_lvl+1, l2, false, false)
    | Lens.LensIterate(l') ->
      fpf ppf "%a* "
        boom_fpf_lens (this_lvl, l', false, false);
    | Lens.LensIdentity r ->
      boom_fpf_regex ppf (this_lvl,r, false, false)
    | Lens.LensInverse _ ->
      failwith "inverse doesn't exist in boom"
    | Lens.LensVariable n ->
      fpf ppf "%a"
        ident
        (Id.string_of_id n)
    | Lens.LensPermute(p,ls) ->
      fpf ppf "@[<hv 2>lens_permute@ #{int}%a@ #{lens}[%a]@]"
        ident (String_utilities.string_of_int_list (Permutation.to_int_list p))
        (Format.pp_print_list
           ~pp_sep:(fun ppf _ -> fpf ppf "%a" ident ";")
           (fun ppf l -> boom_fpf_lens ppf (0,l,false,false)))
        ls
  end;
  (if this_lvl < lvl then fpf ppf ")")

let boom_fpf_typ
    (ppf:formatter)
    (t:boom_typ)
  : unit =
  begin match t with
    | BoomTypRegex -> fpf ppf "regexp"
    | BoomTypLens(r1,r2) ->
      fpf ppf "@[<hv 2>(lens in@ %a@ <=> %a)@]"
        boom_fpf_regex (150,r1,false,false)
        boom_fpf_regex (150,r2,false,false)
  end

let rec boom_fpf_statement
    (ppf:formatter)
    (s:boom_statement)
  : unit =
  begin match s with
    | BoomStmtDefinition(n,t,e) ->
      fpf ppf "@[<hv 2>let %a@ : %a =@ %a @]"
        ident (Id.string_of_id n)
        boom_fpf_typ t
        boom_fpf_expression e
    | BoomStmtTestRegex(r,s) ->
      fpf ppf "@[<hv 2>test matches_cex@ %a@ \"%a\" = true@]"
        boom_fpf_regex (113,r,false,false)
        ident (delimit_string s)
    | BoomStmtTestLens(l,s1,s2) ->
      fpf ppf "@[<hv 2>test %a.get@ \"%a\"@ = \"%a\"@]"
        boom_fpf_lens (113,l,false,false)
        ident (delimit_string s1)
        ident (delimit_string s2)
  end

and boom_fpf_expression
    (ppf:formatter)
    (e:boom_expression)
  : unit =
  begin match e with
    | BoomExpRegex r ->
      boom_fpf_regex ppf (0,r,false,false)
    | BoomExpLens l ->
      boom_fpf_lens ppf (0,l,false,false)
    | BoomExpCut(s,e') ->
      fpf ppf "@[<hv 0>%a in@ %a]"
        boom_fpf_statement s
        boom_fpf_expression e'
  end

let boom_pp_regex (r:Regex.t) : string =
  (boom_fpf_regex str_formatter (0, r, false, false); flush_str_formatter ())

let boom_pp_lens (l:Lens.t) : string =
  (boom_fpf_lens str_formatter (0, l, false, false); flush_str_formatter ())

let pp_typ (t:boom_typ) : string =
  (boom_fpf_typ str_formatter t; flush_str_formatter ())

let pp_expression (e:boom_expression) : string =
  (boom_fpf_expression str_formatter e; flush_str_formatter ())

let pp_statement (s:boom_statement) : string =
  (boom_fpf_statement str_formatter s; flush_str_formatter ())

let pp_program (p:boom_program) : string =
  String.concat
    ~sep:"\n\n"
    (List.map ~f:pp_statement p)
