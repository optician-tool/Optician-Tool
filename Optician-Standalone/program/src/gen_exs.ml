open Stdlib
open Lang
open Regexcontext
open String_utilities

let likelihood_of_continuing_star = 0.6

type flattened_or_var_regex = (bool * sum_flattened_or_var_regex)

and sum_flattened_or_var_regex =
   | FRegExEmpty
   | FRegExBase of string
   | FRegExConcat of flattened_or_var_regex * flattened_or_var_regex
   | FRegExOr of flattened_or_var_regex list
   | FRegExStar of flattened_or_var_regex
    
let make_flattened_concat
    (fr1:flattened_or_var_regex)
    (fr2:flattened_or_var_regex)
  : flattened_or_var_regex =
  begin match (fr1,fr2) with
    | ((_,FRegExEmpty),_) -> (false,FRegExEmpty)
    | (_,(_,FRegExEmpty)) -> (false,FRegExEmpty)
    | _               -> (false,FRegExConcat(fr1,fr2))
  end

let make_flattened_or
    (fr1:flattened_or_var_regex)
    (fr2:flattened_or_var_regex)
  : flattened_or_var_regex =
  begin match (fr1,fr2) with
    | ((_,FRegExEmpty),_) -> fr2
    | (_,(_,FRegExEmpty)) -> fr1
    | ((b1,FRegExOr frl1),(b2,FRegExOr frl2)) ->
      (false,FRegExOr
         ((List.map ~f:(fun (b,ofr) -> (b || b1,ofr)) frl1)
          @ (List.map ~f:(fun (b,ofr) -> (b || b2,ofr)) frl2)))
    | ((b,FRegExOr frl),_) ->
      (false,
       FRegExOr
         (fr2::
          (List.map ~f:(fun (b',fr) -> (b||b',fr)) frl)))
    | (_,(b,FRegExOr frl)) ->
      (false,
       FRegExOr
         (fr1::
          (List.map ~f:(fun (b',fr) -> (b||b',fr)) frl)))
    | _ -> (false,FRegExOr [fr1;fr2])
  end

let rec to_flattened_or_var_regex_relevant_important
    (rc:RegexContext.t)
    (r:Regex.t)
    (imp:Id.t)
  : flattened_or_var_regex =
  begin match r with
    | Regex.RegExEmpty -> (false,FRegExEmpty)
    | Regex.RegExBase s -> (false,FRegExBase s)
    | Regex.RegExConcat (r1,r2) ->
      make_flattened_concat
        (to_flattened_or_var_regex_relevant_important rc r1 imp)
        (to_flattened_or_var_regex_relevant_important rc r2 imp)
    | Regex.RegExOr (r1,r2) ->
      make_flattened_or
        (to_flattened_or_var_regex_relevant_important rc r1 imp)
        (to_flattened_or_var_regex_relevant_important rc r2 imp)
    | Regex.RegExStar r' ->
      (false,FRegExStar (to_flattened_or_var_regex_relevant_important rc r' imp))
    | Regex.RegExVariable v ->
      let r' = RegexContext.lookup_exn rc v in
      let sub_ofr = snd (to_flattened_or_var_regex_relevant_important rc r' v) in
      (v = imp, sub_ofr)
  end

let rec to_flattened_or_var_regex
    (rc:RegexContext.t)
    (r:Regex.t)
  : flattened_or_var_regex =
  begin match r with
    | Regex.RegExEmpty -> (false,FRegExEmpty)
    | Regex.RegExBase s -> (false,FRegExBase s)
    | Regex.RegExConcat (r1,r2) ->
      make_flattened_concat
        (to_flattened_or_var_regex rc r1)
        (to_flattened_or_var_regex rc r2)
    | Regex.RegExOr (r1,r2) ->
      make_flattened_or
        (to_flattened_or_var_regex rc r1)
        (to_flattened_or_var_regex rc r2)
    | Regex.RegExStar r' ->
      (false,FRegExStar (to_flattened_or_var_regex rc r'))
    | Regex.RegExVariable v ->
      let r' = RegexContext.lookup_exn rc v in
      to_flattened_or_var_regex rc r'
  end

let rec flattened_or_var_regex_to_string
  (fro:flattened_or_var_regex)
  : string =
  string_of_pair
    string_of_bool
    sum_flattened_or_var_regex_to_string
    fro


and sum_flattened_or_var_regex_to_string
    (sr:sum_flattened_or_var_regex)
  : string =
  begin match sr with
    | FRegExEmpty -> "FRegExEmpty"
    | FRegExBase s -> "FRegExBase" ^ "\"" ^ s ^ "\""
    | FRegExConcat (fr1,fr2) ->
      "FRegExConcat" ^
      (string_of_pair
         flattened_or_var_regex_to_string
         flattened_or_var_regex_to_string
         (fr1,fr2))
    | FRegExOr frl ->
      "FRegExOr" ^
      (string_of_list
         flattened_or_var_regex_to_string
         frl)
    | FRegExStar (fr') ->
      "FRegExStar" ^
      (paren (flattened_or_var_regex_to_string fr') ^ "*")
      
  end

let compare_flattened_or_var_regex : flattened_or_var_regex comparer =
  compare


let gen_element_and_on_portions_of_flattened_or_var_regex
    (fr:flattened_or_var_regex)
  : string * ((int * int) list) =
  let rec geoop_of_flattened_or_var_regex_internal
      ((is_var,sr):flattened_or_var_regex)
      (start_index:int)
      (on_portions_acc:(int * int) list)
    : string * ((int * int) list) * int =
    let (s,il,end_index) =
      geoop_of_sum_flattened_or_var_regex_internal
        sr
        start_index
        on_portions_acc
    in
    if is_var then
      (s,(start_index,end_index)::il,end_index)
    else
      (s,il,end_index)
  and geoop_of_sum_flattened_or_var_regex_internal
      (sr:sum_flattened_or_var_regex)
      (start_index:int)
      (on_portions_acc:(int * int) list)
    : string * ((int * int) list) * int =
    begin match sr with
      | FRegExBase s -> (s,on_portions_acc,start_index+String.length s)
      | FRegExConcat (fr1,fr2) ->
        let (s1,on_portions_acc,end_index) =
          geoop_of_flattened_or_var_regex_internal
            fr1
            start_index
            on_portions_acc
        in
        let (s2,on_portions_acc,end_index) =
          geoop_of_flattened_or_var_regex_internal
            fr2
            end_index
            on_portions_acc
        in
        (s1^s2,on_portions_acc,end_index)
      | FRegExOr frl ->
        let or_num = Random.int (List.length frl) in
        geoop_of_flattened_or_var_regex_internal
          (List.nth_exn frl or_num)
          start_index
          on_portions_acc
      | FRegExStar fr ->
        if Random.float 1.0 < likelihood_of_continuing_star then
          let (s1,on_portions_acc,end_index) =
            geoop_of_flattened_or_var_regex_internal
              fr
              start_index
              on_portions_acc
          in
          let (s2,on_portions_acc,end_index) =
            geoop_of_sum_flattened_or_var_regex_internal
              sr
              end_index
              on_portions_acc
          in
          (s1 ^ s2,on_portions_acc,end_index)
        else
          ("",on_portions_acc,start_index)
      | FRegExEmpty ->
        failwith "no elements of this language"
    end
  in
  let (x,l,_) = geoop_of_flattened_or_var_regex_internal fr 0 [] in
  (x,List.filter ~f:(fun (l,r) -> l <> r) l)
    
let gen_element_of_regex_language
    (rc:RegexContext.t)
    (r:Regex.t)
  : string =
  let (s,_) =
    (gen_element_and_on_portions_of_flattened_or_var_regex
       (to_flattened_or_var_regex rc r))
  in
  s

let calculate_off_portions
    (size:int)
    (on_portions:(int * int) list)
  : (int * int) list =
  let (final_left,off_portions) = List.fold_left
      ~f:(fun (left_index,acc) (onl,onr) ->
          (onr,(left_index,onl)::acc))
      ~init:(0,[])
      on_portions
  in
  List.rev
    (List.filter
       ~f:(fun (l,r) -> l <> r)
       ((final_left,size)::off_portions))

let gen_element_and_on_off_portions_of_flattened_or_var_regex
    (fr:flattened_or_var_regex)
  : string * (int * int) list * (int * int) list =
  let (s,on_portions) =
    (gen_element_and_on_portions_of_flattened_or_var_regex fr)
  in
  let ordered_on_portions =
    List.sort
      ~cmp:(fun (x1,_) (x2,_) -> x1 - x2)
      on_portions
  in
  let off_portions =
    calculate_off_portions
      (String.length s)
      ordered_on_portions
  in
  (s,ordered_on_portions,off_portions)

let get_var_focused_flattened_regexs
    (rc:RegexContext.t)
    (r:Regex.t)
  : (Id.t * flattened_or_var_regex) list =
  let rec get_all_vars
      (r:Regex.t)
    : Id.t list =
    begin match r with
      | Regex.RegExEmpty -> []
      | Regex.RegExBase _ -> []
      | Regex.RegExConcat (r1,r2) ->
        (get_all_vars r1)@(get_all_vars r2)
      | Regex.RegExOr (r1,r2) ->
        (get_all_vars r1)@(get_all_vars r2)
      | Regex.RegExStar r' ->
        get_all_vars r'
      | Regex.RegExVariable v -> [v]
    end
  in
  let all_vars = List.dedup (get_all_vars r) in
  List.map
    ~f:(fun ud -> (ud,to_flattened_or_var_regex_relevant_important rc r ud))
    all_vars
