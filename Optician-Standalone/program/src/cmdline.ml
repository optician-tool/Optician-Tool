open Stdlib
open Pp
open Lens_put
open Regexcontext
open Lenscontext
open Gen_exs
open Gen
open Lang
open Consts
open Typing
open Program_utilities
open Boom_lang
open Eval
open Converter
open Normalized_lang
open String_utilities
open Lens_utilities

let _ = Random.self_init

exception Arg_exception

type driver_mode =
  | Default
  | Parse
  | Synth
  | Time
  | GeneratedExamples
  | MaxSpecify
  | SpecSize
  | GenerateIOSpec
  | GenerateExtractionSpec
  | ExpansionsPerformed
  | SpecsVisited
  | ExpansionsInferred
  | ExpansionsForced
  | CompositionalLensesUsed
  | LensSize
  | LensAndSpecSize
  | PossibleLensesAtFinalLevelWithNExamples of int

let usage_msg = "synml [-help | opts...] <src>"
let filename : string option ref = ref None
let mode : driver_mode ref = ref Default

let rep_count = ref 0

let parse_file (f:string) : program =
  Preproc.preprocess_file f
    |> Lexing.from_string
    |> Parser.program Lexer.token

let set_opt (d:driver_mode) =
  match !mode with
  | Default -> mode := d
  | _ -> raise Arg_exception

let args =
  [ ( "-parse"
    , Arg.Unit (fun _ -> set_opt Parse)
    , " Parse only"
    )
  ; ( "-synth"
    , Arg.Unit (fun _ -> set_opt Synth)
    , " Synthesize"
    )
  ; ( "-time"
    , Arg.Unit (fun _ -> set_opt Time)
    , " Synthesize and collect statistics (time)"
    )
  ; ( "-generatedexamples"
    , Arg.Unit (fun _ -> set_opt GeneratedExamples)
    , " Synthesize with randomly generated examples"
    )
  ; ( "-forceexpand"
    , Arg.Unit (fun _ -> force_expand_regexps := true)
    , " Synthesize with definitions forced to be expanded"
    )
  ; ( "-iterativedeepenstrategy"
    , Arg.Unit (fun _ -> use_iterative_deepen_strategy := true)
    , " Set use of iterative deepen strategy"
    )
  ; ( "-max_to_specify"
    , Arg.Unit (fun _ -> set_opt MaxSpecify)
    , " Set to calculate the maximum number of examples to fully specify"
    )
  ; ( "-spec_size"
    , Arg.Unit (fun _ -> set_opt SpecSize)
    , " Set to calculate the size of the user input specification size"
    )
  ; ( "-lens_size"
    , Arg.Unit (fun _ -> set_opt LensSize)
    , " Set to calculate the size of the generated lens"
    )
  ; ( "-lens_and_spec_size"
    , Arg.Unit (fun _ -> set_opt LensAndSpecSize)
    , " Set to calculate the size of the generated lens and the spec"
    )
  ; ( "-naive_strategy"
    , Arg.Unit (fun _ -> naive_strategy := true)
    , " Set to use a naive synthesis strategy"
    )
  ; ( "-no_lens_context"
    , Arg.Unit (fun _ -> use_lens_context := false)
    , " Short circuit when distance is 0"
    )
  ; ( "-verbose"
    , Arg.Unit (fun _ -> verbose := true)
    , " Print out information about synthesis"
    )
  ; ( "-no_simplify_generated_lens"
    , Arg.Unit (fun _ -> simplify_generated_lens := false)
    , " Don't Simplify Lens generated lens"
    )
  ; ( "-naive_expansion_search"
    , Arg.Unit (fun _ -> use_naive_expansion_search := true)
    , " No inference of necessary expansions")
  ; ( "-use_only_forced_expansions"
    , Arg.Unit (fun _ -> use_only_forced_expansions := true)
    , " Only infer expansions that are completely forced")
  ; ( "-possible_lenses_ex"
      , Arg.Tuple [(Arg.Int (fun i -> set_opt (PossibleLensesAtFinalLevelWithNExamples i)));Arg.Set_int rep_count]
    , " Synthesize (#) randomly generated examples")
  ; ( "-generate_io_spec"
    , (Arg.Tuple [Arg.Unit (fun _ -> set_opt GenerateIOSpec)
          ;Arg.Set_int generate_io_count])
    , " Synthesize (#) randomly generated examples"
    )
  ; ( "-generate_extraction_spec"
    , (Arg.Tuple [Arg.Unit (fun _ -> set_opt GenerateExtractionSpec)
                 ;(Arg.Set_int generate_io_count)])
    , " Synthesize (#) randomly generated extraction problems"
    )
  ; ( "-expansions_performed"
    , Arg.Unit (fun _ -> set_opt ExpansionsPerformed)
    , " Set to calculate the number of expansions performed"
    )
  ; ( "-specs_visited"
    , Arg.Unit (fun _ -> set_opt SpecsVisited)
    , " Set to calculate the number of specs visited"
    )
  ; ( "-expansions_inferred"
    , Arg.Unit (fun _ -> set_opt ExpansionsInferred)
    , " Set to calculate the number of expansions inferred"
    )
  ; ( "-expansions_forced"
    , Arg.Unit (fun _ -> set_opt ExpansionsForced)
    , " Set to calculate the number of expansions inferred"
    )
  ; ( "-compositional_lenses_used"
    , Arg.Unit (fun _ -> set_opt CompositionalLensesUsed)
    , " Set to calculate the number of compositional lenses used"
    )
  ]
  |> Arg.align

let expand_regexps (p:program) : program =
  let rec expand_regexp (r:Regex.t) (c:RegexContext.t) : Regex.t =
    begin match r with
    | Regex.RegExEmpty -> r
    | Regex.RegExBase _ -> r
    | Regex.RegExConcat (r1,r2) -> Regex.RegExConcat (expand_regexp r1 c,expand_regexp r2 c)
    | Regex.RegExOr (r1,r2) -> Regex.RegExOr (expand_regexp r1 c,expand_regexp r2 c)
    | Regex.RegExStar r' -> Regex.RegExStar (expand_regexp r' c)
    | Regex.RegExVariable t ->
      let r' = RegexContext.lookup_exn c t in
      expand_regexp r' c
    end
  in
  let expand_regexps_decl (c:RegexContext.t)
                          (d:declaration)
                          : (RegexContext.t * declaration) =
    begin match d with
    | DeclRegexCreation (s,r,b) -> (RegexContext.insert_exn c s r b,d)
    | DeclTestString _ -> (c,d)
    | DeclSynthesizeLens (n,r1,r2,exs) ->
      (c,DeclSynthesizeLens (n,expand_regexp r1 c,expand_regexp r2 c,exs))
    | DeclLensCreation _ -> (c,d)
    | DeclTestLens _ -> (c,d)
    end
  in
  List.rev
  (snd
    (List.fold_left
      ~f:(fun (c,ds) d ->
        let (c,d') = expand_regexps_decl c d in
        (c,d'::ds))
      ~init:(RegexContext.empty,[])
      p))

let expand_regexps_if_necessary (p:program) : program =
  if !force_expand_regexps then
    expand_regexps p
  else
    p

let rec check_examples
    (rc:RegexContext.t)
    (lc:LensContext.t)
    (l:Lens.t)
    (exs:examples)
  : unit =
  begin match exs with
    | [] -> ()
    | (lex,rex)::exst ->
      if lens_putr rc lc l lex <> rex then
        failwith "put right didnt work"
      else if lens_putl rc lc l rex <> lex then
        failwith "put left didnt work"
      else
        check_examples rc lc l exst
  end

let print_lenses (lc:LensContext.t) (lss:(string * Lens.t option) list) : unit =
  List.iter
    ~f:(fun (s,lo) ->
      print_endline "\n\n";
      print_endline (s ^ ":");
      begin match lo with
      | None -> print_endline "no lens found"
      | Some ls -> print_endline (Lens.show ls);
        let (t1,t2) = type_lens lc ls in
        print_endline (Regex.show t1);
        print_endline (Regex.show t2)
      end)
    lss

let ignore (_:'a) : unit =
  ()


let collect_time (p:program) : unit =
  let (time, _) = time_action ~f:(fun _ -> synthesize_program p) in
  print_endline (Float.to_string time)

let collect_referenced_lenses (p:program) : unit =
  let (rc,lc,r1,r2,exs) = retrieve_last_synthesis_problem_exn p in
  let l = Option.value_exn (gen_lens rc lc r1 r2 exs) in
  let rec get_referenced_ls (l:Lens.t) : Id.t list =
    begin match l with
      | Lens.LensCompose (l1,l2) -> (get_referenced_ls l1)@(get_referenced_ls l2)
      | Lens.LensConst _ -> []
      | Lens.LensConcat (l1,l2) ->  (get_referenced_ls l1)@(get_referenced_ls l2)
      | Lens.LensInverse l' -> (get_referenced_ls l')
      | Lens.LensIdentity _ -> []
      | Lens.LensIterate l' -> (get_referenced_ls l')
      | Lens.LensPermute (_,ls) -> List.concat_map ~f:get_referenced_ls ls
      | Lens.LensUnion (l1,l2) -> (get_referenced_ls l1)@(get_referenced_ls l2)
      | Lens.LensSwap (l1,l2) -> (get_referenced_ls l1)@(get_referenced_ls l2)
      | Lens.LensVariable v -> v::(get_referenced_ls (LensContext.lookup_impl_exn lc v))
    end
  in
  print_endline (string_of_int (List.length (List.dedup ~compare:Id.compare (get_referenced_ls l))))

let collect_expansions_performed (p:program) : unit =
  let (rc,lc,r1,r2,exs) = retrieve_last_synthesis_problem_exn p in
  let exps_perfed = Option.value_exn (expansions_performed_for_gen rc lc r1 r2 exs) in
  print_endline (string_of_int exps_perfed)

let collect_specs_visited (p:program) : unit =
  let (rc,lc,r1,r2,exs) = retrieve_last_synthesis_problem_exn p in
  let specs_visited = Option.value_exn (specs_visited_for_gen rc lc r1 r2 exs) in
  print_endline (string_of_int specs_visited)

let collect_expansions_forced (p:program) : unit =
  let (rc,lc,r1,r2,exs) = retrieve_last_synthesis_problem_exn p in
  let exps_forced = Option.value_exn (expansions_forced_for_gen rc lc r1 r2 exs) in
  print_endline (string_of_int exps_forced)

let collect_expansions_inferred (p:program) : unit =
  let (rc,lc,r1,r2,exs) = retrieve_last_synthesis_problem_exn p in
  let exps_inferred = Option.value_exn (expansions_inferred_for_gen rc lc r1 r2 exs) in
  print_endline (string_of_int exps_inferred)

let collect_example_number (p:program) : unit =
  let current_total = ref 0 in
  let cb = fun (rc,lc,r1,r2,exs) ->
    let l = Option.value_exn (gen_lens rc lc r1 r2 exs) in
    let exs_required = fold_until_completion
        ~f:(fun acc ->
           let l' = Option.value_exn
               (gen_lens rc lc r1 r2 acc) in
           if l' = l then
             Right (List.length acc)
           else
             let leftex = gen_element_of_regex_language rc r1 in
             let rightex = lens_putr rc lc l leftex in
             let acc = (leftex,rightex)::acc in
             Left acc
        ) [] in
    current_total := !current_total + exs_required;
  in
  let _ = synthesize_and_load_program_with_callback
    p
    cb
  in
  print_endline (string_of_int !current_total)

let rec max_examples_required
    (rc:RegexContext.t)
    (lc:LensContext.t)
    (l:Lens.t)
  : int =
  let sum_list = List.fold_left ~f:(+) ~init:0 in
  let rec examples_required_o_ex_dnf_regex (o_ex_dr:ordered_exampled_dnf_regex) : int =
    let seq_list_list =
      List.map
        ~f:(fun l -> List.map ~f:fst l)
        o_ex_dr
    in
    let examples_required_list_list =
      List.map
        ~f:(fun l -> List.map ~f:examples_required_o_ex_sequence l)
        seq_list_list
    in
    let total_examples_list =
      List.map
        ~f:(fun l -> (List.length l - 1) + sum_list l)
        examples_required_list_list
    in
    sum_list total_examples_list
  and examples_required_o_ex_sequence (o_ex_sq:ordered_exampled_clause) : int =
    let (o_ex_a_i_list_list,_,_) = o_ex_sq in
    let atom_list_list =
      List.map
        ~f:(fun l -> List.map ~f:fst l)
        o_ex_a_i_list_list
    in
    let examples_required_list_list =
      List.map
        ~f:(fun l -> List.map ~f:examples_required_o_ex_atom l)
        atom_list_list
    in
    let total_examples_list =
      List.map
        ~f:(fun l -> (List.length l - 1) + sum_list l)
        examples_required_list_list
    in
    sum_list total_examples_list
  and examples_required_o_ex_atom (_:ordered_exampled_atom) : int =
    1
  in
  let rec referenced_lenses (l:Lens.t) : Lens.t list =
    begin match l with
      | Lens.LensConst _ -> []
      | Lens.LensConcat (l1,l2) -> (referenced_lenses l1) @ (referenced_lenses l2)
      | Lens.LensSwap (l1,l2) -> (referenced_lenses l1) @ (referenced_lenses l2)
      | Lens.LensUnion (l1,l2) -> (referenced_lenses l1) @ (referenced_lenses l2)
      | Lens.LensCompose (l1,l2) -> (referenced_lenses l1) @ (referenced_lenses l2)
      | Lens.LensIterate (l') -> (referenced_lenses l')
      | Lens.LensIdentity _ -> []
      | Lens.LensInverse l' -> (referenced_lenses l')
      | Lens.LensVariable v ->
        [LensContext.lookup_impl_exn lc v]
      | Lens.LensPermute (_,ll) ->
        List.concat_map ~f:referenced_lenses ll
    end
  in
  let (r,_) = type_lens lc l in
  let ex_r = Option.value_exn (regex_to_exampled_regex rc r []) in
  let ex_dr = exampled_regex_to_exampled_dnf_regex rc lc ex_r in
  let o_ex_dr = to_ordered_exampled_dnf_regex ex_dr in
  let ref_lenses = referenced_lenses l in
  let ref_lenses_exs = List.map ~f:(max_examples_required rc lc) ref_lenses in
  (examples_required_o_ex_dnf_regex o_ex_dr) + (sum_list ref_lenses_exs)
    
let collect_max_example_number (p:program) : unit =
  let (rc,lc,r1,r2,exs) = retrieve_last_synthesis_problem_exn p in
  let l = Option.value_exn (gen_lens rc lc r1 r2 exs) in
  let max_exs_required = max_examples_required rc lc l in
  print_endline (string_of_int max_exs_required)
    
let collect_extraction_spec (p:program) : unit =
  let (rc,lc,r1,r2,exs) = retrieve_last_synthesis_problem_exn p in
  let l = Option.value_exn (gen_lens rc lc r1 r2 exs) in
  let rec collect_extraction_spec_internal
      (n:int)
      ((r,(v,f)):Regex.t * (Id.t * flattened_or_var_regex))
    : unit =
    if (n <= 0) then
      ()
    else
      let tsv_delimit = fun s -> delimit_tabs (delimit_newlines (delimit_slashes s)) in
      let (s,on,off) = gen_element_and_on_off_portions_of_flattened_or_var_regex f in
      if List.is_empty on then
        collect_extraction_spec_internal (n-1) (r,(v,f))
      else
        let prob_var_for_tsv =
          tsv_delimit (string_of_pair Regex.show Id.show (r,v))
        in
        let s_for_tsv = tsv_delimit s in
        let on_for_tsv =
          String.concat
            ~sep:";"
            (List.map
               ~f:(fun (i,j) -> (string_of_int i) ^ "," ^ (string_of_int j))
               on)
        in
        let off_for_tsv =
          String.concat
            ~sep:";"
            (List.map
               ~f:(fun (i,j) -> (string_of_int i) ^ "," ^ (string_of_int j))
               off)
        in
        let prob_s_on_off_for_tsv =
          prob_var_for_tsv ^ "\t" ^
          s_for_tsv ^ "\t" ^
          on_for_tsv ^ "\t" ^
          off_for_tsv
        in
        print_endline prob_s_on_off_for_tsv;
        collect_extraction_spec_internal (n-1) (r,(v,f))
  in
  let all_relevant_lenses = retrieve_transitive_referenced_lenses lc l in
  let all_relevant_inputtypes =
    List.map
      ~f:(fun l -> fst (type_lens lc l))
      all_relevant_lenses
  in
  let all_ud_focusings =
    List.concat_map
      ~f:(fun it ->
          List.map
            ~f:(fun fr -> (it,fr))
            (get_var_focused_flattened_regexs rc it))
      all_relevant_inputtypes
  in
  List.iter
    ~f:(collect_extraction_spec_internal !generate_io_count)
    all_ud_focusings
  
    
let collect_final_io_spec (p:program) : unit =
  let (rc,lc,r1,r2,exs) = retrieve_last_synthesis_problem_exn p in
  let l = Option.value_exn (gen_lens rc lc r1 r2 exs) in
  let rec collect_final_io_spec_internal
      (n:int)
    : unit =
    if (n <= 0) then
      ()
    else
      let leftex = gen_element_of_regex_language rc r1 in
      let rightex = lens_putr rc lc l leftex in
      print_endline (((delimit_tabs (delimit_newlines (delimit_slashes leftex))) ^ "\t" ^ ((delimit_tabs (delimit_newlines (delimit_slashes rightex))))));
      collect_final_io_spec_internal (n-1)
  in
  collect_final_io_spec_internal !generate_io_count

let rec retrieve_transitive_regexp_vars (rc:RegexContext.t) (r:Regex.t) : Id.t list =
  begin match r with
    | Regex.RegExEmpty -> []
    | Regex.RegExBase _ -> []
    | Regex.RegExConcat (r1,r2) ->
      (retrieve_transitive_regexp_vars rc r1)
      @ (retrieve_transitive_regexp_vars rc r2)
    | Regex.RegExOr (r1,r2) -> (retrieve_transitive_regexp_vars rc r1) @
                               (retrieve_transitive_regexp_vars rc r2)
    | Regex.RegExStar r' -> retrieve_transitive_regexp_vars rc r'
    | Regex.RegExVariable t ->
      t::(begin match RegexContext.lookup_for_expansion_exn rc t with
          | None -> []
          | Some rex -> retrieve_transitive_regexp_vars rc rex
        end)
  end

let number_of_examples_at_satisfying_level (i:int) (p:program) : unit =
  let cs = List.init
      ~f:(fun _ -> let (rc,lc,r1,r2,exs) = retrieve_last_synthesis_problem_exn p in
           let l = Option.value_exn (gen_lens rc lc r1 r2 exs) in
           let exs =
             List.init ~f:(fun _ ->
                 let leftex = gen_element_of_regex_language rc r1 in
                 let rightex = lens_putr rc lc l leftex in
                 (leftex,rightex))
               i
           in
           Option.value_exn (num_possible_choices rc lc r1 r2 exs))
      !rep_count
  in
  print_endline
    (Float.to_string
    ((List.fold_left
        ~f:(+.)
        ~init:0.0
        cs) /. (Float.of_int !rep_count)))


let lens_size (p:program) : unit =
  let (rc,lc,r1,r2,exs) = retrieve_last_synthesis_problem_exn p in
  let l = Option.value_exn (gen_lens rc lc r1 r2 exs) in
  let rec retrieve_transitive_vars (l:Lens.t) : Id.t list =
    begin match l with
      | Lens.LensConst(_,_) -> []
      | Lens.LensConcat(l1,l2) ->
        (retrieve_transitive_vars l1) @
        (retrieve_transitive_vars l2)
      | Lens.LensSwap (l1,l2) ->
        (retrieve_transitive_vars l1) @
        (retrieve_transitive_vars l2)
      | Lens.LensUnion (l1,l2) ->
        (retrieve_transitive_vars l1) @
        (retrieve_transitive_vars l2)
      | Lens.LensCompose (l1,l2) ->
        (retrieve_transitive_vars l1) @
        (retrieve_transitive_vars l2)
      | Lens.LensIterate l' ->
        retrieve_transitive_vars l'
      | Lens.LensIdentity _ -> []
      | Lens.LensInverse l' ->
        retrieve_transitive_vars l'
      | Lens.LensVariable v -> v::(retrieve_transitive_vars (LensContext.lookup_impl_exn lc v))
      | Lens.LensPermute (_,ls) ->
        List.concat_map
          ~f:retrieve_transitive_vars
          ls
    end
  in
  let rec retrieve_regexps_from_lens
      (l:Lens.t)
    : Regex.t list =
    begin match l with
      | Lens.LensConst(_,_) -> []
      | Lens.LensConcat(l1,l2) ->
        (retrieve_regexps_from_lens l1) @
        (retrieve_regexps_from_lens l2)
      | Lens.LensSwap (l1,l2) ->
        (retrieve_regexps_from_lens l1) @
        (retrieve_regexps_from_lens l2)
      | Lens.LensUnion (l1,l2) ->
        (retrieve_regexps_from_lens l1) @
        (retrieve_regexps_from_lens l2)
      | Lens.LensCompose (l1,l2) ->
        (retrieve_regexps_from_lens l1) @
        (retrieve_regexps_from_lens l2)
      | Lens.LensIterate l' ->
        retrieve_regexps_from_lens l'
      | Lens.LensIdentity v -> [v]
      | Lens.LensInverse l' ->
        retrieve_regexps_from_lens l'
      | Lens.LensVariable v -> retrieve_regexps_from_lens (LensContext.lookup_impl_exn lc v)
      | Lens.LensPermute (_,ls) ->
        List.concat_map
          ~f:retrieve_regexps_from_lens
          ls
    end
  in
  let all_vars = retrieve_transitive_vars l in
  let all_lenses =
    List.dedup(
      l::(List.map ~f:(fun v ->
          (LensContext.lookup_impl_exn lc v))
          all_vars))
  in
  let all_sizes =
    List.map ~f:(fun l -> Lens.size l) all_lenses
  in
  let referred_regexps = (retrieve_regexps_from_lens l) in
  let relevant_regexps =
    List.dedup
      (referred_regexps
       @
       (List.map
          ~f:(fun v -> RegexContext.lookup_exn rc v)
          (List.concat_map
             ~f:(retrieve_transitive_regexp_vars rc)
             referred_regexps)))
  in
  let regexp_sizes =
    List.map ~f:(Regex.size) relevant_regexps
  in
  let regex_size =
    List.fold_left
      ~f:(+)
      ~init:0
      regexp_sizes
  in
  let mysize =
    regex_size
    + 
    (List.fold_left
       ~f:(+)
       ~init:0
       all_sizes)
  in

  print_endline (string_of_int (mysize))

let specification_size (p:program) : unit =
  let (rc,_,r1,r2,_) = retrieve_last_synthesis_problem_exn p in
  let all_vars = (retrieve_transitive_regexp_vars rc r1) @
                     (retrieve_transitive_regexp_vars rc r2) in
  let all_regexps =
    List.dedup(
      r1::r2::(List.map ~f:(fun s ->
          (RegexContext.lookup_exn rc s))
          all_vars))
  in
  let all_sizes =
    List.map ~f:(fun r -> Regex.size r) all_regexps
  in
  let mysize = List.fold_left
    ~f:(+)
    ~init:0
    all_sizes
  in

  print_endline (string_of_int (mysize))

let lens_and_spec_size (p:program) : unit =
  let (rc,lc,r1,r2,exs) = retrieve_last_synthesis_problem_exn p in
  let l = Option.value_exn (gen_lens rc lc r1 r2 exs) in
  let rec retrieve_transitive_vars (l:Lens.t) : Id.t list =
    begin match l with
      | Lens.LensConst(_,_) -> []
      | Lens.LensConcat(l1,l2) ->
        (retrieve_transitive_vars l1) @
        (retrieve_transitive_vars l2)
      | Lens.LensSwap (l1,l2) ->
        (retrieve_transitive_vars l1) @
        (retrieve_transitive_vars l2)
      | Lens.LensUnion (l1,l2) ->
        (retrieve_transitive_vars l1) @
        (retrieve_transitive_vars l2)
      | Lens.LensCompose (l1,l2) ->
        (retrieve_transitive_vars l1) @
        (retrieve_transitive_vars l2)
      | Lens.LensIterate l' ->
        retrieve_transitive_vars l'
      | Lens.LensIdentity _ -> []
      | Lens.LensInverse l' ->
        retrieve_transitive_vars l'
      | Lens.LensVariable v -> v::(retrieve_transitive_vars (LensContext.lookup_impl_exn lc v))
      | Lens.LensPermute (_,ls) ->
        List.concat_map
          ~f:retrieve_transitive_vars
          ls
    end
  in
  let rec retrieve_regexps_from_lens
      (l:Lens.t)
    : Regex.t list =
    begin match l with
      | Lens.LensConst(_,_) -> []
      | Lens.LensConcat(l1,l2) ->
        (retrieve_regexps_from_lens l1) @
        (retrieve_regexps_from_lens l2)
      | Lens.LensSwap (l1,l2) ->
        (retrieve_regexps_from_lens l1) @
        (retrieve_regexps_from_lens l2)
      | Lens.LensUnion (l1,l2) ->
        (retrieve_regexps_from_lens l1) @
        (retrieve_regexps_from_lens l2)
      | Lens.LensCompose (l1,l2) ->
        (retrieve_regexps_from_lens l1) @
        (retrieve_regexps_from_lens l2)
      | Lens.LensIterate l' ->
        retrieve_regexps_from_lens l'
      | Lens.LensIdentity v -> [v]
      | Lens.LensInverse l' ->
        retrieve_regexps_from_lens l'
      | Lens.LensVariable v -> retrieve_regexps_from_lens (LensContext.lookup_impl_exn lc v)
      | Lens.LensPermute (_,ls) ->
        List.concat_map
          ~f:retrieve_regexps_from_lens
          ls
    end
  in
  let all_vars = retrieve_transitive_vars l in
  let all_lenses =
    List.dedup(
      l::(List.map ~f:(fun v ->
          (LensContext.lookup_impl_exn lc v))
          all_vars))
  in
  let all_sizes =
    List.map ~f:(fun l -> Lens.size l) all_lenses
  in
  let referred_regexps = r1::r2::(retrieve_regexps_from_lens l) in
  let relevant_regexps =
    List.dedup
      (referred_regexps
       @
       (List.map
          ~f:(fun v -> RegexContext.lookup_exn rc v)
          (List.concat_map
             ~f:(retrieve_transitive_regexp_vars rc)
             referred_regexps)))
  in
  let regexp_sizes =
    List.map ~f:(Regex.size) relevant_regexps
  in
  let regex_size =
    List.fold_left
      ~f:(+)
      ~init:0
      regexp_sizes
  in
  let mysize =
    regex_size
    + 
    (List.fold_left
       ~f:(+)
       ~init:0
       all_sizes)
  in

  print_endline (string_of_int (mysize))

let print_outputs (p:program) : unit =
  print_endline "module Generated =";
  let (_,lc,p) = synthesize_and_load_program p in
  let bp = boom_program_of_program lc p in
  print_endline (pp_program bp)

let main () =
  begin try
    Arg.parse args (fun s ->
      match !filename with
      | Some _ -> raise Arg_exception
      | None -> filename := Some s) usage_msg
  with
    Arg_exception -> Arg.usage args usage_msg
  end;
  match !filename with
  | None   -> Arg.usage args usage_msg
  | Some f ->
    begin match Sys.file_exists f with
      | `No | `Unknown -> Arg.usage args ("File not found: " ^ f)
      | `Yes -> begin match !mode with
          | Parse ->
            let _ = parse_file f in (*TODO: pp*) ()(*Printf.printf "%s\n"
                                                     (Pp.pp_prog prog)*)
          | Time -> parse_file f |> expand_regexps_if_necessary |> collect_time
          | GeneratedExamples ->
            parse_file f
            |> expand_regexps_if_necessary
            |> collect_example_number
          | MaxSpecify ->
            parse_file f
            |> expand_regexps_if_necessary
            |> collect_max_example_number
          | Default | Synth ->
            parse_file f |> expand_regexps_if_necessary |> print_outputs
          | SpecSize ->
            parse_file f |> expand_regexps_if_necessary |> specification_size
          | LensSize ->
            parse_file f |> expand_regexps_if_necessary |> lens_size
          | CompositionalLensesUsed ->
            parse_file f |> expand_regexps_if_necessary |> collect_referenced_lenses
          | GenerateIOSpec ->
            parse_file f
            |> expand_regexps_if_necessary
            |> collect_final_io_spec
          | GenerateExtractionSpec ->
            parse_file f
            |> expand_regexps_if_necessary
            |> collect_extraction_spec
          | ExpansionsPerformed ->
            parse_file f |> expand_regexps_if_necessary |> collect_expansions_performed
          | SpecsVisited ->
            parse_file f |> expand_regexps_if_necessary |> collect_specs_visited
          | ExpansionsInferred ->
            parse_file f |> expand_regexps_if_necessary |> collect_expansions_inferred
          | ExpansionsForced ->
            parse_file f |> expand_regexps_if_necessary |> collect_expansions_forced
          | LensAndSpecSize ->
            parse_file f |> expand_regexps_if_necessary |> lens_and_spec_size
          | PossibleLensesAtFinalLevelWithNExamples i ->
            parse_file f |> expand_regexps_if_necessary |> (number_of_examples_at_satisfying_level i)
        end
    end

let () = if not !Sys.interactive then main ()
