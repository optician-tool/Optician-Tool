open Stdlib
open Normalized_lang
open Lang
open String_utilities
open Ounit_general_extensions
open Boom_lang
open Gen_exs
open Expand
open Tree_alignment


let assert_dnf_equal (expected:dnf_regex) (actual:dnf_regex) =
  assert_equal
    ~printer:dnf_regex_to_string
    ~cmp:compare_dnf_regexs
    expected
    actual

let assert_swap_concat_compose_tree_equal =
  assert_equal
    ~printer:Permutation.pp_swap_concat_compose_tree
    ~cmp:Permutation.compare_swap_concat_compose_tree

let assert_permutation_option_equal =
  assert_equal
    ~printer:(fun x -> begin match x with
        | None -> "None"
        | Some p -> "Some " ^ (Permutation.show p)
      end)

let assert_permutation_guesses_option_equal =
  assert_equal
    ~printer:(fun x -> begin match x with
        | None -> "None"
        | Some (p,g) ->
          "Some (" ^
          (Permutation.show p) ^ "   ,   [" ^
          String.concat
            ~sep:" ; "
            (List.map
               ~f:(fun (i,j) -> (string_of_int i) ^ "->" ^ (string_of_int
                                                              j))
               g)
          ^ "])"
      end)
    ~cmp:(option_compare
            (pair_compare
               Permutation.compare
               (compare_list
                  ~cmp:(pair_compare compare_int compare_int))))

let assert_lens_equal =
  assert_equal
    ~printer:Lens.show
    ~cmp:Lens.compare

let assert_dnf_lens_option_equal =
  assert_equal
    ~printer:(String_utilities.string_of_option dnf_lens_to_string)
    ~cmp:(option_compare compare_dnf_lens)

let assert_exampled_dnf_option_equal =
  assert_equal
    ~printer:(string_of_option exampled_dnf_regex_to_string)
    ~cmp:(option_compare compare_exampled_dnf_regexs)

let assert_dnf_lens_equal =
  assert_equal
    ~printer:dnf_lens_to_string

let assert_regex_list_equal =
  assert_equal
    ~printer:(fun rs -> "[" ^
                        (String.concat
                           ~sep:";"
                           (List.map ~f:Regex.show rs))
                        ^ "]")

let assert_regex_equal =
  assert_equal
    ~printer:Regex.show
    ~cmp:Regex.compare

let assert_regex_option_equal =
  assert_equal
    ~printer:(string_of_option Regex.show)

let assert_lens_regex_regex_equal =
  assert_equal
    ~printer:(string_of_triple Lens.show Regex.show Regex.show)
    ~cmp:(triple_compare Lens.compare Regex.compare Regex.compare)

let assert_regex_regex_equal =
  assert_equal
    ~printer:(string_of_pair Regex.show Regex.show)
    ~cmp:(pair_compare Regex.compare Regex.compare)

let assert_lens_list_equal =
  assert_equal
    ~printer:(string_of_list Lens.show)
    ~cmp:(compare_list ~cmp:Lens.compare)

let assert_id_lens_list_equal =
  assert_equal
    ~printer:(string_of_pair ident (string_of_list Lens.show))
    ~cmp:(pair_compare compare_string (compare_list ~cmp:Lens.compare))

let assert_id_lens_equal =
  assert_equal
    ~printer:(string_of_pair Id.show Lens.show)
    ~cmp:(pair_compare Id.compare Lens.compare)

let assert_boom_statement_equal =
  assert_equal
    ~printer:Pp.pp_statement
    ~cmp:compare_boom_statement

let assert_boom_expression_equal =
  assert_equal
    ~printer:Pp.pp_expression
    ~cmp:compare_boom_expression

let assert_boom_program_equal =
  assert_equal
    ~printer:Pp.pp_program
    ~cmp:compare_boom_program

module ModTenPQueue = PriorityQueueOf(
  struct
    include IntModule
    let priority = (fun x -> Float.of_int (x mod 10))
  end)

let assert_int_int_int_priority_queue_option_equal =
  let printer =
    string_of_option
      (string_of_triple
         string_of_int
         string_of_float
         ModTenPQueue.show)
  in
  let comparer =
    option_compare
      (triple_compare
         compare
         compare
         ModTenPQueue.compare)
  in
  assert_equal
    ~printer:printer
    ~cmp:comparer

let assert_required_expansions_equal =
  let printer =
    (string_of_triple
       Regex.show
       Regex.show
       string_of_int)
  in
  let comparer =
    (triple_compare
       Regex.compare
       Regex.compare
       compare)
  in
  assert_equal
    ~printer:printer
    ~cmp:comparer

module RegexIntSet = SetOf(
  struct
    type t = Regex.t * int
    [@@deriving ord, show, hash]
  end)

let assert_expansions_equal
    (ri1s:(Regex.t * int) list)
    (ri2s:(Regex.t * int) list) =
  let printer = string_of_list (string_of_pair Regex.show string_of_int) in
  assert_equal
    ~printer:printer
    ~cmp:(ordered_partition_order (pair_compare Regex.compare compare_int))
    ri1s
    ri2s

let assert_double_expansions_equal
    (ri1s:(Regex.t * Regex.t * int) list)
    (ri2s:(Regex.t * Regex.t * int) list) =
  let printer = string_of_list
      (string_of_triple Regex.show Regex.show string_of_int)
  in
  assert_equal
    ~printer:printer
    ~cmp:(ordered_partition_order
            (triple_compare Regex.compare Regex.compare compare_int))
    ri1s
    ri2s


let assert_ordered_string_assoc_list_equal =
  assert_equal
    ~printer:(string_of_list (string_of_pair ident string_of_int))
    ~cmp:(compare_list ~cmp:(pair_compare compare_string compare_int))

let assert_string_int_int_pair_list_pair_equal =
  assert_equal
    ~printer:(string_of_pair
                ident
                (string_of_list
                   (string_of_pair string_of_int string_of_int)))
    ~cmp:(pair_compare
            compare_string
            (compare_list
               ~cmp:(pair_compare compare_int compare_int)))

let assert_id_flattened_or_var_regex_list_equal =
  assert_equal
    ~printer:(string_of_list
                (string_of_pair
                   Id.show
                   flattened_or_var_regex_to_string))
    ~cmp:(compare_list ~cmp:(pair_compare Id.compare compare_flattened_or_var_regex))

let assert_int_int_list_equal =
  assert_equal
    ~printer:(string_of_list (string_of_pair string_of_int string_of_int))
    ~cmp:(compare_list ~cmp:(pair_compare compare_int compare_int))


let assert_transitive_set_equal =
  assert_equal
    ~printer:IdToIntSetDict.show
    ~cmp:IdToIntSetDict.compare

let assert_reachables_set_minus_equal =
  assert_equal
    ~printer:(string_of_pair IdIntSet.show IdIntSet.show)
    ~cmp:(pair_compare IdIntSet.compare IdIntSet.compare)

module IntTreeAlignment = TreeAlignmentOf(IntModule)

let assert_int_tree_alignment_equal =
  assert_equal
    ~printer:IntTreeAlignment.show
    ~cmp:IntTreeAlignment.compare
