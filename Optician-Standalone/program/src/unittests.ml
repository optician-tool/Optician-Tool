open Stdlib
open Normalized_lang
open Converter
open Counters
open Regexcontext
open Language_equivalences
open Lenscontext
open Lens_utilities
open Permutation
open Ounit_extensions
open Ounit_general_extensions
open OUnit2
open Eval
open Lang
open Gen
open Lens_put
open Boom_lang
open Gen_exs
open Expand

let test_to_normalized_exp_base _ =
  assert_dnf_equal
    (to_dnf_regex (Regex.RegExBase "x"))
    [([],["x"])]

let test_to_normalized_exp_concat_easy _ =
  assert_dnf_equal
    [([],["ab"])]
    (to_dnf_regex
      (Regex.RegExConcat
        (Regex.RegExBase "a",
        Regex.RegExBase "b")))
    
let test_to_normalized_exp_concat_tree _ =
  assert_dnf_equal
    [([],["abcde"])]
    (to_dnf_regex
      (Regex.RegExConcat
        (Regex.RegExConcat
          (Regex.RegExBase "a",
          Regex.RegExBase "b"),
        Regex.RegExConcat
          (Regex.RegExBase "c",
          Regex.RegExConcat
            (Regex.RegExBase "d",
            Regex.RegExBase "e")))))

let test_to_normalized_exp_union_tree _ =
  assert_dnf_equal
    [([],["a"]);([],["b"]);([],["c"]);([],["d"]);([],["e"])]
    (to_dnf_regex
      (Regex.RegExOr
        (Regex.RegExOr
          (Regex.RegExBase "a",
          Regex.RegExBase "b"),
        Regex.RegExOr
          (Regex.RegExBase "c",
          Regex.RegExOr
            (Regex.RegExBase "d",
            Regex.RegExBase "e")))))

let test_to_normalized_exp_append_distributeconcat _ =
  assert_dnf_equal
    (to_dnf_regex
      (Regex.RegExConcat
        (Regex.RegExConcat
          (Regex.RegExBase "a",
          Regex.RegExOr
            (Regex.RegExBase "b",
            Regex.RegExBase "c")),
        Regex.RegExBase "d")))
    [([],["abd"]);([],["acd"])]

let test_to_normalized_exp_complicated _ =
  assert_dnf_equal
  ([([],["abg"]);([AStar ([([],["cdf"]);([],["cef"])])],["a";"g"])])
    (to_dnf_regex
    (Regex.RegExConcat
      (Regex.RegExConcat
        (Regex.RegExBase "a",
          Regex.RegExOr
            (Regex.RegExBase "b",
            Regex.RegExStar
              (Regex.RegExConcat
                (Regex.RegExConcat
                  (Regex.RegExBase "c",
                  Regex.RegExOr
                    (Regex.RegExBase "d",
                    Regex.RegExBase "e")),
                Regex.RegExBase "f")))),
         Regex.RegExBase "g")))


let to_normalized_exp_suite = "to_normalized_exp Unit Tests" >:::
  ["test_to_normalized_exp_base" >:: test_to_normalized_exp_base;
   "test_to_normalized_exp_concat_easy" >:: test_to_normalized_exp_concat_easy;
   "test_to_normalized_exp_concat_tree" >:: test_to_normalized_exp_concat_tree;
   "test_to_normalized_exp_union_tree" >:: test_to_normalized_exp_union_tree;
   "test_to_normalized_exp_append_distributeconcat" >:: test_to_normalized_exp_append_distributeconcat;
   "test_to_normalized_exp_complicated" >:: test_to_normalized_exp_complicated]

let _ = run_test_tt_main to_normalized_exp_suite



let test_counters_add_same _ =
  assert_ordered_string_assoc_list_equal
    [("a",2)]
    (Counters.as_ordered_assoc_list (Counters.add (Counters.add (Counters.create
    compare_string) "a") "a"))

let test_counters_add_different _ =
  assert_ordered_string_assoc_list_equal
    [("a",1);("b",1)]
    (Counters.as_ordered_assoc_list (Counters.add (Counters.add (Counters.create
    compare_string) "a") "b"))

let test_counters_add_different_rev _ =
  assert_ordered_string_assoc_list_equal
    [("a",1);("b",1)]
    (Counters.as_ordered_assoc_list (Counters.add (Counters.add (Counters.create
    compare_string) "b") "a"))

let test_counters_merge_same _ =
  assert_ordered_string_assoc_list_equal
    [("a",2)]
    (Counters.as_ordered_assoc_list ((Counters.merge (fun x y -> x+y) (Counters.add (Counters.create compare_string) "a")
    (Counters.add (Counters.create compare_string) "a"))))

let test_counters_merge_different _ =
  assert_ordered_string_assoc_list_equal
    [("a",1);("b",1)]
    (Counters.as_ordered_assoc_list ((Counters.merge (fun x y -> x+y) (Counters.add (Counters.create compare_string) "a")
    (Counters.add (Counters.create compare_string) "b"))))

let test_counters_merge_different_rev _ =
  assert_ordered_string_assoc_list_equal
    [("a",1);("b",1)]
    (Counters.as_ordered_assoc_list ((Counters.merge (fun x y -> x+y) (Counters.add (Counters.create compare_string) "b")
    (Counters.add (Counters.create compare_string) "a"))))

let counters_suite = "compare_dnf_regexs Unit Tests" >:::
  ["test_counters_add_same" >:: test_counters_add_same;
   "test_counters_add_different" >:: test_counters_add_different;
   "test_counters_add_different_rev" >:: test_counters_add_different_rev;
   "test_counters_merge_same" >:: test_counters_merge_same;
   "test_counters_merge_different" >:: test_counters_merge_different;
   "test_counters_merge_different_rev" >:: test_counters_merge_different_rev;
  ]

let _ = run_test_tt_main counters_suite

module IntDisjointSet = DisjointSetOf(
  struct
    type t = int
    [@@deriving ord, show, hash]
  end)

let empty_int : IntDisjointSet.t = IntDisjointSet.empty
let ds_1234equal : IntDisjointSet.t =
  IntDisjointSet.create_from_equivalences
    [(1,2);(3,4);(2,3)]
let ds_1231equal : IntDisjointSet.t =
  IntDisjointSet.create_from_equivalences
    [(1,2);(2,3);(3,1)]

let test_disjointset_singleton _ =
  assert_int_equal
    1
    (IntDisjointSet.find_representative empty_int 1)

let test_disjointset_setequiv _ =
  assert_int_equal
    (IntDisjointSet.find_representative ds_1234equal 1)
    (IntDisjointSet.find_representative ds_1234equal 4)

let test_disjointset_disjoint _ =
  assert_not_equal_int
    (IntDisjointSet.find_representative ds_1234equal 0)
    (IntDisjointSet.find_representative ds_1234equal 2)

let test_disjointset_cyclic _ =
  assert_int_equal
    (IntDisjointSet.find_representative ds_1231equal 1)
    (IntDisjointSet.find_representative ds_1231equal 3)
  

let disjointset_suite = "DisjointSet Unit Tests" >:::
  [
    "test_disjointset_singleton" >:: test_disjointset_singleton;
    "test_disjointset_setequiv"  >:: test_disjointset_setequiv ;
    "test_disjointset_disjoint"  >:: test_disjointset_disjoint ;
    "test_disjointset_cyclic"    >:: test_disjointset_cyclic   ;
  ]

let _ = run_test_tt_main disjointset_suite


let test_to_exampled_dnf_constant_noex _ =
  assert_exampled_dnf_option_equal
    (Some ([([],["a"],[])],[]))
    (regex_to_exampled_dnf_regex RegexContext.empty LensContext.empty
      (Regex.RegExBase "a")
      [])

let test_to_exampled_dnf_constant_2ex _ =
  assert_exampled_dnf_option_equal
    (Some ([([],["a"],[[1];[0]])],[[1];[0]]))
    (regex_to_exampled_dnf_regex RegexContext.empty LensContext.empty
      (Regex.RegExBase "a")
      ["a";"a"])

let test_to_exampled_dnf_or _ =
  assert_exampled_dnf_option_equal
    (Some ([([],["a"],[[1]]);([],["b"],[[0]])],[[1];[0]]))
    (regex_to_exampled_dnf_regex RegexContext.empty LensContext.empty
      (Regex.RegExOr (Regex.RegExBase "a", Regex.RegExBase "b"))
      ["b";"a"])

let test_to_exampled_dnf_var _ =
  assert_exampled_dnf_option_equal
    (Some ([([EAVariable (Id.Id "A",Id.Id "A",Lens.LensIdentity(Regex.RegExVariable (Id.Id "A")),["a"],[[0]])],["";""],[[0]])],[[0]]))
    (regex_to_exampled_dnf_regex (RegexContext.create_from_list_exn [Id.Id "A",Regex.RegExBase "a",true]) LensContext.empty
      (Regex.RegExVariable (Id.Id "A"))
      ["a"])

let test_to_exampled_dnf_star _ =
  assert_exampled_dnf_option_equal
  (Some ([([EAStar (([[],["a"],[[1;0];[0;0]]],[[1;0];[0;0]]),[[0]])],["";""],[[0]])],[[0]]))
    (regex_to_exampled_dnf_regex RegexContext.empty LensContext.empty
      (Regex.RegExStar (Regex.RegExBase "a"))
      ["aa"])

let test_to_exampled_dnf_suite = "to_exampled_dnf_regex Unit Tests" >:::
  ["test_to_exampled_dnf_constant_noex" >:: test_to_exampled_dnf_constant_noex;
   "test_to_exampled_dnf_constant_2ex" >:: test_to_exampled_dnf_constant_2ex;
   "test_to_exampled_dnf_or" >:: test_to_exampled_dnf_or;
   "test_to_exampled_dnf_var" >:: test_to_exampled_dnf_var;
   "test_to_exampled_dnf_star" >:: test_to_exampled_dnf_star;
  ]

let _ = run_test_tt_main test_to_exampled_dnf_suite

let test_compare_dnf_regexs_vars_eq _ =
  assert_comparison_equal
    0
    (compare_dnf_regexs [[AVar (Id.make "a")],["";"1qaz"]]
    [[AVar (Id.Id "a")],["";"2wsx"]])

let test_compare_dnf_regexs_vars_lt _ =
  assert_comparison_equal
    (-1)
    (compare_dnf_regexs [[AVar (Id.make "a")],["";"1qaz"]]
    [[AVar (Id.make "b")],["";"2wsx"]])

let compare_dnf_regexs_suite = "compare_dnf_regexs Unit Tests" >:::
  ["test_compare_dnf_regexs_vars_eq" >:: test_compare_dnf_regexs_vars_eq;
   "test_compare_dnf_regexs_vars_lt" >:: test_compare_dnf_regexs_vars_lt;
  ]

let _ = run_test_tt_main compare_dnf_regexs_suite

let test_compare_exampled_dnf_regexs_vars_eq _ =
  assert_comparison_equal
    0
    (compare_exampled_dnf_regexs ([[EAVariable
    ((Id.make "a"),(Id.make "a"),Lens.LensIdentity (Regex.RegExVariable (Id.make "a")),["a";"aa"],[[0];[1]])],["";"1qaz"],[[0];[1]]],[[0];[1]])
    ([[EAVariable
    ((Id.make "a"),(Id.make "a"),Lens.LensIdentity (Regex.RegExVariable (Id.make "a")),["a";"aa"],[[0];[1]])],["";"2wsx"],[[0];[1]]],[[0];[1]]))

let test_compare_exampled_dnf_regexs_vars_lt1 _ =
  assert_comparison_equal
    (-1)
    (compare_exampled_dnf_regexs ([[EAVariable
    (Id.make "a",Id.make "a",Lens.LensIdentity (Regex.RegExVariable (Id.make "a")),["b"],[[0]])],["";"1qaz"],[[0]]],[[0]])
    ([[EAVariable (Id.make "b",Id.make "b",Lens.LensIdentity (Regex.RegExVariable (Id.make "b")),["a"],[[0]])],["";"2wsx"],[[0]]],[[0]]))

let test_compare_exampled_dnf_regexs_vars_lt2 _ =
  assert_comparison_equal
    (-1)
    (compare_exampled_dnf_regexs ([[EAVariable
    (Id.make "a",Id.make "a",Lens.LensIdentity (Regex.RegExVariable (Id.make "a")), ["a"],[[0]])],["";"1qaz"],[[0]]],[[0]])
    ([[EAVariable (Id.make "a",Id.make "a", Lens.LensIdentity (Regex.RegExVariable (Id.make "a")), ["b"],[[0]])],["";"2wsx"],[[0]]],[[0]]))

let compare_equivalent_dnf_regexs_suite = "compare_dnf_regexs Unit Tests" >:::
  ["test_compare_exampled_dnf_regexs_vars_eq" >:: test_compare_exampled_dnf_regexs_vars_eq;
   "test_compare_exampled_dnf_regexs_vars_lt1" >:: test_compare_exampled_dnf_regexs_vars_lt1;
   "test_compare_exampled_dnf_regexs_vars_lt2" >:: test_compare_exampled_dnf_regexs_vars_lt2;
  ]

let _ = run_test_tt_main compare_equivalent_dnf_regexs_suite




let test_rxc_concrete_name = Id.make "concrete_name"
let test_rxc_concrete_base = (Regex.RegExBase "concrete_base")
let test_rxc_abstract_name = Id.make "abstract_name"
let test_rxc_abstract_base = (Regex.RegExBase "abstract_base")
let test_rxc_context =
  RegexContext.create_from_list_exn
    [(test_rxc_concrete_name,test_rxc_concrete_base,false)
    ;(test_rxc_abstract_name,test_rxc_abstract_base,true)]

let test_lookup_empty _ =
  assert_raises
    (Failure "lookup_exn: (Lang.Id.Id \"none\") not found")
    (fun _ -> RegexContext.lookup_exn RegexContext.empty (Id.make "none"))

let test_lookup_abstract _ =
  assert_regex_equal
    test_rxc_abstract_base
    (RegexContext.lookup_exn test_rxc_context test_rxc_abstract_name)

let test_lookup_concrete _ =
  assert_regex_equal
    test_rxc_concrete_base
    (RegexContext.lookup_exn test_rxc_context test_rxc_concrete_name)

let test_insert_same =
  RegexContext.insert_exn
    test_rxc_context
    test_rxc_abstract_name
    test_rxc_abstract_base
    true

let test_insert_conflicted _ =
  assert_raises
    (Failure (Id.show test_rxc_concrete_name ^ " already exists in the context"))
    (fun _ ->
       RegexContext.insert_exn
         test_rxc_context
         test_rxc_concrete_name
         test_rxc_abstract_base
         false)

let test_lookup_for_expansion_empty _ =
  assert_raises
    (Failure "bad regex name: (Lang.Id.Id \"none\")")
    (fun _ -> RegexContext.lookup_for_expansion_exn RegexContext.empty (Id.make "none"))

let regex_context_suite = "RegexContext Unit Tests" >:::
  [
    "test_lookup_empty" >:: test_lookup_empty;
    "test_lookup_abstract" >:: test_lookup_abstract;
    "test_lookup_concrete" >:: test_lookup_concrete;
    "test_insert_conflicted" >:: test_insert_conflicted;
    "test_lookup_for_expansion_empty" >:: test_lookup_for_expansion_empty;
  ]

let _ = run_test_tt_main regex_context_suite

let test_lc_a_name = Id.make "a"
let test_lc_b_name = Id.make "b"
let test_lc_c_name = Id.make "c"
let test_lc_a = Regex.RegExVariable test_lc_a_name
let test_lc_b = Regex.RegExVariable test_lc_b_name
let test_lc_c = Regex.RegExVariable test_lc_c_name
let test_lc_ab_name = Id.make "ab"
let test_lc_bc_name = Id.make "bc"
let test_lc_ca_name = Id.make "ca"
let test_lc_ab_lens = Lens.LensConst ("a","b")
let test_lc_bc_lens = Lens.LensConst ("b","c")
let test_lc_ca_lens = Lens.LensConst ("c","a")
let test_lc_ab_variable_lens = Lens.LensVariable test_lc_ab_name
let test_lc_bc_variable_lens = Lens.LensVariable test_lc_bc_name
let test_lc_ca_variable_lens = Lens.LensVariable test_lc_ca_name
let test_lc_context =
  LensContext.create_from_list_exn
    [(test_lc_ab_name,test_lc_ab_lens,test_lc_a,test_lc_b)
    ;(test_lc_bc_name,test_lc_bc_lens,test_lc_b,test_lc_c)
    ;(test_lc_ca_name,test_lc_ca_lens,test_lc_c,test_lc_a)]

let test_lc_lookup_empty _ =
  assert_raises
    (Failure "lookup_exn: (Lang.Id.Id \"none\") not found")
    (fun _ -> LensContext.lookup_exn LensContext.empty (Id.make "none"))

let test_lc_lookup_type_empty _ =
  assert_raises
    (Failure "lookup_exn: (Lang.Id.Id \"none\") not found")
    (fun _ -> LensContext.lookup_type_exn LensContext.empty (Id.make "none"))

let test_lc_lookup_impl_empty _ =
  assert_raises
    (Failure "lookup_exn: (Lang.Id.Id \"none\") not found")
    (fun _ -> LensContext.lookup_impl_exn LensContext.empty (Id.make "none"))

let test_lc_lookup _ =
  assert_lens_regex_regex_equal
    (test_lc_ab_lens, test_lc_a, test_lc_b)
    (LensContext.lookup_exn test_lc_context test_lc_ab_name)

let test_lc_lookup_type _ =
  assert_regex_regex_equal
    (test_lc_a, test_lc_b)
    (LensContext.lookup_type_exn test_lc_context test_lc_ab_name)

let test_lc_lookup_impl _ =
  assert_lens_equal
    (test_lc_ab_lens)
    (LensContext.lookup_impl_exn test_lc_context test_lc_ab_name)

let test_lc_insert_conflicted _ =
  assert_raises
    (Failure "bad insert")
    (fun _ ->
       LensContext.insert_exn
         test_lc_context
         test_lc_ab_name
         test_lc_ab_lens
         test_lc_a
         test_lc_b)

let test_lc_shortest_path_exn_nopath _ =
  assert_raises
    (Failure "regexes not in same equivalence class")
    (fun _ ->
       LensContext.shortest_path_exn
         test_lc_context
         test_lc_a_name
         (Id.make "other"))

let test_lc_shortest_path_exn_normal _ =
  assert_lens_equal
    test_lc_bc_variable_lens
    (LensContext.shortest_path_exn
       test_lc_context
       test_lc_b_name
       test_lc_c_name)

let test_lc_shortest_path_exn_inverse _ =
  assert_lens_equal
    (Lens.LensInverse test_lc_ca_variable_lens)
    (LensContext.shortest_path_exn
       test_lc_context
       test_lc_a_name
       test_lc_c_name)

let test_lc_paths_to_rep_elt_1 _ =
  assert_id_lens_equal
    (test_lc_c_name,Lens.LensIdentity (test_lc_c))
    (LensContext.shortest_path_to_rep_elt
       test_lc_context
       test_lc_c_name)

let test_lc_paths_to_rep_elt_2 _ =
  assert_id_lens_equal
    (test_lc_c_name,test_lc_bc_variable_lens)
    (LensContext.shortest_path_to_rep_elt
       test_lc_context
       test_lc_b_name)

let test_lc_paths_to_rep_elt_3 _ =
  assert_id_lens_equal
    (test_lc_c_name,Lens.LensInverse test_lc_ca_variable_lens)
    (LensContext.shortest_path_to_rep_elt
       test_lc_context
       test_lc_a_name)

let test_lc_paths_to_rep_elt_singleton _ =
  assert_id_lens_equal
    ((Id.make "sinlgetonname"),Lens.LensIdentity (Regex.RegExVariable (Id.make "sinlgetonname")))
    (LensContext.shortest_path_to_rep_elt
       test_lc_context
       (Id.make "sinlgetonname"))

let lens_context_suite = "LensContext Unit Tests" >:::
  [
    "test_lc_lookup_empty" >:: test_lc_lookup_empty;
    "test_lc_lookup_type_empty" >:: test_lc_lookup_type_empty;
    "test_lc_lookup_impl_empty" >:: test_lc_lookup_impl_empty;
    "test_lc_lookup" >:: test_lc_lookup;
    "test_lc_lookup_type" >:: test_lc_lookup_type;
    "test_lc_lookup_impl" >:: test_lc_lookup_impl;
    "test_lc_insert_conflicted" >:: test_lc_insert_conflicted;
    "test_lc_shortest_path_exn_nopath" >:: test_lc_shortest_path_exn_nopath;
    "test_lc_shortest_path_exn_normal" >:: test_lc_shortest_path_exn_normal;
    "test_lc_shortest_path_exn_inverse" >:: test_lc_shortest_path_exn_inverse;
    "test_lc_paths_to_rep_elt_1" >:: test_lc_paths_to_rep_elt_1;
    "test_lc_paths_to_rep_elt_2" >:: test_lc_paths_to_rep_elt_2;
    "test_lc_paths_to_rep_elt_3" >:: test_lc_paths_to_rep_elt_3;
  ]

let _ = run_test_tt_main lens_context_suite





(* Eval tests *)
let test_fast_eval_base_positive _ =
  assert_bool_equal
    true
    (fast_eval RegexContext.empty (Regex.RegExBase "x") "x")

let test_fast_eval_base_negative1 _ =
  assert_bool_equal
    false
    (fast_eval RegexContext.empty (Regex.RegExBase "x") "y")

let test_fast_eval_base_negative2 _ =
  assert_bool_equal
    false
    (fast_eval RegexContext.empty (Regex.RegExBase "x") "xx")

let test_fast_eval_concat_positive1 _ =
  assert_bool_equal
    true
    (fast_eval RegexContext.empty
      (Regex.RegExConcat
        (Regex.RegExBase "x",
        Regex.RegExConcat
          (Regex.RegExBase "y",
          Regex.RegExBase "z"))) "xyz")

let test_fast_eval_concat_positive2 _ =
  assert_bool_equal
    true
    (fast_eval RegexContext.empty
      (Regex.RegExConcat
        (Regex.RegExConcat
          (Regex.RegExBase "x",
          Regex.RegExBase "y"),
        Regex.RegExBase "z")) "xyz")

let test_fast_eval_concat_negative1 _ =
  assert_bool_equal
    false
    (fast_eval RegexContext.empty
      (Regex.RegExConcat
        (Regex.RegExBase "x",
        Regex.RegExBase "y")) "x")

let test_fast_eval_concat_negative2 _ =
  assert_bool_equal
    false
    (fast_eval RegexContext.empty
      (Regex.RegExConcat
        (Regex.RegExBase "x",
        Regex.RegExBase "y")) "xz")

let test_fast_eval_concat_negative3 _ =
  assert_bool_equal
    false
    (fast_eval RegexContext.empty
      (Regex.RegExConcat
        (Regex.RegExBase "x",
        Regex.RegExBase "y")) "yx")

let test_fast_eval_concat_negative4 _ =
  assert_bool_equal
    false
    (fast_eval RegexContext.empty
      (Regex.RegExConcat
        (Regex.RegExBase "x",
        Regex.RegExBase "y")) "xyz")

let test_fast_eval_or_positive _ =
  assert_bool_equal
    true
    (fast_eval RegexContext.empty
      (Regex.RegExOr
        (Regex.RegExOr
          (Regex.RegExBase "a",
          Regex.RegExBase "b"),
        (Regex.RegExOr
          (Regex.RegExBase "c",
          Regex.RegExBase "d")))) "c")

let test_fast_eval_or_negative _ =
  assert_bool_equal
    false
    (fast_eval RegexContext.empty
      (Regex.RegExOr
        (Regex.RegExOr
          (Regex.RegExBase "a",
          Regex.RegExBase "b"),
        (Regex.RegExOr
          (Regex.RegExBase "c",
          Regex.RegExBase "d")))) "x")

let test_fast_eval_star_empty _ =
  assert_bool_equal
    true
    (fast_eval RegexContext.empty
      (Regex.RegExStar
        (Regex.RegExBase "a")) "")

let test_fast_eval_star_one _ =
  assert_bool_equal
    true
    (fast_eval RegexContext.empty
      (Regex.RegExStar
        (Regex.RegExBase "a")) "a")

let test_fast_eval_star_two _ =
  assert_bool_equal
    true
    (fast_eval RegexContext.empty
      (Regex.RegExStar
        (Regex.RegExBase "a")) "aa")

let test_fast_eval_star_choice _ =
  assert_bool_equal
    true
    (fast_eval RegexContext.empty
      (Regex.RegExStar
        (Regex.RegExOr
          (Regex.RegExBase "a"
          ,Regex.RegExBase "b"))
      ) "aab" )

let test_fast_eval_star_negative1 _ =
  assert_bool_equal
    false
    (fast_eval RegexContext.empty
      (Regex.RegExStar
        (Regex.RegExBase "a")) "b")

let test_fast_eval_star_negative2 _ =
  assert_bool_equal
    false
    (fast_eval RegexContext.empty
      (Regex.RegExStar
        (Regex.RegExBase "a")) "ab")

let test_fast_eval_star_negative3 _ =
  assert_bool_equal
    false
    (fast_eval RegexContext.empty
      (Regex.RegExStar
        (Regex.RegExBase "a")) "ba")

let test_fast_eval_var_positive _ =
  assert_bool_equal
    true
    (fast_eval (RegexContext.create_from_list_exn [(Id.make "A"),Regex.RegExBase "a",true])
      (Regex.RegExVariable (Id.make "A")) "a")

let test_fast_eval_var_negative _ =
  assert_bool_equal
    false
    (fast_eval (RegexContext.create_from_list_exn [(Id.make "A"),Regex.RegExBase "a",true])
      (Regex.RegExVariable (Id.make "A")) "b")

let test_fast_eval_concat_var _ =
  assert_bool_equal
  true
  (fast_eval
    (RegexContext.create_from_list_exn [(Id.make "A", Regex.RegExBase "a",true);(Id.make "B", Regex.RegExBase "b",true)])
    (Regex.RegExConcat (Regex.RegExVariable (Id.make "A"), Regex.RegExVariable (Id.make "B")))
    "ab")

let test_fast_eval_nested_var _ =
  assert_bool_equal
  true
  (fast_eval
   (RegexContext.create_from_list_exn [(Id.make "A", Regex.RegExBase "a", true);(Id.make "B", Regex.RegExVariable (Id.make "A"),true)])
   (Regex.RegExVariable (Id.make "B")) "a")

let test_fast_eval_fast _ =
  assert_bool_equal
  true
  (fast_eval
     (RegexContext.create_from_list_exn [(Id.make "A", Regex.RegExConcat (Regex.RegExBase "c", Regex.RegExConcat (Regex.RegExStar
  (Regex.RegExBase "a"), Regex.RegExStar (Regex.RegExBase "b"))),true)])
  (Regex.RegExConcat (Regex.RegExStar (Regex.RegExVariable (Id.make "A")), Regex.RegExConcat (Regex.RegExBase "z",
  Regex.RegExStar (Regex.RegExConcat (Regex.RegExConcat (Regex.RegExVariable (Id.make "A"), Regex.RegExBase "q"),
  Regex.RegExStar (Regex.RegExConcat (Regex.RegExVariable (Id.make "A"), Regex.RegExOr (Regex.RegExBase "t",
  Regex.RegExBase "m"))))))))
  "caaabbbbcaaabbbbcaaabbbbcaaabbbbcaaabbbbcaaabbbbcaaabbbbcaaabbbbzcaaabbbqcaaabbbtcaaabbbqcaaabbbtcaaabbbqcaaabbbtcaaabbbqcaaabbbtcaaabbbqcaaabbbtcaaabbbqcaaabbbtcaaabbbqcaaabbbtcaaabbbqcaaabbbtcaaabbbqcaaabbbtcaaabbbqcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbmcaaabbbm")

let fast_eval_suite = "fast_eval Unit Tests" >:::
  ["test_fast_eval_base_positive" >:: test_fast_eval_base_positive;
   "test_fast_eval_base_negative1" >:: test_fast_eval_base_negative1;
   "test_fast_eval_base_negative2" >:: test_fast_eval_base_negative2;
   "test_fast_eval_concat_positive1" >:: test_fast_eval_concat_positive1;
   "test_fast_eval_concat_positive2" >:: test_fast_eval_concat_positive2;
   "test_fast_eval_concat_negative1" >:: test_fast_eval_concat_negative1;
   "test_fast_eval_concat_negative2" >:: test_fast_eval_concat_negative2;
   "test_fast_eval_concat_negative3" >:: test_fast_eval_concat_negative3;
   "test_fast_eval_concat_negative4" >:: test_fast_eval_concat_negative4;
   "test_fast_eval_or_negative" >:: test_fast_eval_or_negative;
   "test_fast_eval_or_positive" >:: test_fast_eval_or_positive;
   "test_fast_eval_star_empty" >:: test_fast_eval_star_empty;
   "test_fast_eval_star_one" >:: test_fast_eval_star_one;
   "test_fast_eval_star_two" >:: test_fast_eval_star_two;
   "test_fast_eval_star_choice" >:: test_fast_eval_star_choice;
   "test_fast_eval_star_negative1" >:: test_fast_eval_star_negative1;
   "test_fast_eval_star_negative2" >:: test_fast_eval_star_negative2;
   "test_fast_eval_star_negative3" >:: test_fast_eval_star_negative3;
   "test_fast_eval_var_positive" >:: test_fast_eval_var_positive;
   "test_fast_eval_var_negative" >:: test_fast_eval_var_negative;
   "test_fast_eval_concat_var" >:: test_fast_eval_concat_var;
   "test_fast_eval_nested_var" >:: test_fast_eval_nested_var;
   "test_fast_eval_fast" >:: test_fast_eval_fast;
  ]

let _ = run_test_tt_main fast_eval_suite

let test_string_options (expected:string option) (actual:string option) =
  assert_equal
    ~printer:(fun x -> begin match x with | None -> "None" | Some s -> s end)
    expected
    actual



let test_int_list = assert_equal
    ~printer:(fun is -> String.concat (List.map ~f:string_of_int is) ~sep:",")

let test_permutation_create_invalid_0 _ =
  assert_raises
    (Failure "Not Bijection")
    (fun _ -> Permutation.create [0;2])

let test_permutation_create_invalid_1 _ =
  assert_raises
    (Failure "Not Bijection")
    (fun _ -> Permutation.create [0;0])

let test_permutation_create_invalid_2 _ =
  assert_raises
    (Failure "Not Bijection")
    (fun _ -> Permutation.create [-1])

let test_permutation_create_from_doubles_invalid_0 _ =
  assert_raises
    (Failure "Not Bijection")
    (fun _ -> Permutation.create_from_doubles [(0,2);(1,0)])

let test_permutation_create_from_doubles_invalid_1 _ =
  assert_raises
    (Failure "Not Bijection")
    (fun _ -> Permutation.create_from_doubles [(0,1);(0,0)])

let test_permutation_create_from_doubles_invalid_2 _ =
  assert_raises
    (Failure "Not Bijection")
    (fun _ -> Permutation.create_from_doubles [(0,1);(1,1)])

let test_permutation_create_from_constraints_none_0 _ =
  assert_permutation_guesses_option_equal
    None
    (Permutation.create_from_constraints 3 [(0,2);(0,1);(0,0)] [])

let test_permutation_create_from_constraints_none_1 _ =
  assert_permutation_guesses_option_equal
    None
    (Permutation.create_from_constraints 3 [(0,0);(1,0);(2,0)] [])

let test_permutation_create_from_constraints_identity _ =
  assert_permutation_guesses_option_equal
    (Some ((Permutation.create [0;1;2]), [(0,0);(1,1);(2,2)]))
    (Permutation.create_from_constraints 3 [] [])

let test_permutation_create_from_constraints_withvalid _ =
  assert_permutation_guesses_option_equal
    (Some ((Permutation.create [1;0;2]), [(1,0);(2,2)]))
    (Permutation.create_from_constraints 3 [] [(0,1)])

let test_permutation_create_from_constraints_withinvalid _ =
  assert_permutation_guesses_option_equal
    (Some ((Permutation.create [1;0;2]), [(0,1);(1,0);(2,2)]))
    (Permutation.create_from_constraints 3 [(0,0)] [])

let test_permutation_apply_identity _ =
  assert_int_equal
     2
     (Permutation.apply (Permutation.create [0;1;2]) 2)

let test_permutation_apply_nonidentity _ =
  assert_int_equal
    1
    (Permutation.apply (Permutation.create [1;2;0]) 2)

let test_permutation_apply_from_doubles _ =
  assert_int_equal
    0
    (Permutation.apply
      (Permutation.create_from_doubles [(1,2);(2,0);(0,1)])
      2)
                
let test_permutation_apply_invalid _ =
  assert_raises
    (Failure "out of range")
    (fun _ -> Permutation.apply (Permutation.create []) 0)

let test_permutation_apply_inverse_identity _ =
  assert_int_equal
    2
    (Permutation.apply_inverse (Permutation.create [0;1;2]) 2)

let test_permutation_apply_inverse_nonidentity _ =
  assert_int_equal
    0
    (Permutation.apply_inverse (Permutation.create [1;2;0]) 2)
                
let test_permutation_apply_inverse_invalid _ =
  assert_raises
    (Failure "out of range")
    (fun _ -> Permutation.apply_inverse (Permutation.create []) 0)

let test_permutation_create_all _ =
  assert_int_equal
    2
    (List.length (Permutation.create_all 2))

let test_permutation_apply_to_list_identity _ =
  test_int_list
    [2;4;8]
    (Permutation.apply_to_list_exn (Permutation.create [0;1;2]) [2;4;8])

let test_permutation_apply_to_list_c3 _ =
  test_int_list
    [8;2;4]
    (Permutation.apply_to_list_exn (Permutation.create [2;0;1]) [2;4;8])

let test_permutation_apply_inverse_to_list_identity _ =
  test_int_list
    [2;4;8]
    (Permutation.apply_inverse_to_list_exn (Permutation.create [0;1;2]) [2;4;8])

let test_permutation_apply_inverse_to_list_c3 _ =
  test_int_list
    [4;8;2]
    (Permutation.apply_inverse_to_list_exn (Permutation.create [2;0;1]) [2;4;8])

let permutation_suite = "permutation Unit Tests" >:::
  ["test_permutation_create_invalid_0" >:: test_permutation_create_invalid_0;
   "test_permutation_create_invalid_1" >:: test_permutation_create_invalid_1;
   "test_permutation_create_invalid_2" >:: test_permutation_create_invalid_2;
   "test_permutation_create_from_doubles_invalid_0" >:: test_permutation_create_from_doubles_invalid_0;
   "test_permutation_create_from_doubles_invalid_1" >:: test_permutation_create_from_doubles_invalid_1;
   "test_permutation_create_from_doubles_invalid_2" >:: test_permutation_create_from_doubles_invalid_2;
   "test_permutation_create_from_constraints_none_0" >:: test_permutation_create_from_constraints_none_0;
   "test_permutation_create_from_constraints_none_1" >:: test_permutation_create_from_constraints_none_1;
   "test_permutation_create_from_constraints_identity" >:: test_permutation_create_from_constraints_identity;
   "test_permutation_create_from_constraints_withvalid" >:: test_permutation_create_from_constraints_withvalid;
   "test_permutation_create_from_constraints_withinvalid" >:: test_permutation_create_from_constraints_withinvalid;
   "test_permutation_apply_identity" >:: test_permutation_apply_identity;
   "test_permutation_apply_nonidentity" >:: test_permutation_apply_nonidentity;
   "test_permutation_apply_from_doubles" >:: test_permutation_apply_from_doubles;
   "test_permutation_apply_invalid" >:: test_permutation_apply_invalid;
   "test_permutation_apply_inverse_identity" >:: test_permutation_apply_inverse_identity;
   "test_permutation_apply_inverse_nonidentity" >:: test_permutation_apply_inverse_nonidentity;
   "test_permutation_apply_inverse_invalid" >:: test_permutation_apply_inverse_invalid;
   "test_permutation_create_all" >:: test_permutation_create_all;
   "test_permutation_apply_to_list_identity" >:: test_permutation_apply_to_list_identity;
   "test_permutation_apply_to_list_c3" >:: test_permutation_apply_to_list_c3;
   "test_permutation_apply_inverse_to_list_identity" >:: test_permutation_apply_inverse_to_list_identity;
   "test_permutation_apply_inverse_to_list_c3" >:: test_permutation_apply_inverse_to_list_c3;
  ]

let _ = run_test_tt_main permutation_suite

let test_bucketize_pairs_symmetric _ =
  assert_char_list_list_equal
    [[];['a'];[]]
    (bucketize_pairs 3 [('a',1)])

let test_bucketize_pairs_asymmetric _ =
  assert_char_list_list_equal
    [['a'];['b';'c'];[]]
    (bucketize_pairs 3 [('b',1);('a',0);('c',1)])

let test_sub0_error_split_at_index_exn _ =
  assert_raises
    (Failure "invalid index")
    (fun _ -> split_at_index_exn [] (-1))

let test_overlen_error_split_at_index_exn _ =
  assert_raises
    (Failure "invalid index")
    (fun _ -> split_at_index_exn [] (7))

let test_0index_split_at_index_exn _ =
  assert_char_list_double_equal
    ([],['a'])
    (split_at_index_exn ['a'] 0)

let test_index_split_at_index_exn _ =
  assert_char_list_double_equal
    (['a'],['b'])
    (split_at_index_exn ['a';'b'] 1)

let test_sort_and_partition _ =
  assert_char_list_list_equal
    [['a';'a'];['b'];['c';'c';'c'];['z']]
    (sort_and_partition
      (fun x y -> compare_char x y)
      ['a';'z';'b';'c';'c';'a';'c'])

let util_suite = "Util Unit Tests" >:::
  ["test_bucketize_pairs_symmetric" >:: test_bucketize_pairs_symmetric;
   "test_bucketize_pairs_asmemetric" >:: test_bucketize_pairs_asymmetric;
   "test_sub0_error_split_at_index_exn" >:: test_sub0_error_split_at_index_exn;
   "test_0index_split_at_index_exn" >:: test_0index_split_at_index_exn;
   "test_index_split_at_index_exn" >:: test_index_split_at_index_exn;
   "test_sort_and_partition" >:: test_sort_and_partition;
  ]

let _ = run_test_tt_main util_suite

let test_priority_queue_pop_empty _ =
  assert_int_int_int_priority_queue_option_equal
    None
    (ModTenPQueue.pop (ModTenPQueue.empty))

let test_priority_queue_pop_forward_backward _ =
  assert_int_int_int_priority_queue_option_equal
    (ModTenPQueue.pop (ModTenPQueue.from_list [2;1]))
    (ModTenPQueue.pop (ModTenPQueue.from_list [1;2]))

let test_priority_queue_pop_values _ =
  assert_int_option_equal
    (Some 1)
    (let vo = ModTenPQueue.pop (ModTenPQueue.from_list [2;1]) in
     Option.map ~f:(fun (x,_,_) -> (x)) vo)

let test_priority_queue_pop_priority _ =
  assert_float_option_equal
    (Some 1.0)
    (let vo = ModTenPQueue.pop (ModTenPQueue.from_list [2;1]) in
     Option.map ~f:(fun (_,y,_) -> (y)) vo)

let priority_queue_suite = "Priority_Queue Unit Tests" >:::
  ["test_priority_queue_pop_empty" >:: test_priority_queue_pop_empty;
   "test_priority_queue_pop_forward_backward" >:: test_priority_queue_pop_forward_backward;
   "test_priority_queue_pop_values" >:: test_priority_queue_pop_values;
   "test_priority_queue_pop_priority" >:: test_priority_queue_pop_priority;
  ]

let _ = run_test_tt_main priority_queue_suite

let test_extract_string_base _ =
  assert_string_equal
    "base"
    (extract_string
       (ERegExBase ("base",[[0]]))
       [0])

let test_extract_string_concat _ =
  assert_string_equal
    "concat"
    (extract_string
       (ERegExConcat
          (ERegExBase ("con",[[0]])
          ,ERegExBase ("cat",[[0]])
          ,[[0]]))
       [0])

let test_extract_string_union_left _ =
  assert_string_equal
    "union"
    (extract_string
       (ERegExOr
          (ERegExBase ("union",[[0]])
          ,ERegExBase ("not",[])
          ,[[0]]))
       [0])

let test_extract_string_union_right _ =
  assert_string_equal
    "union"
    (extract_string
       (ERegExOr
          (ERegExBase ("not",[])
          ,ERegExBase ("union",[[0]])
          ,[[0]]))
       [0])

let test_extract_string_iterate _ =
  assert_string_equal
    "iii"
    (extract_string
       (ERegExStar
          (ERegExBase ("i",[[0;0];[1;0];[2;0];[0;1]])
          ,[[0]]))
       [0])

let test_extract_string_var _ =
  assert_string_equal
    "var"
    (extract_string
       (ERegExVariable (Id.make "t",["var";"not"],[[0];[1]]))
       [0])

let extract_string_suite = "extract_string Unit Tests" >:::
  [
    "test_extract_string_base" >:: test_extract_string_base;
    "test_extract_string_concat" >:: test_extract_string_concat;
    "test_extract_string_union_left" >:: test_extract_string_union_left;
    "test_extract_string_union_right" >:: test_extract_string_union_right;
    "test_extract_string_iterate" >:: test_extract_string_iterate;
    "test_extract_string_var" >:: test_extract_string_var;
  ]

let _ = run_test_tt_main extract_string_suite

let test_lens_putr_const _ =
  assert_string_equal
    "target"
    (lens_putr RegexContext.empty LensContext.empty (Lens.LensConst ("source","target")) "source")

let test_lens_putr_concat _ =
  assert_string_equal
    "t1t2"
    (lens_putr
       RegexContext.empty
       LensContext.empty
       (Lens.LensConcat ((Lens.LensConst ("s1","t1")),Lens.LensConst ("s2","t2")))
       "s1s2")

let test_lens_putr_swap _ =
  assert_string_equal
    "t2t1"
    (lens_putr
       RegexContext.empty
       LensContext.empty
       (Lens.LensSwap ((Lens.LensConst ("s1","t1")),Lens.LensConst ("s2","t2")))
       "s1s2")

let test_lens_putr_union_left _ =
  assert_string_equal
    "t1"
    (lens_putr
       RegexContext.empty
       LensContext.empty
       (Lens.LensUnion ((Lens.LensConst ("s1","t1")),Lens.LensConst ("s2","t2")))
       "s1")

let test_lens_putr_union_right _ =
  assert_string_equal
    "t2"
    (lens_putr
       RegexContext.empty
       LensContext.empty
       (Lens.LensUnion ((Lens.LensConst ("s1","t1")),Lens.LensConst ("s2","t2")))
       "s2")

let test_lens_putr_compose _ =
  assert_string_equal
    "u"
    (lens_putr
       RegexContext.empty
       LensContext.empty
       (Lens.LensCompose ((Lens.LensConst ("t","u")),Lens.LensConst ("s","t")))
       "s")

let test_lens_putr_iterate_empty _ =
  assert_string_equal
    ""
    (lens_putr
       RegexContext.empty
       LensContext.empty
       (Lens.LensIterate (Lens.LensConst ("s","t")))
       "")

let test_lens_putr_iterate_singleton _ =
  assert_string_equal
    "t"
    (lens_putr
       RegexContext.empty
       LensContext.empty
       (Lens.LensIterate (Lens.LensConst ("s","t")))
       "s")

let test_lens_putr_iterate_multiple _ =
  assert_string_equal
    "ttt"
    (lens_putr
       RegexContext.empty
       LensContext.empty
       (Lens.LensIterate (Lens.LensConst ("s","t")))
       "sss")

let test_lens_putr_identity _ =
  assert_string_equal
    "source"
    (lens_putr
       RegexContext.empty
       LensContext.empty
       (Lens.LensIdentity (Regex.RegExBase "source"))
       "source")

let test_inverse_putr _ =
  assert_string_equal
    "source"
    (lens_putr
       RegexContext.empty
       LensContext.empty
       (Lens.LensInverse (Lens.LensConst ("source","target")))
       "target")

let test_lens_putr_perm _ =
  assert_string_equal
    "120"
    (lens_putr
       RegexContext.empty
       LensContext.empty
       (Lens.LensPermute
          (Permutation.create [1;2;0]
          ,[Lens.LensConst("0","0")
           ;Lens.LensConst("1","1")
           ;Lens.LensConst("2","2")]))
    "012")

let lens_putr_suite = "lens_putr Unit Tests" >:::
  [
    "test_lens_putr_const" >:: test_lens_putr_const;
    "test_lens_putr_concat" >:: test_lens_putr_concat;
    "test_lens_putr_swap" >:: test_lens_putr_swap;
    "test_lens_putr_union_left" >:: test_lens_putr_union_left;
    "test_lens_putr_union_right" >:: test_lens_putr_union_right;
    "test_lens_putr_compose" >:: test_lens_putr_compose;
    "test_lens_putr_iterate_empty" >:: test_lens_putr_iterate_empty;
    "test_lens_putr_iterate_singleton" >:: test_lens_putr_iterate_singleton;
    "test_lens_putr_iterate_multiple" >:: test_lens_putr_iterate_multiple;
    "test_lens_putr_identity" >:: test_lens_putr_identity;
    "test_inverse_putr" >:: test_inverse_putr;
    "test_lens_putr_perm" >:: test_lens_putr_perm;
  ]

let _ = run_test_tt_main lens_putr_suite


let test_lens_putl_const _ =
  assert_string_equal
    "source"
    (lens_putl RegexContext.empty LensContext.empty (Lens.LensConst ("source","target")) "target")

let test_lens_putl_concat _ =
  assert_string_equal
    "s1s2"
    (lens_putl
       RegexContext.empty
       LensContext.empty
       (Lens.LensConcat ((Lens.LensConst ("s1","t1")),Lens.LensConst ("s2","t2")))
       "t1t2")

let test_lens_putl_swap _ =
  assert_string_equal
    "s1s2"
    (lens_putl
       RegexContext.empty
       LensContext.empty
       (Lens.LensSwap ((Lens.LensConst ("s1","t1")),Lens.LensConst ("s2","t2")))
       "t2t1")

let test_lens_putl_union_left _ =
  assert_string_equal
    "s1"
    (lens_putl
       RegexContext.empty
       LensContext.empty
       (Lens.LensUnion ((Lens.LensConst ("s1","t1")),Lens.LensConst ("s2","t2")))
       "t1")

let test_lens_putl_union_right _ =
  assert_string_equal
    "s2"
    (lens_putl
       RegexContext.empty
       LensContext.empty
       (Lens.LensUnion ((Lens.LensConst ("s1","t1")),Lens.LensConst ("s2","t2")))
       "t2")

let test_lens_putl_compose _ =
  assert_string_equal
    "s"
    (lens_putl
       RegexContext.empty
       LensContext.empty
       (Lens.LensCompose ((Lens.LensConst ("t","u")),Lens.LensConst ("s","t")))
       "u")

let test_lens_putl_iterate_empty _ =
  assert_string_equal
    ""
    (lens_putl
       RegexContext.empty
       LensContext.empty
       (Lens.LensIterate (Lens.LensConst ("s","t")))
       "")

let test_lens_putl_iterate_singleton _ =
  assert_string_equal
    "s"
    (lens_putl
       RegexContext.empty
       LensContext.empty
       (Lens.LensIterate (Lens.LensConst ("s","t")))
       "t")

let test_lens_putl_iterate_multiple _ =
  assert_string_equal
    "sss"
    (lens_putl
       RegexContext.empty
       LensContext.empty
       (Lens.LensIterate (Lens.LensConst ("s","t")))
       "ttt")

let test_lens_putl_identity _ =
  assert_string_equal
    "target"
    (lens_putl
       RegexContext.empty
       LensContext.empty
       (Lens.LensIdentity (Regex.RegExBase "target"))
       "target")

let test_lens_putl_inverse _ =
  assert_string_equal
    "target"
    (lens_putl
       RegexContext.empty
       LensContext.empty
       (Lens.LensInverse (Lens.LensConst ("source","target")))
       "source")

let test_lens_putl_perm _ =
  assert_string_equal
    "012"
    (lens_putl
       RegexContext.empty
       LensContext.empty
       (Lens.LensPermute
          (Permutation.create [1;2;0]
          ,[Lens.LensConst("0","0")
           ;Lens.LensConst("1","1")
           ;Lens.LensConst("2","2")]))
    "120")

let lens_putl_suite = "lens_putl Unit Tests" >:::
  [
    "test_lens_putl_const"             >:: test_lens_putl_const;
    "test_lens_putl_concat"            >:: test_lens_putl_concat;
    "test_lens_putl_swap"              >:: test_lens_putl_swap;
    "test_lens_putl_union_left"        >:: test_lens_putl_union_left;
    "test_lens_putl_union_right"       >:: test_lens_putl_union_right;
    "test_lens_putl_compose"           >:: test_lens_putl_compose;
    "test_lens_putl_iterate_empty"     >:: test_lens_putl_iterate_empty;
    "test_lens_putl_iterate_singleton" >:: test_lens_putl_iterate_singleton;
    "test_lens_putl_iterate_multiple"  >:: test_lens_putl_iterate_multiple;
    "test_lens_putl_identity"          >:: test_lens_putl_identity;
    "test_lens_putl_inverse"           >:: test_lens_putl_inverse;
    "test_lens_putl_perm"              >:: test_lens_putl_perm;
  ]

let _ = run_test_tt_main lens_putl_suite



let aid = Id.make "A"
let bid = Id.make "B"
let cid = Id.make "C"
let did = Id.make "D"
let eid = Id.make "E"
let fid = Id.make "F"

let transitives_regexcontext =
  RegexContext.create_from_list_exn
    [(aid,Regex.make_base "a",false)
    ;(bid,Regex.make_base "b",false)
    ;(cid,Regex.make_base "c",false)
    ;(did,Regex.make_var aid,false)
    ;(eid,Regex.make_star (Regex.make_var did),false)
    ;(fid,Regex.make_star (Regex.make_var bid),true)]

let transitives_lenscontext =
  LensContext.empty

let test_with_no_transitives_correct _ =
  assert_transitive_set_equal
    (IdToIntSetDict.from_kvp_list
       [(aid,IntSet.from_list [0;1])
       ;(bid,IntSet.from_list [1])
       ;(cid,IntSet.from_list [0])])
    (get_transitive_set
       transitives_regexcontext
       transitives_lenscontext
       (Regex.make_or
          (Regex.make_var aid)
          (Regex.make_or
             (Regex.make_star
                (Regex.make_var aid))
             (Regex.make_or
                (Regex.make_star
                   (Regex.make_var bid))
                (Regex.make_var cid)))))

let test_with_transitives_correct _ =
  assert_transitive_set_equal
    (IdToIntSetDict.from_kvp_list
       [(aid,IntSet.from_list [0;2])
       ;(did,IntSet.from_list [0;2])
       ;(eid,IntSet.from_list [1])
       ;(fid,IntSet.from_list [0])])
    (get_transitive_set
       transitives_regexcontext
       transitives_lenscontext
       (Regex.make_or
          (Regex.make_var did)
          (Regex.make_or
             (Regex.make_star (Regex.make_var eid))
             (Regex.make_var fid))))

let get_transitive_set_suite = "get_transitive_set Unit Tests" >:::
  [
    "test_with_no_transitives_correct" >:: test_with_no_transitives_correct ;
    "test_with_transitives_correct"    >:: test_with_transitives_correct    ;
  ]

let _ = run_test_tt_main get_transitive_set_suite

let test_reachables_set_minus_easy _ =
  assert_reachables_set_minus_equal
    (IdIntSet.from_list [(aid,0)]
    ,IdIntSet.from_list [])
    (reachables_set_minus
       (IdToIntSetDict.from_kvp_list [(aid,IntSet.from_list [0])])
       (IdToIntSetDict.from_kvp_list []))

let test_reachables_set_minus_hard _ =
  assert_reachables_set_minus_equal
    (IdIntSet.from_list [(aid,0);(aid,1)]
    ,IdIntSet.from_list [(bid,1)])
    (reachables_set_minus
       (IdToIntSetDict.from_kvp_list
          [(aid,IntSet.from_list [0;1])
          ;(bid,IntSet.from_list [0])])
       (IdToIntSetDict.from_kvp_list
          [(bid,IntSet.from_list [0;1])]))

let reachables_set_minus_suite = "get_transitive_set Unit Tests" >:::
  [
    "test_reachables_set_minus_easy" >:: test_reachables_set_minus_easy ;
    "test_reachables_set_minus_hard" >:: test_reachables_set_minus_hard ;
  ]

let _ = run_test_tt_main reachables_set_minus_suite

let gen_dnf_lens = DNFSynth.gen_dnf_lens

let test_gen_dnf_lens_const_nosoln _ =
  assert_raises
    (Failure "bad examples")
    (fun _ -> (gen_dnf_lens RegexContext.empty
       LensContext.empty
      (Regex.RegExBase "x")
      (Regex.RegExBase "y")
      [("a","b")]))
    

let test_gen_dnf_lens_const_soln _ =
  assert_dnf_lens_option_equal
    (Some ([[],Permutation.create [], ["x"], ["y"]],Permutation.create [0]))
    (gen_dnf_lens RegexContext.empty LensContext.empty
      (Regex.RegExBase "x")
      (Regex.RegExBase "y")
      [("x","y")])

let test_gen_lenses_union _ =
  assert_dnf_lens_option_equal
    (Some
      ([[],Permutation.create [], ["a"], ["y"];
        [],Permutation.create [], ["b"], ["x"]],
      Permutation.create [1;0]))
    (gen_dnf_lens RegexContext.empty LensContext.empty
      (Regex.RegExOr (Regex.RegExBase "a", Regex.RegExBase "b"))
      (Regex.RegExOr (Regex.RegExBase "x", Regex.RegExBase "y"))
      [("a","y");("b","x")])

let test_gen_lenses_three_union _ =
  assert_dnf_lens_option_equal
    (Some
      ([[],Permutation.create [], ["a"], ["y"];
        [],Permutation.create [], ["b"], ["z"];
        [],Permutation.create [], ["c"], ["x"]],
      Permutation.create [2;0;1]))
    (gen_dnf_lens RegexContext.empty LensContext.empty
      (Regex.RegExOr (Regex.RegExBase "a", Regex.RegExOr (Regex.RegExBase "b", Regex.RegExBase "c")))
      (Regex.RegExOr (Regex.RegExBase "x", Regex.RegExOr (Regex.RegExBase "y", Regex.RegExBase "z")))
      [("a","y");("b","z");("c","x")])

let test_gen_lenses_var_ident _ =
  assert_dnf_lens_option_equal
    (Some
      ([[AtomLensVariable (Lens.LensIdentity (Regex.RegExVariable (Id.make "A")))], Permutation.create [0], ["";""], ["";""]],
      Permutation.create [0]))
    (gen_dnf_lens (RegexContext.create_from_list_exn [Id.make "A",Regex.RegExBase "a",false; Id.make "B", Regex.RegExBase "b",false]) LensContext.empty
      (Regex.RegExVariable (Id.make "A"))
      (Regex.RegExVariable (Id.make "A"))
      [])

let test_gen_lenses_concat_var _ =
  assert_dnf_lens_option_equal
    (Some
      ([[AtomLensVariable (Lens.LensIdentity (Regex.RegExVariable (Id.make "A"))); AtomLensVariable (Lens.LensIdentity (Regex.RegExVariable (Id.make "B")))], Permutation.create [1;0],
        ["";"";""], ["";"";""]],
      Permutation.create [0]))
    (gen_dnf_lens (RegexContext.create_from_list_exn [Id.make "A",Regex.RegExBase "a",true; Id.make "B", Regex.RegExBase "b",true]) LensContext.empty
      (Regex.RegExConcat (Regex.RegExVariable (Id.make "A"), Regex.RegExVariable (Id.make "B")))
      (Regex.RegExConcat (Regex.RegExVariable (Id.make "B"), Regex.RegExVariable (Id.make "A")))
      ["ab","ba"])

let test_gen_lenses_concat_var_hard _ =
  assert_dnf_lens_option_equal
    (Some
      ([[AtomLensVariable(Lens.LensIdentity(Regex.RegExVariable (Id.make "A"))); AtomLensVariable(Lens.LensIdentity(Regex.RegExVariable (Id.make "A")))], Permutation.create [1;0],
        ["";"";""], ["";"";""]],
      Permutation.create [0]))
    (gen_dnf_lens (RegexContext.create_from_list_exn [Id.make "A",Regex.RegExOr (Regex.RegExBase "a", Regex.RegExBase "A"),true]) LensContext.empty
      (Regex.RegExConcat (Regex.RegExVariable (Id.make "A"), Regex.RegExVariable (Id.make "A")))
      (Regex.RegExConcat (Regex.RegExVariable (Id.make "A"), Regex.RegExVariable (Id.make "A")))
      [("Aa","aA")])

let test_gen_lenses_var_expand _ =
  assert_dnf_lens_option_equal
    (Some
      ([[], Permutation.create[], ["a"], ["a"]],
        Permutation.create [0]))
    (gen_dnf_lens (RegexContext.create_from_list_exn [Id.make "A", Regex.RegExBase "a",false]) LensContext.empty
      (Regex.RegExVariable (Id.make "A"))
      (Regex.RegExBase "a") [])

let test_gen_lenses_star _ =
  assert_dnf_lens_option_equal
  (Some ([[(AtomLensIterate ([[], Permutation.create [], ["a"], ["b"]], Permutation.create
  [0]))], Permutation.create [0], ["";""], ["";""]], Permutation.create [0]))
  (gen_dnf_lens RegexContext.empty LensContext.empty
      (Regex.RegExStar (Regex.RegExBase "a"))
      (Regex.RegExStar (Regex.RegExBase "b"))
      ["aa","bb"])

let test_gen_dnf_lens_star_difficult _ =
  assert_dnf_lens_option_equal
  (Some ([
    [(AtomLensIterate ([[], Permutation.create [], ["a"], ["b"]], Permutation.create
    [0]));
    (AtomLensIterate ([[], Permutation.create [], ["b"], ["a"]], Permutation.create
    [0]))
    ], Permutation.create [1;0], ["";"";""], ["";"";""]
    ],
    Permutation.create [0]))
  (gen_dnf_lens RegexContext.empty LensContext.empty
      (Regex.RegExConcat
        (Regex.RegExStar (Regex.RegExBase "a"),
        Regex.RegExStar (Regex.RegExBase "b")))
      (Regex.RegExConcat
        (Regex.RegExStar (Regex.RegExBase "a"),
        Regex.RegExStar (Regex.RegExBase "b")))
      ["abb","aab"])

let test_dnf_lens_star_expansion _ =
  assert_dnf_lens_option_equal
  (Some ([
    [],Permutation.create [], [""], [""];
    [(AtomLensIterate ([[], Permutation.create [], ["a"], ["a"]], Permutation.create
    [0]))], Permutation.create [0], ["a";""], ["a";""]
    ],
    Permutation.create [0;1]))
  (gen_dnf_lens RegexContext.empty LensContext.empty
      (Regex.RegExStar (Regex.RegExBase "a"))
      (Regex.RegExOr
        (Regex.RegExBase "",
        Regex.RegExConcat (Regex.RegExBase "a", Regex.RegExStar (Regex.RegExBase "a"))))
      ["a","a"])


let test_dnf_lens_star_inner_expansion _ =
  assert_dnf_lens_option_equal
    ( Some ([
      [AtomLensIterate ([
        ([],Permutation.create [], ["a"], ["a"]);
        ([AtomLensIterate ([
          ([],Permutation.create [], ["z"], ["z"])
        ],Permutation.create [0])],Permutation.create [0], ["az";""], ["az";""])
      ],Permutation.create [0;1])],Permutation.create [0], ["";""],
      ["";""]
      ],Permutation.create [0]))
    (gen_dnf_lens RegexContext.empty LensContext.empty
      (Regex.RegExStar (Regex.RegExConcat (Regex.RegExBase "a", Regex.RegExStar (Regex.RegExBase
      "z"))))
      (Regex.RegExStar (Regex.RegExOr (Regex.RegExBase "a", Regex.RegExConcat (Regex.RegExBase
      "az", Regex.RegExStar (Regex.RegExBase "z")))))
      [])


let gen_dnf_lens_suite = "gen_dnf_lens Unit Tests" >:::
  ["test_gen_dnf_lens_const_nosoln" >:: test_gen_dnf_lens_const_nosoln;
   "test_gen_dnf_lens_const_soln" >:: test_gen_dnf_lens_const_soln;
   "test_gen_lenses_union" >:: test_gen_lenses_union;
   "test_gen_lenses_three_union" >:: test_gen_lenses_three_union;
   "test_gen_lenses_var_ident" >:: test_gen_lenses_var_ident;
   "test_gen_lenses_concat_var" >:: test_gen_lenses_concat_var;
   "test_gen_lenses_var_expand" >:: test_gen_lenses_var_expand;
   "test_gen_lenses_concat_var_hard" >:: test_gen_lenses_concat_var_hard;
   "test_gen_lenses_star" >:: test_gen_lenses_star;
   "test_gen_dnf_lens_star_difficult" >:: test_gen_dnf_lens_star_difficult;
   "test_dnf_lens_star_expansion" >:: test_dnf_lens_star_expansion;
   "test_dnf_lens_star_inner_expansion" >:: test_dnf_lens_star_inner_expansion;
  ]

let _ = run_test_tt_main gen_dnf_lens_suite



let test_to_swap_concat_compose_tree_singleton _ =
  assert_swap_concat_compose_tree_equal
    (Permutation.to_swap_concat_compose_tree
      (Permutation.create [0]))
    (SCCTLeaf)

let test_to_swap_concat_compose_tree_ordered_double _ =
  assert_swap_concat_compose_tree_equal
    (Permutation.to_swap_concat_compose_tree
      (Permutation.create [0;1]))
    (SCCTConcat
      (SCCTLeaf,
      SCCTLeaf))

let test_to_swap_concat_compose_tree_swapped_double _ =
  assert_swap_concat_compose_tree_equal
    (Permutation.to_swap_concat_compose_tree
      (Permutation.create [1;0]))
    (SCCTSwap
      (SCCTLeaf,
      SCCTLeaf))

let test_to_swap_concat_compose_tree_swapped_triple _ =
  assert_swap_concat_compose_tree_equal
    (Permutation.to_swap_concat_compose_tree
      (Permutation.create [0;2;1]))
    (SCCTConcat
      ((SCCTLeaf),
      SCCTSwap
        (SCCTLeaf,
        SCCTLeaf)))

let test_to_swap_concat_compose_tree_cyclic_triple _ =
  assert_swap_concat_compose_tree_equal
    (Permutation.to_swap_concat_compose_tree
      (Permutation.create [2;1;0]))
    (SCCTSwap
      (SCCTSwap
        (SCCTLeaf,
        SCCTLeaf),
      SCCTLeaf))

let test_to_swap_concat_compose_tree_cyclic_satanic _ =
  assert_swap_concat_compose_tree_equal
    (Permutation.to_swap_concat_compose_tree
    (Permutation.create [2;0;3;1]))
    (SCCTCompose
      (SCCTConcat
        (SCCTSwap
          (SCCTConcat
            (SCCTLeaf, SCCTLeaf)
          ,SCCTLeaf)
        ,SCCTLeaf)
      ,SCCTConcat
        (SCCTConcat
          (SCCTLeaf,SCCTLeaf)
        ,SCCTSwap
          (SCCTLeaf,SCCTLeaf))))

let to_swap_concat_compose_tree_suite = "to_swap_concat_compose_tree Unit Tests" >:::
  [
    "test_to_swap_concat_compose_tree_singleton" >:: test_to_swap_concat_compose_tree_singleton;
    "test_to_swap_concat_compose_tree_ordered_double" >:: test_to_swap_concat_compose_tree_ordered_double;
    "test_to_swap_concat_compose_tree_swapped_double" >:: test_to_swap_concat_compose_tree_swapped_double;
    "test_to_swap_concat_compose_tree_swapped_triple" >:: test_to_swap_concat_compose_tree_swapped_triple;
    "test_to_swap_concat_compose_tree_cyclic_triple" >:: test_to_swap_concat_compose_tree_cyclic_triple;
    "test_to_swap_concat_compose_tree_cyclic_satanic" >:: test_to_swap_concat_compose_tree_cyclic_satanic;
  ]

let _ = run_test_tt_main to_swap_concat_compose_tree_suite




let test_atom_lens_to_lens_basic _ =
  assert_lens_equal
    (Lens.LensIdentity (Regex.RegExBase "TODO"))
    (Lens.LensIdentity (Regex.RegExBase "TODO"))

let atom_lens_to_lens_suite = "atom_lens_to_lens Unit Tests" >:::
  [
    "test_atom_lens_to_lens_basic" >:: test_atom_lens_to_lens_basic;
  ]

let _ = run_test_tt_main atom_lens_to_lens_suite



let test_simplify_lens_lensvariable _ =
  assert_lens_equal
    (Lens.LensVariable (Id.make "var"))
    (simplify_lens (Lens.LensVariable (Id.make "var")))

let test_simplify_lens_combine_identity_or _ =
  assert_lens_equal
    (Lens.LensIdentity (Regex.RegExOr(Regex.RegExVariable (Id.make "A"), Regex.RegExVariable (Id.make "B"))))
    (simplify_lens
       (Lens.LensUnion
          (Lens.LensIdentity (Regex.RegExVariable (Id.make "A"))
          ,Lens.LensIdentity (Regex.RegExVariable (Id.make "B")))))


let test_simplify_lens_combine_identity_concat _ =
  assert_lens_equal
    (Lens.LensIdentity (Regex.RegExConcat(Regex.RegExVariable (Id.make "A"), Regex.RegExVariable (Id.make "B"))))
    (simplify_lens
       (Lens.LensConcat
          (Lens.LensIdentity (Regex.RegExVariable (Id.make "A"))
          ,Lens.LensIdentity (Regex.RegExVariable (Id.make "B")))))

let test_simplify_lens_distribute_iteration _ =
  assert_lens_equal
    (Lens.LensIdentity (Regex.RegExStar (Regex.RegExVariable (Id.make "A"))))
    (simplify_lens
       (Lens.LensIterate
          (Lens.LensIdentity (Regex.RegExVariable (Id.make "A")))))

let test_simplify_lens_distribute_inverses _ =
  assert_lens_equal
    (Lens.LensConcat
       (Lens.LensConcat
          (Lens.LensIdentity (Regex.RegExVariable (Id.make "A"))
          ,Lens.LensConcat
              (Lens.LensConst ("B","b")
              ,Lens.LensIdentity (Regex.RegExVariable (Id.make "C"))))
       ,Lens.LensConst ("D","d")))
    (simplify_lens
       (Lens.LensInverse
          (Lens.LensConcat
             (Lens.LensConcat
                (Lens.LensIdentity (Regex.RegExVariable (Id.make "A"))
                ,Lens.LensConst ("b","B"))
             ,Lens.LensConcat
                 (Lens.LensIdentity (Regex.RegExVariable (Id.make "C"))
                 ,Lens.LensConst ("d","D"))))))

let test_simplify_lens_identify_consts _ =
  assert_lens_equal
    (Lens.LensIdentity (Regex.RegExBase "a"))
    (simplify_lens (Lens.LensConst ("a","a")))

let test_simplify_lens_combine_regex_consts _ =
  assert_lens_equal
    (Lens.LensIdentity (Regex.RegExBase "ab"))
    (simplify_lens (Lens.LensConcat (Lens.LensConst ("a","a"), Lens.LensConst ("b","b"))))


let simplify_lens_suite = "simplify_lens Unit Tests" >:::
  [
    "test_simplify_lens_lensvariable" >:: test_simplify_lens_lensvariable;
    "test_simplify_lens_combine_identity_or" >:: test_simplify_lens_combine_identity_or;
    "test_simplify_lens_combine_identity_concat" >:: test_simplify_lens_combine_identity_concat;
    "test_simplify_lens_distribute_iteration" >:: test_simplify_lens_distribute_iteration;
    "test_simplify_lens_distribute_inverses" >:: test_simplify_lens_distribute_inverses;
    "test_simplify_lens_identify_consts" >:: test_simplify_lens_identify_consts;
    "test_simplify_lens_combine_regex_consts" >:: test_simplify_lens_combine_regex_consts;
  ]

let _ = run_test_tt_main simplify_lens_suite


let test_boom_program_of_program_var_abstract _ =
  assert_boom_program_equal
    [BoomStmtDefinition(Id.make "r",BoomTypRegex,BoomExpRegex (Regex.RegExBase "b"))]
    (boom_program_of_program LensContext.empty [DeclRegexCreation(Id.make "r",Regex.RegExBase "b",true)])

let test_boom_program_of_program_var_concrete _ =
  assert_boom_program_equal
    [BoomStmtDefinition(Id.make "r",BoomTypRegex,BoomExpRegex (Regex.RegExBase "b"))]
    (boom_program_of_program LensContext.empty [DeclRegexCreation(Id.make "r",Regex.RegExBase "b",false)])

let test_boom_program_of_program_test_string _ =
  assert_boom_program_equal
    [BoomStmtTestRegex (Regex.RegExBase "b", "c")]
    (boom_program_of_program LensContext.empty [DeclTestString (Regex.RegExBase "b", "c")])

let test_boom_program_of_program_synthesize_program _ =
  assert_raises
    (Failure "no boom functionality for this")
    (fun _ ->
       boom_program_of_program LensContext.empty
         [DeclSynthesizeLens (Id.make "n",Regex.RegExBase "a", Regex.RegExBase "b", [])])

let test_boom_program_of_program_lens_creation _ =
  assert_boom_program_equal
    [BoomStmtDefinition
       (Id.make "n"
       ,BoomTypLens(Regex.RegExBase "a",Regex.RegExBase "b")
       ,BoomExpLens(Lens.LensVariable (Id.make "x")))]
    (boom_program_of_program LensContext.empty
       [DeclLensCreation (Id.make "n", Regex.RegExBase "a", Regex.RegExBase "b", Lens.LensVariable (Id.make "x"))])

let boom_program_of_program_suite = "boom_program_of_program Unit Tests" >:::
  [
    "test_boom_program_of_program_var_abstract" >:: test_boom_program_of_program_var_abstract;
    "test_boom_program_of_program_var_concrete" >:: test_boom_program_of_program_var_concrete;
    "test_boom_program_of_program_test_string" >:: test_boom_program_of_program_test_string;
    "test_boom_program_of_program_synthesize_program" >:: test_boom_program_of_program_synthesize_program;
    "test_boom_program_of_program_lens_creation" >:: test_boom_program_of_program_lens_creation;
  ]

let _ = run_test_tt_main boom_program_of_program_suite


(*
  a       x     d   f(abs)
 / \     / \    |
b   c   y   z   c
*)


let test_expand_regexcontext = RegexContext.create_from_list_exn
    [(Id.make "a",Regex.RegExConcat(Regex.RegExVariable (Id.make "b"),Regex.RegExVariable (Id.make "c")),false)
    ;(Id.make "b",Regex.RegExBase "b",false)
    ;(Id.make "c",Regex.RegExBase "c",false)
    ;(Id.make "x",Regex.RegExOr(Regex.RegExVariable (Id.make "y"),Regex.RegExVariable (Id.make "z")),false)
    ;(Id.make "y",Regex.RegExBase "y",false)
    ;(Id.make "z",Regex.RegExBase "z",false)
    ;(Id.make "d",Regex.RegExStar(Regex.RegExVariable (Id.make "c")),false)
    ;(Id.make "c",Regex.RegExBase "c",false)
    ;(Id.make "f",Regex.RegExBase "f",true)]

let test_expand_lenscontext = LensContext.empty

let test_expand_nothing_required_base _ =
  assert_required_expansions_equal
    (Regex.RegExBase "a", Regex.RegExBase "b", 0)
    (expand_required
       test_expand_regexcontext
       test_expand_lenscontext
       (Regex.RegExBase "a")
       (Regex.RegExBase "b"))

let test_expand_nothing_required_variable _ =
  assert_required_expansions_equal
    (Regex.RegExVariable (Id.make "a"), Regex.RegExVariable (Id.make "a"), 0)
    (expand_required
       test_expand_regexcontext
       test_expand_lenscontext
       (Regex.RegExVariable (Id.make "a"))
       (Regex.RegExVariable (Id.make "a")))

let test_expand_single_required_left_top _ =
  assert_required_expansions_equal
    (Regex.RegExConcat (Regex.RegExVariable (Id.make "b"),Regex.RegExVariable (Id.make "c")), Regex.RegExOr(Regex.RegExVariable (Id.make "b"),Regex.RegExVariable (Id.make "c")), 1)
    (expand_required
       test_expand_regexcontext
       test_expand_lenscontext
       (Regex.RegExVariable (Id.make "a"))
       (Regex.RegExOr(Regex.RegExVariable (Id.make "b"),Regex.RegExVariable (Id.make "c"))))

let test_expand_single_required_right_top _ =
  assert_required_expansions_equal
    (Regex.RegExOr(Regex.RegExVariable (Id.make "b"),Regex.RegExVariable (Id.make "c")), Regex.RegExConcat (Regex.RegExVariable (Id.make "b"),Regex.RegExVariable (Id.make "c")), 1)
    (expand_required
       test_expand_regexcontext
       test_expand_lenscontext
       (Regex.RegExOr(Regex.RegExVariable (Id.make "b"),Regex.RegExVariable (Id.make "c")))
       (Regex.RegExVariable (Id.make "a")))

let expand_required_expansions_program_suite = "expand_required_expansions Unit Tests" >:::
  [
    "test_expand_nothing_required_base" >:: test_expand_nothing_required_base;
    "test_expand_nothing_required_variable" >:: test_expand_nothing_required_variable;
    "test_expand_single_required_left_top" >:: test_expand_single_required_left_top;
    "test_expand_single_required_right_top" >:: test_expand_single_required_right_top;
  ]

let _ = run_test_tt_main expand_required_expansions_program_suite



let _ = Random.init 0

let gen_element_and_on_portions_of_flattened_or_var_regex_noints _ =
  assert_string_int_int_pair_list_pair_equal
    ("ab",[])
    (gen_element_and_on_portions_of_flattened_or_var_regex
       (false,(FRegExConcat ((false,FRegExBase "a"), (false,FRegExBase "b")))))

let gen_element_and_on_portions_of_flattened_or_var_regex_leftint _ =
  assert_string_int_int_pair_list_pair_equal
    ("ab",[(0,1)])
    (gen_element_and_on_portions_of_flattened_or_var_regex
       (false,(FRegExConcat ((true,FRegExBase "a"), (false,FRegExBase "b")))))

let gen_element_and_on_portions_of_flattened_or_var_regex_rightint _ =
  assert_string_int_int_pair_list_pair_equal
    ("ab",[(1,2)])
    (gen_element_and_on_portions_of_flattened_or_var_regex
       (false,(FRegExConcat ((false,FRegExBase "a"), (true,FRegExBase "b")))))

let gen_element_and_on_portions_of_flattened_or_var_regex_bothint _ =
  assert_string_int_int_pair_list_pair_equal
    ("ab",[(1,2);(0,1)])
    (gen_element_and_on_portions_of_flattened_or_var_regex
       (false,(FRegExConcat ((true,FRegExBase "a"), (true,FRegExBase "b")))))

let gen_element_and_on_portions_of_flattened_or_var_regex_topint _ =
  assert_string_int_int_pair_list_pair_equal
    ("ab",[(0,2)])
    (gen_element_and_on_portions_of_flattened_or_var_regex
       (true,(FRegExConcat ((false,FRegExBase "a"), (false,FRegExBase "b")))))

let get_var_focused_flattened_regex_concats _ =
  assert_id_flattened_or_var_regex_list_equal
    [(Id.make "A",
      (false, FRegExConcat((true,FRegExBase"a"),(true,FRegExBase"a"))))]
    (get_var_focused_flattened_regexs
       (RegexContext.create_from_list_exn [Id.make "A",Regex.RegExBase "a",true])
       (Regex.RegExConcat(Regex.RegExVariable (Id.make "A"), Regex.RegExVariable (Id.make "A"))))

let get_var_focused_flattened_regex_ors _ =
  assert_id_flattened_or_var_regex_list_equal
    [Id.make "A", (false,
      FRegExOr[(false,FRegExBase"c")
              ;(true,FRegExBase"a")
              ;(true,FRegExBase"b")])]
    (get_var_focused_flattened_regexs
       (RegexContext.create_from_list_exn [Id.make "A",(Regex.RegExOr (Regex.RegExBase "a",Regex.RegExBase "b")),true])
       (Regex.RegExOr(Regex.RegExBase "c", Regex.RegExVariable (Id.make "A"))))

let calculate_off_portions_easy _ =
  assert_int_int_list_equal
    [(0,1);(2,3)]
    (calculate_off_portions 4 [(1,2);(3,4)])

let calculate_off_portions_empty _ =
  assert_int_int_list_equal
    []
    (calculate_off_portions 2 [(0,1);(1,2)])

let gen_element_on_off_portions_suite = "gen_element_on_off_portions" >:::
  [
    "gen_element_and_on_portions_of_flattened_or_var_regex_noints" >:: gen_element_and_on_portions_of_flattened_or_var_regex_noints;
    "gen_element_and_on_portions_of_flattened_or_var_regex_leftint" >:: gen_element_and_on_portions_of_flattened_or_var_regex_leftint;
    "gen_element_and_on_portions_of_flattened_or_var_regex_rightint" >:: gen_element_and_on_portions_of_flattened_or_var_regex_rightint;
    "gen_element_and_on_portions_of_flattened_or_var_regex_bothint" >:: gen_element_and_on_portions_of_flattened_or_var_regex_bothint;
    "gen_element_and_on_portions_of_flattened_or_var_regex_topint" >:: gen_element_and_on_portions_of_flattened_or_var_regex_topint;
    "get_var_focused_flattened_regex_concats" >:: get_var_focused_flattened_regex_concats;
    "get_var_focused_flattened_regex_ors" >:: get_var_focused_flattened_regex_ors;
    "calculate_off_portions_easy" >:: calculate_off_portions_easy;
    "calculate_off_portions_empty" >:: calculate_off_portions_empty;
  ]

let _ = run_test_tt_main gen_element_on_off_portions_suite

let test_cost_none _ =
  assert_float_equal
    (1.0)
    (IntTreeAlignment.cost None)

let test_cost_empty _ =
  assert_float_equal
    (0.0)
    (IntTreeAlignment.cost (Some EmptyTree))

let test_cost_singleton _ =
  assert_float_equal
    0.0
    (IntTreeAlignment.cost
       (Some
          (NonemptyTree
             (Node
                (IntTreeAlignment.create_alignment_node
                   ~perm:(Permutation.create [])
                   ~pleft:[]
                   ~pright:[],
                 [])))))

let test_cost_singleton_unmapped_left _ =
  assert_float_equal
    0.5
    (IntTreeAlignment.cost
       (Some
          (NonemptyTree
             (Node
                (IntTreeAlignment.create_alignment_node
                   ~perm:(Permutation.create [])
                   ~pleft:[1]
                   ~pright:[],
                 [])))))

let test_cost_singleton_unmapped_right _ =
  assert_float_equal
    0.5
    (IntTreeAlignment.cost
       (Some
          (NonemptyTree
             (Node
                (IntTreeAlignment.create_alignment_node
                   ~perm:(Permutation.create [])
                   ~pleft:[]
                   ~pright:[1],
                 [])))))


let test_cost_singleton_recursive _ =
  assert_float_equal
    (1.0 /. 3.0)
    (IntTreeAlignment.cost
       (Some
          (NonemptyTree
             (Node
                (IntTreeAlignment.create_alignment_node
                   ~perm:(Permutation.create [0])
                   ~pleft:[]
                   ~pright:[1],
                 [Node
                    (IntTreeAlignment.create_alignment_node
                       ~perm:(Permutation.create [])
                       ~pleft:[]
                       ~pright:[],
                     [])])))))


let test_cost_singleton_recursive_imperfectred _ =
  assert_float_equal
    (1.0 /. 4.0)
    (IntTreeAlignment.cost
       (Some
          (NonemptyTree
             (Node
                (IntTreeAlignment.create_alignment_node
                   ~perm:(Permutation.create [0])
                   ~pleft:[]
                   ~pright:[],
                 [Node
                    (IntTreeAlignment.create_alignment_node
                       ~perm:(Permutation.create [])
                       ~pleft:[]
                       ~pright:[1]
                    ,[])])))))

let test_get_minimal_alignment_empty_empty _ =
  assert_int_tree_alignment_equal
    (Some EmptyTree)
    (IntTreeAlignment.get_minimal_alignment EmptyTree EmptyTree)


let test_get_minimal_alignment_empty_nonempty _ =
  assert_int_tree_alignment_equal
    None
    (IntTreeAlignment.get_minimal_alignment
       EmptyTree
       (NonemptyTree (Node (1,[]))))

let test_get_minimal_alignment_nonempty_empty _ =
  assert_int_tree_alignment_equal
    None
    (IntTreeAlignment.get_minimal_alignment
       (NonemptyTree (Node (1,[])))
       EmptyTree)

let test_get_minimal_alignment_different_nonempty _ =
  assert_int_tree_alignment_equal
    None
    (IntTreeAlignment.get_minimal_alignment
       (NonemptyTree (Node (1,[])))
       (NonemptyTree (Node (2,[]))))

let test_get_minimal_alignment_trivial _ =
  assert_int_tree_alignment_equal
    (Some
       (NonemptyTree
          (Node
             (IntTreeAlignment.create_alignment_node
                ~perm:(Permutation.create [])
                ~pleft:[]
                ~pright:[]
             ,[]))))
    (IntTreeAlignment.get_minimal_alignment
       (NonemptyTree (Node (1,[])))
       (NonemptyTree (Node (1,[]))))

let test_get_minimal_alignment_singleton_bijection _ =
  assert_int_tree_alignment_equal
    (Some
       (NonemptyTree
          (Node
             (IntTreeAlignment.create_alignment_node
                ~perm:(Permutation.create [0])
                ~pleft:[]
                ~pright:[]
             ,[(Node
                  (IntTreeAlignment.create_alignment_node
                     ~perm:(Permutation.create [])
                     ~pleft:[]
                     ~pright:[]
                  ,[]))]))))
    (IntTreeAlignment.get_minimal_alignment
       (NonemptyTree (Node (1,[Node (2,[])])))
       (NonemptyTree (Node (1,[Node (2,[])]))))

let test_get_minimal_alignment_easy_bijection _ =
  assert_int_tree_alignment_equal
    (Some
       (NonemptyTree
          (Node
             (IntTreeAlignment.create_alignment_node
                ~perm:(Permutation.create [0;1])
                ~pleft:[]
                ~pright:[]
             ,[(Node
                  (IntTreeAlignment.create_alignment_node
                     ~perm:(Permutation.create [])
                     ~pleft:[]
                     ~pright:[]
                  ,[]))
              ;(Node
                  (IntTreeAlignment.create_alignment_node
                     ~perm:(Permutation.create [])
                     ~pleft:[]
                     ~pright:[]
                  ,[]))]))))
    (IntTreeAlignment.get_minimal_alignment
       (NonemptyTree (Node (1,[Node (2,[]);Node (2,[])])))
       (NonemptyTree (Node (1,[Node (2,[]);Node (2,[])]))))

let test_get_minimal_alignment_hard_bijection _ =
  assert_int_tree_alignment_equal
    (Some
       (NonemptyTree
          (Node
             (IntTreeAlignment.create_alignment_node
                ~perm:(Permutation.create [1;0])
                ~pleft:[]
                ~pright:[]
             ,[(Node
                  (IntTreeAlignment.create_alignment_node
                     ~perm:(Permutation.create [])
                     ~pleft:[]
                     ~pright:[]
                  ,[]))
              ;(Node
                  (IntTreeAlignment.create_alignment_node
                     ~perm:(Permutation.create [])
                     ~pleft:[]
                     ~pright:[]
                  ,[]))]))))
    (IntTreeAlignment.get_minimal_alignment
       (NonemptyTree (Node (1,[Node (2,[]);Node (3,[])])))
       (NonemptyTree (Node (1,[Node (3,[]);Node (2,[])]))))

let test_get_minimal_alignment_projected_left _ =
  assert_int_tree_alignment_equal
    (Some
       (NonemptyTree
          (Node
             (IntTreeAlignment.create_alignment_node
                ~perm:(Permutation.create [])
                ~pleft:[0]
                ~pright:[]
             ,[]))))
    (IntTreeAlignment.get_minimal_alignment
       (NonemptyTree (Node (1,[Node (2,[])])))
       (NonemptyTree (Node (1,[]))))

let test_get_minimal_alignment_projected_right _ =
  assert_int_tree_alignment_equal
    (Some
       (NonemptyTree
          (Node
             (IntTreeAlignment.create_alignment_node
                ~perm:(Permutation.create [])
                ~pleft:[]
                ~pright:[0]
             ,[]))))
    (IntTreeAlignment.get_minimal_alignment
       (NonemptyTree (Node (1,[])))
       (NonemptyTree (Node (1,[Node (2,[])]))))

let test_get_minimal_alignment_projected_nomatches _ =
  assert_int_tree_alignment_equal
    (Some
       (NonemptyTree
          (Node
             (IntTreeAlignment.create_alignment_node
                ~perm:(Permutation.create [])
                ~pleft:[0]
                ~pright:[0]
             ,[]))))
    (IntTreeAlignment.get_minimal_alignment
       (NonemptyTree (Node (1,[Node (3,[])])))
       (NonemptyTree (Node (1,[Node (2,[])]))))

let tree_alignment_suite = "tree_alignment" >:::
  [
    "test_cost_none" >:: test_cost_none;
    "test_cost_empty" >:: test_cost_empty;
    "test_cost_singleton" >:: test_cost_singleton;
    "test_cost_singleton_unmapped_left" >:: test_cost_singleton_unmapped_left;
    "test_cost_singleton_unmapped_right" >:: test_cost_singleton_unmapped_right;
    "test_cost_singleton_recursive" >:: test_cost_singleton_recursive;
    "test_cost_singleton_recursive_imperfectred" >:: test_cost_singleton_recursive_imperfectred;
    "test_get_minimal_alignment_empty_empty" >:: test_get_minimal_alignment_empty_empty;
    "test_get_minimal_alignment_empty_nonempty" >:: test_get_minimal_alignment_empty_nonempty;
    "test_get_minimal_alignment_nonempty_empty" >:: test_get_minimal_alignment_nonempty_empty;
    "test_get_minimal_alignment_different_nonempty" >:: test_get_minimal_alignment_different_nonempty;
    "test_get_minimal_alignment_trivial" >:: test_get_minimal_alignment_trivial;
    "test_get_minimal_alignment_singleton_bijection" >:: test_get_minimal_alignment_singleton_bijection;
    "test_get_minimal_alignment_easy_bijection" >:: test_get_minimal_alignment_easy_bijection;
    "test_get_minimal_alignment_hard_bijection" >:: test_get_minimal_alignment_hard_bijection;
    "test_get_minimal_alignment_projected_left" >:: test_get_minimal_alignment_projected_left;
    "test_get_minimal_alignment_projected_right" >:: test_get_minimal_alignment_projected_right;
    "test_get_minimal_alignment_projected_nomatches" >:: test_get_minimal_alignment_projected_nomatches;
  ]

let _ = run_test_tt_main tree_alignment_suite
