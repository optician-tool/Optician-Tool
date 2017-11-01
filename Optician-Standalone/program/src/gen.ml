open Stdlib
open Lenscontext
open Converter
open Regexcontext
open Lang
open Regex_utilities
open Lens_utilities
open Normalized_lang
open Consts
open Naive_gen
open Synth_structs
open Expand
open Language_equivalences

module PQ = PriorityQueueOf(QueueElement)

module type LENS_SYNTHESIZER =
sig
  val gen_lens :
    RegexContext.t ->
    LensContext.t ->
    Regex.t ->
    Regex.t ->
    examples ->
    Lens.t option
end

module type LENSSYNTH_PRIORITY_QUEUE =
sig
  type queue
  type element = QueueElement.t

  val empty : queue
  val from_list : element list -> queue
  val push : queue -> element -> queue
  val push_all : queue -> element list -> queue
  val pop : queue -> (element * int * queue) option
  val length : queue -> int
  val compare : queue -> queue -> comparison
  val to_string : queue -> string
end

module DNFSynth =
struct
  type synthesis_info =
    {
      l                    : dnf_lens                   ;
      oedr1                : ordered_exampled_dnf_regex ;
      specs_visited        : int                        ;
      expansions_performed : int                        ;
      expansions_inferred  : int                        ;
      expansions_forced    : int                        ;
    }

  let rec gen_atom_zipper (lc:LensContext.t)
      (atom1:ordered_exampled_atom)
      (atom2:ordered_exampled_atom)
    : atom_lens =
    begin match (atom1,atom2) with
      | (OEAVar (_,sorig1,_,_),OEAVar (_,sorig2,_,_)) ->
        AtomLensVariable (LensContext.shortest_path_exn lc sorig1 sorig2)
      | (OEAStar r1, OEAStar r2) ->
        AtomLensIterate (gen_dnf_lens_zipper_internal lc r1 r2)
      | _ -> failwith "invalid"
    end

  and gen_clause_zipper (lc:LensContext.t)
      ((atoms_partitions1,strs1,_):ordered_exampled_clause)
      ((atoms_partitions2,strs2,_):ordered_exampled_clause)
    : clause_lens =
    let zipped_equivs = List.zip_exn atoms_partitions1 atoms_partitions2 in
    let atom_lens_perm_part_list_list =
      List.map
        ~f:(fun (a_list1,a_list2) ->
            let thingy = List.zip_exn a_list1 a_list2 in
            List.map
              ~f:(fun ((a1,i1),(a2,i2)) ->
                  (gen_atom_zipper lc a1 a2,(i1,i2)))
              thingy
          )
        zipped_equivs in
    let atom_lens_perm_part_list = List.concat atom_lens_perm_part_list_list in
    let atom_lens_perm_part_list_by_left_atom =
      List.sort
        ~cmp:(fun (_,(x,_)) (_,(y,_)) -> compare x y)
        atom_lens_perm_part_list in
    let (atom_lenses,perm_parts) = List.unzip
        atom_lens_perm_part_list_by_left_atom in
    (atom_lenses,Permutation.create_from_doubles_unsafe perm_parts,strs1,strs2)


  and gen_dnf_lens_zipper_internal
      (lc:LensContext.t)
      (r1:ordered_exampled_dnf_regex)
      (r2:ordered_exampled_dnf_regex)
    : dnf_lens =
    let zipped_equivs = List.zip_exn r1 r2 in
    let clause_lens_perm_part_list_list =
      List.map
        ~f:(fun (cl_list1,cl_list2) ->
            let thingy = List.zip_exn cl_list1 cl_list2 in
            List.map
              ~f:(fun ((cl1,i1),(cl2,i2)) ->
                  (gen_clause_zipper lc cl1 cl2,(i1,i2)))
              thingy
          )
        zipped_equivs in
    let clause_lens_perm_part_list = List.concat clause_lens_perm_part_list_list in
    let clause_lens_perm_part_list_by_left_clause =
      List.sort
        ~cmp:(fun (_,(x,_)) (_,(y,_)) -> compare x y)
        clause_lens_perm_part_list in
    let (clause_lenses,perm_parts) = List.unzip
        clause_lens_perm_part_list_by_left_clause in
    (clause_lenses,Permutation.create_from_doubles_unsafe perm_parts)

  let rigid_synth
      (rc:RegexContext.t)
      (lc:LensContext.t)
      (qe:QueueElement.t)
      (exs:examples)
      (count:int)
    : synthesis_info option =
    let r1 = QueueElement.get_r1 qe in
    let r2 = QueueElement.get_r2 qe in
    if (get_dnf_size r1 <> get_dnf_size r2) then
      None
    else
      let (lexs,rexs) = List.unzip exs in
      let exampled_r1_opt = regex_to_exampled_dnf_regex rc lc r1 lexs in
      let exampled_r2_opt = regex_to_exampled_dnf_regex rc lc r2 rexs in
      begin match (exampled_r1_opt,exampled_r2_opt) with
        | (Some exampled_r1,Some exampled_r2) ->
          let e_o_r1 = to_ordered_exampled_dnf_regex exampled_r1 in
          let e_o_r2 = to_ordered_exampled_dnf_regex exampled_r2 in
          begin match make_matchable (compare_ordered_exampled_dnf_regexs e_o_r1 e_o_r2) with
            | EQ ->
              Some (
                {
                  l = gen_dnf_lens_zipper_internal lc e_o_r1 e_o_r2;
                  oedr1 = e_o_r1;
                  specs_visited = count;
                  expansions_performed = (QueueElement.get_expansions_performed qe);
                  expansions_inferred = (QueueElement.get_expansions_inferred qe);
                  expansions_forced = (QueueElement.get_expansions_forced qe);
                })
            | _ -> None
          end
        | _ -> failwith "bad examples"
      end

  let gen_dnf_lens_and_info_zipper
      (rc:RegexContext.t)
      (lc:LensContext.t)
      (r1:Regex.t)
      (r2:Regex.t)
      (exs:examples)
    : synthesis_info option =
    let count = ref 0 in
    let rec gen_dnf_lens_zipper_queueing
        (queue:PQ.t)
      : synthesis_info option =
      begin match PQ.pop queue with
        | None -> None
        | Some (qe,_,q) ->
          incr(count);
          if !verbose then
            (print_endline "popped";
             print_endline ("r1: " ^ Regex.show (QueueElement.get_r1 qe));
             print_endline "\n\n";
             print_endline ("r2: " ^ Regex.show (QueueElement.get_r2 qe));
             print_endline "\n\n";
             print_endline ("count: " ^ (string_of_int !count));
             print_endline "\n\n";
             print_endline ("exps_perfed: " ^ (string_of_int (QueueElement.get_expansions_performed qe)));
             print_endline "\n\n";
             print_endline ("exps_inferred: " ^ (string_of_int (QueueElement.get_expansions_inferred qe)));
             print_endline "\n\n";
             print_endline ("exps_forced: " ^ (string_of_int (QueueElement.get_expansions_forced qe)));
             print_endline ("\n\n\n"));
          let result_o =
            rigid_synth
              rc
              lc
              qe
              exs
              !count
          in
          begin match result_o with
            | Some _ -> result_o
            | None ->
              let queue_elements = 
                expand
                  rc
                  lc
                  qe
              in
              gen_dnf_lens_zipper_queueing
                (PQ.push_all
                   q
                   queue_elements)
          end
      end
    in
      gen_dnf_lens_zipper_queueing
      (PQ.from_list
         [
           QueueElement.make
             ~r1:r1
             ~r2:r2
             ~expansions_performed:0
             ~expansions_inferred:0
             ~expansions_forced:0
           ])


  let gen_dnf_lens (rc:RegexContext.t) (lc:LensContext.t) (r1:Regex.t) (r2:Regex.t)
      (exs:examples)
    : dnf_lens option =
    Option.map ~f:(fun x -> x.l) (gen_dnf_lens_and_info_zipper rc lc r1 r2 exs)

  let expansions_performed_for_gen
      (rc:RegexContext.t)
      (lc:LensContext.t)
      (r1:Regex.t)
      (r2:Regex.t)
      (exs:examples)
    : int option =
    Option.map ~f:(fun x -> x.expansions_performed) (gen_dnf_lens_and_info_zipper rc lc r1 r2 exs)

  let specs_visited_for_gen
      (rc:RegexContext.t)
      (lc:LensContext.t)
      (r1:Regex.t)
      (r2:Regex.t)
      (exs:examples)
    : int option =
    Option.map ~f:(fun x -> x.specs_visited) (gen_dnf_lens_and_info_zipper rc lc r1 r2 exs)

  let expansions_inferred_for_gen
      (rc:RegexContext.t)
      (lc:LensContext.t)
      (r1:Regex.t)
      (r2:Regex.t)
      (exs:examples)
    : int option =
    Option.map ~f:(fun x -> x.expansions_inferred) (gen_dnf_lens_and_info_zipper rc lc r1 r2 exs)

  let expansions_forced_for_gen
      (rc:RegexContext.t)
      (lc:LensContext.t)
      (r1:Regex.t)
      (r2:Regex.t)
      (exs:examples)
    : int option =
    Option.map ~f:(fun x -> x.expansions_forced) (gen_dnf_lens_and_info_zipper rc lc r1 r2 exs)

  let gen_lens
      (rc:RegexContext.t)
      (lc:LensContext.t)
      (r1:Regex.t)
      (r2:Regex.t)
      (exs:examples)
    : Lens.t option =
      let dnf_lens_option = gen_dnf_lens rc lc r1 r2 exs in
      Option.map
        ~f:dnf_lens_to_lens
        dnf_lens_option

  let num_possible_choices
      (rc:RegexContext.t)
      (lc:LensContext.t)
      (r1:Regex.t)
      (r2:Regex.t)
      (exs:examples)
    : float option =
    let rec get_possibible_lenses_oedr
        (oedr:ordered_exampled_dnf_regex)
      : float =
      List.fold_left
        ~f:(fun acc oecl ->
            acc *.
            (Math.factorial (List.length oecl)) *.
            (get_possible_lenses_oec (fst (List.hd_exn oecl))))
        ~init:1.0
        oedr
    and get_possible_lenses_oec
        ((oec,_,_):ordered_exampled_clause)
      : float =
      List.fold_left
        ~f:(fun acc oeal ->
            acc *.
            (Math.factorial (List.length oeal)) *.
            (get_possible_lenses_oea (fst (List.hd_exn oeal))))
        ~init:1.0
        oec
    and get_possible_lenses_oea
        (oea:ordered_exampled_atom)
      : float =
      begin match oea with
      | OEAVar _ -> 1.0
      | OEAStar dr ->
        get_possibible_lenses_oedr dr
      end
    in
    Option.map
      ~f:(fun x -> get_possibible_lenses_oedr x.oedr1)
      (gen_dnf_lens_and_info_zipper rc lc r1 r2 exs)
end

let expansions_performed_for_gen = DNFSynth.expansions_performed_for_gen
let specs_visited_for_gen = DNFSynth.specs_visited_for_gen
let expansions_inferred_for_gen = DNFSynth.expansions_inferred_for_gen
let expansions_forced_for_gen = DNFSynth.expansions_forced_for_gen
let num_possible_choices = DNFSynth.num_possible_choices

let gen_lens
    (rc:RegexContext.t)
    (lc:LensContext.t)
    (r1:Regex.t)
    (r2:Regex.t)
    (exs:examples)
  : Lens.t option =
  if !verbose then
    print_endline "Synthesis Start";
  let rc_orig = rc in
  let lens_option =
    if !naive_strategy then
      Some (gen_lens_naive rc lc r1 r2 exs)
    else
      DNFSynth.gen_lens rc lc r1 r2 exs
  in
  if !verbose then
    print_endline "Synthesis End";
  if !simplify_generated_lens then
    Option.map
      ~f:(simplify_lens % (make_lens_safe_in_smaller_context rc_orig rc))
      lens_option
  else
    Option.map
      ~f:((make_lens_safe_in_smaller_context rc_orig rc))
      lens_option

