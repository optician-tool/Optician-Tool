open Bsyntax
open Bident
open Benv
open Bprint
open Bsubst
open Bregistry
open Gen
open Regexcontext
open Lenscontext

module L = Lang
module V = Bvalue
module G = Bregistry
module BL = Blenses
module BS = Bstring
module Perms = BL.Permutations
module Perm = Permutation.Permutation

let msg = Util.format


let printList (f : 'a -> string) (l : 'a list) : string =
	let rec helper (l : 'a list) (temp : string): string =
		match l with
		| [] -> temp ^ "]"
		| [x] -> temp ^ (f x) ^ "]"
		| x :: xs -> helper xs (temp ^ (f x) ^ "; ")
	in helper l "["

let rec lrxToBrx (r : L.Regex.t) (rc: RegexContext.t) (i : Info.t) : Brx.t =
	match r with
	| L.Regex.RegExEmpty -> Brx.empty
	| L.Regex.RegExBase s -> Brx.mk_string s
	| L.Regex.RegExConcat (r1, r2) -> Brx.mk_seq (lrxToBrx r1 rc i) (lrxToBrx r2 rc i)
	| L.Regex.RegExOr (r1, r2) -> Brx.mk_alt (lrxToBrx r1 rc i) (lrxToBrx r2 rc i)
	| L.Regex.RegExStar r -> Brx.mk_star (lrxToBrx r rc i)
	| L.Regex.RegExVariable s ->
			match RegexContext.lookup rc s with
			| Some r -> Brx.mk_var (Lang.Id.string_of_id s) (lrxToBrx r rc i)
			| None -> Berror.run_error i
						(fun () -> msg "@[%s is unbound" (Lang.Id.string_of_id s) )

let sLensTobLens
		(l : L.Lens.t) (rc: RegexContext.t) (lc : LensContext.t) (i : Info.t) : BL.MLens.t =
	let constLens (s1 : string) (s2 : string) : BL.MLens.t =
		BL.MLens.clobber i (Brx.mk_string s1) s2 (fun _ -> s1) in
	let rec helper (l : L.Lens.t) : BL.MLens.t =
		match l with
		| L.Lens.LensConst (s1, s2) -> constLens s1 s2
		| L.Lens.LensConcat (l1, l2) -> BL.MLens.concat i (helper l1) (helper l2)
		| L.Lens.LensSwap (l1, l2) -> BL.MLens.permute i [1;0] [(helper l1); (helper l2)]
		| L.Lens.LensUnion (l1, l2) -> BL.MLens.union i (helper l1) (helper l2)
		| L.Lens.LensCompose (l1, l2) -> BL.MLens.compose i (helper l2) (helper l1)
		| L.Lens.LensIterate l -> BL.MLens.star i (helper l)
		| L.Lens.LensIdentity r -> BL.MLens.copy i (lrxToBrx r rc i)
		| L.Lens.LensInverse l -> BL.MLens.invert i (helper l)
		| L.Lens.LensVariable s ->
				BL.MLens.mk_var i (Lang.Id.string_of_id s)
					(helper (LensContext.lookup_impl_exn lc s))
		| L.Lens.LensPermute (s, l) ->
				BL.MLens.permute i (Perm.to_int_list s) (List.map (fun l -> helper l) l) in
	helper l

(* let getRegexp (v : V.t) (rc : RegexContext.t) : L.regex = match v with  *)
(* | V.Rx (i, r) -> Brx.brx_to_lrx r i rc | V.Str (i, s) -> Brx.brx_to_lrx     *)
(* (Brx.mk_string s) i rc | V.Chr (i, c) -> Brx.brx_to_lrx (Brx.mk_string    *)
(* (Scanf.unescaped (Char.escaped c))) i rc | _ -> Berror.run_error        *)
(* (V.info_of_t v) (fun () -> msg "Expected a regular expression or string *)
(* or character here" )                                                    *)

let getStrings (l : V.t list) : (string * string) list =
	let helper (temp : (string * string) list) (v : V.t) : (string * string) list =
		match v with
		| V.Par(_, V.Str(_, s1), V.Str(_, s2)) -> (s1, s2) :: temp
		| _ -> Berror.run_error (V.info_of_t v) (fun () -> msg "Expected a list here")
	in List.fold_left helper [] l

let rec toList (v : V.t) (temp : V.t list) : V.t list =
	match v with
	| V.Vnt (_, _, _, None) -> List.rev temp
	| V.Vnt(_, _, _, Some (V.Par(_, hd, tail))) -> toList tail (hd :: temp)
	| _ -> Berror.run_error (V.info_of_t v)
				(fun () -> msg "Expected a list here" )

let rec permutations (l : 'a list) : 'a list list =
	List.map (fun m -> Perms.permute_list m l) (Perms.permutations (List.length l))

let rec evenOdd
		(l : 'a list) (even : 'a list) (odd : 'a list) (p : int) : ('a list) * ('a list) =
	match l with
	| [] -> List.rev even, List.rev odd
	| x :: xs -> if p = 0 then evenOdd xs (x :: even) odd ((p + 1) mod 2)
			else evenOdd xs even (x :: odd) ((p + 1) mod 2)

let rec evenOddInv (even : 'a list) (odd : 'a list) (temp : 'a list) (p : int) : 'a list =
	match even, odd with
	| [], [] -> List.rev temp
	| x :: xs, odd when p = 0 -> evenOddInv xs odd (x :: temp) ((p + 1) mod 2)
	| even, y :: ys when p = 1 -> evenOddInv even ys (y :: temp) ((p + 1) mod 2)
	| _ -> Berror.run_error (Info.I ("", (0, 0), (0, 0)))
				(fun () -> msg "Lists cannot be alternated!" )

let rec getMatches (l : Brx.t list) (s : BS.t) (t : BS.t list) : BS.t list =
	match l with
	| [] -> List.rev t
	| [x] -> List.rev (s :: t)
	| x :: xs -> let s1, s2 = BS.concat_split x (Brx.concatList xs) s in
			getMatches xs s2 (s1 :: t)

let perm_canonizer (cs : BL.Canonizer.t list) (c : BL.Canonizer.t) : BL.Canonizer.t =
	let l = List.fold_left (fun l c -> (BL.Canonizer.uncanonized_type c) :: l) [] cs in
	let l = List.rev l in
	let sep = BL.Canonizer.uncanonized_type c in
	let whole = Brx.mk_perm l sep in
	let l' = List.fold_left (fun l c -> (BL.Canonizer.canonized_type c) :: l) [] cs in
	let l' = List.rev l' in
	let sep' = BL.Canonizer.canonized_type c in
	let kernel = Brx.concatList (Brx.intersperse sep' l') in
	let f (s' : string) : string =
		let s = BS.of_string s' in
		let perm = match fst (Brx.which_perm l sep s') with
			| None -> []
			| Some l -> Perms.invert_permutation l in
		let lperm = Perms.permute_list perm l in
		let matches = getMatches (Brx.intersperse sep lperm) s [] in
		let real, seps = evenOdd matches [] [] 0 in
		let real = Perms.permute_list (Perms.invert_permutation perm) real in
		let ss = List.map BS.to_string (evenOddInv real seps [] 0) in
		let ss = List.map2
				(fun c s -> BL.Canonizer.canonize c (BS.of_string s)) (Brx.intersperse c cs) ss in
		String.concat "" ss in
	let info = Info.I ("", (0, 0), (0, 0)) in
	BL.Canonizer.normalize info whole kernel f

let synth
		(v1 : V.t) (v2 : V.t) (l : V.t) (rc : RegexContext.t) (lc : LensContext.t) =
	match v1 with
	| V.Rx (i1, r1) ->
			begin
				match v2 with
				| V.Rx (i2, r2) ->
						begin
							match l with
							| V.Vnt (i3, _, _, _) ->
									let s1 = Brx.brx_to_lrx r1 i1 rc in
									let s2 = Brx.brx_to_lrx r2 i2 rc in
									(* let () = print_endline ("synthing (" ^ (L.regex_to_string s1) ^ " <=> " *)
									(* ^ (L.regex_to_string s2) ^ ")") in let () = print_newline () in let f   *)
									(* id (r, _) () = print_endline (id ^ " = " ^ L.regex_to_string r) in let  *)
									(* g id (l, r1, r2) () = print_endline (id ^ " : lens in (" ^              *)
									(* (L.regex_to_string r1) ^ " <=> " ^ (L.regex_to_string r2) ^ ") = " ^    *)
									(* L.lens_to_string l) in let h id l () = let f (lens, id) = "(" ^         *)
									(* (L.lens_to_string lens) ^ " * " ^ id in print_endline (id ^ " |-> " ^   *)
									(* (printList f l)) in let () = print_endline "regexcontext contents ..."  *)
									(* in let () = RegexContext.fold f () rc in let () = print_newline () in   *)
									(* let () = print_endline "lenscontext contents ..." in let () =           *)
									(* LensContext.fold g () lc in let () = print_newline () in let () =       *)
									(* print_endline "outgoingsD contents ..." in let () = LensContext.fold1 h *)
									(* () lc in let () = print_newline () in                                   *)
									let l = getStrings (toList l []) in
									let lens = gen_lens rc lc s1 s2 (List.rev l) in
									let lens =
										match lens with
										| None -> Berror.run_error (Info.merge_inc i1 i2)
													(fun () -> msg "Could not synthesize lens" )
										| Some lens -> lens in
									let info = Info.merge_inc i1 i3 in
									let lens' = sLensTobLens lens rc lc info in
									(* let toPrint = ("synthesized lens in (" ^ (L.regex_to_string s1) ^ " <=> *)
									(* " ^ (L.regex_to_string s2) ^ ") = " ^ L.lens_to_string lens) in let ()  *)
									(* = print_endline toPrint in let () = print_newline () in                 *)
									info, lens'
							| _ -> Berror.run_error (V.info_of_t l)
										(fun () -> msg "Synth_from_regexp expects a list here" )
						end
				| _ -> Berror.run_error (V.info_of_t v2)
							(fun () -> msg "Synth_from_regexp expects a regular expression here" )
			end
	| V.Can (i1, c1) ->
			begin
				match v2 with
				| V.Can (i2, c2) ->
						begin
							match l with
							| V.Vnt (i3, _, _, _) ->
									let s1 = Brx.brx_to_lrx (BL.Canonizer.canonized_type c1) i1 rc in
									let s2 = Brx.brx_to_lrx (BL.Canonizer.canonized_type c2) i2 rc in
									let l = getStrings (toList l []) in
									let lens = gen_lens rc lc s1 s2 l in
									let info = Info.merge_inc i1 i3 in
									let lens = match lens with
										| None -> Berror.run_error info
													(fun () -> msg "Could not synthesize lens" )
										| Some lens -> sLensTobLens lens rc lc info in
									let lens = (BL.MLens.left_quot info c1 lens) in
									info, BL.MLens.right_quot info lens c2
							| _ -> Berror.run_error (V.info_of_t l)
										(fun () -> msg "synth expects a list here" )
						end
				| _ -> Berror.run_error (V.info_of_t v2)
							(fun () -> msg "synth expects a canonizer here" )
			end
	| _ -> Berror.run_error (V.info_of_t v1)
				(fun () -> msg "synth expects a regular expression or canonizer" )

(**let rec vtoString (id : Qid.t) (v : V.t) =
	match v with
	| V.Rx (_, r) -> "Rx " ^ (Qid.string_of_t id) ^ " = " ^ (Brx.string_of_t r) ^ "\n"
	| V.Unt _ -> "Unt " ^ (Qid.string_of_t id) ^ " = ()" ^ "\n"
	| V.Bol (_, s) -> let s = match s with | None -> "true" | Some s -> s in
			"Bol " ^ (Qid.string_of_t id) ^ " = " ^ s ^ "\n"
	| V.Int (_, i) -> "Int " ^ (Qid.string_of_t id) ^ " = " ^ (string_of_int i) ^ "\n"
	| V.Chr (_, c) -> "Chr " ^ (Qid.string_of_t id) ^ " = " ^ (Char.escaped c) ^ "\n"
	| V.Str (_, s) -> "Str named " ^ (Qid.string_of_t id) ^ " = " ^ s ^ "\n"
	| V.Arx (_, r) -> "Arx " ^ (Qid.string_of_t id) ^ " = " ^ (Barx.string_of_t r) ^ "\n"
	| V.Kty _ -> "Kty " ^ (Qid.string_of_t id) ^ "\n"
	| V.Mty _ -> "Mty " ^ (Qid.string_of_t id) ^ "\n"
	| V.Lns (_, r) -> "Lns " ^ (Qid.string_of_t id) ^ " = " ^ (BL.MLens.string_of_t r) ^ "\n"
	| V.Can (_, r) -> "Lns " ^ (Qid.string_of_t id) ^ " = " ^ (BL.Canonizer.string_of_t r) ^ "\n"
	| V.Prf _ -> "Prf " ^ (Qid.string_of_t id) ^ "\n"
	| V.Fun _ -> "Fun " ^ (Qid.string_of_t id) ^ "\n"
	| V.Par (_, t1, t2) ->
			"Par " ^ (Qid.string_of_t id) ^ " = (" ^ (vtoString id t1) ^ " * " ^
			(vtoString id t2) ^ ")\n"
	| V.Vnt (_, id, _, opt) ->
			match opt with
			| None -> "Vnt " ^ (Qid.string_of_t id) ^ "\n"
			| Some v -> "Vnt " ^ (Qid.string_of_t id) ^ " = (" ^ (vtoString id v) ^ ")"**)