(******************************************************************************)
(* The Harmony Project                                                        *)
(* harmony@lists.seas.upenn.edu                                               *)
(******************************************************************************)
(* Copyright (C) 2008 J. Nathan Foster and Benjamin C. Pierce                 *)
(*                                                                            *)
(* This library is free software; you can redistribute it and/or              *)
(* modify it under the terms of the GNU Lesser General Public                 *)
(* License as published by the Free Software Foundation; either               *)
(* version 2.1 of the License, or (at your option) any later version.         *)
(*                                                                            *)
(* This library is distributed in the hope that it will be useful,            *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of             *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU          *)
(* Lesser General Public License for more details.                            *)
(******************************************************************************)
(* /src/binterp.ml                                                            *)
(* Boomerang interpreter *)
(* $Id: binterp.ml 4999 2011-03-17 12:38:28Z mgree $ *)
(******************************************************************************)

(* -------------------------------------------------------------------------- *)
(* IMPORTS AND ABBREVIATIONS                                               *)

open Bsyntax
open Bident
open Benv
open Bprint
open Bsubst
open Bregistry
open Regexcontext
open Lenscontext
open Gen

module L = Lang
module V = Bvalue
module G = Bregistry
module BL = Blenses
module BS = Bstring
module Perms = BL.Permutations
module Perm = Permutation.Permutation

(* -------------------------------------------------------------------------- *)
(* ERRORS / DEBUGGING                                                      *)

let msg = Util.format

let test_error i msg_thk =
	raise (Error.Harmony_error
			(fun () -> msg "@[%s: Unit test failed @ " (Info.string_of_t i);
						msg_thk ();
						msg "@]"))

(* -------------------------------------------------------------------------- *)
(* UNIT TESTS                                                              *)

(* test results: success with a value, or failure with an error message *)
type testresult = OK of Bvalue.t | Error of (unit -> unit)

let tests = Prefs.testPref
let test_all = Prefs.testallPref

(* [check_test m] returns [true] iff the command line arguments            *)
(* '-test-all' or '-test m' are set                                        *)
let check_test ms =
	Safelist.fold_left
		(fun r qs -> r || (Qid.id_prefix (G.parse_qid qs) ms))
		(Prefs.read test_all)
		(Prefs.read tests)

(* -------------------------------------------------------------------------- *)
(* INTERPRETER                                                             *)

(* dynamic match: determine if a value *does* match a pattern; return the  *)
(* list of value bindings for variables.                                   *)
let rec dynamic_match i p0 v0 = match p0, v0 with
	| PWld _, _ -> Some []
	| PVar(_, q, so), _ -> Some [(q, v0, so)]
	| PUnt _, V.Unt(_) -> Some []
	| PInt(_, n1), V.Int(_, n2) -> if n1 = n2 then Some [] else None
	| PBol(_, b1), V.Bol(_, b2) ->
			if (b1 && (b2 = None)) || (not b1 && (b2 <> None)) then Some []
			else None
	| PCex(_, p), V.Bol(vi, Some s) -> dynamic_match i p (V.mk_s vi s)
	| PStr(_, s1), V.Str(_, s2) -> if s1 = s2 then Some [] else None
	| PVnt(_, (_, li), pio), V.Vnt(_, _, lj, vjo) ->
			if Id.equal li lj then
				match pio, vjo with
				| None, None -> Some []
				| Some pi, Some vj -> dynamic_match i pi vj
				| _ ->
						Berror.run_error i
							(fun () ->
										msg "@[wrong@ number@ of@ arguments@ to@ constructor@ %s@]"
											(Id.string_of_t li))
			else None
	| PPar(_, p1, p2), V.Par(_, v1, v2) ->
			(match dynamic_match i p1 v1, dynamic_match i p2 v2 with
				| Some l1, Some l2 -> Some (l1 @ l2)
				| _ -> None)
	| _ -> None

(* ----- interpret casts ----- counters for parallel and in-line checks *)
let pc = ref 0
let ic = ref 0
let mc = ref 0

(* precondition: f and t must be compatible. *)
let rec interp_cast (wq: ((unit -> V.t) -> unit) option) cev b f t =
	(* generates cast into the refinement (x:t where e) *)
	let cast_refinement mandatory f x t e =
		let rec run_check wq v =
			let v = interp_cast wq cev b f t v in
			let cev' = CEnv.update cev (Qid.t_of_id x) (G.Unknown, v) in
			match V.get_x (interp_exp wq cev' e) with
			| None -> v
			| Some cex ->
					let cex_s =
						if cex = "" then ""
						else "; counterexample: " ^ cex in
					Berror.blame_error b
						(fun () ->
							(* TODO show bindings of free vars in e *)
									Util.format "@[%s=%a@ did@ not@ satisfy@ %a%s@]"
										(Id.string_of_t x)
										(fun _ -> V.format) v
										(fun _ -> format_exp) e
										cex_s) in
		if Prefs.read Prefs.unsafePref
		then (* no checking at all *)
		(fun v -> v)
		else if ((not mandatory) && wq <> None)
		then (* parallel checking *)
		(fun v ->
					incr pc;
					let wq = Util.extractValueFromOption wq in
					wq (fun () -> run_check None v);
					v)
		else (* in-line mandatory checking *)
		(fun v ->
					if mandatory then incr mc;
					incr ic;
					run_check wq v) in
	let native_coercion x =
		let q = Qid.mk_native_prelude_t b x in
		match CEnv.lookup cev q with
		| Some(_, v) -> V.get_f v wq
		| None ->
				Berror.run_error b
					(fun () -> msg "@[%s unbound@]"
									(Qid.string_of_t q)) in
	let res =
		if Bcheck.trivial_cast f t then (fun v -> v)
		else
			match f, t with
			| SUnit, SUnit
			| SBool, SBool
			| SInteger, SInteger
			| SChar, SChar
			| SString, SString
			| SRegexp, SRegexp
			| SAregexp, SAregexp
			| SLens, SLens
			| SCanonizer, SCanonizer
			| SVar(_), SVar(_) ->
					(fun v -> v)
			| SPrefs f, SPrefs t when f = t ->
					(fun v -> v)
			| SChar, SString ->
					native_coercion "string_of_char"
			| SChar, SRegexp ->
					(fun v ->
								native_coercion "regexp_of_string"
									(native_coercion "string_of_char" v))
			| SChar, SAregexp ->
					(fun v ->
								native_coercion "rxlift"
									(native_coercion "regexp_of_string"
											(native_coercion "string_of_char" v)))
			| SChar, SLens ->
					(fun v ->
								native_coercion "copy"
									(native_coercion "regexp_of_string"
											(native_coercion "string_of_char" v)))
			| SString, SRegexp ->
					native_coercion "regexp_of_string"
			| SString, SAregexp ->
					(fun v ->
								native_coercion "rxlift"
									(native_coercion "regexp_of_string" v))
			| SString, SLens ->
					(fun v ->
								native_coercion "copy"
									(native_coercion "regexp_of_string" v))
			| SRegexp, SAregexp ->
					native_coercion "rxlift"
			| SRegexp, SLens ->
					native_coercion "copy"
			| SFunction(x, f1, f2), SFunction(y, t1, t2) ->
					let fn = Id.mk b "fn" in
					let c1 = Bcheck.mk_cast "function argument" b t1 f1 (mk_var y) in
					let c2 = Bcheck.mk_cast "function result" b f2 t2 (mk_app b (mk_var fn) (mk_var x)) in
					(fun v ->
								let cev' = CEnv.update cev (Qid.t_of_id fn) (G.Unknown, v) in
								interp_exp wq cev' (mk_fun b y t1 (mk_let b x f1 c1 c2)))
			| SProduct(f1, f2), SProduct(t1, t2) ->
			(* JNF: can this first case happen? why isn't this a trivial cast?   *)
			(* if syneq_sort f1 t1 && syneq_sort f2 t2 then (fun v -> v) else    *)
					(fun v ->
								let x = Id.mk b "x" in
								let y = Id.mk b "y" in
								let v1, v2 = V.get_p v in
								let cev' =
									CEnv.update (CEnv.update cev (Qid.t_of_id x) (G.Unknown, v1))
										(Qid.t_of_id y) (G.Unknown, v2) in
								let c1 = Bcheck.mk_cast "pair fst" b f1 t1 (mk_var x) in
								let c2 = Bcheck.mk_cast "pair snd" b f2 t2 (mk_var y) in
								interp_exp wq cev' (EPair(b, c1, c2)))
			| SData(fl, x), SData(tl, y) when Qid.equal x y ->
					let rec aux acc l1 l2 = acc && match l1, l2 with
						| [],[] -> true
						| h1:: t1, h2:: t2 -> aux (syneq_sort h1 h2) t1 t2
						| _ -> false in
					if aux true fl tl then (fun v -> v)
					else
						let _, (svl, cl) = Bcheck.get_type (CEnv.lookup_type cev) b x in
						let fsubst = Safelist.combine svl fl in
						let tsubst = Safelist.combine svl tl in
						let cl_finst = Bcheck.inst_cases fsubst cl in
						let cl_tinst = Bcheck.inst_cases tsubst cl in
						let x = Id.mk b "x" in
						let qx = Qid.t_of_id x in
						let y = Id.mk b "y" in
						let qy = Qid.t_of_id y in
						let pl = Safelist.map
								(fun ((li, fio), (_, tio)) ->
											match fio, tio with
											| None, None ->
													let pi = PVnt(b, li, None) in
													let ei = EVar(b, qx) in
													(pi, ei)
											| Some fi, Some ti ->
													let li_f =
														Safelist.fold_right
															(fun tj acc -> ETyApp(b, acc, tj))
															tl (EVar(b, li)) in
													let py = PVar(b, y, Some fi) in
													let pi = PVnt(b, li, Some py) in
													(* this cast must not be expanded! (it would     *)
													(* loop on recursive data types)                 *)
													let ei = EApp(b, li_f, ECast(b, fi, ti, b, EVar(b, qy))) in
													(pi, ei)
											| _ ->
													Berror.run_error b
														(fun () ->
																	msg "@[cannot@ cast@ different@ datatypes@]"))
								(Safelist.combine cl_finst cl_tinst) in
						(fun v ->
									let cev' = CEnv.update cev (Qid.t_of_id x) (G.Unknown, v) in
									interp_exp wq cev' (ECase(b, EVar(b, qx), pl, Some t)))
			| SRefine(x, _, t1, e1, _), SRefine(y, mandatory, t2, e2, _) ->
					if Id.equal x y && syneq_sort t1 t2 && syneq_exp e1 e2
					then (fun v -> v)
					else cast_refinement mandatory f y t2 e2
			| _, SRefine(x, mandatory, t2, e2, _) ->
					cast_refinement mandatory f x t2 e2
			| SRefine(x, _, f1, e1, _), t1 ->
					interp_cast wq cev b f1 t1
			| SForall(x, f1), SForall(y, t1) ->
			(* no need to freshen since compatibility substitutes *)
					(interp_cast wq cev b f1 t1)
			| _ ->
					Berror.run_error b
						(fun () ->
									msg "@[cannot@ cast@ incompatible@ %s@ to@ %s@]"
										(string_of_sort f) (string_of_sort t)) in
	res

(* ----- interpret expressions ----- *)

and interp_exp wq cev e0 =
	match e0 with
	| ESynth(i, e1, e2, e3) ->
			let v1 = interp_exp wq cev e1 in
			let v2 = interp_exp wq cev e2 in
			let v3 = interp_exp wq cev e3 in
			let rec populate_rc tbl rc s =
				begin
					match RegexContext.lookup rc s with
					| Some _ -> rc
					| None ->
							begin
								match Hashtbl.find tbl s with
								| V.Rx (i, r) ->
										let free = Brx.free_vars r (Lang.Id.string_of_id s) in
										let free = List.map Lang.Id.make free in
										let rc = List.fold_left (fun rc id -> populate_rc tbl rc id) rc free in
										let r = Brx.brx_to_lrx r i rc in
										RegexContext.insert_exn rc s r false
								| _ -> rc
							end
				end in
			let f id (_, v) (tbl, l) =
				let s = Lang.Id.make (Qid.string_of_t id) in
				let () = Hashtbl.add tbl s v in tbl, s :: l in
			let tbl, ids = CEnv.fold f cev (Hashtbl.create 17, []) in
			let rc = List.fold_left (fun rc id -> populate_rc tbl rc id) RegexContext.empty ids in
			let rec populate_lc tbl lc s =
				begin
					match LensContext.lookup lc s with
					| Some _ -> lc
					| None ->
							begin
								match Hashtbl.find tbl s with
								| V.Lns (i, l) ->
										let free = BL.MLens.free_vars l (Lang.Id.string_of_id s) in
										let free = List.map Lang.Id.make free in
										let lc = List.fold_left (fun lc id -> populate_lc tbl lc id) lc free in
										begin match BL.MLens.bLensTosLens i l rc lc with
											| None -> lc
											| Some (l, r1, r2) -> Lenscontext.LensContext.insert_exn lc s l r1 r2
										end
								| _ -> lc
							end
				end in
			let f id (_, v) (tbl, l) =
				let s = Lang.Id.make (Qid.string_of_t id) in
				let () = Hashtbl.add tbl s v in tbl, s :: l in
			let tbl, ids = CEnv.fold f cev (Hashtbl.create 17, []) in
			let lc = List.fold_left (fun lc id -> populate_lc tbl lc id) LensContext.empty ids in
			let info, lens = Bsynth.synth v1 v2 v3 rc lc in
			begin
				match v1, v2 with
				| V.Rx(_, r1), V.Rx(_, r2) ->
						let lens = BL.MLens.set_synth_stype lens r1 in
						let lens = BL.MLens.set_synth_vtype lens r2 in
						V.Lns (info, lens)
				| _ -> V.Lns (info, lens)
			end
	
	| EId(i, e1) ->
			let v1 = interp_exp wq cev e1 in
			begin
				match v1 with
				| V.Str (j, s) -> V.Can (i, BL.Canonizer.copy j (Brx.mk_string s))
				| V.Chr (j, c) ->
						let s = Scanf.unescaped (Char.escaped c) in
						V.Can (i, BL.Canonizer.copy j (Brx.mk_string s))
				| V.Rx (j, r) -> V.Can (i, BL.Canonizer.copy j r)
				| _ -> Berror.run_error i (fun () -> msg
											"The id construct expects a regular expression" )
			end
	
	| EProject(i, e1, e2) ->
			let v1 = interp_exp wq cev e1 in
			let v2 = interp_exp wq cev e2 in
			begin
				match v1 with
				| V.Rx (j, r) ->
						begin
							match v2 with
							| V.Str (_, s) ->
									if not (BS.match_rx r (BS.of_string s)) then
										Berror.run_error i (fun () -> msg
															"@[%s@ must be a member of %s@]" s (Brx.string_of_t r)) else
										V.Can (i, BL.Canonizer.normalize j r (Brx.mk_string s) (fun _ -> s))
							| _ -> Berror.run_error i (fun () -> msg
														"The second part of the project construct should be a string")
						end
				| _ -> Berror.run_error i (fun () -> msg
											"The first part of the project construct should be a regular expression")
			end
	
	| EPerm(i, e1, e2) ->
			let v1 = interp_exp wq cev e1 in
			let v2 = interp_exp wq cev e2 in
			let get_cans (l : V.t list) : BL.Canonizer.t list =
				let f (temp : BL.Canonizer.t list) (v : V.t) : BL.Canonizer.t list =
					match v with
					| V.Can (_, c) -> c :: temp
					| _ -> Berror.run_error (V.info_of_t v) (fun () -> msg
												"I was expecting a canonizer here")
				in List.fold_left f [] l in
			begin
				match v2 with
				| V.Can(_, sep) ->
						let l = List.rev (get_cans (V.to_list v1)) in
						V.Can (i, Bsynth.perm_canonizer l sep)
				| _ -> Berror.run_error (V.info_of_t v2) (fun () -> msg
											"I was expecting a canonizer here")
			end
	
	| EVar(i, q) ->
			begin
				match CEnv.lookup_both cev q with
				| Some((G.Unknown, v), _) -> v
				| Some((G.Sort s, v), s_env) ->
						let s_base = Bsubst.erase_sort s in
						(interp_cast wq s_env i s s_base) v
				| None ->
						Berror.run_error i
							(fun () -> msg "@[%s unbound@]"
											(Qid.string_of_t q))
			end
	| EOver(i, op, _) ->
			Berror.run_error i
				(fun () ->
							msg "@[unresolved@ overloaded@ operator %s@]"
								(string_of_op op))
	
	| EApp(_, e1, e2) ->
			let v1 = interp_exp wq cev e1 in
			let v2 = interp_exp wq cev e2 in
			(V.get_f v1) wq v2
	
	| ELet(_, b, e) ->
			let bcev, _ = interp_binding wq cev b in
			interp_exp wq bcev e
	
	| EFun(i, p, _, e) ->
			let f wq v = (* !!! param'd on wq, to determine parallel/mainline eval *)
				let qp = Qid.t_of_id (id_of_param p) in
				let body_cev = CEnv.update cev qp (G.Unknown, v) in
				interp_exp wq body_cev e in
			V.Fun(i, f)
	
	| EPair(i, e1, e2) ->
			let v1 = interp_exp wq cev e1 in
			let v2 = interp_exp wq cev e2 in
			V.Par(i, v1, v2)
	
	| ECase(i, e1, pl, _) ->
			let v1 = interp_exp wq cev e1 in
			let rec find_match = function
				| [] ->
						Berror.run_error i
							(fun () ->
										msg "@[match@ failure@]")
				| (pi, ei):: rest ->
						(match dynamic_match i pi v1 with
							| None -> find_match rest
							| Some l -> l, ei) in
			let binds, ei = find_match pl in
			let qid_binds = Safelist.map
					(fun (x, v, so) ->
								let rs = match so with
									| None -> G.Unknown
									| Some s -> G.Sort s in
								(Qid.t_of_id x, (rs, v))) binds in
			let ei_cev = CEnv.update_list cev qid_binds in
			interp_exp wq ei_cev ei
	
	(* tyfuns are interpreted as functions; tyapps apply to unit *)
	| ETyFun(i, _, e) ->
			interp_exp wq cev (EFun(i, Param(i, Id.wild, SUnit), None, e))
	
	| ETyApp(i, e1, s2) ->
			interp_exp wq cev (EApp(i, e1, EUnit(i)))
	
	| EGrammar(i, ps) ->
			Berror.run_error i (fun () -> msg "@[unexpected@ grammar@ expression@ at@ interpreter@]")
	
	(* constants *)
	| EUnit(i) -> V.Unt(i)
	| EBoolean(i, None) -> V.Bol(i, None)
	| EBoolean(i, Some e1) -> V.Bol(i, Some (V.get_s (interp_exp wq cev e1)))
	| EInteger(i, n) -> V.Int(i, n)
	| EChar(i, c) -> V.Chr(i, c)
	| EString(i, s) -> V.Str(i, s)
	| ECSet(i, pos, cs) ->
			let csi = Safelist.map (fun (ci, cj) -> (Char.code ci, Char.code cj)) cs in
			let mk = if pos then Brx.mk_cset else Brx.mk_neg_ascii_cset in
			V.Rx(i, mk csi)
	
	| ECast(i, f, t, b, e) ->
			(interp_cast wq cev b f t)
				(interp_exp wq cev e)

and interp_binding wq cev b0 = match b0 with
	| Bind(i, p, so, e) ->
			let v = interp_exp wq cev e in
			let v =
				begin
					match v with
					| V.Lns(i, l) ->
							begin
								match p, so with
								| PVar (_, id, _), Some (SRefine (_, _, _, _, Some (e1, e2))) ->
										let v1 = interp_exp wq cev e1 in
										let v2 = interp_exp wq cev e2 in
										begin
											match v1, v2 with
											| V.Rx(_, r1), V.Rx(_, r2) ->
													let s = Id.string_of_t id in
													let l = BL.MLens.mk_var i s l in
													let l = BL.MLens.set_synth_stype l r1 in
													let l = BL.MLens.set_synth_vtype l r2 in
													V.Lns (i, l)
											| _ -> v
										end
								| _ -> v
							end
					| V.Rx(i, r) ->
							begin
								match p with
								| PVar (_, id, _) -> V.Rx (i, (Brx.mk_var (Id.string_of_t id) r))
								| _ -> v
							end
					| _ -> v
				end in
			let xs_rev, bcev = match dynamic_match i p v with
				| None -> Berror.run_error i
							(fun () -> msg "@[in let-binding: %s does not match %s@]"
											(string_of_pat p) (V.string_of_t v))
				| Some binds ->
						Safelist.fold_left
							(fun (xsi, cevi) (xi, vi, soi) ->
										let qxi = Qid.t_of_id xi in
										let rsi = match soi with
											| None -> G.Unknown
											| Some s -> G.Sort s in
										(qxi:: xsi, CEnv.update cevi (Qid.t_of_id xi) (rsi, vi)))
							([], cev) binds in
			(bcev, Safelist.rev xs_rev)

let rec interp_decl wq cev ms d0 = match d0 with
	| DLet(i, b) -> interp_binding wq cev b
	| DType(i, svl, qx, cl) ->
			let sx = SData(sl_of_svl svl, qx) in
			let mk_univ s =
				Safelist.fold_right
					(fun svi acc -> SForall(svi, acc))
					svl s in
			let mk_impl v =
				Safelist.fold_right
					(fun _ f -> V.Fun(i, (fun _ v -> f)))
					svl v in
			let new_cev, xs =
				Safelist.fold_left
					(fun (cev, xs) (l, so) ->
								let ql = Qid.t_of_id l in
								let rv = match so with
									| None ->
											let s = mk_univ sx in
											let v = mk_impl (V.Vnt(i, qx, l, None)) in
											(G.Sort s, v)
									| Some s ->
											let s = mk_univ (SFunction(Id.wild, s, sx)) in
											let f _ v = V.Vnt(V.info_of_t v, qx, l, Some v) in
											let v = mk_impl (V.Fun(i, f)) in
											(G.Sort s, v) in
								(CEnv.update cev ql rv, Qid.t_of_id l:: xs))
					(cev,[]) cl in
			let qcl = Safelist.map (fun (x, so) -> (Qid.t_of_id x, so)) cl in
			let new_cev' = CEnv.update_type new_cev svl qx qcl in
			(new_cev', xs)
	
	| DMod(i, n, ds) ->
			let m_cev, names = interp_mod_aux wq cev ms ds in
			let n_cev, names_rev =
				Safelist.fold_left
					(fun (n_cev, names) q ->
								match CEnv.lookup m_cev q with
								| Some rv ->
										let nq = Qid.id_dot n q in
										(CEnv.update n_cev nq rv, nq:: names)
								| None ->
										Berror.run_error i
											(fun () -> msg "@[@ declaration@ for@ %s@ missing@]"
															(Qid.string_of_t q)))
					(cev,[])
					names in
			(n_cev, Safelist.rev names_rev)
	
	| DTest(i, e, tr) ->
			begin
				(* disable parallel checking for [test ... = error] *)
				let wq = if tr = TestError then None else wq in
				if check_test ms then
					let vo =
						try OK(interp_exp wq cev e)
						with
						| (Error.Harmony_error(err)) -> Error err
						| exn ->
								if Prefs.read Prefs.unsafePref
								then
									Error (fun () ->
												msg
													"Test result: native exception@\n%s@\n%!"
													(Printexc.to_string exn))
								else raise exn in
					match vo, tr with
					| OK (v), TestPrint ->
							msg "Test result:@ ";
							V.format v;
							msg "@\n%!"
					| OK (v), TestSortPrint(Some s) ->
							msg "Test result:@ ";
							format_sort s;
							msg "@\n%!"
					| OK (v), TestSortPrint(None)
					| OK (v), TestSortEqual(None, _) ->
							Berror.run_error i
								(fun () -> msg "@[unannotated@ unit@ test@]")
					| Error err, TestPrint
					| Error err, TestSortPrint _ ->
							test_error i
								(fun () ->
											msg "Test result: error@\n";
											err ();
											msg "@\n%!")
					| Error _, TestError -> ()
					| OK v1, TestEqual e2 ->
							let v2 = interp_exp wq cev e2 in
							if not (V.equal v1 v2) then
								test_error i
									(fun () ->
												msg "@\nExpected@ "; V.format v2;
												msg "@ but found@ "; V.format v1;
												msg "@\n%!")
					| OK v1, TestSortEqual(Some s1, s2) ->
							let err () =
								test_error i
									(fun () ->
												msg "@\nExpected@ a@ value@ with@ sort@ ";
												format_sort s1;
												msg "@ but found@ "; V.format v1;
												msg "@ : "; format_sort s2;
												msg "@\n%!") in
							if not (Bcheck.compatible s1 s2) then err ()
							else
								begin
									try
										ignore
											((interp_cast wq cev i s1 s2)
													(interp_exp wq cev e))
									with Error.Harmony_error(e) -> err ()
								end
					| Error err, TestEqual e2 ->
							let v2 = interp_exp wq cev e2 in
							test_error i
								(fun () ->
											msg "@\nExpected@ "; V.format v2;
											msg "@ but found an error:@ ";
											err ();
											msg "@\n%!")
					| Error err, TestSortEqual(_, s2) ->
							test_error i
								(fun () ->
											msg "@\nExpected@ "; format_sort s2;
											msg "@ but found an error:@ ";
											err ();
											msg "@\n%!")
					| OK v, TestError ->
							let msgFun =
								(fun () ->
											msg "@\nExpected an error@ ";
											msg "@ but found:@ ";
											V.format v;
											msg "@\n%!") in
							if Prefs.read Prefs.unsafePref
							then (msgFun (); msg "@\nMISSING ERROR IGNORED, RUNNING UNSAFELY@\n%!")
							else test_error i msgFun
			end;
			(cev, [])

and interp_mod_aux wq cev ms ds =
	Safelist.fold_left
		(fun (cev, names) di ->
					let m_cev, new_names = interp_decl wq cev ms di in
					(m_cev, names@new_names))
		(cev,[])
		ds

let interp_module m0 = match m0 with
	| Mod(i, m, nctx, ds) ->
			pc := 0;
			ic := 0;
			mc := 0;
			let qm = Qid.t_of_id m in
			let nctx' = nctx in
			let cev = CEnv.set_ctx (CEnv.empty qm) (qm:: nctx') in
			let wqo : ((unit -> V.t) -> unit) option =
				if Prefs.read Prefs.parallelPref
				then
					let wq = Workqueue.create () in
					Some (fun (f: unit -> V.t) -> Workqueue.enq f wq)
				else None in
			let new_cev, _ = interp_mod_aux wqo cev [m] ds in
			(** let trying id (_, v) _ : unit = print_string (Bsynth.vtoString id v) in
			let _ = CEnv.fold trying new_cev () in **)
			G.register_env (CEnv.get_ev new_cev) nctx' m;
			Trace.debug "parallel"
				(fun () ->
							msg "@[Checks:@ %d parallel, %d inline, %d mandatory@]@\n"
								!pc !ic !mc)
