open Term
open Formula
open Modul


(***normal to binary***)
let ia_bin_size = ref 0
let var_bin_size_ary = ref (Array.make 0 0)
let var_base_val_ary = ref (Array.make 0 0)
let flag = ref false
(*module BDD = Bdd.BDD (struct let nv = 24 end)*)

let rec get_bin_attr modl = 
	let var_list_size = (List.length modl.var_list) in
	let bin_size = ref 0 
	and bin_size_ary =  (Array.make var_list_size 0)
	and var_base_ary =  (Array.make var_list_size 0) 
	and index = ref 0 in
	List.iter (fun a -> 
		(match a with
		| (s, Int_type (i1, i2)) -> let bs = (int_size (i2-i1+1)) in bin_size := !bin_size + bs; bin_size_ary.(!index) <- bs; var_base_ary.(!index) <- i1
		| (s, Scalar_type ss) -> let bs = int_size (List.length ss) in bin_size := !bin_size + bs; bin_size_ary.(!index) <- bs
		| (s, _) -> bin_size := !bin_size + 1; bin_size_ary.(!index) <- 1
		); incr index
		) modl.var_list; (ia_bin_size := !bin_size; var_bin_size_ary := bin_size_ary; var_base_val_ary := var_base_ary; flag := true)
	
and int_size i = 
	let tmp = ref 2
	and index = ref 1 in
	while (i) >= !tmp do
		incr index;
		tmp := 2 * !tmp
	done; !index
	
and int_to_binary i =
	let tmp_list = ref [] 
	and tmp_i = ref i in
	if i = 0 then [0] else
	begin
		while !tmp_i > 0 do
			tmp_list := (!tmp_i mod 2) :: !tmp_list;
			tmp_i := !tmp_i / 2
		done; !tmp_list
	end



let rec ia_to_bin ia modl = 
try
	if !flag = true then
		begin
			let tmp_ary = Array.make !ia_bin_size 0 
			and index = ref 0 in
			for i=0 to (Array.length ia) - 1 do
				if (!var_bin_size_ary.(i) < 2) then (tmp_ary.(!index) <- ia.(i); incr index) else 
				begin
					let bin_lst = int_to_binary (ia.(i) - !var_base_val_ary.(i)) in
					let tmp_index = ref (!index + !var_bin_size_ary.(i) - 1) in
					List.iter (fun a -> tmp_ary.(!tmp_index) <- a; decr tmp_index) (List.rev bin_lst);
					index := !index + !var_bin_size_ary.(i)
				end
			done; tmp_ary
		end
	else
		begin
			ia_to_bin ia modl
		end
with _ -> print_endline "exception encountered in ia_to_bin."; exit (-1)


type continuation = 
	| Basic of bool
	| Cont of State_set.t * formula * string * continuation * continuation

type fml_state_tbl = (string, State_set.t) Hashtbl.t

exception Error_proving_atomic
exception Unable_to_prove

(*whether state s is already in an existing merge*)
let merges = Hashtbl.create 10
let pre_process_merges sub_fml_tbl = 
	Hashtbl.iter (fun a b -> Hashtbl.add merges a (!(Bdd.leaf_false))) sub_fml_tbl;
	Hashtbl.iter (fun a b -> Hashtbl.add true_merge a (!(Bdd.leaf_false))) sub_fml_tbl;
	Hashtbl.iter (fun a b -> Hashtbl.add false_merge a (!(Bdd.leaf_false))) sub_fml_tbl
let post_process_merges () = 
	Hashtbl.iter (fun a b -> print_endline (a ^ ": " ^ (string_of_int (State_set.cardinal b)))) merges

let state_in_merge merg fml st modl = 
	let bs = ia_to_bin st modl in
	let sts = Hashtbl.find merg fml in Bdd.int_array_satisfy bs sts
let add_merge merg fml ss = 
	let sts = Hashtbl.find merg fml in
	Hashtbl.replace merg fml (State_set.fold (fun elem b -> let bs = ia_to_bin elem modl in Bdd.add_int_array bs b) ss sts)

let clear_global_merge level = 
	Hashtbl.replace merges level (!(Bdd.leaf_false))


(* produce new continuations *)
let rec make_ax_cont gamma s fml levl sl contl contr = 
	State_set.fold (fun a c -> Cont (gamma, Formula.subst_s fml s (State a), levl, c, contr)) sl contl
let rec make_ex_cont gamma s fml levl sl contl contr =
	State_set.fold (fun a c -> Cont (gamma, Formula.subst_s fml s (State a), levl, contl, c)) sl contr
let rec make_af_cont gamma s fml levl sl contl contr =
	State_set.fold (fun a c -> Cont (gamma, AF (s, fml, (State a)), levl, c, contr)) sl contl
let rec make_eg_cont gamma s fml levl sl contl contr =
	State_set.fold (fun a c -> Cont (gamma, EG (s, fml, (State a)), levl, contl, c)) sl contr
let rec make_ar_cont gamma s s' fml1 fml2 levl sl contl contr =
	State_set.fold (fun a c -> Cont (gamma, AR (s, s', fml1, fml2, (State a)), levl, c, contr)) sl contl
let rec make_eu_cont gamma s s' fml1 fml2 levl sl contl contr =
	State_set.fold (fun a c -> Cont (gamma, EU (s, s', fml1, fml2, (State a)), levl, contl, c)) sl contr
	
	

let rec prove_resursive gamma fml levl modl = 
	match fml with
	| Top -> true
	| Bottom -> false
	| Atomic (s, sl) -> if prove_atomic s sl modl then true else false
	| Neg Atomic (s, sl) -> if prove_atomic s sl modl then false else true
	| And (fml1, fml2) -> 
		let b1 = prove_resursive State_set.empty fml1 (levl^"1") modl in
		if not b1 then 
			false 
		else 
			let b2 = prove_resursive State_set.empty fml2 (levl^"2") modl in
			if b2 then 
				true 
			else 
				false
	| Or (fml1, fml2) -> 
		let b1 = prove_resursive State_set.empty fml1 (levl^"1") modl in
		if b1 then 
			true 
		else 
			let b2 = prove_resursive State_set.empty fml2 (levl^"2") modl in
			if b2 then 
				true 
			else 
				false
	| AX (s, fml1, State sa) -> 
		let nexts = next sa modl.transitions modl.var_index_tbl in
		let flag = ref true in
		(State_set.iter (fun a -> if not !flag then () else (if prove_resursive State_set.empty (Formula.subst_s fml1 s (State a)) (levl^"1") modl then () else flag := false)) nexts; !flag)
	| EX (s, fml1, State sa) -> 
		let nexts = next sa modl.transitions modl.var_index_tbl in
		let flag = ref false in
		(State_set.iter (fun a -> if !flag then () else (if prove_resursive State_set.empty (Formula.subst_s fml1 s (State a)) (levl^"1") modl then (flag := true) else ())) nexts; !flag)
	| AF (s, fml1, State sa) -> 
		if State_set.mem sa gamma then 
			false 
		else
			let nexts = next sa modl.transitions modl.var_index_tbl in
			let flag = ref true in
			if prove_resursive State_set.empty (Formula.subst_s fml1 s (State sa)) (levl^"1") modl then 
				true 
			else
				(State_set.iter (fun a -> if not !flag then () else (if prove_resursive (State_set.add sa gamma) (AF(s, fml1, State a)) levl modl then () else flag := false)) nexts; !flag)
		| EG (s, fml1, State sa) -> 
			if State_set.mem sa gamma then 
				true 
			else
			let nexts = next sa modl.transitions modl.var_index_tbl in
			let flag = ref false in
			if not (prove_resursive State_set.empty (Formula.subst_s fml1 s (State sa)) (levl^"1") modl) then 
				false 
			else
				(State_set.iter (fun a -> if !flag then () else (if prove_resursive (State_set.add sa gamma) (EG (s, fml1, State a)) levl modl then (flag := true) else ())) nexts; !flag)
	| AR (x, y, fml1, fml2, State sa) -> 
		if (State_set.is_empty gamma) then 
			clear_global_merge levl
		else 
			add_merge merges levl gamma modl; 
		(if state_in_merge merges levl sa modl then 
			true 
		else
			if prove_resursive State_set.empty (Formula.subst_s fml2 y (State sa)) (levl^"2") modl then 
				(
					if prove_resursive State_set.empty (Formula.subst_s fml1 x (State sa)) (levl^"1") modl then 
						true
					else 
						let nexts = next sa modl.transitions modl.var_index_tbl in
						let flag = ref true in
						(State_set.iter (fun a -> if not !flag then () else (if prove_resursive (State_set.add sa gamma) (AR (x, y, fml1, fml2, State a)) levl modl then () else flag := false)) nexts; !flag)								
				) 
			else 
				false
		)
	| EU (s, s', fml1, fml2, State sa) -> 
		if (State_set.is_empty gamma) then 
			clear_global_merge levl
		else 
			add_merge merges levl gamma modl; 
		(if state_in_merge merges levl sa modl then 
			false 
		else
			if not (prove_resursive State_set.empty (Formula.subst_s fml2 s' (State sa)) (levl^"2") modl) then 
				(
					if not (prove_resursive State_set.empty (Formula.subst_s fml1 s (State sa)) (levl^"1") modl) then 
						false
					else 
						let nexts = next sa modl.transitions modl.var_index_tbl in
						let flag = ref false in
						(State_set.iter (fun a -> if !flag then () else (if prove_resursive (State_set.add sa gamma) (EU (s, s', fml1, fml2, State a)) levl modl then (flag := true) else ())) nexts; !flag)
				) 
			else 
				true
		)
	| _ -> raise Unable_to_prove



let rec prove_model modl = 
	let spec_lst = modl.model_spec_list in 
	let rec prove_lst lst = 
	match lst with
	| [] -> ()
	| (s, fml) :: lst' -> ((let nnf_fml = nnf fml in 
							print_endline (fml_to_string (nnf_fml));
							pre_process_merges (select_sub_fmls (sub_fmls nnf_fml "1"));
							(* let b = (prove (Cont (State_set.empty, Formula.subst_s (nnf_fml) (SVar "ini") modl.model_init_state, "1", Basic true, Basic false)) modl) in *)
							let b = (prove_resursive State_set.empty (Formula.subst_s (nnf_fml) (SVar "ini") modl.init_assign) "1" modl) in
							 print_endline (s ^ ": " ^ (string_of_bool b)));
							 prove_lst lst') in prove_lst spec_lst







