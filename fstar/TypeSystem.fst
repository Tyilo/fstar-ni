module TypeSystem

open Label
open Syntax
open Env

val label_of_exp : label_env -> exp -> label
let rec label_of_exp lenv e = match e with
 | Int _ -> Low
 | Var v -> lookup_env lenv v
 | BinOp left _ right -> lub (label_of_exp lenv left) (label_of_exp lenv right)


val typed_com : label_env -> com -> label -> bool
let rec typed_com lenv com pc_label = match com with
 | Skip -> true
 | Assign v e -> (lub pc_label (label_of_exp lenv e)) `leq` lookup_env lenv v
 | Sequence s1 s2 -> typed_com lenv s1 pc_label && typed_com lenv s2 pc_label
 | If cond thn els -> let l = lub pc_label (label_of_exp lenv cond) in
                                  typed_com lenv thn l && typed_com lenv els l
 | While cond body -> typed_com lenv body (lub pc_label (label_of_exp lenv cond))


val seq : list com -> com
let rec seq ss = match ss with
 | [] -> Skip
 | hd :: tl -> Sequence hd (seq tl)


let _ =
	let lenv = make_env Low [("lo", Low); ("hi", High)] in
	let prog_test = seq [
		Assign "hi" (Int 2);
		Assign "lo" (Var "hi")
	] in
	let prog_slides = seq [
		Assign "lo" (Int 0);
		While (Var "hi")
			(Assign "hi" (BinOp (Var "hi") Minus (Int 1)));
		Assign "lo" (Int 1)
	] in
	let prog_ni_fail = seq [
		If (Var "hi")
		  (Assign "lo" (Int 7))
		  (Assign "lo" (Int 7))
	] in

	assert (not (typed_com lenv prog_test Low));
	assert (typed_com lenv prog_slides Low);
	assert (not (typed_com lenv prog_ni_fail Low))
