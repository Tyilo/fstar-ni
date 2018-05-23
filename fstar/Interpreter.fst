module Interpreter

open Label
open Syntax
open TypeSystem
open Env

val interpret_exp : value_env -> exp -> int
let rec interpret_exp env exp = match exp with
 | Int n -> n
 | Var v -> lookup_env env v
 | BinOp left op right ->
   let vleft =  interpret_exp env left in
   let vright = interpret_exp env right in
     match op with
      | Plus -> vleft + vright
	  | Minus -> vleft - vright
	  | Times -> op_Multiply vleft vright


type low_equiv (lenv:label_env) (e1:value_env) (e2:value_env) =
  forall (x:var). is_low lenv x ==> lookup_env e1 x == lookup_env e2 x

type ni_exp (lenv:label_env) (exp:exp) =
  forall (e1:value_env) (e2:value_env). low_equiv lenv e1 e2 ==> interpret_exp e1 exp == interpret_exp e2 exp


val low_equiv_symmetric : lenv:label_env -> e1:value_env -> e2:value_env ->
  Lemma (requires (low_equiv lenv e1 e2))
        (ensures  (low_equiv lenv e2 e1))
let low_equiv_symmetric _ _ _ = ()


val ni_int : lenv:label_env -> n:int ->
  Lemma (requires True)
        (ensures (ni_exp lenv (Int n)))
let ni_int _ _ = ()


val ni_low_var : lenv:label_env -> var:var ->
  Lemma (requires (is_low lenv var))
        (ensures (ni_exp lenv (Var var)))
let ni_low_var _ _ = ()


val var_lemma : var:var -> n:int ->
  Lemma (requires True)
        (ensures (interpret_exp (make_env 0 [(var, n)]) (Var var) = n))
let var_lemma _ _ = ()


val low_equiv_hi : lenv:label_env -> e1:value_env -> e2:value_env -> var:var ->
  Lemma (requires ((low_equiv lenv e1 e2) /\ (lookup_env e1 var) =!= (lookup_env e2 var)))
        (ensures (is_high lenv var))
let low_equiv_hi _ _ _ _ = ()


val ni_high_var : lenv:label_env -> var:var ->
  Lemma (requires (is_high lenv var))
        (ensures (~ (ni_exp lenv (Var var))))
let ni_high_var lenv var =
  let exp = Var var in
  let e1 = make_env 0 [(var, 0)] in
  let e2 = make_env 0 [(var, 1)] in
	low_equiv_hi lenv e1 e2 var


val ni_binop : lenv:label_env -> op:binop -> exp1:exp -> exp2:exp ->
  Lemma (requires (ni_exp lenv exp1 /\ ni_exp lenv exp2))
        (ensures (ni_exp lenv (BinOp exp1 op exp2)))
let ni_binop _ _ _ _ = ()


let _ =
	let lenv = make_env Low [("lo", Low); ("lo2", Low); ("hi", High)] in

	let lo_env = (update_env empty_value_env "lo" 10) in
	let hi_env = (update_env empty_value_env "hi" 7) in
	let lo2_env = (update_env lo_env "lo" 0) in

	let empty_equiv = low_equiv lenv empty_value_env in

	assert (empty_equiv empty_value_env);
	assert (~ (empty_equiv lo_env));
	assert (empty_equiv hi_env);
	assert (empty_equiv lo2_env);

	let exp_int = Int 10 in

	assert (ni_exp lenv exp_int);

	let exp  = (BinOp (Var "lo") Plus (BinOp (Var "lo2") Times (Int 7))) in
	let exp' = (BinOp (Var "hi") Minus (Var "hi")) in
	let exp'' = (BinOp (Var "hi") Times (Int 0)) in

	assert (ni_exp lenv exp);
	assert (ni_exp lenv exp');
	assert (ni_exp lenv exp'')
