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


type result =
 | Finished : result
 | OutOfFuel : result
 | Error : result


noeq type interpret_result =
 | Result : result:result -> env:value_env -> fuel:nat -> interpret_result


val interpret_com : value_env -> com -> nat -> interpret_result
let rec interpret_com env com fuel = match com with
 | Skip -> Result Finished env fuel
 | Assign var exp -> Result Finished (update_env env var (interpret_exp env exp)) fuel
 | Sequence c1 c2 -> let Result res env' fuel' = interpret_com env c1 fuel in
                                              if res = OutOfFuel then
											    Result res env' fuel'
											  else
												interpret_com env' c2 fuel'
 | If cond thn els -> if (not (interpret_exp env cond = 0)) then
                        interpret_com env thn fuel
					  else
                        interpret_com env els fuel
 | While cond body -> if (not (interpret_exp env cond = 0)) then
                        if fuel = 0 then
						  Result OutOfFuel env fuel
						else
							let Result res env' fuel' = interpret_com env body fuel in
												 if res = OutOfFuel then
												   Result res env' fuel'
												 else if fuel' = 0 then
												   Result Error env' fuel'
												 else if fuel' < fuel then
												   interpret_com env' com (fuel' - 1)
												 else
												   Result Error env' fuel'
                      else
					    Result Finished env fuel


type low_equiv (lenv:label_env) (e1:value_env) (e2:value_env) =
  forall (x:var). is_low lenv x ==> lookup_env e1 x == lookup_env e2 x

type ni_exp (lenv:label_env) (exp:exp) =
  forall (e1:value_env) (e2:value_env). low_equiv lenv e1 e2 ==> interpret_exp e1 exp == interpret_exp e2 exp

type res_equal (lenv:label_env) (r1:interpret_result) (r2:interpret_result) =
  Result?.result r1 == Finished /\ Result?.result r2 == Finished ==> low_equiv lenv (Result?.env r1) (Result?.env r2)

type ni_com (lenv:label_env) (com:com) =
  forall (e1:value_env) (e2:value_env) (fuel1:nat) (fuel2:nat). low_equiv lenv e1 e2 ==> res_equal lenv (interpret_com e1 com fuel1) (interpret_com e2 com fuel2)

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


(*
val ni_seq : lenv:label_env -> c1:com -> c2:com ->
  lemma (requires (ni_com lenv c1 /\ ni_com lenv c2))
        (ensures (ni_com lenv (sequence c1 c2)))
let ni_seq lenv c1 c2 = ()
*)

val fuel_decr : env:value_env -> com:com -> fuel:nat ->
  Lemma (requires (Result?.result (interpret_com env com fuel) = OutOfFuel))
        (ensures (Result?.fuel (interpret_com env com fuel) = 0))
let rec fuel_decr env com fuel = match com with
 | Skip -> ()
 | Assign _ _ -> ()
 | If cond thn els ->
					  if (not (interpret_exp env cond = 0)) then
                        fuel_decr env thn fuel
					  else
                        fuel_decr env els fuel
 | Sequence c1 c2 -> admit()
 | _ -> admit()


(*
val ni_seq : lenv:label_env -> env:value_env -> fuel:nat -> c:com{Sequence? c} ->
  Lemma (requires (ni_com lenv (Sequence?.s1 c) /\ ni_com lenv (Sequence?.s2 c)))
        (ensures (ni_com lenv c))
let ni_seq lenv env fuel c = match c with
  | Sequence c1 c2 -> let r1 = interpret_com env fuel in
                      let r2 = interpret_com env
  assert (ni_com lenv c1);
      assert (forall e1:value_env e2:value_env. interpret_exp lenv
    assert (ni_com lenv c2);
*)


val typed_implies_ni : lenv:label_env -> com:com ->
  Lemma (requires (typed_com lenv com Low))
        (ensures (ni_com lenv com))
let typed_implies_ni _ _ = admit()


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
	assert (ni_exp lenv exp'');

	assert (ni_com lenv Skip);
	assert (ni_com lenv (Assign "lo" exp));

	let not_ni_com = Assign "lo" (Var "hi") in
	let env0 = make_env 0 [("lo", 0); ("hi", 0)] in
	let env1 = make_env 0 [("lo", 0); ("hi", 1)] in

	assert (low_equiv lenv env0 env1);

	let r0 = interpret_com env0 not_ni_com 1 in
	let r1 = interpret_com env1 not_ni_com 1 in

	assert (Result?.result r0 = Finished);
	assert (Result?.result r1 = Finished);

	assert (lookup_env (Result?.env r0) "lo" = 0);
	assert (lookup_env (Result?.env r1) "lo" = 1);

	assert (~ (low_equiv lenv (Result?.env r0) (Result?.env r1)));
	assert (~ (res_equal lenv r0 r1));

	assert (~ (ni_com lenv not_ni_com));

	let seq_com = (Sequence (Assign "hi" (Var "lo")) (Assign "lo" (Var "hi"))) in

	assert (ni_com lenv seq_com);

	()
