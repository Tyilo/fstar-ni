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


noeq type interpret_result =
 | Result : env:value_env -> fuel:nat -> interpret_result


val out_of_fuel : interpret_result -> bool
let out_of_fuel res = let Result _ fuel = res in fuel = 0

val finished : interpret_result -> bool
let finished res = not (out_of_fuel res)


val interpret_com : value_env -> com -> fuel:nat -> res:interpret_result{Result?.fuel res <= fuel}
let rec interpret_com env com fuel = if fuel = 0 then
    Result env fuel
  else match com with
 | Skip -> Result env fuel
 | Assign var exp -> Result (update_env env var (interpret_exp env exp)) fuel
 | If cond thn els -> if (not (interpret_exp env cond = 0)) then
                        interpret_com env thn fuel
					  else
                        interpret_com env els fuel
 | Sequence c1 c2 -> let res = interpret_com env c1 fuel in
                     let Result env' fuel' = res in
					   if out_of_fuel res then
					     res
					   else
						 interpret_com env' c2 fuel'
 | While cond body -> if (interpret_exp env cond = 0) then
                        Result env fuel
					  else
					    let res = interpret_com env body fuel in
						let Result env' fuel' = res in
							if out_of_fuel res then
							  res
							else
							  interpret_com env' com (fuel' - 1)


type equiv (e1:value_env) (e2:value_env) =
  forall (x:var). lookup_env e1 x == lookup_env e2 x

(*
This lemma ensures that iff two value environments agree on the values of all variables,
then F* should think of them as being equal.

We need this for proving predicates that rely on (equiv e1 e2) ==> (P(e1, ...) <==> P(e2, ...)).

We can't (?) prove equiv ==> (==), so we use assume.
The other direction is trivial.
*)
val equiv_iff_equal : (e1:value_env) -> (e2:value_env) ->
  Lemma (equiv e1 e2 <==> e1 == e2)
        [SMTPat (equiv e1 e2)]
let equiv_iff_equal e1 e2 = assume (equiv e1 e2 ==> e1 == e2)

type low_equiv (lenv:label_env) (e1:value_env) (e2:value_env) =
  forall (x:var). is_low lenv x ==> lookup_env e1 x == lookup_env e2 x

type ni_exp (lenv:label_env) (exp:exp) =
  forall (e1:value_env) (e2:value_env). low_equiv lenv e1 e2 ==> interpret_exp e1 exp == interpret_exp e2 exp

type res_equal (lenv:label_env) (r1:interpret_result) (r2:interpret_result) =
  finished r1 /\ finished r2 ==> low_equiv lenv (Result?.env r1) (Result?.env r2)

type ni_com' (lenv:label_env) (com:com) (e1:value_env) (e2:value_env) (fuel1:nat) (fuel2:nat) =
  low_equiv lenv e1 e2 ==> res_equal lenv (interpret_com e1 com fuel1) (interpret_com e2 com fuel2)

type ni_com (lenv:label_env) (com:com) =
  forall (e1:value_env) (e2:value_env) (f1:nat) (f2:nat). ni_com' lenv com e1 e2 f1 f2


// Properties of types

val low_equiv_symmetric : lenv:label_env -> e1:value_env -> e2:value_env ->
  Lemma (requires (low_equiv lenv e1 e2))
        (ensures  (low_equiv lenv e2 e1))
let low_equiv_symmetric _ _ _ = ()

val equiv_implies_low_equiv : lenv:label_env -> e1:value_env -> e2:value_env ->
  Lemma (requires (equiv e1 e2))
        (ensures  (low_equiv lenv e1 e2))
let equiv_implies_low_equiv _ _ _ = ()


// Expression lemmas

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


// Command lemmas

val equiv_if_finished : env:value_env -> com:com -> f1:nat -> f2:nat ->
  Lemma (requires (finished (interpret_com env com f1) /\ finished (interpret_com env com f2)))
        (ensures (equiv
		           (Result?.env (interpret_com env com f1))
				   (Result?.env (interpret_com env com f2))))
let rec equiv_if_finished env com f1 f2 = match com with
 | Skip -> ()
 | Assign var exp -> ()
 | If cond thn els -> if (not (interpret_exp env cond = 0)) then
                        equiv_if_finished env thn f1 f2
					  else
                        equiv_if_finished env els f1 f2
 | Sequence c1 c2 -> let r1 = interpret_com env c1 f1 in
                     let r2 = interpret_com env c1 f2 in
					 let Result e1 f1' = r1 in
					 let Result e2 f2' = r2 in
					   if out_of_fuel r1 || out_of_fuel r2 then
					     ()
					   else
					   (
					     equiv_if_finished env c1 f1 f2;
					     // assert (equiv e1 e2);
						 // assert (finished r1);
						 // assert (finished r2);
					     equiv_if_finished e1 c2 f1' f2'
					   )
 | While cond body -> if (interpret_exp env cond = 0) then
                        ()
					  else
                        let r1 = interpret_com env body f1 in
                        let r2 = interpret_com env body f2 in
					    let Result e1 f1' = r1 in
					    let Result e2 f2' = r2 in
							if out_of_fuel r1 || out_of_fuel r2 then
							  ()
							else
							(
							  equiv_if_finished env body f1 f2;
							  equiv_if_finished e1 com (f1' - 1) (f2' - 1)
							)


val ni_different_fuel : lenv:label_env -> env:value_env -> com:com -> f1:nat -> f2:nat ->
  Lemma (requires True)
        (ensures (res_equal lenv (interpret_com env com f1) (interpret_com env com f2)))
let ni_different_fuel _ env com f1 f2 =
  let r1 = interpret_com env com f1 in
  let r2 = interpret_com env com f2 in
  match (finished r1), (finished r2) with
  | true, true -> equiv_if_finished env com f1 f2
  | _, _ -> ()


val ni_seq' : lenv:label_env -> com:com{Sequence? com} -> e1:value_env -> e2:value_env -> f1:nat -> f2:nat ->
  Lemma (requires (ni_com lenv (Sequence?.s1 com) /\ ni_com lenv (Sequence?.s2 com) /\ low_equiv lenv e1 e2))
        (ensures (ni_com' lenv com e1 e2 f1 f2))
        [SMTPat (ni_com' lenv com e1 e2 f1 f2)]
let ni_seq' lenv com e1 e2 f1 f2 = match com with
 | Sequence c1 c2 -> let Result e1' f1' = interpret_com e1 c1 f1 in
                     let Result e2' f2' = interpret_com e2 c1 f2 in
                     assert (ni_com' lenv c1 e1 e2 f1 f2);
                     assert (ni_com' lenv c2 e1' e2' f1' f2')


val ni_seq : lenv:label_env -> com:com{Sequence? com} ->
  Lemma (requires (ni_com lenv (Sequence?.s1 com) /\ ni_com lenv (Sequence?.s2 com)))
        (ensures (ni_com lenv com))
let ni_seq lenv com = assert (forall e1 e2 f1 f2. ni_com' lenv com e1 e2 f1 f2)

(*
val typed_implies_ni : lenv:label_env -> com:com ->
  Lemma (requires (typed_com lenv com Low))
        (ensures (ni_com lenv com))
let typed_implies_ni _ _ = admit()
*)


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

    (*
	let not_ni_com = Assign "lo" (Var "hi") in
	let env0 = make_env 0 [("lo", 0); ("hi", 0)] in
	let env1 = make_env 0 [("lo", 0); ("hi", 1)] in

	assert (low_equiv lenv env0 env1);

	let r0 = interpret_com env0 not_ni_com 1 in
	let r1 = interpret_com env1 not_ni_com 1 in

	assert (finished r0);
	assert (finished r1);

	assert (lookup_env (Result?.env r0) "lo" = 0);
	assert (lookup_env (Result?.env r1) "lo" = 1);

	assert (~ (low_equiv lenv (Result?.env r0) (Result?.env r1)));
	assert (~ (res_equal lenv r0 r1));

	assert (~ (ni_com lenv not_ni_com));
    *)

	let seq_com = (Sequence (Assign "hi" (Var "lo")) (Assign "lo" (Var "hi"))) in

	assert (ni_com lenv seq_com);

	let if_com = (If (Var "hi") (Assign "lo" (Var "lo2")) (Assign "lo" (Var "lo2"))) in

	assert (ni_com lenv if_com);

	()
