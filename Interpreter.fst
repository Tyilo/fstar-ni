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
	  | Times -> vleft `op_Multiply` vright


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
 | If cond thn els -> if (interpret_exp env cond <> 0) then
                        interpret_com env thn fuel
					  else
                        interpret_com env els fuel
 | Sequence c1 c2 -> let res = interpret_com env c1 fuel in
                     let Result env' fuel' = res in
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

// Definitions

type low_equiv (lenv:label_env) (e1:value_env) (e2:value_env) =
  forall (x:var). is_low lenv x ==> lookup_env e1 x == lookup_env e2 x

type ni_exp (lenv:label_env) (exp:exp) =
  forall (e1:value_env) (e2:value_env). low_equiv lenv e1 e2 ==> interpret_exp e1 exp == interpret_exp e2 exp

type res_equal' (lenv:label_env) (e:value_env) (r:interpret_result) =
  finished r ==> low_equiv lenv e (Result?.env r)

type res_equal (lenv:label_env) (r1:interpret_result) (r2:interpret_result) =
  finished r1 /\ finished r2 ==> low_equiv lenv (Result?.env r1) (Result?.env r2)

type ni_com' (lenv:label_env) (com:com) (e1:value_env) (e2:value_env) (fuel1:nat) (fuel2:nat) =
  low_equiv lenv e1 e2 ==> res_equal lenv (interpret_com e1 com fuel1) (interpret_com e2 com fuel2)

type ni_com (lenv:label_env) (com:com) =
  forall (e1:value_env) (e2:value_env) (f1:nat) (f2:nat). ni_com' lenv com e1 e2 f1 f2

// Expression lemmas

val ni_typed_exp : lenv:label_env -> exp:exp ->
  Lemma (requires (label_of_exp lenv exp == Low))
        (ensures  (ni_exp lenv exp))
let rec ni_typed_exp lenv exp = match exp with
 | Int _ -> ()
 | Var _ -> ()
 | BinOp left _ right -> ni_typed_exp lenv left; ni_typed_exp lenv right

// Command lemmas

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


val ni_if' : lenv:label_env -> com:com{If? com} -> e1:value_env -> e2:value_env -> f1:nat -> f2:nat ->
  Lemma (requires (ni_exp lenv (If?.cond com) /\ ni_com lenv (If?.thn com) /\ ni_com lenv (If?.els com) /\ low_equiv lenv e1 e2))
        (ensures (ni_com' lenv com e1 e2 f1 f2))
        [SMTPat (ni_com' lenv com e1 e2 f1 f2)]
let ni_if' lenv com e1 e2 f1 f2 = match com with
 | If cond thn els -> let b1 = interpret_exp e1 cond in
                      let b2 = interpret_exp e2 cond in
                      assert (b1 == b2);
                      if b1 <> 0 then
                      (
                        assert (ni_com' lenv thn e1 e2 f1 f2)
                      )
                      else
                      (
                        assert (ni_com' lenv els e1 e2 f1 f2)
                      )


val ni_if : lenv:label_env -> com:com{If? com} ->
  Lemma (requires (ni_exp lenv (If?.cond com) /\ ni_com lenv (If?.thn com) /\ ni_com lenv (If?.els com)))
        (ensures (ni_com lenv com))
let ni_if lenv com = assert (forall e1 e2 f1 f2. ni_com' lenv com e1 e2 f1 f2)


val ni_while': lenv:label_env -> com:com{While? com} -> e1:value_env -> e2:value_env -> f1:nat -> f2:nat ->
  Lemma (requires (ni_exp lenv (While?.cond com)
                                          /\ ni_com lenv (While?.body com)
                                          /\ low_equiv lenv e1 e2))
        (ensures (ni_com' lenv com e1 e2 f1 f2))
        [SMTPat (ni_com' lenv com e1 e2 f1 f2)]
let rec ni_while' lenv com e1 e2 f1 f2 = match com with
 | While cond body -> let b1 = interpret_exp e1 cond in
                      let b2 = interpret_exp e2 cond in
                      assert (b1 == b2);
                      if b1 = 0 then
                        ()
					  else
                        let r1 = interpret_com e1 body f1 in
                        let r2 = interpret_com e2 body f2 in
					    let Result e1' f1' = r1 in
					    let Result e2' f2' = r2 in
							if out_of_fuel r1 || out_of_fuel r2 then
							  ()
							else
							(
                              assert (ni_com' lenv body e1 e2 f1 f2);
                              ni_while' lenv com e1' e2' (f1' - 1) (f2' - 1)
							)


val ni_while: lenv:label_env -> com:com{While? com} ->
  Lemma (requires (ni_exp lenv (While?.cond com) /\ ni_com lenv (While?.body com)))
        (ensures (ni_com lenv com))
let ni_while lenv com = assert (forall e1 e2 f1 f2. ni_com' lenv com e1 e2 f1 f2)


let rec has_low_assign lenv com = match com with
 | Skip -> false
 | Assign v e -> lookup_env lenv v = Low
 | Sequence c1 c2 -> has_low_assign lenv c1 || has_low_assign lenv c2
 | If cond thn els -> has_low_assign lenv thn || has_low_assign lenv els
 | While cond body -> has_low_assign lenv body


val typed_assign_high : lenv:label_env -> com:com ->
  Lemma (requires (typed_com lenv com High))
        (ensures (~ (has_low_assign lenv com)))
let rec typed_assign_high lenv com = match com with
 | Skip -> ()
 | Assign v e -> ()
 | Sequence c1 c2 -> typed_assign_high lenv c1;
                     typed_assign_high lenv c2
 | If cond thn els -> typed_assign_high lenv thn;
                      typed_assign_high lenv els
 | While cond body -> typed_assign_high lenv body


val no_low_assign_preserves_low_equiv : lenv:label_env -> com:com -> e:value_env -> f:nat ->
  Lemma (requires (~ (has_low_assign lenv com)))
        (ensures (res_equal' lenv e (interpret_com e com f)))
        [SMTPat (res_equal' lenv e (interpret_com e com f))]
let rec no_low_assign_preserves_low_equiv lenv com e f = match com with
 | Skip -> ()
 | Assign v e -> ()
 | Sequence c1 c2 -> no_low_assign_preserves_low_equiv lenv c1 e f;
                     let Result e' f' = interpret_com e c1 f in
                     no_low_assign_preserves_low_equiv lenv c2 e' f'

 | If cond thn els -> no_low_assign_preserves_low_equiv lenv thn e f;
                      no_low_assign_preserves_low_equiv lenv els e f

 | While cond body -> let b = (interpret_exp e cond = 0) in
                      if b then
                        ()
                      else
                        no_low_assign_preserves_low_equiv lenv body e f;
                        let Result e' f' = interpret_com e body f in
                        if f' = 0 then
                          ()
                        else
                          no_low_assign_preserves_low_equiv lenv com e' (f' - 1)


val ni_typed_assign : lenv:label_env -> com:com ->
  Lemma (requires (~ (has_low_assign lenv com)))
        (ensures (ni_com lenv com))
let ni_typed_assign lenv com = assert (forall e f. res_equal' lenv e (interpret_com e com f))


val ni_typed_com : lenv:label_env -> com:com ->
  Lemma (requires (typed_com lenv com Low))
        (ensures (ni_com lenv com))
let rec ni_typed_com lenv com = match com with
| Skip -> ()
| Assign v e -> if (lookup_env lenv v = Low) then
                (
                  assert (label_of_exp lenv e = Low);
                  ni_typed_exp lenv e
                )
                else ()
| Sequence c1 c2 -> ni_typed_com lenv c1;
                    ni_typed_com lenv c2;
                    ni_seq lenv com
| If cond thn els -> if (label_of_exp lenv cond = High) then
                     (
                       typed_assign_high lenv com;
                       ni_typed_assign lenv com
                     )
                     else
                     (
                       ni_typed_exp lenv cond;
                       ni_typed_com lenv thn;
                       ni_typed_com lenv els;
                       ni_if lenv com
                     )
| While cond body -> if (label_of_exp lenv cond = High) then
                     (
                       typed_assign_high lenv com;
                       ni_typed_assign lenv com
                     )
                     else
                     (
                       ni_typed_exp lenv cond;
                       ni_typed_com lenv body;
                       ni_while lenv com
                     )

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

	let seq_com = (Sequence (Assign "hi" (Var "lo")) (Assign "lo" (Var "hi"))) in

	assert (ni_com lenv seq_com);

	let if_com = (If (Var "hi") (Assign "lo" (Var "lo2")) (Assign "lo" (Var "lo2"))) in

	assert (ni_com lenv if_com);

	()
