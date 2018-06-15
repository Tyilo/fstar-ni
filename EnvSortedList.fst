module EnvSortedList

include Var

open FStar.String

type env 'a = 'a * list (var * 'a)

val empty_env : 'a -> env 'a
let empty_env def = (def, [])

val lookup_env : env:env 'a -> var -> Tot 'a (decreases (snd env))
let rec lookup_env env var = let def, l = env in
  match l with
   | [] -> def
   | (var', v) :: tl -> if var' = var then
                    v
                  else
                    lookup_env (def, tl) var

val update_env : e:env 'a -> var -> 'a -> Tot (env 'a) (decreases (snd e))
let rec update_env env var v = let def, l = env in
  (def, (match l with
          | [] -> [(var, v)]
          | (var', v') :: tl -> if var' = var then
                                  (var, v) :: tl
                                else if compare var var' = -1 then
                                  (var, v) :: (var', v') :: tl
                                else
                                  (var', v') :: snd (update_env (def, tl) var v)))

let _ =
      let e = empty_env 0 in
      let e' = (update_env e "foo" (- 12)) in
      let e'' = (update_env e' "bar" 10) in
      let e''' = (update_env e'' "foo" 2) in


      assert (lookup_env e "foo" = 0);
      assert (lookup_env e "bar" = 0);
      assert (lookup_env e' "foo" = -12);
      assert (lookup_env e' "bar" = 0);

      assert (lookup_env e'' "foo" = -12);
      assert (lookup_env e'' "bar" = 10);
      assert (lookup_env e''' "foo" = 2);
      assert (lookup_env e''' "bar" = 10);

      ()
