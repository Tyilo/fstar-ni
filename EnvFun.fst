module EnvFun

include Var

type env 'a = var -> 'a

val empty_env : 'a -> env 'a
let empty_env def = (fun _ -> def)

val lookup_env : env 'a -> var -> 'a
let lookup_env env var = (env var)

val update_env : env 'a -> var -> 'a -> env 'a
let update_env env var v = (fun var' ->
      if var = var' then
        v
      else
        lookup_env env var')

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
      assert (lookup_env e''' "bar" = 10)
