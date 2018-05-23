module Env

include EnvFun
open Label

val make_env : 'a -> list (var * 'a) -> env 'a
let rec make_env def vals = match vals with
 | [] -> empty_env def
 | (var, v)::tl -> update_env (make_env def tl) var v

type value_env = env int
type label_env = env label

let empty_value_env = empty_env 0
let empty_label_env = empty_env Low
