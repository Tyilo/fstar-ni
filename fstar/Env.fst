module Env

// include EnvSortedList
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

val is_low : label_env -> var -> bool
let is_low lenv var = lookup_env lenv var = Low

val is_high : label_env -> var -> bool
let is_high lenv var = lookup_env lenv var = High
