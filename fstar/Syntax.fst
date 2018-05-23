module Syntax

include Var

type binop =
 | Plus : binop
 | Minus : binop
 | Times : binop

type exp =
 | Int : int -> exp
 | Var : var -> exp
 | BinOp : left:exp -> op:binop -> right:exp -> exp

type com =
 | Skip : com
 | Assign : var:var -> exp:exp -> com
 | Sequence : s1:com -> s2:com -> com
 | If : cond:exp -> thn:com -> els:com -> com
 | While : cond:exp -> body:com -> com
