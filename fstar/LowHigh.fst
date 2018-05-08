module LowHigh

type label =
 | Low : label
 | High : label

val op_Less : label -> label -> bool
let op_Less l1 l2 = match l1, l2 with
 | Low, High -> true
 | _, _ -> false

val op_Less_Equals : label -> label -> bool
let op_Less_Equals l1 l2 = l1 < l2 || l1 = l2

val lub : label -> label -> label
let lub l1 l2 = match l1, l2 with
 | Low, Low -> Low
 | _, _ -> High


type binop =
 | Plus : binop
 | Minus : binop
 | Times : binop
 | Divide : binop

type exp =
 | Int : int -> exp
 | Var : string -> exp
 | BinOp : left:exp -> op:binop -> right:exp -> exp

type stmt =
 | Skip : stmt
 | Assign : var:string -> exp:exp -> stmt
 | Sequence : s1:stmt -> s2:stmt -> stmt
 | If : cond:exp -> thn:stmt -> els:stmt -> stmt
 | While : cond:exp -> body:stmt -> stmt

val label_of_var : string -> label
let label_of_var v = match v with
 | "lo" -> Low
 | "hi" -> High
 | _ -> Low

val label_of_exp : exp -> label
let rec label_of_exp e = match e with
 | Int _ -> Low
 | Var v -> label_of_var v
 | BinOp left _ right -> lub (label_of_exp left) (label_of_exp right)


val ni_stmt : stmt -> label -> bool
let rec ni_stmt stmt pc_label = match stmt with
 | Skip -> true
 | Assign v e -> lub pc_label (label_of_exp e) <= label_of_var v
 | Sequence s1 s2 -> ni_stmt s1 pc_label && ni_stmt s2 pc_label
 | If cond thn els -> let l = lub pc_label (label_of_exp cond) in
                                  ni_stmt thn l && ni_stmt els l
 | While cond body -> ni_stmt body (lub pc_label (label_of_exp cond))


val seq : list stmt -> stmt
let rec seq ss = match ss with
 | [] -> Skip
 | hd :: tl -> Sequence hd (seq tl)


let prog_test = seq [
    Assign "hi" (Int 2);
	Assign "lo" (Var "hi")
]

let prog_slides = seq [
	Assign "lo" (Int 0);
	While (Var "hi")
	    (Assign "hi" (BinOp (Var "hi") Minus (Int 1)));
	Assign "lo" (Int 1)
]

let prog_ni_fail = seq [
	If (Var "hi")
	  (Assign "lo" (Int 7))
	  (Assign "lo" (Int 7))
]

let _ = assert (not (ni_stmt prog_test Low))
let _ = assert (ni_stmt prog_slides Low)
let _ = assert (not (ni_stmt prog_ni_fail Low))
