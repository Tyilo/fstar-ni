module Label

type label =
 | Low : label
 | High : label

(*
val op_Less : label -> label -> bool
let op_Less l1 l2 = match l1, l2 with
 | Low, High -> true
 | _, _ -> false

val op_Less_Equals : label -> label -> bool
let op_Less_Equals l1 l2 = l1 < l2 || l1 = l2
*)

val lub : label -> label -> label
let lub l1 l2 = match l1, l2 with
 | Low, Low -> Low
 | _, _ -> High
