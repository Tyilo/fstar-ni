module Label

type label =
 | Low : label
 | High : label


val lub : label -> label -> label
let lub l1 l2 = match l1, l2 with
 | Low, Low -> Low
 | _, _ -> High

val leq : label -> label -> bool
let leq l1 l2 = lub l1 l2 = l2
