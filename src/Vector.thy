
theory Vector 
imports Main
begin

types ('a)vector = "('a)list"
      bitv       = "(bool)list"

value "[False]"
value "[False] # [False] # []"

(* construct bitv of fixed size *)
fun bitv_new2 :: "nat \<Rightarrow> bitv \<Rightarrow> bitv" where
"bitv_new2 0 xs = xs" |
"bitv_new2 (Suc n) [] = bitv_new2 n [False]" |
"bitv_new2 (Suc n) xs = bitv_new2 n (False # xs)"

value "bitv_new2 0 []"
value "bitv_new2 1 []"
value "bitv_new2 2 []"

definition bitv_new :: "nat \<Rightarrow> bitv" where
"bitv_new n = bitv_new2 n []"

value "bitv_new 1"

fun xor

end
