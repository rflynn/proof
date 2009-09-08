(*
 * Author: Ryan Flynn
 * Description: Fixed-width vector and bitv types. 
 *)

theory Vector 
imports Main Boolean
begin

(* TODO: convert to/from integer value *)

types 'a vector = "'a list"
      bitv      = "bool list"

definition new :: "nat \<Rightarrow> bitv" where
"new n \<equiv> replicate n False"

(* * Ordinality * *)

datatype eq = Eq | Lt | Gt

(* generic comparison function; all equality functions reverse
   their params and call me, the difference is in the expected return
   NOTE: for mismatched sizes, we only account for the smallest size *)
fun cmp :: "bitv \<Rightarrow> bitv \<Rightarrow> eq" where
"cmp [] _ = Eq" |
"cmp _ [] = Eq" |
"cmp (False # xs) (True # ys) = Lt" |
"cmp (True # xs) (False # ys) = Gt" |
"cmp (x # xs) (y # ys) = cmp xs ys"

lemma cmp_empty: "cmp [] [] = Eq"
by auto

lemma cmp_empty1 [simp]: "cmp [] x = Eq"
by auto

lemma cmp_eq_x [simp]: "cmp (x#[]) (x#[]) = Eq"
by (induct_tac x) auto

lemma cmp_eq_xy [simp]: "cmp (x#y#[]) (x#y#[]) = Eq"
apply(induct_tac x, simp)
apply(induct_tac y, simp, simp)
done

(* two different bitv items cannot compare equally *)
lemma cmp_eq_xnotx [simp]: "cmp [x] [\<not>x] \<noteq> Eq"
by (induct_tac x) auto

(* a bitv always compares Eq to itself *)
theorem cmp_eq [simp]: "cmp x x = Eq"
apply(induct_tac x, auto)
apply(induct_tac a, simp, simp)
done

lemma cmp_eq_xx [simp]: "cmp (x#[]) (x#x#[]) = Eq"
apply(induct_tac x, simp)
apply(auto)
done

lemma cmp_eq_size0 [simp]: "cmp (replicate 0 b) (replicate n b) = Eq"
by (induct_tac b) auto

lemma cmp_neq [simp]: "cmp (replicate 1 b) (replicate 1 (\<not>b)) \<noteq> Eq"
by (induct_tac b) auto

(*
(* vectors of different amounts of the same thing are Eq *)
theorem cmp_eq_size: "cmp (replicate n True) (replicate m True) = Eq"
apply(induct_tac n)
apply(simp)
done
*)

(*
(* vectors of the same size containing different items are not equal *)
theorem cmp_neq [iff]: "(Eq \<noteq> (cmp (replicate n x) (replicate n (\<not>x)))) = (n \<noteq> 0)"
*)

definition lt :: "bitv \<Rightarrow> bitv \<Rightarrow> bool" (infixr "<" 50) where
"lt xs ys \<equiv> (Lt = cmp (rev xs) (rev ys))"

definition lteq :: "bitv \<Rightarrow> bitv \<Rightarrow> bool" (infixr "\<le>" 50) where
"lteq xs ys \<equiv> let e = cmp (rev xs) (rev ys) in (e = Lt \<or> e = Eq)"

definition gt :: "bitv \<Rightarrow> bitv \<Rightarrow> bool" (infixr ">" 50) where
"gt xs ys \<equiv> (Gt = cmp (rev xs) (rev ys))"

definition gteq :: "bitv \<Rightarrow> bitv \<Rightarrow> bool" (infixr "\<ge>" 50) where
"gteq xs ys \<equiv> let e = cmp (rev xs) (rev ys) in (e = Gt \<or> e = Eq)"

(* * Binary Operations * *)

fun zipWith :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list" where
"zipWith f [] _ = []" |
"zipWith f _ [] = []" |
"zipWith f (x#xs) (y#ys) = (f x y) # (zipWith f xs ys)"

definition and2 :: gate where "and2 x y \<equiv> x \<and> y"
definition band :: "bitv \<Rightarrow> bitv \<Rightarrow> bitv" (infixr "&" 50) where
"band xs ys \<equiv> zipWith and2 xs ys"

value "True & False"
value "[True] & [False]"

(*
theorem band_equiv [simp]: "\<lbrakk> x \<in> {True,False}; y \<in> {True,False} \<rbrakk> \<Longrightarrow> hd(x & y) = (hd(x)) & (hd(y))"
apply(simp only: band_def)
apply(auto)
*)

(* wrap or so it can be used as a parameter to zipWith *)
definition or :: gate where "or x y \<equiv> x \<or> y"

definition bor :: "bitv \<Rightarrow> bitv \<Rightarrow> bitv" (infixr "|" 50) where
"bor xs ys \<equiv> zipWith or xs ys"

value "True | False"
value "[True] | [False]"

fun shr :: "bitv \<Rightarrow> nat \<Rightarrow> bitv" (infixr "\<guillemotright>" 50) where
"shr [] _ = []" |
"shr xs n = (if n > size xs
             then (replicate (size xs) False)
             else (replicate n False) @ (take ((size xs)-n) xs))"

value "shr [True,True] 2"
value "shr [True,True] 3"

(* \<guillemotright>0 is identity *)
theorem shr_0 [simp]: "xs \<guillemotright> 0 = xs"
by (induct_tac xs) auto

(* shifting by more than length equivalent to shifting by length *)
theorem shr_toomany: "xs \<guillemotright> (length xs) = (xs \<guillemotright> ((length xs) + 1))"
by (induct_tac xs, simp) auto

(* shifting by the full length is equivalent to setting value to all False *)
theorem shr_max_val: "xs \<guillemotright> (length xs) = replicate (length xs) False"
by (induct_tac xs) auto

(* shifting preserves the size of a vector *)
theorem shr_preserve_size: "length xs = length (xs \<guillemotright> n)"
by (induct_tac xs) auto

fun shl :: "bitv \<Rightarrow> nat \<Rightarrow> bitv" (infixr "\<guillemotleft>" 50) where
"shl [] _ = []" |
"shl xs n = (if n > size xs
             then (replicate (size xs) False)
             else (take ((size xs)-n) xs) @ (replicate n False))"

value "[True,True] \<guillemotleft> 0"
value "[True,True] \<guillemotleft> 1"
value "[True,True] \<guillemotleft> 2"
value "[True,True] \<guillemotleft> 3"

(* TODO: prove same things for shl as shr... any easier way to do this? *)



end
