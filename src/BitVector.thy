(*
 * Author: Ryan Flynn
 * Description: Define bitv type and operations.
 *)

theory BitVector 
imports Main Bit
begin

(* TODO: convert to/from integer value *)

(* things that i'd like to express in the vector type that i don't
 * know how:
 *   vectors must be of length > 0
 *)
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

definition not :: "bool \<Rightarrow> bool" where "not x \<equiv> (\<not>x)"
definition bnot :: "bitv \<Rightarrow> bitv" where
"bnot xs = map not xs"

(* bnot does not change the length of a vector *)
(* bnot modifies every value in a vector *)
(*
lemma bnot_empty [simp]: "bnot [] = []" by auto
*)

(*
lemma bnot_notempty [iff]: "(bnot x \<noteq> x) = (x \<noteq> [])"
apply(induct_tac x)
apply(induct_tac a)
*)

fun zipWith :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list" where
"zipWith f [] _ = []" |
"zipWith f _ [] = []" |
"zipWith f (x#xs) (y#ys) = (f x y) # (zipWith f xs ys)"

(* the length of zipWith's return is the length of its shorter parameter *)

definition and2 :: gate where "and2 x y \<equiv> x \<and> y"
definition band :: "bitv \<Rightarrow> bitv \<Rightarrow> bitv" (infixr "&" 50) where
"band xs ys \<equiv> zipWith and2 xs ys"

(*
theorem band_equiv [simp]: "\<lbrakk> x \<in> {True,False}; y \<in> {True,False} \<rbrakk> \<Longrightarrow> hd(x & y) = (hd(x)) & (hd(y))"
apply(simp only: band_def)
apply(auto)
*)

(* wrap or so it can be used as a parameter to zipWith *)
definition or :: gate where "or x y \<equiv> x \<or> y"

definition bor :: "bitv \<Rightarrow> bitv \<Rightarrow> bitv" (infixr "|" 50) where
"bor xs ys \<equiv> zipWith or xs ys"

fun shr :: "bitv \<Rightarrow> nat \<Rightarrow> bitv" (infixr "\<guillemotright>" 50) where
"shr [] _ = []" |
"shr xs n = (if n > size xs
             then (replicate (size xs) False)
             else (replicate n False) @ (take ((size xs)-n) xs))"

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

(* TODO: prove same things for shl as shr... any shortcut? *)

value "(3 mod 2)"

(* FIXME: (n-(size xs)) should be (n mod (size xs)) except that it
 * doesn't parse correctly due to something with mod, not sure...* *)
fun ror :: "'a vector \<Rightarrow> nat \<Rightarrow> 'a vector" where
"ror [] _ = []" |
"ror xs n = (if n > (size xs)
             then (ror xs (n - size xs))
             else let s = (size xs) - n
                  in (drop s xs) @ (take s xs))"

fun foldr :: "('a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'a \<Rightarrow> 'a" where
"foldr _ [] z = z" |
"foldr f (x#xs) z = foldr f xs (f z x)"

primrec bitcnt :: "bool \<Rightarrow> nat" where
"bitcnt True = 1" |
"bitcnt False = 0"

definition popcnt :: "nat \<Rightarrow> bool \<Rightarrow> nat" where
"popcnt n b \<equiv> n + (bitcnt b)"

definition pop :: "bitv \<Rightarrow> nat" where
"pop v = foldr popcnt v 0"

definition sort :: "bitv \<Rightarrow> bitv" where
"sort v \<equiv>
  let
    p = pop v
  in
    (replicate ((size v)-p) False) @
    (replicate p True)"

value "sort []"
value "sort [True,False]" 

fun first1b :: "bitv \<Rightarrow> nat \<Rightarrow> nat" where
"first1b [] n = n" |
"first1b (True # xs) n = n" |
"first1b (False # xs) n = first1b xs n+1"

(* index of first True; size v iff none *)
definition first1 :: "bitv \<Rightarrow> nat" where
"first1 v \<equiv> first1b v 0"

(* index of last True; size v iff none *)
definition last1 :: "bitv \<Rightarrow> nat" where
"last1 v \<equiv>
  let
    s = (size v);
    f = first1 (rev v)
  in
   if s = f then s
   else s - f - 1"

fun first0b :: "bitv \<Rightarrow> nat \<Rightarrow> nat" where
"first0b [] n = n" |
"first0b (False # xs) n = n" |
"first0b (True # xs) n = first0b xs n+1"

(* index of first False; size v iff none *)
definition first0 :: "bitv \<Rightarrow> nat" where
"first0 v \<equiv> first0b v 0"

(* index of last False; size v iff none *)
definition last0 :: "bitv \<Rightarrow> nat" where
"last0 v \<equiv>
  let
    s = (size v);
    f = first0 (rev v)
  in
   if s = f then s
   else s - f - 1"

(* TODO: theorems about {first,last}[01] *)

end
