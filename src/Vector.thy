
theory Vector 
imports Main Boolean
begin

(* TODO: convert to/from integer value *)

types 'a vector = "'a list"
      bitv      = "bool list"

definition new :: "nat \<Rightarrow> bitv" where
"new n \<equiv> replicate n False"

(* we get equality "=" for free with list *)

fun zipWith :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list" where
"zipWith f [] _ = []" |
"zipWith f _ [] = []" |
"zipWith f (x#xs) (y#ys) = (f x y) # (zipWith f xs ys)"

datatype eq = Eq | Lt | Gt

(* NOTE: for mismatched sizes, we only account for the smallest size *)
fun cmp :: "bitv \<Rightarrow> bitv \<Rightarrow> eq" where
"cmp [] _ = Eq" |
"cmp _ [] = Eq" |
"cmp (False # xs) (True # ys) = Lt" |
"cmp (True # xs) (False # ys) = Gt" |
"cmp (x # xs) (y # ys) = cmp xs ys"

(* NOTE: for mismatched sizes, we only account for the smallest size *)
fun lt2 :: "bitv \<Rightarrow> bitv \<Rightarrow> bool" where
"lt2 [] _ = False" |
"lt2 _ [] = False" |
"lt2 (False # xs) (True # ys) = True" |
"lt2 (True # xs) (False # ys) = False" |
"lt2 (x # xs) (y # ys) = lt2 xs ys"

definition lt :: "bitv \<Rightarrow> bitv \<Rightarrow> bool" (infixr "<" 50) where
"lt xs ys \<equiv> lt2 (rev xs) (rev ys)"

value "[True] < [False]"
value "[True] < [True]"
value "[False,True] < [True,False]"
value "[True,False] < [False,True]"
value "[] < [False]"

fun lteq2 :: "bitv \<Rightarrow> bitv \<Rightarrow> bool" where
"lteq2 [] _ = True" |
"lteq2 _ [] = True" |
"lteq2 (False # xs) (True # ys) = True" |
"lteq2 (True # xs) (False # ys) = False" |
"lteq2 (x # xs) (y # ys) = lteq2 xs ys"

definition lteq :: "bitv \<Rightarrow> bitv \<Rightarrow> bool" (infixr "\<le>" 50) where
"lteq xs ys \<equiv> lteq2 (rev xs) (rev ys)"

fun gt2 :: "bitv \<Rightarrow> bitv \<Rightarrow> bool" where
"gt2 [] _ = False" |
"gt2 _ [] = False" |
"gt2 (False # xs) (True # ys) = False" |
"gt2 (True # xs) (False # ys) = True" |
"gt2 (x # xs) (y # ys) = gt2 xs ys"

definition gt :: "bitv \<Rightarrow> bitv \<Rightarrow> bool" (infixr ">" 50) where
"gt xs ys \<equiv> gt2 (rev xs) (rev ys)"

value "[False] > [True]"
value "[False,True] > [True,False]"
value "[True] > [True]"

definition and2 :: gate where "and2 x y \<equiv> x \<and> y"
definition band :: "bitv \<Rightarrow> bitv \<Rightarrow> bitv" (infixr "&" 50) where
"band xs ys \<equiv> zipWith and2 xs ys"

value "True & False"
value "[True] & [False]"

(*
theorem band_equiv: "hd(x & y) = (hd(x)) & (hd(y))"
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
apply(induct_tac xs)
apply(auto)
done

(* shifting by more than length equivalent to shifting by length *)
theorem shr_toomany: "xs \<guillemotright> (length xs) = (xs \<guillemotright> ((length xs) + 1))"
apply(induct_tac xs)
apply(simp)
apply(auto)
done

(* shifting by the full length is equivalent to setting value to all False *)
theorem shr_max_val: "xs \<guillemotright> (length xs) = replicate (length xs) False"
apply(induct_tac xs)
apply(auto)
done

(* shifting preserves the size of a vector *)
theorem shr_preserve_size: "length xs = length (xs \<guillemotright> n)"
apply(induct_tac xs)
apply(auto)
done

fun shl :: "bitv \<Rightarrow> nat \<Rightarrow> bitv" (infixr "\<guillemotleft>" 50) where
"shl [] _ = []" |
"shl xs n = (if n > size xs
             then (replicate (size xs) False)
             else (take ((size xs)-n) xs) @ (replicate n False))"

value "[True,True] \<guillemotleft> 0"
value "[True,True] \<guillemotleft> 1"
value "[True,True] \<guillemotleft> 2"
value "[True,True] \<guillemotleft> 3"

end
