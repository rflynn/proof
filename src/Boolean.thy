
theory Boolean
imports Main
begin

types gate = "bool \<Rightarrow> bool \<Rightarrow> bool"

value "True & False"
value "True | False"

definition xor :: gate where
"xor x y \<equiv> (x \<or> y) \<and> (\<not> (x \<and> y))"

theorem xor_neq [simp]: "(xor x y) = (x \<noteq> y)"
apply(simp only: xor_def)
apply(auto)
done

theorem xor_self [simp]: "(xor x x) = False"
apply(auto)
done

theorem xor_self2 [simp]: "xor x (\<not>x)"
apply(simp only: xor_def)
apply(auto)
done

definition nor :: gate where
"nor x y \<equiv> \<not>(x \<or> y)"

theorem nor_self [simp]: "nor x (\<not>x) = False"
apply(simp only: nor_def)
apply(auto)
done

definition xnor :: gate where
"xnor x y \<equiv> (x \<and> y) \<or> \<not>(x \<or> y)"

theorem xnor_eq [simp]: "xnor x y = (x = y)"
apply(simp only: xnor_def)
apply(auto)
done

definition nand :: gate where
"nand x y \<equiv> (\<not>(x \<and> y))"

theorem nand_xx [simp]: "nand x x \<equiv> \<not>x"
apply(simp only: nand_def)
apply(auto)
done

theorem nand_true [simp]: "nand True x \<equiv> \<not>x"
apply(simp only: nand_def)
apply(auto)
done

theorem nand_false: "nand False x"
apply(simp only: nand_def)
apply(auto)
done

end
