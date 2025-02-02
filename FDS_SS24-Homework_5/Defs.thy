theory Defs
  imports Complex_Main "HOL-Library.Tree"
begin

fun sumto :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
"sumto f 0 = 0" |
"sumto f (Suc n) = sumto f n + f(Suc n)"


fun fib :: "nat \<Rightarrow> nat" where
  "fib 0 = 0"
| "fib (Suc 0) = 1"
| "fib (Suc (Suc n)) = fib (Suc n) + fib n"

definition "\<Phi> \<equiv> (1 + sqrt 5) / 2"
definition "\<Psi> \<equiv> (1 - sqrt 5) / 2"

lemma \<Phi>_square: "\<Phi>^2 = 1+\<Phi>"
  by (simp add: field_simps \<Phi>_def power2_eq_square) 
lemma \<Psi>_square: "\<Psi>^2 = 1+\<Psi>"
  by (simp add: field_simps \<Psi>_def power2_eq_square)

end