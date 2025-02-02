theory Defs
  imports Main
begin

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] x = [x]" |
  "snoc (y # ys) x = y # (snoc ys x)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse [] = []" |
  "reverse (x # xs) = snoc (reverse xs) x"

lemma reverse_snoc: "reverse (snoc xs y) = y # reverse xs"
  by (induct xs) auto

theorem "reverse (reverse xs) = xs"
  by (induct xs) (auto simp add: reverse_snoc)

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "count [] _ = 0" |
  "count (x # xs) y = (if x = y then Suc (count xs y) else count xs y)"


consts oddsum :: "nat \<Rightarrow> nat"

consts spread :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"


end