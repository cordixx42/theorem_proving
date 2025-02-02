theory Submission
  imports Defs
begin

fun oddsum :: "nat \<Rightarrow> nat"  where
  "oddsum 0 = 0"
| "oddsum (Suc n) = (oddsum n) + (n + n + 1)"

value "oddsum 3 = 5 + 3 + 1 + 0"
value "oddsum 7 = 49"
value "oddsum 1 = 1"

lemma oddsum_is_square: "oddsum n = n * n"
  apply (induction n)
  apply (auto)
  done 

lemma oddsum_mult: "oddsum (n*m) = oddsum n * oddsum m"  
 apply (simp add : oddsum_is_square)
  done

fun spread :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"  where
  "spread a []  = []"
| "spread a (y#ys) = y#([a]@(spread a ys))"


value "spread (2::nat) [4,5,6,2,4,5,6]"

value "spread (0::nat) [1,2,3] = [1,0,2,0,3,0]"

lemma count_spread: "count (spread a xs) a = count xs a + length xs"
  apply (induction xs)
  apply auto 
  done 


lemma aux_spread_snoc: " snoc (snoc (spread a xs) b) a = spread a (snoc xs b)"
  apply (induction xs)
   apply auto 
  done 

lemma spread_reverse_snoc: "snoc (reverse (spread a xs)) a = a # spread a (reverse xs)"
  apply (induction xs)
  apply (simp add: reverse_snoc)
  apply (simp add: aux_spread_snoc)
  done 

end
