theory Submission_dirty
  imports Defs
begin


(*
numeral_eq_Suc
power_numeral_reduce
eval_nat_numeral
*)

find_theorems "numeral"


lemma nth_root_of_plus_1_bound:
  fixes x :: real  and n :: nat
  assumes ass_1: "x\<ge>0" and ass_2: "n>0" 
  shows "root n (1+x) \<le> 1 + x/n" 
proof -
  have r: "(x/n) \<ge> -1" using assms  by (simp add: field_simps)
  have g: "(1 + n*(x/n)) \<le>  (1 + (x/n))^n" using r Bernoulli_inequality by (blast)

  have i: "root n (1+x) \<ge> 0" using assms by (simp)
  have j:  "(1+ x/n) \<ge> 0" using assms by (simp)
  have k: " (root n (1+x))^n \<le>  (1+ x/n)^n  \<Longrightarrow>  (root n (1+x)) \<le> (1 + x/n)" using ass_2 i j by (simp)

  have l: " (root n (1+x))^n \<le>  (1+ x/n)^n" 
  proof- 
    have "(root (n::nat) (1+(x::real)))^n = 1+x " using assms by (simp)
    also have "\<dots> = (1 + n*(x/n))" using assms by (simp)
    also have "\<dots> \<le> (1 + x/n)^n" using g by (simp)
    finally show "(root n (1+x))^n \<le> (1 + x/n)^n " by (simp)
  qed 

  from k l show "(root n (1+x)) \<le> (1 + x/n)" by (simp)
qed
 


lemma binet: "fib n = (\<Phi>^n - \<Psi>^n) / sqrt 5"
proof(induction n rule: fib.induct)
  case 1
  show "(fib 0) = (\<Phi> ^ 0 - \<Psi> ^ 0) / sqrt 5"
    by simp 
next
  case 2
  have f:  "\<Phi> =  (1 + sqrt 5) / 2" by (simp add: \<Phi>_def)
  have s: "\<Psi> =  (1 - sqrt 5) / 2" by (simp add: \<Psi>_def)
  from f s show "fib (Suc 0) = (\<Phi>^(Suc 0) - \<Psi>^(Suc 0)) / sqrt 5"
    by(simp add: add_divide_distrib)
next
  case (3 n)
  assume IH1: "fib n = (\<Phi>^n - \<Psi>^n) / sqrt 5"
  assume IH2: "fib (Suc n) = (\<Phi>^(Suc n) - \<Psi>^(Suc n)) / sqrt 5"
  have "fib (Suc (Suc n)) = fib n + fib (Suc n) " by (simp)
  also have "\<dots> = (\<Phi>^n - \<Psi>^n) / sqrt 5 + (fib (Suc n))" by (simp add: IH1)
  also have "\<dots> = (\<Phi>^n - \<Psi>^n) / sqrt 5 + (\<Phi>^(Suc n) - \<Psi>^(Suc n)) / sqrt 5" by (simp add: IH2)
  also have "\<dots> = ((\<Phi>^n - \<Psi>^n) + (\<Phi>^(Suc n) - \<Psi>^(Suc n)))  / sqrt 5" by(simp add: add_divide_distrib)
  also have "\<dots> = ((\<Phi>^n + \<Phi>^(Suc n)) - (\<Psi>^n + \<Psi>^(Suc n)))  / sqrt 5" by(simp)
  also have "\<dots> = ((\<Phi>^n + \<Phi>^(Suc n)) /sqrt 5) - ((\<Psi>^n + \<Psi>^(Suc n)) /sqrt 5)" by (simp add: diff_divide_distrib)
  also have "\<dots> = ((\<Phi>^n * 1 + \<Phi>^n * \<Phi>) /sqrt 5) - ((\<Psi>^n  + \<Psi>^(Suc n)) /sqrt 5)" by (simp)
  also have "\<dots> = ((\<Phi>^n * 1 + \<Phi>^n * \<Phi>) /sqrt 5) - ((\<Psi>^n * 1  + \<Psi>^n * \<Psi>) /sqrt 5)" by (simp)
  also have "\<dots> = ((\<Phi>^n * (1 + \<Phi>)) /sqrt 5) - ((\<Psi>^n * (1 + \<Psi>)) /sqrt 5)" by (simp add: distrib_left) 
  also have "\<dots> = ((\<Phi>^n * \<Phi>^2) /sqrt 5) - ((\<Psi>^n * (1 + \<Psi>)) /sqrt 5)" by (simp add: \<Phi>_square)
  also have "\<dots> = ((\<Phi>^n * \<Phi>^2) /sqrt 5) - ((\<Psi>^n * \<Psi>^2) /sqrt 5)" by (simp add: \<Psi>_square)
  also have "\<dots> = (\<Phi>^(Suc(Suc n)) /sqrt 5) - ((\<Psi>^n * \<Psi>^2) /sqrt 5)" by (simp add: power_numeral_reduce)
  also have "\<dots> = (\<Phi>^(Suc(Suc n)) /sqrt 5) - (\<Psi>^(Suc(Suc n)) /sqrt 5)" by (simp add: power_numeral_reduce)
  also have "\<dots> = (\<Phi>^(Suc(Suc n)) - \<Psi>^(Suc(Suc n))) /sqrt 5" by (simp add: diff_divide_distrib)
  finally show "fib (Suc (Suc n)) = (\<Phi>^(Suc (Suc n)) - \<Psi>^(Suc (Suc n))) / sqrt 5" by (simp)
qed

find_consts " _ \<Rightarrow> _ \<Rightarrow> _  \<Rightarrow> 'a list"


fun sublist ::  "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where 
   "sublist [] a b = []"
 | "sublist (x#xs) a b = (if b = 0 then [] else if a = 0 then (x#(sublist xs (a-1) (b-1))) else sublist xs (a-1) (b-1))"

value "sublist [(1::nat),2,3,4] (1::nat) 3 "
   
   

find_theorems "take"


lemma trisecting: 
  "\<exists>xs ys zs . length xs = length as div 3 \<and> length ys = length as div 3 \<and> as = xs @ ys @ zs"
proof-
  obtain xss where xss_init: "xss = (take (length as div 3) as)" by (simp)
  obtain yss where yss_init:  "yss = ((take (length as div 3) (drop (length as div 3) as)))" by (simp)
  obtain zss where zss_init: "zss = (drop ((length as div 3) + (length as div 3)) as)" by (simp)

  have a:  "length xss =  length as div 3" using xss_init by (simp)
  have b:  "length yss =  length as div 3" using yss_init by (simp)

  have d:   "xss @ yss  = take (2*(length as div 3)) as" using xss_init yss_init  by (simp add: take_add field_simps)

  have c: "as = (xss@yss)@zss" using xss_init yss_init zss_init d by (simp)
  then have "as = xss@yss@zss"  by (simp )
  then show  "\<exists>xs ys zs . length xs = length as div 3 \<and> length ys = length as div 3 \<and> as = xs @ ys @ zs" using a b by blast  
qed

proof (standard,standard,standard)
  have a:  "length (take (length as div 3) as) =  length as div 3" by (simp)
  have b:  "length ((take (length as div 3) (drop (length as div 3) as))) =  length as div 3" by (simp)


  have d:   "(take (length as div 3) as) @ ((take (length as div 3) (drop (length as div 3) as))) 
            = take ((length as div 3) + (length as div 3)) as" by (simp add: take_add)


  have c:   "as = 
                ((take (length as div 3) as
                @ ((take (length as div 3) (drop (length as div 3) as)))) 
                @ (drop ((length as div 3) + (length as div 3)) as))" using d by (simp)


  from a b c show 
        "length (take (length as div 3) as)  = length as div 3 
        \<and> length  ((take (length as div 3) (drop (length as div 3) as))) = length as div 3 
        \<and> as = (take (length as div 3) as) @  ((take (length as div 3) (drop (length as div 3) as))) @  (drop ((length as div 3) + (length as div 3)) as)"
    by (simp)
qed
end
