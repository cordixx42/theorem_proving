theory Submission
  imports Defs
begin


lemma nth_root_of_plus_1_bound:
  fixes x :: real  and n :: nat
  assumes ass_1: "x\<ge>0" and ass_2: "n>0" 
  shows "root n (1+x) \<le> 1 + x/n" 
proof -
  have e: "((x/n)) \<ge> 0 " using assms by (simp)
  have f: "(b::real) \<ge> 0 \<Longrightarrow> (1 + n*(b::real)) \<le> (1+b)^n" for b by (simp add: Bernoulli_inequality)
  have g: " (x/n) \<ge> 0 \<Longrightarrow> (1 + n*(x/n)) \<le>  (1 + (x/n))^n" using f by (blast)
  have h: "(1 + n*(x/n)) \<le>  (1 + (x/n))^n" using e g by (simp)

  (*have q: " (x/n) \<ge> 0 \<Longrightarrow> (1 + n*(x/n)) \<le>  (1 + (x/n))^n" by (auto simp add: Bernoulli_inequality)*)
  (*have r: "(x/n) \<ge> -1" using e by (simp)*)

  have i: "root n (1+x) \<ge> 0" using assms by (simp)
  have j:  "(1+ x/n) \<ge> 0" using assms by (simp)
  have k: " (root n (1+x))^n \<le>  (1+ x/n)^n  \<Longrightarrow>  (root n (1+x)) \<le> (1 + x/n)" using i j ass_2 by (simp)

  have l: " (root n (1+x))^n \<le>  (1+ x/n)^n" 
  proof- 
    have "(root (n::nat) (1+(x::real)))^n = 1+x " using assms by (simp)
    also have "\<dots> = (1 + n*(x/n))" using assms by (simp)
    also have "\<dots> \<le> (1 + x/n)^n" using h by (simp)
    finally show "(root n (1+x))^n \<le> (1 + x/n)^n " by (simp)
  qed 

  from k l show "(root n (1+x)) \<le> (1 + x/n)" by (simp)
qed
 


lemma binet: "fib n = (\<Phi>^n - \<Psi>^n) / sqrt 5"
proof(induction n rule: fib.induct)
  case 1
  show "(fib 0) = (\<Phi> ^ 0 - \<Psi> ^ 0) / sqrt 5"
    by (simp) 
next
  case 2
  have f:  "\<Phi> =  (1 + sqrt 5) / 2" by (simp add: \<Phi>_def)
  have s: "\<Psi> =  (1 - sqrt 5) / 2" by (simp add: \<Psi>_def)
  from f s show "fib (Suc 0) = (\<Phi>^(Suc 0) - \<Psi>^(Suc 0)) / sqrt 5"
    by(simp)
next
  case (3 n)
  assume IH1: "fib n = (\<Phi>^n - \<Psi>^n) / sqrt 5"
  assume IH2: "fib (Suc n) = (\<Phi>^(Suc n) - \<Psi>^(Suc n)) / sqrt 5"
  have "fib (Suc (Suc n)) = fib n + fib (Suc n) " by (simp)
  also have "\<dots> = (\<Phi>^n - \<Psi>^n) / sqrt 5 + (fib (Suc n))" by (simp add: IH1)
  also have "\<dots> = (\<Phi>^n - \<Psi>^n) / sqrt 5 + (\<Phi>^(Suc n) - \<Psi>^(Suc n)) / sqrt 5" by (simp add: IH2)
  also have "\<dots> = ((\<Phi>^n * (1 + \<Phi>)) /sqrt 5) - ((\<Psi>^n * (1 + \<Psi>)) /sqrt 5)" by (simp add: field_simps) 
  also have "\<dots> = ((\<Phi>^n * \<Phi>^2) /sqrt 5) - ((\<Psi>^n * (1 + \<Psi>)) /sqrt 5)" by (simp add: \<Phi>_square)
  also have "\<dots> = ((\<Phi>^n * \<Phi>^2) /sqrt 5) - ((\<Psi>^n * \<Psi>^2) /sqrt 5)" by (simp add: \<Psi>_square)
  also have "\<dots> = (\<Phi>^(Suc(Suc n)) /sqrt 5) - ((\<Psi>^n * \<Psi>^2) /sqrt 5)" by (simp add: power_numeral_reduce)
  also have "\<dots> = (\<Phi>^(Suc(Suc n)) /sqrt 5) - (\<Psi>^(Suc(Suc n)) /sqrt 5)" by (simp add: power_numeral_reduce)
  finally show "fib (Suc (Suc n)) = (\<Phi>^(Suc (Suc n)) - \<Psi>^(Suc (Suc n))) / sqrt 5" by (simp add: field_simps)
qed



lemma trisecting: 
  "\<exists>xs ys zs . length xs = length as div 3 \<and> length ys = length as div 3 \<and> as = xs @ ys @ zs"
proof (intro exI)
  have d:   "(take (length as div 3) as) @ ((take (length as div 3) (drop (length as div 3) as))) 
            = take ((length as div 3) + (length as div 3)) as" by (simp add: take_add)
  have c:   "as = 
                ((take (length as div 3) as
                @ ((take (length as div 3) (drop (length as div 3) as)))) 
                @ (drop ((length as div 3) + (length as div 3)) as))" using d by (simp)
  from c show 
        "length (take (length as div 3) as)  = length as div 3 
        \<and> length  ((take (length as div 3) (drop (length as div 3) as))) = length as div 3 
        \<and> as = (take (length as div 3) as) @  ((take (length as div 3) (drop (length as div 3) as))) @  (drop ((length as div 3) + (length as div 3)) as)"
    by (simp)
qed
end
