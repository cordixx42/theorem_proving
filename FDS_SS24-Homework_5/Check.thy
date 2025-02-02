theory Check
  imports Submission
begin

lemma nth_root_of_plus_1_bound:
  "x\<ge>0 \<Longrightarrow> n>0 \<Longrightarrow> root n (1+x) \<le> 1 + x/n" 
  by (rule Submission.nth_root_of_plus_1_bound)

lemma binet: "fib n = (\<Phi>^n - \<Psi>^n) / sqrt 5"
  by (rule Submission.binet)

lemma trisecting: "\<exists>xs ys zs . length xs = length as div 3 \<and> length ys = length as div 3 \<and> as = xs @ ys @ zs"
  by (rule Submission.trisecting)

end