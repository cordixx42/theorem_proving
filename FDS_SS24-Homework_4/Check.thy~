theory Check
  imports Submission
begin

lemma mbst_min: "mbst (Node l m a r) \<Longrightarrow> min_val (Node l m a r) = m"
  by (rule Submission.mbst_min)

lemma mbst_mins: "mbst t \<Longrightarrow> mbst (mins x t)"
  by (rule Submission.mbst_mins)

lemma misin_set: "mbst t \<Longrightarrow> misin x t \<longleftrightarrow> x\<in>set_mtree2 t"
  by (rule Submission.misin_set)

lemma mbst_range: "mbst t \<Longrightarrow> set (mtree_in_range t u v) = {x\<in>set_mtree2 t. u\<le>x \<and> x\<le>v}"
  by (rule Submission.mbst_range)

end