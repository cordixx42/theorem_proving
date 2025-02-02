theory Check
  imports Submission
begin

lemma delete_set_minus: "ibst t \<Longrightarrow> set_itree2 (delete x t) = (set_itree2 t) - {x}"
  by (rule Submission.delete_set_minus)

lemma ibst_delete: "ibst t \<Longrightarrow> ibst (delete x t)"
  by (rule Submission.ibst_delete)

end