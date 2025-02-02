theory Check
  imports Submission
begin

lemma inorder_merge: "inorder(treeI(merge l a m b r)) = (inorder l) @ a # (inorder m) @ b # (inorder r)"
  by (rule Submission.inorder_merge)

theorem invar_ins: "invar t \<Longrightarrow> invar (treeI(ins x t)) \<and> hI (ins x t) = height t"
  by (rule Submission.invar_ins)

end