theory Check
  imports Submission
begin

lemma acomplete_alt: "acomplete t \<longleftrightarrow> height t = min_height t \<or> height t = min_height t + 1"
  by (rule Submission.acomplete_alt)

lemma mk_rbt_inorder: "Tree2.inorder (list_to_rbt xs) = xs"
  by (rule Submission.mk_rbt_inorder)

lemma mk_rbt_color: "color (list_to_rbt xs) = Black"
  by (rule Submission.mk_rbt_color)

lemma mk_rbt_invh: "invh (list_to_rbt xs)"
  by (rule Submission.mk_rbt_invh)

lemma mk_rbt_invc: "invc (list_to_rbt t)"
  by (rule Submission.mk_rbt_invc)

end