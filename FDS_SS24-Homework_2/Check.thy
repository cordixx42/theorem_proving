theory Check
  imports Submission
begin

lemma collect_alt: "collect x ys = map snd (filter (\<lambda>kv. fst kv = x) ys)"
  by (rule Submission.collect_alt)

lemma collect_tr_collect: "collect_tr [] x ys = collect x ys"
  by (rule Submission.collect_tr_collect)

lemma perfect_num_leafs_height: "perfect t \<Longrightarrow> num_leafs t = 2^lheight t"
  by (rule Submission.perfect_num_leafs_height)

lemma set_shuffles: "zs \<in> set (shuffles xs ys) \<Longrightarrow> set zs = set xs \<union> set ys"
  by (rule Submission.set_shuffles)

end