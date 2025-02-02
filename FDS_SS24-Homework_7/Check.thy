theory Check
  imports Submission
begin

lemma T_split_min_cmpx: "xs \<noteq> [] \<Longrightarrow> T_split_min xs = length xs"
  by (rule Submission.T_split_min_cmpx)

lemma C_qsort_bound: "C_qsort xs \<le> (length xs)\<^sup>2"
  by (rule Submission.C_qsort_bound)

lemma mset_rev_pre: "mset (rev_pre n xs) = mset xs"
  by (rule Submission.mset_rev_pre)

lemma mset_place_max_correct: "mset (place_max_correct (x#xs)) = mset (x#xs)"
  by (rule Submission.mset_place_max_correct)

lemma last_place_max_correct: "xs \<noteq> [] \<Longrightarrow> last (place_max_correct xs) = Max (set xs)"
  by (rule Submission.last_place_max_correct)

lemma length_place_max_correct: "length (place_max_correct (x#xs)) = length (x#xs)"
  by (rule Submission.length_place_max_correct)

lemma psort_mset: "mset (psort xs) = mset xs"
  by (rule Submission.psort_mset)

lemma sorted_psort: "sorted (psort xs)"
  by (rule Submission.sorted_psort)

lemma mset_rev_pre_chain_psort_revs: "mset (rev_pre_chain (psort_revs xs) xs) = mset xs"
  by (rule Submission.mset_rev_pre_chain_psort_revs)

lemma sorted_psort_revs: "sorted (rev_pre_chain (psort_revs xs) xs)"
  by (rule Submission.sorted_psort_revs)

end