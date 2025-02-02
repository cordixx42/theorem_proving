theory Check
  imports Submission
begin

lemma exists_simple_path: "(path G u p v) \<Longrightarrow> \<exists>p'. path G u p' v \<and> distinct p'"
  by (rule Submission.exists_simple_path)

theorem compnet_mset: "mset (run_compnet comps xs) = mset xs"
  by (rule Submission.compnet_mset)

lemma sort4_bool_exhaust: "all_n_lists (\<lambda>bs::bool list. sorted (run_compnet sort4 bs)) 4"
  by (rule Submission.sort4_bool_exhaust)

lemma compnet_map_mono: "(mono f) \<Longrightarrow> run_compnet cs (map f xs) = map f (run_compnet cs xs)"
  by (rule Submission.compnet_map_mono)

theorem zero_one_principle: "(\<And>bs:: bool list. length bs = length xs \<Longrightarrow> sorted (run_compnet cs bs)) \<Longrightarrow> sorted (run_compnet cs xs)"
  by (rule Submission.zero_one_principle)

end