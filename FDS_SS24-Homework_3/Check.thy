theory Check
  imports Submission
begin

theorem remdups_set: "set (bst_remdups xs) = set xs"
  by (rule Submission.remdups_set)

theorem remdups_distinct: "distinct (bst_remdups xs)"
  by (rule Submission.remdups_distinct)

theorem remdups_sub: "sublist (bst_remdups xs) xs"
  by (rule Submission.remdups_sub)

lemma get_put: "valid t p \<Longrightarrow> put t p (get t p) = t"
  by (rule Submission.get_put)

lemma put_get: "valid t p \<Longrightarrow> get (put t p s) p = s"
  by (rule Submission.put_get)

lemma find_get: "p \<in> find t s \<Longrightarrow> get t p = s"
  by (rule Submission.find_get)

lemma put_find: "valid t p \<Longrightarrow> p \<in> find (put t p s) s"
  by (rule Submission.put_find)

end