theory Check
  imports Submission
begin

lemma set_trie_insert_trie: "set_trie(insert_trie xs t) = set_trie t \<union> {xs}"
  by (rule Submission.set_trie_insert_trie)

lemma set_trie_delete_trie: "set_trie(delete_trie xs t) = set_trie t - {xs}"
  by (rule Submission.set_trie_delete_trie)

lemma invar_insert_trie: "invar t \<Longrightarrow> invar(insert_trie xs t)"
  by (rule Submission.invar_insert_trie)

lemma invar_delete_trie: "invar t \<Longrightarrow> invar(delete_trie xs t)"
  by (rule Submission.invar_delete_trie)

end