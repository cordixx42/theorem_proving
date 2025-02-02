theory Submission
  imports Defs
begin

lemma exists_simple_path:
  assumes "path G u p v"
  shows "\<exists>p'. path G u p' v \<and> distinct p'"
  using assms proof(induction p rule: length_induct)     
  case (1 xs)
  assume "\<forall>ys. length ys < length xs \<longrightarrow> path G u ys v \<longrightarrow> (\<exists>p'. path G u p' v \<and> distinct p')"
  assume "path G u xs v"
  show "\<exists>p'. path G u p' v \<and> distinct p'" 
  proof(cases "distinct xs")
    case True
    then show ?thesis using "1.prems" by blast
  next
    case False 
    thm not_distinct_decomp[OF False]
    obtain ys zs as y where xs_split:  "xs = ys @ y # zs @ y # as" using not_distinct_decomp[OF False] by auto
    let ?ys_witness = "ys @ y # as" 
    have a: "length ?ys_witness < length xs" using xs_split by simp
    have b: "path G u ?ys_witness v" using  xs_split pump_nondistinct_path 1(2) by auto
    from a b show ?thesis using 1(1) by blast
  qed
qed

type_synonym comparator = "(nat \<times> nat)"
type_synonym compnet = "comparator list"

value "nth [1::nat,2,4] "

definition compnet_step :: "comparator \<Rightarrow> 'a :: linorder list \<Rightarrow> 'a list"  where
  "compnet_step c xs = (if (fst c) \<ge> length xs \<or> snd(c) \<ge> length xs then xs 
                        else if (nth xs (fst c)) > (nth xs (snd c)) then xs[(fst c) := (nth xs (snd c)), (snd c) := (nth xs (fst c))]
                        else xs) "

value "compnet_step (1,100) [1,2::nat] = [1,2]"
value "compnet_step (1,2) [1,3,2::nat] = [1,2,3]"

value "compnet_step (2,5) [1::nat,23,54,2,4,2]"

definition run_compnet :: "compnet \<Rightarrow> 'a :: linorder list \<Rightarrow> 'a list" where
  "run_compnet = fold compnet_step"

declare [[names_short]]

theorem compnet_mset[simp]: "mset (run_compnet comps xs) = mset xs" 
proof(induction comps arbitrary: xs) 
    case Nil
    then show ?case unfolding run_compnet_def by (simp)
  next
    case (Cons a comps)
    then show ?case unfolding run_compnet_def compnet_step_def by (simp add: mset_swap)
  qed 


definition sort4 :: compnet where
"sort4 = [(0,1),(2,3),(0,2),(1,3),(1,2)]"

value "length sort4 \<le> 5"
value "run_compnet sort4 [4,2,1,3::nat] = [1,2,3,4]"

lemma "length ls = 4 \<Longrightarrow> sorted (run_compnet sort4 ls)"
  oops

lemma sort4_bool_exhaust: "all_n_lists (\<lambda>bs::bool list. sorted (run_compnet sort4 bs)) 4"
  \<comment>\<open>Should be provable \<open>by eval\<close> if your definition is correct!\<close>
  by eval

lemma sort4_bool: "length (bs::bool list) = 4 \<Longrightarrow> sorted (run_compnet sort4 bs)"
  using sort4_bool_exhaust[unfolded all_n_lists_def] set_n_lists by fastforce

lemma compnet_step_mono: 
  assumes "mono f" 
  shows "compnet_step c (map f xs)  = map f (compnet_step c  xs)"
  apply(simp add: compnet_step_def) 
  apply(auto)
  apply (simp add: map_update)
  apply (metis (no_types, lifting) antisym_conv3 assms leD list_update_id map_update mono_invE)
  using assms mono_strict_invE by blast


lemma compnet_map_mono:
  assumes "mono f"
  shows "run_compnet cs (map f xs) = map f (run_compnet cs xs)"
proof(induction cs arbitrary: xs)
  case Nil
  then show ?case unfolding run_compnet_def 
    by simp
next
  case (Cons a cs)
  then show ?case unfolding run_compnet_def by (simp add: assms compnet_step_mono) 
qed


theorem zero_one_principle:
  assumes "\<And>bs:: bool list. length bs = length xs \<Longrightarrow> sorted (run_compnet cs bs)"
  shows "sorted (run_compnet cs xs)"
proof (rule ccontr)
  assume ass: "\<not> sorted (run_compnet cs xs)"   

  from  this obtain k where k_prop: "(k < (length (run_compnet cs xs)) - 1) \<and> (nth (run_compnet cs xs) k) >  (nth (run_compnet cs xs) (k + 1))" 
    using less_diff_conv sorted_iff_nth_Suc by fastforce

  have k_len: "(k + 1) <  length (run_compnet cs xs)" using k_prop
    by linarith

  let ?a_k = "(nth (run_compnet cs xs) k)"
  let ?a_k1 = "(nth (run_compnet cs xs) (k + 1))" 
  have g: "?a_k > ?a_k1" using k_prop by simp

  let ?f = "\<lambda>x. x > ?a_k1"
  have "mono ?f" using Fun.ord.mono_on_def by fastforce
  from this have f_mon: "run_compnet cs (map ?f xs) = map ?f (run_compnet cs xs)" using compnet_map_mono
    by blast

  let ?a_k' = "nth (map ?f (run_compnet cs xs)) k"
  let ?a_k1' = "nth (map ?f (run_compnet cs xs)) (k+1)"

  have a_k_t:  "?a_k' = True" using k_len g 
    by simp
  have a_k1_f: "?a_k1' = False" using k_len g 
    by simp

  from a_k_t a_k1_f have  "\<not> sorted (run_compnet cs (map ?f xs))"
    using  f_mon k_len sorted_wrt_nth_less by fastforce

  then show False using assms
    by simp
qed 

corollary "length xs = 4 \<Longrightarrow> sorted (run_compnet sort4 xs)"
  by (simp add: sort4_bool zero_one_principle)

end