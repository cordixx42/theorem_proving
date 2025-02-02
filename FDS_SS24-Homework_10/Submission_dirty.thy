theory Submission_dirty
  imports Defs
begin

fun isin_trie :: "trie \<Rightarrow> bool list \<Rightarrow> bool"  where
  "isin_trie LfR xs = False"
| "isin_trie LfA xs = True"
| "isin_trie (Nd b (t1,t2)) [] = b"
| "isin_trie (Nd b (t1,t2)) (x#xs) = (if x then isin_trie t2 xs else isin_trie t1 xs)"

definition set_trie :: "trie \<Rightarrow> bool list set" where
  "set_trie t = {xs. isin_trie t xs}"

definition node :: "bool \<Rightarrow> trie * trie \<Rightarrow> trie"  where
  "node b t = (if (fst t) = LfR \<and> (snd t) = LfR \<and> \<not>b then LfR 
                     else if (fst t) = LfA \<and> (snd t) = LfA \<and> b then LfA
                     else Nd b t)"


lemma invar_node [simp]:  "invar t1 \<Longrightarrow> invar t2 \<Longrightarrow> invar (node b (t1,t2))" 
  apply(simp add: node_def)
  done 

(*lemma set_node [simp]: "b = False \<Longrightarrow> set_trie t1 \<union> set_trie t2  = set_trie(node b (t1,t2))" nitpick
  oops
*)

fun insert_trie :: "bool list \<Rightarrow> trie \<Rightarrow> trie"  where
  "insert_trie [] LfR = Nd True (LfR,LfR)"
| "insert_trie [] LfA = LfA"
| "insert_trie [] (Nd b (t1,t2)) = node True (t1,t2)"
| "insert_trie (x#xs) LfA = LfA"
| "insert_trie (x#xs) LfR = (if x then node False (LfR, (insert_trie xs LfR)) else node False ((insert_trie xs LfR), LfR))"
| "insert_trie (x#xs) (Nd b (t1,t2)) = (if x then node b (t1, insert_trie xs t2) else node b (insert_trie xs t1, t2))"


value "insert_trie [True]  (Nd False (LfR, Nd True (LfR, LfR))) =  (Nd False (LfR, Nd True (LfR, LfR)))"
value "isin_trie  (Nd False (LfR, Nd True (LfR, LfR))) [True]"

fun delete_trie :: "bool list \<Rightarrow> trie \<Rightarrow> trie"  where
  "delete_trie xs LfR = LfR"
| "delete_trie [] LfA = Nd False (LfA,LfA)"
| "delete_trie (x#xs) LfA = (if x then node True (LfA, delete_trie xs LfA) else node True (delete_trie xs LfA, LfA))"
| "delete_trie [] (Nd b (t1,t2)) = node False (t1,t2)"
| "delete_trie (x#xs) (Nd b (t1,t2)) = (if x then node b (t1, delete_trie xs t2) else node b (delete_trie xs t1, t2))"

find_consts " ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set"

(*lemma set_trie_Nd: "set_trie (Nd False (t1,t2)) = (image (\<lambda>x. False#x) (set_trie t1)) \<union> image (\<lambda>x. True#x) (set_trie t2)" 
  oops*)

lemma set_trie_LfR: "set_trie LfR = {}" 
  apply(simp add: set_trie_def)
  done

lemma set_trie_LfA: "\<forall>xs. xs \<in> set_trie LfA" 
  apply(simp add: set_trie_def)
  done

lemma stit_1: "set_trie (Nd True (LfR,LfR)) = {[]}" 
  apply(simp add: set_trie_def)
  by (smt (z3) Collect_cong Defs.trie.distinct(5) Defs.trie.inject Product_Type.prod.sel(1) Product_Type.prod.sel(2) Submission.isin_trie.elims(1) Submission.isin_trie.simps(1) Submission.isin_trie.simps(3) singleton_conv)

lemma stit_2: "[] \<in> set_trie LfA" 
  by (simp add: set_trie_LfA)

lemma stit_3: "set_trie (Nd b (t1, t2)) = set_trie (node b (t1,t2))" 
  by (smt (z3) Collect_cong Defs.trie.distinct(3) Defs.trie.distinct(5) Defs.trie.inject Submission.isin_trie.elims(1) Submission.isin_trie.simps(1) Submission.isin_trie.simps(2) fst_conv node_def set_trie_def snd_conv)

lemma stit_32: "[] \<in> set_trie (node True t)" 
  using set_trie_def
  by (metis Product_Type.old.prod.exhaust Submission.isin_trie.simps(3) mem_Collect_eq stit_3)

lemma stit_33: "[] \<notin> set_trie (node False t)" 
  using set_trie_def
  by (metis Product_Type.old.prod.exhaust Submission.isin_trie.simps(1) Submission.isin_trie.simps(3) mem_Collect_eq node_def)

lemma stit_35: "isin_trie (Nd False t) ys \<Longrightarrow> isin_trie (Nd True t) ys" 
  using Submission.isin_trie.elims(1) by force

lemma stit_36: " b = True  \<longleftrightarrow> [] \<in> set_trie (node b t)" 
  by (metis (full_types) stit_32 stit_33)

lemma stit_37: "ys \<noteq> [] \<Longrightarrow>  isin_trie (Nd True t) ys \<Longrightarrow> isin_trie (Nd False t) ys" 
  using Submission.isin_trie.elims(3) by fastforce

lemma stit_34: "set_trie (node True (t1,t2)) = set_trie (Nd False (t1,t2)) \<union> {[]}"
  using set_trie_def stit_35 stit_37
  by (smt (verit) Collect_cong Submission.isin_trie.simps(3) Un_def insert_compr mem_Collect_eq stit_3 sup_bot_right)

lemma isin_insert: "isin_trie (insert_trie xs t) ys = (xs = ys \<or> isin_trie t ys)" 
  apply(induction xs t arbitrary: ys   rule: insert_trie.induct)  
  using stit_1 set_trie_LfR apply (metis Submission.insert_trie.simps(1) insert_iff mem_Collect_eq set_trie_def)
  using stit_2 set_trie_LfA apply force
  subgoal for b t1 t2 ys
    by (metis (full_types) Submission.insert_trie.simps(3) mem_Collect_eq set_trie_def stit_3 stit_32 stit_35 stit_37)
  using set_trie_LfA apply simp
  subgoal for x xs ys
  proof -
    assume a_1: "(\<And>ys. x \<Longrightarrow> isin_trie (insert_trie xs LfR) ys = (xs = ys \<or> isin_trie LfR ys))"
    assume a_2: "(\<And>ys. \<not> x \<Longrightarrow> isin_trie (insert_trie xs LfR) ys = (xs = ys \<or> isin_trie LfR ys))"
    have "(insert_trie (x # xs) LfR) =  (if x then node False (LfR, (insert_trie xs LfR)) else node False ((insert_trie xs LfR), LfR))" try0
      by simp
    show "isin_trie (insert_trie (x # xs) LfR) ys = (x # xs = ys \<or> isin_trie LfR ys)"
    proof(cases x)
      case True
      have "(insert_trie (x # xs) LfR) =  node False (LfR, (insert_trie xs LfR))" using True
        by simp
      then show "isin_trie (insert_trie (x # xs) LfR) ys = (x # xs = ys \<or> isin_trie LfR ys)" using a_1
        by (smt (z3) List.min_list.cases Submission.isin_trie.simps(1) Submission.isin_trie.simps(4) True mem_Collect_eq node_def set_trie_def snd_conv stit_33)
    next
      case False
      have "(insert_trie (x # xs) LfR) = node False ((insert_trie xs LfR), LfR)" using False
        by simp
      then show ?thesis using a_2
        by (smt (z3) False List.min_list.cases Submission.isin_trie.simps(1) Submission.isin_trie.simps(3) Submission.isin_trie.simps(4) fst_conv node_def)
    qed
  qed
  subgoal for x xs b t1 t2 ys
  proof-
    assume a_1: " (\<And>ys. x \<Longrightarrow> isin_trie (insert_trie xs t2) ys = (xs = ys \<or> isin_trie t2 ys))"
    assume a_2: "(\<And>ys. \<not> x \<Longrightarrow> isin_trie (insert_trie xs t1) ys = (xs = ys \<or> isin_trie t1 ys))"
    show "isin_trie (insert_trie (x # xs) (Nd b (t1, t2))) ys = (x # xs = ys \<or> isin_trie (Nd b (t1, t2)) ys)" 
    proof(cases x)
      case True
      have uf: "insert_trie (x # xs) (Nd b (t1, t2)) =   node b (t1, insert_trie xs t2) " using True 
        by simp
      have ih: "isin_trie (insert_trie xs t2) ys = (xs = ys \<or> isin_trie t2 ys)" using a_1 True
        by simp
      then show "isin_trie (insert_trie (x # xs) (Nd b (t1, t2))) ys = (x # xs = ys \<or> isin_trie (Nd b (t1, t2)) ys)" using uf ih
        by (smt (z3) List.min_list.cases Submission.isin_trie.simps(1) Submission.isin_trie.simps(3) Submission.isin_trie.simps(4) True a_1 fst_conv mem_Collect_eq node_def set_trie_def snd_conv stit_3 stit_35)
    next
      case False
       have "insert_trie (x # xs) (Nd b (t1, t2)) = node b (insert_trie xs t1, t2)" using False 
         by simp
       have uf: "insert_trie (x # xs) (Nd b (t1, t2)) =   node b ( insert_trie xs t1, t2) " using False 
         by simp
       have ih: "isin_trie (insert_trie xs t1) ys = (xs = ys \<or> isin_trie t1 ys)" using a_2 False 
         by simp
       then show ?thesis using uf ih 
         by (smt (z3) List.min_list.cases Submission.isin_trie.simps(1) Submission.isin_trie.simps(3) Submission.isin_trie.simps(4) False a_2 fst_conv mem_Collect_eq node_def set_trie_def snd_conv stit_3 stit_35)
    qed
  qed
 done
  

lemma set_trie_insert_trie: "set_trie(insert_trie xs t) = set_trie t \<union> {xs}" 
  apply(simp add: isin_insert set_trie_def)
  by auto


lemma stdt_3: "isin_trie (Nd b (t1, t2)) ys  = isin_trie (node b (t1,t2)) ys" 
  by (metis mem_Collect_eq set_trie_def stit_3)


lemma isin_delete: "isin_trie (delete_trie xs t) ys = (xs \<noteq> ys \<and> isin_trie t ys)" 
  apply(induction xs t arbitrary: ys  rule: delete_trie.induct)  
  apply(simp)
  using Submission.isin_trie.elims(3) apply fastforce
  subgoal for x xs ys 
  proof-
    assume a_1: "(\<And>ys. x \<Longrightarrow> isin_trie (delete_trie xs LfA) ys = (xs \<noteq> ys \<and> isin_trie LfA ys))"
    assume a_2: "(\<And>ys. \<not> x \<Longrightarrow> isin_trie (delete_trie xs LfA) ys = (xs \<noteq> ys \<and> isin_trie LfA ys))"
    show "isin_trie (delete_trie (x # xs) LfA) ys = (x # xs \<noteq> ys \<and> isin_trie LfA ys)"
    proof(cases ys)
      case Nil
      then show ?thesis 
        using set_trie_def stit_32 by auto
    next
      case (Cons a list)
      then show ?thesis
        using a_1 a_2 node_def by force
    qed
  qed
  apply (smt (z3) Submission.delete_trie.simps(4) Submission.isin_trie.simps(3) Un_commute insert_iff insert_is_Un mem_Collect_eq set_trie_def stit_3 stit_34)
  subgoal for x xs b t1 t2 ys
  proof - 
    assume a_1: "(\<And>ys. x \<Longrightarrow> isin_trie (delete_trie xs t2) ys = (xs \<noteq> ys \<and> isin_trie t2 ys))"
    assume a_2: "(\<And>ys. \<not> x \<Longrightarrow> isin_trie (delete_trie xs t1) ys = (xs \<noteq> ys \<and> isin_trie t1 ys))"
    show "isin_trie (delete_trie (x # xs) (Nd b (t1, t2))) ys = (x # xs \<noteq> ys \<and> isin_trie (Nd b (t1, t2)) ys)" 
    proof(cases ys)
      case Nil
      then show ?thesis 
        using Submission.isin_trie.simps(3) stdt_3 by auto
    next
      case (Cons a list)
      then show ?thesis
    proof(cases x)
      case True
      have uf: "delete_trie (x # xs) (Nd b (t1, t2)) = node b (t1, delete_trie xs t2)" using True 
        by simp
      have uff: "isin_trie (node b (t1, delete_trie xs t2)) ys = isin_trie (Nd b (t1, delete_trie xs t2)) ys" using stdt_3 
        by simp
      have ih: "isin_trie (delete_trie xs t2) ys = (xs \<noteq> ys \<and> isin_trie t2 ys)" using a_1 True
        by simp
      then show "isin_trie (delete_trie (x # xs) (Nd b (t1, t2))) ys = (x # xs \<noteq> ys \<and> isin_trie (Nd b (t1, t2)) ys)" 
      proof(cases ys)
        case Nil
        then show ?thesis
          using Submission.isin_trie.simps(3) stdt_3 by auto
      next
        case (Cons a list)
        then show ?thesis
          using True a_1 uff by force
      qed    
    next
      case False
      have uf: "delete_trie (x # xs) (Nd b (t1, t2)) = node b (delete_trie xs t1, t2)" using False
        by simp
      have uff: "isin_trie (node b (t1, delete_trie xs t2)) ys = isin_trie (Nd b (t1, delete_trie xs t2)) ys" using stdt_3 
        by simp
      have ih: "isin_trie (delete_trie xs t1) ys = (xs \<noteq> ys \<and> isin_trie t1 ys)" using a_2 False
        by simp
      then show "isin_trie (delete_trie (x # xs) (Nd b (t1, t2))) ys = (x # xs \<noteq> ys \<and> isin_trie (Nd b (t1, t2)) ys)" 
      proof(cases ys)
        case Nil
        then show ?thesis
          using Submission.isin_trie.simps(3) stdt_3 by auto
      next
        case (Cons a list)
        then show ?thesis
          using Submission.isin_trie.simps(4) stdt_3 False a_2
          by simp
      qed    
    qed
  qed
 qed
 done 

   

lemma set_trie_delete_trie: "set_trie(delete_trie xs t) = set_trie t - {xs}"
  using isin_delete set_trie_def
  by auto

lemma invar_insert_trie: "invar t \<Longrightarrow> invar(insert_trie xs t)" 
  apply(induction xs t rule: insert_trie.induct)
  apply(auto)
  done 

lemma invar_delete_trie: "invar t \<Longrightarrow> invar(delete_trie xs t)"
  apply(induction xs t rule: delete_trie.induct)
  apply(auto)
  done 

interpretation S: Set
  where empty = empty_trie and isin = isin_trie and insert = insert_trie and delete = delete_trie
    and set = set_trie and invar = invar
proof(unfold_locales,goal_cases)
  case 1
  then show ?case 
    using set_trie_LfR by auto
next
  case (2 s x)
  then show ?case
    by (simp add: set_trie_def)
next
  case (3 s x)
  then show ?case using set_trie_insert_trie
    by simp
next
  case (4 s x)
  then show ?case using set_trie_delete_trie 
    by simp
next
  case 5
  then show ?case 
    by simp
next
  case (6 s x)
  then show ?case using invar_insert_trie 
    by simp
next
  case (7 s x)
  then show ?case using invar_delete_trie
    by simp
qed
  
end