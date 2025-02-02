theory Submission
  imports Defs
begin



fun incr :: "bool list \<Rightarrow> bool list" where
"incr [] = []" |
"incr (False#bs) = True # bs" |
"incr (True#bs) = False # incr bs"

fun T_incr :: "bool list \<Rightarrow> nat" where
"T_incr [] = 0" |
"T_incr (False#bs) = 1" |
"T_incr (True#bs) = T_incr bs + 1"

locale counter_with_decr =
  fixes decr::"bool list \<Rightarrow> bool list" and k::"nat"
  assumes
     decr[simp]: "decr ((replicate (k-(Suc 0)) False) @ [True]) =
                      (replicate (k-(Suc 0)) True) @ [False]" and
     decr_len_eq[simp]: "length (decr bs) = length bs" and
     k[simp]: "1 \<le> k"
begin

declare [[names_short]]

fun T_decr::"bool list \<Rightarrow> nat" where
  "T_decr _ = 1"

datatype op = Decr | Incr

fun exec1::"op \<Rightarrow> (bool list \<Rightarrow> bool list)" where
  "exec1 Incr = incr" |
  "exec1 Decr = decr"

fun T_exec1::"op \<Rightarrow> (bool list \<Rightarrow> nat)" where
  "T_exec1 Incr = T_incr" |
  "T_exec1 Decr = T_decr"

fun T_exec :: "op list \<Rightarrow> bool list \<Rightarrow> nat" where
  "T_exec [] bs = 0" |
  "T_exec (op # ops) bs = (T_exec1 op bs + T_exec ops (exec1 op bs))"


lemma incr1: "length bs = n \<Longrightarrow> T_incr bs \<le> length bs"
  apply(induction bs arbitrary: n  rule: T_incr.induct)
  apply(auto)
  done 

lemma texec1: " n \<ge> 1 \<Longrightarrow>  length bs = n \<Longrightarrow> T_exec1 op bs \<le> length bs" 
  apply(cases op)
  apply(simp)
  apply(auto simp add: incr1)
  done



lemma incr_len_eq: "length (incr bs) = length bs" 
  apply(induction bs)
  apply(auto)
  by (metis (full_types) Submission.incr.simps(2) Submission.incr.simps(3) length_Cons)

lemma exec1_len_eq: "length (exec1 op bs) = length bs" 
  apply(cases op)
  using decr_len_eq 
  apply simp
  using incr_len_eq
  by simp

lemma gen: " n \<ge> 1 \<Longrightarrow> length bs = n \<Longrightarrow> T_exec ops bs \<le> length ops * length bs" 
proof(induction ops bs arbitrary: n  rule: T_exec.induct)
  case (1 bs)
  then show ?case 
    by simp
next
  case (2 op ops bs)
  have uf: "T_exec (op # ops) bs = (T_exec1 op bs + T_exec ops (exec1 op bs)) " 
    by simp
  then show " T_exec (op # ops) bs \<le> length (op # ops) * length bs "
  proof(cases "(length (exec1 op bs))\<ge> 1")
    case True
    have ih: " T_exec ops (exec1 op bs) \<le> length ops * length (exec1 op bs)" using True 
      using "local.2.IH" by blast

    have uf: "T_exec (op # ops) bs = (T_exec1 op bs + T_exec ops (exec1 op bs)) " 
      by simp

    also have "... \<le> T_exec1 op bs + length ops * length (exec1 op bs) " using ih 
      by simp

    also have "... \<le> length bs + length ops * length (exec1 op bs)" using texec1 True 
      using "local.2.prems"(1) "local.2.prems"(2) by auto

    also have "... \<le> length bs + length ops * length bs" using exec1_len_eq
      by simp

    also have "... = length bs *  ( 1 + length ops)" 
      by simp

    also have "... = length (op # ops) * length bs"  
      by simp 

    finally show " T_exec (op # ops) bs \<le> length (op # ops) * length bs"
      by simp
  next
    case False
    then show ?thesis 
      by (metis (full_types) "local.2.prems"(1) "local.2.prems"(2) List.list.discI One_nat_def Submission.incr.elims Suc_leI decr_len_eq length_greater_0_conv local.exec1.cases local.exec1.simps(1) local.exec1.simps(2))
  qed
  
qed



theorem inc_dec_seq_ubound: "length bs = k \<Longrightarrow> T_exec ops bs \<le> length ops * length bs"
  using gen k
  by simp


fun oplist :: "nat \<Rightarrow> op list"  where
  "oplist 0 = []"
| "oplist (Suc 0) = [Incr]"
| "oplist (Suc (Suc n)) = Incr#Decr#(oplist n)"



definition "bs0 = 
  (if k=0 then [] else (replicate (k-1) True) @ [False])"

lemma induct_list012[case_names empty single multi]:
  "P [] \<Longrightarrow> (\<And>x. P [x]) \<Longrightarrow> (\<And>x y xs. P xs \<Longrightarrow> P (x#y#xs)) \<Longrightarrow> P xs"
  by (rule List.induct_list012)

lemma case_nat012[case_names zero one two]:
  "\<lbrakk>n = 0 \<Longrightarrow> P; n = 1 \<Longrightarrow> P; \<And>n'. n = Suc (Suc n') \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (metis One_nat_def nat.exhaust)


lemma op_len: "length (oplist n) = n" 
  apply(induction n rule: oplist.induct)
  apply(auto)
  done


lemma "k = 1 \<Longrightarrow> decr [True] = [False]" using decr
  by simp


lemma incr_bs0_gen: "T_incr ((replicate n True) @ [False]) = length ((replicate n True) @ [False])" 
  apply(induction n)
  apply(auto)
  done 
 

lemma incr_bs0: "T_incr bs0 = length bs0" 
  using incr_bs0_gen bs0_def 
  by simp


lemma incrr:  "incr ((replicate n True) @ [False]) = (replicate n False) @ [True]" 
  apply(induction n)
  apply(auto)
  done

lemma incrrr: "incr ((replicate (k-1) True) @ [False]) = (replicate (k-1) False) @ [True]" 
  using incrr by blast


lemma decrr: "decr ((replicate (k-1) False) @ [True]) = ((replicate (k-1) True) @ [False])"
  using decr 
  by simp


lemma incr_decr_bs0_gen: "decr (incr ((replicate (k-1) True) @ [False])) = ((replicate (k-1) True) @ [False])" 
  using incrrr decrr 
  by simp


lemma incr_decr_bs0: "(exec1 Decr (exec1 Incr bs0)) = bs0" 
  using incr_decr_bs0_gen bs0_def
  using k by auto



theorem inc_dec_seq_lbound: "length (oplist n) * k \<le> 2 * (T_exec (oplist n)  bs0)" 
proof(induction "oplist n" arbitrary: n  rule: induct_list012)
  case empty
  then show ?case 
    by simp
next
  case (single x)
  assume "[x] = oplist n"
  have op: "oplist n = [Incr]" using single 
    by (metis length_Cons local.oplist.simps(2) op_len)

  then have "k \<le> 2 * T_exec [Incr] bs0"  
  proof-
    have bs0_len:  "length bs0 = k" using bs0_def 
      by simp
    have " T_exec [Incr] bs0 = T_incr bs0" 
      by simp
    show "k \<le> 2 * T_exec [Incr] bs0" using incr_bs0 bs0_len
      by simp
  qed   

  then show "length (oplist n) * k \<le> 2 * T_exec (oplist n) bs0" using op 
    by simp
next
  case (multi x y xs)
  (* xs = oplist ?n \<Longrightarrow> length (oplist ?n) * k \<le> 2 * T_exec (oplist ?n) bs0 *)
  assume a: "x # y # xs = oplist n"

  then have x: "x = Incr"
      by (metis List.list.simps(3) local.multi.hyps(2) local.oplist.elims nth_Cons_0)
  then have y: "y = Decr"
      by (metis List.list.discI List.list.inject local.multi.hyps(2) local.oplist.elims)

  have b_1: " T_exec (oplist n) bs0 = (T_incr bs0 + T_exec (Decr#xs) (exec1 Incr bs0)) " using a x y
    by (metis local.T_exec.simps(2) local.T_exec1.simps(1))

  have b_2: "... = length bs0 + T_exec (Decr#xs) (exec1 Incr bs0)" using incr_bs0 
    by simp

  have b_3 :"... = length bs0 + (T_decr (exec1 Incr bs0) + T_exec xs (exec1 Decr (exec1 Incr bs0)))" 
    by simp

  have b_4:"... = length bs0 + 1 + T_exec xs (exec1 Decr (exec1 Incr bs0))" 
    by simp

  have b_5:"... = length bs0 + 1 + T_exec xs bs0" using  incr_decr_bs0 
    by simp

  have b_sum: "T_exec (oplist n) bs0 =  k + 1 + T_exec xs bs0 " using b_1 b_2 b_3 b_4 b_5 bs0_def
    by simp

  have "xs = oplist (n-2)" 
    by (metis List.list.inject List.list.simps(3) One_nat_def Suc_1 a diff_Suc_Suc diff_zero local.oplist.elims)

  then have "length (oplist (n-2)) * k \<le> 2 * T_exec xs bs0" using multi(1)
    by simp

  then have "(n-2) * k \<le> 2 * T_exec xs bs0"
    using op_len by force

  then have "n*k \<le>  (2 * T_exec xs bs0) + 2*k" 
    by (simp add: diff_mult_distrib)

  then have "n*k \<le> 2 * (k + 1 + T_exec xs bs0)"
    by simp

  then show "length (oplist n) * k \<le> 2 * T_exec (oplist n) bs0"
    using b_sum op_len by presburger
qed




(*
proof(induction bs0 rule: induct_list012)
  case empty
  have "bs0 = []" using empty
    by simp
  then have "k = 0" using bs0_def k 
    by simp
  then show "length (oplist n) * k \<le> 2 * T_exec (oplist n) bs0" 
    using k not_one_le_zero by blast
next
  case (single x)
  assume "[x] = bs0"
  have k_val: "k = 1" using bs0_def k 
    using single by force
  then have "x = False" using bs0_def single
    by simp
  then have bs_val: "bs0 = [False]" using single 
    by simp
  then have "length (oplist n)  \<le> 2* T_exec (oplist n) [False]" 
     (*apply-
    apply(induction n rule: oplist.induct)
      apply(auto)
    by (metis One_nat_def add_increasing append_self_conv2 bs0_def decr k_val plus_1_eq_Suc replicate_empty zero_le_one zero_neq_one)*)
    using c2 k_val
    by simp
  then show "length (oplist n) * k \<le> 2 * T_exec (oplist n) bs0" using k_val bs_val
    by simp
next
  case (multi x y xs)
  assume a_1: "xs = bs0 \<Longrightarrow> length (oplist n) * k \<le> 2 * T_exec (oplist n) bs0"
  assume a_2: " x # y # xs = bs0"
  have k_val: "k \<ge> 2" using bs0_def k 
    using List.list.discI local.multi.hyps(2) by fastforce
  have x_val: "x = True" using k_val bs0_def multi 
    by (metis (no_types, lifting) Cons_replicate_eq One_nat_def Suc_1 add_diff_assoc add_diff_assoc2 diff_add_0 k le_less length_replicate less_diff_conv nth_Cons_0 nth_append nth_replicate plus_1_eq_Suc replicate_0)
  then show "length (oplist n) * k \<le> 2 * T_exec (oplist n) bs0" 
  proof(cases "xs")
    case Nil
    then have y_val: "y = False" using bs0_def a_2
      by (metis List.list.discI last_ConsL last_ConsR snoc_eq_iff_butlast)
    then have bs0_val: "bs0 = [True,False]" using x_val y_val a_2 Nil 
      by simp
    then have " length (oplist n) * k \<le> 2 * T_exec (oplist n) [True,False]"
      sorry
    then show ?thesis using bs0_val 
      by simp
  next
    case (Cons a list)
    then show ?thesis sorry
  qed
qed
 
  *) 


  
end
end