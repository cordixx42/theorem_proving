 theory Submission_dirty
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


value "T_exec [Incr::op] [True::bool, False]"

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

(*
theorem inc_dec_seq_ubound: "length bs = k \<Longrightarrow> T_exec ops bs \<le> length ops * length bs"
proof(induction ops bs arbitrary:  rule: T_exec.induct)
  case (1 bs)
  then show ?case
    by simp
next
  case (2 op ops bs)
  assume a_1: "length (exec1 op bs) = k \<Longrightarrow> T_exec ops (exec1 op bs) \<le> length ops * length (exec1 op bs)"
  assume a_2: "length bs = k"


  have " T_exec1 op bs \<le> length bs" using texec1
    by (simp add: a_2)
    
  have uf: "T_exec (op # ops) bs = (T_exec1 op bs + T_exec ops (exec1 op bs))" 
    by simp
  
  then show "T_exec (op # ops) bs \<le> length (op # ops) * length bs" 
  proof(cases op)
    case Decr
    then have "length (exec1 op bs) = k" using decr_len_eq
      by (simp add: a_2)
    then show ?thesis 
      using "local.2.IH" \<open>T_exec1 op bs \<le> length bs\<close> a_2 by auto
  next
    case Incr
  
    then show "T_exec (op # ops) bs \<le> length (op # ops) * length bs" sorry
  qed
qed

 *) 


(*fun oplist :: "nat \<Rightarrow> op list"  where
  "oplist 0 = []"
| "oplist (Suc 0) = [Incr]"
| "oplist (Suc (Suc n)) = (if n mod 2 = 0 then Incr#Decr#(oplist n) else Decr#Incr#(oplist n))"
*)

fun oplist :: "nat \<Rightarrow> op list"  where
  "oplist 0 = []"
| "oplist (Suc 0) = [Incr]"
| "oplist (Suc (Suc n)) = Incr#Decr#(oplist n)"



(* "oplist n = (if n mod 2 = 1 then Incr#(oplist (n-1)) else Decr#(oplist (n-1)))" *)


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

lemma "k = 1 \<Longrightarrow> decr [False] = [True]" using decr oops


lemma c2: "k = 1 \<Longrightarrow> length (oplist n)  \<le> 2* T_exec (oplist n) [False]" 
proof(induction n rule: oplist.induct)
  case 1
  then show ?case 
    by simp
next
  case 2
  then show ?case
    by simp
next 
  case (3 n)
  assume a_1: "k = 1 \<Longrightarrow> length (oplist n) \<le> 2 * T_exec (oplist n) [False]"
  assume a_2: "k = 1"

  have ih: "length (oplist n) \<le> 2 * T_exec (oplist n) [False]" using a_2 a_1 
    by simp
  have uff: "T_exec (oplist (Suc (Suc n))) [False] = T_exec (Incr#Decr#(oplist n)) [False]"
    by simp
  have ufff: "... = T_exec1 Incr [False] +  T_exec (Decr#(oplist n)) (exec1 Incr [False])" 
      by simp
   have "... = 1 + T_exec (Decr#(oplist n)) [True]" 
      by simp
   have "... = 2 + T_exec (oplist n) [False]" using decr a_2
      by simp 
  then show "length (oplist (Suc (Suc n))) \<le> 2 * T_exec (oplist (Suc (Suc n))) [False]"
    using ih by fastforce 
 qed

(*
next
  case (3 n)
  assume a_1: "n mod 2 = 0 \<Longrightarrow> k = 1 \<Longrightarrow>  length (oplist n) \<le> 2 * T_exec (oplist n) [False]"
  assume a_2: "n mod 2 \<noteq> 0 \<Longrightarrow> k = 1  \<Longrightarrow>  length (oplist n) \<le> 2 * T_exec (oplist n) [False]"
  assume a_3: "k = 1"
  then show " length (oplist (Suc (Suc n))) \<le> 2 * T_exec (oplist (Suc (Suc n))) [False]" 
  proof(cases "n mod 2 = 0")
    case True
    then have ih: "length (oplist n) \<le> 2 * T_exec (oplist n) [False]" using a_1 a_3
      by simp
    then have uf: " (oplist (Suc (Suc n))) = Incr#Decr#(oplist n)" using True 
      by simp
    have "length (oplist (Suc (Suc n))) =  (Suc (Suc n))  " using op_len 
      by simp

    have uff: "T_exec (oplist (Suc (Suc n))) [False] = T_exec (Incr#Decr#(oplist n)) [False] " using uf 
      by simp
    have ufff: "... = T_exec1 Incr [False] +  T_exec (Decr#(oplist n)) (exec1 Incr [False])" 
      by simp
    have "... = 1 + T_exec (Decr#(oplist n)) [True]" 
      by simp
    have "... = 1 +  T_exec1 Decr [True] + T_exec (oplist n) (exec1 Decr [True])" 
      by simp
    have "... = 2 + T_exec (oplist n) [False]" using decr a_3 
      by simp 

    then show "length (oplist (Suc (Suc n))) \<le> 2 * T_exec (oplist (Suc (Suc n))) [False]" 
      using ih uff by auto
  next
    case False
    then have ih: "length (oplist n) \<le> 2 * T_exec (oplist n) [False]" using a_2 a_3
      by simp
    then have uf: " (oplist (Suc (Suc n))) = Decr#Incr#(oplist n)" using False 
      by simp

    have uff: "T_exec (oplist (Suc (Suc n))) [False] = T_exec (Decr#Incr#(oplist n)) [False] " using uf 
      by simp
    then show ?thesis sorry
  qed
qed
*)

lemma "x # y # xs = bs0 \<Longrightarrow> xs = bs0 \<Longrightarrow> False" 
  using bs0_def k 
  by force

theorem inc_dec_seq_lbound: "length (oplist n) * k \<le> 2 * (T_exec (oplist n)  bs0)" 
proof(induction "oplist n" arbitrary:  rule: induct_list012)
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
    have "length bs0 = k" using bs0_def 
      by simp
    have " T_exec [Incr] bs0 = T_incr bs0" 
      by simp
   


    show "k \<le> 2 * T_exec [Incr] bs0" sorry


  qed
    
    
     

  then show "length (oplist n) * k \<le> 2 * T_exec (oplist n) bs0" using op 
    by simp
  proof(inud
next
  case (multi x y xs)
  then show ?case sorry
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