theory Submission_dirty
  imports Defs
begin


fun b_isin :: "nat \<Rightarrow> bool list \<Rightarrow> bool" where 
  "b_isin 0 (y#ys) = (if y then True else False)"
 | "b_isin x [] = False"
| "b_isin (Suc x) (y#ys) = b_isin x ys"


fun bv_isin :: " bool list \<Rightarrow> nat \<Rightarrow> bool" where 
"bv_isin [] x = False"
| "bv_isin (y#ys) x = (if x = 0 then y else bv_isin ys  (x-1))"



value "bv_isin ([False,False,False,True,True]) (4::nat)"

fun bv_insert :: "nat \<Rightarrow> bool list \<Rightarrow> bool list" where 
"bv_insert 0 [] = [True]"
| "bv_insert (Suc x) [] = False#(bv_insert x [])"
| "bv_insert x (y#ys) = (if x=0 then True#ys else y#(bv_insert (x-1) ys))"


fun bv_set  :: "nat \<Rightarrow> bool list \<Rightarrow> nat set" where
  "bv_set x [] = {}"
| "bv_set x (y#ys) = (if y then {x} \<union> bv_set (Suc x) ys else bv_set (Suc x) ys)"


fun set_bvv :: "bool list \<Rightarrow> nat set" where 
   "set_bvv xs = bv_set 0 xs"



(* composed functions *) 

fun bv_isin_c ::  "bool list \<Rightarrow> nat \<Rightarrow> bool" where 
"bv_isin_c xs x = (if x \<ge> length xs then False else (xs!x))"



fun bv_insert_h :: "nat \<Rightarrow> bool list" where 
"bv_insert_h 0 = [True]"
| "bv_insert_h (Suc x) = False #(bv_insert_h x)"


fun bv_insert_c ::  "nat \<Rightarrow> bool list \<Rightarrow> bool list" where 
 "bv_insert_c x xs = (if x < length xs then  xs[x := True] else xs@(bv_insert_h (x-length xs)))"

value "bv_insert_c  (9::nat) ([False,False,False,True,True])"

fun bv_invar :: "bool list \<Rightarrow> bool " where 
 "bv_invar xs =  (xs = [] \<or> last xs = True)"

(* TODO  ensure invariant *) 
fun bv_delete_c ::  "nat \<Rightarrow> bool list \<Rightarrow> bool list" where 
 "bv_delete_c x xs = (if x = (length xs) - 1 then  rev (dropWhile (\<lambda>k. k = False) (rev (butlast xs))) else  xs[x := False])"

value "bv_delete_c 1 [False,True,False,False,True]"

fun set_bv :: "bv \<Rightarrow> nat set" 
  where "set_bv bs = { i. i<length bs \<and> bs!i }"


(* new insert *) 

find_consts name: replicate

fun bv_insert_n :: "nat \<Rightarrow> bool list \<Rightarrow> bool list" where 
"bv_insert_n x xs = (if x < length xs then xs[x := True] else xs@(replicate (x - length xs) False)@[True])"


declare [[names_short]]




lemma insert_h_1: "last (bv_insert_h x) = True" 
  apply(induction x)
  apply(simp)
  using Submission_dirty.bv_insert_h.elims by auto

lemma insert_h_2: "\<forall> y \<in> set (butlast (bv_insert_h x)). y = False" 
  apply(induction x)
  apply(simp)
  using Submission_dirty.bv_insert_h.elims by auto

lemma insert_h_3: "length (bv_insert_h x) = Suc x"
  apply(induction x)
  apply(simp)
  using Submission_dirty.bv_insert_h.elims by auto

lemma delete_1: "bv_invar s \<Longrightarrow> (bv_delete_c x s) = [] \<or> last (bv_delete_c x s) = True"
  apply(induction s arbitrary: x )
  apply(simp)
  apply(auto)
  apply (simp add: Nat.nat.split_sels(2))
  apply (metis List.last.simps dropWhile_append3 hd_Nil_eq_last hd_dropWhile last_appendR last_rev)
  apply (metis dropWhile_eq_Nil_conv hd_dropWhile last_rev set_rev)
  by (metis List.butlast.simps(2) List.last.simps List.list.discI List.list_update.simps(2) One_nat_def Suc_pred last_list_update length_Cons length_butlast length_greater_0_conv)


lemma set_split: " x \<ge> length s \<Longrightarrow> set_bv ( s@(bv_insert_h (x-length s))) = set_bv s \<union> set_bv (bv_insert_h x )" 
  sorry

lemma set_insert_h: "set_bv (bv_insert_h x) = {x}" 
proof-
  have a: "last (bv_insert_h x) = True" using insert_h_1 try0
    by simp
  have b: "\<forall> y \<in> set (butlast (bv_insert_h x)). y = False" using insert_h_2 
    by blast
  have c: "length (bv_insert_h x) = Suc x" using insert_h_3 
    by simp
  from a c have "x \<in> set_bv (bv_insert_h x)"
    by (metis (no_types, lifting) Nat.nat.simps(3) One_nat_def Submission.set_bv.simps diff_Suc_1' last_conv_nth length_0_conv lessI mem_Collect_eq)
  from b c have "\<forall> y < x. y \<notin> set_bv (bv_insert_h x)" sorry 
  show "?thesis" sorry
qed



lemma h1: "length xs \<ge> 1 \<Longrightarrow> last xs = True \<Longrightarrow> (length xs -1) \<in> set_bv xs"
  using Orderings.preorder_class.dual_order.strict_trans1 last_conv_nth by auto


lemma set_bv_split: "set_bv (xs@(replicate x False)@[True]) = set_bv xs \<union> {length xs + x}"
proof- 
  have 1: "(length xs + x) \<in> set_bv (xs@(replicate x False)@[True]) " using h1[of "(xs@(replicate x False)@[True])"] 
    by simp
  have 2:  "\<forall> i. i \<ge> length xs \<and> i < length xs + x \<and> i \<notin> set_bv  (xs@(replicate x False)@[True])" sorry 
  show "set_bv (xs@(replicate x False)@[True]) = set_bv xs \<union> {length xs + x}" using 1 2 
    by blast
qed




lemma delete_2:
  assumes "x = length s-1 \<and> y <length s \<and> s!y  \<and> y<x"
  shows "length (rev (dropWhile (\<lambda>k. k = False) (rev (butlast s)))) > y" 
proof-
  have "y < length s -1" using assms
    by simp
  obtain n where "n = length s - length (rev (dropWhile (\<lambda>k. k = False) (rev (butlast s))))" try0
    by simp
  let ?rev_len = "length  (rev (dropWhile (\<lambda>k. k = False) (rev (butlast s))))"
  obtain zs where zs_prop: "(rev (dropWhile (\<lambda>k. k = False) (rev (butlast s))))@zs = s"
    by (metis append_assoc append_take_drop_id butlast_conv_take rev_append rev_rev_ident takeWhile_dropWhile_id) 
  have "z \<ge> ?rev_len \<and> z < length s -1 \<Longrightarrow> s!z = False" using assms sorry 
   (*obtain z where "z < length s \<and> z \<noteq> x \<and> s!z \<and> (\<nexists> zz. zz > z \<and> zz < length s \<and> zz \<noteq> x \<and> s!zz)" using assms sorry *)
qed


interpretation bv_set: Set \<comment> \<open>Your parameters here\<close> 
  where empty = Nil and isin = bv_isin_c 
  and insert = bv_insert_n and delete = bv_delete_c
  and set = set_bv  and invar = bv_invar 
proof(unfold_locales,goal_cases)
  case 1
  then show ?case
    by simp 
next
  case (2 s x)
  then show ?case 
    by simp
next
  case (3 s x)
  then show "set_bv (bv_insert_n x s) = set_bv s \<union> {x}" 
  proof(cases "x<length s")
    case True
    assume "x < length s"
    then have c: "bv_insert_n x s =  s[x := True]" 
      by simp
    have a: "s[x := True]!x" using True
      by simp
    from a True have b: "x \<in> { i. i<length (s[x := True]) \<and> (s[x := True])!i } "
      by simp
    have "set_bv (bv_insert_n x s) = set_bv (s[x := True])" using c 
      by simp
    also have "... =  { i. i<length (s[x := True]) \<and> (s[x := True])!i } " using True
      by simp
    also have "... = { i. i<length (s[x := True]) \<and> (s[x := True])!i } \<union> {x} " using b 
      by blast
    also have "... = { i. i<length s \<and> (s)!i } \<union> {x} "  using True b 
      by force
    also have "... = set_bv s \<union> {x} "
      by simp
    finally show "set_bv (bv_insert_n x s) = set_bv s \<union> {x}"
      by simp
  next
    case False
    assume "\<not> x < length s"
    then have c: "bv_insert_n x s = s@(replicate (x-length s) False) @ [True]" 
      by simp
    then have "set_bv (bv_insert_n x s) = set_bv (s@(replicate (x-length s) False) @ [True])"
      by simp
    then show "set_bv (bv_insert_n x s) = set_bv s \<union> {x}" using set_bv_split[of "s" "x - length s"] False
      by simp
  qed
next
  case (4 s x)
  case (4 s x)
  then show "set_bv (bv_delete_c x s) = set_bv s - {x}" 
  proof(cases "x = length s - 1")
    case tr: True
    assume "x = length s - 1"
    then have del_def : "bv_delete_c x s = rev (dropWhile (\<lambda>k. k = False) (rev (butlast s)))"
      by simp
    have a: "x \<notin> set_bv (rev (dropWhile (\<lambda>k. k = False) (rev (butlast s))))" using tr 
      by (metis (no_types, lifting) Submission_dirty.set_bv.simps length_butlast length_dropWhile_le length_rev linorder_not_le mem_Collect_eq)
    have b:  "y \<in> set_bv  (rev (dropWhile (\<lambda>k. k = False) (rev (butlast s)))) \<longleftrightarrow> y \<in> set_bv s"  if "y \<noteq> x" for y 
    proof 
     assume ass_1: "y \<in> set_bv (rev (dropWhile (\<lambda>k. k = False) (rev (butlast s))))"
        have d: "\<exists> zs. (rev (dropWhile (\<lambda>k. k = False) (rev (butlast s))))@zs = s" 
        by (metis append_assoc append_take_drop_id butlast_conv_take rev_append rev_rev_ident takeWhile_dropWhile_id)  
      then have yyy: "y \<in> set_bv (rev (dropWhile (\<lambda>k. k = False) (rev (butlast s)))) \<Longrightarrow> y \<in> set_bv s" 
        by (smt (verit, ccfv_SIG) List.butlast.simps(1) List.list.size(3) Nil_is_append_conv Nil_is_rev_conv Orderings.preorder_class.dual_order.strict_trans1 Submission_dirty.set_bv.simps append_butlast_last_id append_eq_conv_conj append_self_conv drop_all length_rev mem_Collect_eq nle_le nth_append zero_order(3))
      then show "y \<in> set_bv s" using ass_1 
        by simp 
    next 
      assume ass_1: "y \<in> set_bv s"
      have "y \<noteq> x"
        by (simp add: that)
      have "x = length s -1"
        by (simp add: tr)
      have d: "\<exists> zs. (rev (dropWhile (\<lambda>k. k = False) (rev (butlast s))))@zs = s" 
        by (metis append_assoc append_take_drop_id butlast_conv_take rev_append rev_rev_ident takeWhile_dropWhile_id)      
      then show  "y \<in> set_bv (rev (dropWhile (\<lambda>k. k = False) (rev (butlast s))))" 
      proof(cases "y < length  (rev (dropWhile (\<lambda>k. k = False) (rev (butlast s))))")
        case True
        then show ?thesis using d 
          by (metis (no_types, lifting) Submission_dirty.set_bv.simps ass_1 mem_Collect_eq nth_append)
      next
        case False
        assume " \<not> y < length (rev (dropWhile (\<lambda>k. k = False) (rev (butlast s))))"
        then have d:  "y \<ge> length  (rev (dropWhile (\<lambda>k. k = False) (rev (butlast s))))" try0
          by simp
        have e: "\<exists> zs. (rev (dropWhile (\<lambda>k. k = False) (rev (butlast s))))@zs = s" 
          by (metis append_assoc append_take_drop_id butlast_conv_take rev_append rev_rev_ident takeWhile_dropWhile_id) 
        have a: "x = length s -1" using tr 
          by simp
        then have b: "y < x" using that
          by (metis (no_types, lifting) List.list.size(3) One_nat_def Submission_dirty.set_bv.simps Suc_pred ass_1 le_neq_implies_less length_greater_0_conv less_Suc_eq_le mem_Collect_eq not_less_zero)
        have "y \<in> set_bv s" using ass_1
          by simp
        then have "y<length s \<and> s!y" 
          by simp
        then have c: "length (rev (dropWhile (\<lambda>k. k = False) (rev (butlast s)))) > y" using a b delete_2 sorry 
        show "y \<in> set_bv (rev (dropWhile (\<lambda>k. k = False) (rev (butlast s))))" using c d try0
          by simp
      qed
    qed
(*
    proof(rule ccontr)
      assume c: "(y \<in> set_bv (rev (dropWhile (\<lambda>k. k = False) (rev (butlast s))))) \<noteq> (y \<in> set_bv s)"
      then have "\<exists> yy. (yy \<in> set_bv (rev (dropWhile (\<lambda>k. k = False) (rev (butlast s))))) \<noteq> (yy \<in> set_bv s)" 
        by blast
      have d: "\<exists> zs. (rev (dropWhile (\<lambda>k. k = False) (rev (butlast s))))@zs = s" 
        by (metis append_assoc append_take_drop_id butlast_conv_take rev_append rev_rev_ident takeWhile_dropWhile_id)  
      then have "yy \<in> set_bv (rev (dropWhile (\<lambda>k. k = False) (rev (butlast s)))) \<Longrightarrow> yy \<in> set_bv s" 
        by (smt (verit, ccfv_SIG) List.butlast.simps(1) List.list.size(3) Nil_is_append_conv Nil_is_rev_conv Orderings.preorder_class.dual_order.strict_trans1 Submission.set_bv.simps append_butlast_last_id append_eq_conv_conj append_self_conv drop_all length_rev mem_Collect_eq nle_le nth_append zero_order(3))
      show "False" sorry
    qed 
*) 
(*
    proof
      assume ass_1: "y \<in> set_bv (rev (dropWhile (\<lambda>k. k = False) (rev (butlast s))))"
      have "length (rev (dropWhile (\<lambda>k. k = False) (rev (butlast s)))) < length s"
        by (smt (verit, best) List.list.size(3) One_nat_def Submission.set_bv.simps Suc_pred ass_1 diff_is_0_eq' length_butlast length_dropWhile_le length_greater_0_conv length_rev lessI less_imp_diff_less mem_Collect_eq nat_less_le order_less_trans)
      then show "y \<in> set_bv s" using tr sorry 
    next 
      assume  "y \<in> set_bv s"
      show  "y \<in> set_bv (rev (dropWhile (\<lambda>k. k = False) (rev (butlast s))))" sorry 
    qed
*)
    then show "set_bv (bv_delete_c x s) = set_bv s - {x}" using del_def a b
      by force
  next
    case neq: False
    assume "\<not> x = length s - 1"
    then show "set_bv (bv_delete_c x s) = set_bv s - {x}" 
    proof(cases "x < length s - 1")
      case True
      assume "x < length s - 1"
      then have del_def: "bv_delete_c x s =  s[x := False] "
        by simp
      have " \<not> s[x := False] ! x" using True 
        by simp
      then have a: "x \<notin> set_bv (bv_delete_c x s)" using del_def
        by simp
      have b: "y \<in> set_bv (bv_delete_c x s) \<longleftrightarrow> y \<in> set_bv s"  if "y \<noteq> x" for y
        using del_def that by auto
      then show "set_bv (bv_delete_c x s) = set_bv s - {x}" using a b 
        by fast
    next
      case False
      then show ?thesis
        using neq by force
    qed
  qed
next
  case 5
  then show ?case 
    by simp
next
  case (6 s x)
  then show ?case 
    by (metis List.list.size(3) Submission_dirty.bv_insert_n.elims Submission_dirty.bv_invar.elims(2) Submission.bv_invar.elims(3) last_append last_list_update last_snoc not_less_zero) 
next
  case (7 s x)
  then show ?case using delete_1
    by simp
qed






fun ibst :: "'a::linorder itree \<Rightarrow> bool"  where
  "ibst _ = False"

fun delete :: "int \<Rightarrow> int itree \<Rightarrow> int itree"  where
  "delete _ _ = iLeaf"

lemma delete_set_minus: "ibst t \<Longrightarrow> set_itree2 (delete x t) = (set_itree2 t) - {x}"
  sorry

lemma ibst_delete: "ibst t \<Longrightarrow> ibst (delete x t)"
  sorry

end