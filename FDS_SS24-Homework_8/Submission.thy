theory Submission
  imports Defs
begin

(* composed functions *) 

fun bv_isin_c ::  "bool list \<Rightarrow> nat \<Rightarrow> bool" where 
"bv_isin_c xs x = (if x \<ge> length xs then False else (xs!x))"

fun bv_invar :: "bool list \<Rightarrow> bool " where 
 "bv_invar xs =  (xs = [] \<or> last xs = True)"

(* new insert *) 

fun bv_insert_n :: "nat \<Rightarrow> bool list \<Rightarrow> bool list" where 
"bv_insert_n x xs = (if x < length xs then xs[x := True] else xs@(replicate (x - length xs) False)@[True])"


(* new delete *)

fun bv_delete_n :: "nat \<Rightarrow> bool list \<Rightarrow> bool list" where 
"bv_delete_n x xs = rev (dropWhile (\<lambda>k. k = False) (rev  (xs[x := False])))"

declare [[names_short]]

(* current helpers *) 

lemma delete_invar:
  assumes  "bv_invar s"
  shows "bv_invar (bv_delete_n x s)"
proof-  
  have "rev (dropWhile (\<lambda>k. k = False) (rev ys)) =  [] \<or> last (rev (dropWhile (\<lambda>k. k = False) (rev ys))) = True " for ys 
    using hd_dropWhile last_rev by blast
  then show "?thesis"
    by simp
qed


lemma h1: "length xs \<ge> 1 \<Longrightarrow> last xs = True \<Longrightarrow> (length xs -1) \<in> set_bv xs" unfolding set_bv_def
  using Orderings.preorder_class.dual_order.strict_trans1 last_conv_nth by auto

lemma set_bv_split: "set_bv (xs@(replicate x False)@[True]) = set_bv xs \<union> {length xs + x}"
proof- 
  have 1: "(length xs + x) \<in> set_bv (xs@(replicate x False)@[True]) " using h1[of "(xs@(replicate x False)@[True])"] 
    by simp
  have 5: "i = length xs + x \<Longrightarrow> (xs@(replicate x False)@[True])!i" for i using 1 unfolding set_bv_def
    by simp
  have 6: "i \<ge> length xs \<and> i < length xs + x \<Longrightarrow> \<not> (xs@(replicate x False)@[True])!i" for i 
    by (simp add: less_diff_conv2 nth_append)

  have "set_bv (xs@(replicate x False)@[True]) =  { i. i<length (xs@(replicate x False)@[True]) \<and> (xs@(replicate x False)@[True])!i }" unfolding set_bv_def
    by simp
  also have "... = {i. i< length xs \<and> (xs@(replicate x False)@[True])!i} \<union>  {i. i\<ge> length xs \<and> i < length (xs@(replicate x False)@[True]) \<and>  (xs@(replicate x False)@[True])!i}"
    by force
  also  have "... = {i. i< length xs \<and> xs!i} \<union>  {i. i\<ge> length xs \<and> i < length (xs@(replicate x False)@[True]) \<and>  (xs@(replicate x False)@[True])!i}"
    by (metis nth_append)
  also have "... = set_bv xs  \<union>  {i. i\<ge> length xs \<and> i < length (xs@(replicate x False)@[True]) \<and>  (xs@(replicate x False)@[True])!i}" unfolding set_bv_def
    by simp
  also have "... = set_bv xs \<union> {i. i\<ge> length xs \<and> i <  length xs + x + 1  \<and>  (xs@(replicate x False)@[True])!i}" 
    by simp
  also have "... = set_bv xs \<union> {i. i\<ge> length xs \<and> i <  length xs + x  \<and>  (xs@(replicate x False)@[True])!i} \<union>  {i. i = length xs + x  \<and>  (xs@(replicate x False)@[True])!i} " 
    by auto
  also  have "... = set_bv xs \<union> {i. i\<ge> length xs \<and> i <  length xs + x  \<and>  (xs@(replicate x False)@[True])!i} \<union> {length xs + x}" using 5 
  proof -
    have "(xs @ replicate x False @ [True]) ! (length xs + x)"
      by (metis length_replicate nth_append_length nth_append_length_plus)
    then show ?thesis
      by fastforce
  qed
  also  have "... = set_bv xs \<union> {length xs + x}" 
  proof - 
    have "i \<ge> length xs \<and> i < length xs + x \<Longrightarrow> \<not> (xs@(replicate x False)@[True])!i" for i using 6 
      by (simp add: less_diff_conv2 nth_append)
    then have "\<nexists> i. i \<ge> length xs \<and> i < length xs + x \<and> (xs@(replicate x False)@[True])!i"
      by (simp add: less_diff_conv2 nth_append)
    then have " {i. i\<ge> length xs \<and> i <  length xs + x  \<and>  (xs@(replicate x False)@[True])!i} = {}"
      by simp
    then show "?thesis"
      by blast
  qed 
  finally show "set_bv (xs@(replicate x False)@[True]) = set_bv xs \<union> {length xs + x}" 
    by simp
qed


lemma set_bv_all_false: 
  assumes  "zs = [] \<or> (\<forall> x \<in> set zs. x = False)" 
  shows "set_bv (ys@zs) = set_bv ys"
proof(cases "zs = []")
  case True
  then show ?thesis try0
    by simp
next
  case False
  have x: "(\<forall> x \<in> set zs. x = False)" using assms 
    by auto
  have y: "i \<ge> length ys \<and> i < length (ys@zs) \<Longrightarrow> (ys@zs)!i = False" for i using x
    by (metis in_set_conv_nth leD le_add_diff_inverse length_append nat_add_left_cancel_less nth_append)
  have " set_bv (ys @ zs) = {i. i< length (ys@zs) \<and> (ys@zs)!i}" unfolding set_bv_def
    by simp 
  also  have "... =  {i. i< length ys \<and> (ys @ zs)!i} \<union> {i. i\<ge> length ys \<and> i < length (ys@zs) \<and>(ys@zs)!i } " 
    by auto
  also have "... =  {i. i< length ys \<and> (ys)!i} \<union> {i. i\<ge> length ys \<and> i < length (ys@zs) \<and>(ys@zs)!i } " 
    by (metis nth_append)
  also have "... = set_bv ys \<union>  {i. i\<ge> length ys \<and> i < length (ys@zs) \<and>(ys@zs)!i }" unfolding set_bv_def
    by simp
  also have "... = set_bv ys" using y
    by blast
  finally show " set_bv (ys @ zs) = set_bv ys" 
    by simp
qed



lemma set_bv_rev: " set_bv (rev (dropWhile (\<lambda>k. k = False) (rev xs))) = set_bv xs" 
proof - 
  obtain zs  where zs_prop:   " (rev (dropWhile (\<lambda>k. k = False) (rev xs))) @ zs = xs "
    by (metis rev_append rev_rev_ident takeWhile_dropWhile_id)
  have zs_all_false: "zs = [] \<or> (\<forall> x \<in> set zs. x = False)" using zs_prop 
    by (smt (verit, ccfv_SIG) append_self_conv2 dropWhile_append1 dropWhile_eq_Nil_conv rev_append rev_rev_ident set_rev) 
  let ?ys =  "(rev (dropWhile (\<lambda>k. k = False) (rev xs)))"
  have "set_bv (?ys@zs) = set_bv ?ys" using set_bv_all_false zs_all_false 
    by blast
  then show "?thesis" using zs_prop
    by fastforce
qed

(*
lemma delete_whole: "set_bv (bv_delete_n x xs) = set_bv (xs) - {x}"
proof(cases "x < length xs")
  case True
  have "set_bv (bv_delete_n x xs) = set_bv (rev (dropWhile (\<lambda>k. k = False) (rev  (xs[x := False]))))"
    by simp
  also have "... = set_bv  (xs[x := False])" using set_bv_rev
    by simp
  also have "... = { i. i<length (xs[x := False]) \<and> (xs[x := False])!i }" 
    by simp
  also have "... = {i. i= x \<and> (xs[x := False])!i} \<union> {i. i \<noteq> x \<and> i < length xs \<and>  (xs[x := False])!i}" using True 
    by auto
  also  have "... = {i. i \<noteq> x \<and> i < length xs \<and>  (xs[x := False])!i}" using True
    by auto
  also have "... = set_bv xs - {x}" using True
    by force
  finally show " set_bv (bv_delete_n x xs) = set_bv xs - {x}"
    by simp
next
  case False
  then show ?thesis 
    using set_bv_rev by auto
qed 
*)

(* TODO ask about if for syntax *)

interpretation bv_set: Set \<comment> \<open>Your parameters here\<close> 
  where empty = Nil and isin = bv_isin_c 
  and insert = bv_insert_n and delete = bv_delete_n
  and set = set_bv  and invar = bv_invar 
proof(unfold_locales,goal_cases)
  case 1
  then show ?case unfolding set_bv_def
    by simp 
next
  case (2 s x)
  then show ?case unfolding set_bv_def
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
    also have "... =  { i. i<length (s[x := True]) \<and> (s[x := True])!i } " using True unfolding set_bv_def
      by simp
    also have "... = { i. i<length (s[x := True]) \<and> (s[x := True])!i } \<union> {x} " using b 
      by blast
    also have "... = { i. i<length s \<and> (s)!i } \<union> {x} "  using True b 
      by force
    also have "... = set_bv s \<union> {x} " unfolding set_bv_def
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
  then show "set_bv (bv_delete_n x s) = set_bv s - {x}"
  proof(cases "x < length s")
  case True
  have "set_bv (bv_delete_n x s) = set_bv (rev (dropWhile (\<lambda>k. k = False) (rev  (s[x := False]))))"
    by simp
  also have "... = set_bv  (s[x := False])" using set_bv_rev
    by simp
  also have "... = { i. i<length (s[x := False]) \<and> (s[x := False])!i }" unfolding set_bv_def 
    by simp
  also have "... = {i. i= x \<and> (s[x := False])!i} \<union> {i. i \<noteq> x \<and> i < length s \<and>  (s[x := False])!i}" using True 
    by auto
  also  have "... = {i. i \<noteq> x \<and> i < length s \<and>  (s[x := False])!i}" using True
    by auto
  also have "... = set_bv s - {x}" using True unfolding set_bv_def
    by force
  finally show " set_bv (bv_delete_n x s) = set_bv s - {x}"
    by simp
next
  case False
  then show ?thesis using set_bv_rev unfolding set_bv_def 
    by auto
qed
next
case 5
  then show ?case 
    by simp
next
  case (6 s x)
  then show ?case 
    by (metis List.list.size(3) Submission.bv_insert_n.elims Submission.bv_invar.elims(2) Submission.bv_invar.elims(3) last_append last_list_update last_snoc not_less_zero) 
next
  case (7 s x)
  then show ?case using delete_invar
    by simp
qed




fun ibst :: "'a::linorder itree \<Rightarrow> bool"  where
  "ibst iLeaf  = True"
| "ibst (iNode l (a,b) r) = ((a \<le> b) \<and> (\<forall>x \<in> set_itree3 l. a > (snd x)) \<and> (\<forall>x \<in> set_itree3 r. b < (fst x)) \<and> ibst l \<and> ibst r)"


fun split_min :: "int itree \<Rightarrow> ((int \<times> int) \<times> int itree)" where 
 "split_min iLeaf = undefined"
| "split_min (iNode l (a,b) r) = (if l = iLeaf then ((a,b),r) 
 else let ((x,y), l') = split_min l in ((x,y),(iNode l' (a,b) r)))"

value "split_min (iNode (iNode iLeaf (2,4) iLeaf) (5,6) iLeaf)"

fun insert_min :: "int itree \<Rightarrow> (int \<times> int) \<Rightarrow> int itree" where 
"insert_min iLeaf (a,b) = (iNode iLeaf (a,b) iLeaf)"
| "insert_min (iNode l x r) (a,b) = (iNode (insert_min l (a,b)) x r)"


value "insert_min (iNode (iNode iLeaf (3,5) iLeaf) (7,11) iLeaf) (1,2)"

lemma insert_min_set_itree2: "set_itree2 (insert_min r (x+1,b)) = set_itree2 r \<union> {x+1..b}"
  apply(induction r)
  apply(simp)
  apply(auto)
  done 


fun joinn :: "int itree \<Rightarrow> int itree \<Rightarrow> int itree" where
  "joinn t iLeaf = t" |
  "joinn iLeaf t = t" |
  "joinn (iNode l1 (a1,b1) r1) (iNode l2 (a2,b2) r2) =
   (case joinn r1 l2 of
     iLeaf \<Rightarrow> iNode l1 (a1,b1) (iNode iLeaf (a2,b2) r2) |
     iNode l (a',b') r \<Rightarrow> iNode (iNode l1 (a1,b1) l) (a',b') (iNode r (a2,b2) r2))"


lemma joinn_set2_same: "ibst (iNode x (a,b) y) \<Longrightarrow> set_itree2 (joinn x y) = set_itree2 x \<union> set_itree2 y" sorry 

lemma joinn_set3_same: "ibst x \<Longrightarrow> ibst y \<Longrightarrow> set_itree3 (joinn x y) = set_itree3 x \<union> set_itree3 y"  sorry 


lemma joinn_set_itree2: 
   "set_itree2 (joinn l r) = set_itree2 l \<union> set_itree2 r " 
proof(induction l r rule: joinn.induct)
  case (1 t)
  then show ?case 
    by simp
next
  case (2 v va vb)
  then show ?case 
    by simp
next
  case (3 l1 a1 b1 r1 l2 a2 b2 r2)
  assume ih: "set_itree2 (joinn r1 l2) = set_itree2 r1 \<union> set_itree2 l2"
  then show " set_itree2 (joinn (iNode l1 (a1, b1) r1) (iNode l2 (a2, b2) r2)) = set_itree2 (iNode l1 (a1, b1) r1) \<union> set_itree2 (iNode l2 (a2, b2) r2)"
  proof(cases "joinn r1 l2")
    case iLeaf
    then show ?thesis 
      using "3" by auto
  next
    case (iNode l x' r)
    obtain a'  b' where a_b_prop: "x' = (a',b')" 
      by force
    have "set_itree2 (joinn (iNode l1 (a1, b1) r1) (iNode l2 (a2, b2) r2)) = set_itree2 (iNode (iNode l1 (a1,b1) l) (a',b') (iNode r (a2,b2) r2))" using iNode 3 a_b_prop
      by simp
    also have "...  = (set_itree2  ( (iNode l1 (a1,b1) l))) \<union> {a'..b'} \<union> (set_itree2 (iNode r (a2,b2) r2)) " 
      by auto 
    also have "... = set_itree2 l1 \<union> {a1..b1} \<union> set_itree2 l  \<union> {a'..b'} \<union> (set_itree2 (iNode r (a2,b2) r2))" 
      by force
    also have "... = set_itree2 l1 \<union> {a1..b1} \<union> set_itree2 l  \<union> {a'..b'} \<union> set_itree2 r \<union> {a2..b2} \<union> set_itree2 r2" 
      by auto
    also have "... = (set_itree2 l  \<union>  {a'..b'} \<union> set_itree2 r)  \<union> set_itree2 l1 \<union> {a1..b1} \<union>  {a2..b2} \<union> set_itree2 r2 " try0
      by blast
    also have "... = set_itree2 (iNode l (a',b') r) \<union> set_itree2 l1 \<union> {a1..b1} \<union>  {a2..b2} \<union> set_itree2 r2 " 
      by auto
    also have "... = set_itree2 (joinn r1 l2) \<union> set_itree2 l1 \<union> {a1..b1} \<union>  {a2..b2} \<union> set_itree2 r2 " using iNode a_b_prop 
      by simp
    also have "... =  set_itree2 r1 \<union> set_itree2 l2 \<union> set_itree2 l1 \<union> {a1..b1} \<union>  {a2..b2} \<union> set_itree2 r2 " using ih 
      by simp
    also have "... = set_itree2 (iNode l1 (a1, b1) r1) \<union> set_itree2 (iNode l2 (a2, b2) r2) " 
      by auto
    finally show "set_itree2 (joinn (iNode l1 (a1, b1) r1) (iNode l2 (a2, b2) r2)) = set_itree2 (iNode l1 (a1, b1) r1) \<union> set_itree2 (iNode l2 (a2, b2) r2)"
      by simp
  qed
qed
   

lemma joinn_ibst: "ibst (iNode x (a,b) y)  \<Longrightarrow> ibst (joinn x y)" 
 proof(induction x y rule: joinn.induct)
    case (1 t)
    then show ?case 
      by simp
  next
    case (2 v va vb)
    then show ?case
      by simp
  next
    case (3 l1 a1 b1 r1 l2 a2 b2 r2)
    (* ibst (iNode r1 (a, b) l2) \<Longrightarrow> ibst (joinn r1 l2)  *)
    (* ibst (iNode (iNode l1 (a1, b1) r1) (a, b) (iNode l2 (a2, b2) r2)) *)
    then show "ibst (joinn (iNode l1 (a1, b1) r1) (iNode l2 (a2, b2) r2))" sorry
  qed


fun delete :: "int \<Rightarrow> int itree \<Rightarrow> int itree"  where
  "delete x iLeaf  = iLeaf"
| "delete x (iNode l (a,b) r) = ( 
   if x < a then (iNode (delete x l) (a,b) r) 
   else if x > b then  (iNode l (a,b) (delete x r)) 
   else if x = a \<and> a = b  then (joinn l r)
   else if x = a then (iNode l (a + 1, b) r)
   else if x = b then (iNode l (a, b-1) r) 
   else (iNode l (a,x-1) (insert_min r (x+1,b)))
)                          
"


(*  (if r = iLeaf then l else let ((a',b'),r') = split_min r in (iNode l (a',b') r')) *) 


value "delete 3 (iNode (iNode (iNode iLeaf (0, 0) iLeaf) (1, 1) (iNode iLeaf (2, 4) iLeaf )) ( (5), 6) (iLeaf ))

   = iNode (iNode (iNode iLeaf (0, 0) iLeaf) (1, 1) (iNode iLeaf (2, 2) (iNode iLeaf (4, 4) iLeaf))) (5, 6) iLeaf"


value  "delete 1 (iNode (iNode (iNode iLeaf (0, 0) iLeaf) (1, 1) (iNode iLeaf (2, 4) iLeaf )) ( (5), 6) (iLeaf ))"

value "delete 4 (iNode (iNode (iNode iLeaf (1,3) iLeaf) (5,6) iLeaf) (7,11) 
            (iNode (iNode iLeaf (12,12) iLeaf) (13,15) (iNode iLeaf (17,17) iLeaf)))"


(* helper lemmas *) 

lemma ss:  "ibst t \<Longrightarrow> (\<forall> y \<in> set_itree3 t. a > snd y) \<Longrightarrow> (\<forall> y \<in> set_itree2 t. a > y)"
  apply(induction t)
  apply(auto)
  done 


lemma itree2_itree3: "ibst t \<Longrightarrow> (\<forall> y \<in> set_itree2 t. a > y) \<Longrightarrow>  (\<forall> y \<in> set_itree3 t. a > snd y)" 
  apply(induction t)
   apply(auto)
   apply fastforce
   by fastforce


lemma ss_2:  "ibst t \<Longrightarrow> (\<forall> y \<in> set_itree3 t. b < fst y) \<Longrightarrow> (\<forall> y \<in> set_itree2 t. b < y)"
  apply(induction t)
  apply(auto)
  done 


lemma itree2_itree3_2: "ibst t \<Longrightarrow> (\<forall> y \<in> set_itree2 t. b < y) \<Longrightarrow>  (\<forall> y \<in> set_itree3 t. b < fst y)" 
  apply(induction t)
  apply(auto)
  apply fastforce
  by fastforce
  

lemma set_itree_x: "ibst (iNode l (a,b) r) \<Longrightarrow> x < a \<Longrightarrow> x \<notin> set_itree2 r " 
proof - 
  assume a: "ibst (iNode l (a,b) r)"
  assume b: "x < a" 
  show  "x \<notin> set_itree2 r"
    by (metis (full_types) Orderings.preorder_class.order.strict_trans2 Submission.ibst.simps(2) a b order_less_imp_not_eq2 order_less_trans ss_2)
qed


lemma set_itree_z: "ibst (iNode l (a,b) r) \<Longrightarrow> x > b \<Longrightarrow> x \<notin> set_itree2 l " 
proof - 
  assume a: "ibst (iNode l (a,b) r)"
  assume b: "x > b" 
  show  "x \<notin> set_itree2 l"
    by (metis Submission.ibst.simps(2) a b linorder_not_le order_less_trans ss)
qed


lemma delete_set_minus: "ibst t \<Longrightarrow> set_itree2 (delete x t) = (set_itree2 t) - {x}"
proof -
  assume ass_1: "ibst t"
  then show "set_itree2 (delete x t) = (set_itree2 t) - {x}"
  proof(induction x t rule: delete.induct)
    case (1 x)
    then show ?case by simp 
  next
    case (2 x l a b r)
    (*  x < a \<Longrightarrow> ibst l \<Longrightarrow> set_itree2 (delete x l) = set_itree2 l - {x}  *)
    (* \<not> x < a \<Longrightarrow> b < x \<Longrightarrow> ibst r \<Longrightarrow> set_itree2 (delete x r) = set_itree2 r - {x}  *)
    then show "set_itree2 (delete x (iNode l (a, b) r)) = (set_itree2 (iNode l (a, b) r)) - {x}"
    proof(cases)
      assume a: "x < a"
      then have w: "(delete x (iNode l (a, b) r)) =  (iNode (delete x l) (a,b) r) "
        by simp
      have ih:  "set_itree2 (delete x l) = set_itree2 l - {x} " using  2(3) 2(1) a
        by simp
      have "set_itree2  (iNode (delete x l) (a,b) r) =  set_itree2  (delete x l) \<union> {a..b} \<union> set_itree2 r" 
        by auto
      also have "... = (set_itree2 l - {x}) \<union> {a..b} \<union> set_itree2 r " using ih 
        by simp
      also have "... =  (set_itree2 l  \<union> {a..b} \<union> set_itree2 r) - {x}" using 2(3) a set_itree_x 
        by fastforce
      also have "... = (set_itree2 (iNode l (a,b) r))  - {x}" 
        by auto
      finally show "set_itree2 (delete x (iNode l (a, b) r)) = set_itree2 (iNode l (a, b) r) - {x}" using w
        by simp
    next 
      assume b:  "\<not> x < a"
      show "set_itree2 (delete x (iNode l (a, b) r)) = set_itree2 (iNode l (a, b) r) - {x}" 
      proof(cases) 
        assume c: "x > b" 
        then have w: "(delete x (iNode l (a, b) r)) =  (iNode l (a,b) (delete x r)) " using b
        by simp
        have ih:  "set_itree2 (delete x r) = set_itree2 r - {x} " using  2(3) 2(2) b c
        by simp
      have "set_itree2  (iNode l (a,b) (delete x r)) =  set_itree2 l \<union> {a..b} \<union> set_itree2 (delete x r)"  
        by auto
      also have "... = (set_itree2 l) \<union> {a..b} \<union> (set_itree2 r - {x}) " using ih 
        by simp
      also have "... =  (set_itree2 l  \<union> {a..b} \<union> set_itree2 r) - {x}" using 2(3) c set_itree_z 
        by fastforce
      also have "... = (set_itree2 (iNode l (a,b) r))  - {x}" 
        by auto
      finally show "set_itree2 (delete x (iNode l (a, b) r)) = set_itree2 (iNode l (a, b) r) - {x}" using w
        by simp
      next 
        assume d: "\<not> x > b" 
        show "set_itree2 (delete x (iNode l (a, b) r)) = set_itree2 (iNode l (a, b) r) - {x}"  
        proof(cases) 
          assume e: "x=a \<and> a =b"
         then have "(delete x (iNode l (a, b) r)) =  (joinn l r) " using b
           by simp
         have f: "set_itree2 (delete x  (iNode l (a, b) r)) = set_itree2 (joinn l r)" using 2 d e 
           by simp
         then have g: "... = set_itree2 l \<union> set_itree2 r" using joinn_set_itree2
           by simp

         have a:"set_itree2 (iNode l (a, b) r) =   ((set_itree2 l) \<union> ({a..b}) \<union> (set_itree2 r))"
           by auto
         have b:" ((set_itree2 l) \<union> ({a..b}) \<union> (set_itree2 r)) =  ((set_itree2 l) \<union> ({x}) \<union> (set_itree2 r))" using e 
           by simp
         have "set_itree2 (iNode l (a, b) r) =(set_itree2 l) \<union> ({x}) \<union> (set_itree2 r) " using a b 
           by simp
         then have "set_itree2 (iNode l (a, b) r) - {x} = (set_itree2 l)  \<union> (set_itree2 r)" 
           by (smt (verit, ccfv_SIG) "local.2.prems" Diff_empty Diff_insert0 Diff_insert_absorb Submission.ibst.simps(2) Un_Diff d e insert_absorb ss ss_2 sup_bot_right)
         then show "set_itree2 (delete x (iNode l (a, b) r)) = set_itree2 (iNode l (a, b) r) - {x}"  using f g
           by simp 
        next 
           assume f:  "\<not> (x=a \<and> a =b)"
           show "set_itree2 (delete x (iNode l (a, b) r)) = set_itree2 (iNode l (a, b) r) - {x}"
           proof (cases) 
             assume g:  "x=a" 
              then have w:  "(delete x (iNode l (a, b) r)) = (iNode l (a+1,b) r)  " using 2 d f g 
                by simp
              then have "set_itree2 (iNode l (a+1, b) r) = (set_itree2 l) \<union> {a+1..b} \<union> (set_itree2 r) " 
                 by auto
               also have "... =  (set_itree2 l) \<union> ({a..b} - {a}) \<union> (set_itree2 r)" try0
                 by fastforce
               also have "... =  ((set_itree2 l) \<union> ({a..b}) \<union> (set_itree2 r)) - {a}" 
                 by (smt (verit) "local.2.prems" Diff_empty Diff_insert0 Submission.ibst.simps(2) Un_Diff b g ss ss_2)
               also have "... =  ((set_itree2 l) \<union> ({a..b}) \<union> (set_itree2 r)) - {x}" using g
                 by simp
               also have "... =  set_itree2 (iNode l (a, b) r) - {x}" 
                 by auto
               finally show "set_itree2 (delete x (iNode l (a, b) r)) = set_itree2 (iNode l (a, b) r) - {x}" using w
                 by simp
           next 
             assume h:  "\<not> x=a"
             show "set_itree2 (delete x (iNode l (a, b) r)) = set_itree2 (iNode l (a, b) r) - {x}"
             proof (cases) 
               assume i:  "x=b"
               then have w:  "(delete x (iNode l (a, b) r)) = (iNode l (a, b-1) r)  " using 2 d h 
                 by simp
               then have "set_itree2 (iNode l (a, b-1) r) = (set_itree2 l) \<union> {a..b-1} \<union> (set_itree2 r) " 
                 by auto
               also have "... =  (set_itree2 l) \<union> ({a..b} - {b}) \<union> (set_itree2 r)" try0
                 by fastforce
               also have "... =  ((set_itree2 l) \<union> ({a..b}) \<union> (set_itree2 r)) - {b}" 
                 by (smt (verit, del_insts) "local.2.prems" Diff_empty Diff_insert0 Submission.ibst.simps(2) Un_Diff d i ss ss_2)  
               also have "... =  ((set_itree2 l) \<union> ({a..b}) \<union> (set_itree2 r)) - {x}" using i 
                 by simp
               also have "... =  set_itree2 (iNode l (a, b) r) - {x}" 
                 by auto
               finally show "set_itree2 (delete x (iNode l (a, b) r)) = set_itree2 (iNode l (a, b) r) - {x}" using w
                 by simp
             next 
               assume j:"\<not> x= b"
               have v: "{a..(x-1)} \<union> {(x+1)..b} \<union> {x} = {a..b}" using 2(3) b d f h j  
                 by auto
               have w:  "(delete x (iNode l (a, b) r)) =  (iNode l (a,x-1) (insert_min r (x+1,b)))  " using  2 b d f h j
                 by simp
               have k: "set_itree2  (iNode l (a,x-1) (insert_min r (x+1,b))) = set_itree2 l \<union> {a..(x-1)} \<union> set_itree2 (insert_min r (x+1,b))" 
                 by auto
                have l: "... =  set_itree2 l \<union> {a..(x-1)} \<union> set_itree2 r \<union> {(x+1)..b}"  using insert_min_set_itree2 try0
                 by blast
                have m: "... =  set_itree2 l \<union> set_itree2 r \<union> ({a..(x-1)} \<union> {(x+1)..b})" 
                 by blast
                have n: "... =  set_itree2 l \<union> set_itree2 r \<union> ({a..(x-1)} \<union> {(x+1)..b} \<union> {x} - {x})" try0
                 by simp 
                have o:  "... =  set_itree2 l \<union> set_itree2 r \<union> ({a..(x-1)} \<union> {(x+1)..b} \<union> {x} - {x})" try0
                 by simp 
                have p:  "... = set_itree2 l \<union> set_itree2 r \<union> ({a..b} - {x})" using v 
                 by simp
               have q: "... = set_itree2 l \<union> set_itree2 r \<union> {a..b} - {x}"
                 by (smt (verit, ccfv_threshold) "local.2.prems" Diff_empty Diff_insert0 Submission.ibst.simps(2) Un_Diff b d ss ss_2)
               have r: "... = set_itree2 (iNode l (a,b) r) - {x}"
                 by auto
               show "set_itree2 (delete x (iNode l (a, b) r)) = set_itree2 (iNode l (a, b) r) - {x}" using k l m n o p q r w 
                by argo
       qed  
    next 
    qed
  qed
qed
qed
qed
qed


(* helpers *)

lemma itree2_del_2: "ibst (iNode l (a,b) r) \<Longrightarrow>  (\<forall> y \<in> set_itree2 (delete x r). b < y)"
proof - 
  assume ass:  "ibst (iNode l (a,b) r)" 
  have b: "set_itree2 (delete x r) = set_itree2 r - {x}"  using delete_set_minus[OF ass]
    by (meson Submission.ibst.simps(2) ass delete_set_minus) 
  have "(\<forall> y \<in> set_itree2 r. b < y)" using ass ss_2
    by auto 
  then show "(\<forall> y \<in> set_itree2 (delete x r). b < y)" using ass b
    by simp
qed


lemma itree2_del: "ibst (iNode l (a,b) r) \<Longrightarrow>  (\<forall> y \<in> set_itree2 (delete x l). a > y)"
proof - 
  assume ass:  "ibst (iNode l (a,b) r)" 
  have b: "set_itree2 (delete x l) = set_itree2 l - {x}"  using delete_set_minus[OF ass]
    by (meson Submission.ibst.simps(2) ass delete_set_minus) 
  have "(\<forall> y \<in> set_itree2 l. a > y)" using ass ss
    by auto 
  then show  "(\<forall> y \<in> set_itree2 (delete x l). a > y)" using ass b
    by simp
qed



(*
fun delete :: "int \<Rightarrow> int itree \<Rightarrow> int itree"  where
  "delete x iLeaf  = iLeaf"
| "delete x (iNode l (a,b) r) = ( 
   if x < a then (iNode (delete x l) (a,b) r) 
   else if x > b then  (iNode l (a,b) (delete x r)) 
   else if x = a \<and> a = b  then (joinn l r)
   else if x = a then (iNode l (a + 1, b) r)
   else if x = b then (iNode l (a, b-1) r) 
   else (iNode l (a,x-1) (insert_min r (x+1,b)))
)                          
*)



lemma ibst_delete: "ibst t \<Longrightarrow> ibst (delete x t)"
proof(induction x t rule: delete.induct)
  case (1 x)
  then show ?case 
    by simp
next
  case (2 x l a b r)
  then consider (c1) "x < a" | (c2) "x >b" | (c3) "x = a \<and> a= b" | (c4) "x=a" | (c5) "x=b" | (c6) "x > a \<and> x < b " sledgehammer
    by force
  then show ?case 
  proof(cases)
    case c1
    assume a: "x < a"
      then have w: "(delete x (iNode l (a, b) r)) =  (iNode (delete x l) (a,b) r) "
        by simp
      have x: "ibst (delete x l)" using 2 a 
        by simp
      have y: "ibst (iNode l (a,b) r)" using 2 
        by simp 
      have z: "(\<forall> y \<in> set_itree3 (delete x l). a > (snd y))" using itree2_del itree2_itree3
        using x y by blast
      have "ibst (iNode (delete x l) (a,b) r)" using x y z 
        by simp
    then show ?thesis 
      using w by presburger
    (*   by (smt (verit, ccfv_threshold) "local.2.IH"(1) "local.2.prems" Submission.delete.simps(2) Submission.ibst.simps(2) itree2_del itree2_itree3)*)
  next
    case c2
     then have w: "(delete x (iNode l (a, b) r)) =  (iNode l (a,b) (delete x r)) "
       using "local.2.prems" by auto
       have x: "ibst (delete x r)"
           using "local.2.IH"(2) "local.2.prems" c2 by force
       have y: "ibst (iNode l (a,b) r)" using 2 
           by simp 
       have z: "(\<forall> y \<in> set_itree3 (delete x r). b < (fst y))" using  itree2_del_2 itree2_itree3_2
           using x y by blast
      have "ibst (iNode l (a,b) (delete x r))" using x y z 
            by simp
       then show "ibst (delete x (iNode l (a, b) r))"  using w 
          by simp
  next
    case c3
    then show ?thesis
      using "local.2.prems" joinn_ibst by auto
  next
    case c4
    then show ?thesis
      using "local.2.prems" joinn_ibst by auto    
  next
    case c5
    then show ?thesis
      using "local.2.prems" joinn_ibst by auto
  next
    case c6
    then have  "(delete x (iNode l (a, b) r)) = (iNode l (a,x-1) (insert_min r (x+1,b)))" 
      by force
    then show ?thesis sorry 
  qed

qed


(*lemma ibst_delete: "ibst t \<Longrightarrow> ibst (delete x t)"
proof -
  assume ass_1: "ibst t"
  then show "ibst (delete x t)"
  proof(induction x t rule: delete.induct)
    case (1 x)
    then show ?case by simp 
  next
    case (2 x l a b r)
    then show "ibst (delete x (iNode l (a, b) r))" 
    proof(cases)
      assume a: "x < a"
      then have w: "(delete x (iNode l (a, b) r)) =  (iNode (delete x l) (a,b) r) "
        by simp
      have x: "ibst (delete x l)" using 2 a 
        by simp
      have y: "ibst (iNode l (a,b) r)" using 2 
        by simp 
      have z: "(\<forall> y \<in> set_itree3 (delete x l). a > (snd y))" using itree2_del itree2_itree3
        using x y by blast
      have "ibst (iNode (delete x l) (a,b) r)" using x y z 
        by simp
      then show "ibst (delete x (iNode l (a, b) r))" using w 
        by simp 
    next 
      assume b:  "\<not> x < a"
      show "ibst (delete x (iNode l (a, b) r))"  
      proof(cases) 
        assume c: "x > b" 
        then have w: "(delete x (iNode l (a, b) r)) =  (iNode l (a,b) (delete x r)) " using b
           by simp
         have x: "ibst (delete x r)" using 2 b c
           by simp
         have y: "ibst (iNode l (a,b) r)" using 2 
           by simp 
         have z: "(\<forall> y \<in> set_itree3 (delete x r). b < (fst y))" using  itree2_del_2 itree2_itree3_2
           using x y by blast
         have "ibst (iNode l (a,b) (delete x r))" using x y z 
            by simp
         then show "ibst (delete x (iNode l (a, b) r))"  using w 
          by simp
      next 
        assume d: "\<not> x > b" 
        show "ibst (delete x (iNode l (a, b) r))"  
        proof(cases) 
          assume e: "x=a \<and> a =b"
          then have "(delete x (iNode l (a, b) r)) =  (joinn l r) " using b
              by simp
          then show "ibst (delete x (iNode l (a, b) r))" using joinn_ibst
            using "local.2.prems" by auto
        next 
           assume f:  "\<not> (x=a \<and> a =b)"
           show "ibst (delete x (iNode l (a, b) r))"  
           proof (cases) 
             assume g:  "x=a"
             then have "(delete x (iNode l (a, b) r)) =  (iNode l (a + 1, b) r) " using 2 d f
               by simp 
             then show "ibst (delete x (iNode l (a, b) r))"
               using "local.2.prems" f g by auto
           next 
             assume h:  "\<not> x=a"
             show "ibst (delete x (iNode l (a, b) r))" 
             proof (cases) 
               assume i:  "x=b"
                then have  "(delete x (iNode l (a, b) r)) = (iNode l (a, b-1) r)  " using 2 d h 
                  by simp
               then show  "ibst (delete x (iNode l (a, b) r))"  using "local.2.prems"  h i by fastforce
             next 
               assume "\<not> x= b"
               then have  "(delete x (iNode l (a, b) r)) = (iNode l (a,x-1) (insert_min r (x+1,b))) " using 2 b d f h
                 by simp
               then show  "ibst (delete x (iNode l (a, b) r))"  sorry     
             qed  
    next 
    qed
  qed
qed
qed
qed
qed
*)

end