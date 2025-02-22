theory Submission_dirty_bonus
  imports Defs
begin


lemma T_split_min_cmpx: "xs \<noteq> [] \<Longrightarrow> T_split_min xs = length xs"
proof(induction xs rule: T_split_min.induct) 
  case (1 x)
  then show ?case by simp
next
  case (2 x v va)
  then show ?case by simp
next
  case 3
  then show ?case by simp 
qed

value "[T_sel_sort (replicate n (0::nat)) . n <- [0..<10]]"


theorem T_sel_sort_cmpx: "T_sel_sort xs = (((length xs) + 1) * ((length xs) + 2)) div 2" 
  apply(induction xs rule: T_sel_sort.induct)
  apply(auto simp add: T_split_min_cmpx split_min_len split: prod.split)
  done 

thm sum_length_filter_compl

lemma C_qsort_bound: "C_qsort xs \<le> (length xs)\<^sup>2"
proof(induction xs rule: length_induct)
  case (1 xs)
  assume "\<forall>ys. length ys < length xs \<longrightarrow> C_qsort ys \<le> (length ys)\<^sup>2"
  then show "C_qsort xs \<le> (length xs)\<^sup>2" 
  proof(cases xs)
    case Nil
    then show ?thesis by simp 
  next
    case (Cons p ps)
    assume a: "xs = p#ps"
    from this have len_xs_ps: "length xs = length ps + 1" by simp 
    let ?l_len = "length  (filter (\<lambda>x. x < p) ps )" 
    let ?r_len = "length  (filter (\<lambda>x. x \<ge> p) ps)" 
    have sum_len: "?l_len + ?r_len = length ps"
    proof -
      have "(\<lambda>a. \<not> a < p) = (\<le>) p"
        by fastforce
      then show ?thesis
        by (metis sum_length_filter_compl)
    qed
    have "C_qsort xs  = C_qsort (filter (\<lambda>x. x < p) ps ) + C_qsort (filter (\<lambda>x. x \<ge> p) ps) + 2*length ps" using a 
      by simp
    also have "... \<le> (?l_len)^2 + (?r_len)^2 + 2*length ps" using "1.IH" a sum_len
      by (simp add: add_mono)
    also have "... \<le> (?l_len + ?r_len)^2 + 2*length ps"
      by (simp add: power2_sum)
    also have "... = (length ps)^2 + 2*length ps" using sum_len 
      by simp 
    also have "... \<le> (length ps)^2 + 2*length ps + 1" 
      by simp 
    also have "... = (length ps + 1) ^2"
      by (simp add: power2_eq_square)
    also have "...  = (length xs)^2" using len_xs_ps
      by simp
    finally show "C_qsort xs \<le> (length xs)\<^sup>2" 
      by simp
  qed
qed


find_consts name: update

find_theorems name: take_drop

fun rev_pre :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where 
  "rev_pre n xs = (if n \<ge> length xs then rev xs else (rev (take n xs)) @ (drop n xs))"

(*
fun rev_pre_rec  :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where 
  "rev_pre 0 xs = xs"
| "rev_pre (Suc n) xs =  xs[(fst c) := (nth xs (snd c)), (snd c) := (nth xs (fst c))] "
*)

value "rev_pre 4 [(1::nat),4,6,3,4]"

lemma mset_rev_pre[simp]: "mset (rev_pre n xs) = mset xs"
proof(induction xs)
  case Nil
  then show ?case by simp 
next
  case (Cons a xs)
  then show ?case by (simp add: union_code)
qed


find_consts name: max

definition place_max_correct :: "('a::linorder) list \<Rightarrow> 'a list"  where
  "place_max_correct xs = rev_pre (length xs)  (rev_pre (Suc (index xs (Max (set xs)))) xs)"

value "place_max_correct [(1::nat),3,7,3,2,4,7]"


value "place_max_correct [(1::nat),12,7,3,2,4,9,4,2]"

value "place_max_correct [(3::nat),5,3]"

lemma mset_place_max_correct[simp]: "mset (place_max_correct (x#xs)) = mset (x#xs)"
  by (auto simp add: place_max_correct_def union_code) 
  
(*  apply(induction xs)
  apply(auto simp add: place_max_correct_def union_code split: if_splits)
  done 
*) 

(*
  apply(simp add: place_max_correct_def)
  apply(simp add:place_max_correct_def)
  apply(simp split: if_splits)
  apply (auto simp add: union_code)
*) 


lemma last_place_max_correct: "xs \<noteq> [] \<Longrightarrow> last (place_max_correct xs) = Max (set xs)"
  unfolding place_max_correct_def 
(*proof(induction xs)
  case Nil
  then show ?case by simp 
next
  case (Cons a xs)
  then show ?case  
    apply(cases "max a (Max (set xs)) = a")
    unfolding max_def sorry
      
qed
 *) 

  apply(induction xs )
  apply(simp add: place_max_correct_def)
  apply(simp add: place_max_correct_def)
  by (smt (verit, ccfv_threshold) Lattices.linorder_class.max.absorb_iff2 Lattices.linorder_class.max.commute List.list.size(3) Max_insert Nat.nat.simps(3) append_take_drop_id diff_diff_cancel empty_iff finite_set last_appendR last_in_set length_append length_drop length_rev max_def rev_append rev_rev_ident take_rev)


find_consts  "'a list \<Rightarrow> 'a"


fun first :: "'a list \<Rightarrow> 'a" where
"first [] = undefined"
| "first (x # xs) = x"

(*lemma first_place_max_correct: "xs \<noteq> [] \<Longrightarrow> first (rev_pre (Suc (index xs (Max (set xs)))) xs) = Max (set xs)"
  apply(induction xs)
   apply(simp)
  apply(simp)
  apply(simp split: if_splits)
  *)

(*lemma rev_pre_prop: "(Suc idx) < length xs \<Longrightarrow> first (rev_pre (Suc idx) xs) = nth xs idx"
  apply(induction xs)
  apply(simp)
  apply(auto)
  sorry 
*) 

lemma length_place_max_correct[simp]: "length (place_max_correct (x#xs)) = length (x#xs)"
  using mset_eq_length mset_place_max_correct by blast

fun psort :: "('a::linorder) list \<Rightarrow> 'a list"  where
   "psort [] = []"
|  "psort xs =  (let ys = place_max_correct xs in (psort (butlast ys)) @ [last ys])"


find_theorems name: butlast

lemma psort_mset[simp]: "mset (psort xs) = mset xs"
proof(induction xs rule: psort.induct)
  case 1
  then show ?case by simp 
next
  case (2 v va)
  let ?ys =  "place_max_correct (v#va)"
  have ys_ne: "?ys \<noteq> []" using mset_place_max_correct
    by (metis List.list.discI mset_zero_iff_right)
  have e: "add_mset (last (z:: 'a list)) (mset (butlast z)) = mset z" if "z \<noteq> []" for z 
    by (metis add_mset_add_single append_butlast_last_id mset_single_iff that union_code)
  have IH: "mset (psort (butlast ?ys)) = mset (butlast ?ys)" using 2  
    by simp 
  have "mset (psort (v#va)) = mset ((psort (butlast ?ys)) @ [last ?ys])" 
    by simp 
  also have "... = add_mset (last ?ys)  (mset ((psort (butlast ?ys))))"
    by simp 
  also have "... = add_mset (last ?ys)  (mset (butlast ?ys))" using "IH"
    by simp
  also have "... = mset ?ys" using e ys_ne
    by simp
  also have "... = mset (v#va)" using mset_place_max_correct 
    by simp
  finally show "mset (psort (v # va)) = mset (v # va)" 
    by simp
qed


(*  apply(induction xs rule: psort.induct)
  apply(simp)
  by (metis List.list.distinct(1) Submission.psort.simps(2) append_butlast_last_id mset_append mset_place_max_correct mset_zero_iff)
*)

lemma sorted_psort: "sorted (psort xs)"
proof(induction xs rule: psort.induct)
  case 1
  then show "sorted (psort [])" by simp 
next
  case (2 v va)
  obtain ys where ys_prop:  "ys = place_max_correct (v#va)" 
    by simp 
  have a: "psort (v # va) = (psort (butlast ys)) @ [last ys]" using ys_prop 
    by simp 
  have b:  "sorted (psort (butlast ys))" using "2.IH" ys_prop 
    by simp
  have c: "last ys = Max (set (v#va))" using ys_prop last_place_max_correct  
    by blast
  from this have d: "last ys = Max (set ys)" using ys_prop mset_place_max_correct 
    by (metis mset_eq_setD)
  from this have e: "(last ys) \<ge> z" if "z \<in> set (butlast ys)" for z
    by (simp add: in_set_butlastD that)
  from b e have  "sorted ((psort (butlast ys)) @ [last ys])"
    by (metis mset_eq_setD psort_mset sorted_insort sorted_insort_is_snoc)
  from this show "sorted (psort (v # va))" using a 
    by simp
qed


(* Bonus exercise starts here: *)

fun rev_pre_chain :: "nat list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rev_pre_chain [] xs = xs"
| "rev_pre_chain (r#rs) xs = rev_pre_chain rs (rev_pre r xs)"

definition "psortable_in xs k \<equiv> \<exists>rs . length rs \<le> k \<and> (let ys = rev_pre_chain rs xs in mset ys = mset xs \<and> sorted ys)"

fun psort_revs :: "('a :: linorder) list \<Rightarrow> nat list"  where
  "psort_revs [] = []"
| "psort_revs (xs) =  (Suc (index xs (Max (set xs))))#(length xs)#(let ys = place_max_correct xs in (psort_revs (butlast ys)))"



fun psort_chain :: "'a list \<Rightarrow> nat list \<Rightarrow> 'a list" where 
  "psort_chain xs [] = xs"
| "psort_chain xs (y#ys) = psort_chain (rev_pre y xs) ys"


value "psort_revs [1::nat,6,3,2, 5, 2, 4,9]"
value "psort_chain [1::nat,6,3,2, 5, 2, 4,9] (psort_revs  [1::nat,6,3,2, 5, 2, 4,9])"

lemma length_psort_revs: "length (psort_revs xs) \<le> 2* ( length xs)" \<comment> \<open>Replace with your bound\<close>
  by (induction xs rule: psort_revs.induct) simp_all


lemma mset_rev_pre_chain : "mset (rev_pre_chain ys xs) = mset xs"
proof(induction ys arbitrary: xs)
  case Nil
  then show ?case by simp 
next
  case (Cons a ys)
  have "mset (rev_pre_chain (a # ys) xs) = mset (rev_pre_chain ys (rev_pre a xs) )" 
    by simp 
  also have "... = mset (rev_pre a xs)" using Cons 
    by simp 
  also have "... = mset xs" using mset_rev_pre 
    by blast
  finally  show "mset (rev_pre_chain (a # ys) xs) = mset xs"
    by simp 
qed


lemma mset_rev_pre_chain_psort_revs: "mset (rev_pre_chain (psort_revs xs) xs) = mset xs"
  by (simp add: mset_rev_pre_chain)


lemma yy: "x \<le> (length (butlast xs)) \<Longrightarrow> rev_pre x (butlast xs) = butlast (rev_pre x xs)" 
  by (smt (verit, ccfv_threshold) List.list.size(3) Submission.rev_pre.simps append_take_drop_id butlast_append butlast_conv_take butlast_take diff_is_0_eq' diffs0_imp_equal drop_all drop_butlast le_numeral_extra(3) length_drop length_rev less_nat_zero_code linorder_not_le nth_take_lemma rev_take take_all_iff take_butlast)


lemma zz: "(\<forall> x \<in> (set xs). x \<le> (length (butlast ys))) \<Longrightarrow> (rev_pre_chain (butlast xs) (butlast ys)) = butlast (rev_pre_chain (butlast xs) ys)"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp 
next
  case (Cons r rs)
  (* \<forall>x\<in>set rs. x \<le> length (butlast ?ys) \<Longrightarrow>
    rev_pre_chain (butlast rs) (butlast ?ys) = butlast (rev_pre_chain (butlast rs) ?ys) *)

  (* \<forall>x\<in>set (r # rs). x \<le> length (butlast ys) *)
  have IH: " \<forall>x\<in>set rs. x \<le> length (butlast ys) \<Longrightarrow>
    rev_pre_chain (butlast rs) (butlast ys) = butlast (rev_pre_chain (butlast rs) ys)" using Cons
    by simp
  have ass_2:  " \<forall>x\<in>set (r # rs). x \<le> length (butlast ys)" using Cons try0
    by simp
  
  then show "rev_pre_chain (butlast (r # rs)) (butlast ys) = butlast (rev_pre_chain (butlast (r # rs)) ys)" 
  proof(cases rs)
    case Nil
    then show ?thesis try0
      by simp
  next
    case (Cons a list)
    from this have "rev_pre_chain (butlast (r # rs)) (butlast ys) = rev_pre_chain (r#(butlast rs)) (butlast ys)" try0
      by simp
    also have "... = rev_pre_chain (butlast rs) (rev_pre r (butlast ys))" try0
      by simp
    also have "... =  rev_pre_chain (butlast rs)  (butlast (rev_pre r ys))" using yy ass_2 
      by force
    also have "... = butlast (rev_pre_chain (butlast rs) (rev_pre r ys))" 
      using ass_2 local.Cons.IH by auto
    also have "... = butlast (rev_pre_chain (butlast (r#rs)) ys)"
      by (simp add: Cons)
    finally  show "rev_pre_chain (butlast (r # rs)) (butlast ys) = butlast (rev_pre_chain (butlast (r # rs)) ys)"  try0
      by simp
  qed
qed 



lemma zzz: "(\<forall> x \<in> (set xs). x \<le> (length (butlast ys))) \<Longrightarrow> (rev_pre_chain xs (butlast ys)) = butlast (rev_pre_chain xs ys)"
proof (induction xs arbitrary: ys )
  case Nil
  then show ?case by simp 
next
  case (Cons a xs)
  (*\<forall>x\<in>set xs. x \<le> length (butlast ?ys) \<Longrightarrow> rev_pre_chain xs (butlast ?ys) = butlast (rev_pre_chain xs ?ys) *)

  (*  \<forall>x\<in>set (a # xs). x \<le> length (butlast ys) *)

  have "rev_pre_chain (a#xs) (butlast ys) = rev_pre_chain (xs) (rev_pre a (butlast ys))" try0
    by simp

  also have "... =  rev_pre_chain xs  (butlast (rev_pre a ys))" using yy Cons
    by (metis List.list.set_intros(1))

  also have "... = butlast (rev_pre_chain xs (rev_pre a ys))" using Cons try0
    by simp 

  also have "... = butlast  (rev_pre_chain (a # xs) ys)" 
    by simp

  finally  show " rev_pre_chain (a # xs) (butlast ys) = butlast (rev_pre_chain (a # xs) ys)" 
    by simp
qed


lemma ggg: "xs \<noteq> [] \<Longrightarrow> (Suc (index (xs) (Max (set (xs))))) \<le> length (xs)" 
  apply(induction xs)
  apply(simp)
  apply(simp)
  by (metis List.list.set(1) Max_insert Max_singleton finite_set max_def)


lemma hhh: "\<forall> x \<in> set (psort_revs xs). x \<le> length xs"
proof(induction xs rule: psort_revs.induct)
  case 1
  then show ?case by simp 
next
  case (2 v va)
  (*  ?x = place_max_correct (v # va) \<Longrightarrow> \<forall>x\<in>set (psort_revs (butlast ?x)). x \<le> length (butlast ?x)  *)

  obtain ys where ys_prop: "ys = place_max_correct (v # va) " try0
    by simp

  have a: "psort_revs (v#va) = 
              (Suc (index (v#va) (Max (set (v#va)))))#(length (v#va))
             #(let ys = place_max_correct (v#va) in (psort_revs (butlast ys)))" try0
    by simp

  have b:  "... = (Suc (index (v#va) (Max (set (v#va)))))#(length (v#va))
             # (psort_revs (butlast ys))" using ys_prop try0
    by simp

  have c: "(Suc (index (v#va) (Max (set (v#va))))) \<le> length (v#va)" using ggg
    by blast 

  from a b c show "\<forall>x\<in>set (psort_revs (v # va)). x \<le> length (v # va)" using 2
    by auto 
qed



lemma qqq:  "(\<forall> x \<in> (set xs). x \<le> (length (butlast ys))) \<Longrightarrow> last (rev_pre_chain xs ys) = last ys"  
  apply(induction xs arbitrary: ys)
  apply(simp)
  apply(simp)
  by (metis Nil_is_rev_conv Suc_pred leD le_imp_less_Suc length_greater_0_conv)
  

lemma sorted_psort_revs: "sorted (rev_pre_chain (psort_revs xs) xs)"
proof(induction xs rule: psort_revs.induct)
  case 1
  then show ?case by simp 
next
  case (2 v va)
  (*IH:  ?x = place_max_correct (v # va) \<Longrightarrow> sorted (rev_pre_chain (psort_revs (butlast ?x)) (butlast ?x))  *)

    (* fix yss assume "x = place_max_correct (v # va)" 

  then have "sorted (rev_pre_chain (psort_revs (butlast x)) (butlast x))" using "2.IH" by simp*)


  obtain yss where yss_prop: "yss = place_max_correct(v#va)"
    by simp

  have c:  "rev_pre_chain (psort_revs (v#va)) (v#va) 
      = rev_pre_chain ((Suc (index (v#va) (Max (set (v#va)))))#(length (v#va))#(let ys = place_max_correct (v#va) in (psort_revs (butlast ys)))) (v#va)"
    by simp

  have d: "... = rev_pre_chain 
                  ((length (v#va))#(let ys = place_max_correct (v#va) in (psort_revs (butlast ys)))) 
                  (rev_pre  ((Suc (index (v#va) (Max (set (v#va)))))) (v#va))"
    by simp

  have e: "... = rev_pre_chain 
                 (let ys = place_max_correct (v#va) in (psort_revs (butlast ys)))
                 (rev_pre  (length (v#va))  (rev_pre  ((Suc (index (v#va) (Max (set (v#va)))))) (v#va)))"
    by simp

  have f: "... = rev_pre_chain 
                 (let ys = place_max_correct (v#va) in (psort_revs (butlast ys))) 
                 ( place_max_correct (v#va)) " using place_max_correct_def 
    by metis

  have g: "... = rev_pre_chain 
                  (psort_revs (butlast yss))
                  (yss)" using yss_prop
    by simp

  have ih:  "sorted (rev_pre_chain 
                    (psort_revs (butlast yss))
                    (butlast yss))" using yss_prop 2
    by simp

  have len: "\<forall> x \<in> set ((psort_revs (butlast yss))). x \<le> length (butlast yss)" using hhh 
    by blast  

  from this  have "butlast (rev_pre_chain 
                  (psort_revs (butlast yss))
                  (yss)) = rev_pre_chain  (psort_revs (butlast yss)) (butlast yss)" using zzz 
    by force 

  from this ih have j: "sorted (butlast (rev_pre_chain 
                  (psort_revs (butlast yss))
                  (yss)))"
    by simp

  have k:  "last (rev_pre_chain 
                  (psort_revs (butlast yss))
                  (yss)) = last yss" using len qqq try0
    by blast

  have l:  "last yss = Max (set yss)" using yss_prop last_place_max_correct
    by (metis List.list.discI mset_eq_setD mset_place_max_correct)


  from this have "last yss = Max (set (rev_pre_chain 
                  (psort_revs (butlast yss))
                  (yss)))" using mset_rev_pre_chain 
    by (metis set_mset_mset)


  from j k this have "sorted ((butlast (rev_pre_chain 
                  (psort_revs (butlast yss))
                  (yss))) @ [last yss])"
    by (simp add: in_set_butlastD sorted_wrt_append)

  from this have "sorted (rev_pre_chain 
                  (psort_revs (butlast yss))
                  (yss))" using k 
    by (metis append_butlast_last_id sorted0)
 
  from c d e f g this have "sorted (rev_pre_chain (psort_revs (v#va)) (v#va))"
    by simp

  then show "sorted (rev_pre_chain (psort_revs (v # va)) (v # va))"
    by simp
qed
  


theorem psortable_in_linear: "psortable_in xs (2*(length xs))" \<comment> \<open>Replace with your bound\<close>
 unfolding psortable_in_def
proof - 
  show "\<exists>rs. length rs \<le> 2 * length xs \<and> (let ys = rev_pre_chain rs xs in mset ys = mset xs \<and> sorted ys) "
    using length_psort_revs mset_rev_pre_chain_psort_revs sorted_psort_revs
    by auto
qed 


end