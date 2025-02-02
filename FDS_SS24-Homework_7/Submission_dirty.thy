theory Submission_dirty
  imports Defs
begin


time_fun split_min
time_fun sel_sort


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


fun C_qsortt :: "'a::linorder list \<Rightarrow> nat" where
  "C_qsortt [] = 0"
| "C_qsortt (p#xs) 
    = C_qsortt (filter (\<lambda>x. x < p) xs) + C_qsortt (filter (\<lambda>x. x \<ge> p) xs) + 2*length xs"


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


find_consts name: rev

find_theorems name: take_drop

fun rev_pre :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where 
  "rev_pre n xs = (if n \<ge> length xs then rev xs else (rev (take n xs)) @ (drop n xs))"

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


lemma psort_mset[simp]: "mset (psort xs) = mset xs"
  apply(induction xs rule: psort.induct)
  apply(simp)
  by (metis List.list.distinct(1) Submission.psort.simps(2) append_butlast_last_id mset_append mset_place_max_correct mset_zero_iff)
 

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
  "psort_revs _ = []"

lemma length_psort_revs: "length (psort_revs xs) \<le> undefined" \<comment> \<open>Replace with your bound\<close>
  sorry

lemma mset_rev_pre_chain_psort_revs: "mset (rev_pre_chain (psort_revs xs) xs) = mset xs"
  sorry

lemma sorted_psort_revs: "sorted (rev_pre_chain (psort_revs xs) xs)"
  sorry

theorem psortable_in_linear: "psortable_in xs undefined" \<comment> \<open>Replace with your bound\<close>
  sorry

end