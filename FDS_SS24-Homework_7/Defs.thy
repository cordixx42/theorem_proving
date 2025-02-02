theory Defs
  imports "HOL-Library.Multiset" "HOL-Data_Structures.Define_Time_Function"
begin

declare Let_def [simp]
declare [[names_short]]

fun split_min :: "'a::linorder list \<Rightarrow> 'a \<times> 'a list" where
  "split_min [x] = (x,[])"
| "split_min (x#xs) = (
    let (y,ys) = split_min xs in
      if (x<y) then (x,xs)
      else (y,x#ys)
    )"

lemma split_min_len: "split_min(x#xs) = (y,ys) \<Longrightarrow> length ys = length xs"
  apply (induction xs arbitrary: x y ys)
   apply (auto split: prod.splits if_splits)
  done

lemma split_min_snd_len_decr[termination_simp]: 
  assumes "(y,ys) = split_min (x#xs)"
  shows "length ys < Suc (length xs)"
  using assms[symmetric] by (simp add: split_min_len)

fun sel_sort where
  "sel_sort [] = []"
| "sel_sort xs = (let (y,ys) = split_min xs in y#sel_sort ys)"

lemma split_min_mset: 
  assumes "split_min (x#xs) = (y,ys)"
  shows "mset (x#xs) = add_mset y (mset ys)"  
  using assms  
  apply (induction xs arbitrary: y ys rule: split_min.induct)
    apply (auto split: prod.splits if_splits)
  done


time_fun split_min
time_fun sel_sort


find_consts name: "qsort"

fun C_qsort :: "'a::linorder list \<Rightarrow> nat" where
  "C_qsort [] = 0"
| "C_qsort (p#xs) 
    = C_qsort (filter (\<lambda>x. x < p) xs) + C_qsort (filter (\<lambda>x. x \<ge> p) xs) + 2*length xs"

(* Might be helpful *)
fun index :: "('a::linorder) list \<Rightarrow> 'a \<Rightarrow> nat" where
  "index [] x = 0"
| "index (x#xs) y = (if x=y then 0 else Suc (index xs y))"

consts rev_pre :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list"

consts place_max_correct :: "('a::linorder) list \<Rightarrow> 'a list"

consts psort :: "('a::linorder) list \<Rightarrow> 'a list"



end