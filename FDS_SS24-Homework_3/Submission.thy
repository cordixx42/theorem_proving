theory Submission
  imports Defs
begin

fun bst_remdups_aux :: "'a::linorder tree \<Rightarrow> 'a list \<Rightarrow> 'a list"  where
  "bst_remdups_aux t [] = []" 
| "bst_remdups_aux t (x#xs) = (if (isin t x) then bst_remdups_aux t xs else (x#(bst_remdups_aux (ins x t) xs)))"


value "bst_remdups_aux Leaf [(1::nat),2,3,4,5,5,3,3]"

definition "bst_remdups xs \<equiv> bst_remdups_aux Leaf xs"


lemma gen: "bst t \<Longrightarrow> (set (bst_remdups_aux t xs) =  (set xs) - (set_tree t)) "
  apply (induction xs arbitrary:t )
   apply (simp)
  apply (simp)
  apply (simp add: set_tree_isin bst_ins set_tree_ins)
  apply (auto) 
  done 

theorem remdups_set: "set (bst_remdups xs) = set xs"
  apply (simp add: bst_remdups_def)
  apply (simp add: gen)
  done 

lemma h:  "bst t \<Longrightarrow> a \<notin> set (bst_remdups_aux (ins a t) xs)"
  apply(simp add: bst_ins set_tree_ins gen)
  done 
  
lemma gen_distinct: "bst t \<Longrightarrow> distinct(bst_remdups_aux t xs)"
  apply (induction xs arbitrary: t )
  apply (simp) 
  apply (simp add: bst_ins gen set_tree_ins) 
  done 

theorem remdups_distinct: " distinct (bst_remdups xs)"
  apply (simp add: bst_remdups_def)
  apply (simp add: gen_distinct)
  done 

fun sublist :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"  where
  "sublist [] (xs) = True"
| "sublist (ys) [] = False"
| "sublist (y#ys) (x#xs) = ((x=y) \<and> sublist ys xs \<or> sublist (y#ys) xs)"
(*| "sublist (y#ys) (x#xs) = (if x = y then sublist ys xs else sublist (y#ys) xs)"*)

value "sublist [(1::nat),5] [1,2,3,4,5]"


lemma sublist: "sublist xs ys \<Longrightarrow> sublist xs (y#ys)"
  apply (induction xs ys rule: sublist.induct)
    apply (auto)
  done 
  


lemma len_smaller: "bst t \<Longrightarrow> (length (bst_remdups_aux t xs) \<le> length (xs))"
  apply (induction xs)
  apply (simp)
  apply(simp add: gen set_tree_isin set_tree_ins bst_ins)
  sorry


lemma remdups_sub_genn: "bst t \<Longrightarrow> length (bst_remdups_aux t xs) \<le> length (xs)"
  apply(induction xs rule: sublist.induct)
  apply (simp)
  apply (simp)
  apply(simp)
  apply auto
  sorry



lemma remdups_sub_gen:  "bst t \<Longrightarrow> sublist (bst_remdups_aux t xs) xs"
  apply(induction xs arbitrary:t)
  apply(simp)
  apply(simp add: set_tree_isin bst_ins)
  by (smt (verit) Diff_iff List.list.distinct(1) List.list.inject List.list.set_intros(1) Submission.sublist.elims(3) gen)
 

theorem remdups_sub: "sublist (bst_remdups xs) xs"
  apply(simp add: bst_remdups_def)
  apply(simp add: remdups_sub_gen)
  done 


fun get :: "'a tree \<Rightarrow> path \<Rightarrow> 'a tree"  where
 "get t [] = t "
| "get Leaf p = Leaf"
| "get (Node l a r) (x#xs)  = (if (x=L) then (get l xs) else (get r xs))"


value "get (Node (Node Leaf 2 Leaf) (1::nat)  (Node Leaf 3 Leaf)) [R]"

fun put :: "'a tree \<Rightarrow> path \<Rightarrow> 'a tree \<Rightarrow> 'a tree"  where
  "put t [] pt = pt"
| "put Leaf p pt = Leaf"
| "put (Node l a r) (x#xs) pt = (if x=L then (Node (put l xs pt) a r) else (Node l a (put r xs pt)))"

value "put (Node (Node Leaf 2 Leaf) (1::nat)  (Node Leaf 3 Leaf)) [R,L] (Node Leaf 8 Leaf)"

fun valid :: "'a tree \<Rightarrow> path \<Rightarrow> bool"  where
  "valid t [] = True"
| "valid Leaf (x#xs) = False"
| "valid (Node l a r) (x#xs) = (if (x=L) then valid l xs else valid r xs)"

value "valid (Node (Node Leaf 2 Leaf) (1::nat)  (Node Leaf 3 Leaf)) [L,R,L]"

find_consts  "(?'a \<Rightarrow> ?'b) \<Rightarrow> ?'a set \<Rightarrow> ?'b set"

fun find :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> path set"  where
  "find Leaf Leaf = {[]}" 
| "find Leaf s = {}"  
| "find (Node l a r) s = (if  (Node l a r) = s then ({[]} \<union>  image (\<lambda>x. (L#x)) (find l s) \<union>  image (\<lambda>x. (R#x)) (find r s))
                          else image (\<lambda>x. (L#x)) (find l s) \<union>  image (\<lambda>x. (R#x)) (find r s)
)"



fun find_else :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> path set"  where
  "find_else Leaf Leaf = {[]}" 
| "find_else Leaf s = {}"  
| "find_else (Node l a r) s = (if  (Node l a r) = s then ({[]}) 
                          else image (\<lambda>x. (L#x)) (find l s) \<union>  image (\<lambda>x. (R#x)) (find r s)
)"



value "find  (Node (Node Leaf 2  (Node Leaf 3 Leaf)) (1::nat)  (Node Leaf 3 Leaf)) (Node Leaf 3 Leaf)"
value "find  (Node (Node Leaf 2  (Node Leaf 3 Leaf)) (1::nat)  (Node Leaf 3 Leaf)) Leaf"
value "find  (Node Leaf (2::nat) Leaf) (Node Leaf  (2::nat) Leaf)"

value "find (Leaf::nat tree) Leaf"

thm "valid.induct"
thm "put.induct"

lemma get_put: "valid t p \<Longrightarrow> put t p (get t p) = t"
  apply (induction t p  rule: valid.induct)
  apply auto 
  done 

lemma put_get: "valid t p \<Longrightarrow> get (put t p s) p = s"
  apply (induction t p  rule: valid.induct)
  apply auto 
  done 

lemma find_get: "p \<in> find t s \<Longrightarrow> get t p = s"
  apply (induction t s arbitrary: p  rule: find.induct)
  apply (auto)
  apply (simp split: if_splits)
  apply (auto)
  done

fun finite :: " 'a tree \<Rightarrow> bool" where 
  "finite Leaf = True" 
| "finite (Node l a r) = (finite l \<and> finite r)"

fun depth :: " 'a tree \<Rightarrow> nat" where 
  "depth Leaf = 0"
| "depth (Node l a r) =1 + (max (depth l) (depth r))"


lemma smaller: "depth (Node l a r) > depth l" "depth (Node l a r) > depth r "
   apply simp
  apply simp 
  done 

lemma tree_sizes: " a = b \<Longrightarrow> depth a = depth b"
  apply simp 
  done 
  

lemma x: "finite l \<Longrightarrow> find l \<langle>l, a, r\<rangle> = {}"
  apply(induction l arbitrary:)
   apply(simp)
  apply(simp)
  sorry 

    


lemma a: "[] \<in> find s s" 
  apply (induction s)
   apply (simp)
  apply (simp)
  done 


lemma a_else: "find_else s s = {[]}" 
  apply (induction s)
  apply (simp)
  apply (simp)
  done 




lemma put_find: "valid t p \<Longrightarrow> p \<in> find (put t p s) s"
  apply (induction t p  arbitrary:   rule: valid.induct)
  apply (simp add: a)
   apply (simp)
  apply (simp)
  using Defs.direction.exhaust by auto


lemma put_find_else: "valid t p \<Longrightarrow> p \<in> find_else (put t p s) s"
  apply (induction t p  arbitrary:   rule: valid.induct)
  apply (simp add: a_else)
   apply (simp)
  sorry 

  

end