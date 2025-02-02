theory Submission
  imports Defs
begin

fun set_mtree2 :: "'a mtree \<Rightarrow> 'a set"  where
  "set_mtree2 Leaf = {}"
| "set_mtree2 (Node l m a r) =  {a} \<union> set_mtree2 l \<union> set_mtree2 r"

value "set_mtree2 (Node (Node Leaf (3::nat) 3 (Node Leaf 3 4 Leaf)) 3 5 (Node Leaf 8 8 Leaf))"

(*fun mbst :: "'a::{linorder,zero} mtree \<Rightarrow> bool"  where
  "mbst Leaf = True" 
| "mbst (Node l m a r) = ( (\<exists> y \<in> ((set_mtree2 l) \<union> {a}). m = y) \<and> (\<forall> z \<in>set_mtree2 l. m \<le> z) \<and> (\<forall>x\<in>set_mtree2 l.  x < a) \<and> (\<forall>x\<in>set_mtree2 r. x > a) \<and> mbst l \<and> mbst r)"
*)

fun mbst :: "'a::{linorder,zero} mtree \<Rightarrow> bool"  where
  "mbst Leaf = True" 
| "mbst (Node l m a r) = ((if l = Leaf then m = a else  m \<in> (set_mtree2 l)) \<and> (\<forall> z \<in>set_mtree2 l. m \<le> z) \<and> (\<forall>x\<in>set_mtree2 l.  x < a) \<and> (\<forall>x\<in>set_mtree2 r. x > a) \<and> mbst l \<and> mbst r)"


value "mbst (Node Leaf (3::nat) 3 Leaf)"

value "mbst (Node (Node Leaf (3::nat) 3 (Node Leaf 4 4 Leaf)) 3 5 (Node Leaf 8 8 Leaf))"

value "(Node (Node Leaf (3::nat) 3 (Node Leaf 3 4 Leaf)) 3 5 (Node Leaf 8 8 Leaf))"
value "mbst (Node (Node Leaf (1::nat) 1 (Node Leaf 4 4 Leaf)) 1 5 (Node Leaf 8 8 Leaf))"


value "mbst (Node (Node (Node (Node Leaf 1 1 Leaf) 1 3 Leaf)  1 5  (Node (Node Leaf 6 6 Leaf) 6 7 Leaf) ) (1::nat) 9 (Node Leaf 12 12 Leaf))"

fun min_val :: "'a::{linorder,zero} mtree \<Rightarrow> 'a"  where
  "min_val Leaf =  0"
| "min_val (Node l m a r) = (if l = Leaf then a else min_val l)"


value "mbst (Node (Node Leaf (2::nat) 2 (Node Leaf 4 4 Leaf)) 2 5 (Node Leaf 8 8 Leaf))"
value "min_val (Node (Node Leaf (2::nat) 2 (Node Leaf 4 4 Leaf)) 2 5 (Node Leaf 8 8 Leaf))"

value "min_val (Node (Node (Node (Node Leaf 2 2 Leaf) 2 3 Leaf)  2 5  (Node (Node Leaf 6 6 Leaf) 6 7 Leaf) ) (2::nat) 9 (Node Leaf 12 12 Leaf))"


lemma mbst_min: "mbst (Node l m a r) \<Longrightarrow> min_val (Node l m a r) = m"
  apply (induction l)
   apply(auto)
  apply (simp add: leD)
  done 


fun mins :: "'a::{linorder,zero} \<Rightarrow> 'a mtree \<Rightarrow> 'a mtree"  where
  "mins x Leaf = (Node Leaf x x Leaf)"
| "mins x (Node l m a r) = (if x < a \<and> x < m then (Node (mins x l) x a r)
                           else if x < a \<and> x \<ge> m then (Node (mins x l) m a r)
                           else if x > a then (Node l m a (mins x r)) 
                            else (Node l m a r) )"


value "mins 1 (Node (Node Leaf (3::nat) 3 (Node Leaf 4 4 Leaf)) 3 5 (Node Leaf 8 8 Leaf))"


lemma mins_set: "x \<in> set_mtree2 (mins x t)"
  apply (induction t)
   apply (auto)
  done 

lemma mins_inserted: "set_mtree2 (mins x t) = {x} \<union> (set_mtree2 t)" 
  apply(induction t)
   apply(auto)
  done


find_theorems "Ball"

lemma mbst_mins: "mbst t \<Longrightarrow> mbst (mins x t)"
  apply (induction t)
  apply(simp)
  apply(auto simp add: mins_inserted)
  apply (metis ball_empty mins_set set_mtree2.simps(1))
  by (metis empty_iff mins_set set_mtree2.simps(1))    



fun misin :: "'a::linorder \<Rightarrow> 'a mtree \<Rightarrow> bool"  where
  "misin x Leaf = False"
| "misin x (Node l m a r) = (if x = a \<or> x = m then True else if x < m then False else if x<a then misin x l else misin x r) "


value "misin 3 (Node (Node Leaf (3::nat) 3 (Node Leaf 4 4 Leaf)) 3 5 (Node Leaf 8 8 Leaf)) "


lemma misin_set: "mbst t \<Longrightarrow> misin x t \<longleftrightarrow> x\<in>set_mtree2 t"
  apply (induction t)
  apply(auto)
  apply(simp split: if_splits)
  apply(auto)
  apply(simp split: if_splits)
  apply(simp split: if_splits)
  done


(*fun mtree_in_range :: "'a::linorder mtree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list"  where
  "mtree_in_range Leaf u v = []"
| "mtree_in_range (Node l m a r) u v = ((if  u < a \<and> m \<le> v  then mtree_in_range l u v else []) @ (if m \<le> v \<and> u \<le> a \<and> a \<le> v then [a] else []) @ (if m \<le> v \<and> a < v then mtree_in_range r u v else []))"
*)


fun mtree_in_range :: "'a::linorder mtree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list"  where
  "mtree_in_range Leaf u v = []"
| "mtree_in_range (Node l m a r) u v = ( if m > v then [] else (if  u < a \<and> m \<noteq> a then mtree_in_range l u v else []) @ (if  u \<le> a \<and> a \<le> v then [a] else []) @ (if  a < v then mtree_in_range r u v else []) )"


value "mtree_in_range (Node (Node (Node (Node Leaf 2 2 Leaf) 2 3 Leaf)  2 5  (Node (Node Leaf 6 6 Leaf) 6 7 Leaf) ) (2::nat) 9 (Node Leaf 12 12 Leaf)) 3 10"


lemma mbst_range: "mbst t \<Longrightarrow> set (mtree_in_range t u v) = {x\<in>set_mtree2 t. u\<le>x \<and> x\<le>v}"
  apply(induction t arbitrary:)
  apply(auto)
  apply(simp split:if_splits)
  apply(auto)
  apply(simp split:if_splits)
  apply(auto)
  apply(force)
  apply(force)
  done

end