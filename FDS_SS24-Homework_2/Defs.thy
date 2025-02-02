theory Defs
  imports Main
begin

datatype 'a ltree = Leaf 'a | Node "'a ltree" "'a ltree"

fun inorder :: "'a ltree \<Rightarrow> 'a list" where
  "inorder (Leaf x) = [x]"
| "inorder (Node l r) = inorder l @ inorder r"  
  
fun fold_ltree :: "('a \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> 'a ltree \<Rightarrow> 's \<Rightarrow> 's" where
  "fold_ltree f (Leaf x) s = f x s"
| "fold_ltree f (Node l r) s = fold_ltree f r (fold_ltree f l s)"

lemma "fold f (inorder t) s = fold_ltree f t s"  
  by (induction t arbitrary: s) auto

fun mirror where
  "mirror (Node l r) = Node (mirror r) (mirror l)"
| "mirror (Leaf x) = Leaf x"  

fun shuffles :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "shuffles xs [] = [xs]"
| "shuffles [] ys = [ys]"  
| "shuffles (x#xs) (y#ys) = map (\<lambda>xs. x # xs) (shuffles xs (y#ys)) @ map (\<lambda>ys. y # ys) (shuffles (x#xs) ys)"  


consts collect :: "'a \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> 'b list"

consts collect_tr :: "'a list \<Rightarrow> 'b \<Rightarrow> ('b \<times> 'a) list \<Rightarrow> 'a list"

consts lheight :: "'a ltree \<Rightarrow> nat"

consts num_leafs :: "'a ltree \<Rightarrow> nat"

consts perfect :: "'a ltree \<Rightarrow> bool"


end