theory Defs
  imports "HOL-Library.Tree"
begin

fun isin :: "('a::linorder) tree \<Rightarrow> 'a \<Rightarrow> bool" where
  "isin Leaf x = False" |
  "isin (Node l a r) x =
  (if x < a then isin l x else
   if x > a then isin r x
   else True)"

fun ins :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
  "ins x Leaf = Node Leaf x Leaf" |
  "ins x (Node l a r) =
  (if x < a then Node (ins x l) a r else
   if x > a then Node l a (ins x r)
   else Node l a r)"

lemma set_tree_isin: "bst t \<Longrightarrow>  isin t x = (x \<in> set_tree t)"
  apply(induction t)
   apply auto
  done

lemma set_tree_ins: "set_tree (ins x t) = {x} \<union> set_tree t"
  apply(induction t)
   apply auto
  done

lemma bst_ins: "bst t \<Longrightarrow> bst (ins x t)"
  apply(induction t)
   apply (auto simp: set_tree_ins)
  done

declare [[names_short]]


consts bst_remdups_aux :: "'a::linorder tree \<Rightarrow> 'a list \<Rightarrow> 'a list"

consts sublist :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"

datatype direction = L | R
type_synonym path = "direction list"

consts get :: "'a tree \<Rightarrow> path \<Rightarrow> 'a tree"

consts put :: "'a tree \<Rightarrow> path \<Rightarrow> 'a tree \<Rightarrow> 'a tree"

consts valid :: "'a tree \<Rightarrow> path \<Rightarrow> bool"

consts find :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> path set"


end