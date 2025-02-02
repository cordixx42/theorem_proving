theory Defs
  imports "HOL-Data_Structures.Cmp"
begin

datatype 'a tree12 =
  Leaf ("\<langle>\<rangle>") |
  Node1 "'a tree12"  ("\<langle>_\<rangle>") |
  Node2 "'a tree12" 'a "'a tree12"  ("\<langle>_, _, _\<rangle>")

fun inorder :: "'a tree12 \<Rightarrow> 'a list" where
"inorder Leaf = []" |
"inorder (Node1 t) = inorder t" |
"inorder (Node2 l a r) = inorder l @ a # inorder r"

class height = fixes height :: "'a \<Rightarrow> nat"

instantiation tree12 :: (type)height
begin

fun height_tree12 :: "'a tree12 \<Rightarrow> nat" where
"height Leaf = 0" |
"height (Node1 t) = Suc (height t)" |
"height (Node2 l _ r) = Suc (max (height l) (height r))"

instance ..

end

fun invar :: "'a tree12 => bool" where
  "invar Leaf = True" |
  "invar (Node1 t) = (case t of
    Leaf => True |
    Node1 _ => False |
    Node2 l _ r => height l = height r \<and> invar l \<and> invar r)" |
  "invar (Node2 l _ r) = (height l = height r \<and> invar l \<and> invar r)"

datatype 'a upI = TI "'a tree12" | OF "'a tree12" 'a "'a tree12"

fun treeI :: "'a upI \<Rightarrow> 'a tree12" where
"treeI (TI t) = t" |
"treeI (OF l a r) = Node2 l a r"

fun hI :: "'a upI \<Rightarrow> nat" where
"hI (TI t) = height t" |
"hI (OF l a r) = height l"


consts merge :: "'a tree12 \<Rightarrow> 'a \<Rightarrow> 'a tree12 \<Rightarrow> 'a \<Rightarrow> 'a tree12 \<Rightarrow> 'a upI"

consts ins :: "'a::linorder \<Rightarrow> 'a tree12 \<Rightarrow> 'a upI"


end