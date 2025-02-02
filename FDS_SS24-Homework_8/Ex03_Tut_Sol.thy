theory Ex03_Tut_Sol
  imports "HOL-Library.Tree"
begin

fun %invisible isin :: "('a::linorder) tree \<Rightarrow> 'a \<Rightarrow> bool" where
  "isin Leaf x = False" |
  "isin (Node l a r) x =
  (if x < a then isin l x else
   if x > a then isin r x
   else True)"

fun isin2 :: "('a::linorder) tree \<Rightarrow> 'a option \<Rightarrow> 'a \<Rightarrow> bool" where
  "isin2 Leaf z x = (case z of None \<Rightarrow> False | Some y \<Rightarrow> x = y) " |
  "isin2 (Node l a r) z x =
  (if x < a then isin2 l z x else isin2 r (Some a) x)"

lemma isin2_Some:
  "\<lbrakk> bst t;  \<forall>x \<in> set_tree t. y < x \<rbrakk>
  \<Longrightarrow> isin2 t (Some y) x = (isin t x \<or> x=y)"
  apply(induction t arbitrary: y)
  apply auto
  done

lemma isin2_None: 
   "bst t \<Longrightarrow> isin2 t None x = isin t x"
apply(induction t)
  apply (auto simp: isin2_Some)
  done

fun join :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
  "join t Leaf = t" |
  "join Leaf t = t" |
  "join (Node l1 a1 r1) (Node l2 a2 r2) =
   (case join r1 l2 of
     Leaf \<Rightarrow> Node l1 a1 (Node Leaf a2 r2) |
     Node l b r \<Rightarrow> Node (Node l1 a1 l) b (Node r a2 r2))"


lemma join_inorder[simp]:  "inorder(join t1 t2) = inorder t1 @ inorder t2"
apply(induction t1 t2 rule: join.induct)
  apply (auto split: tree.split)
  done

lemma  "height(join t1 t2) \<le> max (height t1) (height t2) + 1"
apply(induction t1 t2 rule: join.induct)
  apply (auto split: tree.split)
  done

declare join.simps[simp del]

thm set_inorder[symmetric] bst_iff_sorted_wrt_less

thm bst_wrt.simps
thm sorted_wrt_append

lemma join_set[simp]:  "set_tree (join t1 t2) = set_tree t1 \<union> set_tree t2"
  by (simp del: set_inorder add: set_inorder[symmetric])  

lemma bst_pres[simp]:  "bst (Node l (x::_::linorder) r) \<Longrightarrow> bst (join l r)"
  by (simp del: bst_wrt.simps add: bst_iff_sorted_wrt_less sorted_wrt_append)

fun delete :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
  "delete x Leaf = Leaf"
| "delete x (Node l v r) = (
    if x=v then join l r 
    else if x<v then Node (delete x l) v r
    else Node l v (delete x r)
  )"  

lemma bst_set_delete[simp]:  "bst t \<Longrightarrow> set_tree (delete x t) = (set_tree t) - {x}"
  by (induction t) auto


lemma bst_del_pres:  "bst t \<Longrightarrow> bst (delete x t)"
  by (induction t) auto

end