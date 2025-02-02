theory Submission
  imports Defs
begin

declare [[names_short]]

fun list_to_rbt :: "'a list \<Rightarrow> 'a rbt"  where
  "list_to_rbt xs = mk_rbt (balance_list xs)"



value "balance_list [3,4,5,(1::nat)]"


lemma balance_list_inorder: "Tree.inorder (balance_list xs) = xs"
  by simp


lemma mk_inorder: "Tree2.inorder (mk_rbt t) = Tree.inorder t" 
  apply(induction t)
  apply(auto)
  apply (simp add: inorder_paint)
  apply (simp add: inorder_paint)
  done 
  

lemma acomplete_alt:
  "acomplete t \<longleftrightarrow> height t = min_height t \<or> height t = min_height t + 1" 
  apply(induction t)
  apply(simp add: acomplete_def)
  apply(auto simp add: acomplete_def)
  done 
 

lemma mk_rbt_inorder: "Tree2.inorder (list_to_rbt xs) = xs"
  using mk_inorder balance_list_inorder
  by (metis list_to_rbt.elims)

lemma mk_color: "color (mk_rbt t) = Black"
  apply(induction t)
   apply(auto)
  done

lemma mk_rbt_color: "color (list_to_rbt xs) = Black"
  using mk_color
  by auto


lemma mk_rbt_height: "acomplete t \<Longrightarrow> bheight (mk_rbt t) = min_height t" 
  apply(induction t rule: mk_rbt.induct)
  apply(auto)
  apply (meson acomplete_subtreeL)
  subgoal for l a r
    apply(auto simp add: acomplete_alt)
     apply (metis Lattices.linorder_class.max.strict_boundedE leD min_height_le_height)
     by (metis Lattices.linorder_class.max.strict_coboundedI1 add_diff_cancel_left' bheight_paint_Red le_neq_implies_less max_def min_height_le_height mk_color not_less_eq plus_1_eq_Suc)
  by (meson acomplete_subtreeL)
  




lemma mk_invh: "acomplete t \<Longrightarrow> invh (mk_rbt t)"
proof(induction t rule: mk_rbt.induct)
  case 1
  then show ?case
    by simp
next
  case (2 l a r)
  have a_1: "acomplete l \<Longrightarrow> invh (mk_rbt l)" using 2(1)
    by simp
  have a_2: " x = mk_rbt l \<Longrightarrow> acomplete r \<Longrightarrow> invh (mk_rbt r)" for x using 2(2)
    by simp
  have a_3: "acomplete \<langle>l, a, r\<rangle>" using 2(3) 
    by simp

  have a_4: "acomplete r \<Longrightarrow> invh (mk_rbt r)" using a_2 
    by simp

  have b_1: "acomplete l" using a_3 
    by (meson acomplete_subtreeL)
  have b_2: "acomplete r" using a_3 
    by (meson acomplete_subtreeR)
  have b_3: "invh (mk_rbt l)" using a_1 b_1
    by simp
  have b_4: "invh (mk_rbt r)" using a_4 b_2
    by simp

  have uf:  "mk_rbt \<langle>l, a, r\<rangle> = (let
    l'=mk_rbt l;
    r'=mk_rbt r
  in
    if min_height l > min_height r then
      B (paint Red l') a r'
    else if min_height l < min_height r then
      B l' a (paint Red r')
    else
      B l' a r'
  )" by simp


  let ?l' = "mk_rbt l"
  let ?r' = "mk_rbt r"

  have c_1: "bheight (mk_rbt l) = min_height l" using b_1 mk_rbt_height
    by blast
  have c_2: "bheight (mk_rbt r) = min_height r" using b_2 mk_rbt_height
    by blast


  consider (c1) "min_height l > min_height r" | (c2) "min_height l < min_height r" | (c3) "min_height l = min_height r"
    by fastforce
  then show "invh (mk_rbt \<langle>l, a, r\<rangle>)"
  proof cases
    case c1
    then show ?thesis 
      using a_3 b_3 b_4 c_2 invh_paint mk_rbt_height
      
      by fastforce
  next
    case c2
    then show ?thesis using a_3 b_1 b_2 b_3 b_4 invh_paint mk_rbt_height
      by (smt (verit, ccfv_threshold) Lattices.linorder_class.max.orderE Lattices.linorder_class.max.strict_boundedE Lattices.linorder_class.max.strict_order_iff RBT_Set.bheight.simps(2) RBT_Set.invh.simps(2) Suc_eq_plus1 Suc_leI Tree.height_tree.simps(2) acomplete_alt bheight_paint_Red diff_Suc_1 lessI mk_color uf)  
  next
    case c3
    then show ?thesis 
      using b_3 b_4 c_1 c_2 by auto
  qed
qed 




lemma mk_rbt_invh: "invh (list_to_rbt xs)"
  using mk_invh
  by force





lemma mk_invc: "acomplete t \<Longrightarrow> invc (mk_rbt t)" 
proof(induction t rule: mk_rbt.induct)
  case 1
  then show ?case
    by simp
next
  case (2 l a r)
  have a_1: "acomplete l \<Longrightarrow> invc (mk_rbt l)" using 2(1)
    by simp
  have a_2: " x = mk_rbt l \<Longrightarrow> acomplete r \<Longrightarrow> invc (mk_rbt r)" for x using 2(2)
    by simp
  have a_3: "acomplete \<langle>l, a, r\<rangle>" using 2(3) 
    by simp

  have a_4: "acomplete r \<Longrightarrow> invc (mk_rbt r)" using a_2 
    by simp

  have b_1: "acomplete l" using a_3 
    by (meson acomplete_subtreeL)
  have b_2: "acomplete r" using a_3 
    by (meson acomplete_subtreeR)
  have b_3: "invc (mk_rbt l)" using a_1 b_1
    by simp
  have b_4: "invc (mk_rbt r)" using a_4 b_2
    by simp

  have uf:  "mk_rbt \<langle>l, a, r\<rangle> = (let
    l'=mk_rbt l;
    r'=mk_rbt r
  in
    if min_height l > min_height r then
      B (paint Red l') a r'
    else if min_height l < min_height r then
      B l' a (paint Red r')
    else
      B l' a r'
  )" by simp


  let ?l' = "mk_rbt l"
  let ?r' = "mk_rbt r"

  have c_1: "bheight (mk_rbt l) = min_height l" using b_1 mk_rbt_height
    by blast
  have c_2: "bheight (mk_rbt r) = min_height r" using b_2 mk_rbt_height
    by blast


  consider (c1) "min_height l > min_height r" | (c2) "min_height l < min_height r" | (c3) "min_height l = min_height r"
    by fastforce
  then show "invc (mk_rbt \<langle>l, a, r\<rangle>)"
  proof cases
    case c1
    have uff: "mk_rbt \<langle>l, a, r\<rangle> = (let
        l'=mk_rbt l;
        r'=mk_rbt r
       in  B (paint Red l') a r')" 
      using c1 by auto
    then show "invc (mk_rbt \<langle>l, a, r\<rangle>)" using a_3 acomplete_alt b_1 b_3 b_4 c1 
      by (smt (verit, best) Defs.mk_rbt.elims Lattices.linorder_class.min.absorb4 RBT.paint.elims RBT.paint.simps(1) RBT_Set.invc.simps(2) Suc_eq_plus1 Tree.complete.simps(2) Tree.height_tree.simps(2) Tree.min_height.simps(2) Tree.tree.inject complete_iff_min_height diff_add_inverse2 less_eq_Suc_le max_def mk_color nat_neq_iff not_less_eq)
  next
    case c2
     have uff: "mk_rbt \<langle>l, a, r\<rangle> = (let
        l'=mk_rbt l;
        r'=mk_rbt r
       in  B  l' a (paint Red r'))" 
      using c2 by auto
    then show "invc (mk_rbt \<langle>l, a, r\<rangle>)" using a_3 acomplete_alt b_2 b_3 b_4 c2
      by (smt (verit, ccfv_threshold) Defs.mk_rbt.elims RBT.paint.elims RBT_Set.bheight.simps(2) RBT_Set.invc.simps(2) RBT_Set.invh.simps(2) Tree.complete.simps(2) Tree.height_tree.simps(2) Tree.tree.sel(1) Tree.tree.sel(3) Tree.tree.simps(3) complete_iff_min_height diff_add_inverse2 max_def min_height_le_height mk_color mk_invh mk_rbt_height verit_comp_simplify1(3))
  next
    case c3
    then show ?thesis
      using b_3 b_4 by auto
  qed
qed



lemma mk_rbt_invc: "invc (list_to_rbt t)"
  using mk_invc
  by force

end