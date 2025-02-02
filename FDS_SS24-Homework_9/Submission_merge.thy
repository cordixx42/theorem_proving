theory Submission_merge
  imports Defs
begin

declare [[names_short]]

 (*TI (Node2 l' a' r')*)

(* TODO: TI for recursive case ? *) 
fun merge :: "'a tree12 \<Rightarrow> 'a \<Rightarrow> 'a tree12 \<Rightarrow> 'a \<Rightarrow> 'a tree12 \<Rightarrow> 'a upI"  where
  "merge Leaf a m b r = OF (Node2 Leaf a m) b (Node1 r)"
| "merge l a Leaf b r = OF (Node2 l a Leaf) b (Node1 r)"
| "merge l a m b Leaf = OF (Node2 l a m) b (Node1 Leaf)"
| "merge (Node2 l1 a1 r1) a m b r = OF (Node1 (Node2 l1 a1 r1)) a (Node2 m b r)"
| "merge l a m b (Node2 l2 a2 r2) = OF (Node2 l a m) b (Node1 (Node2 l2 a2 r2))"
| "merge (Node1 l) a (Node1 m) b (Node1 r) = (case  merge l a m b r of  
   TI t \<Rightarrow> TI (Node1 t)
 | OF l' a' r' \<Rightarrow> TI (Node2 l' a' r')
   ) "
| "merge (Node1 l) a (Node2 l1 a1 r1) b (Node1 r) = TI (Node2 (Node2 l a l1) a1 (Node2 r1 b r))"


fun ins :: "'a::linorder \<Rightarrow> 'a tree12 \<Rightarrow> 'a upI"  where
"ins x Leaf = OF Leaf x Leaf" |
"ins x (Node1 t) = (case ins x t of
           TI t' \<Rightarrow> TI (Node1 t') | 
           OF l1 b l2 => TI (Node2 l1 b l2))"|
"ins x (Node2 l a r) =
   (case cmp x a of
      LT \<Rightarrow>
        (case ins x l of
           TI l' => TI (Node2 l' a r) |
           OF l1 b l2 => merge l1 b l2 a r )|
      EQ \<Rightarrow> TI (Node2 l a r) |
      GT \<Rightarrow>
        (case ins x r of
           TI r' => TI (Node2 l a r') |
           OF r1 b r2 => merge l a r1 b r2))"


lemma inorder_merge[simp]:
  "inorder(treeI(merge l a m b r)) = (inorder l) @ a # (inorder m) @ b # (inorder r)"
  apply(induction l a m b r rule: merge.induct)
  apply(auto split: upI.split)
  done 


value "invar (treeI(merge \<langle>\<langle>\<rangle>\<rangle> 2 \<langle>\<langle>\<rangle>\<rangle> 2 \<langle>\<langle>\<rangle>, (2::nat), \<langle>\<rangle>\<rangle>))"


lemma invar_merge: "invar l \<Longrightarrow> invar m \<Longrightarrow>  invar r \<Longrightarrow>  height l = height r  \<and> height r =  height m  \<Longrightarrow> invar (treeI(merge l a m b r)) "
  apply(induction l a m b r rule: merge.induct)
  apply(auto split: tree12.splits upI.splits)
  done

(*
  apply(induction l a m b r rule: merge.induct)
  apply(auto)
     apply (metis (no_types, lifting) Defs.height_tree12.elims Defs.tree12.simps(9) less_numeral_extra(3) zero_less_Suc)
  subgoal for l a m b r
    proof- 
    assume a_1: " (invar l \<Longrightarrow> invar m \<Longrightarrow> invar r \<Longrightarrow> invar (treeI (merge l a m b r)))"
    (*assume "invar l"
    assume "invar m"
    assume "invar (treeI (merge l a m b r))"*)
    assume a_2: " case l of \<langle>\<rangle> \<Rightarrow> True | \<langle>x\<rangle> \<Rightarrow> False | \<langle>l, x, r\<rangle> \<Rightarrow> height l = height r \<and> invar l \<and> invar r"
    assume a_3: " case m of \<langle>\<rangle> \<Rightarrow> True | \<langle>x\<rangle> \<Rightarrow> False | \<langle>l, x, r\<rangle> \<Rightarrow> height l = height r \<and> invar l \<and> invar r "
    assume a_4: " case r of \<langle>\<rangle> \<Rightarrow> True | \<langle>x\<rangle> \<Rightarrow> False | \<langle>l, x, r\<rangle> \<Rightarrow> height l = height r \<and> invar l \<and> invar r"
    assume a_5: " height l = height m"
    assume a_6: " height r = height m "
    have a_7:  "invar l" using a_2
      using Defs.invar.elims(3) by fastforce
    have a_8: "invar m" using a_3
      using Defs.invar.elims(3) by fastforce
    have a_9: "invar r" using a_4
      using Defs.invar.elims(3) by fastforce
    have a_10: "invar (treeI (merge l a m b r))" using a_7 a_8 a_9 a_1 
      by simp
    show "invar (treeI (case merge l a m b r of TI t \<Rightarrow> TI \<langle>t\<rangle> | OF l' a' r' \<Rightarrow> TI \<langle>l', a', r'\<rangle>))  " 
    proof(cases "merge l a m b r")
      case (TI x1)
      then have a_11: "invar (treeI (case merge l a m b r of TI t \<Rightarrow> TI \<langle>t\<rangle> | OF l' a' r' \<Rightarrow> TI \<langle>l', a', r'\<rangle>)) = invar (treeI (TI (Node1 x1)))" 
        by simp
      have "invar x1" using TI a_10
        by simp 
      then have "invar (Node1 x1)"
        by (smt (verit) Defs.invar.elims(2) Defs.tree12.simps(10) Defs.upI.distinct(1) Submission.merge.simps(1) Submission.merge.simps(10) Submission.merge.simps(11) Submission.merge.simps(3) Submission.merge.simps(7) TI a_2 a_3 a_7 a_8 a_9)
      then show "invar (treeI (case merge l a m b r of TI t \<Rightarrow> TI \<langle>t\<rangle> | OF l' a' r' \<Rightarrow> TI \<langle>l', a', r'\<rangle>))"  using a_11
        by simp
    next
      case (OF x21 x22 x23)
      then show ?thesis using a_10
        by simp
    qed
qed
  subgoal for l l1 r1
    using Defs.invar.elims(3) by fastforce
  subgoal for l l1 r1 r
    using Defs.invar.elims(3) by fastforce
*)




value "merge \<langle>\<langle>\<langle>\<rangle>, a\<^sub>1, \<langle>\<rangle>\<rangle>\<rangle> (3::nat) \<langle>\<langle>\<langle>\<rangle>\<rangle>\<rangle> 6 \<langle>\<langle>\<langle>\<rangle>\<rangle>\<rangle>"


(* TODO how to embed fixed variables in proof- after apply script *) 
(*lemma invar_height_merge: "invar l \<Longrightarrow> invar m \<Longrightarrow>  invar r \<Longrightarrow>  height l = height r  \<and> height r =  height m  \<Longrightarrow> hI(merge l a m b r) = height l + 1"
  apply(induction  l a m b r rule: merge.induct)
   apply(auto)
*)



lemma invar_height_merge: "invar l \<Longrightarrow> invar m \<Longrightarrow>  invar r \<Longrightarrow>  height l = height r  \<and> height r =  height m  \<Longrightarrow> hI(merge l a m b r) = height l + 1"
  apply(induction l a m b r rule: merge.induct)
  apply(auto split: tree12.splits upI.splits)
  done 

(*
proof(induction l a m b r rule: merge.induct)
  case (1 a m b r)
  then show ?case 
    by simp
next
  case ("2_1" v a b r)
  then show ?case
    by simp
next
  case ("2_2" v va vb a b r)
  then show ?case
    by simp
next
  case ("3_1" v a va b)
  then show ?case
    by simp
next
  case ("3_2" v a va vb vc b)
  then show ?case 
    by simp
next
  case ("3_3" v va vb a vc b)
  then show ?case 
    by simp
next
  case ("3_4" v va vb a vc vd ve b)
  then show ?case
    by simp
next
  case ("4_1" l1 a1 r1 a v b va)
  then show ?case 
    by simp
next
  case ("4_2" l1 a1 r1 a v b va vb vc)
  then show ?case
    by simp
next
  case ("4_3" l1 a1 r1 a v va vb b vc)
  then show ?case
    by simp
next
  case ("4_4" l1 a1 r1 a v va vb b vc vd ve)
  then show ?case 
    by simp
next
  case ("5_1" v a va b l2 a2 r2)
  then show ?case
    by simp
next
  case ("5_2" v a va vb vc b l2 a2 r2)
  then show ?case
    by simp
next
  case (6 l a m b r)
  then show ?case 
  apply(auto)
  proof-
  assume a_1: " (invar l \<Longrightarrow> invar m \<Longrightarrow> invar r \<Longrightarrow> hI (merge l a m b r) = Suc (height m))"
  assume a_2: " case l of \<langle>\<rangle> \<Rightarrow> True | \<langle>x\<rangle> \<Rightarrow> False | \<langle>l, x, r\<rangle> \<Rightarrow> height l = height r \<and> invar l \<and> invar r"
  assume a_3: " case m of \<langle>\<rangle> \<Rightarrow> True | \<langle>x\<rangle> \<Rightarrow> False | \<langle>l, x, r\<rangle> \<Rightarrow> height l = height r \<and> invar l \<and> invar r "
  assume a_4: " case r of \<langle>\<rangle> \<Rightarrow> True | \<langle>x\<rangle> \<Rightarrow> False | \<langle>l, x, r\<rangle> \<Rightarrow> height l = height r \<and> invar l \<and> invar r"
  assume a_5: "height l = height m"
  assume a_6: "height r = height m "
   have a_7:  "invar l" using a_2
      using Defs.invar.elims(3) by fastforce
   have a_8: "invar m" using a_3
      using Defs.invar.elims(3) by fastforce
   have a_9: "invar r" using a_4
      using Defs.invar.elims(3) by fastforce
   have a_10: " hI (merge l a m b r) = Suc (height m)" using a_7 a_8 a_9 a_1
     by simp
  show " hI (case merge l a m b r of TI t \<Rightarrow> TI \<langle>t\<rangle> | OF l' a' r' \<Rightarrow> TI \<langle>l', a', r'\<rangle>) = Suc (Suc (height m))"
  proof(cases "merge l a m b r")
    case (TI x1)
    then show ?thesis using a_10
      by simp
  next
    case (OF l' a' r')
    then show " hI (case merge l a m b r of TI t \<Rightarrow> TI \<langle>t\<rangle> | OF l' a' r' \<Rightarrow> TI \<langle>l', a', r'\<rangle>) = Suc (Suc (height m))" using a_10
      by (metis Defs.hI.simps(1) Defs.hI.simps(2) Defs.height_tree12.simps(3) Defs.invar.simps(3) Defs.treeI.simps(2) Defs.upI.simps(6) a_5 a_6 a_7 a_8 a_9 invar_merge max_def)
  qed
qed
next
  case (7 l a l1 a1 r1 b r)
  then show ?case
    by simp
qed
*)

lemma merge_node1: "invar l \<Longrightarrow> invar m \<Longrightarrow> invar r \<Longrightarrow>  merge l a m b r \<noteq> TI (Node1 t)" 
  apply(induction l a m b r rule: merge.induct)
  apply(auto) 
proof - 
  fix l a m b r
  assume a_1: " (invar l \<Longrightarrow> invar m \<Longrightarrow> invar r \<Longrightarrow> merge l a m b r \<noteq> TI \<langle>t\<rangle>)"
  assume a_2: " case l of \<langle>\<rangle> \<Rightarrow> True | \<langle>x\<rangle> \<Rightarrow> False | \<langle>l, x, r\<rangle> \<Rightarrow> height l = height r \<and> invar l \<and> invar r"
  assume a_3: " case m of \<langle>\<rangle> \<Rightarrow> True | \<langle>x\<rangle> \<Rightarrow> False | \<langle>l, x, r\<rangle> \<Rightarrow> height l = height r \<and> invar l \<and> invar r"
  assume a_4: " case r of \<langle>\<rangle> \<Rightarrow> True | \<langle>x\<rangle> \<Rightarrow> False | \<langle>l, x, r\<rangle> \<Rightarrow> height l = height r \<and> invar l \<and> invar r "
  assume a_5: "(case merge l a m b r of TI t \<Rightarrow> TI \<langle>t\<rangle> | OF l' a' r' \<Rightarrow> TI \<langle>l', a', r'\<rangle>) = TI \<langle>t\<rangle>"

  have a_7:  "invar l" using a_2 
    using Defs.invar.elims(3) by fastforce
  have a_8: "invar m" using a_3
      using Defs.invar.elims(3) by fastforce
  have a_9: "invar r" using a_4
    using Defs.invar.elims(3) by fastforce

  have " merge l a m b r \<noteq> TI \<langle>t\<rangle>" using a_7 a_8 a_9 a_1 
    by simp

  then show "False" using a_5
    by (smt (z3) Defs.invar.elims(2) Defs.tree12.distinct(5) Defs.tree12.simps(10) Defs.upI.inject(1) Defs.upI.simps(6) Submission.merge.simps(1) Submission.merge.simps(11) Submission.merge.simps(3) Submission.merge.simps(7) a_2 a_3 a_4 a_7 a_8 a_9)
qed


lemma l: "invar t \<Longrightarrow> ins x t = OF l1 b l2 \<Longrightarrow> invar (Node2 l1 b l2) \<and> height l1 = height l2 \<and> height l1 = height t "
proof(induction t arbitrary: l1 b l2)
  case Leaf
  then show ?case 
    by simp
next
  case (Node1 t)
  have "ins x \<langle>t\<rangle> = OF l1 b l2" using Node1(3) 
    by simp
   have "ins x \<langle>t\<rangle> = (case ins x t of
           TI t' \<Rightarrow> TI (Node1 t') | 
           OF l1 b l2 => TI (Node2 l1 b l2))" 
     by simp
   then show ?case 
   proof(cases "ins x t")
     case (TI x1)
     then show ?thesis
       using local.Node1.prems(2) by auto
   next
     case (OF x21 x22 x23)
     then show ?thesis 
       using local.Node1.prems(2) by auto
   qed
next
  case (Node2 t1 x2a t2)
  have a_3: "invar \<langle>t1, x2a, t2\<rangle>" using Node2(3) try0
    by simp
  have a_4: " ins x \<langle>t1, x2a, t2\<rangle> = OF l1 b l2" using Node2(4) try0
    by simp
  have def: "invar \<langle>l1, b, l2\<rangle> = invar( treeI(ins x \<langle>t1, x2a, t2\<rangle>))" using a_4 
    by simp   
  then show "invar \<langle>l1, b, l2\<rangle> \<and> height l1 = height l2 \<and> height l1 = height \<langle>t1, x2a, t2\<rangle>" 
  proof(cases "cmp x x2a")
    case LT
    have unfold: "ins x  \<langle>t1, x2a, t2\<rangle> =  (case ins x t1 of
           TI l' => TI (Node2 l' x2a t2) |
           OF l1 b l2 => merge l1 b l2 x2a t2) " using LT
      by simp
    then show ?thesis
    proof(cases "ins x t1")
      case (TI x1)
      then show ?thesis
        using a_4 unfold by force
    next
      case (OF x21 x22 x23)
      then have ihh: "invar (Node2 x21 x22 x23) \<and> height x21 = height x23 \<and> height x21 = height t1 " using Node2(1)
        by (meson Defs.invar.simps(3) a_3) 
      then have a_6:"ins x \<langle>t1, x2a, t2\<rangle> = merge x21 x22 x23 x2a t2" using unfold 
        by (simp add: OF)
      then have "merge x21 x22 x23 x2a t2 = OF l1 b l2"
        using a_4 by presburger
      have "height x23 = height t2" using ihh
        using a_3 by fastforce
      then have "invar (treeI (merge x21 x22 x23 x2a t2))" using ihh a_3 invar_merge 
        by force
      then show ?thesis 
        by (metis Defs.hI.simps(2) Defs.height_tree12.simps(3) Defs.invar.simps(3) Groups.ab_semigroup_add_class.add.commute Lattices.linorder_class.max.idem a_6 def a_3 a_4 ihh invar_height_merge plus_1_eq_Suc)
    qed
  next
    case EQ
    then show ?thesis
      using a_4 by auto
  next
    case GT
    have unfold: "ins x  \<langle>t1, x2a, t2\<rangle> = (case ins x t2 of
           TI r' => TI (Node2 t1 x2a r') |
           OF r1 b r2 => merge t1 x2a r1 b r2) " using GT
      by auto
    then show ?thesis
    proof(cases "ins x t2")
      case (TI x1)
      then show ?thesis
        using a_4 unfold by force
    next
      case (OF x21 x22 x23)
      then have ihh: "invar (Node2 x21 x22 x23) \<and> height x21 = height x23 \<and> height x21 = height t1 " using Node2(2)
        by (metis Defs.invar.simps(3) a_3) 
      then have a_6:"ins x \<langle>t1, x2a, t2\<rangle> = merge t1 x2a x21 x22 x23" using unfold 
        by (simp add: OF)
      then have "merge t1 x2a x21 x22 x23 = OF l1 b l2"
        using a_4 by presburger
      have "height x23 = height t2" using ihh
        using a_3 by fastforce
      then have "invar (treeI (merge t1 x2a x21 x22 x23))" using ihh a_3 invar_merge 
        by force
      then show ?thesis 
        by (metis Defs.hI.simps(2) Defs.height_tree12.simps(3) Defs.invar.simps(3) Groups.ab_semigroup_add_class.add.commute Lattices.linorder_class.max.idem a_6 def a_3 a_4 ihh invar_height_merge plus_1_eq_Suc)
    qed
  qed
qed


value " treeI (ins (2::nat) (Node2 Leaf 3 Leaf))"

lemma invar_simple: "invar(Node2 l a r) \<Longrightarrow> invar(treeI (ins x (Node2 l a r))) \<Longrightarrow>  treeI (ins x (Node2 l a r)) \<noteq> Node1 y" 
  apply(induction "Node2 l a r" rule: ins.induct) 
  apply(auto)
proof-
  fix a
  assume a_1:" case y of \<langle>\<rangle> \<Rightarrow> True | \<langle>x\<rangle> \<Rightarrow> False | \<langle>l, x, r\<rangle> \<Rightarrow> height l = height r \<and> invar l \<and> invar r"
  assume a_2:"height l = height r"
  assume  a_3:"invar l "
  assume  a_4:"invar r"
  assume  a_5:"a < x"
  assume  a_6:"\<not> x < a "
  assume  a_7:" treeI (case ins x r of TI r' \<Rightarrow> TI \<langle>l, a, r'\<rangle> | OF x xb xc \<Rightarrow> merge l a x xb xc) = \<langle>y\<rangle>"
  show False
  proof(cases "ins x r")
    case (TI x1)
    then show ?thesis
      using a_7 by auto
  next
    case (OF x21 x22 x23)
    then show ?thesis 
      by (metis Defs.invar.simps(3) Defs.tree12.distinct(5) Defs.treeI.elims Defs.upI.simps(6) a_3 a_4 a_7 l merge_node1)
  qed

next 
  fix a
  assume a_1:" case y of \<langle>\<rangle> \<Rightarrow> True | \<langle>x\<rangle> \<Rightarrow> False | \<langle>l, x, r\<rangle> \<Rightarrow> height l = height r \<and> invar l \<and> invar r"
  assume a_2:"height l = height r"
  assume  a_3:"invar l "
  assume  a_4:"invar r"
  assume  a_5:"\<not> a < x"
  assume  a_6:"x < a "
  assume  a_7:" treeI (case ins x l of TI l' \<Rightarrow> TI \<langle>l', a, r\<rangle> | OF l1 b l2 \<Rightarrow> merge l1 b l2 a r) = \<langle>y\<rangle>"
  show False
  proof(cases "ins x l")
    case (TI x1)
    then show ?thesis
      using a_7 by auto
  next
    case (OF x21 x22 x23)
    then show ?thesis 
      by (metis (no_types, lifting) Defs.invar.simps(3) Defs.tree12.distinct(5) Defs.treeI.elims Defs.upI.simps(6) a_3 a_4 a_7 l merge_node1)
    qed
qed


theorem invar_ins: "invar t \<Longrightarrow> invar (treeI(ins x t)) \<and> hI (ins x t) = height t"
  apply(induction x  t rule: ins.induct)
    apply(auto )
  sledgehammer
       apply (smt (verit, del_insts) Defs.hI.simps(1) Defs.height_tree12.elims Defs.invar.elims(1) Defs.invar.simps(3) Defs.tree12.distinct(5) Defs.tree12.inject(1) Defs.tree12.simps(10) Defs.tree12.simps(11) Defs.treeI.elims Defs.treeI.simps(1) Defs.upI.simps(5) Defs.upI.simps(6) invar_simple less_Suc_eq_0_disj less_numeral_extra(3))
  
proof(induction x t rule: ins.induct)
  case (1 x)
  then show ?case
    by simp
next
  case (2 x t)
  have a_0:"invar t" using 2 
    using Defs.invar.elims(3) by fastforce
  then have ih:  "invar (treeI (ins x t))" using 2(1)
    by simp
  have p1: "invar (treeI (ins x \<langle>t\<rangle>))"
  proof(cases "(ins x t)")
    case (TI t')
    (* ins x t = TI t') *)
    then have a_1:  "(ins x \<langle>t\<rangle>) = TI (Node1 t') "
      by simp
    have a_3: "invar t'" using ih TI 
      by simp
    have a_4: "treeI (ins x t) \<noteq> Node1 y" for y
      using invar_simple a_0
      by (metis (no_types, lifting) "local.2.prems" Defs.height_tree12.elims Defs.invar.simps(2) Defs.tree12.simps(10) Defs.upI.distinct(1) Submission.ins.simps(1) TI ih)
   have a_2: "invar (Node1 t')" using 2 TI a_3 a_4 invar_merge
      by (smt (verit, best) Defs.hI.simps(1) Defs.height_tree12.simps(1) Defs.height_tree12.simps(2) Defs.invar.elims(2) Defs.invar.simps(2) Defs.tree12.simps(10) Defs.tree12.simps(11) Defs.tree12.simps(9) Defs.treeI.simps(1) a_0 less_numeral_extra(3) zero_less_Suc)
    then show "invar (treeI (ins x \<langle>t\<rangle>))" using a_1 a_2 
      by simp
  next
    case (OF l1 b l2)
    then show "invar (treeI (ins x \<langle>t\<rangle>))" using ih
      by (simp add: OF)
  qed

  have p2: " hI (ins x \<langle>t\<rangle>) = height \<langle>t\<rangle>" 
  proof(cases "ins x t")
    case (TI t')
    have def_unfold: "ins x (Node1 t) = TI (Node1 t')" using TI
      by simp
    have "hI(TI (Node1 t')) = 1 + height t'"
      by simp
    have "hI(TI t') = height t" using TI 2
      using Defs.invar.elims(3) by fastforce
    then have "height t' = height t"
      by simp
    then show ?thesis 
      using def_unfold by auto
  next
    case (OF l1 b l2)
    have def_unfold: "ins x (Node1 t) = TI (Node2 l1 b l2)" using OF 
      by simp
    have "hI (ins x t) = height t" using 2
      using Defs.invar.elims(3) by fastforce
    then have "hI (OF l1 b l2) = height t" using OF
      by simp
    then have "height l1 = height t" 
      by simp
    then show ?thesis using 2
      using def_unfold p1 by auto
  qed
  show "invar (treeI (ins x \<langle>t\<rangle>)) \<and> hI (ins x \<langle>t\<rangle>) = height \<langle>t\<rangle>" using p1 p2
    by simp
next
  case (3 x l a r)
  have a_1: "invar l" using 3(3) 
    by simp
  have a_2: "invar r"  using 3(3) 
    by simp

  have p1: "invar (treeI (ins x \<langle>l, a, r\<rangle>))"
  proof(cases "cmp x a")
    case LT
    have ih: "invar (treeI (ins x l))" using LT 3(1) a_1 
      by simp
    (*have "(ins x \<langle>l, a, r\<rangle>) =  (case ins x l of
           TI l' => TI (Node2 l' a r) |
           OF l1 b l2 => merge l1 b l2 a r )" using LT
      by simp*) 
    then show "invar (treeI (ins x \<langle>l, a, r\<rangle>))"
    proof(cases "ins x l")
      case (TI l')
      then have def_unfold: "(ins x \<langle>l, a, r\<rangle>) = TI (Node2 l' a r)" using LT 
        by simp
      have b1:  "invar l'" using ih TI
        by simp 
      then have "height l' = height l" using 3(3) TI
        using "local.3.IH"(1) LT by auto
      then show ?thesis  using def_unfold
        using "local.3.prems" b1 by auto
    next
      case (OF l1 b l2)
      then show ?thesis
        using "local.3.IH"(1) "local.3.prems" LT invar_merge by force
    qed
  next
    case EQ
    then show ?thesis using 3 
      by simp
  next
    case GT
     have ih: "invar (treeI (ins x r))" using GT 3(2) a_2 
      by simp
    then show "invar (treeI (ins x \<langle>l, a, r\<rangle>))" 
     proof(cases "ins x r")
     case (TI r')
       then have def_unfold: "(ins x \<langle>l, a, r\<rangle>) = TI (Node2 l a r')" using GT 
         by auto
       have b1:  "invar r'" using ih TI
        by simp 
      then have "height r' = height r"
        using "local.3.IH"(2) GT TI a_2 by auto
      then show ?thesis  using def_unfold
        using "local.3.prems" b1 by auto
     next
       case (OF r1 b r2)
        then show ?thesis
          using "local.3.IH"(2) "local.3.prems" GT invar_merge by fastforce
     qed
  qed

  have p2: "hI (ins x \<langle>l, a, r\<rangle>) = height \<langle>l, a, r\<rangle> " 
  proof(cases "cmp x a")
    case LT
    have ih: " hI (ins x l) = height l" using LT 3(1) a_1 
      by simp
    then show "hI (ins x \<langle>l, a, r\<rangle>) = height \<langle>l, a, r\<rangle>"
    proof(cases "ins x l")
      case (TI l')
      then have def_unfold: "(ins x \<langle>l, a, r\<rangle>) = TI (Node2 l' a r)" using LT 
        by simp
      then show ?thesis  using def_unfold  using TI ih by force
    next
      case (OF l1 b l2)
      then have def_unfold: "(ins x \<langle>l, a, r\<rangle>) = merge l1 b l2 a r " using LT
        by simp
      have b1:  "hI(merge l1 b l2 a r) = height l1 + 1" using invar_height_merge
        using "local.3.IH"(1) "local.3.prems" LT OF by force
      have b2: "height l1 = height l"
        using OF ih by auto
      then show " hI (ins x \<langle>l, a, r\<rangle>) = height \<langle>l, a, r\<rangle>" using def_unfold b1 b2
        using "local.3.prems" by force
    qed
  next
    case EQ
    then show ?thesis using 3 
      by simp
  next
    case GT
     have ih: "invar (treeI (ins x r))" using GT 3(2) a_2 
      by simp
    then show "hI (ins x \<langle>l, a, r\<rangle>) = height \<langle>l, a, r\<rangle>" 
      proof(cases "ins x r")
      case (TI r')
      then have def_unfold: "(ins x \<langle>l, a, r\<rangle>) = TI (Node2 l a r')" using GT 
        by auto
      then show ?thesis  using def_unfold  TI ih "local.3.IH"(2) GT a_2 
        by auto
    next
      case (OF r1 b r2)
      (* why is this auto and LT simp *)
      then have def_unfold: "(ins x \<langle>l, a, r\<rangle>) = merge l a r1 b r2 " using GT
        by auto
      have b1:  "hI(merge l a r1 b r2) = height r1 + 1" using invar_height_merge
        using "local.3.IH"(2) "local.3.prems" GT OF by fastforce
      have b2: "height r1 = height r"
        using "local.3.IH"(2) GT OF a_2 by fastforce
      then show " hI (ins x \<langle>l, a, r\<rangle>) = height \<langle>l, a, r\<rangle>" using def_unfold b1 b2
        using "local.3.prems" by force
    qed 
  qed

  show "invar (treeI (ins x \<langle>l, a, r\<rangle>)) \<and> hI (ins x \<langle>l, a, r\<rangle>) = height \<langle>l, a, r\<rangle>" using p1 p2
    by simp
qed


end