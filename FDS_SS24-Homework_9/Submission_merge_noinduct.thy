theory Submission_merge_noinduct
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
| "merge (Node1 l) a (Node1 m) b (Node1 r) = TI (Node2  (Node2 l a m) b (Node1 r))"

(*(case  merge l a m b r of
   TI t \<Rightarrow> TI (Node1 t)
 | OF l' a' r' \<Rightarrow> TI (Node2 l' a' r')
   ) "
*)

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
  apply(auto)
  done 


value "invar (treeI(merge \<langle>\<langle>\<rangle>\<rangle> 2 \<langle>\<langle>\<rangle>\<rangle> 2 \<langle>\<langle>\<rangle>, (2::nat), \<langle>\<rangle>\<rangle>))"


lemma invar_merge: "invar l \<Longrightarrow> invar m \<Longrightarrow>  invar r \<Longrightarrow>  height l = height r  \<and> height r =  height m  \<Longrightarrow> invar (treeI(merge l a m b r)) "
  apply(induction l a m b r rule: merge.induct)
  apply(auto split: tree12.splits upI.splits)
  done


value "merge \<langle>\<langle>\<langle>\<rangle>, a\<^sub>1, \<langle>\<rangle>\<rangle>\<rangle> (3::nat) \<langle>\<langle>\<langle>\<rangle>\<rangle>\<rangle> 6 \<langle>\<langle>\<langle>\<rangle>\<rangle>\<rangle>"


lemma invar_height_merge: "invar l \<Longrightarrow> invar m \<Longrightarrow>  invar r \<Longrightarrow>  height l = height r  \<and> height r =  height m  \<Longrightarrow> hI(merge l a m b r) = height l + 1"
  apply(induction l a m b r rule: merge.induct)
  apply(auto split: tree12.splits upI.splits)
  done 


lemma merge_node1: "merge l a m b r \<noteq> TI (Node1 t)" 
  apply(induction l a m b r rule: merge.induct)
  apply(auto)
  done 

lemma invar_simple: "invar(Node2 l a r) \<Longrightarrow> invar(treeI (ins x (Node2 l a r))) \<Longrightarrow>  treeI (ins x (Node2 l a r)) \<noteq> Node1 y" 
  apply(induction "Node2 l a r" rule: ins.induct) 
  apply(auto split: upI.splits)
  apply (metis Defs.tree12.distinct(5) Defs.treeI.elims merge_node1)
  apply (metis Defs.tree12.distinct(5) Defs.treeI.elims merge_node1)
  apply (metis Defs.tree12.distinct(5) Defs.treeI.elims merge_node1)
  apply (metis Defs.tree12.distinct(5) Defs.treeI.elims merge_node1)
  done 


theorem invar_ins: "invar t \<Longrightarrow> invar (treeI(ins x t)) \<and> hI (ins x t) = height t" 
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
   have def_unfold: "ins x (Node1 t) = TI (Node1 t')" using TI
      by simp
    (*have a_4: "treeI (ins x t) \<noteq> Node1 y" for y
      using merge_node1 sledgehammer
    
   have a_2: "invar (Node1 t')" using 2 TI a_3 a_4 invar_merge
      by (smt (verit, best) Defs.hI.simps(1) Defs.height_tree12.simps(1) Defs.height_tree12.simps(2) Defs.invar.elims(2) Defs.invar.simps(2) Defs.tree12.simps(10) Defs.tree12.simps(11) Defs.tree12.simps(9) Defs.treeI.simps(1) a_0 less_numeral_extra(3) zero_less_Suc)*)
    then show "invar (treeI (ins x \<langle>t\<rangle>))" using a_1 invar_simple sorry
      by (smt (verit) "local.2.prems" Defs.invar.elims(1) Defs.invar.simps(2) Defs.tree12.simps(10) Defs.tree12.simps(11) Defs.tree12.simps(9) Defs.treeI.simps(1) Defs.upI.distinct(1) Submission_merge_noinduct.ins.simps(1) TI ih)
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