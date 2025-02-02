theory Submission 

imports Defs

begin 


fun collect :: "'a \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> 'b list" where
"collect a [] = []"
| "collect a ((x,y)#xs) = (if (a = x) then (y#(collect a xs)) else (collect a xs))"

value "collect 2 [((2::nat),(3::nat)), (2,5), (3,5)]"

definition ctest :: "(int \<times> int) list" where "ctest \<equiv> [ (2,3),(2,5),(2,7),(2,9),
(3 ,2 ),(3 ,4),(3 ,5 ),(3 ,7 ),(3 ,8 ),
(4,3 ),(4,5 ),(4,7 ),(4,9 ),
(5 ,2 ),(5 ,3 ),(5 ,4),(5 ,6 ),(5 ,7 ),(5 ,8 ),(5 ,9 ), (6,5),(6,7),
(7 ,2 ),(7 ,3 ),(7 ,4),(7 ,5 ),(7 ,6 ),(7 ,8 ),(7 ,9 ), (8,3),(8,5),(8,7),(8,9),
(9 ,2 ),(9 ,4),(9 ,5 ),(9 ,7 ),(9 ,8 ) ]"


value "collect 3 ctest = [2,4,5,7,8]"
value "collect 1 ctest = []"


fun expert_collect :: "'a \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> 'b list" where 
 "expert_collect x ys =  map snd (filter (\<lambda>kv. fst kv = x) ys)"

lemma collect_alt: "collect x ys =  map snd (filter (\<lambda>kv. fst kv = x) ys)" 
  apply (induction ys)
  apply auto 
  done 

fun collect_tr:: "'a list \<Rightarrow> 'b \<Rightarrow> ('b \<times> 'a) list \<Rightarrow> 'a list" where 
   "collect_tr acc x [] = rev acc"
 | "collect_tr acc x ((y1,y2)#ys) = (if (x=y1) then collect_tr (y2#acc) x ys else collect_tr acc x ys)"


value "collect_tr [] 3 ctest = [2,4,5,7,8]" 


lemma collect_gen: "collect_tr xs x ys = (rev xs) @  (collect x ys)"
  apply (induction ys arbitrary: xs)
  apply auto 
  done 


lemma collect_tr_collect: "collect_tr [] x ys = collect x ys" 
  apply (induction ys)
   apply (simp add: collect_gen) 
  apply  (simp add: collect_gen)
  done 

fun lheight :: "'a ltree \<Rightarrow> nat" where 
"lheight (Leaf a) = 0" 
| "lheight (Node l r) = max (1 + (lheight l)) (1 + (lheight r))"

value "lheight (Node (Node (Leaf (1::nat)) (Leaf 2))(Leaf 3) )"


fun num_leafs :: "'a ltree \<Rightarrow> nat" where 
  "num_leafs (Leaf a) = 1"
|  "num_leafs (Node l r) = (num_leafs l) + (num_leafs r)"

value "num_leafs (Node (Node (Leaf (1::nat)) (Leaf 2))(Leaf 3) )"

(*fun perfect :: "'a ltree \<Rightarrow> bool" where 
  "perfect (Leaf a) = True" 
| "perfect (Node l r) = (if ((lheight l) ~= (lheight r)) then False else (perfect l) \<and> (perfect r))"
*)

fun perfect :: "'a ltree \<Rightarrow> bool" where 
  "perfect (Leaf a) = True" 
| "perfect (Node l r) = (( lheight l = lheight r) \<and>  (perfect l) \<and> (perfect r))"



lemma perfect_num_leafs_height: "perfect t \<Longrightarrow> num_leafs t = 2^lheight t" 
  apply (induction t) 
   apply auto 
  done

lemma set_shuffles: "zs \<in> set (shuffles xs ys) \<Longrightarrow> set zs = set xs \<union> set ys"
  apply (induction xs ys arbitrary: zs rule: shuffles.induct)
  done 

end 