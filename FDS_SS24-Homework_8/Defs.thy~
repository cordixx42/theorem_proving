theory Defs
  imports "HOL-Data_Structures.Cmp" "HOL-Data_Structures.Set_Specs"
begin

type_synonym bv = "bool list"
  
definition set_bv :: "bv \<Rightarrow> nat set" 
  where "set_bv bs = { i. i<length bs \<and> bs!i }"

datatype 'a itree = iLeaf | iNode "'a itree" "'a \<times> 'a" "'a itree"

fun set_itree2:: "'a::ord itree \<Rightarrow> 'a set" where
  "set_itree2 iLeaf = {}"
| "set_itree2 (iNode l (low, high) r) = {low .. high} \<union> ((set_itree2 l) \<union> (set_itree2 r))"

fun set_itree3:: "'a itree \<Rightarrow> ('a \<times> 'a) set" where 
  "set_itree3 iLeaf = {}"
| "set_itree3 (iNode l (low, high) r) = {(low, high)} \<union> ((set_itree3 l) \<union> (set_itree3 r))"


consts ibst :: "'a::linorder itree \<Rightarrow> bool"

consts delete :: "int \<Rightarrow> int itree \<Rightarrow> int itree"


end