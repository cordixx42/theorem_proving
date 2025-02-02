theory Defs
  imports Main
begin

datatype 'a mtree = Leaf | Node (left: "'a mtree") (minimum: 'a) (element: 'a) (right: "'a mtree")


consts set_mtree2 :: "'a mtree \<Rightarrow> 'a set"

consts mbst :: "'a::{linorder,zero} mtree \<Rightarrow> bool"

consts min_val :: "'a::{linorder,zero} mtree \<Rightarrow> 'a"

consts mins :: "'a::{linorder,zero} \<Rightarrow> 'a mtree \<Rightarrow> 'a mtree"

consts misin :: "'a::linorder \<Rightarrow> 'a mtree \<Rightarrow> bool"

consts mtree_in_range :: "'a::linorder mtree \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list"


end