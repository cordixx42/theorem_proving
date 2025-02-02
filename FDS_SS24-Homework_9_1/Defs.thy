theory Defs
  imports "HOL-Data_Structures.Balance" "HOL-Data_Structures.RBT_Set"
begin

fun mk_rbt :: "'a tree \<Rightarrow> 'a rbt" where
  "mk_rbt \<langle>\<rangle> = \<langle>\<rangle>"
| "mk_rbt \<langle>l, a, r\<rangle> = (let
    l'=mk_rbt l;
    r'=mk_rbt r
  in
    if min_height l > min_height r then
      B (paint Red l') a r'
    else if min_height l < min_height r then
      B l' a (paint Red r')
    else
      B l' a r'
  )"

consts list_to_rbt :: "'a list \<Rightarrow> 'a rbt"


end