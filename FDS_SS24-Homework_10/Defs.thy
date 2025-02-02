theory Defs
  imports "HOL-Data_Structures.Set_Specs"
begin

declare [[names_short]]
declare Let_def[simp]

datatype trie = LfR | LfA | Nd bool "trie * trie"

(* Magic incantation, just ignore*)
datatype_compat trie


definition empty_trie :: trie where
  [simp]: "empty_trie = LfR"

fun invar where
  "invar LfR = True" |
  "invar LfA = True" |
  "invar (Nd b (l,r)) = (invar l \<and> invar r \<and> (l = LfR \<and> r = LfR \<longrightarrow> b) \<and> (l = LfA \<and> r = LfA \<longrightarrow> \<not> b))"


consts isin_trie :: "trie \<Rightarrow> bool list \<Rightarrow> bool"

consts set_trie :: "trie \<Rightarrow> bool list set"

consts node :: "bool \<Rightarrow> trie * trie \<Rightarrow> trie"

consts insert_trie :: "bool list \<Rightarrow> trie \<Rightarrow> trie"

consts delete_trie :: "bool list \<Rightarrow> trie \<Rightarrow> trie"


end