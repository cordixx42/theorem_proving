theory Defs
  imports "HOL-Library.Multiset"
begin

fun a :: "nat \<Rightarrow> int" where
"a 0 = 0" |
"a (Suc n) = a n ^ 2 + 1"

fun path :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool"
  where
  "path G u [] v \<longleftrightarrow> u=v"
| "path G u (x#xs) v \<longleftrightarrow> G u x \<and> path G x xs v"

lemma path_append[simp]: "path G u (p1@p2) v \<longleftrightarrow> (\<exists>w. path G u p1 w \<and> path G w p2 v)"
  by (induction p1 arbitrary: u) auto

lemma pump_nondistinct_path:
  assumes P: "path G u p v"
  assumes ND: "\<not>distinct p"
  shows "\<exists>p'. length p' > length p \<and> \<not>distinct p' \<and> path G u p' v"
proof -
  from not_distinct_decomp[OF ND]
  obtain xs ys zs y where [simp]: "p = xs @ y # ys @ y # zs" by auto
  from P have 1: "path G u (xs@y#ys@y#ys@y#zs) v"
    by auto

  have 2: "length (xs@y#ys@y#ys@y#zs) > length p" "\<not>distinct (xs@y#ys@y#ys@y#zs)"
    by auto

  from 1 2 show ?thesis by blast
qed

abbreviation "all_n_lists\<equiv>Enum.all_n_lists"
abbreviation "n_lists\<equiv>List.n_lists"
declare in_enum[simp]

consts compnet_step :: "(nat \<times> nat) \<Rightarrow> 'a :: linorder list \<Rightarrow> 'a list"
consts run_compnet :: "(nat \<times> nat) list \<Rightarrow> 'a :: linorder list \<Rightarrow> 'a list" 
consts sort4 :: "(nat \<times> nat) list"
end