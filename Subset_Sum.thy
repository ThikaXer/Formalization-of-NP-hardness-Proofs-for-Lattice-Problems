theory Subset_Sum

imports Main

begin

text \<open>Subset Sum Problem\<close>

definition subset_sum :: "('a list \<times> 'a::{monoid_add,one}) set" where
  "subset_sum \<equiv> {(as,s). (\<exists>xs. length xs = length as \<and> set xs \<subseteq> {0,1} \<and> 
    sum_list (map2 (+) xs as) = s)}"


text \<open>To show: NP-hardness of subset sum problem\<close>


end