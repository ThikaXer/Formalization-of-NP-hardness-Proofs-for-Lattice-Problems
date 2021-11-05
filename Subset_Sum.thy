theory Subset_Sum

imports Main
        "Jordan_Normal_Form.Matrix"

begin

text \<open>Subset Sum Problem\<close>

definition subset_sum :: "((int vec) * int) set" where
  "subset_sum \<equiv> {(as,s). (\<exists>xs::int vec. 
    (\<forall>i<dim_vec xs. xs$i \<in> {0,1}) \<and> xs \<bullet> as = s \<and> dim_vec xs = dim_vec as)}"




text \<open>To show: NP-hardness of subset sum problem\<close>


end