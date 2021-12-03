theory Subset_Sum

imports Main
        Partition
        "Jordan_Normal_Form.Matrix"

begin

text \<open>Subset Sum Problem\<close>

definition subset_sum :: "((int vec) * int) set" where
  "subset_sum \<equiv> {(as,s). (\<exists>xs::int vec. 
    (\<forall>i<dim_vec xs. xs$i \<in> {0,1}) \<and> xs \<bullet> as = s \<and> dim_vec xs = dim_vec as) \<and> dim_vec as \<noteq> 0}"



text \<open>Reduction Subset sum to partition problem.\<close>

definition "gen_subset_sum a = a"

definition "gen_sum a = a $1"

definition reduce_subset_sum_partition:: "(int vec) \<Rightarrow> ((int vec) * int)" where
  "reduce_subset_sum_partition \<equiv> (\<lambda> a. (gen_subset_sum a, gen_sum a))"



text \<open>Lemmas for proof\<close>



text \<open>Well-definedness of reduction function\<close>

lemma well_defined_reduction_subset_sum:
  assumes "a \<in> partition_problem"
  shows "reduce_subset_sum_partition a \<in> subset_sum"
sorry




text \<open>NP-hardness of reduction function\<close>

lemma NP_hardness_reduction_subset_sum:
  assumes "reduce_subset_sum_partition a \<in> subset_sum"
  shows "a \<in> partition_problem"
sorry



text \<open>The Gap-SVP is NP-hard.\<close>
lemma "is_reduction reduce_subset_sum_partition partition_problem subset_sum"
unfolding is_reduction_def
proof (safe, goal_cases)
  case (1 a)
  then show ?case using well_defined_reduction_subset_sum by auto
next
  case (2 a)
  then show ?case using NP_hardness_reduction_subset_sum by auto
qed




end