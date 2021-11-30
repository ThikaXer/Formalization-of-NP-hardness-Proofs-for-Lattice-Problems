theory BHLE

imports Main
        "Jordan_Normal_Form.Matrix"
        infnorm
        Partition
        Lattice_vec

begin
text \<open>Bounded Homogeneous Linear Equation Problem\<close>

definition bhle :: "(int vec * real) set" where
  "bhle \<equiv> {(a,k). \<exists>x. a \<bullet> x = 0 \<and> dim_vec x = dim_vec a \<and> 
      x \<noteq> 0\<^sub>v (dim_vec x) \<and> infnorm x \<le> k}"

text \<open>Reduction of bounded homogeneous linear equation to partition problem\<close>

definition "gen_bhle a = a"

definition "gen_bound a = a $ 1"

definition reduce_bhle_partition:: "(int vec) \<Rightarrow> ((int vec) * real)" where
  "reduce_bhle_partition \<equiv> (\<lambda> a. (gen_bhle a, gen_bound a))"



text \<open>Lemmas for proof\<close>



text \<open>Well-definedness of reduction function\<close>

lemma well_defined_reduction_subset_sum:
  assumes "a \<in> partition_problem"
  shows "reduce_bhle_partition a \<in> bhle"
sorry




text \<open>NP-hardness of reduction function\<close>

lemma NP_hardness_reduction_subset_sum:
  assumes "reduce_bhle_partition a \<in> bhle"
  shows "a \<in> partition_problem"
sorry



text \<open>The Gap-SVP is NP-hard.\<close>
lemma "is_reduction reduce_bhle_partition partition_problem bhle"
unfolding is_reduction_def
proof (safe, goal_cases)
  case (1 a)
  then show ?case using well_defined_reduction_subset_sum by auto
next
  case (2 a)
  then show ?case using NP_hardness_reduction_subset_sum by auto
qed

end