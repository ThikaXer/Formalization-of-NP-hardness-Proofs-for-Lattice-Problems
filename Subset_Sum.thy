theory Subset_Sum

imports Main
        Partition
        "Jordan_Normal_Form.Matrix"

begin

text \<open>Subset Sum Problem\<close>

definition subset_sum :: "((int vec) * int) set" where
  "subset_sum \<equiv> {(as,s). (\<exists>xs::int vec. 
    (\<forall>i<dim_vec xs. xs$i \<in> {0,1}) \<and> xs \<bullet> as = s \<and> dim_vec xs = dim_vec as)}"


definition subset_sum_nonzero :: "((int vec) * int) set" where
  "subset_sum_nonzero \<equiv> {(as,s). (\<exists>xs::int vec. 
    (\<forall>i<dim_vec xs. xs$i \<in> {0,1}) \<and> xs \<bullet> as = s \<and> dim_vec xs = dim_vec as) \<and> dim_vec as \<noteq> 0}"

definition subset_sum_list :: "((int list) * int) set" where
  "subset_sum_list \<equiv> {(as,s). (\<exists>xs::int list. 
    (\<forall>i<length xs. xs!i \<in> {0,1}) \<and> (\<Sum>i<length as. as!i * xs!i) = s \<and> length xs = length as)}"



text \<open>Reduction Subset sum to partition problem.\<close>

definition reduce_subset_sum_partition:: "(int list) \<Rightarrow> ((int list) * int)" where
  "reduce_subset_sum_partition \<equiv> (\<lambda> a. (a, (sum_list a) div 2))"



text \<open>Lemmas for proof\<close>



text \<open>Well-definedness of reduction function\<close>

lemma well_defined_reduction_subset_sum:
  assumes "a \<in> partition_problem"
  shows "reduce_subset_sum_partition a \<in> subset_sum_list"
using assms unfolding partition_problem_def reduce_subset_sum_partition_def subset_sum_list_def Let_def
proof (safe, goal_cases)
  case (1 I)
  then obtain xs::"int list" where 
    xs_prop: "\<forall>i\<in>I. xs ! i = 1"  
    "\<forall>i\<in>{0..<length a}-I. xs ! i = 0"  
    "length xs = length a" sorry
  then have eq: "(\<Sum>i<length a. a!i * xs!i) = (\<Sum>i\<in>I. a!i)" sorry
  have "sum_list a = (\<Sum>i\<in>I. a!i) + (\<Sum>i\<in>{0..<length a}-I. a!i)" using 1(1)
    by (smt (verit) finite_atLeastLessThan sum.subset_diff sum_list_sum_nth)
  also have "\<dots> = 2 * (\<Sum>i\<in>I. a!i)" using 1(2)[symmetric] by auto
  also have "\<dots> = 2 * (sum_list (map2 (*) a xs))" using eq by auto
  finally have "sum_list (map2 (*) a xs) = (sum_list a) div 2" by simp
  then show ?case using xs_prop by (subst exI[of _ xs], auto)
qed

value "let a = [1,2,3::nat] in a ! (length a -1)"



text \<open>NP-hardness of reduction function\<close>

lemma NP_hardness_reduction_subset_sum:
  assumes "reduce_subset_sum_partition a \<in> subset_sum_list"
  shows "a \<in> partition_problem"
using assms unfolding partition_problem_def reduce_subset_sum_partition_def subset_sum_list_def Let_def
proof (safe, goal_cases)
  case (1 xs)
  obtain I where I_prop: "I = {i. i< length xs \<and> xs!i = 1}" by blast
  have "I\<subseteq>{0..<length a}" using I_prop 1 by auto
  moreover have "sum ((!) a) I = sum ((!) a) ({0..<length a} - I)"
  proof - 
    have eq: "(\<Sum>i\<in>I. a!i) = (\<Sum>i<length a. a!i * xs!i)" sorry
    have "(\<Sum>i\<in>{0..<length a}-I. a!i) = sum ((!) a) {0..<length a} - (\<Sum>i\<in>I. a!i)" sorry
    also have "\<dots> = sum_list a - sum_list a div 2" sorry
    also have "\<dots> = sum_list a div 2" sorry
    finally have "(\<Sum>i\<in>{0..<length a}-I. a!i) = (\<Sum>i\<in>I. a!i)" sorry
    then show ?thesis by auto
  qed    
  ultimately show ?case by (subst exI, auto)
qed

find_theorems sum_list


text \<open>The Gap-SVP is NP-hard.\<close>
lemma "is_reduction reduce_subset_sum_partition partition_problem subset_sum_list"
unfolding is_reduction_def
proof (safe, goal_cases)
  case (1 a)
  then show ?case using well_defined_reduction_subset_sum by auto
next
  case (2 a)
  then show ?case using NP_hardness_reduction_subset_sum by auto
qed




end