theory BHLE

imports Main
        "Jordan_Normal_Form.Matrix"
        infnorm
        Partition
        Lattice_int

begin
text \<open>Bounded Homogeneous Linear Equation Problem\<close>

definition bhle :: "(int vec * int) set" where
  "bhle \<equiv> {(a,k). \<exists>x. a \<bullet> x = 0 \<and> dim_vec x = dim_vec a \<and> 
      x \<noteq> 0\<^sub>v (dim_vec x) \<and> infnorm x \<le> k}"

text \<open>Reduction of bounded homogeneous linear equation to partition problem\<close>

definition
  "b1 i M a = a + M * (5^(4*i-4) + 5^(4*i-3) + 5^(4*i-1))"

definition
  "b2 i M = M * (5^(4*i-3) + 5^(4*i))"

definition
  "b2_last i M = M * (5^(4*i-3) + 1)"

definition
  "b3 i M =  M * (5^(4*i-4) + 5^(4*i-2))"

definition
  "b4 i M a = a + M * (5^(4*i-2) + 5^(4*i-1) + 5^(4*i))"

definition
  "b4_last i M a = a + M * (5^(4*i-2) + 5^(4*i-1) + 1)"

definition
  "b5 i M = M * (5^(4*i-1))"

fun rec_bhle where
  "rec_bhle i M [] = []" |
  "rec_bhle i M (a#[]) = [b1 i a M, b2_last i M, b3 i M, b4_last i M a, b5 i M]" |
  "rec_bhle i M (a # as) = [b1 i a M, b2 i M, b3 i M, b4 i M a, b5 i M] @ (rec_bhle (i+1) M as)"

definition gen_bhle :: "int list \<Rightarrow> int vec" where
  "gen_bhle as = vec_of_list (rec_bhle 0 (2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1) as)"



definition reduce_bhle_partition:: "(int list) \<Rightarrow> ((int vec) * int)" where
  "reduce_bhle_partition \<equiv> (\<lambda> a. (gen_bhle a, 1))"



text \<open>Lemmas for proof\<close>

lemma split_sum:
  assumes "\<forall>i<n. a!i = b!i + M * c!i" 
          "length (a::int list) = n" 
          "length (b::int list) = n" 
          "length (c::int list) = n" 
          "length (x::int list) = n"
  shows "(\<Sum>i<n. x!i * a!i) = (\<Sum>i<n. x!i * b!i) + M * (\<Sum>i<n. x!i * c!i)"
proof -
  have "(\<Sum>i<n. x!i * a!i) = (\<Sum>i<n. x!i * ( b!i + M * c!i))" using assms(1) by auto
  also have "\<dots> = (\<Sum>i<n. x!i * b!i) + (\<Sum>i<n. M * x!i * c!i)"
    by (simp add: distrib_left mult.commute mult.left_commute)
  also have "\<dots> = (\<Sum>i<n. x!i * b!i) + M * (\<Sum>i<n. x!i * c!i)"
    using sum_distrib_left[symmetric, where r=M and f="(\<lambda>i. x!i*c!i)" and A = "{0..<n}"]  
    by (metis (no_types, lifting) lessThan_atLeast0 mult.assoc sum.cong)
  finally show ?thesis by blast
qed

lemma lt_M:
  assumes "length (b::int list) = n" 
          "length (x::int list) = n"
          "M > k * (\<Sum>i<n. \<bar>b!i\<bar>)"
          "\<forall>i<n. \<bar>x!i\<bar> \<le>k" 
          "k>0"
  shows "\<bar>(\<Sum>i<n. x!i * b!i)\<bar> < M"
proof - 
  have "\<bar>(\<Sum>i<n. x!i * b!i)\<bar> \<le> (\<Sum>i<n. \<bar>x!i * b!i\<bar>)" using sum_abs by auto
  also have "\<dots> = (\<Sum>i<n. \<bar>x!i\<bar> * \<bar>b!i\<bar>)" using abs_mult by metis
  also have "\<dots> \<le> (\<Sum>i<n. k * \<bar>b!i\<bar>)" using assms
    by (smt (verit, del_insts) lessThan_iff mult.commute mult_left_mono sum_mono)
  also have "\<dots> = k * (\<Sum>i<n. \<bar>b!i\<bar>)" using sum_distrib_left by metis
  finally have "\<bar>(\<Sum>i<n. x!i * b!i)\<bar> \<le> k * (\<Sum>i<n. \<bar>b!i\<bar>)" by linarith
  then show ?thesis using assms by auto
qed

lemma split_eq_system:
  assumes "\<forall>i<n. a!i = b!i + M * c!i" 
          "length (a::int list) = n" 
          "length (b::int list) = n" 
          "length (c::int list) = n" 
          "length (x::int list) = n"
          "M > k * (\<Sum>i<n. \<bar>b!i\<bar>)"
          "\<forall>i<n. \<bar>x!i\<bar> \<le>k" 
          "k>0"
  shows "(\<Sum>i<n. x!i * a!i) = 0 \<longleftrightarrow> (\<Sum>i<n. x!i * b!i) = 0 \<and> (\<Sum>i<n. x!i * c!i) = 0"
using assms proof (safe, goal_cases)
  case 1
  then show ?case 
  proof (cases "(\<Sum>i<n. x!i * c!i) = 0")
    case True
    then show ?thesis using split_sum 1 by auto
  next
    case False
    then have "\<bar>(\<Sum>i<n. x!i * b!i)\<bar> < M * \<bar>(\<Sum>i<n. x!i * c!i)\<bar>" 
      using lt_M[OF assms(3) assms(5) assms(6) assms(7) assms(8)] False 
      by (smt (verit, best) mult_less_cancel_left2)
    moreover have "\<bar>(\<Sum>i<n. x!i * b!i)\<bar> = M * \<bar>(\<Sum>i<n. x!i * c!i)\<bar>" 
      using split_sum[OF assms(1) assms(2) assms(3) assms(4) assms(5)] assms
      by (smt (z3) "1"(9) lt_M[OF assms(3) assms(5) assms(6) assms(7) assms(8)]
        mult_le_0_iff mult_minus_right)
    ultimately have False by linarith 
    then show ?thesis by auto
  qed
next
  case 2
  then show ?case 
  proof (cases "(\<Sum>i<n. x!i * b!i) = 0")
    case True
    then show ?thesis using split_sum 2 using lt_M[OF assms(3) assms(5) assms(6) assms(7) assms(8)]
       by auto
  next
    case False
    then have "\<bar>(\<Sum>i<n. x!i * b!i)\<bar> < M * \<bar>(\<Sum>i<n. x!i * c!i)\<bar>" 
      using lt_M[OF assms(3) assms(5) assms(6) assms(7) assms(8)] False
      by (smt (verit, best) "2"(8) "2"(9) mult_eq_0_iff mult_le_cancel_left1 
        split_sum[OF assms(1) assms(2) assms(3) assms(4) assms(5)])
    moreover have "\<bar>(\<Sum>i<n. x!i * b!i)\<bar> = M * \<bar>(\<Sum>i<n. x!i * c!i)\<bar>" 
      using split_sum[OF assms(1) assms(2) assms(3) assms(4) assms(5)] assms
      by (smt (z3) "2"(9) lt_M[OF assms(3) assms(5) assms(6) assms(7) assms(8)]
         mult_le_0_iff mult_minus_right)
    ultimately have False by linarith 
    then show ?thesis by auto
  qed
next
  case 3
  then show ?case using split_sum[OF assms(1) assms(2) assms(3) assms(4) assms(5)] by auto
qed



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