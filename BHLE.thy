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
      x \<noteq> 0\<^sub>v (dim_vec x) \<and> \<parallel>x\<parallel>\<^sub>\<infinity> \<le> k}"

text \<open>Reduction of bounded homogeneous linear equation to partition problem\<close>
(*Remember: i runs from 1 to n=length a*)
definition b1 :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "b1 i M a = a + M * (5^(4*i-4) + 5^(4*i-3) + 5^(4*i-1))"

definition b2 :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "b2 i M = M * (5^(4*i-3) + 5^(4*i))"

definition b2_last :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "b2_last i M = M * (5^(4*i-3) + 1)"

definition b3 :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "b3 i M =  M * (5^(4*i-4) + 5^(4*i-2))"

definition b4 :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "b4 i M a = a + M * (5^(4*i-2) + 5^(4*i-1) + 5^(4*i))"

definition b4_last :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "b4_last i M a = a + M * (5^(4*i-2) + 5^(4*i-1) + 1)"

definition b5 :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "b5 i M = M * (5^(4*i-1))"

fun rec_bhle where
  "rec_bhle i M [] = []" |
  "rec_bhle i M (a # []) = [b1 i M a, b2_last i M, b3 i M, b4_last i M a, b5 i M]" |
  "rec_bhle i M (a # as) = [b1 i M a, b2 i M, b3 i M, b4 i M a, b5 i M] @ (rec_bhle (i+1) M as)"

definition gen_bhle :: "int list \<Rightarrow> int vec" where
  "gen_bhle as = vec_of_list (rec_bhle 1 (2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1) as)"

(*
try this out
value "(2*(\<Sum>i<length [1,2::nat]. \<bar>[1,2::nat]!i\<bar>)+1)"
value "b1 1 7 1"
value "b4_last 2 7 2"
value "rec_bhle 1 7 [1,2::nat]"
*)

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

lemma length_rec_bhle:
  "length (rec_bhle i M a) = 5 * (length a)"
by (induct a arbitrary: i rule: induct_list012, auto)



text \<open>Well-definedness of reduction function\<close>

lemma well_defined_reduction_subset_sum:
  assumes "a \<in> partition_problem"
  shows "reduce_bhle_partition a \<in> bhle"
using assms unfolding partition_problem_def reduce_bhle_partition_def bhle_def
proof (safe, goal_cases)
  case (1 I)
  have "length a > 0" sorry
  define x::"int vec" where "x = vec_of_list (concat (replicate (length a) [1,-1,0,0,-1]))"
  have "dim_vec x = 5 * length a" unfolding x_def by (induct a , auto)
  then have "0 < dim_vec x" using \<open>length a > 0\<close> by auto
  define n where "n = length a"
  define M where "M = 2*(\<Sum>i<length a. \<bar>a!i\<bar>)+1"
  have "(gen_bhle a) \<bullet> x = 0"
  proof -
    have "(gen_bhle a) \<bullet> x = (\<Sum>i\<in>{1..<n}. (b1 i M (a!(i-1))) - (b2 i M) - (b5 i M)) + 
              (b1 n M (a!(n-1))) - (b2_last n M) - (b5 n M)" unfolding gen_bhle_def sorry
    also have "\<dots> = (\<Sum>i\<in>{1..<n}. (a!(i-1)) + (M * 5^(4*i-4) - M * 5^(4*i))) +
                    (a!(n-1)) + M * 5^(4*n-4) - M" 
      unfolding b1_def b2_def b5_def b2_last_def n_def 
      by (subst distrib_left)+ (simp) 
    also have "\<dots> = (\<Sum>i\<in>{1..<n}. (a!(i-1))) + (a!(n-1)) + 
      (\<Sum>i\<in>{1..<n}. M * 5^(4*i-4) - M * 5^(4*i)) + M * 5^(4*n-4) - M"
      by (subst sum.distrib[of "(\<lambda>i. a ! (i - 1))" "(\<lambda>i. M * 5 ^ (4 * i - 4) - M * 5 ^ (4 * i))" 
        "{1..<n}"], simp)
    also have "\<dots> = (\<Sum>i<n. a!i) + M * ((\<Sum>i\<in>{1..<n+1}. 5^(4*i-4)) - (\<Sum>i\<in>{1..<n}. 5^(4*i)) - 1)"
    proof -
      have "(\<Sum>i\<in>{1..<n}. (a!(i-1))) = (\<Sum>i<n-1. (a!i))" 
        using \<open>length a > 0\<close> 
        by (metis (mono_tags, lifting) add_diff_cancel_left' atLeast0LessThan o_def plus_1_eq_Suc 
        sum.atLeastLessThan_shift_0 sum.cong)
      then have "(\<Sum>i\<in>{1..<n}. (a!(i-1))) + (a!(n-1)) = (\<Sum>i<n. (a!i))"
        by (metis One_nat_def Suc_pred \<open>0 < length a\<close> n_def sum.lessThan_Suc)
      moreover{ 
        have "(\<Sum>i=1..<n. M * 5 ^ (4 * i - 4) - M * 5 ^ (4 * i)) + M * 5 ^ (4 * n - 4) - M = 
          M * ((\<Sum>i=1..<n. 5 ^ (4 * i - 4) - 5 ^ (4 * i)) + 5 ^ (4 * n - 4) - 1)"
        using \<open>length a > 0\<close> n_def 
          apply (subst right_diff_distrib[symmetric, of M])
          apply (subst sum_distrib_left[symmetric])
          apply (subst distrib_left[of M, symmetric])
          by (simp add: right_diff_distrib)
        moreover have "(\<Sum>i=1..<n. 5 ^ (4 * i - 4) - 5 ^ (4 * i)) =
          (\<Sum>i=1..<n. 5 ^ (4 * i - 4)) - (\<Sum>i=1..<n. 5 ^ (4 * i))" 
          using sum_subtractf[of "(\<lambda>i. 5 ^ (4 * i - 4))" "(\<lambda>i. 5 ^ (4 * i))" "{1..<n}"]
            sorry
        moreover have "(\<Sum>i=1..<n. 5 ^ (4 * i - 4)) + 5 ^ (4 * n - 4) =
          (\<Sum>i = 1..<n + 1. 5 ^ (4 * i - 4))" using \<open>length a > 0\<close> n_def by auto
        ultimately have "(\<Sum>i=1..<n. M* 5 ^ (4*i - 4) - M* 5 ^ (4*i)) + M* 5 ^ (4*n - 4) - M = 
          M * ((\<Sum>i = 1..<n + 1. 5 ^ (4 * i - 4)) - (\<Sum>i = 1..<n. 5 ^ (4 * i)) - 1)"
          using \<open>length a > 0\<close> n_def by auto
      }
      ultimately show ?thesis by auto
    qed
    also have "\<dots> = (\<Sum>i<n. a!i) + M * ((\<Sum>i\<in>{0..<n}. 5^(4*i)) - (\<Sum>i\<in>{0..<n}. 5^(4*i)))"
    proof -
      have "(\<Sum>i = 1..<n + 1. 5 ^ (4 * i - 4)) = (\<Sum>i = 0..<n. 5 ^ (4 * i))" sorry
      moreover have "(\<Sum>i = 1..<n. 5 ^ (4 * i)) + 1 = (\<Sum>i\<in>{0..<n}. 5^(4*i))" sorry
      ultimately show ?thesis by (smt (verit, del_insts))
    qed
    also have "\<dots> = (\<Sum>i<n. a!i)" sorry
    also have "\<dots> = 0" sorry
    finally show ?thesis by blast

find_theorems "sum _ _ = sum _ _ - sum _ _"
thm mult_1_right[of "-M", symmetric]

  qed
  moreover have "dim_vec x = dim_vec (gen_bhle a)" 
  proof -
    have "length (concat (replicate (length a) [1,-1,0,0,-1])) = 5 * (length a)" 
      by (induct a, auto)
    moreover have "length (rec_bhle 1 (2 * (\<Sum>i<length a. \<bar>a ! i\<bar>) + 1) a) = 5 * (length a)" 
      using length_rec_bhle by auto
    ultimately have "length (concat (replicate (length a) [1,-1,0,0,-1])) = 
          length (rec_bhle 1 (2 * (\<Sum>i<length a. \<bar>a ! i\<bar>) + 1) a)" by auto
    then show ?thesis unfolding x_def gen_bhle_def by simp
  qed
  moreover have "x \<noteq> 0\<^sub>v (dim_vec x)"
  proof (rule ccontr)
    assume "\<not> x \<noteq> 0\<^sub>v (dim_vec x)"
    then have "x = 0\<^sub>v (dim_vec x)" by auto
    have "x $ 0 = 0" using \<open>dim_vec x >0\<close>
      by (subst \<open>x=0\<^sub>v (dim_vec x)\<close>) (subst index_zero_vec[of 0], auto)
    moreover have "x $ 0 \<noteq> 0" 
    proof -
      have first: "vec_of_list (concat (replicate (length a) [1, - 1, 0, 0, - 1])) $ 0 = 1"
        by (subst vec_of_list_index)
           (metis Suc_pred \<open>0 < length a\<close> append_Cons concat.simps(2) nth_Cons_0 replicate_Suc)
      show ?thesis by (smt (z3) first x_def)
    qed
    ultimately show False by auto
  qed
  moreover have "\<parallel>x\<parallel>\<^sub>\<infinity> \<le> 1"
  proof -
    let ?x_list = "concat (replicate (length a) [1, - 1, 0, 0, - 1])"
    have set: "set (?x_list) = {-1,0,1}" using \<open>length a > 0\<close> by auto
    have "?x_list ! i \<in> {-1,0,1}" if "i< length ?x_list" for i
      using nth_mem[OF that] apply (subst set[symmetric]) sorry
    then have "x$i\<in>{-1,0,1}" if "i<dim_vec x" for i using that unfolding x_def
      by (smt (z3) dim_vec_of_list vec_of_list_index)
    then have "\<bar>x$i\<bar>\<le>1" if "i<dim_vec x" for i using that by fastforce
    then show ?thesis unfolding linf_norm_vec_Max 
      by (subst Max_le_iff, auto simp add: exI[of "(\<lambda>i. dim_vec x > i)" 0] \<open>dim_vec x > 0\<close>)
  qed
  ultimately show ?case by blast
qed




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