theory SVP_vec

imports BHLE
        infnorm
        Lattice_vec


begin

text \<open>The reduction of SVP to CVP in $l_\infty$ norm\<close>

text \<open>The shortest vector problem.\<close>
definition is_shortest_vec :: "lattice  \<Rightarrow> real vec \<Rightarrow> bool" where
  "is_shortest_vec L v \<equiv> (is_lattice L) \<and> (\<forall>x\<in>L. infnorm (x) \<ge> infnorm (v) \<and> v\<in>L) "


text \<open>The decision problem associated with solving SVP exactly.\<close>
definition gap_svp :: "(lattice \<times> real) set" where
  "gap_svp \<equiv> {(L, r). (is_lattice L) \<and> (\<exists>v\<in>L. infnorm v \<le> r \<and> v \<noteq> 0\<^sub>v (dim_vec v))}"

text \<open>Generate a lattice to solve SVP for reduction\<close>

definition gen_svp_basis :: "int vec \<Rightarrow> real \<Rightarrow> real mat" where
  "gen_svp_basis a k = mat (dim_vec a + 1) (dim_vec a + 1) 
    (\<lambda> (i, j). if (i < dim_vec a) \<and> (j< dim_vec a) then (if i = j then 1 else 0)
      else (if (i < dim_vec a) \<and> (j \<ge> dim_vec a) then 0 
      else (if (i \<ge> dim_vec a) \<and> (j < dim_vec a) then (k+1) * (a $ j)
      else 2*(k+1)* (\<Sum> i \<in> {0 ..< dim_vec a}. a $ i) +1 )))"


text \<open>Reduction SVP to bounded homogeneous linear equation problem in $l_\infty$ norm.\<close>
definition reduce_svp_bhle:: "(int vec \<times> real) \<Rightarrow> (lattice \<times> real)" where
  "reduce_svp_bhle \<equiv> (\<lambda> (a, k). (gen_lattice (gen_svp_basis a k), k))"



text \<open>Lemmas for proof\<close>

lemma gen_svp_basis_mult: 
  assumes "dim_vec z = dim_vec a + 1"
  shows "(gen_svp_basis a k) *\<^sub>v z = vec (dim_vec a + 1) 
         (\<lambda>i. if i < dim_vec a then z$i else (k+1) * (z \<bullet> real_of_int_vec a) + 
              (2*(k+1)* (\<Sum> i \<in> {0 ..< dim_vec a}. a $ i) +1) * (z$(dim_vec a)))"
sorry

lemma is_indep_gen_svp_basis: 
  assumes "k>0"
  shows "is_indep (gen_svp_basis a k)"
unfolding is_indep_def
proof (safe, goal_cases)
case (1 z)
  have dim_row_dim_vec: "dim_row (gen_svp_basis a k) = dim_vec z" 
    using 1(2) unfolding gen_svp_basis_def by auto
  then have suc_dim_a_dim_z: "dim_vec z = dim_vec a + 1" unfolding gen_svp_basis_def by auto
  have alt1: "(gen_svp_basis a k *\<^sub>v z) $ i = 0" if "i< dim_vec a +1"for i 
    using 1(1) that unfolding gen_svp_basis_def by auto
  have z_upto_last: "z$i = 0" if "i < dim_vec a" for i 
  proof -
    have elem: "((gen_svp_basis a k) *\<^sub>v z) $ i = z $ i" 
      using gen_svp_basis_mult[OF suc_dim_a_dim_z] that by auto
    show ?thesis by (subst elem[symmetric]) (use alt1[of i] that in \<open>auto\<close>) 
  qed
  moreover have "z $ (dim_vec a) = 0" 
  proof -
    have "0 = (gen_svp_basis a k *\<^sub>v z) $ (dim_vec a)" using alt1 by auto
    also have "\<dots> = vec (Suc (dim_vec a))
       (\<lambda>j. if j < dim_vec a then (k + 1) * real_of_int (a $ j)
         else 2 * (k + 1) * real_of_int (sum (($) a) {0..<dim_vec a}) + 1) \<bullet> z" 
      unfolding gen_svp_basis_def by auto
    also have "\<dots> =  (2 * (k + 1) * real_of_int (sum (($) a) {0..<dim_vec a}) + 1 ) * (z$dim_vec a)"
      unfolding scalar_prod_def using suc_dim_a_dim_z using z_upto_last by auto
    finally have "0 = (2 * (k + 1) * real_of_int (sum (($) a) {0..<dim_vec a}) + 1 ) * 
                      (z$dim_vec a)" by blast
    moreover have "(2 * (k + 1) * real_of_int (sum (($) a) {0..<dim_vec a}) + 1 ) \<noteq> 0"
    proof (safe)
      assume ass: "(2 * (k + 1) * real_of_int (sum (($) a) {0..<dim_vec a}) + 1 ) = 0"
      then show False
        by (smt (z3) ass assms divide_less_eq_1_pos mult_minus_right nonzero_mult_div_cancel_left 
          of_int_hom.hom_one of_int_less_iff of_int_minus)
    qed
    ultimately show ?thesis by auto
  qed
  ultimately have "z$i =  0" if "i < dim_vec z" for i using that suc_dim_a_dim_z
    by (metis discrete le_eq_less_or_eq verit_comp_simplify1(3))
  then show ?case by auto
qed

find_theorems "_$_ = _$_"


text \<open>Well-definedness of reduction function\<close>

lemma well_defined_reduction_svp:
  assumes "(a,k) \<in> bhle"
  shows "reduce_svp_bhle (a,k) \<in> gap_svp"
using assms unfolding reduce_svp_bhle_def gap_svp_def bhle_def
proof (safe, goal_cases)
  case (1 x)
  then show ?case using is_lattice_gen_lattice is_indep_gen_svp_basis by auto
next
  case (2 x)
  define v where "v = (gen_svp_basis a k) *\<^sub>v (real_of_int_vec x)"
  have "v \<in> gen_lattice (gen_svp_basis a k)"  unfolding v_def gen_lattice_def apply auto sorry
  moreover have "infnorm v \<le> k" unfolding v_def using 2 apply auto sorry
  moreover have "v \<noteq> 0\<^sub>v (dim_vec v)" unfolding v_def using 2 apply auto sorry
  ultimately show ?case by blast
qed




text \<open>NP-hardness of reduction function\<close>

lemma NP_hardness_reduction_svp:
  assumes "reduce_svp_bhle (a,k) \<in> gap_svp"
  shows "(a,k) \<in> bhle"
using assms unfolding reduce_svp_bhle_def gap_svp_def bhle_def
proof (safe, goal_cases)
  case (1 v)
  then show ?case sorry
qed
sorry



text \<open>The Gap-SVP is NP-hard.\<close>
lemma "is_reduction reduce_svp_bhle bhle gap_svp"
unfolding is_reduction_def
proof (safe, goal_cases)
  case (1 as s)
  then show ?case using well_defined_reduction_svp by auto
next
  case (2 as s)
  then show ?case using NP_hardness_reduction_svp by auto
qed



end