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
      else k*(k+1)* (\<Sum> i \<in> {0 ..< dim_vec a}. a $ i) +1 )))"


text \<open>Reduction SVP to bounded homogeneous linear equation problem in $l_\infty$ norm.\<close>
definition reduce_svp_bhle:: "(int vec \<times> real) \<Rightarrow> (lattice \<times> real)" where
  "reduce_svp_bhle \<equiv> (\<lambda> (a, k). (gen_lattice (gen_svp_basis a k), k))"



text \<open>Lemmas for proof\<close>

lemma gen_svp_basis_mult: 
  assumes "dim_vec z = dim_vec a + 1"
  shows "(gen_svp_basis a k) *\<^sub>v z = vec (dim_vec a + 1) 
         (\<lambda>i. if i < dim_vec a then z$i else (k+1) * (\<Sum> i \<in> {0 ..< dim_vec a}. z $ i * a $ i) + 
              (k*(k+1)* (\<Sum> i \<in> {0 ..< dim_vec a}. a $ i) +1) * (z$(dim_vec a)))"
using assms proof (subst vec_eq_iff, safe, goal_cases)
case 1
  then show ?case using assms unfolding gen_svp_basis_def by auto
next
case (2 i)
  then show ?case proof (cases "i<dim_vec a")
  case True
    have "{0..<dim_vec a} = insert i {0..<dim_vec a}" using True by auto
    then have "(\<Sum>ia = 0..<dim_vec a. (if i = ia then 1 else 0) * z $ ia) = 
      (\<Sum>ia \<in> insert i {0..<dim_vec a}. (if i = ia then 1 else 0) * z $ ia)" by auto
    also have "\<dots> = z$i" by (subst sum.insert_remove, auto) 
    finally have "(\<Sum>ia = 0..<dim_vec a. (if i = ia then 1 else 0) * z $ ia) = z $ i" 
      by auto
    then show ?thesis unfolding mult_mat_vec_def gen_svp_basis_def scalar_prod_def 
      using True assms by auto
  next
  case False
    then have "i = dim_vec a" using 2 by auto
    then show ?thesis unfolding gen_svp_basis_def using assms 
      by (auto simp add: scalar_prod_def sum_distrib_left mult.commute mult.left_commute)
  qed
qed

lemma gen_svp_basis_mult_last: 
  assumes "dim_vec z = dim_vec a + 1"
  shows "((gen_svp_basis a k) *\<^sub>v z) $ (dim_vec a) = 
         (k+1) * (\<Sum> i \<in> {0 ..< dim_vec a}. z $ i * a $ i) + 
              (k*(k+1)* (\<Sum> i \<in> {0 ..< dim_vec a}. a $ i) +1) * (z$(dim_vec a))"
using gen_svp_basis_mult[OF assms] by auto


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
         else k * (k + 1) * real_of_int (sum (($) a) {0..<dim_vec a}) + 1) \<bullet> z" 
      unfolding gen_svp_basis_def by auto
    also have "\<dots> =  (k * (k + 1) * real_of_int (sum (($) a) {0..<dim_vec a}) + 1 ) * (z$dim_vec a)"
      unfolding scalar_prod_def using suc_dim_a_dim_z using z_upto_last by auto
    finally have "0 = (k * (k + 1) * real_of_int (sum (($) a) {0..<dim_vec a}) + 1 ) * 
                      (z$dim_vec a)" by blast
    moreover have "(k * (k + 1) * real_of_int (sum (($) a) {0..<dim_vec a}) + 1 ) \<noteq> 0"

(*Problems here when changing 2*(k+1) to k*(k+1). 
  This is necessary since k'a only is smaller than k'' under the assumtion that z$i\<le>k, not z$i\<le>2.*)

    proof (safe)
      assume ass: "(k * (k + 1) * real_of_int (sum (($) a) {0..<dim_vec a}) + 1 ) = 0"
      then show False using assms  sorry
        by (smt (z3) ass assms divide_less_eq_1_pos mult_minus_right nonzero_mult_div_cancel_left 
          of_int_hom.hom_one of_int_less_iff of_int_minus)
    qed
    ultimately show ?thesis by auto
  qed
  ultimately have "z$i =  0" if "i < dim_vec z" for i using that suc_dim_a_dim_z
    by (metis discrete le_eq_less_or_eq verit_comp_simplify1(3))
  then show ?case by auto
qed

lemma real_of_int_abs:
  "\<bar>real_of_int x\<bar> = real_of_int \<bar>x\<bar>" 
by auto

lemma mono_real_of_int[simp]:
  "mono real_of_int"
unfolding mono_def by auto

lemma insert_set_comprehension:
  "insert (f x) {f i |i. i<(x::nat)} = {f i | i. i<x+1}"
using less_SucE by fastforce

lemma bhle_k_pos:
  assumes "(a,k) \<in> bhle"
  shows "k>0"
using assms unfolding bhle_def 
proof (safe, goal_cases)
case (1 v)
  have "\<exists>i<dim_vec v. \<bar>v $ i\<bar> > 0" using 1 by auto
  then have "infnorm v > 0" unfolding infnorm_def using 1 by (subst Max_gr_iff, auto)
  then show ?thesis using 1 by auto
qed 



text \<open>Well-definedness of reduction function\<close>

lemma well_defined_reduction_svp:
  assumes "(a,k) \<in> bhle"
  shows "reduce_svp_bhle (a,k) \<in> gap_svp"
using assms unfolding reduce_svp_bhle_def gap_svp_def bhle_def
proof (safe, goal_cases)
  case (1 x)
  have "k>0" using assms bhle_k_pos by auto
  then show ?case using is_lattice_gen_lattice is_indep_gen_svp_basis by auto
next
  case (2 x)
  let ?x = "vec (dim_vec x + 1) (\<lambda>i. if i< dim_vec x then x$i else 0)"
  define v where "v = (gen_svp_basis a k) *\<^sub>v (real_of_int_vec ?x)"
  have eigen_v: "v = real_of_int_vec ?x" unfolding v_def 
  proof (subst gen_svp_basis_mult[where a= a and k=k and z="real_of_int_vec ?x"],
         auto simp add: 2(2) real_of_int_vec_vec comp_def, subst vec_eq_iff,
         auto simp add: 2(1) scalar_prod_def, goal_cases one two)
    case (one i)
    then show ?case by (subst real_of_int_vec_vec, auto simp add: comp_def 2(2))
  next
    case (two i)
    have "(\<Sum>i = 0..<dim_vec a. real_of_int (x $ i) * real_of_int (a $ i)) = 0" 
      using 2 unfolding scalar_prod_def
      by (smt (verit) mult.commute of_int_hom.hom_zero of_int_mult of_int_sum sum.cong)
    then show ?case using 2 by auto
  qed
  have "dim_vec ?x = dim_col (gen_svp_basis a k)" 
    using 2(2) unfolding gen_svp_basis_def by auto
  then have "v \<in> gen_lattice (gen_svp_basis a k)"  
    unfolding v_def gen_lattice_def by auto
  moreover have "infnorm v \<le> k" 
  proof -
    have "infnorm v \<le> infnorm x" 
    proof (subst eigen_v, auto simp add: infnorm_def, subst Max.boundedI, goal_cases)
    case (3 b)
      have dim_x_nonzero: "dim_vec x \<noteq> 0" using 2(3) by auto
      then have nonempty: "(\<exists>a\<in>{\<bar>x $ i\<bar> |i. i < dim_vec x}. 0 \<le> a)"
        using abs_ge_zero by blast
      have " \<bar>real_of_int (x $ i)\<bar> \<le> real_of_int (Max {\<bar>x $ j\<bar> |j. j < dim_vec x})" 
        if "i < dim_vec x" for i 
      using that by (subst real_of_int_abs, subst of_int_le_iff, subst Max_ge, auto)
      moreover have "0 \<le> Max {\<bar>x $ i\<bar> |i. i < dim_vec x}" using 2 nonempty
        by (subst Max_ge_iff, auto)
      ultimately show ?case using 3 by auto
    qed auto
    then show ?thesis using 2 by auto
  qed
  moreover have "v \<noteq> 0\<^sub>v (dim_vec v)" using 2(3) 
  proof (subst eigen_v, safe) 
    assume fst: "x \<noteq> 0\<^sub>v (dim_vec x)" 
    assume snd: "real_of_int_vec ?x = 0\<^sub>v (dim_vec v)"
    have "x$i = 0" if "i< dim_vec x" for i using snd
    by (smt (z3) add.commute dim_vec eigen_v index_map_vec(2) index_vec index_zero_vec(1) 
      of_int_eq_iff of_int_hom.hom_zero real_of_int_vec_def real_of_int_vec_nth that 
      trans_less_add2)
    then show False using fst by auto
  qed
  ultimately show ?case by blast
qed





text \<open>NP-hardness of reduction function\<close>

lemma NP_hardness_reduction_svp:
  assumes "reduce_svp_bhle (a,k) \<in> gap_svp"
  shows "(a,k) \<in> bhle"
using assms unfolding reduce_svp_bhle_def gap_svp_def bhle_def
proof (safe, goal_cases)
  case (1 v)
  have "k>0" using 1(4) 1(3) unfolding infnorm_def 
  proof -
    have "\<exists>i<dim_vec v. \<bar>v $ i\<bar> > 0" using 1(4) by auto
    then have "infnorm v > 0" unfolding infnorm_def using 1(4) by (subst Max_gr_iff, auto)
    then show ?thesis using 1(3) by auto
  qed
  obtain z where z_def:
    "v = (gen_svp_basis a k) *\<^sub>v real_of_int_vec z" 
    "dim_vec z = dim_vec a + 1"
    using 1(2) unfolding gen_lattice_def gen_svp_basis_def by auto
  have dim_v_dim_a:"dim_vec v = dim_vec a + 1" 
    using 1 unfolding gen_lattice_def gen_svp_basis_def by auto
  define x where "x = vec (dim_vec a) (($) z)"
  have "v $ i = z $ i" if "i< dim_vec a" for i 
    by (subst z_def) (subst gen_svp_basis_mult; use that z_def in \<open>auto\<close>)
  have v_le_k: "\<bar>v $ i\<bar> \<le> k" if "i< dim_vec a + 1" for i
    using 1(3) dim_v_dim_a that unfolding infnorm_def
    using Max_le_iff[of "{\<bar>v $ i\<bar> |i. i < dim_vec v}" k]
    by fastforce
  have v_last_zero: "v$(dim_vec a) = 0"
  proof (rule ccontr)
    assume ccontr_assms:"v $ dim_vec a \<noteq> 0"
    have v_last: "v$(dim_vec a) = 
      (k+1) * (\<Sum>i = 0..<dim_vec a. real_of_int (z $ i) * real_of_int (a $ i)) +
      (k* (k+1) * (\<Sum>x = 0..<dim_vec a. real_of_int (a $ x)) + 1) * (z $ dim_vec a) "
      (is "v$(dim_vec a) = ?first + ?second")
    by (subst z_def(1), subst gen_svp_basis_mult_last, use z_def  in \<open>auto\<close>)
    then have "?first \<noteq> 0 \<or> ?second \<noteq> 0"
      using ccontr_assms by auto
    then consider 
      (first) "?first \<noteq> 0 \<and> ?second = 0" | 
      (second) "?second \<noteq> 0 \<and> ?first = 0" |
      (both) "?first \<noteq> 0 \<and> ?second \<noteq> 0"
      by blast
    then show False 
    proof (cases)
      case first
      then have "\<bar>\<Sum>i = 0..<dim_vec a. real_of_int (z $ i) * real_of_int (a $ i)\<bar>\<noteq>0" 
        using \<open>k>0\<close> by auto
      then have "\<bar>\<Sum>i = 0..<dim_vec a. (z $ i) * (a $ i)\<bar>\<noteq>0" 
        by (smt (verit) of_int_hom.hom_zero of_int_mult of_int_sum sum.cong)
      then have "\<bar>\<Sum>i = 0..<dim_vec a.  (z $ i) *  (a $ i)\<bar>\<ge>1" by auto
      then have gr_1: "\<bar>\<Sum>i = 0..<dim_vec a. real_of_int (z $ i) * real_of_int (a $ i)\<bar> \<ge> 1" 
        using of_int_1_le_iff[of "\<bar>\<Sum>i = 0..<dim_vec a. z $ i * a $ i\<bar>"] 
        by auto
      have "\<bar>v$ dim_vec a\<bar> = \<bar>?first\<bar>" using first v_last by auto
      also have "\<dots> = (k+1) * \<bar>\<Sum>i = 0..<dim_vec a. real_of_int (z $ i) * real_of_int (a $ i)\<bar>"
        using \<open>k>0\<close>
        by (smt (verit, best) linordered_semiring_strict_class.mult_pos_pos mult_minus_right)
      also have "\<dots> > k" using first gr_1 \<open>k>0\<close>
      by (smt (verit, best) divide_less_eq_1_pos nonzero_mult_div_cancel_left)
      finally have "\<bar>v$ dim_vec a\<bar> > k" by auto
      then show ?thesis using v_le_k[of "dim_vec a"] by auto
    next
      case second
      then show ?thesis sorry
    next
      case both
      then show ?thesis sorry
    qed



find_theorems of_int "_\<le>_"


  have z_last_zero: "z$(dim_vec a) = 0" sorry

  have v_real_z: "v = real_of_int_vec z" sorry
  have "dim_vec a > 0" sorry

  have "a \<bullet> x = 0" 
  proof -
    have "0 = ((gen_svp_basis a k) *\<^sub>v real_of_int_vec z) $ (dim_vec a)" 
      using v_last_zero z_def by auto
    also have "\<dots> = (k+1) * (\<Sum> i \<in> {0 ..< dim_vec a}. z $ i * a $ i)" 
      by (subst gen_svp_basis_mult, auto simp add: z_def z_last_zero)
    finally have zero: "(k+1) * (\<Sum> i \<in> {0 ..< dim_vec a}. z $ i * a $ i) = 0" by auto
    then show ?thesis unfolding scalar_prod_def using x_def \<open>k>0\<close>
    by (smt (verit, ccfv_SIG) atLeastLessThan_iff dim_vec index_vec mult.commute
       mult_eq_0_iff of_int_hom.hom_0 sum.cong)
  qed
  moreover have "dim_vec x = dim_vec a" unfolding x_def by auto
  moreover have "x \<noteq> 0\<^sub>v (dim_vec x)" 
  proof -
    have "\<exists>i< dim_vec a + 1. v$i \<noteq> 0" using 1 unfolding gen_lattice_def gen_svp_basis_def by auto
    then have "\<exists>i< dim_vec a. v$i \<noteq> 0" using v_last_zero
      by (metis add_le_cancel_right discrete nat_less_le)
    then obtain i where "i<dim_vec a" "v$i\<noteq>0" by blast
    then have "real_of_int (z$i) \<noteq> 0" using v_real_z z_def 
      by (subst real_of_int_vec_nth[symmetric], auto)
    then have "\<exists>i< dim_vec a. x$i \<noteq> 0" using x_def \<open>i<dim_vec a\<close> by auto
    then show ?thesis using x_def by auto
  qed
  moreover have "real_of_int (infnorm x) \<le> k"
  proof - 
    have zs: "\<bar>z$i\<bar> = \<bar>vec (dim_vec a) (($) z) $ i\<bar>" if "i < dim_vec a" for i using that by auto
    have "real_of_int (Max {\<bar>vec (dim_vec a) (($) z) $ i\<bar> |i. i < dim_vec a}) =
               Max (real_of_int ` {\<bar>vec (dim_vec a) (($) z) $ i\<bar> |i. i < dim_vec a})" 
      using \<open>dim_vec a > 0\<close>
      by (subst mono_Max_commute[of real_of_int]) auto
    also have "\<dots> = Max {\<bar>real_of_int (z $ i)\<bar> |i. i < dim_vec a}" 
      using  zs by (subst real_of_int_abs)(smt (z3) Collect_cong Setcompr_eq_image mem_Collect_eq)
    also have "\<dots> = Max {\<bar>real_of_int (z $ i)\<bar> |i. i < dim_vec a + 1}" 
    proof -
      have "Max {\<bar>real_of_int (z $ i)\<bar> |i. i < dim_vec a} \<ge> 0" 
        using \<open>dim_vec a >0\<close> by (subst Max_ge_iff, auto)
      then have "Max {\<bar>real_of_int (z $ i)\<bar> |i. i < dim_vec a} \<ge> \<bar>real_of_int (z$dim_vec a)\<bar>"
        using z_last_zero by simp
      then have "Max {\<bar>real_of_int (z $ i)\<bar> |i. i < dim_vec a} = 
        Max (insert ( \<bar>real_of_int (z$dim_vec a)\<bar>) {\<bar>real_of_int (z $ i)\<bar> |i. i < dim_vec a})"
        using \<open>dim_vec a > 0\<close> by (subst Max_insert, auto)
      then show ?thesis 
        using insert_set_comprehension[of "(\<lambda>i. \<bar>real_of_int (z $ i)\<bar>)" "dim_vec a"] by auto
    qed
    also have "\<dots> = Max {\<bar>real_of_int_vec z $ i\<bar> |i. i < Suc (dim_vec a)}"
    proof -
      have "real_of_int (z $ i) = real_of_int_vec z $ i" if "i < Suc (dim_vec a)" for i
        using real_of_int_vec_nth[symmetric] z_def(2) that by auto
      then show ?thesis
        by (metis (no_types, hide_lams) One_nat_def add.commute add.right_neutral add_Suc)
    qed
    finally have "real_of_int (Max {\<bar>vec (dim_vec a) (($) z) $ i\<bar> |i. i < dim_vec a}) =
                  Max {\<bar>real_of_int_vec z $ i\<bar> |i. i < Suc (dim_vec a)}"
      by blast
    then have "real_of_int (infnorm x) = infnorm v" 
      using x_def z_def v_real_z unfolding infnorm_def by auto
    then show ?thesis using 1(3) by auto
  qed
  ultimately show ?case by blast
qed



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