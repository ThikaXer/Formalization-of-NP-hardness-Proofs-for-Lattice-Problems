theory SVP

imports Subset_Sum
        Lattice_vec
        infnorm

begin

text \<open>The reduction of SVP to Subset Sum in $l_\infty$ norm\<close>

text \<open>The shortest vector problem.\<close>
definition is_shortest_vec :: "lattice  \<Rightarrow> real vec \<Rightarrow> bool" where
  "is_shortest_vec L v \<equiv> (is_lattice L) \<and> (\<forall>x\<in>L. infnorm (x) \<ge> infnorm (v) \<and> v\<in>L) "


text \<open>The decision problem associated with solving SVP exactly.\<close>
definition gap_svp :: "(lattice \<times> real) set" where
  "gap_svp \<equiv> {(L, r). (is_lattice L) \<and> (\<exists>v\<in>L. infnorm v \<le> r \<and> v \<noteq> 0\<^sub>v (dim_vec v))}"

text \<open>Generate a lattice to solve SVP for reduction\<close>

definition gen_basis_svp :: "int vec \<Rightarrow> int \<Rightarrow> real mat" where
  "gen_basis_svp as s = mat (dim_vec as + 1) (dim_vec as + 1) (\<lambda> (i, j). 
    if i = 0 then (if j<dim_vec as then 2 * as$j else 2*s) 
    else (if j = dim_vec as then 1 else (if i = j + 1 then 2 else 0)))"


text \<open>Reduction SVP to CVP in $l_\infty$ norm.\<close>
definition reduce_svp_subset_sum:: "(int vec \<times> int) \<Rightarrow> (lattice \<times> real)" where
  "reduce_svp_subset_sum \<equiv> (\<lambda> (as,s). (gen_lattice (gen_basis_svp as s), 1))"














(*CVP*)


text \<open>Lemmas for Proof\<close>

lemma vec_lambda_eq[intro]: "(\<forall>i<n. a i = b i) \<longrightarrow> vec n a = vec n b"
by auto

lemma eq_fun_applic: assumes "x = y" shows "f x = f y"
using assms by auto


lemma sum_if_zero:
  assumes "finite A" "i\<in>A"
  shows "(\<Sum>j\<in>A. (if i = j then a j else 0)) = a i"
proof -
  have "(\<Sum>x\<in>A. if x = i then a x else 0) =
  (if i = i then a i else 0) + (\<Sum>x\<in>A - {i}. if x = i then a x else 0)"
  using sum.remove[OF assms, of "(\<lambda>x. if x = i then a x else 0)"] by auto
  then show ?thesis by (simp add: assms(1))
qed



lemma Max_real_of_int:
  assumes "finite A" "A\<noteq>{}"
  shows "Max (real_of_int ` A) = real_of_int (Max A)"
using mono_Max_commute[OF _ assms, of real_of_int]  by (simp add: mono_def)

lemma set_compr_elem: 
  assumes "finite A" "a\<in>A"
  shows "{f i | i. i\<in>A} = {f a} \<union> {f i | i. i\<in>A-{a}}"
by (safe, use assms in \<open>auto\<close>)


lemma row_gen_basis_svp: 
  assumes "i>0" "i<dim_vec as + 1"
  shows "row (gen_basis_svp as s) i = vec (dim_vec as + 1) 
           (\<lambda>j. (if j = dim_vec as then 1 else (if i = j + 1 then 2 else 0)))"
unfolding gen_basis_svp_def using assms by auto

lemma Bx_rewrite_real: 
  assumes x_dim: "dim_vec x = dim_vec as + 1"
  shows "(gen_basis_svp as s) *\<^sub>v x = 
    vec (dim_vec as + 1) (\<lambda> i. if i = 0 then 
       (2 * (\<Sum>i<dim_vec as. x $ i * of_int (as $ i)) + 2 * x $ (dim_vec as) * of_int s)
    else (2 * x$(i-1) + x$(dim_vec as)))"
    (is "?init_vec = ?goal_vec")
proof (intro eq_vecI, goal_cases)
  case (1 i)
  show ?case
  proof (cases "i=0")
    case True
    have fact: "(\<Sum>i = 0..<dim_vec as. 2 * of_int (as $ i) * (x $ i)) =
          (\<Sum>n<dim_vec as. 2 * ((x $ n) * of_int (as $ n)))"
    by (subst sum.cong, auto)
    show ?thesis unfolding gen_basis_svp_def mult_mat_vec_def scalar_prod_def using True assms
      by (auto simp add: sum_distrib_left fact)
  next
    case False
    have "(\<Sum>ia=0..<dim_vec as. real_of_int (if i = ia+1 then 2 else 0) *  (x $ ia)) =
          (\<Sum>ib=1..<dim_vec as+1. real_of_int (if i = ib then 2 else 0) *  (x $ (ib-1)))"
      using sum.atLeastLessThan_shift_0[of 
      "(\<lambda>ib. real_of_int (if i = ib then 2 else 0) * (x $ (ib - 1)))" 
      1 "dim_vec as + 1"] by auto
    also have "\<dots> = (\<Sum>ib=1..<dim_vec as+1. (if i = ib then 2*x $ (ib-1) else 0))" 
    proof -
      have "(\<forall>n. (0 = real_of_int (if i = n then 2 else 0) * x $ (n - 1) \<or> i = n) \<and> 
        (2 * x $ (n - 1) = real_of_int (if i = n then 2 else 0) * x $ (n - 1) \<or> i \<noteq> n)) \<or> 
        (\<Sum>n = 1..<dim_vec as + 1. real_of_int (if i = n then 2 else 0) * x $ (n - 1)) = 
        (\<Sum>n = 1..<dim_vec as + 1. if i = n then 2 * x $ (n - 1) else 0)"
        by fastforce
      then show ?thesis
        by (metis (no_types))
    qed
    also have "\<dots> =  2*x $ (i-1)" using 1 False by (subst sum_if_zero) auto
    finally have "(\<Sum>ia=0..<dim_vec as. real_of_int (if i = ia+1 then 2 else 0) * (x $ ia)) =
      2 * (x $ (i - 1))" by auto
    then show ?thesis unfolding gen_basis_svp_def mult_mat_vec_def scalar_prod_def 
      using 1 False assms by auto
  qed
qed (auto simp add: gen_basis_svp_def)

lemma Bx_rewrite: 
  assumes x_dim: "dim_vec x = dim_vec as + 1"
  shows "(gen_basis_svp as s) *\<^sub>v (real_of_int_vec x) = 
    vec (dim_vec as + 1) (\<lambda> i. if i = 0 then 
      real_of_int (2 * (\<Sum>i<dim_vec as. x $ i * as $ i) + 2 * x $ (dim_vec as) * s)
    else real_of_int (2 * x$(i-1) + x$(dim_vec as)))"
    (is "?init_vec = ?goal_vec")
using Bx_rewrite_real[of "real_of_int_vec x"] assms by auto




(*
text \<open>gen_basis_svp actually generates a basis which is spans the lattice (by definition) and 
  is linearly independent.\<close>


lemma is_indep_gen_basis_svp:
  "is_indep (gen_basis_svp as s)"
oops
  This statement is not true for general as, s. The columns might not be linearly independent 
  over R, but might still generate a unique lattice
unfolding is_indep_def 
proof (safe, goal_cases)
case (1 z)
  have z_dim: "dim_vec z = dim_vec as + 1" using 1(2) unfolding gen_basis_svp_def by auto
  have dim_row: "dim_row (gen_basis_svp as s) = dim_vec as + 1" unfolding gen_basis_svp_def by auto
  have eq: "gen_basis_svp as s *\<^sub>v z = vec (dim_vec as + 1) (\<lambda> i. if i = 0 then 
       (2 * (\<Sum>i<dim_vec as. z $ i * of_int (as $ i)) + 2 * z $ (dim_vec as) * of_int s)
    else (2 * z$(i-1) + z$(dim_vec as)))" 
  using Bx_rewrite_real z_dim by auto
  have "\<dots> = 0\<^sub>v (dim_vec as + 1)" using 1(1) dim_row by (subst eq[symmetric], auto) 
  then have "2 * z$(i-1) + z$(dim_vec as) = 0" if "1<i" and "i<dim_vec as + 1" for i 
    using that by (smt (verit, best) cancel_comm_monoid_add_class.diff_cancel 
      empty_iff index_vec index_zero_vec(1) insert_iff not_less_zero zero_less_diff)
  then have "z$i = 0" if "i<dim_vec as" for i using that sorry
  then show ?case using 1 z_dim unfolding gen_basis_svp_def by auto
qed
*)







text \<open>The Gap-SVP is NP-hard in l_infty.\<close>

lemma well_defined_reduction: 
  assumes "(as, s) \<in> subset_sum"
  shows "reduce_svp_subset_sum (as, s) \<in> gap_svp"
proof -
  obtain x where
    x_dim: "dim_vec x = dim_vec as" and
    x_binary: "\<forall>i<dim_vec x. x $ i \<in> {0, 1}" and 
    x_lin_combo: "x \<bullet> as = s" 
    using assms unfolding subset_sum_def by blast
  define L where L_def: "L = fst (reduce_svp_subset_sum (as, s))"
  define B where "B = gen_basis_svp as s"
  define v where "v = real_of_int_vec (
      vec (dim_vec as + 1) (\<lambda>i. if i<dim_vec as then x $ i else -1))"
  then have v_dim: "dim_vec v = dim_vec as + 1" by auto
  have v_last: "v$(dim_vec as) = -1" unfolding v_def by auto  
  have init_eq_goal: "B *\<^sub>v v = 
    vec (dim_vec as + 1) (\<lambda> i. if i = 0 then 
       (2 * (\<Sum>i<dim_vec as. of_int (x$i) * of_int (as$i)) - 2 * of_int s) 
       else (2 * of_int (x$(i-1)) -1))"
    (is "?init_vec = ?goal_vec")
  unfolding B_def reduce_svp_subset_sum_def by (subst Bx_rewrite_real[OF v_dim], subst v_last)+
     (intro eq_vecI, auto simp add: v_def)

  have "infnorm (B *\<^sub>v v) = 
    Max ({real_of_int \<bar>2 * (\<Sum>i<dim_vec as. x $ i * as $ i) - 2 * s\<bar>} \<union> 
      {real_of_int \<bar>2 *(x$(i-1)) - 1\<bar> | i. 1\<le>i \<and> i<dim_vec as + 1 })"
  proof -
    let ?v = "vec (Suc (dim_vec as))
           (\<lambda>i. if i = 0 then 2 * (\<Sum>i<dim_vec as. real_of_int (x $ i) * real_of_int (as $ i)) -
              2 * real_of_int s else 2 * real_of_int (x $ (i - 1)) - 1)"
    have "dim_vec as > 0" using assms unfolding subset_sum_def by auto
    then have "{i. i<dim_vec as +1} = {0} \<union> {i. i \<in> {1..<dim_vec as + 1}}" by auto
    then have "{\<bar>?v $ i\<bar> | i. i < Suc (dim_vec as)} = 
      {\<bar>?v $ 0\<bar>} \<union> {\<bar>?v $ i\<bar> | i. i \<in> {1..< Suc (dim_vec as)}}"
    proof -
      have "{\<bar>?v $ i\<bar> | i. i < Suc (dim_vec as)} = (\<lambda>i. \<bar>?v $ i\<bar>) ` {0..< Suc (dim_vec as)}"
        using \<open>dim_vec as >0\<close> lessThan_atLeast0 by blast
      also have "\<dots> = (\<lambda>i. \<bar>?v $ i\<bar>) ` ({0} \<union> {1..< Suc (dim_vec as)})"
        by (simp add: atLeast0_lessThan_Suc_eq_insert_0)
      also have "\<dots> = ((\<lambda>i. \<bar>?v $ i\<bar>) ` {0}) \<union> ((\<lambda>i. \<bar>?v $ i\<bar>) ` {1..< Suc (dim_vec as)})"
        by blast
      also have "\<dots> = {\<bar>?v $ 0\<bar>} \<union> {\<bar>?v $ i\<bar> | i. i \<in> {1..< Suc (dim_vec as)}}"
        by blast
      finally show ?thesis by blast
    qed
    also have "\<dots> = {\<bar>2 * (\<Sum>i<dim_vec as. real_of_int (x $ i) * real_of_int (as $ i)) - 
        2 * real_of_int s\<bar>} \<union>
        {\<bar>2 * real_of_int (x $ (i - Suc 0)) - 1\<bar> |i. i \<in> {1..< Suc (dim_vec as)}}"
    proof -
      have "?v $ i = 2 * real_of_int (x $ (i - Suc 0)) - 1" 
        if "i \<in> {1..< Suc (dim_vec as)}" for i
        using that by auto
      then have "{\<bar>?v $ i\<bar> | i. i \<in> {1..< Suc (dim_vec as)}} = 
        {\<bar>2 * real_of_int (x $ (i - Suc 0)) - 1\<bar> |i. i \<in> {1..< Suc (dim_vec as)}}" by force
      then show ?thesis by auto
    qed
    also have "{\<bar>2 * real_of_int (x $ (i - Suc 0)) - 1\<bar> |i. i \<in> {1..< Suc (dim_vec as)}} = 
       {\<bar>2 * real_of_int (x $ (i - Suc 0)) - 1\<bar> |i. 1 \<le> i \<and> i < Suc (dim_vec as)}" 
      using atLeastLessThan_iff by blast
    finally have "{\<bar>?v $ i\<bar>| i. i < Suc (dim_vec as)} = 
      insert \<bar>2 * (\<Sum>i<dim_vec as. real_of_int (x $ i) * real_of_int (as $ i)) - 2 * real_of_int s\<bar>
          {\<bar>2 * real_of_int (x $ (i - Suc 0)) - 1\<bar> |i. 1 \<le> i \<and> i < Suc (dim_vec as)}" 
      by blast
    then show ?thesis by (subst init_eq_goal) (auto simp add: infnorm_def)
  qed
  also have  "\<dots> \<le> 1"
  proof -
    have elem: "x$(i-1)\<in>{0,1}" if "1\<le>i \<and> i<dim_vec as+1" for i 
      using that x_binary x_dim
      by (metis One_nat_def Suc_eq_plus1 Suc_le_mono Suc_pred less_eq_Suc_le)
    then have "\<bar>2*x$(i-1)-1\<bar> = 1" if "1\<le>i \<and> i<dim_vec as+1" for i 
      using elem[OF that] by auto
    then have "{real_of_int \<bar>2 * x $ (i - 1) - 1\<bar> |i. 1 \<le> i \<and> i < dim_vec as + 1} \<subseteq> {1}" 
      by (safe, auto)
    moreover have "\<bar>2 * (\<Sum>i<dim_vec as. x $ i * as $ i) - 2 * s\<bar> = 0" 
      using x_lin_combo unfolding scalar_prod_def using lessThan_atLeast0 by auto
    ultimately show ?thesis by auto
  qed
  finally have "infnorm (B *\<^sub>v v) \<le> 1" by blast
  moreover have "B *\<^sub>v v\<in>L" 
  proof -
    have "dim_vec v = dim_col (gen_basis_svp as s)" unfolding gen_basis_svp_def using v_dim by auto
    then show ?thesis
      unfolding L_def reduce_svp_subset_sum_def v_def gen_lattice_def B_def by auto
  qed
  moreover have "B *\<^sub>v v \<noteq> 0\<^sub>v (dim_vec (B *\<^sub>v v))"
  proof - 
    have "dim_vec as \<noteq> 0" using assms unfolding subset_sum_def by simp
    then have "dim_vec as > 0" by auto
    then have elem: "?goal_vec $ 1 = 2 * real_of_int (x $ 0) - 1" by simp
    then have "(B *\<^sub>v v)$1 \<noteq> 0" by (subst init_eq_goal, subst elem)
      (use \<open>0 < dim_vec as\<close> x_dim x_binary in \<open>fastforce\<close>)
    moreover have "0\<^sub>v (dim_vec (B *\<^sub>v v)) $ 1 = 0" 
      using \<open>dim_vec as > 0\<close> index_zero_vec(1)[of "1" "dim_vec as + 1" ] 
      by (subst init_eq_goal) auto
    ultimately show ?thesis by auto
  qed
  ultimately have witness: "\<exists>z\<in>L. infnorm z \<le> 1 \<and> z \<noteq> 0\<^sub>v (dim_vec z)" by auto
  have int_mat: "\<exists>B'::int mat. B = real_of_int_mat B'"
  proof -
    define B' where "B' = mat (dim_vec as + 1) (dim_vec as + 1)
          (\<lambda>x. (case x of (i, j) \<Rightarrow>
             if i = 0 then if j < dim_vec as then 2 * as $ j else 2 * s
             else if j = dim_vec as then 1 else if i = j + 1 then 2 else 0))"
    then have "real_of_int_mat B' = B" using real_of_int_mat_mat 
      unfolding B_def gen_basis_svp_def by auto
    then show ?thesis  by auto
  qed
  have L_lattice: "is_lattice L" unfolding L_def reduce_svp_subset_sum_def
    using is_lattice_gen_lattice_int[OF int_mat] unfolding B_def by auto
  show ?thesis unfolding gap_svp_def 
    using L_lattice witness L_def
    by (metis (mono_tags, lifting) fstI mem_Collect_eq old.prod.case reduce_svp_subset_sum_def)
qed

lemma NP_hardness_reduction:
  assumes "reduce_cvp_subset_sum (as, s) \<in> gap_cvp"
  shows "(as, s) \<in> subset_sum"
proof -
  define n where "n = dim_vec as"
  define B where "B = gen_basis_svp as s"
  define L where "L = gen_lattice B"
  define b where "b = gen_t as s"
  have ex_v: "\<exists>v\<in>L. infnorm (v - b) \<le> 1" and is_lattice: "is_lattice L"
    using assms unfolding gap_cvp_def reduce_cvp_subset_sum_def L_def B_def b_def by auto
  then obtain v where v_in_L:"v\<in>L" and ineq:"infnorm (v - b) \<le> 1" by blast
  have "\<exists>zs::int vec. v = B *\<^sub>v (real_of_int_vec zs) \<and> dim_vec zs = dim_vec as"
  using v_in_L unfolding L_def gen_lattice_def B_def gen_basis_svp_def by auto
  then obtain zs::"int vec" where v_def: "v = B *\<^sub>v (real_of_int_vec zs)" 
    and zs_dim: "dim_vec zs = dim_vec as" by blast
  have init_eq_goal: "v - b = 
    vec (n+2) (\<lambda> i. if i = 0 then real_of_int (zs \<bullet> as - s - 1) else (
      if i = 1 then real_of_int (zs \<bullet> as - s + 1) else real_of_int (2 * zs$(i-2) - 1)))"
    (is "?init_vec = ?goal_vec")
  unfolding v_def B_def b_def using Bx_s_rewrite[OF zs_dim[symmetric]] n_def by simp
  have infnorm_ineq: "infnorm (v-b) = Max ({real_of_int \<bar>zs \<bullet> as - s - 1\<bar>} \<union> 
    {real_of_int \<bar>zs \<bullet> as - s + 1\<bar>} \<union> {real_of_int \<bar>2*zs$(i-2)-1\<bar> | i. 1<i \<and> i<n+2 })"
  unfolding v_def B_def b_def using infnorm_Bx_s[OF zs_dim[symmetric]] n_def by simp

  have Max_le_1: "Max ({real_of_int \<bar>zs \<bullet> as - s - 1\<bar>} \<union> 
    {real_of_int \<bar>zs \<bullet> as - s + 1\<bar>} \<union>  {real_of_int \<bar>2*zs$(i-2)-1\<bar> | i. 1<i \<and> i<n+2 })\<le>1"
  using ineq by (subst infnorm_ineq[symmetric])
  have "\<bar>2*zs$(i-2)-1\<bar>\<le>1" if "1<i \<and> i<n+2" for i using Max_le_1 that by auto
  then have "zs$(i-2) = 0 \<or> zs$(i-2) = 1" if "1<i \<and> i<n+2" for i
    using that by force
  then have "zs$i = 0 \<or> zs$i = 1" if "i<n" for i using that
    by (metis One_nat_def Suc_less_eq add_2_eq_Suc' add_diff_cancel_right' zero_less_Suc)
  then have "\<forall>i<n. zs $ i \<in> {0, 1}" by simp 
  moreover have "zs \<bullet> as = s" using Max_le_1 by auto
  ultimately have "(\<forall>i<dim_vec zs. zs $ i \<in> {0, 1}) \<and> zs \<bullet> as = s \<and> dim_vec zs = dim_vec as"
     using zs_dim n_def by auto
  then show ?thesis unfolding subset_sum_def gap_cvp_def by auto
qed




lemma "is_reduction reduce_cvp_subset_sum subset_sum gap_cvp"
unfolding is_reduction_def
proof (safe, goal_cases)
  case (1 as s)
  then show ?case using well_defined_reduction by auto
next
  case (2 as s)
  then show ?case using NP_hardness_reduction by auto
qed















(*OLD*)
text \<open>Lemmas for proof\<close>

find_theorems "_ *\<^sub>v _ = _"

find_theorems "_$_ = _$_"

value "(vec_of_list [0,1,2::nat])$2"


lemma is_lattice_gen_svp_lattice:
  assumes "is_lattice L" "b\<notin>L" "dim_lattice L = dim_vec b"
  shows "is_lattice (gen_svp_lattice L b)"
proof -
  obtain B where 
    span_B: "L = {B *\<^sub>v real_of_int_vec z |z. dim_vec z = dim_col B}" and
    is_indep_B: "is_indep B" 
    using assms unfolding is_lattice_def by blast
  have dim_B_dim_b: "dim_row B = dim_vec b" sorry

  define B' where B'_def:
    "B' = mat (dim_row B) (dim_col B +1) (\<lambda>(i,j). if j< dim_col B then B $$ (i,j) else b $ i)"

  have "gen_svp_lattice L b = {B' *\<^sub>v real_of_int_vec z |z. dim_vec z = dim_col B'}" 
  proof (safe, goal_cases)
  case (1 a)
    obtain v x where a_def: "a = v + real_of_int x \<cdot>\<^sub>v b" "v \<in> L" "dim_vec v = dim_vec b" 
      using 1 unfolding gen_svp_lattice_def by blast
    then have a_dim: "dim_vec b = dim_row B" using span_B by auto
    obtain y where v_def: "v = B *\<^sub>v real_of_int_vec y" and y_dim: "dim_vec y = dim_col B" 
      using \<open>v\<in>L\<close> unfolding span_B by auto 
    define z where "z = vec (dim_vec y + 1) (\<lambda>i. if i< dim_vec y then y$i else x)"
    have "a = B' *\<^sub>v real_of_int_vec z" 
      unfolding B'_def z_def mult_mat_vec_def a_def v_def
      by (subst vec_eq_iff, auto simp add: a_dim y_dim scalar_prod_def)
    moreover have "dim_vec z = dim_col B'" unfolding B'_def z_def by (auto simp add: y_dim)
    ultimately show ?case unfolding gen_svp_lattice_def by blast
  next
  case (2 x z)
    have dim_z_dim_B: "dim_vec z = dim_col B + 1" using 2 unfolding B'_def by auto
    have "B' *\<^sub>v (real_of_int_vec z) = 
      B *\<^sub>v vec (dim_col B) (\<lambda>i. z$i) + real_of_int (z$(dim_col B)) \<cdot>\<^sub>v b" 
      (is "?left = ?right")
      unfolding B'_def mult_mat_vec_def using dim_B_dim_b dim_z_dim_B 
      unfolding scalar_prod_def by auto
    moreover have "B *\<^sub>v (vec (dim_col B) (\<lambda>i. z$i)) \<in> L"
    proof -
      have "dim_vec (vec (dim_col B) (\<lambda>i. z$i)) = dim_col B" using span_B by auto
      moreover have "vec (dim_col B) (\<lambda>x. real_of_int (z $ x)) = 
        real_of_int_vec (vec (dim_col B) (\<lambda>x. (z $ x)))" unfolding real_of_int_vec_def by auto
      ultimately show ?thesis using span_B unfolding real_of_int_vec_def by auto
    qed
    moreover have "dim_vec (B *\<^sub>v vec (dim_col B) (\<lambda>i. z$i)) = dim_vec b" 
      unfolding mult_mat_vec_def using \<open>dim_row B = dim_vec b\<close> by auto
    ultimately show ?case unfolding gen_svp_lattice_def by blast
  qed
  then have gen: "gen_svp_lattice L b = gen_lattice B'" unfolding gen_lattice_def by auto

  obtain B'' where "gen_lattice B'' = gen_lattice B'" and "is_indep B''" 
    using get_indep_basis by auto

  then show ?thesis apply (subst gen) unfolding is_lattice_def gen_lattice_def by blast
qed

text \<open>Well-definedness of reduction function\<close>

lemma well_defined_reduction_svp:
  assumes "(L,b,r) \<in> gap_cvp"
  shows "reduce_svp_cvp (L,b,r) \<in> gap_svp"
using assms unfolding reduce_svp_cvp_def gap_svp_def gap_cvp_def
proof (safe, goal_cases)
case (1 v)
  then show ?case 
  proof (cases "b\<in>L")
  case True
    then show ?thesis sorry
  next
  case False
    then show ?thesis using is_lattice_gen_svp_lattice[OF _ \<open>b\<notin>L\<close>] by simp
  qed
next
case (2 v)
then show ?case sorry
qed




text \<open>NP-hardness of reduction function\<close>

lemma NP_hardness_reduction_svp:
  assumes "reduce_svp_cvp (L,b,r) \<in> gap_svp"
  shows "(L,b,r) \<in> gap_cvp"
sorry



text \<open>The Gap-SVP is NP-hard.\<close>
lemma "is_reduction reduce_svp_cvp gap_cvp gap_svp"
unfolding is_reduction_def
proof (safe, goal_cases)
  case (1 as s)
  then show ?case using well_defined_reduction_svp by auto
next
  case (2 as s)
  then show ?case using NP_hardness_reduction_svp by auto
qed



end