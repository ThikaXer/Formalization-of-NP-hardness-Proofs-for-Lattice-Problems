theory CVP_vec

imports Main 
        "poly-reductions/Karp21/Reductions"
        (*"poly-reducrions/Karp21/Three_Sat_To_Set_Cover"*)
        (*Subset_Sum*)
        "Berlekamp_Zassenhaus.Finite_Field"
        "Jordan_Normal_Form.Matrix"
        "Jordan_Normal_Form.Matrix_Kernel"
        "Jordan_Normal_Form.DL_Rank"
        "Jordan_Normal_Form.Complexity_Carrier"
        "Jordan_Normal_Form.Conjugate"
        "Jordan_Normal_Form.Ring_Hom_Matrix"
        "VectorSpace.LinearCombinations"


begin

type_synonym lattice = "real vec set"


definition real_of_int_vec :: "int vec \<Rightarrow> real vec"  where
  "real_of_int_vec v = map_vec real_of_int v"

definition real_to_int_vec :: "real vec \<Rightarrow> int vec"  where
  "real_to_int_vec v = map_vec floor v"

definition is_indep :: "real mat \<Rightarrow> bool" where
  "is_indep A \<equiv> (\<forall>z::real vec. (A *\<^sub>v z = 0\<^sub>v (dim_row A) \<and> dim_col A = dim_vec z) 
    \<longrightarrow> z = 0\<^sub>v (dim_vec z))"

(*L is integer span of B and vectors in B are linearly independent*)
definition is_lattice :: "lattice \<Rightarrow> bool" where
  "is_lattice L \<equiv> (\<exists>B::(real mat). 
    L = {B *\<^sub>v (real_of_int_vec z) | z::int vec. dim_vec z = dim_col B} 
    \<and> is_indep B)"



definition gen_lattice :: "real mat \<Rightarrow> real vec set" where
  "gen_lattice A = {A *\<^sub>v (real_of_int_vec z) | z::int vec. dim_vec z = dim_col A}"


lemma is_lattice_gen_lattice:
  assumes "is_indep A"
  shows "is_lattice (gen_lattice A)"
unfolding is_lattice_def gen_lattice_def using assms by auto


text \<open>We do not need a fixed type anymore, but can just take the dimension in 
  the vector specification.\<close>

text \<open>We need to define the l-infinity norm on vectors.\<close>

definition infnorm ::"'a vec \<Rightarrow> 'a::{linorder, abs}" where
  "infnorm v \<equiv> Max { \<bar>v$i\<bar> | i. i < dim_vec v}"


text \<open>The CVP and SVP in $l_\infty$\<close>

text \<open>The closest vector problem.\<close>
definition is_closest_vec :: "lattice \<Rightarrow> real vec \<Rightarrow> real vec \<Rightarrow> bool" where
  "is_closest_vec L b v \<equiv> (is_lattice L) \<and> 
    (\<forall>x\<in>L. infnorm  (x - b) \<ge>  infnorm (v - b) \<and> v\<in>L)"

text \<open>The decision problem associated with solving CVP exactly.\<close>
definition gap_cvp :: "(lattice \<times> real vec \<times> real) set" where
  "gap_cvp \<equiv> {(L, b, r). (is_lattice L) \<and> (\<exists>v\<in>L. infnorm (v - b) \<le> r)}"



text \<open>The shortest vector problem.\<close>
definition is_shortest_vec :: "lattice  \<Rightarrow> real vec \<Rightarrow> bool" where
  "is_shortest_vec L v \<equiv> (is_lattice L) \<and> (\<forall>x\<in>L. infnorm (x) \<ge> infnorm (v) \<and> v\<in>L) "


text \<open>The decision problem associated with solving SVP exactly.\<close>
definition gap_svp :: "(lattice \<times> real) set" where
  "gap_svp \<equiv> {(L, r). (is_lattice L) \<and> (\<exists>v\<in>L. infnorm (v) \<le> r \<and> v \<noteq> 0\<^sub>v (dim_vec v))}"


text \<open>Subset Sum Problem\<close>

definition subset_sum :: "((int vec) * int) set" where
  "subset_sum \<equiv> {(as,s). (\<exists>xs::int vec. 
    (\<forall>i<dim_vec xs. xs$i \<in> {0,1}) \<and> xs \<bullet> as = s \<and> dim_vec xs = dim_vec as)}"



text \<open>Reduction function for cvp to subset sum\<close>

definition gen_basis :: "int vec \<Rightarrow> real mat" where
  "gen_basis as = mat (dim_vec as + 2) (dim_vec as) (\<lambda> (i, j). if i \<in> {0,1} then as$j 
    else (if i = j + 2 then 2 else 0))"


definition gen_t :: "int vec \<Rightarrow> int \<Rightarrow> real vec" where
  "gen_t as s = vec (dim_vec as + 2) ((\<lambda> i. 1)(0:= s+1, 1:= s-1))"



definition reduce_cvp_subset_sum :: 
  "((int vec) * int) \<Rightarrow> (lattice * (real vec) * real)" where
  "reduce_cvp_subset_sum \<equiv> (\<lambda> (as,s).
    (gen_lattice (gen_basis as), gen_t as s, (1::real)))"


text \<open>Lemmas for Proof\<close>

lemma vec_lambda_eq: "(\<forall>i<n. a i = b i) \<longrightarrow> vec n a = vec n b"
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




lemma Bx_rewrite: 
  assumes x_dim: "dim_vec as = dim_vec x"
  shows "(gen_basis as) *\<^sub>v (real_of_int_vec x) = 
    vec (dim_vec as + 2) (\<lambda> i. if i \<in> {0,1} then real_of_int (x \<bullet> as) 
    else real_of_int (2 * x$(i-2)))"
    (is "?init_vec = ?goal_vec")
proof -
  define n::nat where n_def: "n = dim_vec as"
  have "vec n (\<lambda>j. real_of_int (as $ j)) \<bullet> (real_of_int_vec x) = 
     real_of_int (x \<bullet> as)"
    unfolding n_def scalar_prod_def real_of_int_vec_def 
    using x_dim by (auto simp add: mult.commute)
  then show ?thesis 
    unfolding gen_basis_def reduce_cvp_subset_sum_def gen_t_def real_of_int_vec_def
  proof (intro eq_vecI, auto simp add: n_def, goal_cases)
    case (1 i)
    have "(\<Sum>ia = 0..<dim_vec (real_of_int_vec x).
      vec (dim_vec as) (\<lambda>j. real_of_int (if i = Suc (Suc j) then 2 else 0)) $ ia *
      (real_of_int_vec x) $ ia) =
      (\<Sum>ia<n. real_of_int (if i = ia+2 then 2 * (x $ ia) else 0))"
      by (intro sum.cong, auto simp add: n_def x_dim real_of_int_vec_def)
    also have "\<dots> = (\<Sum>ib\<in>{2..<n+2}. 
        real_of_int (if i = ib then 2 * (x $ (ib-2)) else 0))" 
    proof - 
      have eq: "(\<lambda>ib. real_of_int (if i = ib then 2 * x $ (ib - 2) else 0)) \<circ> (+) 2
          = (\<lambda>ia. real_of_int (if i = ia + 2 then 2 * x $ ia else 0))"
      by auto
      then show ?thesis
        by (subst sum.atLeastLessThan_shift_0[
            of "(\<lambda>ib. real_of_int (if i = ib then 2 * x $ (ib - 2) else 0))" 2 "n+2"])
          (subst eq, use lessThan_atLeast0 in \<open>auto\<close>)
    qed
    also have "\<dots> = 2 * real_of_int (x $ (i-2))" 
    proof - 
      have finite: "finite {2..<n+2}" by auto
      have is_in: "i \<in> {2..<n+2}" using 1 by (auto simp add: n_def)
      show ?thesis 
      by (subst of_int_sum[symmetric]) 
         (subst sum_if_zero[OF finite is_in, of "(\<lambda>k.2 * (x $ (k-2)))"], auto)
    qed
    finally show ?case unfolding scalar_prod_def real_of_int_vec_def by auto
  qed
qed


lemma Bx_s_rewrite: 
  assumes x_dim: "dim_vec as = dim_vec x"
  shows "(gen_basis as) *\<^sub>v (real_of_int_vec x) - (gen_t as s) = 
    vec (dim_vec as + 2) (\<lambda> i. if i = 0 then real_of_int (x \<bullet> as - s - 1) else (
      if i = 1 then real_of_int (x \<bullet> as - s + 1) else real_of_int (2 * x$(i-2) - 1)))"
    (is "?init_vec = ?goal_vec")
unfolding gen_t_def by (subst  Bx_rewrite[OF assms], auto)


lemma infnorm_Bx_s:
  assumes x_dim: "dim_vec as = dim_vec x"
  shows "infnorm ((gen_basis as) *\<^sub>v (real_of_int_vec x) - (gen_t as s)) = 
    Max ({real_of_int \<bar>x \<bullet> as - s - 1\<bar>} \<union> {real_of_int \<bar>x \<bullet> as - s + 1\<bar>} \<union> 
      {real_of_int \<bar>2*x$(i-2)-1\<bar> | i. 1<i \<and> i<dim_vec as+2 })"
proof -
  let ?init_vec = "(gen_basis as) *\<^sub>v (real_of_int_vec x) - (gen_t as s)"
  let ?goal_vec = "vec (dim_vec as + 2) (\<lambda> i. if i = 0 then real_of_int (x \<bullet> as - s - 1) else (
      if i = 1 then real_of_int (x \<bullet> as - s + 1) else real_of_int (2 * x$(i-2) - 1)))"
  define n where n_def: "n = dim_vec as"
  have "infnorm ?init_vec = infnorm ?goal_vec" using Bx_s_rewrite[OF x_dim] by auto
  also have "\<dots> = Max {\<bar>?goal_vec $i\<bar> | i. i<n+2}" 
    unfolding infnorm_def n_def by auto
  also have "\<dots> = Max ({real_of_int \<bar>x \<bullet> as - s - 1\<bar>} \<union> 
                       {real_of_int \<bar>x \<bullet> as - s + 1\<bar>} \<union> 
                       {real_of_int \<bar>2*x$(i-2)-1\<bar> | i. 1<i \<and> i<n+2})"
  proof -
    have "{\<bar>?goal_vec $i\<bar> | i. i<n+2} = 
      {\<bar>?goal_vec $0\<bar>} \<union> {\<bar>?goal_vec $1\<bar>} \<union> {\<bar>?goal_vec $i\<bar> | i. 1<i \<and> i<n+2}" 
    proof -
      have "{\<bar>?goal_vec $i\<bar> | i. i\<in>{0..<n+2}} = 
       {\<bar>?goal_vec $0\<bar>} \<union> {\<bar>?goal_vec $i\<bar> | i. i\<in>{1..<n+2}}"   
      by (subst set_compr_elem[of "{0..<n+2}" 0 "(\<lambda>i. \<bar>?goal_vec $i\<bar>)"], auto)
      also have "\<dots> = {\<bar>?goal_vec $0\<bar>} \<union> {\<bar>?goal_vec $1\<bar>} \<union> 
        {\<bar>?goal_vec $i\<bar> | i. i\<in>{2..<n+2}}"
      by (subst set_compr_elem[of "{1..<n+2}" 1 "(\<lambda>i. \<bar>?goal_vec $i\<bar>)"], auto)
      finally show ?thesis by auto
    qed
    also have "\<dots> = {real_of_int \<bar>x \<bullet> as - s - 1\<bar>} \<union> {real_of_int \<bar>x \<bullet> as - s + 1\<bar>} \<union> 
      {\<bar>?goal_vec $i\<bar> | i. 1<i \<and> i<n+2}" by auto
    also have "{\<bar>?goal_vec $i\<bar> | i. 1<i \<and> i<n+2} = 
      {real_of_int \<bar>2*x$(i-2)-1\<bar> | i. 1<i \<and> i<n+2}"
    proof -
      have "\<bar>?goal_vec $i\<bar> = real_of_int \<bar>2*x$(i-2)-1\<bar>" if "1<i \<and> i<n+2" for i 
      using that n_def by force
      then show ?thesis using n_def by force
    qed
    finally have eq: "{\<bar>?goal_vec $i\<bar> | i. i<n+2} = 
      {real_of_int \<bar>x \<bullet> as - s - 1\<bar>} \<union> {real_of_int \<bar>x \<bullet> as - s + 1\<bar>} \<union> 
      {real_of_int \<bar>2*x$(i-2)-1\<bar> | i. 1<i \<and> i<n+2}" by blast
    then show ?thesis by auto
  qed
  finally show ?thesis using n_def by blast
qed



text \<open>gen_basis actually generates a basis which is spans the lattice (by definition) and 
  is linearly independent.\<close>


lemma is_indep_gen_basis:
  "is_indep (gen_basis as)"
unfolding is_indep_def 
proof (safe, goal_cases)
case (1 z)
  let ?n = "dim_vec as"
  have z_dim: "dim_vec z = ?n" using 1(2) unfolding gen_basis_def by auto
  have dim_row: "dim_row (gen_basis as) = ?n + 2" unfolding gen_basis_def by auto
  have eq: "gen_basis as *\<^sub>v z = vec (?n + 2) (\<lambda> i. if i \<in> {0,1} 
    then (z \<bullet> (real_of_int_vec as)) else (2 * z$(i-2)))" 
  (is "gen_basis as *\<^sub>v z = ?goal_vec")
  proof -
    have scal_prod_com: "z \<bullet> real_of_int_vec as = real_of_int_vec as \<bullet> z"
      using comm_scalar_prod[of "real_of_int_vec as" ?n z] z_dim
      by (metis carrier_dim_vec index_map_vec(2) real_of_int_vec_def)
    have *: "row (mat (?n+2) (?n) (\<lambda>x. real_of_int
      (case x of (i, j) \<Rightarrow> if i = 0 \<or> i = Suc 0 then as $ j
                           else if i = j + 2 then 2 else 0))) i = 
      (if i\<in>{0,1} then real_of_int_vec as else vec ?n (\<lambda>j. if i = j + 2 then 2 else 0))"
    (is "?row = ?vec") 
    if "i<?n+2" for i 
    using that by (auto simp add: real_of_int_vec_def)
    then have "?row i \<bullet> z = 
      (if i \<in> {0,1} then (real_of_int_vec as) \<bullet> z else 2 * z $ (i - 2))"
    if "i<?n+2" for i
    using that proof (subst *[OF that], auto, goal_cases)
    case 1
      have plus_2: "(i-2 = j) = (i = j+2)" for j using 1 that by auto
      have finite: "finite {0..<?n}" and elem: "i-2 \<in> {0..<?n}" using that 1 by auto
      have vec: "vec (dim_vec as) (\<lambda>j. if i = j+2 then 2 else 0) $ ia = 
        (if i = ia+2 then 2 else 0)" if "ia<?n" for ia
        using index_vec that by blast
      then have "(\<Sum>ia = 0..<dim_vec z.
        vec (dim_vec as) (\<lambda>j. if i = Suc (Suc j) then 2 else 0) $ ia * z $ ia) =
        (\<Sum>ia = 0..<dim_vec as. (if i = ia+2 then 2 else 0) * z $ ia)"
        using z_dim by auto
      also have "\<dots> = (\<Sum>ia = 0..<dim_vec as. (if i = ia+2 then 2 * z $ ia else 0))"
        proof -
          have "(\<forall>n. (0 = (if i = n + 2 then 2 else 0) * z $ n \<or> n + 2 = i) \<and> 
            (2 * z $ n = (if i = n + 2 then 2 else 0) * z $ n \<or> n + 2 \<noteq> i)) \<or> 
            (\<Sum>n = 0..<dim_vec as. (if i = n + 2 then 2 else 0) * z $ n) = 
            (\<Sum>n = 0..<dim_vec as. if i = n + 2 then 2 * z $ n else 0)" by simp
          then show ?thesis by (metis (no_types))
        qed
      also have "\<dots> = 2*z$(i-2)" using sum_if_zero[OF finite elem, of "(\<lambda>j. 2*z$j)"]
        using plus_2 by auto
      finally show ?case unfolding scalar_prod_def by blast
    qed
    then have "?row i \<bullet> z = 
      (if i \<in> {0,1} then z \<bullet> real_of_int_vec as else 2 * z $ (i - 2))"
    if "i<?n+2" for i using that by (subst scal_prod_com)
    then show ?thesis 
      unfolding gen_basis_def mult_mat_vec_def by auto
  qed
  have "\<dots> = 0\<^sub>v (?n + 2)" using 1(1) dim_row by (subst eq[symmetric], auto) 
  then have "2 * z$(i-2) = 0" if "1<i" and "i<?n +2" for i 
    using that by (smt (verit, best) cancel_comm_monoid_add_class.diff_cancel 
      empty_iff index_vec index_zero_vec(1) insert_iff not_less_zero zero_less_diff)
  then have "z$i = 0" if "i<?n" for i using that by force
  then show ?case using 1 z_dim unfolding gen_basis_def by auto
qed








text \<open>The Gap-CVP is NP-hard in l_infty.\<close>

lemma well_defined_reduction: 
  assumes "(as, s) \<in> subset_sum"
  shows "reduce_cvp_subset_sum (as, s) \<in> gap_cvp"
proof -
  obtain x where
    x_dim: "dim_vec x = dim_vec as" and
    x_binary: "\<forall>i<dim_vec x. x $ i \<in> {0, 1}" and 
    x_lin_combo: "x \<bullet> as = s" 
    using assms unfolding subset_sum_def by blast
  define L where L_def: "L = fst (reduce_cvp_subset_sum (as, s))"
  define b where b_def: "b = fst (snd (reduce_cvp_subset_sum (as, s)))"
  define r where r_def: "r = snd (snd (reduce_cvp_subset_sum (as, s)))"
  have "r = 1" by (simp add: r_def reduce_cvp_subset_sum_def Pair_inject prod.exhaust_sel)
  (*have "(L,b,r) = reduce_cvp_subset_sum (as, s)" using L_def b_def r_def by auto*)
  define B where "B = gen_basis as"
  define n where n_def: "n = dim_vec as"
  have init_eq_goal: "B *\<^sub>v (real_of_int_vec x) - b = 
    vec (n+2) (\<lambda> i. if i = 0 then real_of_int (x \<bullet> as - s - 1) else (
      if i = 1 then real_of_int (x \<bullet> as - s + 1) else real_of_int (2 * x$(i-2) - 1)))"
    (is "?init_vec = ?goal_vec")
  unfolding B_def b_def reduce_cvp_subset_sum_def
  by (auto simp add: Bx_s_rewrite[OF x_dim[symmetric]] n_def)
  have "infnorm (B *\<^sub>v (real_of_int_vec x) - b) = 
    Max ({real_of_int \<bar>x \<bullet> as - s - 1\<bar>} \<union> {real_of_int \<bar>x \<bullet> as - s + 1\<bar>} \<union> 
      {real_of_int \<bar>2*x$(i-2)-1\<bar> | i. 1<i \<and> i<n+2 })"
  unfolding B_def b_def reduce_cvp_subset_sum_def 
  by (auto simp add: infnorm_Bx_s[OF x_dim[symmetric]] n_def)
  also have  "\<dots> \<le> r"
  proof -
    have elem: "x$(i-2)\<in>{0,1}" if "1<i \<and> i<n+2" for i 
      using that x_binary x_dim n_def
      by (smt (verit) add_diff_cancel_right' diff_diff_left diff_less_mono2 
      less_add_same_cancel2 less_imp_add_positive less_one linorder_neqE_nat 
      nat_1_add_1 not_add_less2)
    then have "\<bar>2*x$(i-2)-1\<bar> = 1" if "1<i \<and> i<n+2" for i 
      using elem[OF that] by auto
    then have "{real_of_int \<bar>2 * x $ (i - 2) - 1\<bar> |i. 1 < i \<and> i < n + 2} \<subseteq> {1}" 
      by (safe, auto)
    then show ?thesis using x_lin_combo \<open>r=1\<close> by auto
  qed
  finally have "infnorm (?init_vec) \<le> r" by blast
  moreover have "B *\<^sub>v (real_of_int_vec x)\<in>L" 
  proof -
    have "dim_vec x = dim_col (gen_basis as)" unfolding gen_basis_def using x_dim by auto
    then show ?thesis
      unfolding L_def reduce_cvp_subset_sum_def gen_lattice_def B_def by auto
  qed
  ultimately have witness: "\<exists>v\<in>L. infnorm (v - b) \<le> r" by auto
  have is_indep: "is_indep B" unfolding B_def using is_indep_gen_basis[of as] by simp
  have L_lattice: "is_lattice L" unfolding L_def reduce_cvp_subset_sum_def 
    using is_lattice_gen_lattice[OF is_indep] unfolding B_def by auto
  show ?thesis unfolding gap_cvp_def using L_lattice witness L_def b_def r_def by force
qed

lemma NP_hardness_reduction:
  assumes "reduce_cvp_subset_sum (as, s) \<in> gap_cvp"
  shows "(as, s) \<in> subset_sum"
proof -
  define n where "n = dim_vec as"
  define B where "B = gen_basis as"
  define L where "L = gen_lattice B"
  define b where "b = gen_t as s"
  have ex_v: "\<exists>v\<in>L. infnorm (v - b) \<le> 1" and is_lattice: "is_lattice L"
    using assms unfolding gap_cvp_def reduce_cvp_subset_sum_def L_def B_def b_def by auto
  then obtain v where v_in_L:"v\<in>L" and ineq:"infnorm (v - b) \<le> 1" by blast
  have "\<exists>zs::int vec. v = B *\<^sub>v (real_of_int_vec zs) \<and> dim_vec zs = dim_vec as"
  using v_in_L unfolding L_def gen_lattice_def B_def gen_basis_def by auto
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




text \<open>The Gap-SVP is NP-hard.\<close>
lemma "is_reduction my_fun gap_svp gap_cvp"
oops


(*
eNorm (\<LL> \<infinity> M) f
*)


end