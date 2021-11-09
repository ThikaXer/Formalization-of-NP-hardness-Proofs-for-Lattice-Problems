theory SVP_vec

imports CVP_vec

begin

text \<open>The reduction of SVP to CVP in $l_\infty$ norm\<close>

text \<open>The shortest vector problem.\<close>
definition is_shortest_vec :: "lattice  \<Rightarrow> real vec \<Rightarrow> bool" where
  "is_shortest_vec L v \<equiv> (is_lattice L) \<and> (\<forall>x\<in>L. infnorm (x) \<ge> infnorm (v) \<and> v\<in>L) "


text \<open>The decision problem associated with solving SVP exactly.\<close>
definition gap_svp :: "(lattice \<times> real) set" where
  "gap_svp \<equiv> {(L, r). (is_lattice L) \<and> (\<exists>v\<in>L. infnorm v \<le> r \<and> v \<noteq> 0\<^sub>v (dim_vec v))}"

text \<open>Generate a lattice to solve SVP for reduction\<close>

definition gen_svp_lattice :: "lattice \<Rightarrow> real vec \<Rightarrow> lattice" where
  "gen_svp_lattice L b = {v + c \<cdot>\<^sub>v b | (c::int) v. v\<in>L \<and> dim_vec v = dim_vec b}"


text \<open>Reduction SVP to CVP in $l_\infty$ norm.\<close>
definition reduce_svp_cvp:: "(lattice \<times> (real vec) \<times> real) \<Rightarrow> (lattice \<times> real)" where
  "reduce_svp_cvp \<equiv> (\<lambda> (L, b, r). (gen_svp_lattice L b, r::real))"

text \<open>Lemmas for proof\<close>

find_theorems "_ *\<^sub>v _ = _"

find_theorems "_$_ = _$_"

value "(vec_of_list [0,1,2::nat])$2"



lemma is_lattice_gen_svp_lattice:
  assumes "is_lattice L" "b\<notin>L"
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
  
  then have gen: "gen_svp_lattice L b = gen_lattice B'" sorry

  obtain B'' where "gen_lattice B'' = gen_lattice B'" and "is_indep B''" sorry

  then show ?thesis apply (subst gen) unfolding is_lattice_def gen_lattice_def by blast
qed

text \<open>Well-definedness of reduction function\<close>

lemma well_defined_reduction_svp:
  assumes "(L,b,r) \<in> gap_cvp"
  shows "reduce_svp_cvp (L,b,r) \<in> gap_svp"
using assms unfolding reduce_svp_cvp_def gap_svp_def gap_cvp_def
proof (safe, goal_cases)
case (1 v)
then show ?case using is_lattice_gen_svp_lattice by simp
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