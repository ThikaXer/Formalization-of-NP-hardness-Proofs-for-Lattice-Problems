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


lemma is_lattice_gen_svp_lattice:
  assumes "is_lattice L"
  shows "is_lattice (gen_svp_lattice L b)"
proof -
  obtain B where 
    span_B: "L = {B *\<^sub>v real_of_int_vec z |z. dim_vec z = dim_col B}" and
    is_indep_B: "is_indep B" 
    using assms unfolding is_lattice_def by blast

  define B' where B'_def:
    "B' = mat (dim_row B) (dim_col B +1) (\<lambda>(i,j). if j< dim_col B then B $$ (i,j) else b $ i)"

  have "gen_svp_lattice L b = {B' *\<^sub>v real_of_int_vec z |z. dim_vec z = dim_col B'}" 
  proof (safe, goal_cases)
  case (1 a)
    obtain v x where a_def: "a = v + real_of_int x \<cdot>\<^sub>v b" "v \<in> L" "dim_vec v = dim_vec b" 
      using 1 unfolding gen_svp_lattice_def by blast
    then have a_dim: "dim_vec b = dim_row B" using span_B by auto
    obtain y where v_def: "v = B *\<^sub>v real_of_int_vec y" "dim_vec y = dim_col B" 
      using \<open>v\<in>L\<close> unfolding span_B by auto 
    define z where "z = vec (dim_vec y + 1) (\<lambda>i. if i< dim_vec y then y$i else x)"
    have "a = B' *\<^sub>v real_of_int_vec z" 
      unfolding B'_def z_def mult_mat_vec_def a_def v_def
      proof (subst vec_eq_iff, auto simp add: a_dim, goal_cases)
      case (1 i)
        then show ?case unfolding scalar_prod_def   sorry
      qed
    moreover have "dim_vec z = dim_col B'" sorry
    ultimately show ?case unfolding gen_svp_lattice_def by blast
  next
  case (2 x z)
    then show ?case sorry
  qed

  moreover have "is_indep B'" sorry

  ultimately show ?thesis unfolding is_lattice_def by blast
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