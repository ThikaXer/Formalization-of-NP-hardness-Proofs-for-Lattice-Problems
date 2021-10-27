theory CVP

imports Main 
        "HOL-Analysis.Finite_Cartesian_Product"
        "HOL-Analysis.Linear_Algebra"
        "poly-reductions/Karp21/Reductions"
        (*"poly-reducrions/Karp21/Three_Sat_To_Set_Cover"*)
        (*Subset_Sum*)


begin


type_synonym 'n lattice = "(real ^ ('n::finite)) set "


definition vec_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a ^ 'n \<Rightarrow> 'b ^ 'n" where
  "vec_map f v = (\<chi> i. f (v$i))"


definition real_of_int_vec :: "int ^ 'n \<Rightarrow> real ^ ('n::finite)"  where
  "real_of_int_vec v = vec_map real_of_int v"

definition real_to_int_vec :: "real ^ 'n \<Rightarrow> int ^ ('n::finite)"  where
  "real_to_int_vec v = vec_map floor v"



definition is_lattice :: "('n::finite) lattice \<Rightarrow> bool" where
  "is_lattice L \<equiv> (\<exists>B::(real ^'n ^'n). \<forall>v\<in>L. \<exists>z::int^'n. B *v (real_of_int_vec z) = v)"



definition lin_combo :: "'a list \<Rightarrow> ('a, 'b) vec list \<Rightarrow> ('a::{plus, times, zero}, 'b::finite) vec" where
  "lin_combo zs vs = foldr (+) (map2 (*s) zs vs) (vec 0)"

definition gen_lattice_list :: "(real, 'a) vec list \<Rightarrow> (real, 'a::finite) vec set" where
  "gen_lattice_list vs = {v. \<exists>zs::int list. v = lin_combo zs vs}"

definition gen_lattice :: "(real^'a) ^'a \<Rightarrow> (real, 'a::finite) vec set" where
  "gen_lattice vs = {v. \<exists>z::int ^'a. v = vs *v (real_of_int_vec z)}"


text \<open>From now on work over fixed dimension!\<close>

locale fixed_dim = 
fixes n::nat
  and f::"'n::finite \<Rightarrow> nat"
assumes n_def: "n = CARD ('n)"
    and f_bij: "bij_betw f UNIV {0..<n}"
begin

definition finv :: "nat \<Rightarrow> 'n" where
  "finv = the_inv f"


lemma f_finv:
  assumes "j\<in>{0..<n}"
  shows "(f \<circ> finv) j = j" 
unfolding finv_def using assms f_bij 
by (metis comp_apply f_the_inv_into_f_bij_betw)


lemma finv_f: 
  "finv \<circ> f = id"
unfolding finv_def using f_bij
by (metis bij_betw_imp_inj_on comp_apply eq_id_iff the_inv_f_f)

definition incr :: "'n \<Rightarrow> 'n" where
  "incr i = finv (f i + 1)"

text \<open>The CVP and SVP in $l_\infty$\<close>

text \<open>The closest vector problem.\<close>
definition is_closest_vec :: "'n lattice \<Rightarrow> real ^ 'n \<Rightarrow> real ^ 'n \<Rightarrow> bool" where
  "is_closest_vec L b v \<equiv> (is_lattice L) \<and> (\<forall>x\<in>L. infnorm  (x - b) \<ge>  infnorm (v - b) \<and> v\<in>L)"

text \<open>The decision problem associated with solving CVP exactly.\<close>
definition gap_cvp :: "('n lattice \<times> (real, 'n) vec \<times> real) set" where
  "gap_cvp \<equiv> {(L, b, r). (is_lattice L) \<and> (\<exists>v\<in>L. infnorm (v - b) \<le> r)}"



text \<open>The shortest vector problem.\<close>
definition is_shortest_vec :: "'n lattice  \<Rightarrow> real ^ 'n \<Rightarrow> bool" where
  "is_shortest_vec L v \<equiv> (is_lattice L) \<and> (\<forall>x\<in>L. infnorm (x) \<ge> infnorm (v) \<and> v\<in>L) "


text \<open>The decision problem associated with solving SVP exactly.\<close>
definition gap_svp :: "('n lattice \<times> real) set" where
  "gap_svp \<equiv> {(L, r). (is_lattice L) \<and> (\<exists>v\<in>L. infnorm (v) \<le> r \<and> v\<noteq>0)}"


text \<open>Subset Sum Problem\<close>

definition subset_sum :: "((int ^'n) * int) set" where
  "subset_sum \<equiv> {(as,s). (\<exists>xs::int^'n. (\<forall>i. xs$i \<in> {0,1}) \<and> scalar_product xs as = s)}"



text \<open>Reduction function for cvp to subset sum\<close>

definition gen_basis :: "int ^ 'n \<Rightarrow> (real ^'n) ^'n" where
  "gen_basis as = (\<chi> i j. if f i = 0 then as$j else (if f i = f j + 1 then 2 else 0))"


definition gen_t :: "int \<Rightarrow> (real, 'n) vec" where
  "gen_t s = (\<chi> i. if f i = 0 then s else 1)"



definition reduce_cvp_subset_sum :: 
  "((int ^'n) * int) \<Rightarrow> (('n lattice) * (real ^'n) * real)" where
  "reduce_cvp_subset_sum input = 
    (gen_lattice (gen_basis (fst input)), gen_t (snd input), 1)"

text \<open>The Gap-CVP is NP-hard in l_infty.\<close>
lemma "is_reduction reduce_cvp_subset_sum subset_sum gap_cvp"
unfolding is_reduction_def
proof (safe, goal_cases)
  case (1 as s)
  then obtain x where 
    x_binary: "\<forall>i. x $ i \<in> {0, 1}" and 
    x_lin_combo: "scalar_product x as = s" 
    unfolding subset_sum_def by blast
  define L where L_def: "L = fst (reduce_cvp_subset_sum (as, s))"
  define b where b_def: "b = fst (snd (reduce_cvp_subset_sum (as, s)))"
  define r where r_def: "r = snd (snd (reduce_cvp_subset_sum (as, s)))"
  have "r = 1" using r_def reduce_cvp_subset_sum_def by auto
  (*have "(L,b,r) = reduce_cvp_subset_sum (as, s)" using L_def b_def r_def by auto*)
  define B where "B = gen_basis as"
  have "B *v (real_of_int_vec x) - b = 
    (\<chi> i. if f i = 0 then scalar_product x as - s else 2 * x$(incr i) - 1)"
    (is "_ = ?goal_vec")
    sorry
  then have "infnorm (B *v (real_of_int_vec x) - b) = 
    Max ({\<bar>scalar_product x as - s\<bar>} \<union> {\<bar>2*x$(finv i)-1\<bar> | i. i\<in>{1..<n} })"
  proof -
    have "infnorm (?goal_vec) = Max {\<bar>?goal_vec $(finv i)\<bar> | i. i\<in>{0..<n}}" 
      apply (subst infnorm_Max) 

find_theorems Basis

    then have "\<dots> = Max ({\<bar>scalar_product x as - s\<bar>} \<union> {\<bar>2*x$(finv i)-1\<bar> | i. i\<in>{1..<n}})"
      sorry
    then show ?thesis sorry
  qed
  also have "\<dots> = Max ({0} \<union>  {y. \<exists>i\<in>{1..<n}. y = \<bar>2*x$(finv i)-1\<bar> })" 
    using x_lin_combo by auto
  also have "\<dots> \<le> Max ({0} \<union>  {1})"
  proof -
    have "\<bar>2*x$(finv i)-1\<bar> = 1" if "i\<in>{1..<n}" for i using x_binary
      by (smt (z3) insert_iff singletonD)
    then show ?thesis by auto
  qed
  also have "\<dots> \<le> r" using \<open>r=1\<close> by auto
  finally have "infnorm (B *v (real_of_int_vec x) -b) \<le> r" by blast
  have L_lattice: "is_lattice L" sorry
  then have witness: "\<exists>v\<in>L. infnorm (v - b) \<le> r" sorry
  show ?case unfolding gap_cvp_def using L_lattice witness L_def b_def r_def by force
next
  case (2 as s)
  then show ?case sorry
qed




text \<open>The Gap-SVP is NP-hard.\<close>
lemma "is_reduction my_fun gap_svp gap_cvp"
oops


(*
eNorm (\<LL> \<infinity> M) f
*)


end