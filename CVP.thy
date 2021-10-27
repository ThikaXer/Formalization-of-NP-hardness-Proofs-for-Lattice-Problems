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


definition lin_combo :: "'a list \<Rightarrow> ('a, 'b) vec list \<Rightarrow> ('a::{plus, times, zero}, 'b::finite) vec" where
  "lin_combo zs vs = foldr (+) (map2 (*s) zs vs) (vec 0)"

definition gen_lattice :: "(real, 'a) vec list \<Rightarrow> (real, 'a::finite) vec set" where
  "gen_lattice vs = {v. \<exists>zs::int list. v = lin_combo zs vs}"



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

text \<open>The CVP and SVP in $l_\infty$\<close>

text \<open>The closest vector problem.\<close>
definition is_closest_vec :: "'n lattice \<Rightarrow> real ^ 'n \<Rightarrow> real ^ 'n \<Rightarrow> bool" where
  "is_closest_vec L b v \<equiv> (\<forall>x\<in>L. infnorm  (x - b) \<ge> 
        infnorm (v - b) \<and> v\<in>L)"

text \<open>The decision problem associated with solving CVP exactly.\<close>
definition gap_cvp :: "('n lattice \<times> (real, 'n) vec \<times> real) set" where
  "gap_cvp \<equiv> {(L, b, r). (\<exists>v\<in>L. infnorm (v - b) \<le> r)}"



text \<open>The shortest vector problem.\<close>
definition is_shortest_vec :: "'n lattice  \<Rightarrow> real ^ 'n \<Rightarrow> bool" where
  "is_shortest_vec L v \<equiv> (\<forall>x\<in>L. infnorm (x) \<ge> infnorm (v) \<and> v\<in>L) "


text \<open>The decision problem associated with solving SVP exactly.\<close>
definition gap_svp :: "('n lattice \<times> real) set" where
  "gap_svp \<equiv> {(L, r). (\<exists>v\<in>L. infnorm (v) \<le> r \<and> v\<noteq>0)}"


text \<open>Subset Sum Problem\<close>

definition subset_sum :: "((int ^'n) * int) set" where
  "subset_sum \<equiv> {(as,s). (\<exists>xs::int^'n. (\<forall>i. xs$i \<in> {0,1}) \<and> scalar_product xs as = s)}"



text \<open>Reduction function for cvp to subset sum\<close>

definition gen_basis :: "('a::{zero,numeral}, 'n) vec \<Rightarrow> ('a, 'n) vec list" where
  "gen_basis as =  map 
    (\<lambda> j. (\<chi> i. if (f i) = 1 then as$(finv j) else (if (f i) = j + 1 then 2 else 0)))
    [0..<n]"


definition gen_t :: "'a::one \<Rightarrow> ('a, 'n) vec" where
  "gen_t s = (\<chi> i. if f i = 0 then s else 1)"



definition reduce_cvp_subset_sum :: 
  "((int ^'n) * int) \<Rightarrow> (('n lattice) * (real ^'n) * real)" where
  "reduce_cvp_subset_sum input = 
    (gen_lattice (gen_basis (real_of_int_vec (fst input))), gen_t (snd input), 1)"

text \<open>The Gap-CVP is NP-hard in l_infty.\<close>
lemma "is_reduction reduce_cvp_subset_sum subset_sum gap_cvp"
unfolding is_reduction_def
proof (safe, goal_cases)
  case (1 as s)
  then show ?case sorry
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