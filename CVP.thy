theory CVP

imports Main 
        "HOL-Analysis.Finite_Cartesian_Product"
        "HOL-Analysis.Linear_Algebra"
        "poly-reductions/Karp21/Reductions"
        (*"poly-reducrions/Karp21/Three_Sat_To_Set_Cover"*)
        (*Subset_Sum*)
        "Berlekamp_Zassenhaus.Finite_Field"

begin

type_synonym 'n len = "('n::finite) mod_ring"

type_synonym 'n lattice = "(real ^ ('n::finite)) set "


definition vec_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a ^ 'n \<Rightarrow> 'b ^ 'n" where
  "vec_map f v = (\<chi> i. f (v$i))"


definition real_of_int_vec :: "int ^ 'n \<Rightarrow> real ^ ('n::finite)"  where
  "real_of_int_vec v = vec_map real_of_int v"

definition real_to_int_vec :: "real ^ 'n \<Rightarrow> int ^ ('n::finite)"  where
  "real_to_int_vec v = vec_map floor v"



definition is_lattice :: "('n::finite) lattice \<Rightarrow> bool" where
  "is_lattice L \<equiv> (\<exists>B::(real ^'n ^'n). \<forall>v\<in>L. \<exists>z::int^'n. 
    B *v (real_of_int_vec z) = v)"


definition lin_combo :: "'a list \<Rightarrow> ('a, 'b) vec list \<Rightarrow> ('a::{plus, times, zero}, 'b::finite) vec" where
  "lin_combo zs vs = foldr (+) (map2 (*s) zs vs) (vec 0)"

definition gen_lattice_list :: "(real, 'n) vec list \<Rightarrow> (real, 'n::finite) vec set" where
  "gen_lattice_list vs = {v. \<exists>zs::int list. v = lin_combo zs vs}"

definition gen_lattice :: "(real^'a) ^'a \<Rightarrow> (real, 'a::finite) vec set" where
  "gen_lattice vs = {v. \<exists>z::int ^'a. v = vs *v (real_of_int_vec z)}"


text \<open>From now on work over fixed dimension!\<close>

locale fixed_dim = 
fixes n::nat
assumes n_def: "n = CARD ('n::{finite,nontriv})"
begin


text \<open>The CVP and SVP in $l_\infty$\<close>

text \<open>The closest vector problem.\<close>
definition is_closest_vec :: "('n len) lattice \<Rightarrow> real ^ ('n len) \<Rightarrow> real ^ ('n len) \<Rightarrow> bool" where
  "is_closest_vec L b v \<equiv> (is_lattice L) \<and> (\<forall>x\<in>L. infnorm  (x - b) \<ge>  infnorm (v - b) \<and> v\<in>L)"

text \<open>The decision problem associated with solving CVP exactly.\<close>
definition gap_cvp :: "(('n len) lattice \<times> (real, ('n len)) vec \<times> real) set" where
  "gap_cvp \<equiv> {(L, b, r). (is_lattice L) \<and> (\<exists>v\<in>L. infnorm (v - b) \<le> r)}"



text \<open>The shortest vector problem.\<close>
definition is_shortest_vec :: "('n len) lattice  \<Rightarrow> real ^ ('n len) \<Rightarrow> bool" where
  "is_shortest_vec L v \<equiv> (is_lattice L) \<and> (\<forall>x\<in>L. infnorm (x) \<ge> infnorm (v) \<and> v\<in>L) "


text \<open>The decision problem associated with solving SVP exactly.\<close>
definition gap_svp :: "(('n len) lattice \<times> real) set" where
  "gap_svp \<equiv> {(L, r). (is_lattice L) \<and> (\<exists>v\<in>L. infnorm (v) \<le> r \<and> v\<noteq>0)}"


text \<open>Subset Sum Problem\<close>

definition subset_sum :: "((int ^('n len)) * int) set" where
  "subset_sum \<equiv> {(as,s). (\<exists>xs::int^('n len). (\<forall>i. xs$i \<in> {0,1}) \<and> scalar_product xs as = s)}"



text \<open>Reduction function for cvp to subset sum\<close>

definition gen_basis :: "int ^('n len) \<Rightarrow> (real ^('n len)) ^('n len)" where
  "gen_basis as = (\<chi> i j. if i = 0 then as$j else (if i = j + (1::'n len) then 2 else 0))"


definition gen_t :: "int \<Rightarrow> (real, ('n len)) vec" where
  "gen_t s = (\<chi> i. if i = 0 then s else 1)"



definition reduce_cvp_subset_sum :: 
  "((int ^('n len)) * int) \<Rightarrow> ((('n len) lattice) * (real ^('n len)) * real)" where
  "reduce_cvp_subset_sum input = 
    (gen_lattice (gen_basis (fst input)), gen_t (snd input), 1)"


text \<open>Lemmas for Proof\<close>

lemma vec_lambda_eq: "(\<forall>i. a i = b i) \<longrightarrow> (\<chi> i. a i) = (\<chi> i. b i)"
by auto


lemma sum_if_zero: 
  "(\<Sum>(j::'n len)\<in>UNIV. (if j = i then a j else 0)) = a i"
proof -
  have "(\<Sum>(x::'n len)\<in>UNIV. if x = i then a x else 0) =
  (if i = i then a i else 0) + (\<Sum>x\<in>UNIV - {i}. if x = i then a x else 0)"
  using sum.remove[of "UNIV::'n len set" i "(\<lambda>x. if x = i then a x else 0)"] by auto
  then show ?thesis by auto
qed
  


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
    (\<chi> i. if i = 0 then scalar_product x as - s else 2 * x$(i-1) - 1)"
    (is "?init_vec = ?goal_vec")
  proof -
    have "(\<chi> i. \<Sum>j\<in>UNIV.
            real_of_int (if i = 0 then as $ j else if i = j + 1 then 2 else 0) *
            real_of_int (x $ j)) = 
          (\<chi> i. if i = 0 then scalar_product x as else 2 * x$ (i-1))"
    proof -
      have "(\<Sum>j\<in>UNIV. real_of_int (x $ j) * real_of_int (if i = j + 1 then 2 else 0)) =
        2 * real_of_int (x $ (i - 1))" for i 
      proof -
        have "(x $ j) * (if i = j + 1 then 2 else 0) = 
              (if i = j + 1 then 2 * x$j else 0 * x$j)" for j
          by auto
        then have "(\<Sum>j\<in>UNIV. (x $ j) * (if i = j + 1 then 2 else 0)) =
          (\<Sum>j\<in>UNIV. (if i = j + 1 then 2 * x$j else 0 * x$j))"
         by auto
        also have "\<dots> = 2 * x$(i-1)" using sum_if_zero[of "i-1" "(\<lambda>y. 2*x$y)"]
          by (smt (verit, best) eq_diff_eq sum.cong)
        finally have "(\<Sum>j\<in>UNIV. (x $ j) * (if i = j + 1 then 2 else 0)) = 2 * x$(i-1)" by auto
        then have "real_of_int (\<Sum>j\<in>UNIV. (x $ j) * (if i = j + 1 then 2 else 0)) = 
          real_of_int (2 * x$(i-1))" by auto
        then show ?thesis by auto
      qed
      then show ?thesis by (auto simp add: scalar_product_def mult.commute) 
    qed
    also have "\<dots> - (\<chi> i. if i = 0 then real_of_int (snd (as, s)) else 1) =
      (\<chi> i. if i = 0 then scalar_product x as - s else 2* x $ (i-1) -1)"
    unfolding minus_vec_def by auto
    finally have "(\<chi> i. \<Sum>j\<in>UNIV.
            real_of_int (if i = 0 then as $ j else if i = j + 1 then 2 else 0) *
            real_of_int (x $ j))- (\<chi> i. if i = 0 then real_of_int (snd (as, s)) else 1) =
      ?goal_vec" by auto
    then show ?thesis 
      unfolding B_def b_def gen_basis_def reduce_cvp_subset_sum_def gen_t_def 
        matrix_vector_mult_def real_of_int_vec_def vec_map_def 
      by auto
  qed

  then have "infnorm (B *v (real_of_int_vec x) - b) = 
    Max ({\<bar>scalar_product x as - s\<bar>} \<union> {\<bar>2*x$(i-1)-1\<bar> | i. i\<in>UNIV })"
  proof -
    have "infnorm (?goal_vec) = Max {\<bar>?goal_vec $(i-1)\<bar> | i. i\<in>UNIV}" 
      apply (subst infnorm_Max) 

find_theorems Basis

    then have "\<dots> = Max ({\<bar>scalar_product x as - s\<bar>} \<union> {\<bar>2*x$(i-1)-1\<bar> | i. i\<in>UNIV})"
      sorry
    then show ?thesis sorry
  qed
  also have "\<dots> = Max ({0} \<union>  {y. \<exists>i\<in>UNIV. y = \<bar>2*x$(i-1)-1\<bar> })" 
    using x_lin_combo by auto
  also have "\<dots> \<le> Max ({0} \<union>  {1})"
  proof -
    have "\<bar>2*x$(i-1)-1\<bar> = 1" for i::"'n len" using x_binary
      by (smt (z3) insert_iff singletonD)
    then show ?thesis by auto
  qed
  also have "\<dots> \<le> r" using \<open>r=1\<close> by auto
  finally have "infnorm (?init_vec) \<le> r" by blast
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