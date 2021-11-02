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
  "is_lattice L \<equiv> (\<exists>B::(real ^'n ^'n). (\<forall>v\<in>L. \<exists>z::int^'n. 
    B *v (real_of_int_vec z) = v) \<and> independent (columns B))"




definition lin_combo :: "'a list \<Rightarrow> ('a, 'b) vec list \<Rightarrow> ('a::{plus, times, zero}, 'b::finite) vec" where
  "lin_combo zs vs = foldr (+) (map2 (*s) zs vs) (vec 0)"

definition gen_lattice_list :: "(real, 'n) vec list \<Rightarrow> (real, 'n::finite) vec set" where
  "gen_lattice_list vs = {v. \<exists>zs::int list. v = lin_combo zs vs}"

definition gen_lattice :: "(real^'a) ^'a \<Rightarrow> (real, 'a::finite) vec set" where
  "gen_lattice vs = {v. \<exists>z::int ^'a. v = vs *v (real_of_int_vec z)}"

lemma is_lattice_gen_lattice:
  "is_lattice (gen_lattice vs)"
unfolding is_lattice_def gen_lattice_def sorry

text \<open>From now on work over fixed dimension!\<close>

locale fixed_dim = 
fixes n::nat
assumes n_def: "n = CARD ('n::{finite,nontriv})"
    and n1_def: "n+1 = CARD ('n1::{finite,nontriv})"
begin

text \<open>Problem: Since we don't have dependent types in Isabelle, we need to work over a 
  fixed dimension. Here, the CVP of dimension (n+1) reduces to subset sum of dimension n.
  That is:  \<open>dim (CVP) \<ge> 2\<close>.\<close>

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

lemma eq_fun_applic: assumes "x = y" shows "f x = f y"
using assms by auto


lemma sum_if_zero: 
  "(\<Sum>(j::'n len)\<in>UNIV. (if j = i then a j else 0)) = a i"
proof -
  have "(\<Sum>(x::'n len)\<in>UNIV. if x = i then a x else 0) =
  (if i = i then a i else 0) + (\<Sum>x\<in>UNIV - {i}. if x = i then a x else 0)"
  using sum.remove[of "UNIV::'n len set" i "(\<lambda>x. if x = i then a x else 0)"] by auto
  then show ?thesis by auto
qed

lemma Basis_vec_nth: 
  "{x \<bullet> i | i. i\<in>Basis } = {x $ i |i. i\<in>UNIV}"
apply auto 
  subgoal by (metis axis_index cart_eq_inner_axis)
  subgoal using cart_eq_inner_axis by force
done



lemma Max_real_of_int:
  assumes "finite A" "A\<noteq>{}"
  shows "Max (real_of_int ` A) = real_of_int (Max A)"
using mono_Max_commute[OF _ assms, of real_of_int]  by (simp add: mono_def)



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
  have init_eq_goal: "B *v (real_of_int_vec x) - b = 
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
    Max ({\<bar>scalar_product x as - s\<bar>} \<union> {\<bar>2*x$(i-1)-1\<bar> | i. i\<in>UNIV-{0} })"
  proof -
    have "infnorm ?init_vec = infnorm ?goal_vec" using init_eq_goal by auto
    also have "\<dots> = Max {\<bar>?goal_vec $i\<bar> | i. i\<in>UNIV}" 
    proof (subst infnorm_Max)
      have "\<And>v. range (($) (v::(real, 'n mod_ring) vec)) = (\<bullet>) v ` Basis"
        by (metis (no_types) Basis_vec_nth Setcompr_eq_image)
      then show "(MAX v\<in>Basis. \<bar>?goal_vec \<bullet> v\<bar>) = Max {\<bar>?goal_vec $ m\<bar> | m. m \<in> UNIV}"
        by (metis Setcompr_eq_image image_image)
    qed
    also have "\<dots> = Max ({\<bar>scalar_product x as - s\<bar>} \<union> {\<bar>2*x$(i-1)-1\<bar> | i. i\<in>UNIV-{0}})"
    proof - 
      have "{\<bar>?goal_vec $i\<bar> | i. i\<in>UNIV} = 
        {real_of_int \<bar>scalar_product x as - s\<bar>} \<union> {real_of_int \<bar>2*x$(i-1)-1\<bar> | i. i\<in>UNIV-{0}}"
        by auto
      also have "\<dots> = (real_of_int ` {\<bar>scalar_product x as - s\<bar>}) \<union> 
        (real_of_int ` {\<bar>2*x$(i-1)-1\<bar> | i. i\<in>UNIV-{0}})"
      proof -
        have "{real_of_int \<bar>scalar_product x as - s\<bar>} = 
          real_of_int ` {\<bar>scalar_product x as - s\<bar>}" by auto
        moreover have "{real_of_int \<bar>2*x$(i-1)-1\<bar> | i. i\<in>UNIV-{0}} = 
          real_of_int ` {\<bar>2*x$(i-1)-1\<bar> | i. i\<in>UNIV-{0}}" by blast
        ultimately show ?thesis by auto
      qed
      finally have eq: "{\<bar>?goal_vec $i\<bar> | i. i\<in>UNIV} = 
        real_of_int `({\<bar>scalar_product x as - s\<bar>} \<union> {\<bar>2*x$(i-1)-1\<bar> | i. i\<in>UNIV-{0}})"
        by auto
      have "Max {\<bar>?goal_vec $i\<bar> | i. i\<in>UNIV} = 
        Max (real_of_int ` ({\<bar>scalar_product x as - s\<bar>} \<union> {\<bar>2*x$(i-1)-1\<bar> | i. i\<in>UNIV-{0}}))" 
      by (subst eq_fun_applic[OF eq, of Max], simp)
      also have "\<dots> = Max ({\<bar>scalar_product x as - s\<bar>} \<union> {\<bar>2*x$(i-1)-1\<bar> | i. i\<in>UNIV-{0}})"
        using Max_real_of_int[of "{\<bar>scalar_product x as - s\<bar>} \<union> {\<bar>2*x$(i-1)-1\<bar> | i. i\<in>UNIV-{0}}"] 
        by auto
      finally show ?thesis by auto
    qed
    finally show ?thesis by auto
  qed
  also have "\<dots> = Max ({0} \<union> {\<bar>2*x$(i-1)-1\<bar> | i. i\<in>UNIV-{0}})" 
    using x_lin_combo by auto
  also have "\<dots> \<le> Max ({0} \<union> {1})"
  proof -
    have "\<bar>2*x$(i-1)-1\<bar> = 1" for i::"'n len" using x_binary
      by (smt (z3) insert_iff singletonD)
    then show ?thesis by auto
  qed
  also have "\<dots> \<le> r" using \<open>r=1\<close> by auto
  finally have "infnorm (?init_vec) \<le> r" by blast
  moreover have "B *v (real_of_int_vec x)\<in>L" 
    unfolding L_def reduce_cvp_subset_sum_def gen_lattice_def B_def by auto
  ultimately have witness: "\<exists>v\<in>L. infnorm (v - b) \<le> r" by auto
  have L_lattice: "is_lattice L" sorry
  show ?case unfolding gap_cvp_def using L_lattice witness L_def b_def r_def by force


next
  case (2 as s)
  define B where "B = gen_basis as"
  define L where "L = gen_lattice B"
  define b where "b = gen_t s"
  have "\<exists>v\<in>L. infnorm (v - b) \<le> 1" 
    using 2 unfolding gap_cvp_def reduce_cvp_subset_sum_def L_def B_def  b_def by auto
  then obtain v where "v\<in>L" "infnorm (v - b) \<le> 1" by blast
  then obtain zs::"int ^('n len)" where "v = B *v (real_of_int_vec zs)" sorry 

  have "infnorm (v-b) = Max ({\<bar>scalar_product zs as - s\<bar>} \<union> {\<bar>2*zs$(i-1)-1\<bar> | i. i\<in>UNIV-{0} })"
  sorry

  then have "Max ({\<bar>scalar_product zs as - s\<bar>} \<union> {\<bar>2*zs$(i-1)-1\<bar> | i. i\<in>UNIV-{0} })\<le>1"
  sorry

  then have "\<bar>scalar_product zs as - s\<bar>\<le>1" sorry
  have "\<bar>2*zs$(i-1)-1\<bar>\<le>1" if "i\<in>UNIV-{0}" for i sorry



  have "\<forall>i. zs $ i \<in> {0, 1}" sorry 
  moreover have "scalar_product xs as = s" sorry
  ultimately show ?case unfolding subset_sum_def gap_cvp_def
     sorry
qed




text \<open>The Gap-SVP is NP-hard.\<close>
lemma "is_reduction my_fun gap_svp gap_cvp"
oops


(*
eNorm (\<LL> \<infinity> M) f
*)


end