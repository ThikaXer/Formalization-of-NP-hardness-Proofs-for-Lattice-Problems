theory Lattice_vec

imports Main
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


lemma[simp]: "dim_vec (real_of_int_vec v) = dim_vec v" 
  unfolding real_of_int_vec_def by auto

lemma real_of_int_vec_nth[simp, intro]: "i<dim_vec v \<Longrightarrow> (real_of_int_vec v) $ i = real_of_int (v$i)"
by (simp add: real_of_int_vec_def)

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


text \<open>Some lemmas for vectors\<close>



end