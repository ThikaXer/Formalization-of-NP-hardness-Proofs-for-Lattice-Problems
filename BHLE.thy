theory BHLE

imports Main
        "Jordan_Normal_Form.Matrix"
        infnorm
        Partition
        Lattice_int
        Digits_2

begin
text \<open>Bounded Homogeneous Linear Equation Problem\<close>

definition bhle :: "(int vec * int) set" where
  "bhle \<equiv> {(a,k). \<exists>x. a \<bullet> x = 0 \<and> dim_vec x = dim_vec a \<and> dim_vec a > 0 \<and>
      x \<noteq> 0\<^sub>v (dim_vec x) \<and> \<parallel>x\<parallel>\<^sub>\<infinity> \<le> k}"

text \<open>Reduction of bounded homogeneous linear equation to partition problem\<close>
(*Remember: i runs from 1 to n=length a*)
definition b1 :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "b1 i M a = a + M * (5^(4*i-4) + 5^(4*i-3) + 5^(4*i-1))"

definition b2 :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "b2 i M = M * (5^(4*i-3) + 5^(4*i))"

definition b2_last :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "b2_last i M = M * (5^(4*i-3) + 1)"

definition b3 :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "b3 i M =  M * (5^(4*i-4) + 5^(4*i-2))"

definition b4 :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "b4 i M a = a + M * (5^(4*i-2) + 5^(4*i-1) + 5^(4*i))"

definition b4_last :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "b4_last i M a = a + M * (5^(4*i-2) + 5^(4*i-1) + 1)"

definition b5 :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "b5 i M = M * (5^(4*i-1))"

(*
fun rec_bhle where
  "rec_bhle i M [] = []" |
  "rec_bhle i M (a # []) = [[b1 i M a, b2_last i M, b3 i M, b4_last i M a, b5 i M]]" |
  "rec_bhle i M (a # as) = [b1 i M a, b2 i M, b3 i M, b4 i M a, b5 i M] # (rec_bhle (i+1) M as)"

definition gen_bhle :: "int list \<Rightarrow> int vec" where
  "gen_bhle as = vec_of_list (concat (rec_bhle 1 (2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1) as))"
*)

definition b_list :: "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list" where
  "b_list as i M = [b1 (i+1) M (as!i), b2 (i+1) M, b3 (i+1) M, b4 (i+1) M (as!i), b5 (i+1) M]"

definition b_list_last :: "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list" where
  "b_list_last as n M = [b1 n M (last as), b2_last n M, b3 n M, b4_last n M (last as), b5 n M]"

definition gen_bhle :: "int list \<Rightarrow> int vec" where
"gen_bhle as = (let M = 2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1; n = length as in
  vec_of_list (concat 
  (map (\<lambda>i. b_list as i M) [0..<n-1]) 
  @ (if n>0 then b_list_last as n M else [])))"

(*
try this out
value "(2*(\<Sum>i<length [1,2::nat]. \<bar>[1,2::nat]!i\<bar>)+1)"
value "b1 1 7 1"
value "b4_last 2 7 2"
value "rec_bhle 1 7 [1,2::nat]"
*)

definition reduce_bhle_partition:: "(int list) \<Rightarrow> ((int vec) * int)" where
  "reduce_bhle_partition \<equiv> (\<lambda> a. (gen_bhle a, 1))"



text \<open>Lemmas for proof\<close>

lemma length_concat_map_5: 
  "length (concat (map (\<lambda>i. [f1 i, f2 i, f3 i, f4 i, f5 i]) xs)) = length xs * 5" 
by (induct xs, auto)

lemma dim_vec_gen_bhle:
  assumes "as\<noteq>[]"
  shows "dim_vec (gen_bhle as) = 5 * (length as)"
using assms 
proof (induct as rule: list_nonempty_induct)
  case (single x)
  then show ?case unfolding gen_bhle_def Let_def b_list_def b_list_last_def by auto
next
  case (cons x xs)
  define M where "M = (2 * (\<Sum>i<length (x # xs). \<bar>(x # xs) ! i\<bar>) + 1)"
  then show ?case using cons unfolding gen_bhle_def b_list_def b_list_last_def 
    Let_def M_def[symmetric]
    by (subst dim_vec_of_list)+ 
       (use length_concat_map_5[of 
      "(\<lambda>i. b1 (i + 1) M ((x#xs) ! i))"  
      "(\<lambda>i. b2 (i + 1) M             )"
      "(\<lambda>i. b3 (i + 1) M             )"
      "(\<lambda>i. b4 (i + 1) M ((x#xs) ! i))"
      "(\<lambda>i. b5 (i + 1) M             )"] in \<open>simp\<close>)
qed

lemma dim_vec_gen_bhle_empty:
  "dim_vec (gen_bhle []) = 0"
unfolding gen_bhle_def by auto


(*Lemmas about length*)

lemma length_b_list:
  "length (b_list a i M) = 5" unfolding b_list_def by auto

lemma length_b_list_last:
  "length (b_list_last a n M) = 5" unfolding b_list_last_def by auto

lemma length_concat_map_b_list:
  "length (concat (map (\<lambda>i. b_list as i M) [0..<k])) = 5 * k"
by (subst length_concat)(simp add: comp_def length_b_list sum_list_triv) 

(*Last values of gen_bhle*)
lemma gen_bhle_last0:
  assumes "length as > 0"
  shows "(gen_bhle as) $ ((length as -1) * 5) = 
    b1 (length as) (2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1) (last as)"
proof (unfold gen_bhle_def Let_def, subst vec_of_list_append, subst index_append_vec(1), 
  goal_cases)
  case 1
  then show ?case using assms
    by (subst dim_vec_of_list)+ (split if_splits,
        subst length_b_list_last, subst length_concat_map_b_list, auto) 
next
  case 2
  then show ?case using assms
  by (subst dim_vec_of_list, subst length_concat_map_b_list, subst vec_index_vec_of_list)+  
     (auto split: if_splits simp add: b_list_last_def)
qed


lemma gen_bhle_last1:
  assumes "length as > 0"
  shows "(gen_bhle as) $ ((length as -1) * 5 + 1) = 
    b2_last (length as) (2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1)"
proof (unfold gen_bhle_def Let_def, subst vec_of_list_append, subst index_append_vec(1), 
  goal_cases)
  case 1
  then show ?case using assms
    by (subst dim_vec_of_list)+ (split if_split, 
      subst length_b_list_last, subst length_concat_map_b_list, auto) 
next
  case 2
  then show ?case using assms
  by (subst dim_vec_of_list, subst length_concat_map_b_list, subst vec_index_vec_of_list)+  
     (auto split: if_splits simp add: b_list_last_def)
qed

lemma gen_bhle_last2:
  assumes "length as > 0"
  shows "(gen_bhle as) $ ((length as -1) * 5 + 2) = 
    b3 (length as) (2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1)"
proof (unfold gen_bhle_def Let_def, subst vec_of_list_append, subst index_append_vec(1), 
  goal_cases)
  case 1
  then show ?case using assms
    by (subst dim_vec_of_list)+ (split if_split, 
      subst length_b_list_last, subst length_concat_map_b_list, auto) 
next
  case 2
  then show ?case using assms
  by (subst dim_vec_of_list, subst length_concat_map_b_list, subst vec_index_vec_of_list)+  
     (auto split: if_splits simp add: b_list_last_def)
qed


lemma gen_bhle_last3:
  assumes "length as > 0"
  shows "(gen_bhle as) $ ((length as -1) * 5 + 3) = 
    b4_last (length as) (2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1) (last as)"
proof (unfold gen_bhle_def Let_def, subst vec_of_list_append, subst index_append_vec(1), 
  goal_cases)
  case 1
  then show ?case using assms
    by (subst dim_vec_of_list)+ (split if_split, 
      subst length_b_list_last, subst length_concat_map_b_list, auto) 
next
  case 2
  then show ?case using assms 
  by (subst dim_vec_of_list, subst length_concat_map_b_list, subst vec_index_vec_of_list)+  
     (auto split: if_splits simp add: b_list_last_def)
qed

lemma gen_bhle_last4:
  assumes "length as > 0"
  shows "(gen_bhle as) $ ((length as-1) * 5 + 4) = 
    b5 (length as) (2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1)"
proof (unfold gen_bhle_def Let_def, subst vec_of_list_append, subst index_append_vec(1), 
  goal_cases)
  case 1
  then show ?case using assms
    by (subst dim_vec_of_list)+ (split if_split, 
      subst length_b_list_last, subst length_concat_map_b_list, auto) 
next
  case 2
  then show ?case using assms
  by (subst dim_vec_of_list, subst length_concat_map_b_list, subst vec_index_vec_of_list)+  
     (auto split: if_splits simp add: b_list_last_def)
qed

(*Up to last values of gen_bhle*)

lemma b_list_nth:
  assumes "i<length as-1" "j<5"
  shows "concat (map (\<lambda>i. b_list as i M) [0..<length as - 1]) ! (i * 5 + j) = 
      b_list as i M ! j"
proof -
  have "map (\<lambda>i. b_list as i M) [0..<length as - 1] = 
        map (\<lambda>i. b_list as i M) [0..<i] @
        map (\<lambda>i. b_list as i M) [i..<length as - 1]"
    using assms
    by (metis append_self_conv2 less_zeroE linorder_neqE_nat map_append upt.simps(1) upt_append)
  then have "concat (map (\<lambda>i. b_list as i M) [0..<length as - 1]) =
        concat (map (\<lambda>i. b_list as i M) [0..<i]) @
        concat (map (\<lambda>i. b_list as i M) [i..<length as - 1])"
    by (subst concat_append[of "map (\<lambda>i. b_list as i M) [0..<i]" 
      "map (\<lambda>i. b_list as i M) [i..<length as -1]", symmetric], auto)
  moreover have "concat (map (\<lambda>i. b_list as i M) [i..<length as - 1]) =
    (b_list as i M @ concat (map (\<lambda>i. b_list as i M) [i+1..<length as - 1]))" 
    using assms upt_conv_Cons by fastforce
  ultimately have concat_unfold: "concat (map (\<lambda>i. b_list as i M) [0..<length as - 1]) =
        concat (map (\<lambda>i. b_list as i M) [0..<i]) @
        (b_list as i M @ concat (map (\<lambda>i. b_list as i M) [i+1..<length as - 1]))"
    by auto
  have "concat (map (\<lambda>i. b_list as i M) [0..<length as - 1]) ! (i * 5 + j) =
    (b_list as i M @ concat (map (\<lambda>i. b_list as i M) [i+1..<length as - 1])) ! j"
    unfolding concat_unfold 
    by (subst nth_append_length_plus[of "concat (map (\<lambda>i. b_list as i M) [0..<i])" 
      "b_list as i M @ concat (map (\<lambda>i. b_list as i M) [i + 1..<length as - 1])" j, symmetric])
       (subst length_concat_map_b_list, simp add: mult.commute)
  moreover have "(b_list as i M @ concat (map (\<lambda>i. b_list as i M) [i+1..<length as - 1])) ! j =
    b_list as i M ! j" using assms length_b_list
    by (subst nth_append[of "b_list as i M" "concat (map (\<lambda>i. b_list as i M) 
      [i+1..<length as - 1])" j], auto)
  ultimately show ?thesis by auto
qed


lemma b_list_nth0:
  assumes "i<length as-1"
  shows "concat (map (\<lambda>i. b_list as i M) [0..<length as - 1]) ! (i * 5) = 
      b_list as i M ! 0"
using b_list_nth[OF assms, of 0] by auto

lemma gen_bhle_0:
  assumes "i<length as-1"
  shows "(gen_bhle as) $ (i * 5) = 
    b1 (i+1) (2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1) (as!i)"
proof (unfold gen_bhle_def Let_def, subst vec_of_list_append, subst index_append_vec(1), 
  goal_cases)
  case 1
  then show ?case using assms
    by (subst dim_vec_of_list)+ (split if_split, 
      subst length_b_list_last, subst length_concat_map_b_list, auto) 
next
  case 2
  define M where "M = (2 * (\<Sum>i<length as. \<bar>as ! i\<bar>) + 1)"
  then show ?case unfolding M_def[symmetric] using assms
  by (subst dim_vec_of_list, subst length_concat_map_b_list, subst vec_index_vec_of_list)+ 
     (subst b_list_nth0[OF assms, of M], auto split: if_splits, simp add: b_list_def)
qed

lemma gen_bhle_1:
  assumes "i<length as-1"
  shows "(gen_bhle as) $ (i * 5 + 1) = 
    b2 (i+1) (2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1)"
proof (unfold gen_bhle_def Let_def, subst vec_of_list_append, subst index_append_vec(1), 
  goal_cases)
  case 1
  then show ?case using assms
    by (subst dim_vec_of_list)+ (split if_split, 
      subst length_b_list_last, subst length_concat_map_b_list, auto) 
next
  case 2
  define M where "M = (2 * (\<Sum>i<length as. \<bar>as ! i\<bar>) + 1)"
  then show ?case unfolding M_def[symmetric] using assms
  by (subst dim_vec_of_list, subst length_concat_map_b_list, subst vec_index_vec_of_list)+  
     (subst b_list_nth[OF assms, of 1 M], auto split: if_splits, simp add: b_list_def)
qed

lemma gen_bhle_2:
  assumes "i<length as-1"
  shows "(gen_bhle as) $ (i * 5 + 2) = 
    b3 (i+1) (2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1)"
proof (unfold gen_bhle_def Let_def, subst vec_of_list_append, subst index_append_vec(1), 
  goal_cases)
  case 1
  then show ?case using assms
    by (subst dim_vec_of_list)+ (split if_split, 
      subst length_b_list_last, subst length_concat_map_b_list, auto) 
next
  case 2
  define M where "M = (2 * (\<Sum>i<length as. \<bar>as ! i\<bar>) + 1)"
  then show ?case unfolding M_def[symmetric] using assms
  by (subst dim_vec_of_list, subst length_concat_map_b_list, subst vec_index_vec_of_list)+  
     (subst b_list_nth[OF assms, of 2 M], auto split: if_splits, simp add: b_list_def)
qed

lemma gen_bhle_3:
  assumes "i<length as-1"
  shows "(gen_bhle as) $ (i * 5 + 3) = 
    b4 (i+1) (2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1) (as!i)"
proof (unfold gen_bhle_def Let_def, subst vec_of_list_append, subst index_append_vec(1), 
  goal_cases)
  case 1
  then show ?case using assms
    by (subst dim_vec_of_list)+ (split if_split, 
      subst length_b_list_last, subst length_concat_map_b_list, auto) 
next
  case 2
  define M where "M = (2 * (\<Sum>i<length as. \<bar>as ! i\<bar>) + 1)"
  then show ?case unfolding M_def[symmetric] using assms
  by (subst dim_vec_of_list, subst length_concat_map_b_list, subst vec_index_vec_of_list)+  
     (subst b_list_nth[OF assms, of 3 M], auto split: if_splits, simp add: b_list_def)
qed

lemma gen_bhle_4:
  assumes "i<length as-1"
  shows "(gen_bhle as) $ (i * 5 + 4) = 
    b5 (i+1) (2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1)"
proof (unfold gen_bhle_def Let_def, subst vec_of_list_append, subst index_append_vec(1), 
  goal_cases)
  case 1
  then show ?case using assms
    by (subst dim_vec_of_list)+ (split if_split, 
      subst length_b_list_last, subst length_concat_map_b_list, auto) 
next
  case 2
  define M where "M = (2 * (\<Sum>i<length as. \<bar>as ! i\<bar>) + 1)"
  then show ?case unfolding M_def[symmetric] using assms
  by (subst dim_vec_of_list, subst length_concat_map_b_list, subst vec_index_vec_of_list)+  
     (subst b_list_nth[OF assms, of 4 M], auto split: if_splits, simp add: b_list_def)
qed


lemma split_sum_list:
  assumes "\<forall>i<n. a!i = b!i + M * c!i" 
          "length (a::int list) = n" 
          "length (b::int list) = n" 
          "length (c::int list) = n" 
          "length (x::int list) = n"
  shows "(\<Sum>i<n. x!i * a!i) = (\<Sum>i<n. x!i * b!i) + M * (\<Sum>i<n. x!i * c!i)"
proof -
  have "(\<Sum>i<n. x!i * a!i) = (\<Sum>i<n. x!i * ( b!i + M * c!i))" using assms(1) by auto
  also have "\<dots> = (\<Sum>i<n. x!i * b!i) + (\<Sum>i<n. M * x!i * c!i)"
    by (simp add: distrib_left mult.commute mult.left_commute)
  also have "\<dots> = (\<Sum>i<n. x!i * b!i) + M * (\<Sum>i<n. x!i * c!i)"
    using sum_distrib_left[symmetric, where r=M and f="(\<lambda>i. x!i*c!i)" and A = "{0..<n}"]  
    by (metis (no_types, lifting) lessThan_atLeast0 mult.assoc sum.cong)
  finally show ?thesis by blast
qed

lemma sum_split_idx_prod:
  "(\<Sum>i=0..<k*l::nat. f i) = (\<Sum>i=0..<k. (\<Sum>j=0..<l. f (i*l+j)))"
proof -
  have set_rew: "{0..<k*l} = (\<lambda>(i,j). i*l+j) ` ({0..<k} \<times> {0..<l})"
  proof (safe, goal_cases)
    case (1 x)
    have "x = (\<lambda>(i,j). i*l+j) (x div l, x mod l)" by auto
    moreover have "(x div l, x mod l)\<in>{0..<k} \<times> {0..<l}" using 1 less_mult_imp_div_less
      by (metis le_less_trans lessThan_atLeast0 lessThan_iff mem_Sigma_iff
        mod_less_divisor mult_zero_right neq0_conv zero_le)
    ultimately show ?case by blast
  next
    case (2 x i j)
    then show ?case 
    by (auto, metis less_nat_zero_code linorder_neqE_nat mod_lemma mult.commute nat_mod_lem)
  qed
  have inj: "inj_on (\<lambda>(i, y). i * l + y) ({0..<k} \<times> {0..<l})" 
    unfolding inj_on_def by (auto) 
      (metis add.commute add_right_imp_eq linorder_neqE_nat mod_mult_self2 mult.commute 
        mult_cancel_right nat_mod_lem not_less_zero, 
       metis add.commute le0 le_less_trans mod_mult_self2 mult.commute nat_mod_lem)
  have "(\<Sum> i\<in>{0..<k*l}. f i) = (\<Sum>(i,j)\<in>{0..<k}\<times>{0..<l}. f (i*l+j))" 
    unfolding set_rew using inj
    by (subst sum.reindex[of "(\<lambda>(i, j). i * l + j)" "({0..<k} \<times> {0..<l})" f])
       (auto simp add: prod.case_distrib)
  also have "\<dots> = (\<Sum>i\<in>{0..<k}. (\<Sum>j\<in>{0..<l}. f (i*l+j)))"
    using sum.cartesian_product[of "(\<lambda>i j. f (i*l+j))" "{0..<l}" "{0..<k}", symmetric]
    by auto
  finally show ?thesis by auto
qed


lemma lt_M_list:
  assumes "length (b::int list) = n" 
          "length (x::int list) = n"
          "M > k * (\<Sum>i<n. \<bar>b!i\<bar>)"
          "\<forall>i<n. \<bar>x!i\<bar> \<le>k" 
          "k>0"
  shows "\<bar>(\<Sum>i<n. x!i * b!i)\<bar> < M"
proof - 
  have "\<bar>(\<Sum>i<n. x!i * b!i)\<bar> \<le> (\<Sum>i<n. \<bar>x!i * b!i\<bar>)" using sum_abs by auto
  also have "\<dots> = (\<Sum>i<n. \<bar>x!i\<bar> * \<bar>b!i\<bar>)" using abs_mult by metis
  also have "\<dots> \<le> (\<Sum>i<n. k * \<bar>b!i\<bar>)" using assms
    by (smt (verit, del_insts) lessThan_iff mult.commute mult_left_mono sum_mono)
  also have "\<dots> = k * (\<Sum>i<n. \<bar>b!i\<bar>)" using sum_distrib_left by metis
  finally have "\<bar>(\<Sum>i<n. x!i * b!i)\<bar> \<le> k * (\<Sum>i<n. \<bar>b!i\<bar>)" by linarith
  then show ?thesis using assms by auto
qed


(*not on lists, using functions instead*)
(* declare [[show_types]]*)

lemma lt_M:
  assumes "M > (\<Sum>i<(n::nat). \<bar>b i\<bar>::int)"
          "\<forall>i<n. \<bar>x i\<bar> \<le> 1" 
  shows "\<bar>(\<Sum>i<n. x i * b i)\<bar> < M"
proof - 
  have "\<bar>(\<Sum>i<(n::nat). x i * b i)::int\<bar> \<le> (\<Sum>i<n. \<bar>x i * b i\<bar>)" using sum_abs by auto
  moreover have "\<dots> = (\<Sum>i<n. \<bar>x i\<bar> * \<bar>b i\<bar>)" using abs_mult by metis
  moreover have "\<dots> \<le> (\<Sum>i<n. \<bar>b i\<bar>)" using assms 
    by (smt (verit, best) lessThan_iff mult_cancel_right2 sum_mono zero_less_mult_iff)
  moreover have "\<dots> = (\<Sum>i<n. \<bar>b i\<bar>)" using sum_distrib_left by metis
  ultimately have "\<bar>(\<Sum>i<n. x i * b i)\<bar> \<le> (\<Sum>i<n. \<bar>b i\<bar>)" by linarith
  then show ?thesis using assms by auto
qed



lemma split_sum:
  "(\<Sum>i<(n::nat). x i * (a i + M * b i)::int) = (\<Sum>i<n. x i * a i) + M * (\<Sum>i<n. x i * b i)"
proof -
  have "(\<Sum>i<(n::nat). x i * (a i + M * b i)) = (\<Sum>i<n. x i * a i) + (\<Sum>i<n. M * x i * b i)"
    by (simp add: distrib_left mult.commute mult.left_commute)
  also have "\<dots> = (\<Sum>i<n. x i * a i) + M * (\<Sum>i<n. x i * b i)"
    using sum_distrib_left[symmetric, where r=M and f="(\<lambda>i. x i*b i)" and A = "{0..<n}"]  
    by (metis (no_types, lifting) lessThan_atLeast0 mult.assoc sum.cong)
  finally show ?thesis by blast
qed



lemma split_eq_system:
  assumes "M > (\<Sum>i<n::nat. \<bar>a i\<bar>::int)"
          "\<forall>i<n. \<bar>x i\<bar> \<le> 1" 
          "(\<Sum>i<n. x i * (a i + M * b i)) = 0" 
  shows   "(\<Sum>i<n. x i * a i) = 0 \<and> (\<Sum>i<n. x i * b i) = 0"
using assms proof (safe, goal_cases)
  case 1
  then show ?case 
  proof (cases "(\<Sum>i<n. x i * b i) = 0")
    case True
    then show ?thesis using assms(3) split_sum[of x a M b n] by auto
  next
    case False
    then have "\<bar>(\<Sum>i<n. x i * a i)\<bar> < M * \<bar>(\<Sum>i<n. x i * b i)\<bar>" 
      using lt_M[OF assms(1) assms(2)] False
      by (smt (verit, best) mult_less_cancel_left2)
    moreover have "\<bar>(\<Sum>i<n. x i * a i)\<bar> = M * \<bar>(\<Sum>i<n. x i * b i)\<bar>" 
      using assms(3) split_sum[of x a M b n] calculation by linarith
    ultimately have False by linarith 
    then show ?thesis by auto
  qed
next
  case 2
  then show ?case 
  proof (cases "(\<Sum>i<n. x i * b i) = 0")
    case True
    then show ?thesis using split_sum 2 using lt_M[OF assms(1) assms(2)]
       by auto
  next
    case False
    then have "\<bar>(\<Sum>i<n. x i * a i)\<bar> < M * \<bar>(\<Sum>i<n. x i * b i)\<bar>" 
      using lt_M[OF assms(1) assms(2)] False
      by (smt (verit, best) mult_less_cancel_left2)
    moreover have "\<bar>(\<Sum>i<n. x i * a i)\<bar> = M * \<bar>(\<Sum>i<n. x i * b i)\<bar>" 
      using split_sum[of x a M b n] assms calculation by linarith
    ultimately have False by linarith 
    then show ?thesis by auto
  qed
qed



(*list*)

lemma split_eq_system_list:
  assumes "\<forall>i<n. a!i = b!i + M * c!i" 
          "length (a::int list) = n" 
          "length (b::int list) = n" 
          "length (c::int list) = n" 
          "length (x::int list) = n"
          "M > k * (\<Sum>i<n. \<bar>b!i\<bar>)"
          "\<forall>i<n. \<bar>x!i\<bar> \<le>k" 
          "k>0"
  shows "(\<Sum>i<n. x!i * a!i) = 0 \<longleftrightarrow> (\<Sum>i<n. x!i * b!i) = 0 \<and> (\<Sum>i<n. x!i * c!i) = 0"
using assms proof (safe, goal_cases)
  case 1
  then show ?case 
  proof (cases "(\<Sum>i<n. x!i * c!i) = 0")
    case True
    then show ?thesis using split_sum 1 by auto
  next
    case False
    then have "\<bar>(\<Sum>i<n. x!i * b!i)\<bar> < M * \<bar>(\<Sum>i<n. x!i * c!i)\<bar>" 
      using lt_M[OF assms(3) assms(5) assms(6) assms(7) assms(8)] False 
      by (smt (verit, best) mult_less_cancel_left2)
    moreover have "\<bar>(\<Sum>i<n. x!i * b!i)\<bar> = M * \<bar>(\<Sum>i<n. x!i * c!i)\<bar>" 
      using split_sum[OF assms(1) assms(2) assms(3) assms(4) assms(5)] assms
      by (smt (z3) "1"(9) lt_M[OF assms(3) assms(5) assms(6) assms(7) assms(8)]
        mult_le_0_iff mult_minus_right)
    ultimately have False by linarith 
    then show ?thesis by auto
  qed
next
  case 2
  then show ?case 
  proof (cases "(\<Sum>i<n. x!i * b!i) = 0")
    case True
    then show ?thesis using split_sum 2 using lt_M[OF assms(3) assms(5) assms(6) assms(7) assms(8)]
       by auto
  next
    case False
    then have "\<bar>(\<Sum>i<n. x!i * b!i)\<bar> < M * \<bar>(\<Sum>i<n. x!i * c!i)\<bar>" 
      using lt_M[OF assms(3) assms(5) assms(6) assms(7) assms(8)] False
      by (smt (verit, best) "2"(8) "2"(9) mult_eq_0_iff mult_le_cancel_left1 
        split_sum[OF assms(1) assms(2) assms(3) assms(4) assms(5)])
    moreover have "\<bar>(\<Sum>i<n. x!i * b!i)\<bar> = M * \<bar>(\<Sum>i<n. x!i * c!i)\<bar>" 
      using split_sum[OF assms(1) assms(2) assms(3) assms(4) assms(5)] assms
      by (smt (z3) "2"(9) lt_M[OF assms(3) assms(5) assms(6) assms(7) assms(8)]
         mult_le_0_iff mult_minus_right)
    ultimately have False by linarith 
    then show ?thesis by auto
  qed
next
  case 3
  then show ?case using split_sum[OF assms(1) assms(2) assms(3) assms(4) assms(5)] by auto
qed




text \<open>Well-definedness of reduction function\<close>

lemma well_defined_reduction_subset_sum:
  assumes "a \<in> partition_problem_nonzero"
  shows "reduce_bhle_partition a \<in> bhle"
using assms unfolding partition_problem_nonzero_def reduce_bhle_partition_def bhle_def
proof (safe, goal_cases)
  case (1 I)
  have "finite I" using 1 by (meson subset_eq_atLeast0_lessThan_finite)
  have "length a > 0" using \<open>a\<noteq>[]\<close> by auto
  define n where "n = length a"
  define minus_x::"int list" where "minus_x = [0,0,1,-1,1]"
  define plus_x::"int list" where "plus_x = [1,-1,0,0,-1]"
  define x::"int vec" where 
    "x = vec_of_list (concat (map (\<lambda>i. if i\<in>I then plus_x else minus_x) [0..<n]))"
  have dimx_eq_5dima:"dim_vec x = length a * 5" unfolding x_def plus_x_def minus_x_def n_def 
    by (induct a , auto)
  then have "0 < dim_vec x" using \<open>length a > 0\<close> by auto
  define M where "M = 2*(\<Sum>i<length a. \<bar>a!i\<bar>)+1"

(*lemmas for proof*)
  have x_nth: 
    "x $ (i*5+j) = (if i\<in>I then plus_x ! j else minus_x ! j)" if "i<n" "j<5" for i j 
  proof -
    have len_rew: "i*5 = length (concat (map (\<lambda>i. if i \<in> I then plus_x else minus_x) [0..<i]))"
    proof -
      have if_rew: "(\<lambda>i. if i\<in>I then plus_x else minus_x) = 
        (\<lambda>i. [(if i\<in>I then plus_x!0 else minus_x!0), (if i\<in>I then plus_x!1 else minus_x!1),
              (if i\<in>I then plus_x!2 else minus_x!2), (if i\<in>I then plus_x!3 else minus_x!3),
              (if i\<in>I then plus_x!4 else minus_x!4)])"
       unfolding plus_x_def minus_x_def by auto
      then show ?thesis
      unfolding if_rew length_concat_map_5[of "(\<lambda>i. if i\<in>I then plus_x!0 else minus_x!0)"
        "(\<lambda>i. if i\<in>I then plus_x!1 else minus_x!1)" "(\<lambda>i. if i\<in>I then plus_x!2 else minus_x!2)"
        "(\<lambda>i. if i\<in>I then plus_x!3 else minus_x!3)" "(\<lambda>i. if i\<in>I then plus_x!4 else minus_x!4)"
        "[0..<i]"] by auto
    qed
    have map_rew: "map f [0..<n] = map f [0..<i] @ map f [i..<n]" for f ::"nat \<Rightarrow> int list"
      using that(1) by (metis list_trisect map_append n_def upt_conv_Cons)
    have "concat (map (\<lambda>i. if i \<in> I then plus_x else minus_x) [0..<n]) ! (i * 5 + j) =
          concat (map (\<lambda>i. if i \<in> I then plus_x else minus_x) [i..<n]) ! j"
     by (subst map_rew, subst concat_append, subst len_rew)
        (subst nth_append_length_plus[of 
          "concat (map (\<lambda>i. if i \<in> I then plus_x else minus_x) [0..<i])"], simp)
    also have "\<dots> = (if i \<in> I then plus_x!j else minus_x!j)"
    proof -
      have concat_rewr: "concat (map f [i..<n])=
       (f i) @ (concat (map f [i+1..<n]))" for f::"nat \<Rightarrow> int list"
        by (simp add: that(1) upt_conv_Cons)
      have length_if: "length (if i \<in> I then plus_x else minus_x) = 5" 
        unfolding plus_x_def minus_x_def by auto
      show ?thesis unfolding concat_rewr nth_append length_if using \<open>j<5\<close> by auto
    qed
    finally show ?thesis unfolding x_def by (subst vec_index_vec_of_list, auto)
  qed

  
  have x_nth0:
    "x $ (i*5) = (if i\<in>I then plus_x ! 0 else minus_x ! 0)" if "i<n" for i 
    using that by (subst x_nth[of i 0,symmetric], auto)

  have gen_bhle_in_I:
    "(\<Sum>j=0..<5. (gen_bhle a) $ (i*5+j) * x $ (i*5+j)) = 
     (b1 (i+1) M (a!i)) - (b2 (i+1) M) - (b5 (i+1) M)" if "i\<in>I-{length a-1}" for i
  proof -
    have "(\<Sum>j=0..<5. (gen_bhle a) $ (i*5+j) * x $ (i*5+j)) =
            (gen_bhle a) $ (i*5) * x $ (i*5) +
            (gen_bhle a) $ (i*5+1) * x $ (i*5+1) +
            (gen_bhle a) $ (i*5+2) * x $ (i*5+2) +
            (gen_bhle a) $ (i*5+3) * x $ (i*5+3) +
            (gen_bhle a) $ (i*5+4) * x $ (i*5+4)"
      by (simp add: eval_nat_numeral)
    also have "\<dots> = (b1 (i+1) M (a!i)) - (b2 (i+1) M) - (b5 (i+1) M)" 
    using that 1 n_def \<open>length a > 0\<close>
    apply (subst gen_bhle_0[of i a], fastforce)
    apply (subst gen_bhle_1[of i a], fastforce)
    apply (subst gen_bhle_2[of i a], fastforce)
    apply (subst gen_bhle_3[of i a], fastforce)
    apply (subst gen_bhle_4[of i a], fastforce)
    apply (subst x_nth[of i], fastforce, fastforce)+
    apply (subst x_nth0[of i], fastforce)
    apply (unfold M_def plus_x_def)
    apply (simp add: eval_nat_numeral) 
    done
    finally show ?thesis by auto
  qed

  have gen_bhle_not_in_I:
    "(\<Sum>j=0..<5. (gen_bhle a) $ (i*5+j) * x $ (i*5+j)) =
     (b3 (i+1) M)  - (b4 (i+1) M (a!i)) + (b5 (i+1) M)" if  "i\<in>{0..<n}-I-{n-1}" for i
  proof -
    have "(\<Sum>j=0..<5. (gen_bhle a) $ (i*5+j) * x $ (i*5+j)) =
            (gen_bhle a) $ (i*5) * x $ (i*5) +
            (gen_bhle a) $ (i*5+1) * x $ (i*5+1) +
            (gen_bhle a) $ (i*5+2) * x $ (i*5+2) +
            (gen_bhle a) $ (i*5+3) * x $ (i*5+3) +
            (gen_bhle a) $ (i*5+4) * x $ (i*5+4)"
      by (simp add: eval_nat_numeral)
    also have "\<dots> = (b3 (i+1) M)  - (b4 (i+1) M (a!i)) + (b5 (i+1) M)" 
    using that 1 n_def \<open>length a > 0\<close>
    apply (subst gen_bhle_0[of i a], fastforce)
    apply (subst gen_bhle_1[of i a], fastforce)
    apply (subst gen_bhle_2[of i a], fastforce)
    apply (subst gen_bhle_3[of i a], fastforce)
    apply (subst gen_bhle_4[of i a], fastforce)
    apply (subst x_nth[of i], fastforce, fastforce)+
    apply (subst x_nth0[of i], fastforce)
    apply (unfold M_def minus_x_def)
    apply (simp add: eval_nat_numeral) 
    done
    finally show ?thesis by auto
  qed

  have gen_bhle_last:
    "(\<Sum>j=0..<5. (gen_bhle a) $ ((n-1)*5+j) * x $ ((n-1)*5+j)) =
     (if n-1\<in>I then (b1 n M (a!(n-1))) - (b2_last n M) - (b5 n M) 
      else (b3 n M)  - (b4_last n M (a!(n-1))) + (b5 n M))"
  proof -
    have "(\<Sum>j=0..<5. (gen_bhle a) $ ((n-1)*5+j) * x $ ((n-1)*5+j)) =
            (gen_bhle a) $ ((n-1)*5) * x $ ((n-1)*5) +
            (gen_bhle a) $ ((n-1)*5+1) * x $ ((n-1)*5+1) +
            (gen_bhle a) $ ((n-1)*5+2) * x $ ((n-1)*5+2) +
            (gen_bhle a) $ ((n-1)*5+3) * x $ ((n-1)*5+3) +
            (gen_bhle a) $ ((n-1)*5+4) * x $ ((n-1)*5+4)"
      by (simp add: eval_nat_numeral)
    also have "\<dots> = (if n-1\<in>I then (b1 n M (a!(n-1))) - (b2_last n M) - (b5 n M) 
      else (b3 n M)  - (b4_last n M (a!(n-1))) + (b5 n M))" 
    using 1 n_def \<open>length a > 0\<close> unfolding n_def
    apply (subst gen_bhle_last0[of a, OF \<open>length a > 0\<close>])
    apply (subst gen_bhle_last1[of a, OF \<open>length a > 0\<close>])
    apply (subst gen_bhle_last2[of a, OF \<open>length a > 0\<close>])
    apply (subst gen_bhle_last3[of a, OF \<open>length a > 0\<close>])
    apply (subst gen_bhle_last4[of a, OF \<open>length a > 0\<close>]) using x_nth[of "n-1"]
    apply (subst x_nth[of "length a-1"], simp add: n_def, linarith)+
    apply (subst x_nth0[of "length a-1"], simp add: n_def)
    apply (unfold M_def plus_x_def minus_x_def)
    apply (auto simp add: eval_nat_numeral last_conv_nth) 
    done
    finally show ?thesis by auto
  qed

(*actual proof*)
  have "(gen_bhle a) \<bullet> x = 0"
  proof -
    define f where "f = (\<lambda>i. (\<Sum>j = 0..<5. gen_bhle a $ (i*5+j) * x $ (i*5+j)))"
    have "(gen_bhle a) \<bullet> x = (\<Sum>i = 0..<n*5. (gen_bhle a) $ i * x $ i) "
      unfolding M_def n_def gen_bhle_def scalar_prod_def dimx_eq_5dima by (auto)
    also have "\<dots> = (\<Sum>i = 0..<n. f i)" unfolding f_def
      using sum_split_idx_prod[of "(\<lambda>i. (gen_bhle a) $ i * x $ i)" n 5]  by auto
    also have "\<dots> = (\<Sum>i = 0..<n-1. f i) + f (n-1)"
      by (subst sum.atLeast0_lessThan_Suc[of "(\<lambda>i. f i)" "n-1", symmetric], 
        use \<open>length a > 0\<close> n_def in \<open>auto\<close>)
    also have "\<dots> = (\<Sum>i\<in>I-{n-1}. f i) + (\<Sum>i\<in>{0..<n}-I-{n-1}. f i) + f (n-1)" 
    proof -
      have "I - {n - 1} \<union> (({0..<n} - I) - {n - 1}) = {0..<n-1}"
        using "1"(1) n_def by auto
      then show ?thesis
        by (subst sum.union_disjoint[of "I - {n - 1}" "{0..<n} - I - {n - 1}", symmetric]) 
           (auto simp add: \<open>finite I\<close>)
    qed
    also have "\<dots> = (\<Sum>i\<in>I-{n-1}. (b1 (i+1) M (a!i)) - (b2 (i+1) M) - (b5 (i+1) M)) 
      + (\<Sum>i\<in>{0..<n}-I-{n-1}. (b3 (i+1) M)  - (b4 (i+1) M (a!i)) + (b5 (i+1) M)) 
      + (if n-1\<in>I then (b1 n M (a!(n-1))) - (b2_last n M) - (b5 n M) 
          else (b3 n M)  - (b4_last n M (a!(n-1))) + (b5 n M))"
    proof -
      have "(\<Sum>i\<in>I-{n-1}. f i) =
            (\<Sum>i\<in>I-{n-1}. (b1 (i+1) M (a!i)) - (b2 (i+1) M) - (b5 (i+1) M)) "
      unfolding f_def using gen_bhle_in_I by (simp add: n_def)
      moreover have "(\<Sum>i\<in>{0..<n}-I-{n-1}. f i) =
            (\<Sum>i\<in>{0..<n}-I-{n-1}. (b3 (i+1) M)  - (b4 (i+1) M (a!i)) + (b5 (i+1) M)) "
      unfolding f_def using gen_bhle_not_in_I by (meson sum.cong)
      ultimately show ?thesis unfolding f_def using gen_bhle_last by auto
    qed
    also have "\<dots> = (\<Sum>i\<in>I-{n-1}.  (a!i) + (M * 5^(4*(i+1)-4) - M * 5^(4*(i+1)))) 
      + (\<Sum>i\<in>{0..<n}-I-{n-1}. - (a!i) + (M * 5^(4*(i+1)-4) - M * 5^(4*(i+1)))) 
      + (if n-1\<in>I then (a!(n-1)) + M * 5^(4*n-4) - M*1 
          else -(a!(n-1)) + M * 5^(4*n-4) - M*1)"
    proof -
      have "b1 (i + 1) M (a ! i) - b2 (i + 1) M - b5 (i + 1) M =
         (a!i) + (M * 5^(4*(i+1)-4) - M * 5^(4*(i+1)))" if "i\<in>I-{n-1}" for i
      unfolding b1_def b2_def b5_def
      by (smt (verit, best) add_uminus_conv_diff right_diff_distrib)
      moreover have "b3 (i + 1) M - b4 (i + 1) M (a ! i) + b5 (i + 1) M =
        - (a!i) + (M * 5^(4*(i+1)-4) - M * 5^(4*(i+1)))" if "i\<in>{0..<n} - I - {n - 1}" for i
      unfolding b3_def b4_def b5_def 
      by (smt (verit, best) add_uminus_conv_diff right_diff_distrib)
      moreover have "b1 n M (a ! (n - 1)) - b2_last n M - b5 n M =
        (a!(n-1)) + M * 5^(4*n-4) - M"
      unfolding b1_def b2_last_def b5_def by (simp add: distrib_left)
      moreover have "b3 n M - b4_last n M (a ! (n - 1)) + b5 n M = 
        -(a!(n-1)) + M * 5^(4*n-4) - M"
      unfolding b3_def b4_last_def b5_def by (simp add: distrib_left)
      ultimately show ?thesis by auto
    qed
    also have "\<dots> = (\<Sum>i\<in>I-{n-1}.  (a!i)) + (\<Sum>i\<in>{0..<n}-I-{n-1}. - (a!i))
      + M * (\<Sum>i\<in>{0..<n-1}. 5^(4*(i+1)-4) - 5^(4*(i+1)))
      + (if n-1\<in>I then (a!(n-1)) else -(a!(n-1))) + M * 5^(4*n-4) - M"
    proof -
      have sets1: "{0..<n - 1} \<inter> I = I - {n -1}" using "1"(1) n_def by auto
      have sets2: "{0..<n - 1} - I = {0..<n}- I - {n-1}" using "1"(1) n_def by auto
      have subs: "(\<Sum>i\<in>I-{n-1}. M * 5^(4*i+4*1-4) - M * 5^(4*i+4*1)) +
            (\<Sum>i\<in>{0..<n}-I-{n-1}. M * 5^(4*i+4*1-4) - M * 5^(4*i+4*1)) =
            (\<Sum>i = 0..<n-1. M * 5^(4*i+4*1-4) - M * 5^(4*i+4*1))" 
      using sum.Int_Diff[of "{0..<n-1}" "(\<lambda>i. M * 5^(4*i+4*1-4) - M * 5^(4*i+4*1))" "I"]
        \<open>finite I\<close> unfolding sets1 sets2  by auto
      show ?thesis
        apply (subst distrib_left)+ 
        apply (subst sum.distrib)+ 
        apply (subst sum_distrib_left) 
        apply (subst right_diff_distrib)+ 
        apply (subst subs[symmetric]) 
        apply auto 
        done
    qed
    also have "\<dots> = (\<Sum>i\<in>I. (a!i)) + (\<Sum>i\<in>{0..<n}-I. - (a!i))
      + M * (\<Sum>i\<in>{0..<n-1}. 5^(4*(i+1)-4) - 5^(4*(i+1)))
      + M * 5^(4*n-4) - M"
    proof (auto split: if_splits, goal_cases inI notinI)
      case inI
      then show ?case  by (subst sum.Int_Diff[of "I" _ "{n-1}"], auto simp add: \<open>finite I\<close>)
    next
      case notinI
      then have "n-1\<in>{0..<n}-I" using \<open>length a > 0\<close> n_def by auto
      then show ?case by (subst sum.Int_Diff[of "{0..<n}-I" _ "{n-1}"], auto simp add: \<open>finite I\<close>)
    qed
    also have "\<dots> = M * (\<Sum>i\<in>{0..<n-1}. 5^(4*(i+1)-4) - 5^(4*(i+1)))
      + M * 5^(4*n-4) - M"
      unfolding n_def using 1(2) by (subst sum_negf, auto)
    also have "\<dots> = M * ((\<Sum>i\<in>{1..<n}. 5^(4*i-4) - 5^(4*i)) + 5^(4*n-4) - 1)"
    proof -
      have sums: "(\<Sum>i = Suc 0..<Suc (n - 1). 5 ^ (4 * i - 4) - 5 ^ (4 * i)) =
                  sum ((\<lambda>i. 5 ^ (4*(i+1) - 4) - 5 ^ (4*(i+1)))) {0..<n - 1}"
      using sum.atLeast_Suc_lessThan_Suc_shift[of "(\<lambda>i. 5^(4*i-4) - 5^(4*i))" 0 "n-1"] 
      unfolding comp_def by auto
      show ?thesis
      by (subst distrib_left[symmetric], subst right_diff_distrib, subst mult_1_right)
         (subst sums[symmetric], use \<open>0 < length a\<close> n_def in \<open>force\<close>)
    qed
    also have "\<dots> = M * (((\<Sum>i\<in>{1..<n}. 5^(4*i-4)) + 5^(4*n-4)) - ((\<Sum>i\<in>{1..<n}. 5^(4*i)) + 1))"
      using sum.distrib[of "(\<lambda>i. 5^(4*i-4))" "(\<lambda>i. (-1) * 5^(4*i))" "{1..<n}"] 
      by (simp add: sum_subtractf)
    also have "\<dots> = M * ((\<Sum>i\<in>{1..<n+1}. 5^(4*i-4)) - (\<Sum>i\<in>{0..<n}. 5^(4*i)))"
      using sum.atLeastLessThan_Suc[of 1 n "(\<lambda>i. 5^(4*i-4))"]
            sum.atLeast_Suc_lessThan[of 0 n "(\<lambda>i. 5^(4*i))"]
      by (smt (verit, best) One_nat_def Suc_eq_plus1 Suc_leI \<open>0 < length a\<close> mult_eq_0_iff 
        n_def power_0)
    also have "\<dots> = M * ((\<Sum>i\<in>{0..<n}. 5^(4*i)) - (\<Sum>i\<in>{0..<n}. 5^(4*i)))"
      using sum.atLeast_Suc_lessThan_Suc_shift[of "(\<lambda>i. 5^(4*i-4))" 0 n] by auto
    also have "\<dots> = 0" by auto
    finally show ?thesis by blast
  qed

  moreover have "dim_vec x = dim_vec (gen_bhle a)" 
    using dim_vec_gen_bhle[OF \<open>a\<noteq>[]\<close>] dimx_eq_5dima by simp
  moreover have "x \<noteq> 0\<^sub>v (dim_vec x)"
  proof (rule ccontr)
    assume "\<not> x \<noteq> 0\<^sub>v (dim_vec x)"
    then have "x = 0\<^sub>v (dim_vec x)" by auto
    have "dim_vec x > 4" using \<open>0 < length a\<close> dimx_eq_5dima by linarith
    have "x $ 4 = 0" using \<open>dim_vec x > 4\<close>
      by (subst \<open>x=0\<^sub>v (dim_vec x)\<close>) (subst index_zero_vec[of 4], auto)
    moreover have "x $ 4 \<noteq> 0" 
    proof (cases "0\<in>I")
      case True
      then have rewr: "x = vec_of_list (plus_x @ 
        concat (map (\<lambda>i. if i\<in>I then plus_x else minus_x) [1..<n]))" unfolding x_def 
        using \<open>0 < length a\<close> n_def upt_conv_Cons by auto
      then show ?thesis by (subst rewr, unfold plus_x_def, simp add: numeral_Bit0)
    next
      case False
      then have rewr: "x = vec_of_list (minus_x @ 
        concat (map (\<lambda>i. if i\<in>I then plus_x else minus_x) [1..<n]))" unfolding x_def 
        using \<open>0 < length a\<close> n_def upt_conv_Cons by auto
      then show ?thesis by (subst rewr) (unfold minus_x_def, simp add: numeral_Bit0)
    qed
    ultimately show False by auto
  qed
  moreover have "\<parallel>x\<parallel>\<^sub>\<infinity> \<le> 1"
  proof -
    let ?x_list = "(concat (map (\<lambda>i. if i \<in> I then ([1, - 1, 0, 0, - 1]::int list)
      else ([0, 0, 1, - 1, 1]::int list)) [0..<n]))"
    have set: "set (?x_list) = {-1,0,1::int}" 
      using \<open>length a > 0\<close> 1 unfolding n_def 
      by (subst set_concat, subst set_map)(auto simp add: atLeast0LessThan)
    have "?x_list ! i \<in> {-1,0,1::int}" if "i< length ?x_list" for i
      using nth_mem[OF that] by (subst set[symmetric], auto)
    then have "x$i\<in>{-1,0,1::int}" if "i<dim_vec x" for i 
      using that unfolding x_def plus_x_def minus_x_def
      by (smt (z3) dim_vec_of_list vec_of_list_index)
    then have "\<bar>x$i\<bar>\<le>1" if "i<dim_vec x" for i using that by fastforce
    then show ?thesis unfolding linf_norm_vec_Max 
      by (subst Max_le_iff, auto simp add: exI[of "(\<lambda>i. dim_vec x > i)" 0] \<open>dim_vec x > 0\<close>)
  qed
  ultimately show ?case by (subst exI[of _ x], auto) 
qed

value " {i. ([1,2,0,0,1]::nat list)! i \<noteq> 0}"

text \<open>NP-hardness of reduction function\<close>

lemma NP_hardness_reduction_subset_sum:
  assumes "reduce_bhle_partition a \<in> bhle"
  shows "a \<in> partition_problem_nonzero"
using assms unfolding reduce_bhle_partition_def bhle_def partition_problem_nonzero_def
proof (safe, goal_cases)
  case (1 x)
  have "length a > 0" sorry
  define I where "I = {i\<in>{0..<length a}. x $ (5*i)\<noteq>0}"
  define n where "n = length a"
  have dim_vec_x_5n: "dim_vec x = 5 * n" unfolding n_def using 1
  by (metis dim_vec_gen_bhle dim_vec_gen_bhle_empty less_not_refl2)
  have "length a > 0" using dim_vec_gen_bhle_empty 1(3) by auto
  moreover have "I\<subseteq>{0..<length a}" using 1 I_def by auto
  moreover have "sum ((!) a) I = sum ((!) a) ({0..<length a} - I)" 
  proof -
    define M where "M = 2 * (\<Sum>i<length a. \<bar>a ! i\<bar>) + 1"


(*
have "gen_bhle a \<bullet> x = (\<Sum>i<n. (\<Sum>j<5. (gen_bhle a) $ (i*5+j) * x $ (i*5+j)))" sorry
*)

    define a0 where "a0 = (\<lambda>i. if i mod (5::nat) \<in> {0,3} then a!(i div 5) else 0)"
    define a1 where "a1 = (\<lambda>i. if i mod (5::nat) \<in> {0,2} then 1 else 0::int)"
    define a2 where "a2 = (\<lambda>i. if i mod (5::nat) \<in> {0,1} then 1 else 0::int)"
    define a3 where "a3 = (\<lambda>i. if i mod (5::nat) \<in> {2,3} then 1 else 0::int)"
    define a4 where "a4 = (\<lambda>i. if i mod (5::nat) \<in> {0,3,4} then 1 else 0::int)"
    define a5 where "a5 = (\<lambda>i. if i mod (5::nat) \<in> {1,3} then 
                          (if i div 5 < n-1 then 5^(4*(i div 5 +1)) else 1) else 0::int)"
    
    define a0_rest where "a0_rest = 
          (\<lambda>i. a1 i * 5 ^ (4 * (i div 5+1)) + a2 i * 5 ^ (4 * (i div 5+1) + 1) +
          a3 i * 5 ^ (4 * (i div 5+1) + 2) + a4 i * 5 ^ (4 * (i div 5+1) + 3) + a5 i)"

    have gen_bhle_nth: "gen_bhle a $ i =  (a0 i + M * (a0_rest i))" 
      if "i<dim_vec (gen_bhle a)" for i
    unfolding gen_bhle_def Let_def unfolding M_def[symmetric] b_list_def b_list_last_def sorry


    have  "gen_bhle a \<bullet> x = (\<Sum>i<5*n. x $ i * 
      (a0 i + M * a0_rest i))"
      using 1(1) gen_bhle_nth  unfolding scalar_prod_def Let_def dim_vec_x_5n 1(2)[symmetric]
      by (smt (verit, best) lessThan_atLeast0 lessThan_iff mult.commute sum.cong)

    then have sum_gen_bhle: "(\<Sum>i<5 * n. x $ i * (a0 i + M * a0_rest i)) = 0"
      using 1(1) by simp


    (* have sum_gen_bhle: "gen_bhle a \<bullet> x = (\<Sum>i<n. a ! i * c i +  
      M * (d1 i * 5^i + d2 i * 5^(i+1) + d3 i * 5^(i+2) + d4 i * 5^(i+4)))"
      using 1(1) unfolding gen_bhle_def scalar_prod_def Let_def sorry*)

    have eq_0: "(\<Sum>i<n. (x $ (i*5) + x $ (i*5+3)) * a!i) = 0" and
         eq_0': "(\<Sum>i<5*n. x$i * (a0_rest i)) = 0"
    proof -
      have *: "(\<Sum>i<5*n. \<bar>a0 i\<bar>) < M"
      proof -
        have "(\<Sum>i<5*n. \<bar>a0 i\<bar>) = (\<Sum>i<n. (\<Sum>j<5. \<bar>a0 (i*5+j)\<bar>))"
          using sum_split_idx_prod[of "(\<lambda>i. \<bar>a0 i\<bar>)" n 5]
          by (simp add: lessThan_atLeast0 mult.commute)
        also have "\<dots> = (\<Sum>i<n. (\<Sum>j<5::nat. \<bar>if j \<in> {0, 3} then a ! i else 0\<bar>))" 
          unfolding a0_def by (subst div_mult_self3[of 5], simp,
            subst sum.cong[of "{..<n}" "{..<n}"], auto,
            subst sum.cong[of "{..<5}" "{..<5}"], auto)
        also have "\<dots> = (\<Sum>i<n. 2 * \<bar>a ! i\<bar>)" by (auto simp add: eval_nat_numeral)
        also have "\<dots> = 2 * (\<Sum>i<n. \<bar>a ! i\<bar>)"
          by (simp add: sum_distrib_left)
        finally show ?thesis unfolding M_def n_def by linarith
      qed
      have **: "\<forall>i<5*n. \<bar>x $ i\<bar> \<le> 1" using 1(5)
        by (metis dim_vec_x_5n ge_trans vec_index_le_linf_norm)
      have "(\<Sum>i<5*n. x $ i * a0 i) = 0 \<and> (\<Sum>i<5*n. x$i * (a0_rest i)) = 0"
        using split_eq_system[OF * ** sum_gen_bhle] by auto
      moreover have "(\<Sum>i<5*n. x $ i * a0 i) = (\<Sum>i<n. (x $ (i*5) + x $ (i*5+3)) * a!i)"
      proof -
        have "(\<Sum>j = i*5..<i*5+5. x$j * (if j mod 5 \<in> {0, 3} then a!(j div 5) else 0)) =
              (x$(i*5) + x$(i*5+3)) * a ! i" if "i<n" for i
        proof -
          have div_rule: "(i * 5 + xa) div 5 = i" if "xa <5" for xa using that by auto
          have "(\<Sum>j = i*5..<i*5+5. x$j * (if j mod 5 \<in> {0, 3} then a!(j div 5) else 0)) =
            sum (\<lambda>j. x$j * (if j mod 5 \<in> {0, 3} then a!(j div 5) else 0)) ((+) (i * 5) ` {0..<5})"
            by (simp add: add.commute)
          also have "\<dots> = (\<Sum>j<5. x$(i*5 + j) * (if j \<in> {0, 3} then a!i else 0))" 
            apply (subst sum.reindex[of "(\<lambda>j. i*5+j)" "{0..<5}"], simp) 
            apply (unfold comp_def) using mod_mult_self3[of i 5] div_rule
            apply (metis (no_types, lifting) One_nat_def lessThan_atLeast0 lessThan_iff 
              nat_mod_lem not_less_eq not_numeral_less_one sum.cong) done
          also have "\<dots> = x$(i*5 + 0) * a!i + x$(i*5 + 3) * a!i" 
            by (auto simp add: eval_nat_numeral split: if_splits)
          finally show ?thesis by (simp add: distrib_left mult.commute)
        qed
        then show ?thesis unfolding a0_def by (subst mult.commute[of 5 n]) 
           (subst sum.nat_group[symmetric], auto)
      qed
      ultimately show "(\<Sum>i<n. (x $ (i*5) + x $ (i*5+3)) * a!i) = 0" and
                      "(\<Sum>i<5*n. x$i * (a0_rest i)) = 0" by auto
    qed
  
    let ?eq_0'_left = "(\<Sum>i<5*n. x$i * (a0_rest i))"
    interpret digits 5 by (simp add: digits_def)
    have digit_a0_rest: "digit ?eq_0'_left k = 0" for k
      by (simp add: eq_0' digit_altdef)




    define d1 where "d1 = (\<lambda>i. x$(i*5) + x$(i*5+2))"
    define d2 where "d2 = (\<lambda>i. x$(i*5) + x$(i*5+1))"
    define d3 where "d3 = (\<lambda>i. x$(i*5+2) + x$(i*5+3))"
    define d4 where "d4 = (\<lambda>i. x$(i*5) + x$(i*5+3) + x$(i*5+4))"
    define d5 where "d5 = (\<lambda>i. x$(5*i+1) + x$(5*i+3))"



    have rewrite_digits:"(\<Sum>i<5*n. x$i * (a0_rest i)) = 
       d5 (n-1) + d1 0 +
      (\<Sum>j\<in>{0..<n}. d2 j * 5 ^(4*j+1)) + 
      (\<Sum>j\<in>{0..<n}. d3 j * 5 ^(4*j+2)) + 
      (\<Sum>j\<in>{0..<n}. d4 j * 5 ^(4*j+3)) +
      (\<Sum>j\<in>{1..<n}. (d1 j + d5 (j-1)) * 5 ^(4*j))" 
      (is "(\<Sum>i<5*n. x$i * (a0_rest i)) = ?digits")
    proof -
      let ?x_a0_rest = "(\<lambda>i j. x$(i*5+j) * (a0_rest (i*5+j)))"
      have "(\<Sum>i<5*n. x$i * (a0_rest i)) = (\<Sum>i<n. (\<Sum>j<5. ?x_a0_rest i j))"
        using sum_split_idx_prod[of "(\<lambda>i. x$i * (a0_rest i))" n 5]
        by (simp add: lessThan_atLeast0 mult.commute)
      moreover have "\<dots> = (\<Sum>i<n.
        ?x_a0_rest i 0 + ?x_a0_rest i 1 + ?x_a0_rest i 2 + ?x_a0_rest i 3 + ?x_a0_rest i 4)"
        by (simp add: eval_nat_numeral)
      moreover have "\<dots> = 
          ?x_a0_rest 0 0 + ?x_a0_rest 0 1 + ?x_a0_rest 0 2 + ?x_a0_rest 0 3 + ?x_a0_rest 0 4 +
        (\<Sum>i\<in>{1..<n}.
          ?x_a0_rest i 0 + ?x_a0_rest i 1 + ?x_a0_rest i 2 + ?x_a0_rest i 3 + ?x_a0_rest i 4 )" 
        unfolding n_def using sum.atLeast_Suc_lessThan[OF \<open>length a > 0\<close>, of
        "(\<lambda>i. ?x_a0_rest i 0 + ?x_a0_rest i 1 + ?x_a0_rest i 2 + ?x_a0_rest i 3 + ?x_a0_rest i 4)"] 
        using One_nat_def lessThan_atLeast0 by presburger
      moreover have 
sorry
find_theorems sum "_+_" name: lessThan

      then show ?thesis unfolding a0_rest_def a1_def a2_def a3_def a4_def a5_def 
          sorry
    qed



    
    moreover have "d5 (n-1) + d1 0 < 5" sorry
    
    moreover have "d3 j<5" if "j\<in>{0..<n}" for j sorry
    moreover have "d4 j<5" if "j\<in>{0..<n}" for j sorry
    moreover have "d1 j + d5 j <5" if "j\<in>{1..<n}" for j sorry

    have d2_lt_5: "d2 j<5" if "j\<in>{0..<n}" for j sorry

    have "digit ?eq_0'_left (i*4+1) = d2 i" 
      if "i\<in>{0..<n}" for i 
      apply (subst digit_altdef) apply (subst rewrite_digits) 
      proof -
      have "(d5 (n - 1) + d1 0 + 
     (\<Sum>j = 0..<n. d2 j * 5 ^ (4 * j + 1)) +
     (\<Sum>j = 0..<n. d3 j * 5 ^ (4 * j + 2)) +
     (\<Sum>j = 0..<n. d4 j * 5 ^ (4 * j + 3)) +
     (\<Sum>j = 1..<n. (d1 j + d5 (j - 1)) * 5 ^ (4 * j))) div
       5 ^ (i * 4 + 1) =
     (\<Sum>j = i..<n. d2 j * 5 ^ (4 * j + 1)) +
     (\<Sum>j = i..<n. d3 j * 5 ^ (4 * j + 2)) +
     (\<Sum>j = i..<n. d4 j * 5 ^ (4 * j + 3)) +
     (\<Sum>j = (i+1)..<n. (d1 j + d5 (j - 1)) * 5 ^ (4 * j))"
      
      using d2_lt_5[OF that] apply auto
    sorry


find_theorems "(_ + _) div _"


    (*k-th digit is zero*)
    ultimately have "digit ?digits k = 0" if "k\<in>{0..<4*n}" for k sorry

find_theorems "_ mod _" "_ div _" "_ = 0"


    have eq_1: "x$(i*5) + x$(i*5+2) + x$((i-1)*5+1) + x$((i-1)*5+3) = 0" if "i\<in>{1..<n}" for i sorry
    have eq_2: "x$0 + x$2 + x$((n-1)*5+1) + x$((n-1)*5+3) = 0" sorry
    have eq_3: "x$(i*5) + x$(i*5+1) = 0" if "i\<in>{0..<n}" for i sorry
    have eq_4: "x$(i*5+2) + x$(i*5+3) = 0" if "i\<in>{0..<n}" for i sorry
    have eq_5: "x$(i*5) + x$(i*5+3) + x$(i*5+4) = 0" if "i\<in>{0..<n}" for i sorry
    
    have "x$(5*i) + x$(5*i+2) = x$(5*(i-1)) + x$(5*(i-1)+2)" if "i\<in>{1..<n}" for i sorry
    define w where "w = x$0 + x$2"
  (*This is the weight of the solution, since $x_{i,0} + x_{i,2}$ does not depend on the index i.*)
    

    have "\<bar>w\<bar> \<le> 1" using eq_4 w_def sorry

    moreover have "w\<noteq>0" sorry

    ultimately have "w=1 \<or> w = -1" by auto
    then consider (pos) "w=1" | (neg) "w=-1" by blast
    then show ?thesis
    proof cases
      case pos
      then show ?thesis sorry
    next
      case neg
      then show ?thesis sorry
    qed
  qed
  ultimately show ?case by auto
qed



text \<open>The Gap-SVP is NP-hard.\<close>
lemma "is_reduction reduce_bhle_partition partition_problem_nonzero bhle"
unfolding is_reduction_def
proof (safe, goal_cases)
  case (1 a)
  then show ?case using well_defined_reduction_subset_sum by auto
next
  case (2 a)
  then show ?case using NP_hardness_reduction_subset_sum by auto
qed

end