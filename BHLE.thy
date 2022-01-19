theory BHLE

imports Main
        "Jordan_Normal_Form.Matrix"
        infnorm
        Partition
        Lattice_int

begin
text \<open>Bounded Homogeneous Linear Equation Problem\<close>

definition bhle :: "(int vec * int) set" where
  "bhle \<equiv> {(a,k). \<exists>x. a \<bullet> x = 0 \<and> dim_vec x = dim_vec a \<and> 
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
  @ b_list_last as n M))"


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
  "(gen_bhle as) $ ((length as -1) * 5) = 
    b1 (length as) (2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1) (last as)"
proof (unfold gen_bhle_def Let_def, subst vec_of_list_append, subst index_append_vec(1), 
  goal_cases)
  case 1
  then show ?case
    by (subst dim_vec_of_list)+ (subst length_b_list_last, subst length_concat_map_b_list, auto) 
next
  case 2
  then show ?case
  by (subst dim_vec_of_list, subst length_concat_map_b_list, subst vec_index_vec_of_list)+  
     (auto split: if_splits simp add: b_list_last_def)
qed


lemma gen_bhle_last1:
  "(gen_bhle as) $ ((length as -1) * 5 + 1) = 
    b2_last (length as) (2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1)"
proof (unfold gen_bhle_def Let_def, subst vec_of_list_append, subst index_append_vec(1), 
  goal_cases)
  case 1
  then show ?case
    by (subst dim_vec_of_list)+ (subst length_b_list_last, subst length_concat_map_b_list, auto) 
next
  case 2
  then show ?case
  by (subst dim_vec_of_list, subst length_concat_map_b_list, subst vec_index_vec_of_list)+  
     (auto split: if_splits simp add: b_list_last_def)
qed

lemma gen_bhle_last2:
  "(gen_bhle as) $ ((length as -1) * 5 + 2) = 
    b3 (length as) (2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1)"
proof (unfold gen_bhle_def Let_def, subst vec_of_list_append, subst index_append_vec(1), 
  goal_cases)
  case 1
  then show ?case
    by (subst dim_vec_of_list)+ (subst length_b_list_last, subst length_concat_map_b_list, auto) 
next
  case 2
  then show ?case
  by (subst dim_vec_of_list, subst length_concat_map_b_list, subst vec_index_vec_of_list)+  
     (auto split: if_splits simp add: b_list_last_def)
qed


lemma gen_bhle_last3:
  "(gen_bhle as) $ ((length as -1) * 5 + 3) = 
    b4_last (length as) (2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1) (last as)"
proof (unfold gen_bhle_def Let_def, subst vec_of_list_append, subst index_append_vec(1), 
  goal_cases)
  case 1
  then show ?case
    by (subst dim_vec_of_list)+ (subst length_b_list_last, subst length_concat_map_b_list, auto) 
next
  case 2
  then show ?case
  by (subst dim_vec_of_list, subst length_concat_map_b_list, subst vec_index_vec_of_list)+  
     (auto split: if_splits simp add: b_list_last_def)
qed

lemma gen_bhle_last4:
  "(gen_bhle as) $ ((length as-1) * 5 + 4) = 
    b5 (length as) (2*(\<Sum>i<length as. \<bar>as!i\<bar>)+1)"
proof (unfold gen_bhle_def Let_def, subst vec_of_list_append, subst index_append_vec(1), 
  goal_cases)
  case 1
  then show ?case
    by (subst dim_vec_of_list)+ (subst length_b_list_last, subst length_concat_map_b_list, auto) 
next
  case 2
  then show ?case
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
    by (subst dim_vec_of_list)+ (subst length_b_list_last, subst length_concat_map_b_list, auto) 
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
    by (subst dim_vec_of_list)+ (subst length_b_list_last, subst length_concat_map_b_list, auto) 
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
    by (subst dim_vec_of_list)+ (subst length_b_list_last, subst length_concat_map_b_list, auto) 
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
    by (subst dim_vec_of_list)+ (subst length_b_list_last, subst length_concat_map_b_list, auto) 
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
    by (subst dim_vec_of_list)+ (subst length_b_list_last, subst length_concat_map_b_list, auto) 
next
  case 2
  define M where "M = (2 * (\<Sum>i<length as. \<bar>as ! i\<bar>) + 1)"
  then show ?case unfolding M_def[symmetric] using assms
  by (subst dim_vec_of_list, subst length_concat_map_b_list, subst vec_index_vec_of_list)+  
     (subst b_list_nth[OF assms, of 4 M], auto split: if_splits, simp add: b_list_def)
qed

(*
lemma gen_bhle_last:
  "gen_bhle [a] = (let M = 2*\<bar>a\<bar> + 1; i = 1 in
    vec_of_list [b1 i M a, b2_last i M, b3 i M, b4_last i M a, b5 i M])"
unfolding gen_bhle_def Let_def by auto

lemma gen_bhle_split:
  "gen_bhle (a0 # a1 # as) = (let M = 2*(\<Sum>i<length (a0#a1#as). \<bar>(a0#a1#as)!i\<bar>)+1; i=1  in
   vec_of_list ([b1 i M a0, b2 i M, b3 i M, b4 i M a0, b5 i M] @ 
      concat (rec_bhle (i+1) M (a1#as))))"
unfolding gen_bhle_def Let_def by auto

lemma last_rec_bhle_1:
  assumes "a\<noteq>[]"
  shows "last (rec_bhle 1 M a) = concat (rec_bhle (length a) M [last a])"
sorry

lemma concat_rec_bhle':
  assumes "n = length a" "a\<noteq>[]"
  shows "last (rec_bhle 1 M a) = 
    [b1 n M (last a), b2_last n M, b3 n M, b4_last n M (last a), b5 n M]"
unfolding \<open>n= length a\<close> using \<open>a\<noteq>[]\<close> apply (induct a rule: list_nonempty_induct) apply auto
sorry

find_theorems "_!(_-1)"
find_theorems name: list name: induct "_ \<noteq> []"


lemma concat_rec_bhle:
  assumes "j\<in>{0..<5}" "n = length a"
  shows "concat (rec_bhle 1 M a) ! ((n-1)*5+j) = 
    [b1 n M (a!(n-1)), b2_last n M, b3 n M, b4_last n M (a!(n-1)), b5 n M] ! j"
apply auto sorry
*)


lemma split_sum:
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
  "(\<Sum>i=0..<k*l. f i) = (\<Sum>i=0..<k. (\<Sum>j=0..<l. f (i*l+j)))"
  oops


lemma lt_M:
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

lemma split_eq_system:
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





(*
lemma length_concat_rec_bhle:
  "length (concat (rec_bhle i M a)) = 5 * (length a)"
by (induct a arbitrary: i rule: induct_list012, auto)

lemma length_rec_bhle:
  "length (rec_bhle i M a) = length a"
by (induct a arbitrary: i rule: induct_list012, auto)
*)

text \<open>Well-definedness of reduction function\<close>

lemma well_defined_reduction_subset_sum:
  assumes "a \<in> partition_problem"
  shows "reduce_bhle_partition a \<in> bhle"
using assms unfolding partition_problem_def reduce_bhle_partition_def bhle_def
proof (safe, goal_cases)
  case (1 I)
  have "finite I" using 1 by (meson subset_eq_atLeast0_lessThan_finite)
  have "length a > 0" sorry
  then have "a\<noteq>[]" by auto
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
      unfolding plus_x_def minus_x_def sorry
    have map_rew: "map (\<lambda>i. if i \<in> I then plus_x else minus_x) [0..<n] =
          map (\<lambda>i. if i \<in> I then plus_x else minus_x) [0..<i] @
          map (\<lambda>i. if i \<in> I then plus_x else minus_x) [i..<n]"
    using that(1) sorry
    have "concat (map (\<lambda>i. if i \<in> I then plus_x else minus_x) [0..<n]) ! (i * 5 + j) =
          concat (map (\<lambda>i. if i \<in> I then plus_x else minus_x) [i..<n]) ! j"
     by (subst map_rew, subst concat_append, subst len_rew)
        (subst nth_append_length_plus[of 
          "concat (map (\<lambda>i. if i \<in> I then plus_x else minus_x) [0..<i])"], simp)
    also have "\<dots> = (if i \<in> I then plus_x!j else minus_x!j)" sorry
    finally show ?thesis unfolding x_def by (subst vec_index_vec_of_list, auto)
  qed

find_theorems nth append
  
  have x_nth0:
    "x $ (i*5) = (if i\<in>I then plus_x ! 0 else minus_x ! 0)" if "i<n" for i sorry

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
    apply (subst gen_bhle_last0[of a])
    apply (subst gen_bhle_last1[of a])
    apply (subst gen_bhle_last2[of a])
    apply (subst gen_bhle_last3[of a])
    apply (subst gen_bhle_last4[of a]) using x_nth[of "n-1"]
    apply (subst x_nth[of "length a-1"], simp add: n_def, linarith)+
    apply (subst x_nth0[of "length a-1"], simp add: n_def)
    apply (unfold M_def plus_x_def minus_x_def)
    apply (auto simp add: eval_nat_numeral last_conv_nth) 
    done
    finally show ?thesis by auto
  qed


  have "(gen_bhle a) \<bullet> x = 0"
  proof -
    have "(gen_bhle a) \<bullet> x = (\<Sum>i = 0..<n*5. (gen_bhle a) $ i * x $ i) "
      unfolding M_def n_def gen_bhle_def scalar_prod_def dimx_eq_5dima by (auto)
    also have "\<dots> = (\<Sum>i = 0..<n. (\<Sum>j=0..<5. (gen_bhle a) $ (i*5+j) * x $ (i*5+j)))"
      (*using sum_split_idx_prod[of "(\<lambda>i. (gen_bhle a) $ i * x $ i)" n 5]  by auto*) sorry
    also have "\<dots> = (\<Sum>i = 0..<n-1. (\<Sum>j=0..<5. (gen_bhle a) $ (i*5+j) * x $ (i*5+j))) 
      + (\<Sum>j=0..<5. (gen_bhle a) $ ((n-1)*5+j) * x $ ((n-1)*5+j))"
      by (subst sum.atLeast0_lessThan_Suc[of "\<lambda>i. (\<Sum>j = 0..<5. (gen_bhle a) $ (i*5+j) *
         x $ (i*5+j))" "n-1", symmetric], use \<open>length a > 0\<close> n_def in \<open>auto\<close>)
    also have "\<dots> = (\<Sum>i\<in>I-{n-1}. (\<Sum>j=0..<5. (gen_bhle a) $ (i*5+j) * x $ (i*5+j))) 
      + (\<Sum>i\<in>{0..<n}-I-{n-1}. (\<Sum>j=0..<5. (gen_bhle a) $ (i*5+j) * x $ (i*5+j))) 
      + (\<Sum>j=0..<5. (gen_bhle a) $ ((n-1)*5+j) * x $ ((n-1)*5+j))" 
    sorry (*
    proof -
      have sets: "I - {n - 1} \<union> (({0..<n} - I) - {n - 1}) = {0..<n-1}"
        using "1"(1) n_def by auto
      then have ?thesis
        by (subst sum.union_disjoint[of "I - {n - 1}" "{0..<n} - I - {n - 1}", symmetric]) 
           (auto simp add: \<open>finite I\<close>)
    qed (* What is happening here?!*) *)
    also have "\<dots> = (\<Sum>i\<in>I-{n-1}. (b1 (i+1) M (a!i)) - (b2 (i+1) M) - (b5 (i+1) M)) 
      + (\<Sum>i\<in>{0..<n}-I-{n-1}. (b3 (i+1) M)  - (b4 (i+1) M (a!i)) + (b5 (i+1) M)) 
      + (if n-1\<in>I then (b1 n M (a!(n-1))) - (b2_last n M) - (b5 n M) 
          else (b3 n M)  - (b4_last n M (a!(n-1))) + (b5 n M))"
    proof -
      have "(\<Sum>i\<in>I-{n-1}. (\<Sum>j=0..<5. (gen_bhle a) $ (i*5+j) * x $ (i*5+j))) =
            (\<Sum>i\<in>I-{n-1}. (b1 (i+1) M (a!i)) - (b2 (i+1) M) - (b5 (i+1) M)) "
      using gen_bhle_in_I[ of _ I n a x M] by (meson sum.cong)
      moreover have "(\<Sum>i\<in>{0..<n}-I-{n-1}. (\<Sum>j=0..<5. (gen_bhle a) $ (i*5+j) * x $ (i*5+j))) =
            (\<Sum>i\<in>{0..<n}-I-{n-1}. (b3 (i+1) M)  - (b4 (i+1) M (a!i)) + (b5 (i+1) M)) "
      using gen_bhle_not_in_I[of _ n I a x M] by (meson sum.cong)
      ultimately show ?thesis using gen_bhle_last by auto
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
    have set: "set (?x_list) = {-1,0,1::int}" using \<open>length a > 0\<close> unfolding n_def sorry
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




text \<open>NP-hardness of reduction function\<close>

lemma NP_hardness_reduction_subset_sum:
  assumes "reduce_bhle_partition a \<in> bhle"
  shows "a \<in> partition_problem"
sorry



text \<open>The Gap-SVP is NP-hard.\<close>
lemma "is_reduction reduce_bhle_partition partition_problem bhle"
unfolding is_reduction_def
proof (safe, goal_cases)
  case (1 a)
  then show ?case using well_defined_reduction_subset_sum by auto
next
  case (2 a)
  then show ?case using NP_hardness_reduction_subset_sum by auto
qed

end