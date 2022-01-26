theory Digits_2
  imports Digits
begin

text \<open>In order to use representation of numbers in a basis \<open>base\<close> and to calculate the conversion 
to and from integers, we introduce the following locale.\<close>
locale digits =
  fixes base :: int
  assumes base_pos: "base > 0"
begin

text \<open>Conversion from basis base to integers: \<open>from_digits n d\<close>

\begin{tabular}{lcp{8cm}}
  n:& \<open>nat\<close>& length of representation in basis base\\
  d:& \<open>nat \<Rightarrow> nat\<close>& function of digits in basis base where \<open>d i\<close> is the $i$-th digit in basis base\\
  output:& \<open>nat\<close>& natural number corresponding to $d(n-1) \dots d(0)$ as integer\\
\end{tabular}
\<close>
fun from_digits :: "nat \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> int" where
  "from_digits 0 d = 0"
| "from_digits (Suc n) d = d 0 + base * from_digits n (d \<circ> Suc)"

text \<open>Alternative definition using sum:\<close>
lemma from_digits_altdef: "from_digits n d = (\<Sum>i<n. d i * base ^ i)"
  by (induction n d rule: from_digits.induct)
     (auto simp add: sum.lessThan_Suc_shift o_def sum_distrib_left 
       sum_distrib_right mult_ac simp del: sum.lessThan_Suc)

text \<open>Digit in basis base of some integer number: \<open>digit x i\<close>

\begin{tabular}{lcp{8cm}}
  x:& \<open>nat\<close>& integer\\
  i:& \<open>nat\<close>& index\\
  output:& \<open>nat\<close>& $i$-th digit of representation in basis base of $x$\\
\end{tabular}
\<close>
fun digit :: "int \<Rightarrow> nat \<Rightarrow> int" where
  "digit x 0 = x mod base"
| "digit x (Suc i) = digit (x div base) i"

text \<open>Alternative definition using divisor and modulo:\<close>
lemma digit_altdef: "digit x i = (x div (base ^ i)) mod base"
  by (induction x i rule: digit.induct, simp)
     (use base_pos zdiv_zmult2_eq in \<open>force\<close>) 

text \<open>Every digit must be smaller that the base.\<close>
lemma digit_less_base: "digit x i < base"
  using base_pos by (auto simp: digit_altdef)

text \<open>A representation in basis \<open>base\<close> of length $n$ must be less than $\<open>base\<close> ^ n$.\<close>
lemma from_digits_less: 
  assumes "\<forall>i<n. \<bar>d i\<bar> < base" 
  shows "from_digits n d < base ^ n"
using assms proof (induct n d rule: from_digits.induct)
  case (2 n d)
  have "from_digits n (d \<circ> Suc) \<le> base ^ n -1" using 2 
    by (simp add: "2.hyps")
  moreover have "\<bar>d 0\<bar> \<le> base -1" using 2 by simp
  ultimately have "d 0 + base * from_digits n (d \<circ> Suc) \<le> 
      base - 1 + base * (base^(n) - 1)" 
    by (smt (verit, ccfv_SIG) base_pos mult_less_cancel_left_pos)
  then show "from_digits (Suc n) d < base ^ Suc n" 
    using base_pos
    by (simp add: right_diff_distrib)
qed auto

(*
text \<open>Lemmas for \<open>mod\<close> and \<open>div\<close> in number systems of basis \<open>base\<close>:\<close>
lemma mod_base:  assumes "\<And>i. i<n \<Longrightarrow> \<bar>d i\<bar> < base" "n>0"
  shows "from_digits n d mod base = d 0 " oops
proof -
  have mod_fac: "(\<Sum>i<n. d i * base ^ i) mod base = 
          (\<Sum>i<n. d i * base ^ i mod base) mod base"  
  by (subst mod_sum_eq[symmetric]) simp
  have sum_mod: "(\<Sum>i<n. d i * base ^ i mod base) =
    d 0 * base ^ 0 mod base + (\<Sum>i<n - 1. d (Suc i) * base ^ Suc i mod base)"
    using sum.lessThan_Suc_shift[of "(\<lambda>i. d i * base ^ i mod base)" "n-1"] assms
    by simp
  show ?thesis using assms(1)[OF assms(2)] 
    unfolding from_digits_altdef mod_fac apply (subst sum_mod) apply simp
using mod_less[of ]
    apply (subst mod_less)
    sledgehammer
qed

find_theorems "_ < _" "_ mod _ = (_::int)"

lemma mod_base_i:  
  assumes "\<And>i. i<n \<Longrightarrow> d i < base" "n>0" "i<n"
  shows "(\<Sum>j=i..<n. d j * base ^ (j-i)) mod base = d i " oops
proof -
  have "(\<Sum>j=i..<n. d j * base ^ (j-i)) mod base = 
        (\<Sum>j=i..<n. d j * base ^ (j-i) mod base) mod base"  
    by (subst mod_sum_eq[symmetric]) simp
  then show ?thesis 
    using assms split_sum_first_elt_less[where 
        f = "(\<lambda>j. d j * base ^ (j-i) mod base)"] 
    unfolding from_digits_altdef by simp
qed

lemma div_base_i: 
  assumes "\<And>i. i<n \<Longrightarrow> d i < base" "n>0" "i<n"
  shows "from_digits n d div (base ^i) = (\<Sum>j=i..<n. d j * base ^ (j-i))"
  unfolding from_digits_altdef proof -
  have base_exp: "base^(j) =  base^(j-i) * base^i" 
    if "j\<in>{i..<n}" for j 
    by (metis Nat.add_diff_assoc2 add_diff_cancel_right' atLeastLessThan_iff 
        power_add that)
  have first:"(\<Sum>j<i. d j * base ^ j)< base ^ i" 
    using assms from_digits_less[where n="i"] 
    unfolding from_digits_altdef by auto
  have "(\<Sum>j<n. d j * base ^ j) = 
          (\<Sum>j<i. d j * base ^ j) + (\<Sum>j=i..<n. d j * base ^ j)" 
    using assms split_sum_mid_less[where f="(\<lambda>j. d j * base^j)"] by auto
  then have split_sum: "(\<Sum>j<n. d j * base ^ j) = 
      (\<Sum>j<i. d j * base ^ j) + base^i * (\<Sum>j=i..<n. d j * base ^ (j-i))"
    using base_exp mult.assoc sum_distrib_right 
    by (smt (z3) mult.commute sum.cong)
  then show "(\<Sum>i<n. d i * base ^ i) div base ^ i = 
              (\<Sum>j = i..<n. d j * base ^ (j - i))" 
    using first by (simp add:split_sum base_pos)
qed



text \<open>Conversions are inverse to each other.\<close>
lemma digit_from_digits:
  assumes "\<And>j. j<n \<Longrightarrow> d j < base" "n>0" "i<n"
  shows   "digit (from_digits n d) i = d i"
  using assms proof (cases "i=0")
  case True
  then show ?thesis 
    by (simp add: assms(1) assms(2) digits.mod_base digits_axioms)
next
  case False
  have "from_digits n d div base^i mod base = d i" 
    using assms by (auto simp add: div_base_i mod_base_i) 
  then show "digit (from_digits n d) i = d i" 
    unfolding digit_altdef by auto
qed

lemma div_distrib: assumes "i<n" 
  shows "(a*base^n + b) div base^i mod base = b div base^i mod base"
proof -
  have "base^i dvd (a*base^n)" using assms 
    by (simp add: le_imp_power_dvd)
  moreover have "a*base^n div base^i mod base = 0" 
    by (metis Suc_leI assms dvd_imp_mod_0 dvd_mult 
        dvd_mult_imp_div le_imp_power_dvd power_Suc)
  ultimately show ?thesis
    by (metis add.right_neutral div_mult_mod_eq 
        div_plus_div_distrib_dvd_left mod_mult_self3)
qed

lemma from_digits_digit:
  assumes "x < base ^ n"
  shows   "from_digits n (digit x) = x"
  using assms unfolding digit_altdef from_digits_altdef 
proof (induction n arbitrary: x)
  case 0
  then show ?case by simp
next
  case (Suc n)
  define x_less where "x_less = x mod base^n"
  define x_n where "x_n = x div base^n"
  have "x_less < base^n" 
    using x_less_def base_pos mod_less_divisor by presburger
  then have IH_x_less:
    "(\<Sum>i<n. x_less div base ^ i mod base * base ^ i) = x_less" 
    using Suc.IH by simp
  have "x_n < base" using \<open>x<base^Suc n\<close> 
    by auto (metis less_mult_imp_div_less x_n_def)
  then have "x_n mod base = x_n" by simp
  have x_less_i_eq_x_i:"x mod base^n div base ^i mod base = 
    x div base^i mod base" if "i<n" for i
  proof -
    have "x div base^i mod base = 
          ((x div base^n) * base^n + x mod base^n) div base^i mod base"
      using div_mult_mod_eq[of x "base^n"] by simp
    also have "\<dots> = x mod base^n div base^i mod base" 
      using div_distrib[where a="x div base^n" and b = "x mod base^n"]
        that by auto
    finally show ?thesis by simp
  qed
  have "x = (x_n mod base)*base^n + x_less" 
    unfolding \<open>x_n mod base=x_n\<close> 
    using x_n_def x_less_def div_mod_decomp by blast 
  also have "\<dots> = (x div base^n mod base) * base^n + 
                (\<Sum>i<n. x div base ^ i mod base * base ^ i)"
    using IH_x_less x_less_def x_less_i_eq_x_i x_n_def by auto
  finally show ?case using sum.atMost_Suc 
    by (simp add: add.commute)
qed

text \<open>Stronger formulation of above lemma.\<close>
lemma from_digits_digit': 
  "from_digits n (digit x) = x mod (base ^ n)"
  unfolding from_digits_altdef digit_altdef 
proof (induction n arbitrary: x)
  case 0
  then show ?case by simp
next
  case (Suc n)
  define x_less where "x_less = x mod base^n"
  define x_n where "x_n = x div base^n mod base"
  have "x_less < base^n" using x_less_def base_pos 
      mod_less_divisor by presburger
  then have IH_x_less:
    "(\<Sum>i<n. x_less div base ^ i mod base * base ^ i) = x_less" 
    using Suc.IH by simp
  have "x_n < base" using base_pos mod_less_divisor x_n_def 
    by blast
  then have "x_n mod base = x_n" by simp
  have x_less_i_eq_x_i:"x mod base^n div base ^i mod base = 
    x div base^i mod base" if "i<n" for i
  proof -
    have "x div base^i mod base = 
      ((x div base^n) * base^n + x mod base^n) div base^i mod base"
      using div_mult_mod_eq[of x "base^n"] by simp
    also have "\<dots> = x mod base^n div base^i mod base" 
      using div_distrib[where a="x div base^n" and b = "x mod base^n"] 
        that by auto
    finally show ?thesis by simp
  qed
  have "x mod base^Suc n = x_n*base^n + x_less" 
    by (metis mod_mult2_eq mult.commute power_Suc2 x_less_def x_n_def)
  also have "\<dots> = (x div base^n mod base) * base^n + 
                (\<Sum>i<n. x div base ^ i mod base * base ^ i)"
    using IH_x_less x_less_def x_less_i_eq_x_i x_n_def by auto
  finally show ?case using sum.atMost_Suc 
    by (simp add: add.commute)
qed
*)

end
lemma(in digits) digits_eq_0:
  assumes "x = 0"
  shows "digit x i = 0"
by (simp add: assms digit_altdef)

find_theorems name: sign

end