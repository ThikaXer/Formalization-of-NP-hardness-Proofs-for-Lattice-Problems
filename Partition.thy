theory Partition

imports Main
        "Jordan_Normal_Form.Matrix"
        "poly-reductions/Karp21/Reductions"

begin
text \<open>The Partition Problem.\<close>

definition partition_problem :: "(int vec) set " where
  "partition_problem = {a. \<exists>I. I \<subseteq> {0..<dim_vec a} \<and> 
    (\<Sum>i\<in>I. a $ i) = (\<Sum>i\<in>({0..<dim_vec a}-I). a $ i)}"

text \<open>Reduction partition problem to Knapsack.\<close>


end