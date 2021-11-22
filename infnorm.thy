theory infnorm

imports Main
        "Jordan_Normal_Form.Matrix"

begin

text \<open>We need to define the l-infinity norm on vectors.\<close>

definition infnorm ::"'a vec \<Rightarrow> 'a::{linorder, abs}" where
  "infnorm v \<equiv> Max { \<bar>v$i\<bar> | i. i < dim_vec v}"

end