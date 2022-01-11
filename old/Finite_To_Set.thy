theory Finite_To_Set

imports Main
        "HOL-Analysis.Finite_Cartesian_Product"

begin

locale fixed_dim = 
fixes n::nat
assumes n_def: "n = CARD ('n::finite)"
begin
(*
lemma exist_bij_finite: "\<exists>f::('n \<Rightarrow> nat). bij_betw f UNIV {0..<n}"
using ex_bij_betw_finite_nat finite_class.finite_UNIV n_def by blast
*)
lemma obtains f::"('n \<Rightarrow> nat)" where "bij_betw f UNIV {0..<n}"
by (metis ex_bij_betw_finite_nat finite n_def)



end


end