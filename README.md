# Formalization-of-NP-hardness-Proofs-for-Lattice-Problems
Formalization of NP-hardness proofs of the shortest vector problem and the closest vector problem.

This repository contains the following formalizations:

**Formalization of basics:**

- Additional_Lemmas.thy
- Digits_int.thy: Number system of variable basis and lemmas thereof
- Lattice_int.thy: Formalization of lattices, lemmas from linear algebra applied to lattices
- infnorm.thy: representation of infnorm as maximum

**Formalizations of new concept:**

- Partition.thy: Formalization of statement of the Partition Problem
- Subset_Sum.thy: Formalization of statement of Subset Sum
- CVP_vec.thy: Formalization of statement of CVP and reduction proof SubsetSum => CVP in maximum norm
- CVP_p.thy: Formalization of statement of CVP and reduction Subset Sum => CVP in p-norm for p>=1 and p finite
- BHLE.thy: Formalization of statement of BHLE Problem and reduction proof Partition => BHLE in maximum norm
- SVP_vec.thy: Formalization of statement of SVP and reduction proof BHLE => SVP in maximum norm

To run these files, you need a running version of Isabelle (https://isabelle.in.tum.de/ Version 2021 or newer).
Clone the directory and open the theory files (*.thy) with Isabelle.
