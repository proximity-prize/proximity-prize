import ProximityPrize.SubmissionLower.BCHKSFrobeniusArithmetic6400

/-!
# Degree descent from a full-source multiplier relation

This file isolates the root-counting step in the sparse two-Frobenius route.
If two products have degree below the number of source agreements and their
sum vanishes on every agreement, then the products are negatives as
polynomials.  Equality of product degrees cancels the common cofactor degree,
forcing both multipliers to have the same degree.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

variable {F : Type} [Field F]

/-- A pointwise relation on sufficiently many distinct source points descends
to equality of multiplier degrees.  The cofactors may be different, provided
that they are nonzero and have the same degree. -/
theorem multiplier_degree_eq_of_many_root_relation
    (A B C Cp : F[X]) (S : Finset F)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hCp : Cp ≠ 0)
    (hcofactorDegree : Cp.natDegree = C.natDegree)
    (hAC : A.natDegree + C.natDegree < S.card)
    (hBCp : B.natDegree + Cp.natDegree < S.card)
    (hroot : ∀ x ∈ S, (A * C + B * Cp).eval x = 0) :
    A.natDegree = B.natDegree := by
  have hAC' : (A * C).natDegree < S.card := by
    rw [Polynomial.natDegree_mul hA hC]
    exact hAC
  have hBCp' : (B * Cp).natDegree < S.card := by
    rw [Polynomial.natDegree_mul hB hCp]
    exact hBCp
  have hsumDegree : (A * C + B * Cp).natDegree < S.card :=
    (Polynomial.natDegree_add_le (A * C) (B * Cp)).trans_lt
      (max_lt hAC' hBCp')
  have hzero : A * C + B * Cp = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      (A * C + B * Cp) S hroot hsumDegree
  have heq : A * C = -(B * Cp) := eq_neg_of_add_eq_zero_left hzero
  have hdegree := congrArg Polynomial.natDegree heq
  rw [Polynomial.natDegree_mul hA hC,
    Polynomial.natDegree_neg,
    Polynomial.natDegree_mul hB hCp,
    hcofactorDegree] at hdegree
  omega

/-- In the sparse source regime, a full-block relation with a cofactor small
enough for root counting forces the first multiplier into the shorter
`h`-row block as well. -/
theorem multiplier_degree_descent
    (A B C Cp : F[X]) (S : Finset F) (c h : ℕ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hCp : Cp ≠ 0)
    (hcofactorDegree : Cp.natDegree = C.natDegree)
    (hAdegree : A.natDegree < c)
    (hBdegree : B.natDegree < h)
    (hhc : h ≤ c)
    (hcofactorRoom : C.natDegree + c < S.card)
    (hroot : ∀ x ∈ S, (A * C + B * Cp).eval x = 0) :
    A.natDegree = B.natDegree ∧ A.natDegree < h := by
  have hAC : A.natDegree + C.natDegree < S.card := by
    omega
  have hBCp : B.natDegree + Cp.natDegree < S.card := by
    rw [hcofactorDegree]
    omega
  have heq := multiplier_degree_eq_of_many_root_relation
    A B C Cp S hA hB hC hCp hcofactorDegree hAC hBCp hroot
  exact ⟨heq, heq.trans_lt hBdegree⟩

end ProximityPrize.SubmissionLower
