import ProximityPrize.SubmissionLower.BCHKSFrobeniusBivariatePencil6400
import ProximityPrize.SubmissionLower.BCHKSFrobeniusMixedStack6400

/-!
# The score-64 locator Hankel pencil

An error locator has `76781` coefficient coordinates.  The score-64 syndrome
window supplies `54292` ordinary equations, and the first Frobenius conjugate
supplies another copy.  Selecting all ordinary rows and `22489` conjugate rows
gives a square minor.  This file isolates the determinant argument: many
kernel specializations on `(z,z^p)` force the corresponding two-parameter
minor to vanish identically.

The Hankel realization and the classification of the identically singular
case are intentionally separate downstream tasks.
-/

namespace ProximityPrize.SubmissionLower

open Polynomial

variable {K : Type} [Field K]

/-- Root counting on the Frobenius diagonal, followed by Kronecker
separation.  This is the square-matrix form needed by a selected locator
Hankel minor. -/
theorem twoBlockBivariate_det_eq_zero_of_many_frobenius_kernels
    {I J : Type} [Fintype I] [Fintype J] [DecidableEq (I ⊕ J)]
    (T : Finset K) (p : ℕ)
    (base slope : Matrix (I ⊕ J) (I ⊕ J) K)
    (hp : 0 < p) (hIp : Fintype.card I < p)
    (hcard : Fintype.card I + p * Fintype.card J < T.card)
    (hkernels : ∀ z ∈ T,
      LinearMap.ker
        (twoBlockSpecialization base slope z (z ^ p)).mulVecLin ≠ ⊥) :
    (twoBlockBivariatePencil base slope).det = 0 := by
  apply frobeniusDiagonalSubstitution_injective_of_natDegree_lt hp
  · exact (natDegree_det_twoBlockBivariatePencil_le base slope).trans_lt hIp
  · apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      (frobeniusDiagonalSubstitution p
        (twoBlockBivariatePencil base slope).det) T
    · intro z hz
      rw [eval_frobeniusDiagonalSubstitution,
        ← Polynomial.coe_evalEvalRingHom,
        evalEval_det_twoBlockBivariatePencil]
      have hminor := all_maximal_minors_zero_of_matrix_ker_ne_bot
        (twoBlockSpecialization base slope z (z ^ p))
        (hkernels z hz) id
      simpa using hminor
    · rw [frobeniusDiagonalSubstitution_det_twoBlockBivariatePencil]
      exact (natDegree_det_twoBlockFrobeniusPencil_le p base slope).trans_lt
        hcard

/-- Transpose-kernel variant.  A concrete locator is naturally a kernel
vector for the equation-by-coefficient stack, whereas
`twoBlockSpecialization` is its transpose so that the two parameters occupy
column blocks. -/
theorem twoBlockBivariate_det_eq_zero_of_many_frobenius_transpose_kernels
    {I J : Type} [Fintype I] [Fintype J] [DecidableEq (I ⊕ J)]
    (T : Finset K) (p : ℕ)
    (base slope : Matrix (I ⊕ J) (I ⊕ J) K)
    (hp : 0 < p) (hIp : Fintype.card I < p)
    (hcard : Fintype.card I + p * Fintype.card J < T.card)
    (hkernels : ∀ z ∈ T,
      LinearMap.ker
        (twoBlockSpecialization base slope z (z ^ p)).transpose.mulVecLin ≠
          ⊥) :
    (twoBlockBivariatePencil base slope).det = 0 := by
  apply twoBlockBivariate_det_eq_zero_of_many_frobenius_kernels
    T p base slope hp hIp hcard
  intro z hz
  exact matrix_ker_ne_bot_of_transpose_ker_ne_bot_of_card_eq
    (twoBlockSpecialization base slope z (z ^ p)) rfl (hkernels z hz)

/-- Number of ordinary locator-syndrome equations at score 64. -/
abbrev locatorOrdinaryRows6400 : ℕ := 54292

/-- Extra conjugate rows needed to make the selected locator minor square. -/
abbrev locatorFrobeniusRows6400 : ℕ := 22489

/-- Number of coefficients of a degree-at-most-`76780` error locator. -/
abbrev locatorColumns6400 : ℕ := 76780 + 1

theorem locator_rows_sum_6400 :
    locatorOrdinaryRows6400 + locatorFrobeniusRows6400 =
      locatorColumns6400 := by
  norm_num [locatorOrdinaryRows6400, locatorFrobeniusRows6400,
    locatorColumns6400]

/-- Exact univariate degree of the selected diagonal minor's coarse bound. -/
abbrev locatorDiagonalDegree6400 : ℕ :=
  locatorOrdinaryRows6400 + 2130706433 * locatorFrobeniusRows6400

theorem locatorDiagonalDegree_eq_6400 :
    locatorDiagonalDegree6400 = 47917457026029 := by
  norm_num [locatorDiagonalDegree6400, locatorOrdinaryRows6400,
    locatorFrobeniusRows6400]

/-- The diagonal determinant has enormous room below the score-64 numerator. -/
theorem locatorDiagonalDegree_lt_score6400_numerator :
    locatorDiagonalDegree6400 < 274972148031419760 := by
  norm_num [locatorDiagonalDegree6400, locatorOrdinaryRows6400,
    locatorFrobeniusRows6400]

/-- Concrete determinant-degree specialization, independent of the entries
of the selected square Hankel minor. -/
theorem score6400_selected_locator_minor_natDegree_le
    (base slope : Matrix
      (Fin locatorOrdinaryRows6400 ⊕ Fin locatorFrobeniusRows6400)
      (Fin locatorOrdinaryRows6400 ⊕ Fin locatorFrobeniusRows6400) K) :
    (twoBlockFrobeniusPencil 2130706433 base slope).det.natDegree ≤
      locatorDiagonalDegree6400 := by
  simpa only [Fintype.card_sum, Fintype.card_fin,
    locatorDiagonalDegree6400] using
      natDegree_det_twoBlockFrobeniusPencil_le 2130706433 base slope

end ProximityPrize.SubmissionLower
