import ProximityPrize.SubmissionLower.ContactIdentityResidualPrimeTransport
import ProximityPrize.SubmissionLower.ContactResidualSparseComponentAdapter

namespace ProximityPrize.SubmissionLower.ContactIdentityResidualZeroBudgetTransport

open scoped Classical
open ContactFlagBezout
open ContactFlagAffineResidualAutomorphism
open ContactIdentityResidualPrimeTransport
open ContactResidualSparseComponentAdapter

noncomputable section

set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

variable {K : Type} [Field K]

abbrev Poly3 (K : Type) [Field K] := MvPolynomial (Fin 3) K

@[simp] theorem residual_original_apply
    (aY v bY aS bS cS : K) (hv : v ≠ 0) (A : Poly3 K) :
    residualAlgHom aY v bY aS bS cS
        (originalAlgHom aY v bY aS bS cS A) = A := by
  have h := AlgHom.congr_fun
    (residual_comp_original aY v bY aS bS cS hv) A
  simpa only [AlgHom.comp_apply, AlgHom.id_apply] using h

theorem forwardResidualPoint_injective
    (aY v bY aS bS cS : K) (hv : v ≠ 0) :
    Function.Injective (forwardResidualPoint aY v bY aS bS cS) := by
  intro q r hqr
  have h0 := congrFun hqr 0
  have h1 := congrFun hqr 1
  have h2 := congrFun hqr 2
  simp only [forwardResidualPoint, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two] at h0 h1 h2
  change q 2 = r 2 at h2
  have hy : q 0 = r 0 := by
    apply (mul_left_cancel₀ hv)
    rw [h2] at h0
    linear_combination h0
  have hs : q 1 = r 1 := by
    apply (mul_left_cancel₀ hv)
    rw [hy, h2] at h1
    linear_combination h1
  funext i
  fin_cases i
  · exact hy
  · exact hs
  · exact h2

structure PrimeFlagZeroBudget
    (P : Ideal (Poly3 K)) (cost : FlagDegree → ℕ) where
  zero_le : ∀ (r : FlagDegree) (A : Poly3 K),
    PolynomialInFlag r A → A ∉ P → FiniteZeroSetBound P A (cost r)

end

end ProximityPrize.SubmissionLower.ContactIdentityResidualZeroBudgetTransport
