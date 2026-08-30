import ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalTransform
import ProximityPrize.SubmissionLower.ContactFlagBezout
import ProximityPrize.SubmissionLower.ContactPost6464MinkowskiRecurrence

namespace ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlag

open scoped Classical BigOperators
open ContactIdentityResidualGlobalTransform
open ContactPost6464MinkowskiRecurrence
open ContactFlagBezout
open ContactGenericSurface ContactTaylorNumerators

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

variable {K Omega : Type} [Field K] [Field Omega]

abbrev Poly4 (K : Type) [Field K] := MvPolynomial (Fin 4) K

def residualPullWeights (weights : Fin 4 → ℕ) : Fin 4 → ℕ :=
  ![weights 0,
    max (weights 1) (weights 3),
    max (weights 2) (max (weights 1) (weights 3)),
    weights 3]

theorem wt_embedX_zero (weights : Fin 4 → ℕ) (hX : weights 0 = 0)
    (P : Polynomial K) :
    wt weights (embedX K P) = 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [map_add]
      apply Nat.eq_zero_of_le_zero
      exact (wt_add_le weights (embedX K P) (embedX K Q)).trans
        (by simpa only [hP, hQ, max_self] using (Nat.le_refl 0))
  | monomial n a =>
      have hembed : embedX K (Polynomial.monomial n a) =
          MvPolynomial.C a * MvPolynomial.X (0 : Fin 4) ^ n := by
        simp [embedX]
      rw [hembed]
      apply Nat.eq_zero_of_le_zero
      have hm := wt_mul_le weights (MvPolynomial.C a : Poly4 K)
        (MvPolynomial.X (0 : Fin 4) ^ n)
      have hp := wt_pow_le weights (MvPolynomial.X (0 : Fin 4) : Poly4 K) n
      rw [wt_C] at hm
      rw [wt_X, hX, Nat.mul_zero] at hp
      omega

theorem globalResidualImage_wt_le
    (weights : Fin 4 → ℕ) (hX : weights 0 = 0)
    (P0 P1 V : Polynomial K) (i : Fin 4) :
    wt weights (globalResidualImage P0 P1 V i) ≤
      residualPullWeights weights i := by
  fin_cases i
  · simp [globalResidualImage, residualPullWeights, wt_X]
  · dsimp [globalResidualImage, residualPullWeights]
    have hP0 := wt_embedX_zero weights hX P0
    have hP1 := wt_embedX_zero weights hX P1
    have hV := wt_embedX_zero weights hX V
    have hz := wt_mul_le weights
      (MvPolynomial.X (3 : Fin 4) : Poly4 K) (embedX K P1)
    have hy := wt_mul_le weights (embedX K V)
      (MvPolynomial.X (1 : Fin 4) : Poly4 K)
    rw [wt_X, hP1, Nat.add_zero] at hz
    rw [hV, wt_X, Nat.zero_add] at hy
    have h01 := wt_add_le weights (embedX K P0)
      (MvPolynomial.X (3 : Fin 4) * embedX K P1)
    have h012 := wt_add_le weights
      (embedX K P0 + MvPolynomial.X (3 : Fin 4) * embedX K P1)
      (embedX K V * MvPolynomial.X (1 : Fin 4))
    omega
  · dsimp [globalResidualImage, residualPullWeights]
    have hP0 := wt_embedX_zero weights hX P0.derivative
    have hP1 := wt_embedX_zero weights hX P1.derivative
    have hV' := wt_embedX_zero weights hX V.derivative
    have hV := wt_embedX_zero weights hX V
    have hz := wt_mul_le weights
      (MvPolynomial.X (3 : Fin 4) : Poly4 K) (embedX K P1.derivative)
    have hy := wt_mul_le weights (embedX K V.derivative)
      (MvPolynomial.X (1 : Fin 4) : Poly4 K)
    have hr := wt_mul_le weights (embedX K V)
      (MvPolynomial.X (2 : Fin 4) : Poly4 K)
    rw [wt_X, hP1, Nat.add_zero] at hz
    rw [hV', wt_X, Nat.zero_add] at hy
    rw [hV, wt_X, Nat.zero_add] at hr
    have h01 := wt_add_le weights (embedX K P0.derivative)
      (MvPolynomial.X (3 : Fin 4) * embedX K P1.derivative)
    have h012 := wt_add_le weights
      (embedX K P0.derivative +
        MvPolynomial.X (3 : Fin 4) * embedX K P1.derivative)
      (embedX K V.derivative * MvPolynomial.X (1 : Fin 4))
    have h0123 := wt_add_le weights
      (embedX K P0.derivative +
        MvPolynomial.X (3 : Fin 4) * embedX K P1.derivative +
        embedX K V.derivative * MvPolynomial.X (1 : Fin 4))
      (embedX K V * MvPolynomial.X (2 : Fin 4))
    omega
  · simp [globalResidualImage, residualPullWeights, wt_X]

theorem globalResidual_monomial_product_wt_le
    (weights : Fin 4 → ℕ) (hX : weights 0 = 0)
    (P0 P1 V : Polynomial K) (d : Fin 4 →₀ ℕ) :
    wt weights
        (∏ i ∈ d.support, globalResidualImage P0 P1 V i ^ d i) ≤
      Finsupp.weight (residualPullWeights weights) d := by
  apply (wt_finset_prod_le_sum weights d.support
    (fun i ↦ globalResidualImage P0 P1 V i ^ d i)).trans
  calc
    (∑ i ∈ d.support,
        wt weights (globalResidualImage P0 P1 V i ^ d i)) ≤
        ∑ i ∈ d.support, d i * residualPullWeights weights i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (wt_pow_le weights (globalResidualImage P0 P1 V i) (d i)).trans
        (Nat.mul_le_mul_left _
          (globalResidualImage_wt_le weights hX P0 P1 V i))
    _ = Finsupp.weight (residualPullWeights weights) d := by
      rw [Finsupp.weight_apply]
      simp only [Finsupp.sum, nsmul_eq_mul]
      simp

theorem globalResidualHom_wt_le_pulled
    (weights : Fin 4 → ℕ) (hX : weights 0 = 0)
    (P0 P1 V : Polynomial K) (F : Poly4 K) :
    wt weights (globalResidualHom P0 P1 V F) ≤
      wt (residualPullWeights weights) F := by
  change wt weights
      (MvPolynomial.eval₂ MvPolynomial.C
        (globalResidualImage P0 P1 V) F) ≤ _
  rw [MvPolynomial.eval₂_eq]
  apply wt_finset_sum_le
  intro d hd
  have hprod := globalResidual_monomial_product_wt_le
    weights hX P0 P1 V d
  have hcoeff : wt weights
      (MvPolynomial.C (F.coeff d) : Poly4 K) = 0 := wt_C weights _
  have hmul := wt_mul_le weights
    (MvPolynomial.C (F.coeff d) : Poly4 K)
    (∏ i ∈ d.support, globalResidualImage P0 P1 V i ^ d i)
  rw [hcoeff, Nat.zero_add] at hmul
  exact hmul.trans (hprod.trans
    (MvPolynomial.le_weightedTotalDegree
      (residualPullWeights weights) hd))

def residualSWeights : Fin 4 → ℕ := ![0, 0, 1, 0]
def residualYSWeights : Fin 4 → ℕ := ![0, 1, 1, 0]
def residualTotalWeights : Fin 4 → ℕ := ![0, 1, 1, 1]

theorem residualPullWeights_s :
    residualPullWeights residualSWeights = residualSWeights := by
  funext i
  fin_cases i <;> rfl

theorem residualPullWeights_ys :
    residualPullWeights residualYSWeights = residualYSWeights := by
  funext i
  fin_cases i <;> rfl

theorem residualPullWeights_total :
    residualPullWeights residualTotalWeights = residualTotalWeights := by
  funext i
  fin_cases i <;> rfl

end

end ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlag
