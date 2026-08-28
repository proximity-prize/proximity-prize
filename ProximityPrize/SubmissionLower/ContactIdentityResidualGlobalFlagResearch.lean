import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalTransformResearch
import ProximityPrize.SubmissionLower.ContactPost6464ShearSupportResearch
import ProximityPrize.SubmissionLower.ContactFlagBezout6543Research

/-!
# Global flag support under actual-identity residualization

The component-field affine automorphism preserves the three-variable flag,
but agreement numerators are constructed before mapping `X` into the
coefficient field.  This module closes that separate global obligation.

All polynomials in `X` have weight zero for the three flag functionals.  The
global nodal substitution is therefore support-nonincreasing for those
functionals, including the `X` derivatives appearing in the contact
recurrence.  Combining this with the exact Minkowski recurrence gives the
residual-degree agreement flag

`Flag(1098*d, 1 + 54*d, 11*d)`

for the score-66.00 surface flag `Flag(549,27,6)`.
-/

namespace ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlagResearch

open scoped Classical BigOperators
open ContactIdentityResidualGlobalTransformResearch
open ContactPost6464MinkowskiRecurrenceResearch
open ContactPost6464ShearSupportResearch
open ContactFlagBezout6543Research
open ContactGenericSurface ContactTaylorNumerators

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

variable {K Omega : Type} [Field K] [Field Omega]

abbrev Poly4 (K : Type) [Field K] := MvPolynomial (Fin 4) K

/-- Pull a weight through the global affine-triangular residual
substitution.  This formula is valid when the `X` weight is zero. -/
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

/-- Global support-functional transport.  Unlike the component-field
automorphism theorem, this statement sees all `X` derivatives used by the
agreement recurrence. -/
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

/-- The three support values of a score-66.00 surface survive the global
nodal transform without any charge depending on the identity count. -/
theorem globalResidualHom_surface_flag_weights
    (P0 P1 V : Polynomial K) (F : Poly4 K)
    (hS : wt residualSWeights F ≤ 6)
    (hYS : wt residualYSWeights F ≤ 33)
    (hTotal : wt residualTotalWeights F ≤ 582) :
    wt residualSWeights (globalResidualHom P0 P1 V F) ≤ 6 ∧
      wt residualYSWeights (globalResidualHom P0 P1 V F) ≤ 33 ∧
      wt residualTotalWeights (globalResidualHom P0 P1 V F) ≤ 582 := by
  refine ⟨?_, ?_, ?_⟩
  · exact (globalResidualHom_wt_le_pulled residualSWeights rfl
      P0 P1 V F).trans (by simpa [residualPullWeights_s] using hS)
  · exact (globalResidualHom_wt_le_pulled residualYSWeights rfl
      P0 P1 V F).trans (by simpa [residualPullWeights_ys] using hYS)
  · exact (globalResidualHom_wt_le_pulled residualTotalWeights rfl
      P0 P1 V F).trans (by simpa [residualPullWeights_total] using hTotal)

/-- Agreement weight bounds at residual degree `d`.  The pure derivative
coordinate uses the exact coordinate-degree recurrence; the other two
facets use the Minkowski recurrence. -/
theorem globalResidual_agreement_weight_bounds
    (P0 P1 V : Polynomial K) (F : Poly4 K)
    (hS : wt residualSWeights F ≤ 6)
    (hYS : wt residualYSWeights F ≤ 33)
    (hTotal : wt residualTotalWeights F ≤ 582)
    (d : ℕ) (coeffs : ℕ → K) (x u0 u1 : K) :
    (agreementNumerator (globalResidualHom P0 P1 V F)
        d coeffs x u0 u1).degreeOf (2 : Fin 4) ≤ 11 * d ∧
      wt residualYSWeights
        (agreementNumerator (globalResidualHom P0 P1 V F)
          d coeffs x u0 u1) ≤ 1 + 65 * d ∧
      wt residualTotalWeights
        (agreementNumerator (globalResidualHom P0 P1 V F)
          d coeffs x u0 u1) ≤ 1 + 1163 * d := by
  let Fres := globalResidualHom P0 P1 V F
  obtain ⟨hFs, hFys, hFtot⟩ :=
    globalResidualHom_surface_flag_weights P0 P1 V F hS hYS hTotal
  have hR : Fres.degreeOf (2 : Fin 4) ≤ 6 := by
    have hw : residualSWeights = Pi.single (2 : Fin 4) 1 := by
      funext i
      fin_cases i <;> rfl
    rw [hw, wt, MvPolynomial.weightedTotalDegree_piSingle] at hFs
    exact hFs
  have hY : Fres.degreeOf (1 : Fin 4) ≤ 33 := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    have hw := (MvPolynomial.le_weightedTotalDegree residualYSWeights he).trans hFys
    rw [ContactFactorCaps.weight_fin4] at hw
    change e 0 * 0 + e 1 * 1 + e 2 * 1 + e 3 * 0 ≤ 33 at hw
    norm_num at hw
    omega
  have hZ : Fres.degreeOf (3 : Fin 4) ≤ 582 := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    have hw := (MvPolynomial.le_weightedTotalDegree residualTotalWeights he).trans hFtot
    rw [ContactFactorCaps.weight_fin4] at hw
    change e 0 * 0 + e 1 * 1 + e 2 * 1 + e 3 * 1 ≤ 582 at hw
    norm_num at hw
    omega
  refine ⟨?_, ?_, ?_⟩
  · have hr := (agreementNumerator_degree_bounds Fres 33 6 582
      (by norm_num) hY hR hZ d coeffs x u0 u1).2.1
    convert hr using 1 <;> ring
  · have h := agreementNumerator_wt_le_minkowski residualYSWeights rfl
      Fres 33 (by change 1 ≤ 33; norm_num)
      (by change 2 * 1 ≤ 33; norm_num)
      (by change 1 ≤ 1; norm_num) hFys d coeffs x u0 u1
    calc
      wt residualYSWeights (agreementNumerator Fres d coeffs x u0 u1) ≤
          max (residualYSWeights 1) (residualYSWeights 3) +
            d * (33 + (33 - residualYSWeights 2)) := h
      _ = 1 + 65 * d := by
        change max 1 0 + d * (33 + (33 - 1)) = 1 + 65 * d
        norm_num
        ring
  · have h := agreementNumerator_wt_le_minkowski residualTotalWeights rfl
      Fres 582 (by change 1 ≤ 582; norm_num)
      (by change 2 * 1 ≤ 582; norm_num)
      (by change 1 ≤ 1; norm_num) hFtot d coeffs x u0 u1
    calc
      wt residualTotalWeights (agreementNumerator Fres d coeffs x u0 u1) ≤
          max (residualTotalWeights 1) (residualTotalWeights 3) +
            d * (582 + (582 - residualTotalWeights 2)) := h
      _ = 1 + 1163 * d := by
        change max 1 1 + d * (582 + (582 - 1)) = 1 + 1163 * d
        norm_num
        ring

def residualAgreementFlag (d : ℕ) : FlagDegree :=
  ⟨1098 * d, 1 + 54 * d, 11 * d⟩

/-- The mapped agreement cut lies in the exact affine flag family used by
the stratified mixed-volume expansion. -/
theorem surfaceMap_globalResidual_agreement_in_flag
    (phi : Polynomial K →+* Omega)
    (P0 P1 V : Polynomial K) (F : Poly4 K)
    (hS : wt residualSWeights F ≤ 6)
    (hYS : wt residualYSWeights F ≤ 33)
    (hTotal : wt residualTotalWeights F ≤ 582)
    (d : ℕ) (coeffs : ℕ → K) (x u0 u1 : K) :
    PolynomialInFlag (residualAgreementFlag d)
      (surfaceMap phi
        (agreementNumerator (globalResidualHom P0 P1 V F)
          d coeffs x u0 u1)) := by
  intro e he
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp
    (support_surfaceMap_subset phi
      (agreementNumerator (globalResidualHom P0 P1 V F)
        d coeffs x u0 u1) he)
  obtain ⟨hR, hYS', hTot⟩ := globalResidual_agreement_weight_bounds
    P0 P1 V F hS hYS hTotal d coeffs x u0 u1
  have hqR := (MvPolynomial.monomial_le_degreeOf (2 : Fin 4) hq).trans hR
  have hqYS := (MvPolynomial.le_weightedTotalDegree residualYSWeights hq).trans hYS'
  have hqTot := (MvPolynomial.le_weightedTotalDegree residualTotalWeights hq).trans hTot
  rw [ContactFactorCaps.weight_fin4] at hqYS hqTot
  change q 0 * 0 + q 1 * 1 + q 2 * 1 + q 3 * 0 ≤ 1 + 65 * d at hqYS
  change q 0 * 0 + q 1 * 1 + q 2 * 1 + q 3 * 1 ≤ 1 + 1163 * d at hqTot
  norm_num at hqYS hqTot
  change q 2 ≤ 11 * d ∧
    q 1 + q 2 ≤ (1 + 54 * d) + 11 * d ∧
    q 1 + q 2 + q 3 ≤ 1098 * d + (1 + 54 * d) + 11 * d
  omega

end

end ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlagResearch

#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlagResearch.globalResidualHom_wt_le_pulled
#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlagResearch.globalResidual_agreement_weight_bounds
#print axioms ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlagResearch.surfaceMap_globalResidual_agreement_in_flag
