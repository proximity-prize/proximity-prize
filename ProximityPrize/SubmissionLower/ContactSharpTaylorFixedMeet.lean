import ProximityPrize.SubmissionLower.ContactJointTaylorMiddleCap
import ProximityPrize.SubmissionLower.ContactIdentityResidualIteration
import ProximityPrize.SubmissionLower.ContactGlobalSelectedFamilies
import ProximityPrize.SubmissionLower.ContactSingularBranchParameterized
namespace ProximityPrize.SubmissionLower.ContactSharpTaylorFixedMeet

open scoped Classical BigOperators
open ContactFactorCaps ContactTaylorNumerators ContactGenericSurface
open ContactPost6464MinkowskiRecurrence
open ContactJointTaylorMiddleCap
open ContactFlagBezout
open ContactResidualSupportParameters
open ContactResidualSupportParameters.ResidualSupportParameters
open ContactIdentityResidualGlobalFlag
open ContactInterpolation ContactPrimeSeedIncidence
open ContactRegularFactorFlag
open ContactIdentityResidualIteration
open ContactRobustFixedMeet
open ContactTightSingularLedger
open ContactGlobalSelectedFamilies

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 35000

def sharpAgreementDirection (P : ResidualSupportParameters) : FlagDegree :=
  ⟨2 * (P.total - P.ys), 2 * (P.ys - P.s) - 1, 2 * P.s - 1⟩

def sharpResidualAgreementFlag
    (P : ResidualSupportParameters) (d : ℕ) : FlagDegree :=
  ⟨(sharpAgreementDirection P).zOnly * d,
    1 + (sharpAgreementDirection P).yz * d,
    (sharpAgreementDirection P).all * d⟩

theorem sharpResidualAgreementFlag_ys
    (P : ResidualSupportParameters) (hsy : P.s < P.ys) (d : ℕ) :
    (sharpResidualAgreementFlag P d).yz +
        (sharpResidualAgreementFlag P d).all =
      1 + d * (2 * P.ys - 2) := by
  have hcoeff :
      (2 * (P.ys - P.s) - 1) + (2 * P.s - 1) = 2 * P.ys - 2 := by
    have hleft : 1 ≤ 2 * (P.ys - P.s) := by
      have : 1 ≤ P.ys - P.s := Nat.sub_pos_of_lt hsy
      omega
    have hright : 1 ≤ 2 * P.s := by
      have : 1 ≤ P.s := P.one_le_s
      omega
    rw [tsub_add_tsub_comm hleft hright]
    have hsum : 2 * (P.ys - P.s) + 2 * P.s = 2 * P.ys := by
      calc
        2 * (P.ys - P.s) + 2 * P.s = 2 * ((P.ys - P.s) + P.s) := by ring
        _ = 2 * P.ys := by rw [Nat.sub_add_cancel (Nat.le_of_lt hsy)]
    rw [hsum]
  simp only [sharpResidualAgreementFlag, sharpAgreementDirection]
  rw [← hcoeff]
  ring

theorem sharpResidualAgreementFlag_total
    (P : ResidualSupportParameters) (hsy : P.s < P.ys) (d : ℕ) :
    (sharpResidualAgreementFlag P d).zOnly +
        (sharpResidualAgreementFlag P d).yz +
        (sharpResidualAgreementFlag P d).all =
      1 + d * (2 * P.total - 2) := by
  have hcoeff :
      2 * (P.total - P.ys) + (2 * (P.ys - P.s) - 1) +
          (2 * P.s - 1) = 2 * P.total - 2 := by
    have hmiddle :
        (2 * (P.ys - P.s) - 1) + (2 * P.s - 1) =
          2 * P.ys - 2 := by
      have hleft : 1 ≤ 2 * (P.ys - P.s) := by
        have : 1 ≤ P.ys - P.s := Nat.sub_pos_of_lt hsy
        omega
      have hright : 1 ≤ 2 * P.s := by
        have : 1 ≤ P.s := P.one_le_s
        omega
      rw [tsub_add_tsub_comm hleft hright]
      have hsum : 2 * (P.ys - P.s) + 2 * P.s = 2 * P.ys := by
        calc
          2 * (P.ys - P.s) + 2 * P.s =
              2 * ((P.ys - P.s) + P.s) := by ring
          _ = 2 * P.ys := by rw [Nat.sub_add_cancel (Nat.le_of_lt hsy)]
      rw [hsum]
    rw [Nat.add_assoc, hmiddle]
    have htwo : 2 ≤ 2 * P.ys := by
      have : 1 ≤ P.ys := P.one_le_s.trans P.s_le_ys
      omega
    rw [← Nat.add_sub_assoc htwo]
    have hsum : 2 * (P.total - P.ys) + 2 * P.ys = 2 * P.total := by
      calc
        2 * (P.total - P.ys) + 2 * P.ys =
            2 * ((P.total - P.ys) + P.ys) := by ring
        _ = 2 * P.total := by rw [Nat.sub_add_cancel P.ys_le_total]
    rw [hsum]
  simp only [sharpResidualAgreementFlag, sharpAgreementDirection]
  rw [← hcoeff]
  ring

variable {K Omega : Type} [Field K] [Field Omega]

theorem sharp_agreement_weight_bounds
    {P : ResidualSupportParameters} {F : MvPolynomial (Fin 4) K}
    (H : ResidualSupportData P F)
    (d : ℕ) (coeffs : ℕ → K) (x u0 u1 : K) :
    (agreementNumerator F d coeffs x u0 u1).degreeOf (2 : Fin 4) ≤
        d * (2 * P.s - 1) ∧
      wt residualYSWeights (agreementNumerator F d coeffs x u0 u1) ≤
        1 + d * (2 * P.ys - 2) ∧
      wt residualTotalWeights (agreementNumerator F d coeffs x u0 u1) ≤
        1 + d * (2 * P.total - 2) := by
  obtain ⟨hY, hR, hZ⟩ := H.coordinate_bounds
  refine ⟨(agreementNumerator_degree_bounds F P.ys P.s P.total
    P.one_le_s hY hR hZ d coeffs x u0 u1).2.1, ?_, ?_⟩
  · have h := agreementNumerator_wt_le_equal_weight residualYSWeights rfl
      F P.ys (by change 1 ≤ 1; norm_num)
      (by change 1 ≤ P.ys; exact P.one_le_s.trans P.s_le_ys)
      (by change 2 * 1 ≤ P.ys; simpa using P.two_le_ys)
      (by change 1 ≤ 1; norm_num) H.ys_weight d coeffs x u0 u1
    have hcoeff : 2 * (P.ys - 1) = 2 * P.ys - 2 := by omega
    apply h.trans_eq
    change max 1 0 + d * (2 * (P.ys - 1)) =
      1 + d * (2 * P.ys - 2)
    rw [hcoeff]
    norm_num
  · have htotalTwo : 2 ≤ P.total := P.two_le_ys.trans P.ys_le_total
    have honeTotal : 1 ≤ P.total :=
      P.one_le_s.trans (P.s_le_ys.trans P.ys_le_total)
    have h := agreementNumerator_wt_le_equal_weight residualTotalWeights rfl
      F P.total (by change 1 ≤ 1; norm_num)
      (by change 1 ≤ P.total; exact honeTotal)
      (by change 2 * 1 ≤ P.total; simpa using htotalTwo)
      (by change 1 ≤ 1; norm_num) H.total_weight d coeffs x u0 u1
    have hcoeff : 2 * (P.total - 1) = 2 * P.total - 2 := by omega
    apply h.trans_eq
    change max 1 1 + d * (2 * (P.total - 1)) =
      1 + d * (2 * P.total - 2)
    rw [hcoeff]
    norm_num

theorem surfaceMap_agreement_in_sharp_flag
    {P : ResidualSupportParameters} (hsy : P.s < P.ys)
    (phi : Polynomial K →+* Omega) {F : MvPolynomial (Fin 4) K}
    (H : ResidualSupportData P F)
    (d : ℕ) (coeffs : ℕ → K) (x u0 u1 : K) :
    PolynomialInFlag (sharpResidualAgreementFlag P d)
      (surfaceMap phi (agreementNumerator F d coeffs x u0 u1)) := by
  intro e he
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp
    (support_surfaceMap_subset phi (agreementNumerator F d coeffs x u0 u1) he)
  obtain ⟨hR, hYS, hTotal⟩ := sharp_agreement_weight_bounds H
    d coeffs x u0 u1
  have hqR := (MvPolynomial.monomial_le_degreeOf (2 : Fin 4) hq).trans hR
  have hqYS :=
    (MvPolynomial.le_weightedTotalDegree residualYSWeights hq).trans hYS
  have hqTotal :=
    (MvPolynomial.le_weightedTotalDegree residualTotalWeights hq).trans hTotal
  rw [ContactFactorCaps.weight_fin4] at hqYS hqTotal
  change q 0 * 0 + q 1 * 1 + q 2 * 1 + q 3 * 0 ≤
    1 + d * (2 * P.ys - 2) at hqYS
  change q 0 * 0 + q 1 * 1 + q 2 * 1 + q 3 * 1 ≤
    1 + d * (2 * P.total - 2) at hqTotal
  norm_num at hqYS hqTotal
  have hqR' : q 2 ≤ (sharpResidualAgreementFlag P d).all := by
    change q 2 ≤ (2 * P.s - 1) * d
    rw [Nat.mul_comm]
    exact hqR
  change q 2 ≤ (sharpResidualAgreementFlag P d).all ∧
    q 1 + q 2 ≤ (sharpResidualAgreementFlag P d).yz +
      (sharpResidualAgreementFlag P d).all ∧
    q 1 + q 2 + q 3 ≤ (sharpResidualAgreementFlag P d).zOnly +
      (sharpResidualAgreementFlag P d).yz +
      (sharpResidualAgreementFlag P d).all
  refine ⟨hqR', ?_, ?_⟩
  · rw [sharpResidualAgreementFlag_ys P hsy]
    exact hqYS
  · rw [sharpResidualAgreementFlag_total P hsy]
    exact hqTotal

variable {K Omega Iota : Type} [Field K] [Field Omega]
variable {phi : Polynomial K →+* Omega} {Gamma : Finset K} {x : Iota → K}
variable {pchar : ℕ} [CharP Omega pchar]

end

end ProximityPrize.SubmissionLower.ContactSharpTaylorFixedMeet
