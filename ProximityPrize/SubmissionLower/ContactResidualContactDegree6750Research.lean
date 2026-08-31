import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactFactorCaps
import ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlagResearch

 









namespace ProximityPrize.SubmissionLower
namespace ContactResidualContactDegree6750Research

open scoped Classical BigOperators
open ContactFactorCaps
open ContactIdentityResidualGlobalFlagResearch

noncomputable section

set_option autoImplicit false

universe u

variable {K : Type u} [Field K]

 

theorem residualYS_mul_sub_residualS_le_contact
    (w : Nat) (hw : 0 < w) (H : MvPolynomial (Fin 4) K) (hH : H ≠ 0) :
    w * MvPolynomial.weightedTotalDegree residualYSWeights H -
        MvPolynomial.weightedTotalDegree residualSWeights H ≤
      MvPolynomial.weightedTotalDegree (contactWeights w) H := by
  let y := MvPolynomial.weightedTotalDegree residualYSWeights H
  let r := MvPolynomial.weightedTotalDegree residualSWeights H
  let c := MvPolynomial.weightedTotalDegree (contactWeights w) H
  obtain ⟨d, hd, hdys⟩ := H.support.exists_mem_eq_sup
    (MvPolynomial.support_nonempty.mpr hH)
    (Finsupp.weight residualYSWeights)
  have hdys' : Finsupp.weight residualYSWeights d = y := by
    change Finsupp.weight residualYSWeights d =
      H.support.sup (Finsupp.weight residualYSWeights)
    exact hdys.symm
  have hds : Finsupp.weight residualSWeights d ≤ r := by
    exact MvPolynomial.le_weightedTotalDegree residualSWeights hd
  have hdc : Finsupp.weight (contactWeights w) d ≤ c := by
    exact MvPolynomial.le_weightedTotalDegree (contactWeights w) hd
  have hw1 : 1 ≤ w := by omega
  have hsplit : (w - 1) * d 2 + d 2 = w * d 2 := by
    calc
      (w - 1) * d 2 + d 2 = (w - 1) * d 2 + 1 * d 2 := by rw [one_mul]
      _ = ((w - 1) + 1) * d 2 := (Nat.add_mul _ _ _).symm
      _ = w * d 2 := by rw [Nat.sub_add_cancel hw1]
  have hdysWeight :
      Finsupp.weight residualYSWeights d = d 1 + d 2 := by
    rw [weight_fin4]
    simp [residualYSWeights]
  have hdsWeight : Finsupp.weight residualSWeights d = d 2 := by
    rw [weight_fin4]
    simp [residualSWeights]
  have hpoint :
      w * Finsupp.weight residualYSWeights d ≤
        Finsupp.weight (contactWeights w) d +
          Finsupp.weight residualSWeights d := by
    rw [hdysWeight, hdsWeight, contact_weight]
    calc
      w * (d 1 + d 2) = w * d 1 + w * d 2 := Nat.mul_add _ _ _
      _ = w * d 1 + ((w - 1) * d 2 + d 2) := by rw [hsplit]
      _ ≤ (d 0 + w * d 1 + (w - 1) * d 2) + d 2 := by omega
  have hsum : w * y ≤ c + r := by
    rw [← hdys']
    exact hpoint.trans (Nat.add_le_add hdc hds)
  change w * y - r ≤ c
  omega

end

end ContactResidualContactDegree6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactResidualContactDegree6750Research.residualYS_mul_sub_residualS_le_contact
