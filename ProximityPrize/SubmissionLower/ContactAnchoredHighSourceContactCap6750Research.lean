import ProximityPrize.SubmissionLower.ContactAnchoredHighSourceHull6750Research
import ProximityPrize.SubmissionLower.ContactAnchoredHighKernelSelectorRealization6750Research

 









namespace ProximityPrize.SubmissionLower
namespace ContactAnchoredHighSourceContactCap6750Research

open scoped Classical BigOperators
open ContactFlagInterpolation6641Research
open ContactAnchoredOneFamilySelector6750Research
open ContactAnchoredHighSourceHull6750Research
open ContactAnchoredHighKernelSelectorRealization6750Research
open ContactNestedFiveCapCoefficientBox6750Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u v x

variable {K : Type u} [Field K]
variable {I : Type v} [Fintype I]

 

theorem nestedFiveCap_fixedSource_mem_globalCoefficientBox
    {T YS S : Nat}
    (G : MvPolynomial (Fin 4) K)
    (hGbox : G ∈ nestedFiveCapCoefficientBox K
      (48 * agreements) 131071 T YS S) :
    G ∈ ContactInterpolation.globalCoefficientBox K
      (48 * agreements) 131071 T S := by
  intro d hd
  have h := hGbox hd
  have htotal := h.1
  exact ⟨by omega, h.2.2.1, h.2.2.2⟩

 

theorem highSourceCore_contact_le_47agreements_sub_one
    (nodes u0 u1 : I → K)
    (g : CoefficientIndex 11458062 131071 familyMaxTotal 18 → K)
    {beta : Type x} [Fintype beta]
    (b : Module.Basis beta K (highSourceHull nodes u0 u1 g))
    {T YS S : Nat}
    (hfixed : reconstruct K 11458062 131071 familyMaxTotal 18 g ≠ 0)
    (hfixedBox : reconstruct K 11458062 131071 familyMaxTotal 18 g ∈
      nestedFiveCapCoefficientBox K
        (48 * agreements) 131071 T YS S) :
    MvPolynomial.weightedTotalDegree (ContactFactorCaps.contactWeights 131071)
        (highSourceCore nodes u0 u1 g b) ≤
      48 * agreements - 1 := by
  apply contact_le_47agreements_sub_one_of_dvd
    (highSourceCore nodes u0 u1 g b)
    (reconstruct K 11458062 131071 familyMaxTotal 18 g)
    hfixed
  · exact highSourceCore_dvd_fixed_reconstruct nodes u0 u1 g b
  · exact nestedFiveCap_fixedSource_mem_globalCoefficientBox _ hfixedBox

 

theorem canonicalHighSourceCore_contact_le_47agreements_sub_one
    (nodes u0 u1 : I → K)
    (g : CoefficientIndex 11458062 131071 familyMaxTotal 18 → K)
    {T YS S : Nat}
    (hfixed : reconstruct K 11458062 131071 familyMaxTotal 18 g ≠ 0)
    (hfixedBox : reconstruct K 11458062 131071 familyMaxTotal 18 g ∈
      nestedFiveCapCoefficientBox K
        (48 * agreements) 131071 T YS S) :
    MvPolynomial.weightedTotalDegree (ContactFactorCaps.contactWeights 131071)
        (canonicalHighSourceCore nodes u0 u1 g) ≤
      48 * agreements - 1 := by
  exact highSourceCore_contact_le_47agreements_sub_one
    nodes u0 u1 g (highSourceBasis nodes u0 u1 g) hfixed hfixedBox

end

end ContactAnchoredHighSourceContactCap6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactAnchoredHighSourceContactCap6750Research.nestedFiveCap_fixedSource_mem_globalCoefficientBox
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredHighSourceContactCap6750Research.highSourceCore_contact_le_47agreements_sub_one
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredHighSourceContactCap6750Research.canonicalHighSourceCore_contact_le_47agreements_sub_one
