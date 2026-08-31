import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAnchoredHardCellSelector6750Research
import ProximityPrize.SubmissionLower.ContactAnchoredHighKernelLowSlice6750Research
import ProximityPrize.SubmissionLower.ContactFlagNestedKernelCommonGCD6750Research
import ProximityPrize.SubmissionLower.ContactFlagNestedSpanSpecialization6750Research
import ProximityPrize.SubmissionLower.ContactFlagNestedCommonCoreRealizer6750Research

 

















namespace ProximityPrize.SubmissionLower
namespace ContactAnchoredHighSourceHull6750Research

open scoped Classical BigOperators
open ContactTranslation
open ContactFlagInterpolation6641Research
open ContactFlagKernelZeroExtension6750Research
open ContactFlagNestedKernelCommonGCD6750Research
open ContactFlagNestedSpanSpecialization6750Research
open ContactFlagNestedCommonCoreRealizer6750Research
open ContactAnchoredOneFamilySelector6750Research
open ContactAnchoredHighKernelLowSlice6750Research
open ContactNestedFiveCapCoefficientBox6750Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000

universe u v x

variable {K : Type u} [Field K]
variable {I : Type v} [Fintype I]

abbrev Poly4 (K : Type u) [Field K] := MvPolynomial (Fin 4) K

 

abbrev HighFamilyIndex := Fin (familyMaxTotal + 1)

def highFamilyCap (i : HighFamilyIndex) : Nat := i.val

theorem highFamilyCap_le (i : HighFamilyIndex) :
    highFamilyCap i ≤ familyMaxTotal := by
  exact Nat.le_of_lt_succ i.isLt

 


def fullHighKernelSelection
    (nodes u0 u1 : I → K) (i : HighFamilyIndex) :
    Submodule K
      (LinearMap.ker
        (constraintMap K 11458062 131071 (highFamilyCap i) 18 63
          nodes u0 u1)) :=
  ⊤

 
abbrev fullHighKernelFamilySum
    (nodes u0 u1 : I → K) :
    Submodule K (CoefficientIndex 11458062 131071 familyMaxTotal 18 → K) :=
  embeddedSelectedKernelFamilySum 11458062 131071 familyMaxTotal 18 63
    nodes u0 u1 highFamilyCap highFamilyCap_le
      (fullHighKernelSelection nodes u0 u1)

 
abbrev highSourceHull
    (nodes u0 u1 : I → K)
    (g : CoefficientIndex 11458062 131071 familyMaxTotal 18 → K) :
    Submodule K (CoefficientIndex 11458062 131071 familyMaxTotal 18 → K) :=
  adjoinFixedArray g (fullHighKernelFamilySum nodes u0 u1)

 
def highSourceCore
    (nodes u0 u1 : I → K)
    (g : CoefficientIndex 11458062 131071 familyMaxTotal 18 → K)
    {β : Type x} [Fintype β]
    (b : Module.Basis β K (highSourceHull nodes u0 u1 g)) : Poly4 K :=
  commonGCDAtMax (highSourceHull nodes u0 u1 g) b

 


noncomputable def highSourceBasis
    (nodes u0 u1 : I → K)
    (g : CoefficientIndex 11458062 131071 familyMaxTotal 18 → K) :
    Module.Basis
      (Module.Free.ChooseBasisIndex K (highSourceHull nodes u0 u1 g)) K
      (highSourceHull nodes u0 u1 g) :=
  Module.Free.chooseBasis K (highSourceHull nodes u0 u1 g)

 
noncomputable def canonicalHighSourceCore
    (nodes u0 u1 : I → K)
    (g : CoefficientIndex 11458062 131071 familyMaxTotal 18 → K) : Poly4 K :=
  highSourceCore nodes u0 u1 g (highSourceBasis nodes u0 u1 g)

theorem highSourceCore_ne_zero
    (nodes u0 u1 : I → K)
    (g : CoefficientIndex 11458062 131071 familyMaxTotal 18 → K)
    {β : Type x} [Fintype β] [Nonempty β]
    (b : Module.Basis β K (highSourceHull nodes u0 u1 g)) :
    highSourceCore nodes u0 u1 g b ≠ 0 :=
  commonGCDAtMax_ne_zero (highSourceHull nodes u0 u1 g) b

 


theorem highSourceCore_dvd_fixed_reconstruct
    (nodes u0 u1 : I → K)
    (g : CoefficientIndex 11458062 131071 familyMaxTotal 18 → K)
    {β : Type x} [Fintype β]
    (b : Module.Basis β K (highSourceHull nodes u0 u1 g)) :
    highSourceCore nodes u0 u1 g b ∣
      reconstruct K 11458062 131071 familyMaxTotal 18 g := by
  have hall :=
    (dvd_commonGCDAtMax_adjoinedSelectedFamily_iff
      11458062 131071 familyMaxTotal 18 63 nodes u0 u1
      highFamilyCap highFamilyCap_le (fullHighKernelSelection nodes u0 u1)
      g b (highSourceCore nodes u0 u1 g b)).mp dvd_rfl
  exact hall.1

 


theorem highSourceCore_dvd_fullKernel_reconstruct
    (nodes u0 u1 : I → K)
    (g : CoefficientIndex 11458062 131071 familyMaxTotal 18 → K)
    {β : Type x} [Fintype β]
    (b : Module.Basis β K (highSourceHull nodes u0 u1 g))
    (i : HighFamilyIndex)
    (theta : LinearMap.ker
      (constraintMap K 11458062 131071 (highFamilyCap i) 18 63
        nodes u0 u1)) :
    highSourceCore nodes u0 u1 g b ∣
      reconstruct K 11458062 131071 (highFamilyCap i) 18 theta.1 := by
  let thetaTop : fullHighKernelSelection nodes u0 u1 i := ⟨theta, trivial⟩
  have hall :=
    (dvd_commonGCDAtMax_adjoinedSelectedFamily_iff
      11458062 131071 familyMaxTotal 18 63 nodes u0 u1
      highFamilyCap highFamilyCap_le (fullHighKernelSelection nodes u0 u1)
      g b (highSourceCore nodes u0 u1 g b)).mp dvd_rfl
  exact hall.2 i thetaTop

 
theorem canonicalHighSourceCore_dvd_fixed_reconstruct
    (nodes u0 u1 : I → K)
    (g : CoefficientIndex 11458062 131071 familyMaxTotal 18 → K) :
    canonicalHighSourceCore nodes u0 u1 g ∣
      reconstruct K 11458062 131071 familyMaxTotal 18 g := by
  exact highSourceCore_dvd_fixed_reconstruct nodes u0 u1 g
    (highSourceBasis nodes u0 u1 g)

 

theorem canonicalHighSourceCore_dvd_fullKernel_reconstruct
    (nodes u0 u1 : I → K)
    (g : CoefficientIndex 11458062 131071 familyMaxTotal 18 → K)
    (i : HighFamilyIndex)
    (theta : LinearMap.ker
      (constraintMap K 11458062 131071 (highFamilyCap i) 18 63
        nodes u0 u1)) :
    canonicalHighSourceCore nodes u0 u1 g ∣
      reconstruct K 11458062 131071 (highFamilyCap i) 18 theta.1 := by
  exact highSourceCore_dvd_fullKernel_reconstruct nodes u0 u1 g
    (highSourceBasis nodes u0 u1 g) i theta

 


theorem canonicalHighSourceCore_ne_zero_of_fixed
    (nodes u0 u1 : I → K)
    (g : CoefficientIndex 11458062 131071 familyMaxTotal 18 → K)
    (hfixed : reconstruct K 11458062 131071 familyMaxTotal 18 g ≠ 0) :
    canonicalHighSourceCore nodes u0 u1 g ≠ 0 := by
  intro hcore
  obtain ⟨Q, hQ⟩ := canonicalHighSourceCore_dvd_fixed_reconstruct
    nodes u0 u1 g
  apply hfixed
  rw [hQ, hcore, zero_mul]

 

theorem fullHighKernel_member_specializes_zero
    [DecidableEq K] [DecidableEq I]
    (nodes : I ↪ K) (u0 u1 : I → K)
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hP : P.natDegree ≤ 131071)
    (hcard : 181874 ≤ support.card)
    (hvalues : ∀ i ∈ support,
      P.eval (nodes i) = u0 i + gamma * u1 i) :
    ∀ (i : HighFamilyIndex)
      (theta : fullHighKernelSelection nodes u0 u1 i),
      specialization K P gamma
        (reconstruct K 11458062 131071 (highFamilyCap i) 18
          theta.1.1) = 0 := by
  intro i theta
  exact specialization_eq_zero_of_mem_m61_high_kernel
    (highFamilyCap i) nodes u0 u1 theta.1.1 theta.1.2
      P gamma support hP hcard hvalues

 
theorem specialization_eq_zero_of_mem_highSourceHull
    [DecidableEq K] [DecidableEq I]
    (nodes : I ↪ K) (u0 u1 : I → K)
    (g : CoefficientIndex 11458062 131071 familyMaxTotal 18 → K)
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hP : P.natDegree ≤ 131071)
    (hcard : 181874 ≤ support.card)
    (hvalues : ∀ i ∈ support,
      P.eval (nodes i) = u0 i + gamma * u1 i)
    (hfixed : specialization K P gamma
      (reconstruct K 11458062 131071 familyMaxTotal 18 g) = 0)
    (v : highSourceHull nodes u0 u1 g) :
    specialization K P gamma
      (reconstruct K 11458062 131071 familyMaxTotal 18 v.1) = 0 := by
  exact specialization_eq_zero_of_mem_adjoinedSelectedFamily
    11458062 131071 familyMaxTotal 18 63 nodes u0 u1
      highFamilyCap highFamilyCap_le (fullHighKernelSelection nodes u0 u1)
      g P gamma hfixed
      (fullHighKernel_member_specializes_zero
        nodes u0 u1 P gamma support hP hcard hvalues) v

 

theorem highSourceHull_quotient_specializes_zero
    [DecidableEq K] [DecidableEq I]
    (nodes : I ↪ K) (u0 u1 : I → K)
    (g : CoefficientIndex 11458062 131071 familyMaxTotal 18 → K)
    {β : Type x} [Fintype β]
    (b : Module.Basis β K (highSourceHull nodes u0 u1 g))
    (P : Polynomial K) (gamma : K) (support : Finset I)
    (hP : P.natDegree ≤ 131071)
    (hcard : 181874 ≤ support.card)
    (hvalues : ∀ i ∈ support,
      P.eval (nodes i) = u0 i + gamma * u1 i)
    (hfixed : specialization K P gamma
      (reconstruct K 11458062 131071 familyMaxTotal 18 g) = 0)
    (hcore : specialization K P gamma
      (highSourceCore nodes u0 u1 g b) ≠ 0)
    (v : highSourceHull nodes u0 u1 g)
    (Q : Poly4 K)
    (hfactor : reconstruct K 11458062 131071 familyMaxTotal 18 v.1 =
      highSourceCore nodes u0 u1 g b * Q) :
    specialization K P gamma Q = 0 := by
  apply quotient_specialization_eq_zero_of_mul_eq P gamma
    (reconstruct K 11458062 131071 familyMaxTotal 18 v.1)
    (highSourceCore nodes u0 u1 g b) Q hfactor
  · exact specialization_eq_zero_of_mem_highSourceHull
      nodes u0 u1 g P gamma support hP hcard hvalues hfixed v
  · exact hcore

 

theorem reconstruct_mem_high_parent_of_mem_fullHighKernelFamilySum
    (nodes u0 u1 : I → K)
    (a : fullHighKernelFamilySum nodes u0 u1) :
    reconstruct K 11458062 131071 familyMaxTotal 18 a.1 ∈
      nestedFiveCapCoefficientBox K 11458062 131071
        familyMaxTotal 87 18 := by
  apply reconstruct_mem_nestedFiveCap_of_mem_selectedFamilySum
    11458062 131071 familyMaxTotal 18 63 familyMaxTotal 87 18
      nodes u0 u1 highFamilyCap highFamilyCap_le
      (fullHighKernelSelection nodes u0 u1)
  · intro i theta
    have hbox := reconstruct_mem_m61_high_fiveCap
      (highFamilyCap i) theta.1.1
    change ∀ d ∈ (reconstruct K 11458062 131071
      (highFamilyCap i) 18 theta.1.1).support,
        d 1 + d 2 + d 3 ≤ familyMaxTotal ∧
        d 1 + d 2 ≤ 87 ∧ d 2 ≤ 18 ∧
        d 0 + 131071 * d 1 + (131071 - 1) * d 2 < 11458062
    change ∀ d ∈ (reconstruct K 11458062 131071
      (highFamilyCap i) 18 theta.1.1).support,
        d 1 + d 2 + d 3 ≤ highFamilyCap i ∧
        d 1 + d 2 ≤ 87 ∧ d 2 ≤ 18 ∧
        d 0 + 131071 * d 1 + (131071 - 1) * d 2 < 11458062 at hbox
    intro d hd
    have h := hbox d hd
    exact ⟨h.1.trans (highFamilyCap_le i), h.2.1, h.2.2.1, h.2.2.2⟩

end

end ContactAnchoredHighSourceHull6750Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactAnchoredHighSourceHull6750Research.highSourceCore_dvd_fullKernel_reconstruct
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredHighSourceHull6750Research.highSourceCore_dvd_fixed_reconstruct
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredHighSourceHull6750Research.specialization_eq_zero_of_mem_highSourceHull
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredHighSourceHull6750Research.highSourceHull_quotient_specializes_zero
#print axioms ProximityPrize.SubmissionLower.ContactAnchoredHighSourceHull6750Research.reconstruct_mem_high_parent_of_mem_fullHighKernelFamilySum
