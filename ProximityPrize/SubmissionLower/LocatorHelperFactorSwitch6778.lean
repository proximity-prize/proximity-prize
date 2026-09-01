import ProximityPrize.SubmissionLower.LocatorFifthPowerAvoidance
import ProximityPrize.SubmissionLower.BF

namespace ProximityPrize.SubmissionLower.LocatorHelperFactorSwitch6778

open ProximityPrize.Benchmark
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN260 RCN266 RCN319
open LocatorCoprimeQuotient LocatorLowQuotient

open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

/-- The larger interpolation kernel used only by the local factor switch. -/
abbrev HelperKernel (u0 u1 : I → K) :=
  ConstraintKernel (K := K) 53211437 131071 359728 87 293
    IRSProfile.domain u0 u1

/-- Unequal-pair parameters for a regular factor and one helper witness. -/
def helperPair (leftY leftR leftZ : ℕ) : UnequalParameters :=
  ⟨262144, 131071, 181609, leftY, leftR, leftZ, 405, 87, 359728⟩

def HelperPairGates (leftY leftR leftZ : ℕ) : Prop :=
  let P := helperPair leftY leftR leftZ
  1 ≤ P.leftR ∧ P.leftY < 2130706433 ∧ P.leftR < 2130706433 ∧
    P.leftZ < 2130706433 ∧ P.mixedCost.y < 2130706433 ∧
    P.mixedCost.r < 2130706433 ∧ P.mixedCost.z < 2130706433

private theorem degreeY_le_ysWeight (Q : P4) :
    Q.degreeOf (1 : Fin 4) ≤ wt residualYSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤
    wt residualYSWeights Q at h
  omega

private theorem degreeR_le_sWeight (Q : P4) :
    Q.degreeOf (2 : Fin 4) ≤ wt residualSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤
    wt residualSWeights Q at h
  omega

private theorem degreeZ_le_totalWeight (Q : P4) :
    Q.degreeOf (3 : Fin 4) ≤ wt residualTotalWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤
    wt residualTotalWeights Q at h
  omega

/-- For each regular irreducible factor, either it divides the whole helper
kernel or a single coprime helper witness gives the unequal-pair count. -/
theorem divisor_or_helper_count
    {u0 u1 : I → K} {H : P4}
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181609 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80535)
    (F : RegularIndex H) (leftY leftR leftZ : ℕ)
    (hFY : F.1.degreeOf 1 ≤ leftY)
    (hFR : F.1.degreeOf 2 ≤ leftR)
    (hFZ : F.1.degreeOf 3 ≤ leftZ)
    (hgates : HelperPairGates leftY leftR leftZ) :
    (∀ v : HelperKernel u0 u1,
      F.1 ∣ reconstruct K 53211437 131071 359728 87 v.1) ∨
      (regularSeeds H selected Gamma F).card ≤
        (helperPair leftY leftR leftZ).regularCountCap := by
  classical
  by_cases hdiv : ∀ v : HelperKernel u0 u1,
      F.1 ∣ reconstruct K 53211437 131071 359728 87 v.1
  · exact Or.inl hdiv
  · right
    push Not at hdiv
    obtain ⟨v, hv⟩ := hdiv
    let Q := reconstruct K 53211437 131071 359728 87 v.1
    have hF := RCN167.positiveRFactors_spec H F.1 F.2
    have hrel : IsRelPrime F.1 Q :=
      hF.1.isRelPrime_iff_not_dvd.mpr hv
    have hQbox : Q ∈ globalCoefficientBox K 53211437 131071 359728 87 :=
      reconstruct_mem_globalCoefficientBox K 53211437 131071 359728 87 v.1
    have hQYS : wt residualYSWeights Q ≤ 405 := by
      apply flag_box_ys_bound 53211437 131071 359728 87 405
        (by decide) (by decide) Q hQbox
    have hweights := (mem_flagGlobalCoefficientBox_iff Q
      53211437 131071 359728 87 (by decide)).mp hQbox
    have hQY : Q.degreeOf 1 ≤ 405 :=
      (degreeY_le_ysWeight Q).trans hQYS
    have hQR : Q.degreeOf 2 ≤ 87 :=
      (degreeR_le_sWeight Q).trans hweights.2.1
    have hQZ : Q.degreeOf 3 ≤ 359728 :=
      (degreeZ_le_totalWeight Q).trans hweights.1
    obtain ⟨hleftR, hleftYSmall, hleftRSmall, hleftZSmall,
      hmixedYSmall, hmixedRSmall, hmixedZSmall⟩ := hgates
    apply regularSeeds_count_le_intersection
      (helperPair leftY leftR leftZ) H Q F hrel 2130706433
      hFY hFR hFZ hQY hQR hQZ
      hleftR hleftYSmall hleftRSmall hleftZSmall
      hmixedYSmall hmixedRSmall hmixedZSmall
      selected Gamma (Finset.univ : Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
      (by
        change (Finset.univ : Finset I).card = 262144
        rw [Finset.card_univ]
        norm_num [I, IRSProfile.Index])
      (by norm_num [helperPair]) (by norm_num [helperPair])
      (by norm_num [helperPair]) (by norm_num [helperPair])
      (by simpa only [helperPair] using hdegree)
      (by simpa only [helperPair] using hagreement)
      (by simpa only [helperPair, UnequalParameters.errors, Nat.reduceSub] using hno)
    intro gamma hgamma
    dsimp only [Q]
    apply specialization_eq_zero_of_mem_ker K
      53211437 131071 359728 87 293 IRSProfile.domain u0 u1
      v.1 v.2 (selected gamma) gamma
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i))
    · decide
    · exact hdegree gamma (Finset.mem_filter.mp hgamma).1
    · have hcard := hagreement gamma (Finset.mem_filter.mp hgamma).1
      omega
    · intro i hi
      exact (Finset.mem_filter.mp hi).2

end

end ProximityPrize.SubmissionLower.LocatorHelperFactorSwitch6778
