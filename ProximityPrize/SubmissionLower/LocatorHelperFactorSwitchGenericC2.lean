/-
Re-derived from the public proximity-prize repository, PR #471, commit db5c259
(submission 8aab1b73-c3cb-4cd9-a382-f1ed2c2dadc2, score 6784), authored by jieyilong.
Row constants are taken from LocatorReplacementGridData rather than written as
literals, so a row retune is a one-line change in GridCore and never here.
-/
import ProximityPrize.SubmissionLower.LocatorGenericSourceCount
import ProximityPrize.SubmissionLower.BF

namespace ProximityPrize.SubmissionLower.LocatorHelperFactorSwitchGenericC2

open ProximityPrize.Benchmark
open RCN081 RCN100 RCN101 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN260 RCN266 RCN319
open LocatorCoprimeQuotient LocatorLowQuotient LocatorReplacementGridData

open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

abbrev HelperKernel (D L s m : ℕ) (u0 u1 : I → K) :=
  ConstraintKernel (K := K) D selectedDegree L s m IRSProfile.domain u0 u1

def helperPair (rightY rightR rightZ leftY leftR leftZ : ℕ) :
    UnequalParameters :=
  ⟨262144, selectedDegree, agreements, leftY, leftR, leftZ,
    rightY, rightR, rightZ⟩

def HelperPairGates
    (rightY rightR rightZ leftY leftR leftZ : ℕ) : Prop :=
  let P := helperPair rightY rightR rightZ leftY leftR leftZ
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

/-- For any helper source, a regular irreducible factor either divides the
whole helper kernel or one helper witness is coprime and supplies the pair
count.  Source-specific arithmetic is kept out of this theorem. -/
theorem divisor_or_helper_count
    (D L s m rightY : ℕ)
    (hD : 0 < D)
    (hDa : D = m * agreements)
    (hshape : D + s ≤ selectedDegree * (rightY + 1))
    {u0 u1 : I → K} {H : P4}
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ selectedDegree)
    (hagreement : ∀ gamma ∈ Gamma, agreements ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma selectedDegree
      (262144 - agreements))
    (F : RegularIndex H) (leftY leftR leftZ : ℕ)
    (hFY : F.1.degreeOf 1 ≤ leftY)
    (hFR : F.1.degreeOf 2 ≤ leftR)
    (hFZ : F.1.degreeOf 3 ≤ leftZ)
    (hgates : HelperPairGates rightY s L leftY leftR leftZ) :
    (∀ v : HelperKernel D L s m u0 u1,
      F.1 ∣ reconstruct K D selectedDegree L s v.1) ∨
      (regularSeeds H selected Gamma F).card ≤
        (helperPair rightY s L leftY leftR leftZ).regularCountCap := by
  classical
  by_cases hdiv : ∀ v : HelperKernel D L s m u0 u1,
      F.1 ∣ reconstruct K D selectedDegree L s v.1
  · exact Or.inl hdiv
  · right
    push Not at hdiv
    obtain ⟨v, hv⟩ := hdiv
    let Q := reconstruct K D selectedDegree L s v.1
    have hF := RCN167.positiveRFactors_spec H F.1 F.2
    have hrel : IsRelPrime F.1 Q :=
      hF.1.isRelPrime_iff_not_dvd.mpr hv
    have hQbox : Q ∈ globalCoefficientBox K D selectedDegree L s :=
      reconstruct_mem_globalCoefficientBox K D selectedDegree L s v.1
    have hQYS : wt residualYSWeights Q ≤ rightY := by
      apply flag_box_ys_bound D selectedDegree L s rightY (by decide) hshape Q hQbox
    have hweights := (mem_flagGlobalCoefficientBox_iff Q
      D selectedDegree L s hD).mp hQbox
    have hQY : Q.degreeOf 1 ≤ rightY :=
      (degreeY_le_ysWeight Q).trans hQYS
    have hQR : Q.degreeOf 2 ≤ s :=
      (degreeR_le_sWeight Q).trans hweights.2.1
    have hQZ : Q.degreeOf 3 ≤ L :=
      (degreeZ_le_totalWeight Q).trans hweights.1
    obtain ⟨hleftR, hleftYSmall, hleftRSmall, hleftZSmall,
      hmixedYSmall, hmixedRSmall, hmixedZSmall⟩ := hgates
    apply regularSeeds_count_le_intersection
      (helperPair rightY s L leftY leftR leftZ)
      H Q F hrel 2130706433 hFY hFR hFZ hQY hQR hQZ
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
      (by simpa only [helperPair, UnequalParameters.errors] using hno)
    intro gamma hgamma
    dsimp only [Q]
    apply specialization_eq_zero_of_mem_ker K
      D selectedDegree L s m IRSProfile.domain u0 u1
      v.1 v.2 (selected gamma) gamma
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i))
    · exact hD
    · exact hdegree gamma (Finset.mem_filter.mp hgamma).1
    · rw [hDa]
      exact Nat.mul_le_mul_left m
        (hagreement gamma (Finset.mem_filter.mp hgamma).1)
    · intro i hi
      exact (Finset.mem_filter.mp hi).2

end

end ProximityPrize.SubmissionLower.LocatorHelperFactorSwitchGenericC2
