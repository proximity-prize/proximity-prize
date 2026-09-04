import ProximityPrize.SubmissionLower.LocatorResidualGrouped6803
import ProximityPrize.SubmissionLower.LocatorGroupedCoverCardinality6803
import ProximityPrize.SubmissionLower.LocatorCover

/-!
# Retained residual cover for the 68.03 row

This module combines the retained quotient boxes, the unequal regular-pair
bound, and the branch-free grouped derivative tail into one residual-set
consumer.  Its output has exactly the four summands used by the checked
coupled receipt.
-/

namespace ProximityPrize.SubmissionLower.LocatorResidualBridge6803

open ProximityPrize.Benchmark
open scoped Classical BigOperators
open RCN052 RCN081 RCN095 RCN100 RCN130 RCN140 RCN156 RCN167 RCN174 RCN180
  RCN234 RCN238 RCN243 RCN259 RCN266 RCN319
open LocatorFactorAggregate LocatorCoprimeQuotient
  LocatorRetainedQuotient6803 LocatorRetainedResidualBridge6803
  LocatorResidualRegular6803 LocatorResidualGrouped6803
  LocatorGroupedNonRegularAssembly6803
  LocatorGroupedNonRegularCardinality6803
  LocatorGroupedCoverCardinality6803

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq (Polynomial K) := Classical.decEq (Polynomial K)
local instance : GCDMonoid P4 := UniqueFactorizationMonoid.toGCDMonoid P4
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

/-- The quotient statement before forgetting the three weighted caps. -/
theorem quotientB_mem_retained_flag_box
    (QA QB P : P4) (hQA : QA ≠ 0) (hQB : QB ≠ 0) (hP : P ≠ 0)
    (hQBbox : QB ∈ RCN100.globalCoefficientBox K
      20131293 131071 14261 34)
    (hPH : P ∣ gcd12 QA QB) :
    quotientB QA QB ∈ RCN100.globalCoefficientBox K
      (20131293 - retainedContact 131071 (originalCumulativeFlag P)) 131071
      (14261 - LocatorRetainedQuotient6803.total (originalCumulativeFlag P))
      (34 - (originalCumulativeFlag P).all) := by
  let H := gcd12 QA QB
  let Q := quotientB QA QB
  have hH : H ≠ 0 := gcd_ne_zero_of_left hQA
  have hQeq : QB = H * Q := b_eq_gcd12_mul_quotientB QA QB
  have hQ : Q ≠ 0 := by
    intro hz
    exact hQB (by rw [hQeq, hz, mul_zero])
  exact quotient_mem_box_of_retained_divisor
    QB H Q P 20131293 131071 14261 34
      hQB hH hQ hP hQBbox hQeq hPH (by decide)

private theorem quotientB_retained_weight_caps
    (QA QB P : P4) (hQA : QA ≠ 0) (hQB : QB ≠ 0) (hP : P ≠ 0)
    (hQBbox : QB ∈ RCN100.globalCoefficientBox K
      20131293 131071 14261 34)
    (hPH : P ∣ gcd12 QA QB)
    (hs : (originalCumulativeFlag P).all ≤ 29)
    (hy : LocatorRetainedQuotient6803.middle (originalCumulativeFlag P) ≤ 135) :
    wt residualYSWeights (quotientB QA QB) ≤
        153 - LocatorRetainedQuotient6803.middle (originalCumulativeFlag P) ∧
      wt residualSWeights (quotientB QA QB) ≤
        34 - (originalCumulativeFlag P).all ∧
      wt residualTotalWeights (quotientB QA QB) ≤
        14261 - LocatorRetainedQuotient6803.total (originalCumulativeFlag P) ∧
      wt (contactWeights 131071) (quotientB QA QB) ≤
        20131293 - retainedContact 131071 (originalCumulativeFlag P) - 1 := by
  let p := originalCumulativeFlag P
  let Q := quotientB QA QB
  have hyraw : p.yz + p.all ≤ 135 := by
    simpa only [p, LocatorRetainedQuotient6803.middle] using hy
  have hD : 0 < 20131293 - retainedContact 131071 p := by
    unfold retainedContact LocatorRetainedQuotient6803.middle
    omega
  have hflag := quotientB_mem_retained_flag_box
    QA QB P hQA hQB hP hQBbox hPH
  have hcaps := (mem_flagGlobalCoefficientBox_iff Q
    (20131293 - retainedContact 131071 p) 131071
      (14261 - LocatorRetainedQuotient6803.total p) (34 - p.all) hD).mp hflag
  have hweighted := residualYS_mul_le_contact_add_slope Q 131071 (by decide)
  have hY : wt residualYSWeights Q ≤
      153 - LocatorRetainedQuotient6803.middle p := by
    unfold retainedContact LocatorRetainedQuotient6803.middle at hcaps
    unfold LocatorRetainedQuotient6803.middle
    omega
  exact ⟨hY, hcaps.2.1, hcaps.1, hcaps.2.2⟩

/-- The residual set after retaining `P` is bounded by the exact four-term
receipt charge: unequal regular pair, grouped predecessor, escape dot, and
one exact-contact aggregate tail. -/
theorem retained_residual_count_le
    (QA QB P : P4) (hQA : QA ≠ 0) (hQB : QB ≠ 0) (hP : P ≠ 0)
    (hQAbox : QA ∈ RCN100.globalCoefficientBox K
      32826703 131071 6679 56)
    (hQBbox : QB ∈ RCN100.globalCoefficientBox K
      20131293 131071 14261 34)
    (hPH : P ∣ gcd12 QA QB)
    (hs : (originalCumulativeFlag P).all ≤ 29)
    (hy : LocatorRetainedQuotient6803.middle (originalCumulativeFlag P) ≤ 135)
    (ht : LocatorRetainedQuotient6803.total (originalCumulativeFlag P) ≤ 6676)
    (selected : K → Polynomial K) (Gamma : Finset K) (u0 u1 : I → K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181363 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80781)
    (hAsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma QA = 0)
    (hBsolution : ∀ gamma ∈ Gamma,
      specialization K (selected gamma) gamma QB = 0) :
    let phi : K → P4 →+* Polynomial K := fun gamma ↦
      (specialization K (selected gamma) gamma).toRingHom
    let Delta := LocatorCover.residual phi Gamma QA QB
    Delta.card ≤
      (residualPairStage (originalCumulativeFlag P)).regularCountCap +
        (residualBGroupedStage (originalCumulativeFlag P)).regularCountCap +
        residualBMaxEscapeDot +
        (residualBExactTailStage (originalCumulativeFlag P)).countCap := by
  dsimp only
  let phi : K → P4 →+* Polynomial K := fun gamma ↦
    (specialization K (selected gamma) gamma).toRingHom
  let Delta := LocatorCover.residual phi Gamma QA QB
  let Q := quotientB QA QB
  let T := quotientA QA QB
  let p := originalCumulativeFlag P
  have hH : gcd12 QA QB ≠ 0 := gcd_ne_zero_of_left hQA
  have hQ : Q ≠ 0 := by
    intro hz
    exact hQB (by rw [b_eq_gcd12_mul_quotientB QA QB, show quotientB QA QB = Q by rfl,
      hz, mul_zero])
  have hsub : Delta ⊆ Gamma := by
    intro gamma hgamma
    exact (Finset.mem_filter.mp hgamma).1
  have hdegreeD : ∀ gamma ∈ Delta,
      (selected gamma).natDegree ≤ 131071 :=
    fun gamma hgamma ↦ hdegree gamma (hsub hgamma)
  have hagreementD : ∀ gamma ∈ Delta, 181363 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card :=
    fun gamma hgamma ↦ hagreement gamma (hsub hgamma)
  have hnoD : NoLargeSelectedPencil selected Delta 131071 80781 :=
    RCN243.noLargeSelectedPencil_mono selected Gamma Delta
      131071 80781 hsub hno
  have hquotientSolutions : ∀ gamma ∈ Delta,
      specialization K (selected gamma) gamma T = 0 ∧
        specialization K (selected gamma) gamma Q = 0 := by
    intro gamma hgamma
    change phi gamma T = 0 ∧ phi gamma Q = 0
    simpa only [T, Q] using LocatorCover.residual_vanish phi Gamma QA QB
        (fun gamma hgamma ↦ hAsolution gamma hgamma)
        (fun gamma hgamma ↦ hBsolution gamma hgamma)
        gamma hgamma
  have hweights := quotientB_retained_weight_caps
    QA QB P hQA hQB hP hQBbox hPH hs hy
  have hregular := retained_regularPairSeeds_sum_le
    QA QB P hQA hQB hP hQAbox hQBbox hPH hs
      selected Delta u0 u1 hdegreeD hagreementD hnoD
  have hgrouped := residual_grouped_exact p hs hy ht Q hQ
    hweights.1 hweights.2.1 hweights.2.2.1 hweights.2.2.2
    selected Delta u0 u1 hdegreeD hagreementD hnoD
  have hR : ∀ F ∈ positiveRFactors Q,
      F.degreeOf 2 ≤ 34 - p.all := by
    intro F hF
    exact (RCN081.degreeOf_le_of_dvd (2 : Fin 4) F Q
      (positiveRFactors_spec Q F hF).2.1 hQ).trans
        (by
          have hdegreeQ : Q.degreeOf (2 : Fin 4) ≤
              wt residualSWeights Q := by
            apply MvPolynomial.degreeOf_le_iff.mpr
            intro d hd
            have h := MvPolynomial.le_weightedTotalDegree residualSWeights hd
            rw [weight_fin4] at h
            change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤
              MvPolynomial.weightedTotalDegree residualSWeights Q at h
            simpa only [Nat.mul_zero, Nat.mul_one, Nat.add_zero,
              Nat.zero_add, RCN234.wt] using h
          exact hdegreeQ.trans hweights.2.1)
  have hcard := residual_card_le_regular_add_grouped
    Q T hQ 2130706433 (34 - p.all)
      ((Nat.sub_le _ _).trans_lt (by decide)) hR
      selected Delta
      (fun gamma hgamma ↦ (hquotientSolutions gamma hgamma).2)
      (fun gamma hgamma ↦ (hquotientSolutions gamma hgamma).1)
      (residualPairStage p).regularCountCap
      ((residualBGroupedStage p).regularCountCap + residualBMaxEscapeDot +
        (residualBExactTailStage p).countCap)
      (by simpa only [Q, T, p] using hregular)
      hgrouped
  simpa only [Delta, p, Nat.add_assoc] using hcard

end

end ProximityPrize.SubmissionLower.LocatorResidualBridge6803
