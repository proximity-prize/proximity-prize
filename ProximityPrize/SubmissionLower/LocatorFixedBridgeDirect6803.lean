import ProximityPrize.SubmissionLower.LocatorFixedBridge6803
import ProximityPrize.SubmissionLower.LocatorFixed

/-! The direct-helper half of the retuned initial-A bridge. -/

namespace ProximityPrize.SubmissionLower.LocatorFixedBridge6803

open ProximityPrize.Benchmark
open scoped Classical
open RCN081 RCN095 RCN100 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234
  RCN238 RCN260 RCN266 RCN275 RCN319
open LocatorFactorAggregate LocatorCoprimeQuotient LocatorLowQuotient

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using
    RCN128.challenge_field_characteristic6600

private theorem degreeY_le_ysWeight (Q : P4) :
    Q.degreeOf (1 : Fin 4) ≤ wt residualYSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤
    wt residualYSWeights Q at h
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

private theorem degreeR_le_sWeight (Q : P4) :
    Q.degreeOf (2 : Fin 4) ≤ wt residualSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 0 + d 2 * 1 + d 3 * 0 ≤
    wt residualSWeights Q at h
  omega

private theorem initialA_helper_gates (p : FlagDegree)
    (hr : 1 ≤ p.all) (hs : p.all ≤ 34)
    (hy : middle p ≤ 153) (ht : total p ≤ 6676) :
    LocatorGenericHelperFactorSwitch6803.HelperPairGates
      130000 135 29 (middle p) p.all (total p) := by
  unfold LocatorGenericHelperFactorSwitch6803.HelperPairGates
  change 1 ≤ p.all ∧ middle p < 2130706433 ∧
    p.all < 2130706433 ∧ total p < 2130706433 ∧
    p.all * 130000 + total p * 29 < 2130706433 ∧
    middle p * 130000 + total p * 135 < 2130706433 ∧
    middle p * 29 + p.all * 135 < 2130706433
  omega

/-- A factor outside the A-universal child gets the direct coprime helper
charge with the retuned agreement and error thresholds. -/
theorem initialA_nonuniversal_count
    (u0 u1 : I → K) (H : P4) (hH : H ≠ 0)
    (hwide : ResidualSupportData wideSupport H)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181363 ≤
      ((Finset.univ : Finset I).filter fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80781)
    (F : RegularIndex H) (hFU : F ∉ initialAUniversalFactors u0 u1 H) :
    (regularSeeds H selected Gamma F).card ≤
      initialAHelperCap (regularCumulativeFlag H F) := by
  have hFsupport := LocatorFixed.factor_support H hH hwide F
  have hc := originalCumulativeFlag_cumulative F.1
  have hs : (regularCumulativeFlag H F).all ≤ 34 := by
    simpa only [regularCumulativeFlag, hc.1, wideSupport] using
      hFsupport.s_weight
  have hy : middle (regularCumulativeFlag H F) ≤ 153 := by
    simpa only [regularCumulativeFlag, middle, hc.2.1, wideSupport] using
      hFsupport.ys_weight
  have ht : total (regularCumulativeFlag H F) ≤ 6676 := by
    simpa only [regularCumulativeFlag, total, hc.2.2, wideSupport] using
      hFsupport.total_weight
  have hr : 1 ≤ (regularCumulativeFlag H F).all :=
    Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (regularCumulativeFlag_positive H F))
  have hFY : F.1.degreeOf 1 ≤ middle (regularCumulativeFlag H F) := by
    rw [regularCumulativeFlag, middle, hc.2.1]
    exact degreeY_le_ysWeight F.1
  have hFR : F.1.degreeOf 2 ≤ (regularCumulativeFlag H F).all := by
    rw [regularCumulativeFlag, originalCumulativeFlag_all]
  have hFZ : F.1.degreeOf 3 ≤ total (regularCumulativeFlag H F) := by
    rw [regularCumulativeFlag, total, hc.2.2]
    exact degreeZ_le_totalWeight F.1
  by_cases hdiv : ∀ v : AKernel u0 u1,
      F.1 ∣ reconstruct K 17773574 131071 130000 29 v.1
  · exact False.elim
      (hFU ((mem_initialAUniversalFactors u0 u1 H F).2 hdiv))
  · push Not at hdiv
    obtain ⟨v, hv⟩ := hdiv
    let Q := reconstruct K 17773574 131071 130000 29 v.1
    have hF := RCN167.positiveRFactors_spec H F.1 F.2
    have hrel : IsRelPrime F.1 Q :=
      hF.1.isRelPrime_iff_not_dvd.mpr hv
    have hQbox : Q ∈ globalCoefficientBox K 17773574 131071 130000 29 :=
      reconstruct_mem_globalCoefficientBox K 17773574 131071 130000 29 v.1
    have hQYS : wt residualYSWeights Q ≤ 135 := by
      apply flag_box_ys_bound 17773574 131071 130000 29 135
        (by decide) (by decide) Q hQbox
    have hweights := (mem_flagGlobalCoefficientBox_iff Q
      17773574 131071 130000 29 (by decide)).mp hQbox
    have hQY : Q.degreeOf 1 ≤ 135 :=
      (degreeY_le_ysWeight Q).trans hQYS
    have hQR : Q.degreeOf 2 ≤ 29 :=
      (degreeR_le_sWeight Q).trans hweights.2.1
    have hQZ : Q.degreeOf 3 ≤ 130000 :=
      (degreeZ_le_totalWeight Q).trans hweights.1
    obtain ⟨hleftR, hleftYSmall, hleftRSmall, hleftZSmall,
      hmixedYSmall, hmixedRSmall, hmixedZSmall⟩ :=
        initialA_helper_gates (regularCumulativeFlag H F) hr hs hy ht
    change (regularSeeds H selected Gamma F).card ≤
      (LocatorGenericHelperFactorSwitch6803.helperPair
        130000 135 29 (middle (regularCumulativeFlag H F))
          (regularCumulativeFlag H F).all
          (total (regularCumulativeFlag H F))).regularCountCap
    apply regularSeeds_count_le_intersection
      (LocatorGenericHelperFactorSwitch6803.helperPair
        130000 135 29 (middle (regularCumulativeFlag H F))
          (regularCumulativeFlag H F).all
          (total (regularCumulativeFlag H F)))
      H Q F hrel 2130706433 hFY hFR hFZ hQY hQR hQZ
      hleftR hleftYSmall hleftRSmall hleftZSmall
      hmixedYSmall hmixedRSmall hmixedZSmall
      selected Gamma (Finset.univ : Finset I) IRSProfile.domain u0 u1
      IRSProfile.domain.injective.injOn
      (by
        change (Finset.univ : Finset I).card = 262144
        rw [Finset.card_univ]
        norm_num [I, IRSProfile.Index])
      (by norm_num [LocatorGenericHelperFactorSwitch6803.helperPair])
      (by norm_num [LocatorGenericHelperFactorSwitch6803.helperPair])
      (by norm_num [LocatorGenericHelperFactorSwitch6803.helperPair])
      (by norm_num [LocatorGenericHelperFactorSwitch6803.helperPair])
      (by simpa only [LocatorGenericHelperFactorSwitch6803.helperPair] using hdegree)
      (by simpa only [LocatorGenericHelperFactorSwitch6803.helperPair] using hagreement)
      (by
        simpa only [LocatorGenericHelperFactorSwitch6803.helperPair,
          UnequalParameters.errors, Nat.reduceSub] using hno)
    intro gamma hgamma
    dsimp only [Q]
    apply RCN101.specialization_eq_zero_of_mem_ker K
      17773574 131071 130000 29 98 IRSProfile.domain u0 u1
      v.1 v.2 (selected gamma) gamma
      ((Finset.univ : Finset I).filter fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)
    · decide
    · exact hdegree gamma (Finset.mem_filter.mp hgamma).1
    · have ha := hagreement gamma (Finset.mem_filter.mp hgamma).1
      omega
    · intro i hi
      exact (Finset.mem_filter.mp hi).2

end

end ProximityPrize.SubmissionLower.LocatorFixedBridge6803
