import ProximityPrize.SubmissionLower.LocatorLowQuotient
import ProximityPrize.SubmissionLower.LocatorReplacementData
import ProximityPrize.SubmissionLower.LocatorEquation

/-! A receipt bounds the regular seeds of one actual factor.  On an ordinary
cell its own-support bound suffices.  On a replacement cell a single nonzero
quotient is selected from the whole A68/2820 contact kernel; all regular seeds
of the original factor satisfy that same quotient equation. -/
namespace ProximityPrize.SubmissionLower.LocatorQuotientReplacement

open ProximityPrize.Benchmark
open RCN081 RCN100 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238 RCN266
open LocatorFactorAggregate LocatorLowQuotient

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 600000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

theorem factor_weights_of_cell (H : P4) (F : RegularIndex H)
    (c : LocatorReplacementGrid.Cell)
    (hcell : LocatorReplacementGrid.InCell (regularCumulativeFlag H F) c) :
    wt residualSWeights F.1 = LocatorReplacementGrid.r c ∧
      LocatorReplacementGrid.ylo c ≤ wt residualYSWeights F.1 ∧
      LocatorReplacementGrid.tlo c ≤ wt residualTotalWeights F.1 ∧
      131071 * LocatorReplacementGrid.ylo c - LocatorReplacementGrid.r c ≤
        wt (contactWeights 131071) F.1 := by
  have hc := originalCumulativeFlag_cumulative F.1
  have hr : wt residualSWeights F.1 = LocatorReplacementGrid.r c := by
    simpa only [regularCumulativeFlag, hc.1] using hcell.all_eq
  have hy : LocatorReplacementGrid.ylo c ≤ wt residualYSWeights F.1 := by
    simpa only [middle, regularCumulativeFlag, hc.2.1] using hcell.ylo_le
  have ht : LocatorReplacementGrid.tlo c ≤ wt residualTotalWeights F.1 := by
    simpa only [total, regularCumulativeFlag, hc.2.2] using hcell.tlo_le
  refine ⟨hr, hy, ht, ?_⟩
  have hmul := Nat.mul_le_mul_left 131071 hy
  have hweight := residualYS_mul_le_contact_add_slope F.1 131071 (by decide)
  rw [hr] at hweight
  omega

theorem regularSeeds_count_le_chosen
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181845 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80299)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (hdiv : ∀ v : ConstraintKernel (K := K) 13456530 131071 2820 22 74
      IRSProfile.domain u0 u1,
      F.1 ∣ reconstruct K 13456530 131071 2820 22 v.1)
    (c : LocatorReplacementGrid.Cell)
    (hcell : LocatorReplacementGrid.InCell (regularCumulativeFlag H F) c)
    (hown : (regularSeeds H selected Gamma F).card ≤
      paddedCost 131072 131073 (regularCumulativeFlag H F)) :
    (regularSeeds H selected Gamma F).card ≤ LocatorReplacementData.chosenCost c := by
  classical
  by_cases ho : LocatorReplacementData.OrdinaryFits c
  · simpa only [LocatorReplacementData.chosenCost, if_pos ho] using
      LocatorReplacementGrid.count_le_ordinaryCost (regularCumulativeFlag H F) c
        (regularSeeds H selected Gamma F).card hcell hown
  have hvalid := LocatorReplacementGrid.valid_of_inCell
    (regularCumulativeFlag H F) c hcell
  obtain ⟨hr, hy, ht, hc⟩ := factor_weights_of_cell H F c hcell
  have hqT : 2820 - wt residualTotalWeights F.1 ≤
      LocatorReplacementData.quotientT c := by
    dsimp [LocatorReplacementData.quotientT]
    omega
  have hqY : 102 - wt residualYSWeights F.1 ≤
      LocatorReplacementData.quotientYS c := by
    dsimp [LocatorReplacementData.quotientYS]
    omega
  have hqS : 22 - wt residualSWeights F.1 ≤
      LocatorReplacementData.quotientS c := by
    dsimp [LocatorReplacementData.quotientS]
    omega
  have hqD : 13456530 - 50775 - wt (contactWeights 131071) F.1 ≤
      LocatorReplacementData.quotientD c := by
    dsimp [LocatorReplacementData.quotientD]
    omega
  have hchannels := channelCount_mono hqT hqY hqS
  have hband : 50775 * channelCount
      (LocatorReplacementData.quotientT c) (LocatorReplacementData.quotientYS c)
        (LocatorReplacementData.quotientS c) < 41375181758 :=
    LocatorReplacementData.band_lt c hvalid ho
  have hslab : 50775 * channelCount (2820 - wt residualTotalWeights F.1)
      (102 - wt residualYSWeights F.1) (22 - wt residualSWeights F.1) < 41375181758 :=
    (Nat.mul_le_mul_left 50775 hchannels).trans_lt hband
  have hsource : 50775 * channelCount (2820 - wt residualTotalWeights F.1)
      (102 - wt residualYSWeights F.1) (22 - wt residualSWeights F.1) <
      coefficientCount 13456530 131071 2820 22 -
        Fintype.card I * localRankBound 74 2820 22 := by
    rw [show Fintype.card I = 262144 by norm_num [I, IRSProfile.Index],
      LocatorAuxiliaryArithmetic.auxiliary_nullity]
    exact hslab
  obtain ⟨v, Q, _hv, hQ, _heq, hqbox, _hparent, hproduct⟩ :=
    exists_fixed_quotient_with_derivative_vanishing (K := K) (I := I)
      13456530 131071 2820 22 74 102 50775 181845 IRSProfile.domain u0 u1 F.1 hF hdiv
      (by decide) LocatorAuxiliaryArithmetic.auxiliary_shape hsource
      LocatorAuxiliaryArithmetic.auxiliary_capacity selected Gamma hdegree hagreement
  have hbox : Q ∈ nestedCoefficientBox K (LocatorReplacementData.quotientD c) 131071
      (LocatorReplacementData.quotientT c) (LocatorReplacementData.quotientYS c)
        (LocatorReplacementData.quotientS c) :=
    nestedCoefficientBox_mono hqD hqT hqY hqS hqbox
  have hordinary : Q ∈ RCN174.globalCoefficientBox K
      (LocatorReplacementData.quotientD c) 131071
      (LocatorReplacementData.quotientT c) (LocatorReplacementData.quotientS c) :=
    RCN101.flag_box_to_ordinary K (LocatorReplacementData.quotientD c) 131071
      (LocatorReplacementData.quotientT c) (LocatorReplacementData.quotientS c)
      Q (nested_mem_global hbox)
  have hweights := nested_mem_weights hbox hQ
  obtain ⟨hDlow, hDhigh, hSpos, hSY, hYT, hYpos, hSmax, hYmax, hTmax⟩ :=
    LocatorReplacementData.quotient_caps c hvalid
  have hcount := LocatorEquation.regularSeeds_count_le_equation
    (LocatorReplacementData.quotientD c) (LocatorReplacementData.quotientT c)
    (LocatorReplacementData.quotientYS c) (LocatorReplacementData.quotientS c)
    hDlow hDhigh hSpos hSY hYT hYpos hSmax hYmax hTmax H Q hQ hordinary
    ⟨hweights.2.2.1, hweights.2.1, hweights.1⟩
    selected Gamma u0 u1 hdegree hagreement hno F
    (fun gamma hgamma => hproduct gamma (regularSeeds_subset H selected Gamma F hgamma))
  simpa only [LocatorReplacementData.chosenCost, if_neg ho,
    LocatorReplacementData.quotientCost, LocatorEquation.equationCost] using hcount

end
end ProximityPrize.SubmissionLower.LocatorQuotientReplacement
