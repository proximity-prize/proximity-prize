import ProximityPrize.SubmissionLower.LocatorReplacementGridData
import ProximityPrize.SubmissionLower.LocatorIteratedPowerAvoidance
import ProximityPrize.SubmissionLower.LocatorSixthPowerAvoidance
import ProximityPrize.SubmissionLower.LocatorHybridCost
import ProximityPrize.SubmissionLower.LocatorHybridCostC2
import ProximityPrize.SubmissionLower.LocatorQuotientMonotone
import ProximityPrize.SubmissionLower.LocatorGenericSourceCountC2
import ProximityPrize.SubmissionLower.BF

namespace ProximityPrize.SubmissionLower.LocatorQuotientReplacement

open ProximityPrize.Benchmark
open scoped BigOperators
open RCN081 RCN100 RCN119 RCN130 RCN140 RCN156 RCN180 RCN234 RCN238
  RCN260 RCN266
open LocatorFactorAggregate LocatorLowQuotient LocatorCoprimeQuotient
  LocatorReplacementGridData

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option Elab.async false

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I
local instance : CharP K 2130706433 := by
  simpa [RCN223.prime] using RCN128.challenge_field_characteristic6600

theorem degreeY_le_ysWeight (Q : P4) :
    Q.degreeOf (1 : Fin 4) ≤ wt residualYSWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualYSWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 0 ≤
    wt residualYSWeights Q at h
  omega

theorem degreeZ_le_totalWeight (Q : P4) :
    Q.degreeOf (3 : Fin 4) ≤ wt residualTotalWeights Q := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have h := MvPolynomial.le_weightedTotalDegree residualTotalWeights hd
  rw [weight_fin4] at h
  change d 0 * 0 + d 1 * 1 + d 2 * 1 + d 3 * 1 ≤
    wt residualTotalWeights Q at h
  omega

private theorem factor_bounds_of_cell (H : P4) (F : RegularIndex H)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c) :
    wt residualSWeights F.1 = (box c).r ∧
      (box c).ylo ≤ wt residualYSWeights F.1 ∧
      wt residualYSWeights F.1 ≤ (box c).factorY ∧
      (box c).factorT ≤ wt residualTotalWeights F.1 ∧
      wt residualTotalWeights F.1 ≤ (box c).thi := by
  have hc := originalCumulativeFlag_cumulative F.1
  have hr : wt residualSWeights F.1 = (box c).r := by
    simpa only [regularCumulativeFlag, hc.1] using hcell.all_eq
  have hylo : (box c).ylo ≤ wt residualYSWeights F.1 := by
    simpa only [middle, regularCumulativeFlag, hc.2.1] using hcell.ylo_le
  have hyhi : wt residualYSWeights F.1 ≤ (box c).yhi := by
    simpa only [middle, regularCumulativeFlag, hc.2.1] using
      hcell.middle_le_yhi
  have hyT : wt residualYSWeights F.1 ≤ (box c).thi := by
    simpa only [middle, total, regularCumulativeFlag, hc.2.1, hc.2.2] using
      (middle_le_total (regularCumulativeFlag H F)).trans hcell.total_le_thi
  have htlo : (box c).tlo ≤ wt residualTotalWeights F.1 := by
    simpa only [total, regularCumulativeFlag, hc.2.2] using hcell.tlo_le
  have hthi : wt residualTotalWeights F.1 ≤ (box c).thi := by
    simpa only [total, regularCumulativeFlag, hc.2.2] using hcell.total_le_thi
  have hysTotal : wt residualYSWeights F.1 ≤ wt residualTotalWeights F.1 := by
    simpa only [middle, total, regularCumulativeFlag, hc.2.1, hc.2.2] using
      middle_le_total (regularCumulativeFlag H F)
  exact ⟨hr, hylo, le_min hyhi hyT, max_le htlo (hylo.trans hysTotal), hthi⟩

private theorem ordinary_count
    (H : P4) (selected : K → Polynomial K) (Gamma : Finset K)
    (F : RegularIndex H) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c) (hv : Valid c)
    (hown : LocatorHybridCostC2.OwnBoundC2
      (regularSeeds H selected Gamma F).card
      (regularCumulativeFlag H F)) :
    (regularSeeds H selected Gamma F).card ≤ (box c).ordinaryCost := by
  have hb := hv.1
  have hcap := cap_cumulative (box c).thi (box c).factorY (box c).r
    (by
      apply le_min
      · exact hb.2.1.trans hb.2.2.1
      · exact hb.2.1.trans hb.2.2.2.2.1)
    (Nat.min_le_right _ _)
  have hbelow : Below (regularCumulativeFlag H F) (box c).ordinaryCap := by
    unfold Below Box.ordinaryCap
    rw [hcap.1, hcap.2.1, hcap.2.2]
    exact ⟨hcell.all_eq.le,
      le_min hcell.middle_le_yhi
        ((middle_le_total (regularCumulativeFlag H F)).trans hcell.total_le_thi),
      hcell.total_le_thi⟩
  have hpadded := hown.1.trans (paddedCost_mono 131072 131073 hbelow)
  unfold Box.ordinaryCost
  split_ifs with hhyb
  · have happ : LocatorHybridCostC2.HybridAppliesC2
        (regularCumulativeFlag H F) := by
      refine ⟨?_, ?_⟩
      · rw [hcell.all_eq]; exact hhyb.1
      · have h1 := hcell.all_eq
        have h2 := hcell.ylo_le
        omega
    exact le_min
      ((hown.2 happ).trans (LocatorHybridCostC2.hybridCostC2_mono hbelow))
      hpadded
  · exact hpadded


/-- Every valid leaf cell charges its factor at most `chosenCost`: the ordinary
(padded / C2 hybrid) bound when it fits, otherwise the arm the receipt chose,
each of which is a divisor-or-helper count of one route source. -/
theorem regularSeeds_count_le_chosen
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181530 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80614)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (hv : Valid c)
    (hown : LocatorHybridCostC2.OwnBoundC2
      (regularSeeds H selected Gamma F).card
      (regularCumulativeFlag H F)) :
    (regularSeeds H selected Gamma F).card ≤ chosenCost c := by
  classical
  by_cases ho : (box c).ordinaryFits
  · have h := ordinary_count H selected Gamma F c hcell hv hown
    simpa only [chosenCost, ho, if_pos] using h
  have hroutes := (receipt c hv).resolve_left ho
  by_cases hA : AFits (box c)
  · have h := LocatorGenericSourceCountC2.sourceA_count 1 le_rfl u0 u1 H selected
      Gamma hdegree hagreement hno F hF c hcell hA
    simpa only [chosenCost, ho, hA, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hA
  by_cases hAux : AuxFits (box c)
  · have h := LocatorGenericSourceCountC2.sourceAux_count 1 le_rfl u0 u1 H selected
      Gamma hdegree hagreement hno F hF c hcell hAux
    simpa only [chosenCost, ho, hA, hAux, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hAux
  by_cases hC : CHFits (box c)
  · have hk := routeDepth_le_routeCap sourceC (box c) hC.1
    have h := LocatorGenericSourceCountC2.sourceC_count (routeDepth sourceC (box c))
      hk u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hC.2
    simpa only [chosenCost, ho, hA, hAux, hC, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hC
  by_cases hH1 : H1Fits (box c)
  · have hfit := helperDepthH1_spec (box c) hH1
    have hk := (helperDepthH1_bounds (box c) hH1).2
    have h := LocatorGenericSourceCountC2.sourceH1_count
      (helperDepthH1 (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hH1, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hH1
  by_cases hH2 : H2Fits (box c)
  · have hfit := helperDepthH2_spec (box c) hH2
    have hk := (helperDepthH2_bounds (box c) hH2).2
    have h := LocatorGenericSourceCountC2.sourceH2_count
      (helperDepthH2 (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hH1, hH2, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hH2
  by_cases hH3 : H3Fits (box c)
  · have hfit := helperDepthH3_spec (box c) hH3
    have hk := (helperDepthH3_bounds (box c) hH3).2
    have h := LocatorGenericSourceCountC2.sourceH3_count
      (helperDepthH3 (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hH1, hH2, hH3, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hH3
  by_cases hCb : CbigFits (box c)
  · have hfit := helperDepthCbig_spec (box c) hCb
    have hk := (helperDepthCbig_bounds (box c) hCb).2
    have h := LocatorGenericSourceCountC2.sourceCbig_count
      (helperDepthCbig (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hH1, hH2, hH3, hCb, if_pos,
      if_false] using h
  have hroutes := hroutes.resolve_left hCb
  by_cases hX : H3XFits (box c)
  · have hfit := helperDepthH3X_spec (box c) hX
    have hk := (helperDepthH3X_bounds (box c) hX).2
    have h := LocatorGenericSourceCountC2.sourceH3X_count
      (helperDepthH3X (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hH1, hH2, hH3, hCb, hX, if_pos,
      if_false] using h
  have hroutes := hroutes.resolve_left hX
  by_cases hT2 : T20kFits (box c)
  · have hfit := helperDepthT20k_spec (box c) hT2
    have hk := (helperDepthT20k_bounds (box c) hT2).2
    have h := LocatorGenericSourceCountC2.sourceT20k_count
      (helperDepthT20k (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hH1, hH2, hH3, hCb, hX, hT2, if_pos,
      if_false] using h
  have hT3 := hroutes.resolve_left hT2
  have hfit := helperDepthT30k_spec (box c) hT3
  have hk := (helperDepthT30k_bounds (box c) hT3).2
  have h := LocatorGenericSourceCountC2.sourceT30k_count
    (helperDepthT30k (box c)) hk u0 u1 H selected Gamma hdegree
    hagreement hno F hF c hcell hfit
  simpa only [chosenCost, ho, hA, hAux, hC, hH1, hH2, hH3, hCb, hX, hT2, if_pos,
    if_false] using h

end

end LocatorQuotientReplacement
