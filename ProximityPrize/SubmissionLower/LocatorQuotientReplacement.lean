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
    (hagreement : ∀ gamma ∈ Gamma, 181520 ≤
      ((Finset.univ : Finset I).filter (fun i =>
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80624)
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
  by_cases hS2 : S2Fits (box c)
  · have hfit := helperDepthS2_spec (box c) hS2
    have hk := (helperDepthS2_bounds (box c) hS2).2
    have h := LocatorGenericSourceCountC2.sourceS2_count
      (helperDepthS2 (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hS2, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hS2
  by_cases hS3 : S3Fits (box c)
  · have hfit := helperDepthS3_spec (box c) hS3
    have hk := (helperDepthS3_bounds (box c) hS3).2
    have h := LocatorGenericSourceCountC2.sourceS3_count
      (helperDepthS3 (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hS3
  by_cases hH3X : H3XFits (box c)
  · have hfit := helperDepthH3X_spec (box c) hH3X
    have hk := (helperDepthH3X_bounds (box c) hH3X).2
    have h := LocatorGenericSourceCountC2.sourceH3X_count
      (helperDepthH3X (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hH3X
  by_cases hH4 : H4Fits (box c)
  · have hfit := helperDepthH4_spec (box c) hH4
    have hk := (helperDepthH4_bounds (box c) hH4).2
    have h := LocatorGenericSourceCountC2.sourceH4_count
      (helperDepthH4 (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hH4
  by_cases hT10k : T10kFits (box c)
  · have hfit := helperDepthT10k_spec (box c) hT10k
    have hk := (helperDepthT10k_bounds (box c) hT10k).2
    have h := LocatorGenericSourceCountC2.sourceT10k_count
      (helperDepthT10k (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hT10k
  by_cases hT15k : T15kFits (box c)
  · have hfit := helperDepthT15k_spec (box c) hT15k
    have hk := (helperDepthT15k_bounds (box c) hT15k).2
    have h := LocatorGenericSourceCountC2.sourceT15k_count
      (helperDepthT15k (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, hT15k, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hT15k
  by_cases hT20k : T20kFits (box c)
  · have hfit := helperDepthT20k_spec (box c) hT20k
    have hk := (helperDepthT20k_bounds (box c) hT20k).2
    have h := LocatorGenericSourceCountC2.sourceT20k_count
      (helperDepthT20k (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, hT15k, hT20k, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hT20k
  by_cases hT30k : T30kFits (box c)
  · have hfit := helperDepthT30k_spec (box c) hT30k
    have hk := (helperDepthT30k_bounds (box c) hT30k).2
    have h := LocatorGenericSourceCountC2.sourceT30k_count
      (helperDepthT30k (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, hT15k, hT20k, hT30k, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hT30k
  by_cases hL1 : L1Fits (box c)
  · have hfit := helperDepthL1_spec (box c) hL1
    have hk := (helperDepthL1_bounds (box c) hL1).2
    have h := LocatorGenericSourceCountC2.sourceL1_count
      (helperDepthL1 (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, hT15k, hT20k, hT30k, hL1, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hL1
  by_cases hL2 : L2Fits (box c)
  · have hfit := helperDepthL2_spec (box c) hL2
    have hk := (helperDepthL2_bounds (box c) hL2).2
    have h := LocatorGenericSourceCountC2.sourceL2_count
      (helperDepthL2 (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, hT15k, hT20k, hT30k, hL1, hL2, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hL2
  by_cases hL3 : L3Fits (box c)
  · have hfit := helperDepthL3_spec (box c) hL3
    have hk := (helperDepthL3_bounds (box c) hL3).2
    have h := LocatorGenericSourceCountC2.sourceL3_count
      (helperDepthL3 (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, hT15k, hT20k, hT30k, hL1, hL2, hL3, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hL3
  by_cases hL4 : L4Fits (box c)
  · have hfit := helperDepthL4_spec (box c) hL4
    have hk := (helperDepthL4_bounds (box c) hL4).2
    have h := LocatorGenericSourceCountC2.sourceL4_count
      (helperDepthL4 (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, hT15k, hT20k, hT30k, hL1, hL2, hL3, hL4, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hL4
  by_cases hL5 : L5Fits (box c)
  · have hfit := helperDepthL5_spec (box c) hL5
    have hk := (helperDepthL5_bounds (box c) hL5).2
    have h := LocatorGenericSourceCountC2.sourceL5_count
      (helperDepthL5 (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, hT15k, hT20k, hT30k, hL1, hL2, hL3, hL4, hL5, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hL5
  by_cases hL6 : L6Fits (box c)
  · have hfit := helperDepthL6_spec (box c) hL6
    have hk := (helperDepthL6_bounds (box c) hL6).2
    have h := LocatorGenericSourceCountC2.sourceL6_count
      (helperDepthL6 (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, hT15k, hT20k, hT30k, hL1, hL2, hL3, hL4, hL5, hL6, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hL6
  by_cases hM1 : M1Fits (box c)
  · have hfit := helperDepthM1_spec (box c) hM1
    have hk := (helperDepthM1_bounds (box c) hM1).2
    have h := LocatorGenericSourceCountC2.sourceM1_count
      (helperDepthM1 (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, hT15k, hT20k, hT30k, hL1, hL2, hL3, hL4, hL5, hL6, hM1, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hM1
  by_cases hM3 : M3Fits (box c)
  · have hfit := helperDepthM3_spec (box c) hM3
    have hk := (helperDepthM3_bounds (box c) hM3).2
    have h := LocatorGenericSourceCountC2.sourceM3_count
      (helperDepthM3 (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, hT15k, hT20k, hT30k, hL1, hL2, hL3, hL4, hL5, hL6, hM1, hM3, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hM3
  by_cases hN1 : N1Fits (box c)
  · have hfit := helperDepthN1_spec (box c) hN1
    have hk := (helperDepthN1_bounds (box c) hN1).2
    have h := LocatorGenericSourceCountC2.sourceN1_count
      (helperDepthN1 (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, hT15k, hT20k, hT30k, hL1, hL2, hL3, hL4, hL5, hL6, hM1, hM3, hN1, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hN1
  by_cases hN3 : N3Fits (box c)
  · have hfit := helperDepthN3_spec (box c) hN3
    have hk := (helperDepthN3_bounds (box c) hN3).2
    have h := LocatorGenericSourceCountC2.sourceN3_count
      (helperDepthN3 (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, hT15k, hT20k, hT30k, hL1, hL2, hL3, hL4, hL5, hL6, hM1, hM3, hN1, hN3, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hN3
  have hN4 := hroutes
  have hfit := helperDepthN4_spec (box c) hN4
  have hk := (helperDepthN4_bounds (box c) hN4).2
  have h := LocatorGenericSourceCountC2.sourceN4_count
    (helperDepthN4 (box c)) hk u0 u1 H selected Gamma hdegree
    hagreement hno F hF c hcell hfit
  simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, hT15k, hT20k, hT30k, hL1, hL2, hL3, hL4, hL5, hL6, hM1, hM3, hN1, hN3, if_pos, if_false] using h

end

end LocatorQuotientReplacement
