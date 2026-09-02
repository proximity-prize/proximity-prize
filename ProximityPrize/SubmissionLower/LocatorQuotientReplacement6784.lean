import ProximityPrize.SubmissionLower.LocatorReplacementGridData
import ProximityPrize.SubmissionLower.LocatorGenericSourceRoutes6784

namespace ProximityPrize.SubmissionLower.LocatorQuotientReplacement

open ProximityPrize.Benchmark
open RCN100 RCN130 RCN140 RCN180 RCN238 RCN260 RCN266
open LocatorFactorAggregate LocatorReplacementGridData

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

abbrev K := IRSProfile.Field
abbrev I := IRSProfile.Index
abbrev P4 := MvPolynomial (Fin 4) K

local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq I := Classical.decEq I

private theorem ordinary_count
    (H : P4) (selected : K → Polynomial K) (Gamma : Finset K)
    (F : RegularIndex H) (c : Cell)
    (hcell : InCell (regularCumulativeFlag H F) c) (hv : Valid c)
    (hown : LocatorHybridCost.OwnBound (regularSeeds H selected Gamma F).card
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
  unfold Box.ordinaryCost
  split_ifs with hhyb
  · have happ : LocatorHybridCost.HybridApplies
        (regularCumulativeFlag H F) := by
      refine ⟨?_, ?_⟩
      · rw [hcell.all_eq]
        exact hhyb.1
      · have h1 := hcell.all_eq
        have h2 := hcell.ylo_le
        omega
    exact (hown.2 happ).trans (LocatorHybridCost.hybridCost_mono hbelow)
  · exact hown.1.trans (paddedCost_mono 131072 131073 hbelow)

theorem regularSeeds_count_le_chosen
    (u0 u1 : I → K) (H : P4) (selected : K → Polynomial K)
    (Gamma : Finset K)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ 131071)
    (hagreement : ∀ gamma ∈ Gamma, 181540 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) = u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80604)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (hdivA : ∀ v : LocatorGenericSourceCountEngine.SourceKernel
        13070880 130000 21 72 u0 u1,
      F.1 ∣ reconstruct K 13070880 131071 130000 21 v.1)
    (hdivAux : ∀ v : LocatorGenericSourceCountEngine.SourceKernel
        13252420 130000 22 73 u0 u1,
      F.1 ∣ reconstruct K 13252420 131071 130000 22 v.1)
    (hdivC : ∀ v : LocatorGenericSourceCountEngine.SourceKernel
        51738900 130000 85 285 u0 u1,
      F.1 ∣ reconstruct K 51738900 131071 130000 85 v.1)
    (c : Cell) (hcell : InCell (regularCumulativeFlag H F) c)
    (hv : Valid c)
    (hown : LocatorHybridCost.OwnBound (regularSeeds H selected Gamma F).card
      (regularCumulativeFlag H F)) :
    (regularSeeds H selected Gamma F).card ≤ chosenCost c := by
  classical
  by_cases ho : (box c).ordinaryFits
  · have h := ordinary_count H selected Gamma F c hcell hv hown
    simpa only [chosenCost, ho, if_pos] using h
  have hroutes := (receipt c hv).resolve_left ho
  by_cases hA : RouteFits sourceA 1 (box c)
  · have h := LocatorGenericSourceRoutes6784.sourceA_count
      u0 u1 H selected Gamma hdegree hagreement hno F hF hdivA c hcell hA
    simpa only [chosenCost, ho, hA, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hA
  by_cases hAux : RouteFits sourceAux 1 (box c)
  · have h := LocatorGenericSourceRoutes6784.sourceAux_count
      u0 u1 H selected Gamma hdegree hagreement hno F hF hdivAux c hcell hAux
    simpa only [chosenCost, ho, hA, hAux, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hAux
  by_cases hC : CFits (box c)
  · have hfit := routeDepth_spec sourceC (box c) hC
    have hk := LocatorGenericSourceRoutes6784.routeDepth_le_fourteen
      sourceC (box c) hC
    have h := LocatorGenericSourceRoutes6784.sourceC_count
      (routeDepth sourceC (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF hdivC c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hC
  by_cases hH1 : H1Fits (box c)
  · have hfit := helperDepthH1_spec (box c) hH1
    have hk := (helperDepthH1_bounds (box c) hH1).2
    have h := LocatorGenericSourceCount6784.sourceH1_count
      (helperDepthH1 (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hH1,
      if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hH1
  by_cases hH2 : H2Fits (box c)
  · have hfit := helperDepthH2_spec (box c) hH2
    have hk := (helperDepthH2_bounds (box c) hH2).2
    have h := LocatorGenericSourceCount6784.sourceH2_count
      (helperDepthH2 (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hH1, hH2,
      if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hH2
  by_cases hH3 : H3Fits (box c)
  · have hfit := helperDepthH3_spec (box c) hH3
    have hk := (helperDepthH3_bounds (box c) hH3).2
    have h := LocatorGenericSourceCount6784.sourceH3_count
      (helperDepthH3 (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hH1, hH2, hH3,
      if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hH3
  by_cases hH4 : H4Fits (box c)
  · have hfit := helperDepthH4_spec (box c) hH4
    have hk := (helperDepthH4_bounds (box c) hH4).2
    have h := LocatorGenericSourceCount6784.sourceH4_count
      (helperDepthH4 (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hH1, hH2, hH3, hH4,
      if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hH4
  by_cases hH5 : H5Fits (box c)
  · have hfit := helperDepthH5_spec (box c) hH5
    have hk : helperDepthH5 (box c) ≤ 28 := by
      rw [helperDepthH5_bounds (box c) hH5]
    have h := LocatorGenericSourceCount6784.sourceH5_count
      (helperDepthH5 (box c)) hk u0 u1 H selected Gamma hdegree
      hagreement hno F hF c hcell hfit
    simpa only [chosenCost, ho, hA, hAux, hC, hH1, hH2, hH3, hH4, hH5,
      if_pos, if_false] using h
  have hH6 := hroutes.resolve_left hH5
  have hfit := helperDepthH6_spec (box c) hH6
  have hk := (helperDepthH6_bounds (box c) hH6).2
  have h := LocatorGenericSourceCount6784.sourceH6_count
    (helperDepthH6 (box c)) hk u0 u1 H selected Gamma hdegree
    hagreement hno F hF c hcell hfit
  simpa only [chosenCost, ho, hA, hAux, hC, hH1, hH2, hH3, hH4, hH5,
    if_pos, if_false] using h

end

end ProximityPrize.SubmissionLower.LocatorQuotientReplacement
