import ProximityPrize.SubmissionLower.LocatorReplacementGridData
import ProximityPrize.SubmissionLower.LocatorGenericSourceRoutes6783

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
    (hagreement : ∀ gamma ∈ Gamma, 181559 ≤
      ((Finset.univ : Finset I).filter (fun i ↦
        (selected gamma).eval (IRSProfile.domain i) =
          u0 i + gamma * u1 i)).card)
    (hno : NoLargeSelectedPencil selected Gamma 131071 80585)
    (F : RegularIndex H) (hF : F.1 ≠ 0)
    (hdivA : ∀ v : LocatorGenericSourceCountEngine.SourceKernel
        12709130 130000 21 70 u0 u1,
      F.1 ∣ reconstruct K 12709130 131071 130000 21 v.1)
    (hdivAux : ∀ v : LocatorGenericSourceCountEngine.SourceKernel
        13072248 130000 21 72 u0 u1,
      F.1 ∣ reconstruct K 13072248 131071 130000 21 v.1)
    (hdivC : ∀ v : LocatorGenericSourceCountEngine.SourceKernel
        51744315 130000 85 285 u0 u1,
      F.1 ∣ reconstruct K 51744315 131071 130000 85 v.1)
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
  · have h := LocatorGenericSourceRoutes6783.sourceA_count
      u0 u1 H selected Gamma hdegree hagreement hno F hF hdivA c hcell hA
    simpa only [chosenCost, ho, hA, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hA
  by_cases hAux : RouteFits sourceAux 1 (box c)
  · have h := LocatorGenericSourceRoutes6783.sourceAux_count
      u0 u1 H selected Gamma hdegree hagreement hno F hF hdivAux c hcell hAux
    simpa only [chosenCost, ho, hA, hAux, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hAux
  by_cases hC2 : RouteFits sourceC 2 (box c)
  · have h := LocatorGenericSourceRoutes6783.sourceC_count 2 (by decide)
      u0 u1 H selected Gamma hdegree hagreement hno F hF hdivC c hcell hC2
    simpa only [chosenCost, ho, hA, hAux, hC2, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hC2
  by_cases hC3 : RouteFits sourceC 3 (box c)
  · have h := LocatorGenericSourceRoutes6783.sourceC_count 3 (by decide)
      u0 u1 H selected Gamma hdegree hagreement hno F hF hdivC c hcell hC3
    simpa only [chosenCost, ho, hA, hAux, hC2, hC3,
      if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hC3
  by_cases hC4 : RouteFits sourceC 4 (box c)
  · have h := LocatorGenericSourceRoutes6783.sourceC_count 4 (by decide)
      u0 u1 H selected Gamma hdegree hagreement hno F hF hdivC c hcell hC4
    simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4,
      if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hC4
  by_cases hC5 : RouteFits sourceC 5 (box c)
  · have h := LocatorGenericSourceRoutes6783.sourceC_count 5 (by decide)
      u0 u1 H selected Gamma hdegree hagreement hno F hF hdivC c hcell hC5
    simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4, hC5,
      if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hC5
  by_cases hC6 : RouteFits sourceC 6 (box c)
  · have h := LocatorGenericSourceRoutes6783.sourceC_count 6 (by decide)
      u0 u1 H selected Gamma hdegree hagreement hno F hF hdivC c hcell hC6
    simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4, hC5, hC6,
      if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hC6
  by_cases hC7 : RouteFits sourceC 7 (box c)
  · have h := LocatorGenericSourceRoutes6783.sourceC_count 7 (by decide)
      u0 u1 H selected Gamma hdegree hagreement hno F hF hdivC c hcell hC7
    simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4, hC5, hC6, hC7,
      if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hC7
  by_cases hC8 : RouteFits sourceC 8 (box c)
  · have h := LocatorGenericSourceRoutes6783.sourceC_count 8 (by decide)
      u0 u1 H selected Gamma hdegree hagreement hno F hF hdivC c hcell hC8
    simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4, hC5, hC6, hC7,
      hC8, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hC8
  by_cases hC9 : RouteFits sourceC 9 (box c)
  · have h := LocatorGenericSourceRoutes6783.sourceC_count 9 (by decide)
      u0 u1 H selected Gamma hdegree hagreement hno F hF hdivC c hcell hC9
    simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4, hC5, hC6, hC7,
      hC8, hC9, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hC9
  by_cases hH10 : HelperFits sourceH1 10 (box c)
  · have h := LocatorGenericSourceCount6783.sourceH1_count 10 (by decide)
      u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hH10
    simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4, hC5, hC6, hC7,
      hC8, hC9, hH10, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hH10
  by_cases hH11 : HelperFits sourceH1 11 (box c)
  · have h := LocatorGenericSourceCount6783.sourceH1_count 11 (by decide)
      u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hH11
    simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4, hC5, hC6, hC7,
      hC8, hC9, hH10, hH11, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hH11
  by_cases hH12 : HelperFits sourceH1 12 (box c)
  · have h := LocatorGenericSourceCount6783.sourceH1_count 12 (by decide)
      u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hH12
    simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4, hC5, hC6, hC7,
      hC8, hC9, hH10, hH11, hH12, if_pos, if_false] using h
  have hroutes := hroutes.resolve_left hH12
  by_cases hH13 : HelperFits sourceH1 13 (box c)
  · have h := LocatorGenericSourceCount6783.sourceH1_count 13 (by decide)
      u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hH13
    simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4, hC5, hC6, hC7,
      hC8, hC9, hH10, hH11, hH12, hH13, if_pos, if_false] using h
  have hH18 := hroutes.resolve_left hH13
  have h := LocatorGenericSourceCount6783.sourceH2_count
    u0 u1 H selected Gamma hdegree hagreement hno F hF c hcell hH18
  simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4, hC5, hC6, hC7,
    hC8, hC9, hH10, hH11, hH12, hH13, if_pos, if_false] using h

end

end ProximityPrize.SubmissionLower.LocatorQuotientReplacement
