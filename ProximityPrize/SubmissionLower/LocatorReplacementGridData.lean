import ProximityPrize.SubmissionLower.LocatorReplacementGridRow00
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow01
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow02
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow03
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow04
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow05
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow06
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow07
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow08
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow09
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow10
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow11
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow12
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow13
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow14
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow15
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow16
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow17
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow18
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow19
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow20
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow21

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

private theorem receipt_rows (ri : Fin slopeRows) : RowReceipt ri := by
  fin_cases ri
  · exact receipt_row_00
  · exact receipt_row_01
  · exact receipt_row_02
  · exact receipt_row_03
  · exact receipt_row_04
  · exact receipt_row_05
  · exact receipt_row_06
  · exact receipt_row_07
  · exact receipt_row_08
  · exact receipt_row_09
  · exact receipt_row_10
  · exact receipt_row_11
  · exact receipt_row_12
  · exact receipt_row_13
  · exact receipt_row_14
  · exact receipt_row_15
  · exact receipt_row_16
  · exact receipt_row_17
  · exact receipt_row_18
  · exact receipt_row_19
  · exact receipt_row_20
  · exact receipt_row_21

theorem receipt_unit (c : UnitCell) (hv : (unitBox c).valid) : Fits (unitBox c) := by
  let f := c.parent.1
  let coarse := f.parent.1
  have hhardCoarse : HardCoarse coarse := f.parent.2
  have hhardFine : (fineBoxAt coarse f.yi f.ti).valid ∧
      ¬ Fits (fineBoxAt coarse f.yi f.ti) := by
    simpa only [HardFine, fineBox_eq_fineBoxAt, f, coarse] using c.parent.2
  have hv' : (unitBoxAt coarse f.yi f.ti c.ti).valid := by
    simpa only [unitBox_eq_unitBoxAt, f, coarse] using hv
  have h := receipt_rows coarse.1 coarse.2.1 coarse.2.2 hhardCoarse
    f.yi f.ti hhardFine c.ti hv'
  simpa only [unitBox_eq_unitBoxAt, f, coarse] using h

theorem receipt (c : Cell) : Valid c → Fits (box c) := by
  intro hv
  rcases c with c | c
  · simp only [Valid, box, Leaf] at hv ⊢
    by_contra hfit
    exact hv.2 ⟨hv.1, hfit⟩
  · rcases c with c | c
    · simp only [Valid, box, Leaf] at hv ⊢
      by_contra hfit
      exact hv.2 ⟨hv.1, hfit⟩
    · exact receipt_unit c hv.1

/-- The cost the receipt certifies for a leaf: the ordinary bound when it fits,
otherwise the first fitting arm, each a divisor-or-helper count
`max (route, direct pair)` of one route source. -/
def chosenCost (c : Cell) : ℕ :=
  let b := box c
  if b.ordinaryFits then b.ordinaryCost
  else if AFits b then
    max (routeCost sourceA b 1) (helperPair sourceA b).regularCountCap
  else if AuxFits b then
    max (routeCost sourceAux b 1) (helperPair sourceAux b).regularCountCap
  else if CHFits b then
    max (routeCost sourceC b (routeDepth sourceC b)) (helperPair sourceC b).regularCountCap
  else if S2Fits b then
    max (routeCost sourceS2 b (helperDepthS2 b)) (helperPair sourceS2 b).regularCountCap
  else if S3Fits b then
    max (routeCost sourceS3 b (helperDepthS3 b)) (helperPair sourceS3 b).regularCountCap
  else if H3XFits b then
    max (routeCost sourceH3X b (helperDepthH3X b)) (helperPair sourceH3X b).regularCountCap
  else if H4Fits b then
    max (routeCost sourceH4 b (helperDepthH4 b)) (helperPair sourceH4 b).regularCountCap
  else if T10kFits b then
    max (routeCost sourceT10k b (helperDepthT10k b)) (helperPair sourceT10k b).regularCountCap
  else if T15kFits b then
    max (routeCost sourceT15k b (helperDepthT15k b)) (helperPair sourceT15k b).regularCountCap
  else if T20kFits b then
    max (routeCost sourceT20k b (helperDepthT20k b)) (helperPair sourceT20k b).regularCountCap
  else if T30kFits b then
    max (routeCost sourceT30k b (helperDepthT30k b)) (helperPair sourceT30k b).regularCountCap
  else if L1Fits b then
    max (routeCost sourceL1 b (helperDepthL1 b)) (helperPair sourceL1 b).regularCountCap
  else if L2Fits b then
    max (routeCost sourceL2 b (helperDepthL2 b)) (helperPair sourceL2 b).regularCountCap
  else if L3Fits b then
    max (routeCost sourceL3 b (helperDepthL3 b)) (helperPair sourceL3 b).regularCountCap
  else if L4Fits b then
    max (routeCost sourceL4 b (helperDepthL4 b)) (helperPair sourceL4 b).regularCountCap
  else if L5Fits b then
    max (routeCost sourceL5 b (helperDepthL5 b)) (helperPair sourceL5 b).regularCountCap
  else if L6Fits b then
    max (routeCost sourceL6 b (helperDepthL6 b)) (helperPair sourceL6 b).regularCountCap
  else if M1Fits b then
    max (routeCost sourceM1 b (helperDepthM1 b)) (helperPair sourceM1 b).regularCountCap
  else if M3Fits b then
    max (routeCost sourceM3 b (helperDepthM3 b)) (helperPair sourceM3 b).regularCountCap
  else if N1Fits b then
    max (routeCost sourceN1 b (helperDepthN1 b)) (helperPair sourceN1 b).regularCountCap
  else if N3Fits b then
    max (routeCost sourceN3 b (helperDepthN3 b)) (helperPair sourceN3 b).regularCountCap
  else
    max (routeCost sourceN4 b (helperDepthN4 b)) (helperPair sourceN4 b).regularCountCap

theorem chosenCost_rate (c : Cell) (hv : Valid c) :
    capSum * chosenCost c ≤ bound * (box c).weight := by
  have h := receipt c hv
  simp only [Fits] at h
  by_cases ho : (box c).ordinaryFits
  · rw [chosenCost, if_pos ho]
    exact ho
  have hroutes := h.resolve_left ho
  by_cases hA : AFits (box c)
  · simpa only [chosenCost, ho, hA, if_pos, if_false] using hA.2.2
  have hroutes := hroutes.resolve_left hA
  by_cases hAux : AuxFits (box c)
  · simpa only [chosenCost, ho, hA, hAux, if_pos, if_false] using hAux.2.2
  have hroutes := hroutes.resolve_left hAux
  by_cases hC : CHFits (box c)
  · simpa only [chosenCost, ho, hA, hAux, hC, if_pos, if_false] using hC.2.2.2
  have hroutes := hroutes.resolve_left hC
  by_cases hS2 : S2Fits (box c)
  · simpa only [chosenCost, ho, hA, hAux, hC, hS2, if_pos, if_false] using (helperDepthS2_spec (box c) hS2).2.2
  have hroutes := hroutes.resolve_left hS2
  by_cases hS3 : S3Fits (box c)
  · simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, if_pos, if_false] using (helperDepthS3_spec (box c) hS3).2.2
  have hroutes := hroutes.resolve_left hS3
  by_cases hH3X : H3XFits (box c)
  · simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, if_pos, if_false] using (helperDepthH3X_spec (box c) hH3X).2.2
  have hroutes := hroutes.resolve_left hH3X
  by_cases hH4 : H4Fits (box c)
  · simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, if_pos, if_false] using (helperDepthH4_spec (box c) hH4).2.2
  have hroutes := hroutes.resolve_left hH4
  by_cases hT10k : T10kFits (box c)
  · simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, if_pos, if_false] using (helperDepthT10k_spec (box c) hT10k).2.2
  have hroutes := hroutes.resolve_left hT10k
  by_cases hT15k : T15kFits (box c)
  · simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, hT15k, if_pos, if_false] using (helperDepthT15k_spec (box c) hT15k).2.2
  have hroutes := hroutes.resolve_left hT15k
  by_cases hT20k : T20kFits (box c)
  · simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, hT15k, hT20k, if_pos, if_false] using (helperDepthT20k_spec (box c) hT20k).2.2
  have hroutes := hroutes.resolve_left hT20k
  by_cases hT30k : T30kFits (box c)
  · simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, hT15k, hT20k, hT30k, if_pos, if_false] using (helperDepthT30k_spec (box c) hT30k).2.2
  have hroutes := hroutes.resolve_left hT30k
  by_cases hL1 : L1Fits (box c)
  · simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, hT15k, hT20k, hT30k, hL1, if_pos, if_false] using (helperDepthL1_spec (box c) hL1).2.2
  have hroutes := hroutes.resolve_left hL1
  by_cases hL2 : L2Fits (box c)
  · simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, hT15k, hT20k, hT30k, hL1, hL2, if_pos, if_false] using (helperDepthL2_spec (box c) hL2).2.2
  have hroutes := hroutes.resolve_left hL2
  by_cases hL3 : L3Fits (box c)
  · simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, hT15k, hT20k, hT30k, hL1, hL2, hL3, if_pos, if_false] using (helperDepthL3_spec (box c) hL3).2.2
  have hroutes := hroutes.resolve_left hL3
  by_cases hL4 : L4Fits (box c)
  · simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, hT15k, hT20k, hT30k, hL1, hL2, hL3, hL4, if_pos, if_false] using (helperDepthL4_spec (box c) hL4).2.2
  have hroutes := hroutes.resolve_left hL4
  by_cases hL5 : L5Fits (box c)
  · simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, hT15k, hT20k, hT30k, hL1, hL2, hL3, hL4, hL5, if_pos, if_false] using (helperDepthL5_spec (box c) hL5).2.2
  have hroutes := hroutes.resolve_left hL5
  by_cases hL6 : L6Fits (box c)
  · simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, hT15k, hT20k, hT30k, hL1, hL2, hL3, hL4, hL5, hL6, if_pos, if_false] using (helperDepthL6_spec (box c) hL6).2.2
  have hroutes := hroutes.resolve_left hL6
  by_cases hM1 : M1Fits (box c)
  · simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, hT15k, hT20k, hT30k, hL1, hL2, hL3, hL4, hL5, hL6, hM1, if_pos, if_false] using (helperDepthM1_spec (box c) hM1).2.2
  have hroutes := hroutes.resolve_left hM1
  by_cases hM3 : M3Fits (box c)
  · simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, hT15k, hT20k, hT30k, hL1, hL2, hL3, hL4, hL5, hL6, hM1, hM3, if_pos, if_false] using (helperDepthM3_spec (box c) hM3).2.2
  have hroutes := hroutes.resolve_left hM3
  by_cases hN1 : N1Fits (box c)
  · simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, hT15k, hT20k, hT30k, hL1, hL2, hL3, hL4, hL5, hL6, hM1, hM3, hN1, if_pos, if_false] using (helperDepthN1_spec (box c) hN1).2.2
  have hroutes := hroutes.resolve_left hN1
  by_cases hN3 : N3Fits (box c)
  · simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, hT15k, hT20k, hT30k, hL1, hL2, hL3, hL4, hL5, hL6, hM1, hM3, hN1, hN3, if_pos, if_false] using (helperDepthN3_spec (box c) hN3).2.2
  have hroutes := hroutes.resolve_left hN3
  have hN4 : N4Fits (box c) := hroutes
  simpa only [chosenCost, ho, hA, hAux, hC, hS2, hS3, hH3X, hH4, hT10k, hT15k, hT20k, hT30k, hL1, hL2, hL3, hL4, hL5, hL6, hM1, hM3, hN1, hN3, if_pos, if_false] using (helperDepthN4_spec (box c) hN4).2.2

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
