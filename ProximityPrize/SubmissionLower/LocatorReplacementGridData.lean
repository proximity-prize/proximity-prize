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

/-- Every valid leaf has either the direct ordinary rate or a conservative
    source replacement rate.  Width-one terminal leaves are discharged by
    the row receipts; coarse and fine failures are refined definitionally. -/
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
  else if H1Fits b then
    max (routeCost sourceH1 b (helperDepthH1 b)) (helperPair sourceH1 b).regularCountCap
  else if H2Fits b then
    max (routeCost sourceH2 b (helperDepthH2 b)) (helperPair sourceH2 b).regularCountCap
  else if H3Fits b then
    max (routeCost sourceH3 b (helperDepthH3 b)) (helperPair sourceH3 b).regularCountCap
  else if CbigFits b then
    max (routeCost sourceCbig b (helperDepthCbig b)) (helperPair sourceCbig b).regularCountCap
  else if H3XFits b then
    max (routeCost sourceH3X b (helperDepthH3X b)) (helperPair sourceH3X b).regularCountCap
  else if T20kFits b then
    max (routeCost sourceT20k b (helperDepthT20k b)) (helperPair sourceT20k b).regularCountCap
  else
    max (routeCost sourceT30k b (helperDepthT30k b)) (helperPair sourceT30k b).regularCountCap

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
  by_cases hH1 : H1Fits (box c)
  · simpa only [chosenCost, ho, hA, hAux, hC, hH1, if_pos, if_false] using (helperDepthH1_spec (box c) hH1).2.2
  have hroutes := hroutes.resolve_left hH1
  by_cases hH2 : H2Fits (box c)
  · simpa only [chosenCost, ho, hA, hAux, hC, hH1, hH2, if_pos, if_false] using (helperDepthH2_spec (box c) hH2).2.2
  have hroutes := hroutes.resolve_left hH2
  by_cases hH3 : H3Fits (box c)
  · simpa only [chosenCost, ho, hA, hAux, hC, hH1, hH2, hH3, if_pos, if_false] using (helperDepthH3_spec (box c) hH3).2.2
  have hroutes := hroutes.resolve_left hH3
  by_cases hCb : CbigFits (box c)
  · simpa only [chosenCost, ho, hA, hAux, hC, hH1, hH2, hH3, hCb, if_pos, if_false] using (helperDepthCbig_spec (box c) hCb).2.2
  have hroutes := hroutes.resolve_left hCb
  by_cases hX : H3XFits (box c)
  · simpa only [chosenCost, ho, hA, hAux, hC, hH1, hH2, hH3, hCb, hX, if_pos, if_false] using (helperDepthH3X_spec (box c) hX).2.2
  have hroutes := hroutes.resolve_left hX
  by_cases hT2 : T20kFits (box c)
  · simpa only [chosenCost, ho, hA, hAux, hC, hH1, hH2, hH3, hCb, hX, hT2, if_pos, if_false] using (helperDepthT20k_spec (box c) hT2).2.2
  have hroutes := hroutes.resolve_left hT2
  have hT3 : T30kFits (box c) := hroutes
  simpa only [chosenCost, ho, hA, hAux, hC, hH1, hH2, hH3, hCb, hX, hT2, if_pos, if_false] using (helperDepthT30k_spec (box c) hT3).2.2

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
