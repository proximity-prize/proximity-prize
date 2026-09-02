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

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

private theorem receipt_rows (ri : Fin 20) : RowReceipt ri := by
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
    source replacement rate.  Width-eight terminal leaves are discharged by
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

def chosenCost (c : Cell) : ℕ :=
  let b := box c
  if b.ordinaryFits then b.ordinaryCost
  else if RouteFits sourceA 1 b then routeCost sourceA b 1
  else if RouteFits sourceAux 1 b then routeCost sourceAux b 1
  else if RouteFits sourceC 2 b then routeCost sourceC b 2
  else if RouteFits sourceC 3 b then routeCost sourceC b 3
  else if RouteFits sourceC 4 b then routeCost sourceC b 4
  else if RouteFits sourceC 5 b then routeCost sourceC b 5
  else if RouteFits sourceC 6 b then routeCost sourceC b 6
  else if RouteFits sourceC 7 b then routeCost sourceC b 7
  else if RouteFits sourceC 8 b then routeCost sourceC b 8
  else if RouteFits sourceC 9 b then routeCost sourceC b 9
  else routeCost sourceC b 10

theorem chosenCost_rate (c : Cell) (hv : Valid c) :
    totalCap * chosenCost c ≤ bound * (box c).factorT := by
  have h := receipt c hv
  simp only [Fits] at h
  by_cases ho : (box c).ordinaryFits
  · rw [chosenCost, if_pos ho]
    exact ho
  · have hroutes := h.resolve_left ho
    by_cases hA : RouteFits sourceA 1 (box c)
    · simpa only [chosenCost, ho, hA, if_pos, if_false] using
        hA.2.2.2.2.2.2.2.2
    · have hroutes := hroutes.resolve_left hA
      by_cases hAux : RouteFits sourceAux 1 (box c)
      · simpa only [chosenCost, ho, hA, hAux, if_pos, if_false] using
          hAux.2.2.2.2.2.2.2.2
      · have hroutes := hroutes.resolve_left hAux
        by_cases hC2 : RouteFits sourceC 2 (box c)
        · simpa only [chosenCost, ho, hA, hAux, hC2, if_pos, if_false] using
            hC2.2.2.2.2.2.2.2.2
        · have hroutes := hroutes.resolve_left hC2
          by_cases hC3 : RouteFits sourceC 3 (box c)
          · simpa only [chosenCost, ho, hA, hAux, hC2, hC3, if_pos, if_false] using
              hC3.2.2.2.2.2.2.2.2
          · have hroutes := hroutes.resolve_left hC3
            by_cases hC4 : RouteFits sourceC 4 (box c)
            · simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4,
                if_pos, if_false] using hC4.2.2.2.2.2.2.2.2
            · have hroutes := hroutes.resolve_left hC4
              by_cases hC5 : RouteFits sourceC 5 (box c)
              · simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4, hC5,
                  if_pos, if_false] using hC5.2.2.2.2.2.2.2.2
              · have hroutes := hroutes.resolve_left hC5
                by_cases hC6 : RouteFits sourceC 6 (box c)
                · simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4, hC5,
                    hC6, if_pos, if_false] using hC6.2.2.2.2.2.2.2.2
                · have hroutes := hroutes.resolve_left hC6
                  by_cases hC7 : RouteFits sourceC 7 (box c)
                  · simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4, hC5,
                      hC6, hC7, if_pos, if_false] using hC7.2.2.2.2.2.2.2.2
                  · have hroutes := hroutes.resolve_left hC7
                    by_cases hC8 : RouteFits sourceC 8 (box c)
                    · simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4, hC5,
                        hC6, hC7, hC8, if_pos, if_false] using hC8.2.2.2.2.2.2.2.2
                    · have hroutes := hroutes.resolve_left hC8
                      by_cases hC9 : RouteFits sourceC 9 (box c)
                      · simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4,
                          hC5, hC6, hC7, hC8, hC9, if_pos, if_false] using
                          hC9.2.2.2.2.2.2.2.2
                      · have hC10 := hroutes.resolve_left hC9
                        simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4,
                          hC5, hC6, hC7, hC8, hC9, if_pos, if_false] using
                          hC10.2.2.2.2.2.2.2.2

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
