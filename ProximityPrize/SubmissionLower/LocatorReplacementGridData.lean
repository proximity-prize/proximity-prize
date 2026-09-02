import ProximityPrize.SubmissionLower.LocatorReplacementGridRow006783
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow016783
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow026783
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow036783
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow046783
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow056783
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow066783
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow076783
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow086783
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow096783
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow106783
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow116783
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow126783
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow136783
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow146783
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow156783
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow166783
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow176783
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow186783
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow196783
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow206783

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

private theorem receipt_rows (ri : Fin 21) : RowReceipt ri := by
  fin_cases ri
  · exact receipt_row_00_6783
  · exact receipt_row_01_6783
  · exact receipt_row_02_6783
  · exact receipt_row_03_6783
  · exact receipt_row_04_6783
  · exact receipt_row_05_6783
  · exact receipt_row_06_6783
  · exact receipt_row_07_6783
  · exact receipt_row_08_6783
  · exact receipt_row_09_6783
  · exact receipt_row_10_6783
  · exact receipt_row_11_6783
  · exact receipt_row_12_6783
  · exact receipt_row_13_6783
  · exact receipt_row_14_6783
  · exact receipt_row_15_6783
  · exact receipt_row_16_6783
  · exact receipt_row_17_6783
  · exact receipt_row_18_6783
  · exact receipt_row_19_6783
  · exact receipt_row_20_6783

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
  else if HelperFits sourceH1 10 b then
    max (routeCost sourceH1 b 10) (helperPair sourceH1 b).regularCountCap
  else if HelperFits sourceH1 11 b then
    max (routeCost sourceH1 b 11) (helperPair sourceH1 b).regularCountCap
  else if HelperFits sourceH1 12 b then
    max (routeCost sourceH1 b 12) (helperPair sourceH1 b).regularCountCap
  else if HelperFits sourceH1 13 b then
    max (routeCost sourceH1 b 13) (helperPair sourceH1 b).regularCountCap
  else max (routeCost sourceH2 b 18) (helperPair sourceH2 b).regularCountCap

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
                      · have hroutes := hroutes.resolve_left hC9
                        by_cases hH10 : HelperFits sourceH1 10 (box c)
                        · simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4,
                            hC5, hC6, hC7, hC8, hC9, hH10, if_pos, if_false]
                            using hH10.2.2
                        · have hroutes := hroutes.resolve_left hH10
                          by_cases hH11 : HelperFits sourceH1 11 (box c)
                          · simpa only [chosenCost, ho, hA, hAux, hC2, hC3,
                              hC4, hC5, hC6, hC7, hC8, hC9, hH10, hH11,
                              if_pos, if_false] using hH11.2.2
                          · have hroutes := hroutes.resolve_left hH11
                            by_cases hH12 : HelperFits sourceH1 12 (box c)
                            · simpa only [chosenCost, ho, hA, hAux, hC2, hC3,
                                hC4, hC5, hC6, hC7, hC8, hC9, hH10, hH11,
                                hH12, if_pos, if_false] using hH12.2.2
                            · have hroutes := hroutes.resolve_left hH12
                              by_cases hH13 : HelperFits sourceH1 13 (box c)
                              · simpa only [chosenCost, ho, hA, hAux, hC2,
                                  hC3, hC4, hC5, hC6, hC7, hC8, hC9, hH10,
                                  hH11, hH12, hH13, if_pos, if_false] using
                                  hH13.2.2
                              · have hH218 := hroutes.resolve_left hH13
                                simpa only [chosenCost, ho, hA, hAux, hC2,
                                  hC3, hC4, hC5, hC6, hC7, hC8, hC9, hH10,
                                  hH11, hH12, hH13, if_pos, if_false] using
                                  hH218.2.2

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
