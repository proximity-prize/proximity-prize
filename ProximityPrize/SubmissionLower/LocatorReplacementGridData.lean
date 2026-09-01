import ProximityPrize.SubmissionLower.LocatorReplacementGridRow16
import ProximityPrize.SubmissionLower.LocatorReplacementGridRow17

namespace ProximityPrize.SubmissionLower.LocatorReplacementGridData

private theorem receipt_rows (ri : Fin 18) : RowReceipt ri := by
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

theorem receipt_unit (c : UnitCell) (hv : (unitBox c).valid)
    (hleaf : ¬ HardUnit c) : Fits (unitBox c) := by
  apply Or.inl
  by_contra hordinary
  exact hleaf ⟨hv, hordinary⟩

theorem receipt_point (c : PointCell) (hv : (pointBox c).valid) :
    Fits (pointBox c) := by
  let u := c.parent.1
  let f := u.parent.1
  let coarse := f.parent.1
  have hhardCoarse : HardCoarse coarse := f.parent.2
  have hhardFine : (fineBoxAt coarse f.yi f.ti).valid ∧
      ¬ Fits (fineBoxAt coarse f.yi f.ti) := by
    simpa only [HardFine, fineBox_eq_fineBoxAt, u, f, coarse] using u.parent.2
  have huvalid : (unitBoxAt coarse f.yi f.ti u.ti).valid := by
    simpa only [HardUnit, unitBox_eq_unitBoxAt, u, f, coarse] using c.parent.2.1
  have hunfit : ¬ (unitBoxAt coarse f.yi f.ti u.ti).ordinaryFits := by
    simpa only [HardUnit, unitBox_eq_unitBoxAt, u, f, coarse] using c.parent.2.2
  have hv' : (pointBoxAt coarse f.yi f.ti u.ti c.ti).valid := by
    simpa only [pointBox_eq_pointBoxAt, u, f, coarse] using hv
  have h := receipt_rows coarse.1 coarse.2.1 coarse.2.2 hhardCoarse
    f.yi f.ti hhardFine u.ti huvalid
  have hp := (h.resolve_left hunfit) c.ti hv'
  apply Or.inl
  simpa only [pointBox_eq_pointBoxAt, u, f, coarse] using hp

/-- Every valid leaf has either the direct ordinary rate or a conservative
    source replacement rate.  Hard width-eight units alone are refined to
    width-two point boxes; coarse and fine failures are refined definitionally. -/
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
    · rcases c with c | c
      · simp only [Valid, box, Leaf] at hv ⊢
        exact receipt_unit c hv.1 hv.2
      · exact receipt_point c hv.1

def chosenCost (c : Cell) : ℕ :=
  let b := box c
  if b.ordinaryFits then b.ordinaryCost
  else if RouteFits sourceA 1 b then routeCost sourceA b 1
  else if RouteFits sourceAux 1 b then routeCost sourceAux b 1
  else if RouteFits sourceC 2 b then routeCost sourceC b 2
  else if RouteFits sourceC 3 b then routeCost sourceC b 3
  else if RouteFits sourceC 4 b then routeCost sourceC b 4
  else routeCost sourceC b 5

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
            · have hC5 := hroutes.resolve_left hC4
              simpa only [chosenCost, ho, hA, hAux, hC2, hC3, hC4,
                if_pos, if_false] using hC5.2.2.2.2.2.2.2.2

end ProximityPrize.SubmissionLower.LocatorReplacementGridData
