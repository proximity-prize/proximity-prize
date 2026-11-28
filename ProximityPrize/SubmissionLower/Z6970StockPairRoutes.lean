import ProximityPrize.SubmissionLower.Z6969Pack0934
import ProximityPrize.SubmissionLower.Z6970StockAxisRun

set_option autoImplicit false
set_option Elab.async false

namespace Research6969.PairRoute

open OrdinaryRoute (Region)

abbrev AxisRun (i : Fin 18) (r : Region) (wt : ℕ) (wh : Option ℕ) :=
  Research6970.StockAxis.Run (fun a => Done i ⟨r,a,some a,wt,wh⟩)

theorem axesOfRun {i : Fin 18} {r : Region} {wt : ℕ} {wh : Option ℕ}
    (lo n : ℕ) (run : AxisRun i r wt wh lo (n+1)) :
    Done i ⟨r,lo,some (lo+n),wt,wh⟩ := by
  intro s h
  let a := Research6966.PadeNativeQuotient.axis s.native.poly 1
  have ha : a ≤ lo+n := h.ah _ rfl
  exact Research6970.StockAxis.atIndex run h.al (show a < lo+(n+1) by omega) s
    ⟨h.root,le_rfl,fun _ eq => (Option.some.inj eq).le,h.wl,h.wh⟩

end Research6969.PairRoute

namespace Research6969.StockPairs

open PairRoute

theorem fromCheck {i : Fin 18} {row : PairCell.Row} {decision : PairPrices.Decision}
    (paid : PairPrices.valid row i decision) (endWeight : Option ℕ)
    (validEnd : PairProof.node decision = true → endWeight = some decision.cutoff) :
    Done i (of_row row endWeight) :=
  PairLeaves.paired row decision paid endWeight validEnd

abbrev surfaceWhole : PairPrices.Decision := ⟨.surface,.whole,.impossible,0⟩
abbrev markedWhole : PairPrices.Decision := ⟨.marked,.whole,.impossible,0⟩
abbrev markedAxisWhole : PairPrices.Decision := ⟨.markedAxis,.whole,.impossible,0⟩
abbrev separateWhole : PairPrices.Decision := ⟨.separate,.whole,.impossible,0⟩
abbrev surfaceIntersection : PairPrices.Decision := ⟨.surface,.intersection,.impossible,0⟩
abbrev markedIntersection : PairPrices.Decision := ⟨.marked,.intersection,.impossible,0⟩
abbrev markedAxisIntersection : PairPrices.Decision := ⟨.markedAxis,.intersection,.impossible,0⟩
abbrev separateIntersection : PairPrices.Decision := ⟨.separate,.intersection,.impossible,0⟩

structure Receipt where
  row : PairCell.Row
  seed : Fin 18
  choice : PairPrices.Decision

def checked (data : List Receipt) : Bool :=
  data.all fun e => decide (PairPrices.valid e.row e.seed e.choice)

abbrev ValidAt (data : List Receipt) (i : Fin data.length) : Prop :=
  PairPrices.valid (data.get i).row (data.get i).seed (data.get i).choice

theorem atChecked {data : List Receipt} (paid : checked data = true) (i : Fin data.length) :
    ValidAt data i := by
  unfold checked at paid
  exact of_decide_eq_true (List.all_eq_true.mp paid _ (List.get_mem data i))

end Research6969.StockPairs
