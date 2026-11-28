import ProximityPrize.SubmissionLower.R6970Height2313ExplicitCore
import ProximityPrize.SubmissionLower.Z6970StockAxisRun

set_option autoImplicit false

namespace Research6970.Height2313.Research6969.PairRoute

open _root_.Research6969.OrdinaryRoute (Region)

abbrev AxisRun (i : Fin 18) (r : Region) (wt : ℕ) (wh : Option ℕ) :=
  _root_.Research6970.StockAxis.Run (fun a => Done i ⟨r,a,some a,wt,wh⟩)

theorem axesOfRun {i : Fin 18} {r : Region} {wt : ℕ} {wh : Option ℕ}
    (lo n : ℕ) (run : AxisRun i r wt wh lo (n+1)) :
    Done i ⟨r,lo,some (lo+n),wt,wh⟩ := by
  intro s h
  let a := _root_.Research6966.PadeNativeQuotient.axis s.native.poly 1
  have ha : a ≤ lo+n := h.ah _ rfl
  exact _root_.Research6970.StockAxis.atIndex run h.al (show a < lo+(n+1) by omega) s
    ⟨h.root,le_rfl,fun _ eq => (Option.some.inj eq).le,h.wl,h.wh⟩

end Research6970.Height2313.Research6969.PairRoute
