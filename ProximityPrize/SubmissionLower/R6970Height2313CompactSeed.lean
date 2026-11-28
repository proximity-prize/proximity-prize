import ProximityPrize.SubmissionLower.R6970Height2313CompressedCore

set_option autoImplicit false

namespace Research6970.Height2313.Research6969.NormalRoute

def SeedRun (i : Fin 18) (e top c a : ℕ) : ℕ → List ℕ → Prop
  | lo, [] => Tail i e top c a lo
  | lo, hi :: rest =>
    Done i ⟨e,top,c,a,lo,some hi⟩ ∧ SeedRun i e top c a (hi+1) rest

theorem tailOfRun {i : Fin 18} {e top c a lo : ℕ} (bounds : List ℕ)
    (run : SeedRun i e top c a lo bounds) : Tail i e top c a lo := by
  induction bounds generalizing lo with
  | nil => exact run
  | cons hi bounds ih =>
    change Done i ⟨e,top,c,a,lo,some hi⟩ ∧ SeedRun i e top c a (hi+1) bounds at run
    exact join run.1 (ih run.2)

end Research6970.Height2313.Research6969.NormalRoute
