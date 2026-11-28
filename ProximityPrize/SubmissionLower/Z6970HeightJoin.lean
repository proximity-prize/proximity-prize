import ProximityPrize.SubmissionLower.Z6969Pack0977
import ProximityPrize.SubmissionLower.Far6970Geometry

set_option autoImplicit false

namespace Research6970.HeightJoin

open K1 (K I)

def Low : Prop :=
  ∀ (u : P1.Words) (deleted : Finset I) (M : P1.ModelAt 33755 u deleted)
    (Γ : Finset K), P1.FamilyAt 179730 M Γ →
    1 ≤ M.overhead → M.overhead ≤ 2313 → Γ.card ≤ 274779381266040420

theorem high {u : P1.Words} {deleted : Finset I}
    (M : P1.ModelAt 33755 u deleted) {Γ : Finset K} (F : P1.FamilyAt 179730 M Γ)
    (lo : 2314 ≤ M.overhead) (hi : M.overhead ≤ 33755) :
    Γ.card ≤ 274779381266040420 := by
  by_cases transition : M.overhead ≤ 2557
  · exact (Research6969.Completed.count M F lo transition).trans (by decide)
  · exact (Research6969.Far6970TerminalCount.count M F (by omega) hi).trans (by decide)

end Research6970.HeightJoin
