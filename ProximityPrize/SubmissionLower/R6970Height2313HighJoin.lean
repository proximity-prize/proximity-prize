import ProximityPrize.SubmissionLower.R6970Height2313Count
import ProximityPrize.SubmissionLower.Z6970HeightJoin

set_option autoImplicit false

namespace Research6970.Height2313

open K1 (K I)

theorem high {u : P1.Words} {deleted : Finset I}
    (M : P1.ModelAt 33755 u deleted) {Γ : Finset K} (F : P1.FamilyAt 179730 M Γ)
    (lo : 2308 ≤ M.overhead) (hi : M.overhead ≤ 33755) :
    Γ.card ≤ 274779381266040420 := by
  by_cases edge : M.overhead ≤ 2313
  · exact (count M F lo edge).trans (by decide)
  · exact Research6970.HeightJoin.high M F (by omega) hi

end Research6970.Height2313
