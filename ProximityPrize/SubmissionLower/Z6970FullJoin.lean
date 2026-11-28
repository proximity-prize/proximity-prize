import ProximityPrize.SubmissionLower.R6970Height2313HighJoin
import ProximityPrize.SubmissionLower.Z6970Composition

set_option autoImplicit false

namespace Research6970.FullJoin

open K1 (K I)

def NativeLow : Prop :=
  ∀ (u : P1.Words) (deleted : Finset I) (M : P1.ModelAt 33755 u deleted)
    (Γ : Finset K), P1.FamilyAt 179730 M Γ →
    1 ≤ M.overhead → M.overhead ≤ 2307 → Γ.card ≤ 274779381266040420

theorem candidate_of_native_low (low : NativeLow) :
    ProximityPrize.Benchmark.ProtocolClaim 6970 2899720025701049676 9223372036854649837 := by
  apply Research6970.Composition.candidate_of_low
  intro u deleted M Γ F lo hi
  by_cases edge : M.overhead ≤ 2307
  · exact low u deleted M Γ F lo edge
  · exact Research6970.Height2313.high M F (by omega) (by omega)

end Research6970.FullJoin

#print axioms Research6970.FullJoin.candidate_of_native_low
