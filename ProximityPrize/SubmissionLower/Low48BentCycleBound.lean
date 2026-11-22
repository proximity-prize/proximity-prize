import ProximityPrize.SubmissionLower.Low48BentCycle
import ProximityPrize.SubmissionLower.Final50ActiveCycleBound
set_option autoImplicit false
namespace Low48BentCycle
noncomputable section
structure Doubled (R B : Family) : Prop where
  zero_mem : ∀ i, 0 ∈ R i
  pair_mem : ∀ i, ∀ a ∈ R i, ∀ b ∈ R i, a + b ∈ B i
  last_coordinate : ∀ v : Fin 5, Finsupp.single v 1 ∈ R 4
end
end Low48BentCycle
