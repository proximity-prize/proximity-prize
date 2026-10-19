import ProximityPrize.Benchmark.BinaryTargetLower
import Mathlib.RingTheory.Radical.Basic

/-!
# Compatibility aliases

The BCHKS development was written against an older Mathlib. These aliases keep
the old names available under the pinned Lean 4.34 Mathlib.
-/

theorem Finset.filter_card_add_filter_neg_card_eq_card {α : Type*} {s : Finset α}
    (p : α → Prop) [DecidablePred p] [∀ x, Decidable (¬p x)] :
    (s.filter p).card + (s.filter fun a => ¬ p a).card = s.card :=
  Finset.card_filter_add_card_filter_not p

attribute [simp] UniqueFactorizationMonoid.mem_primeFactors
