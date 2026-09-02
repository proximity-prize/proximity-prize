/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Completed rational-cubic fibre obstruction

Suppose a degree-three rational pencil partitions the 512th roots of unity
together with infinity into 171 full fibres.  After choosing one finite fibre
`A = 0`, its pole fibre has the form `B = 0`, with `A` cubic and `B`
quadratic, and the remaining 169 fibres have the form `A + tᵢ B = 0`.
At a root of `A`, the product identity therefore contains `B` once from the
pole fibre and 169 more times from the other finite fibres: the observable
derivative quotient is a common scalar times `B(r)^170`.

The first theorem below is the exact algebraic identity behind that
reconstruction.  In the KoalaBear field, `170 = 2 * 85` and the 85th-power
map is bijective because `gcd(85,p-1)=1`; hence each projective value of `B`
has only a sign ambiguity.  Three points leave four projective sign patterns,
so a seed cubic determines every possible quadratic pole direction.

`scripts/upper-rational-cubic-completion.cpp` exhausts those directions over
the actual 512th-root domain.  It finds no reconstructed quadratic whose two
roots both lie in that domain, and therefore excludes this completed-fibre
subcase.  The audit does not claim to exclude a cubic fold with two arbitrary
leftovers that are not the finite pole points.
-/

namespace ProximityPrize.SubmissionUpper.RationalCubicCompletionGate

open scoped BigOperators

/-- At a seed point where `A = 0`, a pole factor followed by `m` members of
the pencil contributes exactly `m+1` copies of the direction `B`. -/
theorem pole_times_pencil_at_seed
    {R ι : Type*} [CommSemiring R] [DecidableEq ι]
    (s : Finset ι) (t : ι → R) (A B : R) (hA : A = 0) :
    B * ∏ i ∈ s, (A + t i * B) =
      (∏ i ∈ s, t i) * B ^ (s.card + 1) := by
  subst A
  simp only [zero_add, Finset.prod_mul_distrib, Finset.prod_const]
  rw [pow_succ]
  ac_rfl

/-- The benchmark's exponent decomposition. -/
theorem reconstruction_exponent_receipt : 169 + 1 = 2 * 85 := by
  norm_num

/-- The odd part of the reconstruction exponent is invertible on the
KoalaBear multiplicative group. -/
theorem odd_power_bijection_receipt : Nat.Coprime 85 (2130706433 - 1) := by
  norm_num

/-- Fixing one projective sign leaves four sign patterns at the other two
seed points. -/
theorem projective_sign_pattern_receipt : 2 ^ (3 - 1) = 4 := by
  norm_num

/-- Three fixed anchors cannot all be swallowed by a two-point pole fibre.
This is the small covering fact used to reduce the exhaustive search to
`3 * choose 511 2` seed triples. -/
theorem three_anchors_cover_two_poles
    (poles : Finset (Fin 3)) (hpoles : poles.card ≤ 2) :
    ∃ anchor : Fin 3, anchor ∉ poles := by
  by_contra h
  push Not at h
  have huniv : poles = Finset.univ := by
    ext anchor
    simp [h anchor]
  rw [huniv, Finset.card_univ, Fintype.card_fin] at hpoles
  omega

set_option maxRecDepth 1000000 in
/-- Exact number of anchored seed triples searched by the audit. -/
theorem anchored_seed_count_receipt :
    3 * Nat.choose 511 2 = 390915 := by
  rw [Nat.choose_eq_fast_choose]
  decide

end ProximityPrize.SubmissionUpper.RationalCubicCompletionGate

#print axioms ProximityPrize.SubmissionUpper.RationalCubicCompletionGate.pole_times_pencil_at_seed
#print axioms ProximityPrize.SubmissionUpper.RationalCubicCompletionGate.three_anchors_cover_two_poles
