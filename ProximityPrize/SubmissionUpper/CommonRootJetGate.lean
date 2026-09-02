/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# The common-root jet gate for the 512-fibre orbit pencil

Forcing every support locator to contain a fixed root `beta` looks like a
cheap way to gain a third divisor of the orbit-pencil numerator.  It does
indeed lower the quotient degree by one.  However, after cancelling the
common factor, the `beta` block is no longer an ordinary value contact: its
mismatch is the first jet, namely the cofactor value `W_U(beta) = V_U'(beta)`.

This file isolates that exact algebra.  It also records the benchmark
arithmetic.  Requiring one common included fibre and one common excluded
fibre leaves enough locator entropy, and the freed quotient degree permits a
degree-1023 fixed multiplier.  But the noncommon fibres plus those fixed
roots total exactly the old `139775` agreements.  Reaching `139782` therefore
requires seven genuine jet contacts.  With 512 physical coordinates in the
common fibre, double counting forces an affine jet fibre of size at least
`3759502142147980` on any threshold-sized challenge family.
-/

namespace ProximityPrize.SubmissionUpper.CommonRootJetGate

open Polynomial

variable {F : Type} [Field F]

/-- The numerator obtained by using the common root as one of three intended
quotient roots. -/
noncomputable def commonRootPencil (beta gamma : F)
    (Vzero V : Polynomial F) : Polynomial F :=
  Vzero - V - Polynomial.C gamma * Polynomial.X *
    (Polynomial.X - Polynomial.C beta)

/-- Cancelling the common factor exposes the cofactor difference and a
linear challenge correction. -/
theorem commonRootPencil_factor
    {beta gamma : F} {Vzero V Wzero W : Polynomial F}
    (hzero : Vzero = (Polynomial.X - Polynomial.C beta) * Wzero)
    (hV : V = (Polynomial.X - Polynomial.C beta) * W) :
    commonRootPencil beta gamma Vzero V =
      (Polynomial.X - Polynomial.C beta) *
        (Wzero - W - Polynomial.C gamma * Polynomial.X) := by
  rw [hzero, hV]
  simp only [commonRootPencil]
  ring

/-- Evaluation of the cancelled numerator at the common root.  The term
`W.eval beta` is precisely the first-jet obstruction. -/
theorem cancelled_eval_common_root
    (beta gamma : F) (Wzero W : Polynomial F) :
    (Wzero - W - Polynomial.C gamma * Polynomial.X).eval beta =
      Wzero.eval beta - W.eval beta - gamma * beta := by
  simp [Polynomial.eval_sub, Polynomial.eval_mul]

/-- Cofactor of a square-free locator after its distinguished root has been
removed. -/
noncomputable def squarefreeCofactor (roots : Finset F) : Polynomial F :=
  ∏ x ∈ roots, (Polynomial.X - Polynomial.C x)

/-- The exposed first jet is nonzero when all remaining locator roots differ
from the common root.  This is the situation for the orbit locators. -/
theorem squarefreeCofactor_eval_ne_zero
    (beta : F) (roots : Finset F)
    (hdistinct : ∀ x ∈ roots, x ≠ beta) :
    (squarefreeCofactor roots).eval beta ≠ 0 := by
  classical
  rw [squarefreeCofactor, Polynomial.eval_prod, Finset.prod_ne_zero_iff]
  intro x hx
  simpa [sub_ne_zero] using (hdistinct x hx).symm

/-- The exposed jet and the full complementary locator multiply to the fixed
grid cofactor.  This is the precise upper counterpart of the accepted
lower-bound complement replacement: the complement can recover the jet, but
it is selector-dependent data rather than a fixed received-word value. -/
theorem common_jet_mul_complement_eval
    (beta : F) (W complement gridCofactor : Polynomial F)
    (hgrid : (Polynomial.X - Polynomial.C beta) * W * complement =
      (Polynomial.X - Polynomial.C beta) * gridCofactor) :
    W.eval beta * complement.eval beta = gridCofactor.eval beta := by
  have hcancel : W * complement = gridCofactor := by
    apply mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero beta)
    simpa [mul_assoc] using hgrid
  have h := congrArg (Polynomial.eval beta) hcancel
  simpa [Polynomial.eval_mul] using h

/-- If the cancelled numerator has the two remaining factors `X` and
`X-alpha`, then its value at `beta` determines the codeword quotient there.
-/
theorem quotient_eval_common_root
    {alpha beta gamma : F} {Wzero W Q : Polynomial F}
    (hQ : Wzero - W - Polynomial.C gamma * Polynomial.X =
      Polynomial.X * (Polynomial.X - Polynomial.C alpha) * Q) :
    beta * (beta - alpha) * Q.eval beta =
      Wzero.eval beta - W.eval beta - gamma * beta := by
  have h := congrArg (Polynomial.eval beta) hQ
  simpa [Polynomial.eval_sub, Polynomial.eval_mul] using h.symm

/-- The natural received-word value obtained by taking the removable limit
of the fixed part misses the codeword by exactly the locator cofactor jet.
Thus a square-free common locator root contributes no new contact unless the
fixed multiplier already vanishes there. -/
theorem natural_common_root_contact_iff
    {alpha beta gamma r : F} {Wzero W Q : Polynomial F}
    (hden : beta * (beta - alpha) ≠ 0)
    (hQ : Wzero - W - Polynomial.C gamma * Polynomial.X =
      Polynomial.X * (Polynomial.X - Polynomial.C alpha) * Q) :
    r * (Wzero.eval beta - gamma * beta) / (beta * (beta - alpha)) =
        r * Q.eval beta ↔
      r * W.eval beta = 0 := by
  have hEval := quotient_eval_common_root (beta := beta) hQ
  rw [div_eq_iff hden]
  constructor
  · intro hcontact
    linear_combination r * hEval + hcontact
  · intro hjet
    linear_combination -r * hEval + hjet

/-- In particular, away from a fixed multiplier root, a simple common root
is not an agreement coordinate for the natural pencil. -/
theorem natural_common_root_not_contact
    {alpha beta gamma r : F} {Wzero W Q : Polynomial F}
    (hden : beta * (beta - alpha) ≠ 0)
    (hr : r ≠ 0) (hjet : W.eval beta ≠ 0)
    (hQ : Wzero - W - Polynomial.C gamma * Polynomial.X =
      Polynomial.X * (Polynomial.X - Polynomial.C alpha) * Q) :
    r * (Wzero.eval beta - gamma * beta) / (beta * (beta - alpha)) ≠
      r * Q.eval beta := by
  intro hcontact
  have hzero :=
    (natural_common_root_contact_iff (beta := beta) hden hQ).mp hcontact
  exact (mul_ne_zero hr hjet) hzero

/-- Allowing an arbitrary affine received value at the common coordinate
does not remove the obstruction.  It asks for the cofactor jet to lie on one
explicit affine line in the challenge. -/
theorem affine_common_root_contact_iff
    {alpha beta gamma r a b : F} {Wzero W Q : Polynomial F}
    (hden : beta * (beta - alpha) ≠ 0) (hr : r ≠ 0)
    (hQ : Wzero - W - Polynomial.C gamma * Polynomial.X =
      Polynomial.X * (Polynomial.X - Polynomial.C alpha) * Q) :
    a + gamma * b = r * Q.eval beta ↔
      W.eval beta =
        Wzero.eval beta - (beta * (beta - alpha) * a) / r +
          gamma * (-(beta) - (beta * (beta - alpha) * b) / r) := by
  have hEval := quotient_eval_common_root (beta := beta) hQ
  constructor
  · intro h
    field_simp [hr]
    linear_combination r * hEval + beta * (beta - alpha) * h
  · intro h
    field_simp [hr] at h
    apply (mul_left_cancel₀ hden)
    linear_combination h - r * hEval

/-! ## Base-field jet versus extension-valued challenge -/

/-- A nonhorizontal affine line in `(challenge, jet)` space contains at most
one injectively labelled challenge for each base-field jet value.  Hence its
intersection with the locator graph has size at most the base-field size.

This is the key distinction between the upstream lower helper switch and an
upper received-word switch: the upper challenge lies in the six-dimensional
extension, while the exposed locator jet lies in the base field. -/
theorem nonhorizontal_affine_jet_fibre_card_le
    {K E S : Type} [Field K] [Field E] [Algebra K E] [Fintype K]
    [DecidableEq E] [DecidableEq S]
    (selectors : Finset S) (challenge : S → E) (jet : S → K)
    (hinjective : Set.InjOn challenge selectors)
    (a b : E) (hb : b ≠ 0) :
    (selectors.filter fun s ↦
      algebraMap K E (jet s) = a + challenge s * b).card ≤ Fintype.card K := by
  classical
  rw [← Finset.card_univ]
  apply Finset.card_le_card_of_injOn jet
  · intro s hs
    exact Finset.mem_univ _
  · intro x hx y hy hjet
    apply hinjective (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1
    apply mul_right_cancel₀ hb
    have hxline := (Finset.mem_filter.mp hx).2
    have hyline := (Finset.mem_filter.mp hy).2
    calc
      challenge x * b = algebraMap K E (jet x) - a := by rw [hxline]; ring
      _ = algebraMap K E (jet y) - a := by rw [hjet]
      _ = challenge y * b := by rw [hyline]; ring

/-! ## Exact benchmark receipts -/

def baseFieldCardinality : Nat := 2130706433
def challengeThreshold : Nat := 274980728111395088

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
set_option exponentiation.threshold 100000 in
/-- One forced included label and one forced excluded label leave
`C(509,271)` raw locators.  The existing fourteen top coefficients and the
512-state product key still leave more than the required challenge count. -/
theorem restricted_locator_entropy :
    baseFieldCardinality ^ 14 * 512 * challengeThreshold < Nat.choose 509 271 := by
  rw [Nat.choose_eq_fast_choose]
  decide

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
set_option exponentiation.threshold 100000 in
/-- A generic additional base-field jet key is far too expensive; the plain
pigeonhole estimate then fails by more than 29 bits. -/
theorem full_jet_key_pigeonhole_fails :
    Nat.choose 509 271 <
      baseFieldCardinality ^ 15 * 512 * challengeThreshold := by
  rw [Nat.choose_eq_fast_choose]
  decide

/-- Three numerator roots lower the orbit quotient to degree 254, allowing a
degree-1023 fixed multiplier without exceeding the row degree. -/
theorem freed_degree_receipt : 1023 + 254 * 512 = 131071 := by
  norm_num

/-- The common root itself is a jet coordinate.  Counting only the 271
ordinary selected fibres and the 1023 fixed multiplier roots gives exactly
the existing agreement count. -/
theorem contact_conservation_receipt : 271 * 512 + 1023 = 139775 := by
  norm_num

/-- Counting the common fibre as ordinary value contacts would give 140287,
but `natural_common_root_contact_iff` shows why those 512 contacts are not
automatic. -/
theorem tempting_but_jet_dependent_count : 272 * 512 + 1023 = 140287 := by
  norm_num

/-- Seven jet contacts per challenge across 512 common-fibre coordinates
force some coordinate/affine-line fibre to contain at least this many
challenges. -/
theorem required_affine_jet_fibre :
    7 * challengeThreshold ≤ 512 * 3759502142147980 := by
  norm_num [challengeThreshold]

/-- One less than the stated fibre size cannot carry the required incidence,
so the preceding threshold is exact. -/
theorem required_affine_jet_fibre_sharp :
    512 * 3759502142147979 < 7 * challengeThreshold := by
  norm_num [challengeThreshold]

/-- Even assigning all 512 common-fibre coordinates distinct nonhorizontal
affine lines cannot supply seven contacts to a threshold-sized family. -/
theorem nonhorizontal_jet_incidence_is_too_small :
    512 * baseFieldCardinality < 7 * challengeThreshold := by
  norm_num [baseFieldCardinality, challengeThreshold]

/-- After generously crediting every possible nonhorizontal coordinate by
the full base-field cap, a horizontal (fixed-jet) fibre must still have at
least this size. -/
theorem required_horizontal_jet_fibre :
    7 * challengeThreshold - 512 * baseFieldCardinality ≤
      512 * 3759500011441547 := by
  norm_num [baseFieldCardinality, challengeThreshold]

/-- The preceding horizontal-fibre threshold is the exact ceiling of the
remaining incidence divided by 512. -/
theorem required_horizontal_jet_fibre_sharp :
    512 * 3759500011441546 <
      7 * challengeThreshold - 512 * baseFieldCardinality := by
  norm_num [baseFieldCardinality, challengeThreshold]

#print axioms commonRootPencil_factor
#print axioms natural_common_root_contact_iff
#print axioms affine_common_root_contact_iff
#print axioms nonhorizontal_affine_jet_fibre_card_le
#print axioms restricted_locator_entropy

end ProximityPrize.SubmissionUpper.CommonRootJetGate
