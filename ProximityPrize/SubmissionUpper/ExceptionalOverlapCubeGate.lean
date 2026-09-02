/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.SubmissionUpper.ExceptionalJointMomentGate

/-!
# Overlapping affine-cube gate for the exceptional moment fibre

`ExceptionalJointMomentGate` rules out pairwise-disjoint small trades and complete dyadic-coset
unions.  An apparent gap is that binary generators can overlap.  This file closes every affine
`F_2` cube inside the same fixed-weight, fifteen-moment fibre, without assuming that its chosen
basis toggles are disjoint.

Assign to each endpoint its toggle signature in the dual of the cube.  Endpoints with the same
nonzero signature form a *Walsh atom*.  The atoms are disjoint even when the original basis
toggles overlap.  Walsh orthogonality applied to the constant weight and each constant moment
isolates one atom at a time: its endpoints selected in the base record and those not selected
have equal cardinality and equal first fifteen power sums.

Newton's identities (all indices `1,...,15` are units in the benchmark field) determine every
elementary symmetric function of an atom side of size at most fifteen.  Such a side would be
rigid, so a nontrivial atom has at least sixteen endpoints on each side.  Every base record omits
one whole side of every atom.  Since a weight-272 record omits only `510 - 272 = 238` endpoints,
at most `floor(238 / 16) = 14` active atoms fit.  An injective `d`-dimensional cube needs at least
`d` nonzero signatures, so `d <= 14` and the entire cube has at most `2^14 = 16384` records.

The generic Walsh theorem below formalizes the isolation step over an arbitrary field.  The
trade theorem starts at the coefficient interface supplied by Newton's identities, just as the
companion exceptional-fibre gate does.  The final theorem packages the exact atom-packing and
benchmark arithmetic.

This is strictly stronger than a disjoint-generator audit: a basis toggle may meet every other
basis toggle.  It does not bound a non-affine fibre or a union of many unrelated small cubes, so
it is a scoped research gate rather than a score claim.
-/

namespace ProximityPrize.SubmissionUpper.ExceptionalOverlapCubeGate

open Polynomial
open ProximityPrize.SubmissionUpper.ExceptionalJointMomentGate

/-! ## Walsh isolation for overlapping generators -/

section Walsh

variable {V S F : Type*} [Fintype V] [Fintype S] [DecidableEq S] [Field F]

/-- If a finite character expansion is constant, orthogonality isolates every nonconstant
coefficient.  In the application, `S` is the set of endpoint toggle signatures, `V` is the
binary challenge cube, and `weight s` is one signed moment of the endpoints in atom `s`.

The theorem takes only the one row of character orthogonality needed for `target`; this keeps it
independent of a particular encoding of finite binary vectors. -/
theorem walsh_isolates_nonconstant_atom
    (character : S → V → F) (weight : S → F) (target : S) (constant : F)
    (hconstant : ∀ u, ∑ s, character s u * weight s = constant)
    (hmean : ∑ u, character target u = 0)
    (horthogonal : ∀ s, ∑ u, character target u * character s u =
      if s = target then (Fintype.card V : F) else 0)
    (hcard : (Fintype.card V : F) ≠ 0) :
    weight target = 0 := by
  have hweighted :
      ∑ u, character target u * (∑ s, character s u * weight s) = 0 := by
    calc
      ∑ u, character target u * (∑ s, character s u * weight s) =
          ∑ u, character target u * constant := by
            apply Finset.sum_congr rfl
            intro u _
            rw [hconstant]
      _ = (∑ u, character target u) * constant := by
            rw [Finset.sum_mul]
      _ = 0 := by rw [hmean, zero_mul]
  have hrearrange :
      ∑ u, character target u * (∑ s, character s u * weight s) =
        ∑ s, (∑ u, character target u * character s u) * weight s := by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro u _
    ring
  rw [hrearrange] at hweighted
  have hisolated : (Fintype.card V : F) * weight target = 0 := by
    simpa [horthogonal] using hweighted
  exact (mul_eq_zero.mp hisolated).resolve_left hcard

end Walsh

/-! ## One Walsh atom consumes at least 32 endpoints -/

variable {F : Type*} [Field F]

/-- Locator coefficients through index fifteen determine any root multiset of cardinality at
most fifteen.  This is the exact coefficient interface produced from the first fifteen power
sums by Newton's identities. -/
theorem multiset_eq_of_coefficients_through_fifteen
    (A B : Multiset F) (hcard : A.card = B.card) (hsmall : A.card ≤ 15)
    (hcoeff : ∀ k, k ≤ 15 → (locator A).coeff k = (locator B).coeff k) :
    A = B := by
  have hAdegree : (locator A).natDegree ≤ 15 := by
    rw [locator, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]
    exact hsmall
  have hBdegree : (locator B).natDegree ≤ 15 := by
    rw [locator, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, ← hcard]
    exact hsmall
  have hlocator : locator A = locator B := by
    apply Polynomial.ext
    intro k
    by_cases hk : k ≤ 15
    · exact hcoeff k hk
    · have hklarge : 15 < k := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hAdegree hklarge),
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hBdegree hklarge)]
  have hroots := congrArg Polynomial.roots hlocator
  simpa [locator] using hroots

/-- Equality of the elementary symmetric functions `e_1,...,e_15` determines a root multiset of
cardinality at most fifteen.  These are exactly the quantities recursively supplied by equal
power sums through fifteen via Newton's identities. -/
theorem multiset_eq_of_esymm_through_fifteen
    (A B : Multiset F) (hcard : A.card = B.card) (hsmall : A.card ≤ 15)
    (hesymm : ∀ j, j ≤ 15 → A.esymm j = B.esymm j) :
    A = B := by
  apply multiset_eq_of_coefficients_through_fifteen A B hcard hsmall
  intro k hk
  by_cases hkcard : k ≤ A.card
  · have hkcardB : k ≤ B.card := by omega
    rw [locator, locator, Multiset.prod_X_sub_C_coeff A hkcard,
      Multiset.prod_X_sub_C_coeff B hkcardB, ← hcard]
    rw [hesymm (A.card - k) (by omega)]
  · have hklargeA : (locator A).natDegree < k := by
      rw [locator, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]
      omega
    have hklargeB : (locator B).natDegree < k := by
      rw [locator, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, ← hcard]
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hklargeA,
      Polynomial.coeff_eq_zero_of_natDegree_lt hklargeB]

/-- Contrapositive Newton rigidity without using the product key: a nontrivial equal-weight atom
whose first fifteen elementary symmetric functions agree has at least sixteen roots on each
side. -/
theorem nontrivial_atom_side_at_least_sixteen
    (A B : Multiset F) (hcard : A.card = B.card)
    (hesymm : ∀ j, j ≤ 15 → A.esymm j = B.esymm j)
    (hne : A ≠ B) :
    16 ≤ A.card := by
  by_contra hnot
  have hsmall : A.card ≤ 15 := by omega
  exact hne (multiset_eq_of_esymm_through_fifteen A B hcard hsmall hesymm)

/-- The selected and unselected halves of every active Walsh atom together occupy at least
thirty-two endpoint positions. -/
theorem nontrivial_atom_support_at_least_thirty_two
    (A B : Multiset F) (hcard : A.card = B.card)
    (hesymm : ∀ j, j ≤ 15 → A.esymm j = B.esymm j)
    (hne : A ≠ B) :
    32 ≤ A.card + B.card := by
  have hside := nontrivial_atom_side_at_least_sixteen A B hcard hesymm hne
  omega

/-! ## Exact benchmark packing -/

def endpointPool : ℕ := 510
def selectorWeight : ℕ := 272
def unselectedPool : ℕ := 238
def minimumAtomSide : ℕ := 16
def minimumAtomSupport : ℕ := 32
def maximumActiveAtoms : ℕ := 14
def maximumAffineDimension : ℕ := 14
def maximumAffineCubeSize : ℕ := 16384
def challengeThreshold : ℕ := 274980728111395088
def minimumThresholdCubeCover : ℕ := 16783491706018

/-- One unselected side of every disjoint Walsh atom lies in the 238-point complement of a base
record.  Sides of size at least sixteen leave room for at most fourteen active signatures. -/
theorem active_atom_count_le_fourteen
    (activeAtoms : ℕ) (hpacking : minimumAtomSide * activeAtoms ≤ unselectedPool) :
    activeAtoms ≤ maximumActiveAtoms := by
  norm_num [minimumAtomSide, unselectedPool, maximumActiveAtoms] at hpacking ⊢
  omega

/-- Finite-sum form of the same packing gate.  It records explicitly that each active atom
contributes one disjoint side to the complement of a fixed base record. -/
theorem active_atom_count_le_fourteen_of_side_sum
    (activeAtoms : ℕ) (side : Fin activeAtoms → ℕ)
    (hside : ∀ i, minimumAtomSide ≤ side i)
    (hpool : ∑ i, side i ≤ unselectedPool) :
    activeAtoms ≤ maximumActiveAtoms := by
  have hminimum : ∑ _i : Fin activeAtoms, minimumAtomSide ≤ ∑ i, side i := by
    apply Finset.sum_le_sum
    intro i _
    exact hside i
  apply active_atom_count_le_fourteen activeAtoms
  calc
    minimumAtomSide * activeAtoms = ∑ _i : Fin activeAtoms, minimumAtomSide := by
      simp [Nat.mul_comm]
    _ ≤ ∑ i, side i := hminimum
    _ ≤ unselectedPool := hpool

/-- This is the overlap closure: once Walsh atomization supplies the support packing and
injectivity supplies `dimension <= activeAtoms`, no choice of overlapping affine generators can
reach the benchmark threshold. -/
theorem overlapping_affine_cube_below_threshold
    (dimension activeAtoms : ℕ) (hspan : dimension ≤ activeAtoms)
    (hpacking : minimumAtomSide * activeAtoms ≤ unselectedPool) :
    2 ^ dimension < challengeThreshold := by
  have hatoms : activeAtoms ≤ maximumActiveAtoms :=
    active_atom_count_le_fourteen activeAtoms hpacking
  have hdimension : dimension ≤ maximumAffineDimension := by
    norm_num [maximumActiveAtoms, maximumAffineDimension] at hatoms ⊢
    omega
  calc
    2 ^ dimension ≤ 2 ^ maximumAffineDimension :=
      Nat.pow_le_pow_right (by norm_num) hdimension
    _ = maximumAffineCubeSize := by
      norm_num [maximumAffineDimension, maximumAffineCubeSize]
    _ < challengeThreshold := by
      norm_num [maximumAffineCubeSize, challengeThreshold]

/-- Side-list form of the full overlap closure. -/
theorem overlapping_affine_cube_below_threshold_of_side_sum
    (dimension activeAtoms : ℕ) (side : Fin activeAtoms → ℕ)
    (hspan : dimension ≤ activeAtoms)
    (hside : ∀ i, minimumAtomSide ≤ side i)
    (hpool : ∑ i, side i ≤ unselectedPool) :
    2 ^ dimension < challengeThreshold := by
  have hatoms := active_atom_count_le_fourteen_of_side_sum activeAtoms side hside hpool
  have hdimension : dimension ≤ maximumAffineDimension := by
    norm_num [maximumActiveAtoms, maximumAffineDimension] at hatoms ⊢
    omega
  calc
    2 ^ dimension ≤ 2 ^ maximumAffineDimension :=
      Nat.pow_le_pow_right (by norm_num) hdimension
    _ = maximumAffineCubeSize := by
      norm_num [maximumAffineDimension, maximumAffineCubeSize]
    _ < challengeThreshold := by
      norm_num [maximumAffineCubeSize, challengeThreshold]

/-- A threshold-sized fibre cannot even be covered by fewer than
`16,783,491,706,018` affine cubes of the preceding kind. -/
theorem affine_cube_cover_count_lower_bound
    (pieces : ℕ) (hcover : challengeThreshold ≤ pieces * maximumAffineCubeSize) :
    minimumThresholdCubeCover ≤ pieces := by
  norm_num [challengeThreshold, maximumAffineCubeSize, minimumThresholdCubeCover] at hcover ⊢
  omega

theorem benchmark_cube_ledger :
    endpointPool - selectorWeight = unselectedPool ∧
      minimumAtomSide * maximumActiveAtoms = 224 ∧
      224 ≤ unselectedPool ∧ unselectedPool < minimumAtomSide * 15 ∧
      maximumAffineCubeSize = 2 ^ maximumAffineDimension ∧
      maximumAffineCubeSize < challengeThreshold ∧
      (challengeThreshold + maximumAffineCubeSize - 1) / maximumAffineCubeSize =
        minimumThresholdCubeCover := by
  norm_num [endpointPool, selectorWeight, unselectedPool, minimumAtomSide,
    maximumActiveAtoms, maximumAffineCubeSize, maximumAffineDimension, challengeThreshold,
    minimumThresholdCubeCover]

#print axioms walsh_isolates_nonconstant_atom
#print axioms multiset_eq_of_coefficients_through_fifteen
#print axioms multiset_eq_of_esymm_through_fifteen
#print axioms nontrivial_atom_support_at_least_thirty_two
#print axioms active_atom_count_le_fourteen_of_side_sum
#print axioms overlapping_affine_cube_below_threshold
#print axioms overlapping_affine_cube_below_threshold_of_side_sum
#print axioms affine_cube_cover_count_lower_bound
#print axioms benchmark_cube_ledger

end ProximityPrize.SubmissionUpper.ExceptionalOverlapCubeGate
