/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# One-line obstruction for fourth-root-normalized locator compilers

Fourth-root normalization of a degree-136 locator repairs its constant and
linear coefficients, but exposes two independent correction coordinates:

* a four-valued leading-band branch coordinate; and
* the freely varying off-grid challenge coordinate.

Modulo the row Reed--Solomon code these coordinates span an affine plane.  A
benchmark received pair still traces only one affine line, even with eight
interleaves because every row uses the same scalar challenge.  This file
isolates the abstract linear-algebra consequence.  If the line moves in the
branch coordinate, it meets each fixed-branch line at most once.  If it does
not move in that coordinate, it can remain in only one branch.

The concrete degree audit establishing independence of the two normalized
locator directions is checked by `scripts/upper-quartic-branch-line-audit.py`.
-/

namespace ProximityPrize.SubmissionUpper.QuarticBranchLineGate

variable {F M : Type*} [Field F] [AddCommGroup M] [Module F M]

/-- Two vectors have no nontrivial two-term linear relation.  This elementary
form avoids choosing a basis for the ambient received-word quotient. -/
def TwoDirectionIndependent (u v : M) : Prop :=
  ∀ a b : F, a • u + b • v = 0 → a = 0 ∧ b = 0

/-- Coordinate realization of the affine plane spanned by two quotient
directions. -/
def planePoint (base u v : M) (s t : F) : M :=
  base + s • u + t • v

/-- Independent directions give injective affine-plane coordinates. -/
theorem planePoint_injective (base u v : M)
    (hind : TwoDirectionIndependent (F := F) u v) :
    Function.Injective (fun st : F × F => planePoint base u v st.1 st.2) := by
  intro x y hxy
  have hsum : x.1 • u + x.2 • v = y.1 • u + y.2 • v := by
    apply add_left_cancel (a := base)
    simpa only [planePoint, add_assoc] using hxy
  have hzero : (x.1 - y.1) • u + (x.2 - y.2) • v = 0 := by
    calc
      (x.1 - y.1) • u + (x.2 - y.2) • v =
          (x.1 • u + x.2 • v) - (y.1 • u + y.2 • v) := by
            simp only [sub_smul]
            abel
      _ = 0 := sub_eq_zero.mpr hsum
  obtain ⟨hfirst, hsecond⟩ := hind _ _ hzero
  apply Prod.ext
  · exact sub_eq_zero.mp hfirst
  · exact sub_eq_zero.mp hsecond

/-- Equality in the affine plane forces equality of the branch coordinate. -/
theorem first_coordinate_eq_of_planePoint_eq
    {base u v : M} (hind : TwoDirectionIndependent (F := F) u v)
    {s t s' t' : F} (h : planePoint base u v s t = planePoint base u v s' t') :
    s = s' := by
  have hinj := planePoint_injective base u v hind
  have hpairs : (s, t) = (s', t') := hinj h
  exact congrArg Prod.fst hpairs

/-- If the received line has a nonzero component in the branch direction,
two challenges assigned to the same branch must coincide. -/
theorem branch_assignment_injOn_of_nonzero
    {B : Type*} {base u v : M} (hind : TwoDirectionIndependent (F := F) u v)
    (branchValue : B → F) (branch : F → B) (challenges : Finset F)
    (a b c d : F) (hc : c ≠ 0)
    (hmeet : ∀ γ ∈ challenges, ∃ t : F,
      planePoint base u v (a + γ * c) (b + γ * d) =
        planePoint base u v (branchValue (branch γ)) t) :
    Set.InjOn branch (challenges : Set F) := by
  intro γ hγ δ hδ hbranch
  obtain ⟨tγ, htγ⟩ := hmeet γ hγ
  obtain ⟨tδ, htδ⟩ := hmeet δ hδ
  have hcoordγ : a + γ * c = branchValue (branch γ) :=
    first_coordinate_eq_of_planePoint_eq hind htγ
  have hcoordδ : a + δ * c = branchValue (branch δ) :=
    first_coordinate_eq_of_planePoint_eq hind htδ
  have hmul : γ * c = δ * c := by
    apply add_left_cancel (a := a)
    rw [hcoordγ, hcoordδ, hbranch]
  exact mul_right_cancel₀ hc hmul

/-- A line moving in the branch coordinate has at most one challenge per
branch. -/
theorem challenge_card_le_branch_card_of_nonzero
    {B : Type*} [Fintype B] [DecidableEq B]
    {base u v : M} (hind : TwoDirectionIndependent (F := F) u v)
    (branchValue : B → F) (branch : F → B) (challenges : Finset F)
    (a b c d : F) (hc : c ≠ 0)
    (hmeet : ∀ γ ∈ challenges, ∃ t : F,
      planePoint base u v (a + γ * c) (b + γ * d) =
        planePoint base u v (branchValue (branch γ)) t) :
    challenges.card ≤ Fintype.card B := by
  classical
  have hinj := branch_assignment_injOn_of_nonzero hind branchValue branch challenges
    a b c d hc hmeet
  calc
    challenges.card = (challenges.image branch).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.univ : Finset B).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card B := Finset.card_univ

/-- If the received line has zero branch component, every point it realizes
belongs to the one branch value fixed by its affine offset. -/
theorem branch_value_eq_offset_of_zero
    {B : Type*} {base u v : M} (hind : TwoDirectionIndependent (F := F) u v)
    (branchValue : B → F) (branch : F → B) (challenges : Finset F)
    (a b c d : F) (hc : c = 0)
    (hmeet : ∀ γ ∈ challenges, ∃ t : F,
      planePoint base u v (a + γ * c) (b + γ * d) =
        planePoint base u v (branchValue (branch γ)) t) :
    ∀ γ ∈ challenges, branchValue (branch γ) = a := by
  intro γ hγ
  obtain ⟨t, ht⟩ := hmeet γ hγ
  have hcoord : a + γ * c = branchValue (branch γ) :=
    first_coordinate_eq_of_planePoint_eq hind ht
  simpa only [hc, mul_zero, add_zero] using hcoord.symm

/-- With an injective branch-value label, a zero branch direction supports at
most one branch, although it may carry many challenges inside that branch. -/
theorem branch_constant_on_of_zero
    {B : Type*} {base u v : M} (hind : TwoDirectionIndependent (F := F) u v)
    (branchValue : B → F) (hbranchValue : Function.Injective branchValue)
    (branch : F → B) (challenges : Finset F)
    (a b c d : F) (hc : c = 0)
    (hmeet : ∀ γ ∈ challenges, ∃ t : F,
      planePoint base u v (a + γ * c) (b + γ * d) =
        planePoint base u v (branchValue (branch γ)) t) :
    ∀ γ ∈ challenges, ∀ δ ∈ challenges, branch γ = branch δ := by
  intro γ hγ δ hδ
  apply hbranchValue
  rw [branch_value_eq_offset_of_zero hind branchValue branch challenges
      a b c d hc hmeet γ hγ,
    branch_value_eq_offset_of_zero hind branchValue branch challenges
      a b c d hc hmeet δ hδ]

/-- Exact cap when the branch type consists of the four fourth roots. -/
theorem four_branch_challenge_cap
    {base u v : M} (hind : TwoDirectionIndependent (F := F) u v)
    (branchValue : Fin 4 → F) (branch : F → Fin 4) (challenges : Finset F)
    (a b c d : F) (hc : c ≠ 0)
    (hmeet : ∀ γ ∈ challenges, ∃ t : F,
      planePoint base u v (a + γ * c) (b + γ * d) =
        planePoint base u v (branchValue (branch γ)) t) :
    challenges.card ≤ 4 := by
  simpa using challenge_card_le_branch_card_of_nonzero hind branchValue branch challenges
    a b c d hc hmeet

def challengeThreshold : ℕ := 274980728111395088

theorem four_branches_below_challenge_threshold : 4 < challengeThreshold := by
  norm_num [challengeThreshold]

end ProximityPrize.SubmissionUpper.QuarticBranchLineGate

#print axioms ProximityPrize.SubmissionUpper.QuarticBranchLineGate.planePoint_injective
#print axioms ProximityPrize.SubmissionUpper.QuarticBranchLineGate.four_branch_challenge_cap
#print axioms ProximityPrize.SubmissionUpper.QuarticBranchLineGate.branch_constant_on_of_zero
