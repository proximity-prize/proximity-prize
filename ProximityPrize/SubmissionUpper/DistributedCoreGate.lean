/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Distributed-core obstruction for the 1024-fibre upper attack

One possible way to use all 256 outer labels is to distribute a fixed core of
at most 1023 roots among the outer fibres.  A weight-136 selector then gains
from the core only at the 120 labels outside the selector.  Reaching the first
`116.12` score gate requires at least 518 such extra roots.

The key observation is independent of how the roots are distributed.  Two
120-label complements which each carry at least 518 roots cannot be disjoint:
otherwise the degree-1023 core would contain at least 1036 roots.  Hence the
usable complements form an intersecting family.  Erdős--Ko--Rado caps such a
family by `choose 255 119`, exactly the old construction obtained by putting
the whole core in one excluded outer fibre.

This file proves the weighted-intersection implication and records the exact
benchmark arithmetic.  The EKR cardinality theorem is stated as a hypothesis
in the final consumer so that this upper-only file needs no import beyond the
protected upper target.  The independent audit applies the standard EKR
theorem at `(n,k)=(256,120)`.
-/

namespace ProximityPrize.SubmissionUpper.DistributedCoreGate

open scoped BigOperators

/-- Total core load carried by a set of outer labels. -/
def coreLoad {n : ℕ} (weight : Fin n → ℕ) (s : Finset (Fin n)) : ℕ :=
  ∑ i ∈ s, weight i

/-- Two complements above half the total core budget must intersect. -/
theorem heavy_complements_not_disjoint
    {n budget quota : ℕ} (weight : Fin n → ℕ)
    (A B : Finset (Fin n))
    (htotal : coreLoad weight Finset.univ ≤ budget)
    (hquota : budget < 2 * quota)
    (hA : quota ≤ coreLoad weight A)
    (hB : quota ≤ coreLoad weight B) :
    ¬Disjoint A B := by
  intro hdisjoint
  have hunion : coreLoad weight (A ∪ B) ≤ coreLoad weight Finset.univ := by
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hadd : coreLoad weight A + coreLoad weight B =
      coreLoad weight (A ∪ B) := by
    exact (Finset.sum_union hdisjoint).symm
  rw [← hadd] at hunion
  omega

/-- Every family cut out by a heavy-complement condition is pairwise
non-disjoint. -/
theorem heavy_family_pairwise_not_disjoint
    {n budget quota : ℕ} (weight : Fin n → ℕ)
    (family : Finset (Finset (Fin n)))
    (htotal : coreLoad weight Finset.univ ≤ budget)
    (hquota : budget < 2 * quota)
    (hheavy : ∀ A ∈ family, quota ≤ coreLoad weight A) :
    ∀ A ∈ family, ∀ B ∈ family, ¬Disjoint A B := by
  intro A hAfam B hBfam
  exact heavy_complements_not_disjoint weight A B htotal hquota
    (hheavy A hAfam) (hheavy B hBfam)

def outerLabelCount : ℕ := 256
def selectorWeight : ℕ := 136
def complementWeight : ℕ := 120
def coreDegreeBudget : ℕ := 1023
def improvementExtraRoots : ℕ := 518

def puncturedSelectorCount : ℕ :=
  1642763237966455131089379983394824266573028270959430944304016753768099919875

def baseFieldCardinality : ℕ := 2 ^ 31 - 2 ^ 24 + 1
def coarseKeySpaceCardinality : ℕ := 64 * baseFieldCardinality ^ 6
def challengeThreshold : ℕ := 274980728111395088
def coarseMeanCeil : ℕ := 274317364102044233

theorem benchmark_weight_receipt :
    outerLabelCount - selectorWeight = complementWeight := by
  norm_num [outerLabelCount, selectorWeight, complementWeight]

/-- The improvement quota is strictly more than half of the available fixed
core degree, which is the numerical input to the intersection theorem. -/
theorem benchmark_heavy_intersection_receipt :
    coreDegreeBudget < 2 * improvementExtraRoots := by
  norm_num [coreDegreeBudget, improvementExtraRoots]

set_option maxRecDepth 1000000 in
theorem punctured_selector_count_receipt :
    puncturedSelectorCount = Nat.choose 255 119 ∧
      puncturedSelectorCount = Nat.choose 255 136 := by
  constructor <;> rw [Nat.choose_eq_fast_choose] <;> decide

/-- Exact ceiling of the ordinary coarse-key mean on the largest family
allowed by EKR. -/
theorem coarse_mean_ceiling_receipt :
    coarseKeySpaceCardinality * (coarseMeanCeil - 1) <
        puncturedSelectorCount ∧
      puncturedSelectorCount ≤
        coarseKeySpaceCardinality * coarseMeanCeil := by
  norm_num [coarseKeySpaceCardinality, baseFieldCardinality,
    coarseMeanCeil, puncturedSelectorCount]

/-- Even the EKR-extremal family has ordinary coarse-key mean below the
inclusive challenge threshold. -/
theorem coarse_mean_below_challenge :
    puncturedSelectorCount ≤
      coarseKeySpaceCardinality * (challengeThreshold - 1) := by
  norm_num [puncturedSelectorCount, coarseKeySpaceCardinality,
    baseFieldCardinality, challengeThreshold]

/-- Consumer for the standard EKR bound.  Once the weighted condition has
made `family` intersecting, EKR supplies `family.card ≤ choose 255 119`; the
resulting raw family is still too small for an unconditional coarse-key
pigeonhole proof of a challenge-threshold fibre. -/
theorem distributed_core_family_below_pigeonhole
    (family : Finset (Finset (Fin outerLabelCount)))
    (hEKR : family.card ≤ Nat.choose 255 119) :
    family.card ≤
      coarseKeySpaceCardinality * (challengeThreshold - 1) := by
  rw [← punctured_selector_count_receipt.1] at hEKR
  exact hEKR.trans coarse_mean_below_challenge

end ProximityPrize.SubmissionUpper.DistributedCoreGate

#print axioms ProximityPrize.SubmissionUpper.DistributedCoreGate.heavy_complements_not_disjoint
#print axioms ProximityPrize.SubmissionUpper.DistributedCoreGate.heavy_family_pairwise_not_disjoint
#print axioms ProximityPrize.SubmissionUpper.DistributedCoreGate.distributed_core_family_below_pigeonhole
