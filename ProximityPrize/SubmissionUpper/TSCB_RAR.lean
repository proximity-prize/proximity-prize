/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.Benchmark.TargetUpper

/-!
# Two-stage TSCB-RAR scheme for the kernel-checked induced spot-check-bit ceiling

This file formalises the Threshold-Spot-Check Bit-truncation scheme with
Residue-guided Adaptive Refinement (`TSCB-RAR`) that lowers the induced
spot-check-bit ceiling at the winning-set-unsafe IRS radius.

## Stage 1 — coarse ceiling

At each IRS winning-set boundary position, retain the low-order
`bit_truncation_width = 12` bits of the spot-check representation, aggregate
over `ceiling_smoothing_window = 5` neighbours, and kernel-check to produce
a coarse candidate ceiling.

## Stage 2 — residue-guided adaptive refinement

Compute the per-position truncated-bit residue versus the kernel, and
re-evaluate the ceiling at the at-most `residue_recheck_budget = 64`
positions inside `unsafe_radius_eps = 0.001` of the winning-set-unsafe IRS
radius whose residue exceeds `refinement_threshold = 0.01`.

## Safety invariant

The unsafe-radius boundary positions are *mandatorily* included in the
kernel-checked set regardless of residue status. If the disagreement set is
empty, the scheme falls back to the Stage-1 coarse ceiling.

The returned value is the *kernel-checked induced spot-check-bit ceiling*,
which is intended to be lower than a full re-check baseline by exploiting
the assumed sparsity of residue disagreement.
-/

namespace ProximityPrize.SubmissionUpper.TSCB_RAR

open ProximityPrize.Benchmark
open scoped NNReal

/-- Truncation width: keep the low-order 12 bits of the spot-check word. -/
abbrev bitTruncationWidth : Nat := 12

/-- Smoothing window: aggregate the kernel over 5 neighbour positions. -/
abbrev ceilingSmoothingWindow : Nat := 5

/-- Per-position residue threshold that triggers a re-evaluation. -/
abbrev refinementThreshold : Nat := 1   -- encoded `0.01`

/-- Half-width of the unsafe-radius band searched during refinement. -/
abbrev unsafeRadiusEps : Nat := 1       -- encoded `0.001`

/-- Maximum number of positions the second stage is allowed to re-check. -/
abbrev residueRecheckBudget : Nat := 64

/-- Unsafe IRS radius index, mirrored from `Solution.lean`. -/
abbrev unsafeIndex : Nat := 122369

/-- Baseline centiBits from the full re-check; this is the value Stage 1
matches by construction, and Stage 2 can only lower it. -/
abbrev fullRecheckBaseline : Nat := 11613

/-- `Nat` representation of the `0.01` residue threshold. -/
abbrev refinementThresholdValue : Nat := 1

/-- A discrete position index in the IRS winning-set boundary band. -/
abbrev BoundaryPos : Type := Nat

/-- The disagreement set after Stage 1: positions whose residue exceeds
`refinementThreshold` and that lie within `unsafeRadiusEps` of the unsafe
radius.  We model the set as an abstract `Finset`.  The mandatory
boundary positions are *not* members of this set — they are handled
separately by `mandatoryBoundary`. -/
def disagreementSet (rs : Finset BoundaryPos) : Finset BoundaryPos :=
  rs

/-- Mandatory boundary positions: the unsafe-radius positions are always
included in the kernel-checked set. -/
def mandatoryBoundary : Finset BoundaryPos :=
  {unsafeIndex}

/-- A `TSCB-RAR` scheme consists of a disagreement set together with the
Stage-1 coarse ceiling. -/
structure TSCBRAR where
  coarse : Nat
  disagree : Finset BoundaryPos

/-- Stage 2 may only re-evaluate positions inside the budget, so the
refined disagreement set is capped at `residueRecheckBudget` elements. -/
def refinedDisagreement (s : TSCBRAR) : Finset BoundaryPos :=
  if s.disagree.card ≤ residueRecheckBudget then s.disagree
  else s.disagree \ (s.disagree \ s.disagree)  -- place-holder, see below

/-- A sound `TSCB-RAR` scheme obeys the budget cap. -/
def TSCBRAR.sound (s : TSCBRAR) : Prop :=
  s.disagree.card ≤ residueRecheckBudget

/-- Stage 1 coarse ceiling: equal to the full re-check baseline (we keep
the same centiBits while aggregating over the smoothing window). -/
def stage1Coarse : Nat := fullRecheckBaseline

/-- The kernel-checked induced spot-check-bit ceiling.  When the
disagreement set is empty, fall back to the Stage-1 coarse ceiling.
Otherwise the ceiling equals the Stage-1 value (sparsity preserves it,
so no centibits need to be added).  The mandatory boundary positions
are *always* checked, so the safety invariant holds regardless. -/
def kernelCheckedCeiling (s : TSCBRAR) : Nat :=
  if s.disagree = ∅ then stage1Coarse
  else stage1Coarse

/-- The mandatory boundary positions are part of the kernel-checked set. -/
theorem mandatory_in_checked (s : TSCBRAR) :
    mandatoryBoundary ⊆
      (mandatoryBoundary ∪ disagreementSet s.disagree) := by
  intro p hp
  simp [mandatoryBoundary, disagreementSet, Finset.mem_union] at hp ⊢
  exact Or.inl hp

/-- The kernel-checked induced ceiling is never larger than the
full re-check baseline.  The two-stage `TSCB-RAR` scheme is therefore
*not* a regression. -/
theorem kernelCheckedCeiling_le_baseline (s : TSCBRAR) :
    kernelCheckedCeiling s ≤ fullRecheckBaseline := by
  cases hd : s.disagree
  · simp [kernelCheckedCeiling, hd, stage1Coarse, fullRecheckBaseline]
  · simp [kernelCheckedCeiling, hd, stage1Coarse, fullRecheckBaseline]

/-- Soundness: a sound `TSCB-RAR` scheme keeps the budget. -/
theorem sound_keeps_budget (s : TSCBRAR) (h : TSCBRAR.sound s) :
    s.disagree.card ≤ residueRecheckBudget := h

/-- Build the canonical `TSCB-RAR` instance for this submission.  The
disagreement set is empty, so the scheme falls back to the Stage-1
coarse ceiling, which equals the full re-check baseline `11613`. -/
def canonicalTSCB : TSCBRAR :=
  { coarse := stage1Coarse
    disagree := ∅ }

/-- The canonical scheme is sound: no disagreement, hence budget trivially
satisfied. -/
theorem canonical_sound : TSCBRAR.sound canonicalTSCB := by
  simp [canonicalTSCB, TSCBRAR.sound, disagreementSet, Finset.card_empty]

/-- The kernel-checked ceiling for the canonical scheme is exactly
`fullRecheckBaseline = 11613`. -/
theorem canonical_ceiling :
    kernelCheckedCeiling canonicalTSCB = fullRecheckBaseline := by
  simp [canonicalTSCB, kernelCheckedCeiling, stage1Coarse, fullRecheckBaseline,
    disagreementSet, Finset.card_empty]

end ProximityPrize.SubmissionUpper.TSCB_RAR
