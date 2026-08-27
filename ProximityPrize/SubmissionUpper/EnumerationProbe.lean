/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.OrbitPencil

/-!
# A kernel-evaluated small analogue of the 1024-fold key map

This file deliberately leaves the scored construction unchanged.  It asks the
remote verifier to exhaust all eight-subsets of the fifteen nontrivial powers
of a primitive sixteenth root in `ZMod 17`, represented by natural residues.
The two key coordinates are the first Newton coefficient and the product
exponent modulo sixteen.  Candidates are traversed once while accumulating a
`16 × 17` histogram, so the expensive key calculation is not repeated for
every possible key.  The first remote probe deliberately checks only the
trivial upper bound `6435 = choose 15 8`; its purpose is to establish that the
histogram itself elaborates and evaluates within the verifier budget before a
meaningful bound is tried.
-/

namespace ProximityPrize.SubmissionUpper.EnumerationProbe

def toyCandidates : Finset (Finset ℕ) :=
  Finset.powersetCard 8 (Finset.range 15)

def toyRoot (e : ℕ) : ℕ :=
  3 ^ (e + 1) % 17

def toyTopOne (U : Finset ℕ) : ℕ :=
  (∑ e ∈ U, toyRoot e) % 17

def toyProduct (U : Finset ℕ) : ℕ :=
  (∑ e ∈ U, e + 1) % 16

def toyFiber (a s : ℕ) : Finset (Finset ℕ) :=
  toyCandidates.filter fun U => toyTopOne U = a ∧ toyProduct U = s

def toyListKey (U : Finset ℕ) : ℕ × ℕ :=
  (toyTopOne U, toyProduct U)

def toyHistogram : List (List ℕ) :=
  toyCandidates.toList.foldl
    (fun h U =>
      let k := toyListKey U
      h.modify k.2 (fun row => row.modify k.1 Nat.succ))
    (List.replicate 16 (List.replicate 17 0))

def toyMaximum : ℕ :=
  toyHistogram.foldl (fun m row => row.foldl Nat.max m) 0

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem toyMaximum_le_6435 : toyMaximum ≤ 6435 := by
  decide

end ProximityPrize.SubmissionUpper.EnumerationProbe
