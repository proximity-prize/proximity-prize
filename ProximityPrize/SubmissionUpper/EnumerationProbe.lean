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
every possible key.  A preceding remote smoke test established that this
histogram evaluates within the verifier budget, and a second run proved the
upper bounds 64 and 44.  This probe bisects the remaining interval by asking
whether every fibre has size at most 34.
-/

namespace ProximityPrize.SubmissionUpper.EnumerationProbe

def toyRoot (e : ℕ) : ℕ :=
  3 ^ (e + 1) % 17

def toyListKey (U : List ℕ) : ℕ × ℕ :=
  U.foldl
    (fun k e => ((k.1 + toyRoot e) % 17, (k.2 + e + 1) % 16))
    (0, 0)

def toyHistogram : List (List ℕ) :=
  (List.sublistsLen 8 (List.range 15)).foldl
    (fun h U =>
      let k := toyListKey U
      h.modify k.2 (fun row => row.modify k.1 Nat.succ))
    (List.replicate 16 (List.replicate 17 0))

def toyMaximum : ℕ :=
  toyHistogram.foldl (fun m row => row.foldl Nat.max m) 0

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem toyMaximum_le_34 : toyMaximum ≤ 34 := by
  decide

end ProximityPrize.SubmissionUpper.EnumerationProbe
