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
exponent modulo sixteen.  The assertion rules out a fibre larger than 32 in
this small model (the mean fibre size is about 23.7).
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

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
theorem toy_key_fibres_le_32 :
    ∀ a ∈ Finset.range 17, ∀ s ∈ Finset.range 16, (toyFiber a s).card ≤ 32 := by
  decide

end ProximityPrize.SubmissionUpper.EnumerationProbe
