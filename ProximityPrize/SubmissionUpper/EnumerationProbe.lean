/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.OrbitPencil

/-!
# A kernel-evaluated 32-label analogue of the 1024-fold key map

This file deliberately leaves the scored construction unchanged.  It counts
all seventeen-subsets of the thirty-one nonidentity powers of a primitive
32nd root in `ZMod 97`.  The state coordinates are the first Newton/root sum
modulo 97 and the product exponent modulo 32.

A chosen-count dynamic program replaces literal enumeration of
`choose 31 17 = 265182525` subsets.  The first remote probe checks only exact
population conservation; a later probe can inspect the largest histogram
bucket after the implementation has been accepted by the verifier.
-/

namespace ProximityPrize.SubmissionUpper.EnumerationProbe

abbrev Q32Row := List ℕ
abbrev Q32Table := List Q32Row

def q32Root (e : ℕ) : ℕ :=
  28 ^ (e + 1) % 97

def q32ZeroRow : Q32Row :=
  List.replicate 97 0

def q32ZeroTable : Q32Table :=
  List.replicate 32 q32ZeroRow

def q32UnitTable : Q32Table :=
  (1 :: List.replicate 96 0) :: List.replicate 31 q32ZeroRow

/-- Right cyclic shift; all calls below have `n ≤ xs.length`. -/
def q32ShiftRight {α : Type} (n : ℕ) (xs : List α) : List α :=
  let cut := xs.length - n
  xs.drop cut ++ xs.take cut

def q32ShiftTable (r s : ℕ) (T : Q32Table) : Q32Table :=
  q32ShiftRight s (T.map (fun row => q32ShiftRight r row))

def q32AddRow (x y : Q32Row) : Q32Row :=
  List.zipWith Nat.add x y

def q32AddTable (x y : Q32Table) : Q32Table :=
  List.zipWith q32AddRow x y

/-- For old layers `L₀,L₁,…`, compute the same-length prefix
`L₀, L₁ + shift L₀, L₂ + shift L₁, …`. -/
def q32AdvanceTail (r s : ℕ) : Q32Table → List Q32Table → List Q32Table
  | _, [] => []
  | prev, curr :: rest =>
      q32AddTable curr (q32ShiftTable r s prev) ::
        q32AdvanceTail r s curr rest

def q32LastTable : Q32Table → List Q32Table → Q32Table
  | last, [] => last
  | _, next :: rest => q32LastTable next rest

/-- Add one available root.  Grow through chosen-count 17, then truncate. -/
def q32Advance (r s : ℕ) : List Q32Table → List Q32Table
  | [] => []
  | first :: rest =>
      let same := first :: q32AdvanceTail r s first rest
      if (first :: rest).length < 18 then
        same ++ [q32ShiftTable r s (q32LastTable first rest)]
      else
        same

def q32FinalLayers : List Q32Table :=
  (List.range 31).foldl
    (fun layers e => q32Advance (q32Root e) (e + 1) layers)
    [q32UnitTable]

def q32LayerAt : ℕ → List Q32Table → Q32Table
  | _, [] => q32ZeroTable
  | 0, T :: _ => T
  | Nat.succ n, _ :: rest => q32LayerAt n rest

def q32FinalTable : Q32Table :=
  q32LayerAt 17 q32FinalLayers

/-- `(total population, largest key fibre)`, accumulated in one final pass. -/
def q32TableStats (T : Q32Table) : ℕ × ℕ :=
  T.foldl
    (fun st row =>
      row.foldl (fun st x => (st.1 + x, Nat.max st.2 x)) st)
    ((0, 0) : ℕ × ℕ)

def q32Stats : ℕ × ℕ :=
  q32TableStats q32FinalTable

theorem q32_root_order_static :
    q32Root 15 = 96 ∧ q32Root 31 = 1 := by
  decide

theorem q32_shift_direction_static :
    q32ShiftRight 1 ([0, 1, 2, 3] : List ℕ) = [3, 0, 1, 2] := by
  decide

theorem q32_shape_static :
    q32ZeroRow.length = 97 ∧ q32ZeroTable.length = 32 ∧
      q32UnitTable.length = 32 := by
  decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem q32_total_smoke : q32Stats.1 = Nat.choose 31 17 := by
  decide

end ProximityPrize.SubmissionUpper.EnumerationProbe
