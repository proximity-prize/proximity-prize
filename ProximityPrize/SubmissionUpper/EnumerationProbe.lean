/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ProximityPrize.SubmissionUpper.OrbitPencil

/-!
# A packed kernel-evaluated 32-label analogue of the 1024-fold key map

This file deliberately leaves the scored construction unchanged.  It counts
all seventeen-subsets of the thirty-one nonidentity powers of a primitive
32nd root in `ZMod 97`.  The state coordinates are the first Newton/root sum
modulo 97 and the product exponent modulo 32.

Each 97-cell root-sum row is packed into one natural number using base `2^32`
digits.  Every intermediate cell count is at most `2^31 < 2^32`, so digitwise
additions never carry between cells.  The first remote probe checks exact
population conservation.
-/

namespace ProximityPrize.SubmissionUpper.EnumerationProbe

abbrev Q32PackedTable := List ℕ

def q32Root (e : ℕ) : ℕ :=
  28 ^ (e + 1) % 97

def q32SplitAt {α : Type} : ℕ → List α → List α × List α
  | _, [] => ([], [])
  | 0, xs => ([], xs)
  | Nat.succ n, x :: xs =>
      match q32SplitAt n xs with
      | (left, right) => (x :: left, right)

def q32ZipWithAppend {α β γ : Type} (f : α → β → γ) :
    List α → List β → List β → List γ
  | [], _, _ => []
  | x :: xs, y :: ys, zs =>
      f x y :: q32ZipWithAppend f xs ys zs
  | xs, [], zs => List.zipWith f xs zs

def q32PackBase : ℕ :=
  (2 : ℕ) ^ 32

def q32DigitPow (n : ℕ) : ℕ :=
  (2 : ℕ) ^ (32 * n)

def q32PackedZeroTable : Q32PackedTable :=
  List.replicate 32 0

def q32PackedUnitTable : Q32PackedTable :=
  1 :: List.replicate 31 0

/-- Add `r` to the root-sum digit index modulo 97. -/
def q32RotatePackedRoot (r x : ℕ) : ℕ :=
  let cutPow := q32DigitPow (97 - r)
  let movePow := q32DigitPow r
  (x % cutPow) * movePow + x / cutPow

def q32PackedAddShiftTable (r s : ℕ)
    (curr prev : Q32PackedTable) : Q32PackedTable :=
  match q32SplitAt (32 - s) prev with
  | (prefix, suffix) =>
      q32ZipWithAppend
        (fun x y => x + q32RotatePackedRoot r y)
        curr suffix prefix

def q32PackedShiftOnlyTable (r s : ℕ)
    (T : Q32PackedTable) : Q32PackedTable :=
  match q32SplitAt (32 - s) T with
  | (prefix, suffix) =>
      (suffix ++ prefix).map (q32RotatePackedRoot r)

def q32PackedAdvanceTail (r s : ℕ) :
    Q32PackedTable → List Q32PackedTable → List Q32PackedTable
  | _, [] => []
  | prev, curr :: rest =>
      q32PackedAddShiftTable r s curr prev ::
        q32PackedAdvanceTail r s curr rest

def q32PackedLast : Q32PackedTable → List Q32PackedTable → Q32PackedTable
  | last, [] => last
  | _, next :: rest => q32PackedLast next rest

def q32PackedAdvance (r s : ℕ) :
    List Q32PackedTable → List Q32PackedTable
  | [] => []
  | first :: rest =>
      let same := first :: q32PackedAdvanceTail r s first rest
      if (first :: rest).length < 18 then
        same ++ [q32PackedShiftOnlyTable r s (q32PackedLast first rest)]
      else
        same

def q32PackedFinalLayers : List Q32PackedTable :=
  (List.range 31).foldl
    (fun layers e => q32PackedAdvance (q32Root e) (e + 1) layers)
    [q32PackedUnitTable]

def q32PackedLayerAt : ℕ → List Q32PackedTable → Q32PackedTable
  | _, [] => q32PackedZeroTable
  | 0, T :: _ => T
  | Nat.succ n, _ :: rest => q32PackedLayerAt n rest

def q32PackedFinalTable : Q32PackedTable :=
  q32PackedLayerAt 17 q32PackedFinalLayers

def q32PackedRowStats : ℕ → ℕ → ℕ × ℕ
  | 0, _ => (0, 0)
  | Nat.succ n, x =>
      let digit := x % q32PackBase
      match q32PackedRowStats n (x / q32PackBase) with
      | (total, largest) => (digit + total, Nat.max digit largest)

def q32PackedTableStats : List ℕ → ℕ × ℕ
  | [] => (0, 0)
  | row :: rest =>
      match q32PackedRowStats 97 row with
      | (rowTotal, rowMax) =>
          match q32PackedTableStats rest with
          | (restTotal, restMax) =>
              (rowTotal + restTotal, Nat.max rowMax restMax)

def q32PackedStats : ℕ × ℕ :=
  q32PackedTableStats q32PackedFinalTable

theorem q32_root_order_static :
    q32Root 15 = 96 ∧ q32Root 31 = 1 := by
  decide

theorem q32_pack_capacity_static :
    (2 : ℕ) ^ 31 < q32PackBase := by
  decide

theorem q32_pack_rotation_static :
    q32RotatePackedRoot 1 1 = q32PackBase ∧
      q32RotatePackedRoot 1 (q32DigitPow 96) = 1 := by
  decide

theorem q32_packed_shape_static :
    q32PackedZeroTable.length = 32 ∧ q32PackedUnitTable.length = 32 := by
  decide

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 1000000 in
theorem q32_packed_total_smoke :
    q32PackedStats.1 = Nat.choose 31 17 := by
  decide

end ProximityPrize.SubmissionUpper.EnumerationProbe
