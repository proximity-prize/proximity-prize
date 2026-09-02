import ProximityPrize.SubmissionLower.LocatorReplacementGridCore

/-!
# The extended coarse grid for the A-pair branch

A factor of the common divisor that fails to divide some A-kernel
reconstruction is counted by a direct coprime pair with that reconstruction.
Such a factor is only known to lie in the B box (slope at most `23`, ys weight
at most `110`, total at most `3922`), so its cell lives on a wider grid than
the A-restricted receipt grid.  The pair rate holds on every coarse box of
that grid, so no refinement is needed.
-/

namespace ProximityPrize.SubmissionLower.LocatorPairGrid

open RCN095 LocatorFactorAggregate LocatorReplacementGridData

/-- The direct-pair charge of a source on a box: the pair gates and the
weighted rate of the coprime witness count. -/
def PairFits (src : Source) (b : Box) : Prop :=
  PairGates (helperPair src b) ∧
    capSum * (helperPair src b).regularCountCap ≤ bound * b.weight

instance (src : Source) (b : Box) : Decidable (PairFits src b) := by
  unfold PairFits; infer_instance

abbrev ExtCell := Fin 23 × Fin 28 × Fin 31

def extR (c : ExtCell) : ℕ := c.1.val + 1
def extYlo (c : ExtCell) : ℕ := extR c + 4 * c.2.1.val
def extYhi (c : ExtCell) : ℕ := min 110 (extYlo c + 3)
def extTlo (c : ExtCell) : ℕ := 128 * c.2.2.val
def extThi (c : ExtCell) : ℕ := min 3922 (extTlo c + 127)
def extBox (c : ExtCell) : Box :=
  ⟨extR c, extYlo c, extYhi c, extTlo c, extThi c⟩

/-- Validity on the wide grid (the `Box.valid` predicate is tied to the
    A-restricted caps, so the wide grid carries its own). -/
def ExtValid (c : ExtCell) : Prop :=
  extR c ≤ extYlo c ∧ extYlo c ≤ extYhi c ∧ extYlo c ≤ extThi c ∧
    extTlo c ≤ extThi c

instance (c : ExtCell) : Decidable (ExtValid c) := by
  unfold ExtValid; infer_instance

/-- The wide-grid receipt of one slope row.  Rows are decided separately so
that each kernel evaluation stays small. -/
def ExtRowReceipt (ri : Fin 23) : Prop :=
  ∀ (cy : Fin 28) (ct : Fin 31),
    ExtValid (ri, cy, ct) → PairFits sourceA (extBox (ri, cy, ct))

instance (ri : Fin 23) : Decidable (ExtRowReceipt ri) := by
  unfold ExtRowReceipt; infer_instance

set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem ext_row_00 : ExtRowReceipt 0 := by decide +kernel

theorem ext_row_01 : ExtRowReceipt 1 := by decide +kernel

theorem ext_row_02 : ExtRowReceipt 2 := by decide +kernel

theorem ext_row_03 : ExtRowReceipt 3 := by decide +kernel

theorem ext_row_04 : ExtRowReceipt 4 := by decide +kernel

theorem ext_row_05 : ExtRowReceipt 5 := by decide +kernel

theorem ext_row_06 : ExtRowReceipt 6 := by decide +kernel

theorem ext_row_07 : ExtRowReceipt 7 := by decide +kernel

theorem ext_row_08 : ExtRowReceipt 8 := by decide +kernel

theorem ext_row_09 : ExtRowReceipt 9 := by decide +kernel

theorem ext_row_10 : ExtRowReceipt 10 := by decide +kernel

theorem ext_row_11 : ExtRowReceipt 11 := by decide +kernel

theorem ext_row_12 : ExtRowReceipt 12 := by decide +kernel

theorem ext_row_13 : ExtRowReceipt 13 := by decide +kernel

theorem ext_row_14 : ExtRowReceipt 14 := by decide +kernel

theorem ext_row_15 : ExtRowReceipt 15 := by decide +kernel

theorem ext_row_16 : ExtRowReceipt 16 := by decide +kernel

theorem ext_row_17 : ExtRowReceipt 17 := by decide +kernel

theorem ext_row_18 : ExtRowReceipt 18 := by decide +kernel

theorem ext_row_19 : ExtRowReceipt 19 := by decide +kernel

theorem ext_row_20 : ExtRowReceipt 20 := by decide +kernel

theorem ext_row_21 : ExtRowReceipt 21 := by decide +kernel

theorem ext_row_22 : ExtRowReceipt 22 := by decide +kernel

theorem ext_rows (ri : Fin 23) : ExtRowReceipt ri := by
  fin_cases ri
  · exact ext_row_00
  · exact ext_row_01
  · exact ext_row_02
  · exact ext_row_03
  · exact ext_row_04
  · exact ext_row_05
  · exact ext_row_06
  · exact ext_row_07
  · exact ext_row_08
  · exact ext_row_09
  · exact ext_row_10
  · exact ext_row_11
  · exact ext_row_12
  · exact ext_row_13
  · exact ext_row_14
  · exact ext_row_15
  · exact ext_row_16
  · exact ext_row_17
  · exact ext_row_18
  · exact ext_row_19
  · exact ext_row_20
  · exact ext_row_21
  · exact ext_row_22

def ExtReceipt : Prop := ∀ c : ExtCell, ExtValid c → PairFits sourceA (extBox c)

theorem ext_receipt : ExtReceipt := by
  intro c hv
  rcases c with ⟨ri, cy, ct⟩
  exact ext_rows ri cy ct hv

def extCellOf (p : FlagDegree) (hslo : 1 ≤ p.all) (hshi : p.all ≤ 23)
    (hy : middle p ≤ 110) (ht : total p ≤ 3922) : ExtCell :=
  (⟨p.all - 1, by omega⟩,
    ⟨(middle p - p.all) / 4, by
      have := all_le_middle p
      omega⟩,
    ⟨total p / 128, by omega⟩)

theorem extCellOf_bounds (p : FlagDegree) (hslo : 1 ≤ p.all)
    (hshi : p.all ≤ 23) (hy : middle p ≤ 110) (ht : total p ≤ 3922) :
    p.all = extR (extCellOf p hslo hshi hy ht) ∧
      extYlo (extCellOf p hslo hshi hy ht) ≤ middle p ∧
      middle p ≤ extYhi (extCellOf p hslo hshi hy ht) ∧
      extTlo (extCellOf p hslo hshi hy ht) ≤ total p ∧
      total p ≤ extThi (extCellOf p hslo hshi hy ht) := by
  have hmy := all_le_middle p
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change p.all = p.all - 1 + 1; omega
  · change (p.all - 1 + 1) + 4 * ((middle p - p.all) / 4) ≤ middle p; omega
  · change middle p ≤ min 110 ((p.all - 1 + 1) + 4 * ((middle p - p.all) / 4) + 3)
    exact le_min hy (by omega)
  · change 128 * (total p / 128) ≤ total p; omega
  · change total p ≤ min 3922 (128 * (total p / 128) + 127)
    exact le_min ht (by omega)

theorem extValid_of (p : FlagDegree) (hslo : 1 ≤ p.all)
    (hshi : p.all ≤ 23) (hy : middle p ≤ 110) (ht : total p ≤ 3922) :
    ExtValid (extCellOf p hslo hshi hy ht) := by
  have hb := extCellOf_bounds p hslo hshi hy ht
  have hmt := middle_le_total p
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Nat.le_add_right _ _
  · exact le_min (hb.2.1.trans hy) (Nat.le_add_right _ _)
  · exact hb.2.1.trans (hmt.trans hb.2.2.2.2)
  · exact le_min (hb.2.2.2.1.trans ht) (Nat.le_add_right _ _)

theorem ext_pair_fits (p : FlagDegree) (hslo : 1 ≤ p.all)
    (hshi : p.all ≤ 23) (hy : middle p ≤ 110) (ht : total p ≤ 3922) :
    PairFits sourceA (extBox (extCellOf p hslo hshi hy ht)) :=
  ext_receipt _ (extValid_of p hslo hshi hy ht)

end ProximityPrize.SubmissionLower.LocatorPairGrid
