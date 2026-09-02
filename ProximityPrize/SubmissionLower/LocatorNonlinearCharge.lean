import ProximityPrize.SubmissionLower.D

/-!
# Certified nonlinear aggregate charging

This module isolates two nonlinear features used by the fixed-factor charge:

* an unbounded-knapsack lookup depending on slope, certified by a finite table;
* the sum of the quotient features `total / q`, bounded by the quotient of the
  aggregate total.

The generic theorems are independent of the concrete row.  The final section
instantiates them at slope capacity `22`, total capacity `3806`, and `q = 224`.
-/

namespace ProximityPrize.SubmissionLower.LocatorNonlinearCharge

open scoped BigOperators

set_option autoImplicit false

/-- A finite certificate for an unbounded slope-knapsack table.

`step` says that an item of every size `s ≤ cap` can be prepended to a packing
of capacity `cap - s`.  `mono` lets a packing with unused slope budget be
charged to the terminal table entry.  Quantification through `Fin` makes a
concrete certificate reducible to a small, kernel-checkable finite decision.
-/
def IsSlopeTable (maxSlope : ℕ) (lookup table : ℕ → ℕ) : Prop :=
  (∀ a b : Fin (maxSlope + 1), a.val ≤ b.val → table a.val ≤ table b.val) ∧
  (∀ cap : Fin (maxSlope + 1), ∀ s : Fin (cap.val + 1),
    lookup s.val + table (cap.val - s.val) ≤ table cap.val)

/-- A valid slope table bounds the lookup charge of any finite family whose
aggregate slope stays within the certified range. -/
theorem sum_lookup_le_table_of_sum_le
    {ι : Type} [DecidableEq ι]
    (maxSlope : ℕ) (lookup table : ℕ → ℕ)
    (hcert : IsSlopeTable maxSlope lookup table)
    (items : Finset ι) (slope : ι → ℕ)
    (hsum : (∑ i ∈ items, slope i) ≤ maxSlope) :
    (∑ i ∈ items, lookup (slope i)) ≤ table (∑ i ∈ items, slope i) := by
  classical
  induction items using Finset.induction_on with
  | empty => simp
  | @insert a items ha ih =>
      have hsum' : slope a + ∑ i ∈ items, slope i ≤ maxSlope := by
        simpa only [Finset.sum_insert ha] using hsum
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hrest : (∑ i ∈ items, slope i) ≤ maxSlope := by omega
      have hih := ih hrest
      let cap : Fin (maxSlope + 1) :=
        ⟨slope a + ∑ i ∈ items, slope i, by omega⟩
      let chosen : Fin (cap.val + 1) := ⟨slope a, by
        dsimp only [cap]
        omega⟩
      have hstep := hcert.2 cap chosen
      dsimp only [cap, chosen] at hstep
      have hsub : slope a + ∑ i ∈ items, slope i - slope a =
          ∑ i ∈ items, slope i := by omega
      rw [hsub] at hstep
      exact (Nat.add_le_add_left hih _).trans hstep

/-- Terminal form of `sum_lookup_le_table_of_sum_le`: unused capacity is
absorbed using the table's monotonicity certificate. -/
theorem sum_lookup_le_table_cap
    {ι : Type} [DecidableEq ι]
    (maxSlope : ℕ) (lookup table : ℕ → ℕ)
    (hcert : IsSlopeTable maxSlope lookup table)
    (items : Finset ι) (slope : ι → ℕ)
    (hsum : (∑ i ∈ items, slope i) ≤ maxSlope) :
    (∑ i ∈ items, lookup (slope i)) ≤ table maxSlope := by
  have hsumTable := sum_lookup_le_table_of_sum_le
    maxSlope lookup table hcert items slope hsum
  let used : Fin (maxSlope + 1) := ⟨∑ i ∈ items, slope i, by omega⟩
  let full : Fin (maxSlope + 1) := ⟨maxSlope, by omega⟩
  exact hsumTable.trans (hcert.1 used full hsum)

/-- Natural-number floor division is superadditive over a finite sum. -/
theorem sum_div_le_div_sum
    {ι : Type} [DecidableEq ι]
    (items : Finset ι) (total : ι → ℕ) (q : ℕ) :
    (∑ i ∈ items, total i / q) ≤ (∑ i ∈ items, total i) / q := by
  classical
  induction items using Finset.induction_on with
  | empty => simp
  | @insert a items ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (Nat.add_le_add_left ih _).trans
        (Nat.add_div_le_add_div (total a) (∑ i ∈ items, total i) q)

/-! ## Concrete `q = 224`, slope-22 certificate -/

abbrev maxSlope : ℕ := 22
abbrev totalCap : ℕ := 3806
abbrev middleCap : ℕ := 99
abbrev q : ℕ := 224

abbrev wT : ℕ := 1000000
abbrev wY : ℕ := 261576
abbrev wFloor : ℕ := 2110711

/-- Nonlinear slope bonus.  Unlisted slopes carry no bonus. -/
def slopeBonus : ℕ → ℕ
  | 7 => 57487179
  | 8 => 114974357
  | 9 => 43904444
  | 10 => 3998474
  | _ => 0

/-- Unbounded-knapsack values for capacities `0, …, 22`.  The table is
monotone, so each entry permits unused capacity. -/
def slopeTable : ℕ → ℕ
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => 0
  | 7 => 57487179
  | 8 | 9 | 10 | 11 | 12 | 13 => 114974357
  | 14 => 114974358
  | 15 => 172461536
  | 16 | 17 | 18 | 19 | 20 | 21 => 229948714
  | _ => 229948715

abbrev slopeKnapsackCap : ℕ := 229948715

/-- The finite table is a complete certificate for all slope capacities up to
`22`.  This checks only `23²` tiny natural-number inequalities. -/
theorem slopeTable_certified : IsSlopeTable maxSlope slopeBonus slopeTable := by
  unfold IsSlopeTable
  decide +kernel

theorem slopeTable_at_cap : slopeTable maxSlope = slopeKnapsackCap := by rfl

/-- The slope lookup is maximized by the packing `7 + 7 + 8`. -/
theorem slopeKnapsackCap_attained :
    slopeBonus 7 + slopeBonus 7 + slopeBonus 8 = slopeKnapsackCap := by decide

def nonlinearCharge (slope total : ℕ) : ℕ :=
  slopeBonus slope + wFloor * (total / q)

abbrev nonlinearCap : ℕ := slopeKnapsackCap + wFloor * (totalCap / q)

theorem nonlinearCap_exact : nonlinearCap = 263720091 := by decide

/-- Aggregate bound requested by the nonlinear feature: floor-total charging
and the finite slope lookup share only the two global support budgets. -/
theorem sum_nonlinearCharge_le
    {ι : Type} [DecidableEq ι]
    (items : Finset ι) (slope total : ι → ℕ)
    (hslope : (∑ i ∈ items, slope i) ≤ maxSlope)
    (htotal : (∑ i ∈ items, total i) ≤ totalCap) :
    (∑ i ∈ items, nonlinearCharge (slope i) (total i)) ≤ nonlinearCap := by
  have hs := sum_lookup_le_table_cap maxSlope slopeBonus slopeTable
    slopeTable_certified items slope hslope
  rw [slopeTable_at_cap] at hs
  have hdiv := sum_div_le_div_sum items total q
  have hdivCap : (∑ i ∈ items, total i / q) ≤ totalCap / q :=
    hdiv.trans (Nat.div_le_div_right htotal)
  simp only [nonlinearCharge, Finset.sum_add_distrib, ← Finset.mul_sum]
  exact Nat.add_le_add hs (Nat.mul_le_mul_left wFloor hdivCap)

/-- Full weight used by the intended fixed-factor consumer. -/
def charge (slope middle total : ℕ) : ℕ :=
  wT * total + wY * middle + nonlinearCharge slope total

abbrev capSum : ℕ :=
  wT * totalCap + wY * middleCap + nonlinearCap

theorem capSum_exact : capSum = 4095616115 := by decide

/-- Concrete aggregate theorem including the existing linear total and middle
coordinates. -/
theorem sum_charge_le
    {ι : Type} [DecidableEq ι]
    (items : Finset ι) (slope middle total : ι → ℕ)
    (hslope : (∑ i ∈ items, slope i) ≤ maxSlope)
    (hmiddle : (∑ i ∈ items, middle i) ≤ middleCap)
    (htotal : (∑ i ∈ items, total i) ≤ totalCap) :
    (∑ i ∈ items, charge (slope i) (middle i) (total i)) ≤ capSum := by
  have hn := sum_nonlinearCharge_le items slope total hslope htotal
  simp only [charge, Finset.sum_add_distrib, ← Finset.mul_sum]
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left wT htotal)
      (Nat.mul_le_mul_left wY hmiddle)) hn

end ProximityPrize.SubmissionLower.LocatorNonlinearCharge
