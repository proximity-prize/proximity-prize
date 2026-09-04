import ProximityPrize.SubmissionLower.LocatorPhase6803SourceSound
import ProximityPrize.SubmissionLower.LocatorPhase6803ReceiptCore

/-!
# Retuned initial-A complement ledger

The direct A-helper potential is linear.  This file proves that the greedy
complement encoded by the checked receipt majorizes the sum of all helpers
which leave the universal-factor branch, throughout the full 68.03 support
box `(total,middle,slope) = (6676,153,34)`.
-/

namespace ProximityPrize.SubmissionLower.LocatorInitialAComplement6803

open scoped BigOperators
open RCN095
open LocatorFactorAggregate LocatorPhase6800Oracle LocatorPhase6803Oracle
  LocatorPhase6803ReceiptCore

set_option autoImplicit false
set_option maxHeartbeats 5000000

/-- The receipt's greedy raw complement maximizes the wide A-potential among
all flags which can be added to `p` inside the selected-gcd support box. -/
theorem initialAWidePotential_le_complement (p n : FlagDegree)
    (ht : total p + total n ≤ 6676)
    (hy : middle p + middle n ≤ 153)
    (hr : p.all + n.all ≤ 34) :
    initialAWidePotential.eval n ≤
      LocatorPhase6803ReceiptCore.initialAComplement p := by
  have hnY : n.all ≤ middle n := by simp [middle]
  have hnT : middle n ≤ total n := by simp [middle, total]
  have hpY : p.all ≤ middle p := by simp [middle]
  have hpT : middle p ≤ total p := by simp [middle, total]
  simp only [LocatorPhase6803ReceiptCore.initialAComplement, Potential.eval,
    initialAWidePotential,
    rawFlag_total, rawFlag_middle, rawFlag_all]
  simp only [Nat.min_def]
  split_ifs <;> omega

/-- Additivity of the wide potential over an aggregate factor flag. -/
theorem sum_initialAWidePotential_eval {iota : Type} [DecidableEq iota]
    (s : Finset iota) (p : iota → FlagDegree) :
    (∑ i ∈ s, initialAWidePotential.eval (p i)) =
      initialAWidePotential.eval (sumFlag s p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sumFlag, Potential.eval, total, middle]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, ih]
      simp [sumFlag, Potential.eval, total, middle, hi]
      ring

/-- Aggregate every direct A-helper charge into the single correlated
complement term used by the checked receipt. -/
theorem initialA_helpers_sum_le_complement
    {iota : Type} [DecidableEq iota]
    (s : Finset iota) (p : iota → FlagDegree)
    (helper : iota → ℕ) (universal : FlagDegree)
    (hhelper : ∀ i ∈ s,
      helper i ≤ initialAWidePotential.eval (p i))
    (ht : total universal + ∑ i ∈ s, total (p i) ≤ 6676)
    (hy : middle universal + ∑ i ∈ s, middle (p i) ≤ 153)
    (hr : universal.all + ∑ i ∈ s, (p i).all ≤ 34) :
    (∑ i ∈ s, helper i) ≤
      LocatorPhase6803ReceiptCore.initialAComplement universal := by
  calc
    (∑ i ∈ s, helper i) ≤
        ∑ i ∈ s, initialAWidePotential.eval (p i) :=
      Finset.sum_le_sum (fun i hi ↦ hhelper i hi)
    _ = initialAWidePotential.eval (sumFlag s p) :=
      sum_initialAWidePotential_eval s p
    _ ≤ LocatorPhase6803ReceiptCore.initialAComplement universal := by
      apply initialAWidePotential_le_complement
      · simpa only [sumFlag_total] using ht
      · simpa only [sumFlag_middle] using hy
      · simpa only [sumFlag_all] using hr

end ProximityPrize.SubmissionLower.LocatorInitialAComplement6803
