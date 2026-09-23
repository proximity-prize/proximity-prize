import ProximityPrize.SubmissionLower.LowerGeometry
namespace ProximityPrize.SubmissionLower.Lower80860.Initial
open scoped BigOperators
open RCN095 LocatorFactorAggregate
open LocatorPhase6800Oracle (Potential rawFlag rawFlag_all rawFlag_middle rawFlag_total
  sumFlag sumFlag_all sumFlag_middle sumFlag_total)
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def initialAPotential : Potential := ⟨9182745250, 5716429996169, 26789807578148⟩
def initialAComplement (p : FlagDegree) : ℕ :=
    let t := 10169 - total p
    let y := 185 - middle p
    let r := 40 - p.all
  let nr := min t (min y r)
  let t' := t - nr
  let y' := y - nr
  let nv := min t' y'
  initialAPotential.eval (rawFlag nr nv (t' - nv))

/-- The greedy complement is maximal for the A potential among all raw flags
that can be added to `p` inside the wide box. -/
theorem initialAPotential_le_complement (p n : FlagDegree)
    (ht : total p + total n ≤ 10169)
    (hy : middle p + middle n ≤ 185)
    (hr : p.all + n.all ≤ 40) :
    initialAPotential.eval n ≤ initialAComplement p := by
  have hnpY : n.all ≤ middle n := by simp [middle]
  have hnpT : middle n ≤ total n := by simp [middle, total]
  have hppY : p.all ≤ middle p := by simp [middle]
  have hppT : middle p ≤ total p := by simp [middle, total]
  simp only [initialAComplement, Potential.eval, initialAPotential,
    rawFlag_total, rawFlag_middle, rawFlag_all]
  simp only [Nat.min_def]
  split_ifs <;> omega
theorem sum_initialAPotential_eval {ι : Type} [DecidableEq ι] (s : Finset ι)
    (p : ι → FlagDegree) :
    (∑ i ∈ s, initialAPotential.eval (p i)) =
      initialAPotential.eval (sumFlag s p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sumFlag, Potential.eval, total, middle]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, ih]
      simp [sumFlag, Potential.eval, total, middle, hi]
      ring

/-- Aggregate direct-A helper ledger for the factors that leave the initial
split.  The exact greedy complement avoids the seven-trillion loss of three
independent cumulative-coordinate remainders. -/
theorem initialA_helpers_sum_le_complement
    {ι : Type} [DecidableEq ι] (s : Finset ι) (p : ι → FlagDegree)
    (helper : ι → ℕ)
    (universal : FlagDegree)
    (hhelper : ∀ i ∈ s, helper i ≤ initialAPotential.eval (p i))
    (ht : total universal + ∑ i ∈ s, total (p i) ≤ 10169)
    (hy : middle universal + ∑ i ∈ s, middle (p i) ≤ 185)
    (hr : universal.all + ∑ i ∈ s, (p i).all ≤ 40) :
    (∑ i ∈ s, helper i) ≤ initialAComplement universal := by
  calc
    (∑ i ∈ s, helper i) ≤ ∑ i ∈ s, initialAPotential.eval (p i) :=
      Finset.sum_le_sum (fun i hi => hhelper i hi)
    _ = initialAPotential.eval (sumFlag s p) := sum_initialAPotential_eval s p
    _ ≤ initialAComplement universal := by
      apply initialAPotential_le_complement
      · simpa only [sumFlag_total] using ht
      · simpa only [sumFlag_middle] using hy
      · simpa only [sumFlag_all] using hr


end ProximityPrize.SubmissionLower.Lower80860.Initial
