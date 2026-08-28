import ProximityPrize.Benchmark.TargetLower

/-!
# Parameter-free tight aggregation of a finite core and exceptions

This is the arithmetic seam used to remove historical singular-ledger
padding.  It deliberately knows nothing about a particular score row: a
row-specific geometric theorem supplies the finite-family core, and the
exception theorem supplies its exact cap.
-/

namespace ProximityPrize.SubmissionLower.ContactTightSingularAggregationResearch

open scoped BigOperators

/-- Add an exceptional family to an already aggregated one-gap core without
introducing any unrelated positive padding. -/
theorem tight_exception_bound
    {I : Type} [Fintype I]
    (count : I → ℕ) (exceptions gap core exceptionCap : ℕ)
    (hcore : (∑ i, count i) * gap ≤ core)
    (hexceptions : exceptions ≤ exceptionCap) :
    ((∑ i, count i) + exceptions) * gap ≤
      core + exceptionCap * gap := by
  calc
    ((∑ i, count i) + exceptions) * gap =
        (∑ i, count i) * gap + exceptions * gap := Nat.add_mul _ _ _
    _ ≤ core + exceptionCap * gap :=
      Nat.add_le_add hcore (Nat.mul_le_mul_right gap hexceptions)

/-- Common-denominator form of `tight_exception_bound`. -/
theorem tight_exception_scaled_bound
    {I : Type} [Fintype I]
    (count : I → ℕ) (exceptions gap core exceptionCap : ℕ)
    (hcore : (∑ i, count i) * gap ≤ core)
    (hexceptions : exceptions ≤ exceptionCap) :
    ((∑ i, count i) + exceptions) * gap ^ 2 ≤
      gap * (core + exceptionCap * gap) := by
  have h := tight_exception_bound count exceptions gap core exceptionCap
    hcore hexceptions
  calc
    ((∑ i, count i) + exceptions) * gap ^ 2 =
        (((∑ i, count i) + exceptions) * gap) * gap := by ring
    _ ≤ (core + exceptionCap * gap) * gap := Nat.mul_le_mul_right gap h
    _ = gap * (core + exceptionCap * gap) := by ring

end ProximityPrize.SubmissionLower.ContactTightSingularAggregationResearch
