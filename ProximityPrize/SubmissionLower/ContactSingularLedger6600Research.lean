import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactParameters6600Research

/-!
# Singular/implicit finite-family ledger for score 66

This isolates the unchanged implicit-pair and exceptional-seed arithmetic
from the new residual regular branch.  It aggregates component costs at
`(m,s,L,e) = (24,6,576,78777)` and exposes both the natural one-`gap` bound
and the exact `gap^2` contribution used by the final ledger.
-/

namespace ProximityPrize.SubmissionLower.ContactSingularLedger6600Research

open scoped BigOperators
open ContactParameters6600Research

def sumVector {I : Type} [Fintype I] (v : I -> DegreeVector) : DegreeVector :=
  ⟨∑ i, (v i).y, ∑ i, (v i).r, ∑ i, (v i).z⟩

def vectorLE (a b : DegreeVector) : Prop :=
  a.y ≤ b.y ∧ a.r ≤ b.r ∧ a.z ≤ b.z

def dot (a b : DegreeVector) : Nat :=
  a.y * b.y + a.r * b.r + a.z * b.z

theorem dot_mono_left {a b : DegreeVector} (c : DegreeVector)
    (h : vectorLE a b) : dot a c ≤ dot b c :=
  Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_right c.y h.1)
      (Nat.mul_le_mul_right c.r h.2.1))
    (Nat.mul_le_mul_right c.z h.2.2)

theorem dot_sum_left {I : Type} [Fintype I]
    (v : I -> DegreeVector) (a : DegreeVector) :
    dot (sumVector v) a = ∑ i, dot (v i) a := by
  simp only [dot, sumVector, Finset.sum_add_distrib, Finset.sum_mul]

def implicitAggregateCost : DegreeVector :=
  ⟨algebraicCap, 2 * implicitYCap * algebraicCap, implicitYCap⟩

def implicitCoefficients : DegreeVector :=
  ⟨(n - w) * liftedAgreement.y,
    (n - w) * liftedAgreement.r,
    (n - w) * liftedAgreement.z + (errors + 1) * gap⟩

def implicitCoreNumerator : Nat :=
  (n - w) * mixed liftedSurface implicitCut liftedAgreement +
    (errors + 1) * gap * mixed liftedSurface implicitCut unitZ

theorem implicit_bound_eq_dot (v : DegreeVector) :
    (n - w) * dot liftedAgreement v + (errors + 1) * gap * v.z =
      dot v implicitCoefficients := by
  simp only [implicitCoefficients, dot]
  ring

theorem implicit_aggregate_eq_core :
    dot implicitAggregateCost implicitCoefficients = implicitCoreNumerator := by
  simp only [implicitAggregateCost, implicitCoefficients,
    implicitCoreNumerator, dot, mixed, liftedSurface, implicitCut, unitZ]
  ring

theorem sum_implicit_counts_bound {I : Type} [Fintype I]
    (count : I -> Nat) (cost : I -> DegreeVector)
    (hy : (∑ i, (cost i).y) ≤ algebraicCap)
    (hr : (∑ i, (cost i).r) ≤ 2 * implicitYCap * algebraicCap)
    (hz : (∑ i, (cost i).z) ≤ implicitYCap)
    (hcount : forall i, count i * gap ≤
      (n - w) * dot liftedAgreement (cost i) +
        (errors + 1) * gap * (cost i).z) :
    (∑ i, count i) * gap ≤ implicitCoreNumerator := by
  calc
    _ = ∑ i, count i * gap := Finset.sum_mul _ _ _
    _ ≤ ∑ i, dot (cost i) implicitCoefficients := by
      apply Finset.sum_le_sum
      intro i _
      rw [← implicit_bound_eq_dot]
      exact hcount i
    _ = dot (sumVector cost) implicitCoefficients :=
      (dot_sum_left cost implicitCoefficients).symm
    _ ≤ dot implicitAggregateCost implicitCoefficients :=
      dot_mono_left implicitCoefficients ⟨hy, hr, hz⟩
    _ = implicitCoreNumerator := implicit_aggregate_eq_core

theorem retained_singular_padding :
    retainedSingularNumerator =
      implicitCoreNumerator +
        gap * (algebraicCap + 2 * algebraicCap ^ 2 +
          mixed liftedSurface implicitCut liftedLast) := by
  simp only [retainedSingularNumerator, implicitCoreNumerator]
  ring

theorem implicit_with_exceptions_bound {I : Type} [Fintype I]
    (count : I -> Nat) (cost : I -> DegreeVector) (exceptions : Nat)
    (hy : (∑ i, (cost i).y) ≤ algebraicCap)
    (hr : (∑ i, (cost i).r) ≤ 2 * implicitYCap * algebraicCap)
    (hz : (∑ i, (cost i).z) ≤ implicitYCap)
    (hcount : forall i, count i * gap ≤
      (n - w) * dot liftedAgreement (cost i) +
        (errors + 1) * gap * (cost i).z)
    (hexceptions : exceptions ≤ 2 * algebraicCap ^ 2) :
    ((∑ i, count i) + exceptions) * gap ≤ retainedSingularNumerator := by
  have hmain := sum_implicit_counts_bound count cost hy hr hz hcount
  calc
    _ = (∑ i, count i) * gap + exceptions * gap := Nat.add_mul _ _ _
    _ ≤ implicitCoreNumerator + 2 * algebraicCap ^ 2 * gap :=
      Nat.add_le_add hmain (Nat.mul_le_mul_right gap hexceptions)
    _ ≤ retainedSingularNumerator := by
      rw [retained_singular_padding]
      apply Nat.add_le_add_left
      calc
        2 * algebraicCap ^ 2 * gap = gap * (2 * algebraicCap ^ 2) := by ring
        _ ≤ gap * (algebraicCap + 2 * algebraicCap ^ 2 +
            mixed liftedSurface implicitCut liftedLast) :=
          Nat.mul_le_mul_left gap (by omega)

/-- Exact bridge from the natural one-`gap` singular estimate to the common
`gap^2` denominator used by the final score-66 ledger. -/
theorem implicit_with_exceptions_scaled_bound {I : Type} [Fintype I]
    (count : I -> Nat) (cost : I -> DegreeVector) (exceptions : Nat)
    (hy : (∑ i, (cost i).y) ≤ algebraicCap)
    (hr : (∑ i, (cost i).r) ≤ 2 * implicitYCap * algebraicCap)
    (hz : (∑ i, (cost i).z) ≤ implicitYCap)
    (hcount : forall i, count i * gap ≤
      (n - w) * dot liftedAgreement (cost i) +
        (errors + 1) * gap * (cost i).z)
    (hexceptions : exceptions ≤ 2 * algebraicCap ^ 2) :
    ((∑ i, count i) + exceptions) * gap ^ 2 ≤
      retainedSingularContribution := by
  have h := implicit_with_exceptions_bound count cost exceptions
    hy hr hz hcount hexceptions
  calc
    ((∑ i, count i) + exceptions) * gap ^ 2 =
        (((∑ i, count i) + exceptions) * gap) * gap := by ring
    _ ≤ retainedSingularNumerator * gap := Nat.mul_le_mul_right gap h
    _ = retainedSingularContribution := by
      simp only [retainedSingularContribution]
      ring

end ProximityPrize.SubmissionLower.ContactSingularLedger6600Research
