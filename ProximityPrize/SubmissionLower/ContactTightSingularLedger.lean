import ProximityPrize.SubmissionLower.ContactSingularLedger

namespace ProximityPrize.SubmissionLower.ContactTightSingularLedger

open scoped BigOperators
open ContactParameters
open ContactSingularLedger

structure TightParameters where
  n : ℕ
  w : ℕ
  a : ℕ
  D : ℕ
  L : ℕ
  s : ℕ
  deriving DecidableEq

namespace TightParameters

def errors (P : TightParameters) : ℕ := P.n - P.a
def gap (P : TightParameters) : ℕ := P.a - P.w
def kappa (P : TightParameters) : ℕ := 2 * P.s - 1
def implicitYCap (P : TightParameters) : ℕ := (P.kappa * P.D - 1) / P.w
def algebraicCap (P : TightParameters) : ℕ := P.kappa * P.L

def agreement (P : TightParameters) : DegreeVector :=
  ⟨1 + 2 * P.w * P.implicitYCap,
    P.w,
    2 * P.w * P.algebraicCap + 1⟩

def aggregateCost (P : TightParameters) : DegreeVector :=
  ⟨P.algebraicCap,
    2 * P.implicitYCap * P.algebraicCap,
    P.implicitYCap⟩

def coefficients (P : TightParameters) : DegreeVector :=
  ⟨(P.n - P.w) * P.agreement.y,
    (P.n - P.w) * P.agreement.r,
    (P.n - P.w) * P.agreement.z + (P.errors + 1) * P.gap⟩

def coreNumerator (P : TightParameters) : ℕ :=
  (P.n - P.w) * dot P.agreement P.aggregateCost +
    (P.errors + 1) * P.gap * P.implicitYCap

def tightNumerator (P : TightParameters) : ℕ :=
  P.coreNumerator + 2 * P.algebraicCap ^ 2 * P.gap

def countCap (P : TightParameters) : ℕ := P.tightNumerator / P.gap

theorem bound_eq_dot (P : TightParameters) (v : DegreeVector) :
    (P.n - P.w) * dot P.agreement v +
        (P.errors + 1) * P.gap * v.z =
      dot v P.coefficients := by
  simp only [coefficients, errors, gap, dot]
  ring

theorem aggregate_eq_core (P : TightParameters) :
    dot P.aggregateCost P.coefficients = P.coreNumerator := by
  simp only [aggregateCost, coefficients, coreNumerator, dot]
  ring

theorem sum_counts_bound (P : TightParameters) {I : Type} [Fintype I]
    (count : I → ℕ) (cost : I → DegreeVector)
    (hy : (∑ i, (cost i).y) ≤ P.algebraicCap)
    (hr : (∑ i, (cost i).r) ≤ 2 * P.implicitYCap * P.algebraicCap)
    (hz : (∑ i, (cost i).z) ≤ P.implicitYCap)
    (hcount : ∀ i, count i * P.gap ≤
      (P.n - P.w) * dot P.agreement (cost i) +
        (P.errors + 1) * P.gap * (cost i).z) :
    (∑ i, count i) * P.gap ≤ P.coreNumerator := by
  calc
    _ = ∑ i, count i * P.gap := Finset.sum_mul _ _ _
    _ ≤ ∑ i, dot (cost i) P.coefficients := by
      apply Finset.sum_le_sum
      intro i _
      rw [← P.bound_eq_dot]
      exact hcount i
    _ = dot (sumVector cost) P.coefficients :=
      (dot_sum_left cost P.coefficients).symm
    _ ≤ dot P.aggregateCost P.coefficients :=
      dot_mono_left P.coefficients ⟨hy, hr, hz⟩
    _ = P.coreNumerator := P.aggregate_eq_core

theorem with_exceptions_bound (P : TightParameters) {I : Type} [Fintype I]
    (count : I → ℕ) (cost : I → DegreeVector) (exceptions : ℕ)
    (hy : (∑ i, (cost i).y) ≤ P.algebraicCap)
    (hr : (∑ i, (cost i).r) ≤ 2 * P.implicitYCap * P.algebraicCap)
    (hz : (∑ i, (cost i).z) ≤ P.implicitYCap)
    (hcount : ∀ i, count i * P.gap ≤
      (P.n - P.w) * dot P.agreement (cost i) +
        (P.errors + 1) * P.gap * (cost i).z)
    (hexceptions : exceptions ≤ 2 * P.algebraicCap ^ 2) :
    ((∑ i, count i) + exceptions) * P.gap ≤ P.tightNumerator := by
  have hmain := P.sum_counts_bound count cost hy hr hz hcount
  calc
    _ = (∑ i, count i) * P.gap + exceptions * P.gap := Nat.add_mul _ _ _
    _ ≤ P.coreNumerator + 2 * P.algebraicCap ^ 2 * P.gap :=
      Nat.add_le_add hmain (Nat.mul_le_mul_right P.gap hexceptions)
    _ = P.tightNumerator := rfl

theorem count_le_countCap (P : TightParameters) (count : ℕ)
    (hgap : 0 < P.gap) (hcount : count * P.gap ≤ P.tightNumerator) :
    count ≤ P.countCap := by
  exact (Nat.le_div_iff_mul_le hgap).mpr hcount

end TightParameters

end ProximityPrize.SubmissionLower.ContactTightSingularLedger
