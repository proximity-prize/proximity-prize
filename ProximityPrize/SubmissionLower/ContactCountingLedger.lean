import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactImplicitLiftParameters

/-!
# Finite-family arithmetic for the frozen conservative counting ledger

Model label: gpt-5.

All geometric branch estimates are EXPLICIT inputs in this module. The
proofs establish linearity, the coordinatewise maximum envelope, finite
aggregation, and the finish into the already verified conservative
ContactAlignmentParameters / ContactImplicitLiftParameters numerators.

The implicit bound permits the older nonnegative algebraic/isolated
padding. No new geometric estimate or complete alignment claim is made.
-/

namespace ProximityPrize.SubmissionLower.ContactCountingLedger

open ContactAlignmentParameters ContactImplicitLiftParameters
open scoped BigOperators

def addVector (a b : DegreeVector) : DegreeVector :=
  ⟨a.y + b.y, a.r + b.r, a.z + b.z⟩

def scaleVector (c : ℕ) (v : DegreeVector) : DegreeVector :=
  ⟨c * v.y, c * v.r, c * v.z⟩

def sumVector {I : Type} [Fintype I] (v : I → DegreeVector) : DegreeVector :=
  ⟨∑ i, (v i).y, ∑ i, (v i).r, ∑ i, (v i).z⟩

def vectorLE (a b : DegreeVector) : Prop := a.y ≤ b.y ∧ a.r ≤ b.r ∧ a.z ≤ b.z

def dot (a b : DegreeVector) : ℕ := a.y * b.y + a.r * b.r + a.z * b.z

theorem dot_comm (a b : DegreeVector) : dot a b = dot b a := by
  simp only [dot]
  ring

theorem dot_mono_left {a b : DegreeVector} (c : DegreeVector) (h : vectorLE a b) :
    dot a c ≤ dot b c :=
  Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_right c.y h.1) (Nat.mul_le_mul_right c.r h.2.1))
    (Nat.mul_le_mul_right c.z h.2.2)

theorem dot_mono_right (a : DegreeVector) {b c : DegreeVector} (h : vectorLE b c) :
    dot a b ≤ dot a c := by
  rw [dot_comm a b, dot_comm a c]
  exact dot_mono_left a h

theorem dot_sum_left {I : Type} [Fintype I] (v : I → DegreeVector) (a : DegreeVector) :
    dot (sumVector v) a = ∑ i, dot (v i) a := by
  simp only [dot, sumVector, Finset.sum_add_distrib, Finset.sum_mul]

theorem dot_sum_right {I : Type} [Fintype I] (v : I → DegreeVector) (a : DegreeVector) :
    dot a (sumVector v) = ∑ i, dot a (v i) := by
  rw [dot_comm, dot_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  exact dot_comm (v i) a

theorem mixed_first_decomposition (v a b : DegreeVector) :
    mixed v a b = v.y * mixed unitY a b + v.r * mixed unitR a b + v.z * mixed unitZ a b := by
  simp only [mixed, unitY, unitR, unitZ]
  ring

theorem mixed_add_left (u v a b : DegreeVector) :
    mixed (addVector u v) a b = mixed u a b + mixed v a b := by
  simp only [mixed, addVector]
  ring

theorem mixed_scale_left (c : ℕ) (v a b : DegreeVector) :
    mixed (scaleVector c v) a b = c * mixed v a b := by
  simp only [mixed, scaleVector]
  ring

theorem mixed_sum_left {I : Type} [Fintype I] (v : I → DegreeVector) (a b : DegreeVector) :
    mixed (sumVector v) a b = ∑ i, mixed (v i) a b := by
  calc
    _ = dot (sumVector v) ⟨mixed unitY a b, mixed unitR a b, mixed unitZ a b⟩ :=
      mixed_first_decomposition _ _ _
    _ = ∑ i, dot (v i) ⟨mixed unitY a b, mixed unitR a b, mixed unitZ a b⟩ := dot_sum_left _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact (mixed_first_decomposition (v i) a b).symm

def cutCoefficients : DegreeVector :=
  ⟨cutNumerator unitY, cutNumerator unitR, cutNumerator unitZ⟩

def wholeCoefficients : DegreeVector :=
  ⟨wholeNumerator unitY, wholeNumerator unitR, wholeNumerator unitZ⟩

def envelopeCoefficients : DegreeVector :=
  ⟨max (cutNumerator unitY) (wholeNumerator unitY),
    max (cutNumerator unitR) (wholeNumerator unitR),
    max (cutNumerator unitZ) (wholeNumerator unitZ)⟩

def regularSurface : DegreeVector := ⟨yCap, slopeCap, seedTotalCap⟩

theorem cut_eq_dot (v : DegreeVector) : cutNumerator v = dot v cutCoefficients := by
  simp only [cutNumerator, cutCoefficients, dot, mixed, unitY, unitR, unitZ]
  ring

theorem whole_eq_dot (v : DegreeVector) : wholeNumerator v = dot v wholeCoefficients := by
  simp only [wholeNumerator, wholeCoefficients, dot, mixed, unitY, unitR, unitZ]
  ring

theorem cut_add (u v : DegreeVector) :
    cutNumerator (addVector u v) = cutNumerator u + cutNumerator v := by
  rw [cut_eq_dot, cut_eq_dot, cut_eq_dot]
  simp only [dot, addVector]
  ring

theorem whole_add (u v : DegreeVector) :
    wholeNumerator (addVector u v) = wholeNumerator u + wholeNumerator v := by
  rw [whole_eq_dot, whole_eq_dot, whole_eq_dot]
  simp only [dot, addVector]
  ring

theorem cut_scale (c : ℕ) (v : DegreeVector) :
    cutNumerator (scaleVector c v) = c * cutNumerator v := by
  rw [cut_eq_dot, cut_eq_dot]
  simp only [dot, scaleVector]
  ring

theorem whole_scale (c : ℕ) (v : DegreeVector) :
    wholeNumerator (scaleVector c v) = c * wholeNumerator v := by
  rw [whole_eq_dot, whole_eq_dot]
  simp only [dot, scaleVector]
  ring

theorem cut_sum {I : Type} [Fintype I] (v : I → DegreeVector) :
    cutNumerator (sumVector v) = ∑ i, cutNumerator (v i) := by
  rw [cut_eq_dot, dot_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  exact (cut_eq_dot (v i)).symm

theorem whole_sum {I : Type} [Fintype I] (v : I → DegreeVector) :
    wholeNumerator (sumVector v) = ∑ i, wholeNumerator (v i) := by
  rw [whole_eq_dot, dot_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  exact (whole_eq_dot (v i)).symm

theorem cut_le_envelope (v : DegreeVector) : cutNumerator v ≤ dot v envelopeCoefficients := by
  rw [cut_eq_dot]
  exact dot_mono_right v ⟨le_max_left _ _, le_max_left _ _, le_max_left _ _⟩

theorem whole_le_envelope (v : DegreeVector) : wholeNumerator v ≤ dot v envelopeCoefficients := by
  rw [whole_eq_dot]
  exact dot_mono_right v ⟨le_max_right _ _, le_max_right _ _, le_max_right _ _⟩

theorem max_branch_le_envelope (v : DegreeVector) :
    max (cutNumerator v) (wholeNumerator v) ≤ dot v envelopeCoefficients :=
  max_le (cut_le_envelope v) (whole_le_envelope v)

theorem regularNumerator_eq_dot : regularNumerator = dot regularSurface wholeCoefficients := rfl

/-- Every branch inequality remains an explicit input. -/
theorem sum_regular_max_bound {I : Type} [Fintype I]
    (count : I → ℕ) (v : I → DegreeVector)
    (hy : (∑ i, (v i).y) ≤ yCap) (hr : (∑ i, (v i).r) ≤ slopeCap)
    (hz : (∑ i, (v i).z) ≤ seedTotalCap)
    (hcount : ∀ i, count i * gap ^ 2 ≤ wholeNumerator (v i)) :
    (∑ i, count i) * gap ^ 2 ≤ regularNumerator := by
  calc
    _ = ∑ i, count i * gap ^ 2 := Finset.sum_mul _ _ _
    _ ≤ ∑ i, dot (v i) wholeCoefficients := by
      apply Finset.sum_le_sum
      intro i _
      rw [← whole_eq_dot]
      exact hcount i
    _ = dot (sumVector v) wholeCoefficients := (dot_sum_left _ _).symm
    _ ≤ dot regularSurface wholeCoefficients := dot_mono_left _ ⟨hy, hr, hz⟩
    _ = regularNumerator := rfl

theorem sum_regular_branch_bound {I : Type} [Fintype I]
    (count : I → ℕ) (v : I → DegreeVector)
    (hy : (∑ i, (v i).y) ≤ yCap) (hr : (∑ i, (v i).r) ≤ slopeCap)
    (hz : (∑ i, (v i).z) ≤ seedTotalCap)
    (hcount : ∀ i, count i * gap ^ 2 ≤ wholeNumerator (v i)) :
    (∑ i, count i) * gap ^ 2 ≤ regularNumerator := by
  apply sum_regular_max_bound count v hy hr hz
  exact hcount

theorem sum_regular_numeric_caps {I : Type} [Fintype I]
    (count : I → ℕ) (v : I → DegreeVector)
    (hy : (∑ i, (v i).y) ≤ 25) (hr : (∑ i, (v i).r) ≤ 5)
    (hz : (∑ i, (v i).z) ≤ 176)
    (hcount : ∀ i, count i * gap ^ 2 ≤ wholeNumerator (v i)) :
    (∑ i, count i) * gap ^ 2 ≤ regularNumerator := by
  exact sum_regular_branch_bound count v
    (by simpa only [parameter_values.2.1] using hy)
    (by simpa only [slopeCap] using hr)
    (by simpa only [seedTotalCap] using hz) hcount

def implicitAggregateCost : DegreeVector :=
  ⟨algebraicCap, 2 * implicitYCap * algebraicCap, implicitYCap⟩

def implicitCoefficients : DegreeVector :=
  ⟨(n - w) * liftedAgreement.y, (n - w) * liftedAgreement.r,
    (n - w) * liftedAgreement.z + (errors + 1) * gap⟩

def implicitCoreNumerator : ℕ :=
  (n - w) * mixed liftedSurface implicitCut liftedAgreement +
    (errors + 1) * gap * mixed liftedSurface implicitCut unitZ

theorem implicit_bound_eq_dot (v : DegreeVector) :
    (n - w) * dot liftedAgreement v + (errors + 1) * gap * v.z =
      dot v implicitCoefficients := by
  simp only [implicitCoefficients, dot]
  ring

theorem implicit_aggregate_eq_core :
    dot implicitAggregateCost implicitCoefficients = implicitCoreNumerator := by
  simp only [implicitAggregateCost, implicitCoefficients, implicitCoreNumerator,
    dot, mixed, liftedSurface, implicitCut, unitZ]
  ring

/-- The geometric per-pair bound and actual pair-degree sums are inputs;
this theorem performs only their exact finite aggregation. -/
theorem sum_implicit_counts_bound {I : Type} [Fintype I]
    (count : I → ℕ) (cost : I → DegreeVector)
    (hy : (∑ i, (cost i).y) ≤ algebraicCap)
    (hr : (∑ i, (cost i).r) ≤ 2 * implicitYCap * algebraicCap)
    (hz : (∑ i, (cost i).z) ≤ implicitYCap)
    (hcount : ∀ i, count i * gap ≤
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
    _ = dot (sumVector cost) implicitCoefficients := (dot_sum_left _ _).symm
    _ ≤ dot implicitAggregateCost implicitCoefficients := dot_mono_left _ ⟨hy, hr, hz⟩
    _ = implicitCoreNumerator := implicit_aggregate_eq_core

/-- Exact identity exposing the unused nonnegative legacy padding. -/
theorem lifted_singular_padding :
    liftedSingularNumerator =
      (implicitCoreNumerator + 2 * algebraicCap ^ 2 * gap) +
        gap * (algebraicCap + mixed liftedSurface implicitCut liftedLastTail) := by
  simp only [liftedSingularNumerator, implicitCoreNumerator]
  ring

theorem implicit_with_exceptions_bound {I : Type} [Fintype I]
    (count : I → ℕ) (cost : I → DegreeVector) (exceptions : ℕ)
    (hy : (∑ i, (cost i).y) ≤ algebraicCap)
    (hr : (∑ i, (cost i).r) ≤ 2 * implicitYCap * algebraicCap)
    (hz : (∑ i, (cost i).z) ≤ implicitYCap)
    (hcount : ∀ i, count i * gap ≤
      (n - w) * dot liftedAgreement (cost i) +
        (errors + 1) * gap * (cost i).z)
    (hexceptions : exceptions ≤ 2 * algebraicCap ^ 2) :
    ((∑ i, count i) + exceptions) * gap ≤ liftedSingularNumerator := by
  have hmain := sum_implicit_counts_bound count cost hy hr hz hcount
  calc
    _ = (∑ i, count i) * gap + exceptions * gap := Nat.add_mul _ _ _
    _ ≤ implicitCoreNumerator + 2 * algebraicCap ^ 2 * gap :=
      Nat.add_le_add hmain (Nat.mul_le_mul_right gap hexceptions)
    _ ≤ liftedSingularNumerator := by
      rw [lifted_singular_padding]
      exact Nat.le_add_right _ _

theorem combined_scaled_bound (regularCount implicitCount exceptions : ℕ)
    (hregular : regularCount * gap ^ 2 ≤ regularNumerator)
    (himplicit : (implicitCount + exceptions) * gap ≤ liftedSingularNumerator) :
    (regularCount + implicitCount + exceptions) * gap ^ 2 ≤ liftedTotalNumerator := by
  calc
    _ = regularCount * gap ^ 2 + ((implicitCount + exceptions) * gap) * gap := by ring
    _ ≤ regularNumerator + liftedSingularNumerator * gap :=
      Nat.add_le_add hregular (Nat.mul_le_mul_right gap himplicit)
    _ = liftedTotalNumerator := by
      simp only [liftedTotalNumerator]
      ring

theorem below_budget_of_lifted_scaled_bound (cardinality : ℕ)
    (h : cardinality * gap ^ 2 ≤ liftedTotalNumerator) : cardinality < alignmentBudget := by
  exact Nat.lt_of_mul_lt_mul_right (h.trans_lt lifted_strict_budget)

/-- Conditional finite-family arithmetic finish; all branch-count and
cover hypotheses remain explicit and must come from the geometric proof. -/
theorem final_family_ledger {I J : Type} [Fintype I] [Fintype J]
    (regularCount : I → ℕ) (v : I → DegreeVector)
    (implicitCount : J → ℕ) (cost : J → DegreeVector) (exceptions cardinality : ℕ)
    (hregularY : (∑ i, (v i).y) ≤ 25) (hregularR : (∑ i, (v i).r) ≤ 5)
    (hregularZ : (∑ i, (v i).z) ≤ 176)
    (hregular : ∀ i, regularCount i * gap ^ 2 ≤ wholeNumerator (v i))
    (hcostY : (∑ i, (cost i).y) ≤ algebraicCap)
    (hcostR : (∑ i, (cost i).r) ≤ 2 * implicitYCap * algebraicCap)
    (hcostZ : (∑ i, (cost i).z) ≤ implicitYCap)
    (himplicit : ∀ i, implicitCount i * gap ≤
      (n - w) * dot liftedAgreement (cost i) +
        (errors + 1) * gap * (cost i).z)
    (hexceptions : exceptions ≤ 2 * algebraicCap ^ 2)
    (hcover : cardinality ≤ (∑ i, regularCount i) + (∑ i, implicitCount i) + exceptions) :
    cardinality < alignmentBudget := by
  have hreg := sum_regular_numeric_caps regularCount v hregularY hregularR hregularZ hregular
  have himp := implicit_with_exceptions_bound implicitCount cost exceptions
    hcostY hcostR hcostZ himplicit hexceptions
  have hscaled := combined_scaled_bound (∑ i, regularCount i) (∑ i, implicitCount i)
    exceptions hreg himp
  exact below_budget_of_lifted_scaled_bound cardinality
    ((Nat.mul_le_mul_right (gap ^ 2) hcover).trans hscaled)

end ProximityPrize.SubmissionLower.ContactCountingLedger

#print axioms ProximityPrize.SubmissionLower.ContactCountingLedger.mixed_first_decomposition
#print axioms ProximityPrize.SubmissionLower.ContactCountingLedger.mixed_add_left
#print axioms ProximityPrize.SubmissionLower.ContactCountingLedger.mixed_scale_left
#print axioms ProximityPrize.SubmissionLower.ContactCountingLedger.mixed_sum_left
#print axioms ProximityPrize.SubmissionLower.ContactCountingLedger.cut_eq_dot
#print axioms ProximityPrize.SubmissionLower.ContactCountingLedger.whole_eq_dot
#print axioms ProximityPrize.SubmissionLower.ContactCountingLedger.cut_add
#print axioms ProximityPrize.SubmissionLower.ContactCountingLedger.whole_add
#print axioms ProximityPrize.SubmissionLower.ContactCountingLedger.cut_scale
#print axioms ProximityPrize.SubmissionLower.ContactCountingLedger.whole_scale
#print axioms ProximityPrize.SubmissionLower.ContactCountingLedger.cut_sum
#print axioms ProximityPrize.SubmissionLower.ContactCountingLedger.whole_sum
#print axioms ProximityPrize.SubmissionLower.ContactCountingLedger.max_branch_le_envelope
#print axioms ProximityPrize.SubmissionLower.ContactCountingLedger.sum_regular_branch_bound
#print axioms ProximityPrize.SubmissionLower.ContactCountingLedger.sum_regular_numeric_caps
#print axioms ProximityPrize.SubmissionLower.ContactCountingLedger.implicit_aggregate_eq_core
#print axioms ProximityPrize.SubmissionLower.ContactCountingLedger.sum_implicit_counts_bound
#print axioms ProximityPrize.SubmissionLower.ContactCountingLedger.lifted_singular_padding
#print axioms ProximityPrize.SubmissionLower.ContactCountingLedger.implicit_with_exceptions_bound
#print axioms ProximityPrize.SubmissionLower.ContactCountingLedger.combined_scaled_bound
#print axioms ProximityPrize.SubmissionLower.ContactCountingLedger.below_budget_of_lifted_scaled_bound
#print axioms ProximityPrize.SubmissionLower.ContactCountingLedger.final_family_ledger
