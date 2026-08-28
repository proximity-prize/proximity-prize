import ProximityPrize.SubmissionLower.ContactShearParameters6533

/-!
# Finite-family ledger for the 65.67 global-shear row

This file performs only the linear finite-family aggregation.  Its regular
branch charges the exact common-shear correction
`2 * agreement.r * mixed(v, agreement, unitZ)`.  The implicit branch is the
unchanged lifted singular ledger.  All geometric component estimates remain
explicit inputs.
-/

namespace ProximityPrize.SubmissionLower.ContactShearLedger6533

open scoped BigOperators
open ContactParameters6533 ContactShearParameters6533

def sumVector {I : Type} [Fintype I] (v : I → DegreeVector) : DegreeVector :=
  ⟨∑ i, (v i).y, ∑ i, (v i).r, ∑ i, (v i).z⟩

def vectorLE (a b : DegreeVector) : Prop :=
  a.y ≤ b.y ∧ a.r ≤ b.r ∧ a.z ≤ b.z

def dot (a b : DegreeVector) : ℕ :=
  a.y * b.y + a.r * b.r + a.z * b.z

theorem dot_mono_left {a b : DegreeVector} (c : DegreeVector)
    (h : vectorLE a b) : dot a c ≤ dot b c :=
  Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_right c.y h.1)
      (Nat.mul_le_mul_right c.r h.2.1))
    (Nat.mul_le_mul_right c.z h.2.2)

theorem dot_sum_left {I : Type} [Fintype I]
    (v : I → DegreeVector) (a : DegreeVector) :
    dot (sumVector v) a = ∑ i, dot (v i) a := by
  simp only [dot, sumVector, Finset.sum_add_distrib, Finset.sum_mul]

/-- Per-surface regular numerator after paying the global-shear correction. -/
def shearedWholeNumerator (v : DegreeVector) : ℕ :=
  (n - w) ^ 2 *
      (mixed v sharpAgreement sharpAgreement +
        2 * sharpAgreement.r * mixed v sharpAgreement unitZ) +
    (errors + 1) * (n - w) * gap * mixed v sharpAgreement unitZ

def regularCoefficients : DegreeVector :=
  ⟨shearedWholeNumerator unitY,
    shearedWholeNumerator unitR,
    shearedWholeNumerator unitZ⟩

theorem shearedWhole_eq_dot (v : DegreeVector) :
    shearedWholeNumerator v = dot v regularCoefficients := by
  simp only [shearedWholeNumerator, regularCoefficients, dot, mixed,
    unitY, unitR, unitZ]
  ring

theorem sum_shearedWhole {I : Type} [Fintype I]
    (v : I → DegreeVector) :
    shearedWholeNumerator (sumVector v) =
      ∑ i, shearedWholeNumerator (v i) := by
  rw [shearedWhole_eq_dot, dot_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  exact (shearedWhole_eq_dot (v i)).symm

theorem shearedWhole_surface_exact :
    shearedWholeNumerator surfaceVector =
      sharpYWholeNumerator + shearWholePenalty := by
  simp only [shearedWholeNumerator, sharpYWholeNumerator,
    shearWholePenalty, shearMixedPenalty, sharpAgreementZProjection]
  ring

/-- Aggregate all regular original factors using only their three summed
degree budgets and their componentwise sheared incidence estimates. -/
theorem sum_regular_sheared_bound {I : Type} [Fintype I]
    (count : I → ℕ) (v : I → DegreeVector)
    (hy : (∑ i, (v i).y) ≤ yCap)
    (hr : (∑ i, (v i).r) ≤ slopeCap)
    (hz : (∑ i, (v i).z) ≤ seedTotalCap)
    (hcount : ∀ i,
      count i * gap ^ 2 ≤ shearedWholeNumerator (v i)) :
    (∑ i, count i) * gap ^ 2 ≤
      sharpYWholeNumerator + shearWholePenalty := by
  calc
    _ = ∑ i, count i * gap ^ 2 := Finset.sum_mul _ _ _
    _ ≤ ∑ i, shearedWholeNumerator (v i) :=
      Finset.sum_le_sum (fun i _ ↦ hcount i)
    _ = shearedWholeNumerator (sumVector v) :=
      (sum_shearedWhole v).symm
    _ = dot (sumVector v) regularCoefficients :=
      shearedWhole_eq_dot _
    _ ≤ dot surfaceVector regularCoefficients :=
      dot_mono_left regularCoefficients ⟨hy, hr, hz⟩
    _ = shearedWholeNumerator surfaceVector :=
      (shearedWhole_eq_dot _).symm
    _ = _ := shearedWhole_surface_exact

def implicitAggregateCost : DegreeVector :=
  ⟨algebraicCap, 2 * implicitYCap * algebraicCap, implicitYCap⟩

def implicitCoefficients : DegreeVector :=
  ⟨(n - w) * liftedAgreement.y,
    (n - w) * liftedAgreement.r,
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
  simp only [implicitAggregateCost, implicitCoefficients,
    implicitCoreNumerator, dot, mixed, liftedSurface, implicitCut, unitZ]
  ring

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
    _ = dot (sumVector cost) implicitCoefficients :=
      (dot_sum_left cost implicitCoefficients).symm
    _ ≤ dot implicitAggregateCost implicitCoefficients :=
      dot_mono_left implicitCoefficients ⟨hy, hr, hz⟩
    _ = implicitCoreNumerator := implicit_aggregate_eq_core

theorem sharp_singular_padding :
    sharpSingularNumerator =
      implicitCoreNumerator +
        gap * (algebraicCap + 2 * algebraicCap ^ 2 +
          mixed liftedSurface implicitCut liftedLast) := by
  simp only [sharpSingularNumerator, implicitCoreNumerator]
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
    ((∑ i, count i) + exceptions) * gap ≤ sharpSingularNumerator := by
  have hmain := sum_implicit_counts_bound count cost hy hr hz hcount
  calc
    _ = (∑ i, count i) * gap + exceptions * gap := Nat.add_mul _ _ _
    _ ≤ implicitCoreNumerator + 2 * algebraicCap ^ 2 * gap :=
      Nat.add_le_add hmain (Nat.mul_le_mul_right gap hexceptions)
    _ ≤ sharpSingularNumerator := by
      rw [sharp_singular_padding]
      apply Nat.add_le_add_left
      calc
        2 * algebraicCap ^ 2 * gap = gap * (2 * algebraicCap ^ 2) := by
          ring
        _ ≤ gap * (algebraicCap + 2 * algebraicCap ^ 2 +
            mixed liftedSurface implicitCut liftedLast) :=
          Nat.mul_le_mul_left gap (by omega)

/-- Final exact finite-family ledger.  All geometry is explicit in the two
per-branch hypotheses and the cover inequality. -/
theorem final_family_ledger {I J : Type} [Fintype I] [Fintype J]
    (regularCount : I → ℕ) (v : I → DegreeVector)
    (implicitCount : J → ℕ) (cost : J → DegreeVector)
    (exceptions cardinality : ℕ)
    (hregularY : (∑ i, (v i).y) ≤ yCap)
    (hregularR : (∑ i, (v i).r) ≤ slopeCap)
    (hregularZ : (∑ i, (v i).z) ≤ seedTotalCap)
    (hregular : ∀ i,
      regularCount i * gap ^ 2 ≤ shearedWholeNumerator (v i))
    (hcostY : (∑ i, (cost i).y) ≤ algebraicCap)
    (hcostR : (∑ i, (cost i).r) ≤ 2 * implicitYCap * algebraicCap)
    (hcostZ : (∑ i, (cost i).z) ≤ implicitYCap)
    (himplicit : ∀ i, implicitCount i * gap ≤
      (n - w) * dot liftedAgreement (cost i) +
        (errors + 1) * gap * (cost i).z)
    (hexceptions : exceptions ≤ 2 * algebraicCap ^ 2)
    (hcover : cardinality ≤
      (∑ i, regularCount i) + (∑ i, implicitCount i) + exceptions) :
    cardinality < alignmentBudget := by
  have hreg := sum_regular_sheared_bound regularCount v
    hregularY hregularR hregularZ hregular
  have himp := implicit_with_exceptions_bound implicitCount cost exceptions
    hcostY hcostR hcostZ himplicit hexceptions
  have hscaled :
      ((∑ i, regularCount i) + (∑ i, implicitCount i) + exceptions) *
          gap ^ 2 ≤ shearedTotalNumerator := by
    calc
      _ = (∑ i, regularCount i) * gap ^ 2 +
          (((∑ i, implicitCount i) + exceptions) * gap) * gap := by
        ring
      _ ≤ (sharpYWholeNumerator + shearWholePenalty) +
          sharpSingularNumerator * gap :=
        Nat.add_le_add hreg (Nat.mul_le_mul_right gap himp)
      _ = shearedTotalNumerator := by
        simp only [shearedTotalNumerator, sharpYTotalNumerator]
        ring
  have hcard : cardinality * gap ^ 2 ≤ shearedTotalNumerator :=
    (Nat.mul_le_mul_right (gap ^ 2) hcover).trans hscaled
  exact Nat.lt_of_mul_lt_mul_right
    (hcard.trans_lt (by
      simpa only [gapSquared] using sheared_strict_budget))

end ProximityPrize.SubmissionLower.ContactShearLedger6533

#print axioms ProximityPrize.SubmissionLower.ContactShearLedger6533.shearedWhole_surface_exact
#print axioms ProximityPrize.SubmissionLower.ContactShearLedger6533.final_family_ledger
