import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactAlignmentBridge
import ProximityPrize.SubmissionLower.ContactPrimeSeedIncidence
import ProximityPrize.SubmissionLower.ContactTranslation
import ProximityPrize.SubmissionLower.ContactAlignmentParameters

/-!
# The 64.88 interpolation front end and stock alignment interface

Model label: gpt-5.

This new adapter applies the re-instantiated universal interpolant to each
caller's ORIGINAL agreement support at e=77665. Its only counting input is
the actual selected-polynomial bound in the new coefficient box. The
companion ContactAlignment6401 module discharges that input by the actual
global factor-counting theorem.

No old ContactFrozenAlignment or ContactAlignment6400 module is imported.
The final step uses the unchanged generic alignmentBound_of_selected_count,
not its old numerical 6400 wrapper. This file alone is still conditional
on the explicit count; it is not a ProtocolClaim or submission.
-/

namespace ProximityPrize.SubmissionLower.ContactFrozenAlignment6401

open ProximityPrize.Benchmark
open ContactAlignmentParameters ContactAlignmentBridge ContactInterpolation
open ContactTranslation ContactPrimeSeedIncidence

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

local instance : DecidableEq IRSProfile.Field := Classical.decEq _

/-- The new selected-family bound uses the actual domain and the exact
77665-error, 10^17-seed parameters. -/
def SelectedNoLargePencilBound6401 : Prop :=
  SelectedNoLargePencilBound IRSProfile.domain 131071 78386 137490364055697543

/-- The precise actual-interpolant count supplied by the global counting
module; it is an explicit input to this frontend, never a new axiom. -/
def InterpolantSelectedCount6401 : Prop :=
  ∀ (Q : MvPolynomial (Fin 4) IRSProfile.Field),
    Q ≠ 0 →
    Q ∈ globalCoefficientBox IRSProfile.Field weightedCap w seedTotalCap slopeCap →
    ∀ (selected : IRSProfile.Field → Polynomial IRSProfile.Field)
      (seeds : Finset IRSProfile.Field) (u₀ u₁ : IRSProfile.Index → IRSProfile.Field),
      (∀ γ ∈ seeds, (selected γ).natDegree ≤ w) →
      (∀ γ ∈ seeds, specialization IRSProfile.Field (selected γ) γ Q = 0) →
      (∀ γ ∈ seeds, agreements ≤
        (Finset.univ.filter (fun i : IRSProfile.Index =>
          (selected γ).eval (IRSProfile.domain i) = u₀ i + γ * u₁ i)).card) →
      NoLargeSelectedPencil selected seeds w errors →
      seeds.card < alignmentBudget

theorem challenge_field_characteristic :
    CharP IRSProfile.Field prime := by
  change CharP KoalaBear.Ext6 2130706433
  exact charP_of_injective_algebraMap' KoalaBear.Field 2130706433

theorem original_support_card
    (A : IRSProfile.Field → Finset IRSProfile.Index)
    (seeds : Finset IRSProfile.Field)
    (hcard : ∀ γ ∈ seeds, Fintype.card IRSProfile.Index - 78386 ≤ (A γ).card) :
    ∀ γ ∈ seeds, agreements ≤ (A γ).card := by
  intro γ hγ
  have hh := hcard γ hγ
  simpa [IRSProfile.Index, agreements] using hh

/-- The SAME nonzero universal interpolant applies to every selected
polynomial using exactly its supplied support A(γ). -/
theorem selected_count_of_interpolant_count
    (hcount : InterpolantSelectedCount6401) :
    SelectedNoLargePencilBound6401 := by
  classical
  intro U seeds A selected hdegree hcard hvalues hno
  have hcard' := original_support_card A seeds hcard
  obtain ⟨Q, hQ, hbox, hvanish⟩ :=
    exists_frozen_universal_vanishing_interpolant (U 0) (U 1)
  have hbox' : Q ∈
      globalCoefficientBox IRSProfile.Field weightedCap w seedTotalCap slopeCap := hbox
  have hsolution : ∀ γ ∈ seeds,
      specialization IRSProfile.Field (selected γ) γ Q = 0 := by
    intro γ hγ
    exact hvanish γ (selected γ) (A γ) (hdegree γ hγ) (hcard' γ hγ) (hvalues γ hγ)
  have hagreement : ∀ γ ∈ seeds, agreements ≤
      (Finset.univ.filter (fun i : IRSProfile.Index =>
        (selected γ).eval (IRSProfile.domain i) = U 0 i + γ * U 1 i)).card := by
    intro γ hγ
    apply le_trans (hcard' γ hγ)
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hvalues γ hγ i hi⟩
  have hno' : NoLargeSelectedPencil selected seeds w errors := by
    intro P₀ P₁ h₀ h₁
    have hp := hno P₀ P₁ h₀ h₁
    change (seeds.filter (fun γ => selected γ = P₀ + Polynomial.C γ * P₁)).card ≤ errors + 1
    rw [parameter_values.2.2.2.1]
    refine le_trans ?_ hp
    apply Finset.card_le_card
    intro γ hγ
    simpa only [pencilSeeds, Finset.mem_filter] using (Finset.mem_filter.mp hγ)
  exact Nat.le_of_lt (hcount Q hQ hbox' selected seeds (U 0) (U 1)
    hdegree hsolution hagreement hno')

/-- Use the generic stock-code bridge at the new error and seed budget. -/
theorem alignment_of_interpolant_count
    (hcount : InterpolantSelectedCount6401) :
    AffineLineAlignmentBound IRSProfile.baseCode 78386 137490364055697543 := by
  change AffineLineAlignmentBound (ReedSolomon.code IRSProfile.domain (131071 + 1))
    78386 137490364055697543
  exact alignmentBound_of_selected_count IRSProfile.domain 131071 78386
    137490364055697543 (selected_count_of_interpolant_count hcount)

#print axioms challenge_field_characteristic
#print axioms original_support_card
#print axioms selected_count_of_interpolant_count
#print axioms alignment_of_interpolant_count

end
end ProximityPrize.SubmissionLower.ContactFrozenAlignment6401
