import ProximityPrize.SubmissionLower.AlignmentProtocol6401Conditional
import ProximityPrize.SubmissionLower.ContactScore6656Research

/-!
# Conditional protocol certificate at 66.56 bits

The sole substantive premise is the stock affine-line alignment bound at
`79337` errors and the promoted list budget `137490364055697543`.  The
interleaving, MCA transfer, list transfer, and field-capacity arguments are
unchanged.
-/

namespace ProximityPrize.SubmissionLower.AlignmentProtocol6656ConditionalResearch

open ProximityPrize.Benchmark
open CoreDefinitions ProximityGap ToyProblem
open scoped NNReal

noncomputable section

def radius6656 : ℝ≥0 := ContactScore6656Research.radius6656
def errors6656 : ℕ := ContactScore6656Research.errors6656
def budget6656 : ℕ := 137490364055697543

theorem budget6656_eq_budget6401 :
    budget6656 = AlignmentProtocol6401Conditional.budget6401 := rfl

theorem radius6656_floor :
    ⌊(radius6656 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ = errors6656 := by
  simpa [radius6656, errors6656] using
    ContactScore6656Research.radius6656_floor

theorem radius6656_cell_cross :
    317351 * Fintype.card IRSProfile.Index <
      (errors6656 + 1) * 1048576 := by
  simpa [errors6656] using ContactScore6656Research.radius6656_cell_cross

theorem radius6656_gap :
    131071 < Fintype.card IRSProfile.Index - errors6656 := by
  simpa [errors6656] using ContactScore6656Research.radius6656_gap

theorem base_mca6656_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6656 budget6656) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (radius6656 : ℝ) ≤
      ENNReal.ofReal ((budget6656 : ℝ) / Fintype.card IRSProfile.Field) := by
  apply mcaError_affineLine_le_of_givenSetsBound
  apply givenSetsBound_of_alignmentBound IRSProfile.baseCode
    (radius6656 : ℝ) errors6656 budget6656
  · intro A hA
    have hcomp :=
      (mul_one_sub_le_card_iff_sub_card_le_floor A
        (show (0 : ℝ) ≤ (radius6656 : ℝ) by positivity)).mp hA
    rw [radius6656_floor] at hcomp
    have hn : Fintype.card IRSProfile.Index = 262144 := by
      norm_num [IRSProfile.Index]
    rw [hn]
    norm_num [errors6656, ContactScore6656Research.errors6656] at hcomp ⊢
    omega
  · exact halign

theorem mca6656_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6656 budget6656) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
        (radius6656 : ℝ) ≤
      (budget6656 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) := by
  calc
    _ ≤ mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (radius6656 : ℝ) := by
      rw [AlignmentProtocol6401Conditional.irs_code_eq_base_interleaved]
      exact ProximityGap.mcaError_interleaved_le IRSProfile.baseCode
        IRSProfile.interleaving radius6656
        (by norm_num [IRSProfile.interleaving])
        (by norm_num [radius6656, ContactScore6656Research.radius6656,
          claimedRadius])
        (by norm_num [radius6656, ContactScore6656Research.radius6656,
          claimedRadius])
    _ ≤ ENNReal.ofReal
        ((budget6656 : ℝ) / Fintype.card IRSProfile.Field) :=
      base_mca6656_le_of_alignment halign
    _ = (budget6656 : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]

theorem lambda6656_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6656 budget6656) :
    Code.Lambda
      ((IRSProfile.code ^⋈ (Fin 2) :
        ModuleCode IRSProfile.Index IRSProfile.Field
          (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
        Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
          IRSProfile.Field))
      (radius6656 : ℝ) ≤ (budget6656 : ℕ∞) := by
  exact AlignmentInterleavedLambda.irs_squared_claimedRadius_lambda_le
    317351 1048576 errors6656 budget6656 (by norm_num)
    radius6656_cell_cross radius6656_gap halign
    (by
      rw [budget6656_eq_budget6401]
      exact AlignmentProtocol6401Conditional.budget6401_lt_field)
    (by
      rw [budget6656_eq_budget6401]
      exact AlignmentProtocol6401Conditional.sixteen_row_separation_gate)

theorem certifiedGammaError6656_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6656 budget6656) :
    certifiedGammaError IRSProfile.code radius6656 ≤
      (1 : ℝ≥0) / 2 ^ (128 : ℕ) := by
  rw [← ENNReal.coe_le_coe, coe_certifiedGammaError]
  push_cast
  have hLambdaNat := ENat.toNat_le_of_le_coe
    (lambda6656_le_of_alignment halign)
  have hList :
      ((Code.Lambda
        ((IRSProfile.code ^⋈ (Fin 2) :
          ModuleCode IRSProfile.Index IRSProfile.Field
            (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
          Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
            IRSProfile.Field))
        (radius6656 : ℝ)).toNat : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) ≤
        (budget6656 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) :=
    ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
  calc
    _ ≤ (budget6656 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) +
        (budget6656 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) :=
      add_le_add (mca6656_le_of_alignment halign) hList
    _ = ((budget6656 + budget6656 : ℕ) : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [← ENNReal.add_div, Nat.cast_add]
    _ ≤ (1 : ENNReal) / 2 ^ (128 : ℕ) := by
      apply AlignmentProtocol6401Conditional.nat_div_le_inv_pow
      · norm_num [budget6656]
      · rw [Nat.mul_comm, budget6656_eq_budget6401]
        exact AlignmentProtocol6401Conditional.doubled_budget6401_nat

/-- Conditional endpoint with exactly one substantive alignment premise. -/
theorem protocolClaim6656_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode
      errors6656 budget6656) :
    ProtocolClaim 6656 317351 1048576 where
  admissible := ContactScore6656Research.radius6656_admissible
  reduction := by
    change certifiedGammaError IRSProfile.code radius6656 ≤ reductionTarget
    exact (certifiedGammaError6656_le_of_alignment halign).trans
      (by norm_num [reductionTarget, ProximityGap.prizeThreshold, div_le_iff₀])
  score := ContactScore6656Research.radius6656_score

/-- Literal-parameter endpoint used by the stacked counting integration. -/
theorem protocolClaim6656
    (halign : AffineLineAlignmentBound IRSProfile.baseCode
      79337 137490364055697543) :
    ProtocolClaim 6656 317351 1048576 := by
  apply protocolClaim6656_of_alignment
  simpa [errors6656, budget6656, ContactScore6656Research.errors6656] using halign

end


end ProximityPrize.SubmissionLower.AlignmentProtocol6656ConditionalResearch

#print axioms ProximityPrize.SubmissionLower.AlignmentProtocol6656ConditionalResearch.protocolClaim6656_of_alignment
#print axioms ProximityPrize.SubmissionLower.AlignmentProtocol6656ConditionalResearch.protocolClaim6656
