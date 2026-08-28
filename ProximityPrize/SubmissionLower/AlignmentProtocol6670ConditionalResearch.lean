import ProximityPrize.SubmissionLower.AlignmentProtocol6656ConditionalResearch
import ProximityPrize.SubmissionLower.ContactScore6670Research

/-!
# Conditional protocol certificate at 66.70 bits

The sole substantive premise is the stock affine-line alignment bound at
`79476` errors and the promoted list budget `137490364055697543`.  The
interleaving, MCA transfer, list transfer, and field-capacity arguments are
the accepted 66.56 endpoint specialized mechanically to the new radius cell.
-/

namespace ProximityPrize.SubmissionLower.AlignmentProtocol6670ConditionalResearch

open ProximityPrize.Benchmark
open CoreDefinitions ProximityGap ToyProblem
open scoped NNReal

noncomputable section

def radius6670 : ℝ≥0 := ContactScore6670Research.radius6670
def errors6670 : ℕ := ContactScore6670Research.errors6670
def budget6670 : ℕ := 137490364055697543

theorem budget6670_eq_budget6656 :
    budget6670 = AlignmentProtocol6656ConditionalResearch.budget6656 := rfl

theorem radius6670_floor :
    ⌊(radius6670 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ = errors6670 := by
  simpa [radius6670, errors6670] using ContactScore6670Research.radius6670_floor

theorem radius6670_cell_cross :
    317907 * Fintype.card IRSProfile.Index <
      (errors6670 + 1) * 1048576 := by
  simpa [errors6670] using ContactScore6670Research.radius6670_cell_cross

theorem radius6670_gap :
    131071 < Fintype.card IRSProfile.Index - errors6670 := by
  simpa [errors6670] using ContactScore6670Research.radius6670_gap

theorem base_mca6670_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6670 budget6670) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (radius6670 : ℝ) ≤
      ENNReal.ofReal ((budget6670 : ℝ) / Fintype.card IRSProfile.Field) := by
  apply mcaError_affineLine_le_of_givenSetsBound
  apply givenSetsBound_of_alignmentBound IRSProfile.baseCode
    (radius6670 : ℝ) errors6670 budget6670
  · intro A hA
    have hcomp :=
      (mul_one_sub_le_card_iff_sub_card_le_floor A
        (show (0 : ℝ) ≤ (radius6670 : ℝ) by positivity)).mp hA
    rw [radius6670_floor] at hcomp
    have hn : Fintype.card IRSProfile.Index = 262144 := by
      norm_num [IRSProfile.Index]
    rw [hn]
    norm_num [errors6670, ContactScore6670Research.errors6670] at hcomp ⊢
    omega
  · exact halign

theorem mca6670_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6670 budget6670) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
        (radius6670 : ℝ) ≤
      (budget6670 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) := by
  calc
    _ ≤ mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (radius6670 : ℝ) := by
      rw [AlignmentProtocol6401Conditional.irs_code_eq_base_interleaved]
      exact ProximityGap.mcaError_interleaved_le IRSProfile.baseCode
        IRSProfile.interleaving radius6670
        (by norm_num [IRSProfile.interleaving])
        (by norm_num [radius6670, ContactScore6670Research.radius6670,
          claimedRadius])
        (by norm_num [radius6670, ContactScore6670Research.radius6670,
          claimedRadius])
    _ ≤ ENNReal.ofReal
        ((budget6670 : ℝ) / Fintype.card IRSProfile.Field) :=
      base_mca6670_le_of_alignment halign
    _ = (budget6670 : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]

theorem lambda6670_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6670 budget6670) :
    Code.Lambda
      ((IRSProfile.code ^⋈ (Fin 2) :
        ModuleCode IRSProfile.Index IRSProfile.Field
          (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
        Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
          IRSProfile.Field))
      (radius6670 : ℝ) ≤ (budget6670 : ℕ∞) := by
  exact AlignmentInterleavedLambda.irs_squared_claimedRadius_lambda_le
    317907 1048576 errors6670 budget6670 (by norm_num)
    radius6670_cell_cross radius6670_gap halign
    (by
      rw [budget6670_eq_budget6656,
        AlignmentProtocol6656ConditionalResearch.budget6656_eq_budget6401]
      exact AlignmentProtocol6401Conditional.budget6401_lt_field)
    (by
      rw [budget6670_eq_budget6656,
        AlignmentProtocol6656ConditionalResearch.budget6656_eq_budget6401]
      exact AlignmentProtocol6401Conditional.sixteen_row_separation_gate)

theorem certifiedGammaError6670_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6670 budget6670) :
    certifiedGammaError IRSProfile.code radius6670 ≤
      (1 : ℝ≥0) / 2 ^ (128 : ℕ) := by
  rw [← ENNReal.coe_le_coe, coe_certifiedGammaError]
  push_cast
  have hLambdaNat := ENat.toNat_le_of_le_coe
    (lambda6670_le_of_alignment halign)
  have hList :
      ((Code.Lambda
        ((IRSProfile.code ^⋈ (Fin 2) :
          ModuleCode IRSProfile.Index IRSProfile.Field
            (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
          Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
            IRSProfile.Field))
        (radius6670 : ℝ)).toNat : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) ≤
        (budget6670 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) :=
    ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
  calc
    _ ≤ (budget6670 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) +
        (budget6670 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) :=
      add_le_add (mca6670_le_of_alignment halign) hList
    _ = ((budget6670 + budget6670 : ℕ) : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [← ENNReal.add_div, Nat.cast_add]
    _ ≤ (1 : ENNReal) / 2 ^ (128 : ℕ) := by
      apply AlignmentProtocol6401Conditional.nat_div_le_inv_pow
      · norm_num [budget6670]
      · rw [Nat.mul_comm, budget6670_eq_budget6656,
          AlignmentProtocol6656ConditionalResearch.budget6656_eq_budget6401]
        exact AlignmentProtocol6401Conditional.doubled_budget6401_nat

/-- Conditional endpoint with exactly one substantive alignment premise. -/
theorem protocolClaim6670_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode
      errors6670 budget6670) :
    ProtocolClaim 6670 317907 1048576 where
  admissible := ContactScore6670Research.radius6670_admissible
  reduction := by
    change certifiedGammaError IRSProfile.code radius6670 ≤ reductionTarget
    exact (certifiedGammaError6670_le_of_alignment halign).trans
      (by norm_num [reductionTarget, ProximityGap.prizeThreshold, div_le_iff₀])
  score := ContactScore6670Research.radius6670_score

/-- Literal-parameter endpoint used by the stacked counting integration. -/
theorem protocolClaim6670
    (halign : AffineLineAlignmentBound IRSProfile.baseCode
      79476 137490364055697543) :
    ProtocolClaim 6670 317907 1048576 := by
  apply protocolClaim6670_of_alignment
  simpa [errors6670, budget6670, ContactScore6670Research.errors6670] using halign

end


end ProximityPrize.SubmissionLower.AlignmentProtocol6670ConditionalResearch

#print axioms ProximityPrize.SubmissionLower.AlignmentProtocol6670ConditionalResearch.protocolClaim6670_of_alignment
#print axioms ProximityPrize.SubmissionLower.AlignmentProtocol6670ConditionalResearch.protocolClaim6670
