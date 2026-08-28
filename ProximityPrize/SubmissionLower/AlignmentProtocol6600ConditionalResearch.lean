import ProximityPrize.SubmissionLower.AlignmentProtocol6401Conditional
import ProximityPrize.SubmissionLower.ContactScore6600Research

/-!
# Conditional protocol certificate at 66.00 bits

The sole premise is the stock affine-line alignment bound at `78777`
errors and list budget `10^17`.  The interleaving, MCA transfer, list
transfer, and field-capacity arguments are unchanged.
-/

namespace ProximityPrize.SubmissionLower.AlignmentProtocol6600ConditionalResearch

open ProximityPrize.Benchmark
open CoreDefinitions ProximityGap ToyProblem
open scoped NNReal

noncomputable section

def radius6600 : ℝ≥0 := ContactScore6600Research.radius6600
def errors6600 : ℕ := ContactScore6600Research.errors6600
def budget6600 : ℕ := 137490364055697543

theorem budget6600_eq_budget6401 :
    budget6600 = AlignmentProtocol6401Conditional.budget6401 := rfl

theorem radius6600_floor :
    ⌊(radius6600 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ = errors6600 := by
  simpa [radius6600, errors6600] using
    ContactScore6600Research.radius6600_floor

theorem radius6600_cell_cross :
    315871 * Fintype.card IRSProfile.Index <
      (errors6600 + 1) * 1048576 := by
  simpa [errors6600] using
    ContactScore6600Research.radius6600_cell_cross

theorem radius6600_gap :
    131071 < Fintype.card IRSProfile.Index - errors6600 := by
  simpa [errors6600] using ContactScore6600Research.radius6600_gap

theorem base_mca6600_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6600 budget6600) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (radius6600 : ℝ) ≤
      ENNReal.ofReal ((budget6600 : ℝ) / Fintype.card IRSProfile.Field) := by
  apply mcaError_affineLine_le_of_givenSetsBound
  apply givenSetsBound_of_alignmentBound IRSProfile.baseCode
    (radius6600 : ℝ) errors6600 budget6600
  · intro A hA
    have hcomp :=
      (mul_one_sub_le_card_iff_sub_card_le_floor A
        (show (0 : ℝ) ≤ (radius6600 : ℝ) by positivity)).mp hA
    rw [radius6600_floor] at hcomp
    have hn : Fintype.card IRSProfile.Index = 262144 := by
      norm_num [IRSProfile.Index]
    rw [hn]
    norm_num [errors6600, ContactScore6600Research.errors6600] at hcomp ⊢
    omega
  · exact halign

theorem mca6600_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6600 budget6600) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
        (radius6600 : ℝ) ≤
      (budget6600 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) := by
  calc
    _ ≤ mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (radius6600 : ℝ) := by
      rw [AlignmentProtocol6401Conditional.irs_code_eq_base_interleaved]
      exact ProximityGap.mcaError_interleaved_le IRSProfile.baseCode
        IRSProfile.interleaving radius6600
        (by norm_num [IRSProfile.interleaving])
        (by norm_num [radius6600, ContactScore6600Research.radius6600,
          claimedRadius])
        (by norm_num [radius6600, ContactScore6600Research.radius6600,
          claimedRadius])
    _ ≤ ENNReal.ofReal
        ((budget6600 : ℝ) / Fintype.card IRSProfile.Field) :=
      base_mca6600_le_of_alignment halign
    _ = (budget6600 : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]

theorem lambda6600_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6600 budget6600) :
    Code.Lambda
      ((IRSProfile.code ^⋈ (Fin 2) :
        ModuleCode IRSProfile.Index IRSProfile.Field
          (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
        Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
          IRSProfile.Field))
      (radius6600 : ℝ) ≤ (budget6600 : ℕ∞) := by
  exact AlignmentInterleavedLambda.irs_squared_claimedRadius_lambda_le
    315871 1048576 errors6600 budget6600 (by norm_num)
    radius6600_cell_cross radius6600_gap halign
    (by
      rw [budget6600_eq_budget6401]
      exact AlignmentProtocol6401Conditional.budget6401_lt_field)
    (by
      rw [budget6600_eq_budget6401]
      exact AlignmentProtocol6401Conditional.sixteen_row_separation_gate)

theorem certifiedGammaError6600_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6600 budget6600) :
    certifiedGammaError IRSProfile.code radius6600 ≤
      (1 : ℝ≥0) / 2 ^ (128 : ℕ) := by
  rw [← ENNReal.coe_le_coe, coe_certifiedGammaError]
  push_cast
  have hLambdaNat := ENat.toNat_le_of_le_coe
    (lambda6600_le_of_alignment halign)
  have hList :
      ((Code.Lambda
        ((IRSProfile.code ^⋈ (Fin 2) :
          ModuleCode IRSProfile.Index IRSProfile.Field
            (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
          Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
            IRSProfile.Field))
        (radius6600 : ℝ)).toNat : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) ≤
        (budget6600 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) :=
    ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
  calc
    _ ≤ (budget6600 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) +
        (budget6600 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) :=
      add_le_add (mca6600_le_of_alignment halign) hList
    _ = ((budget6600 + budget6600 : ℕ) : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [← ENNReal.add_div, Nat.cast_add]
    _ ≤ (1 : ENNReal) / 2 ^ (128 : ℕ) := by
      apply AlignmentProtocol6401Conditional.nat_div_le_inv_pow
      · norm_num [budget6600]
      · rw [Nat.mul_comm, budget6600_eq_budget6401]
        exact AlignmentProtocol6401Conditional.doubled_budget6401_nat

theorem protocolClaim6600_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode
      errors6600 budget6600) :
    ProtocolClaim 6619 315871 1048576 where
  admissible := ContactScore6600Research.radius6600_admissible
  reduction := by
    change certifiedGammaError IRSProfile.code radius6600 ≤ reductionTarget
    exact (certifiedGammaError6600_le_of_alignment halign).trans
      (by norm_num [reductionTarget, ProximityGap.prizeThreshold, div_le_iff₀])
  score := ContactScore6600Research.radius6600_score

end

end ProximityPrize.SubmissionLower.AlignmentProtocol6600ConditionalResearch

#print axioms ProximityPrize.SubmissionLower.AlignmentProtocol6600ConditionalResearch.protocolClaim6600_of_alignment
