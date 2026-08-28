import ProximityPrize.SubmissionLower.AlignmentProtocol6401Conditional
import ProximityPrize.SubmissionLower.ContactScore6533

/-!
# Conditional protocol certificate at 65.67 bits

This adapter isolates the final reduction from the one remaining mathematical
input: an alignment bound at 78455 errors with the exact doubled-field-safe
list budget.  The code,
alphabet, interleaving, MCA transfer, list transfer, and field-capacity
calculation are unchanged from the verified 64.64 assembly; only the decoding
radius and its exact score certificate change.
-/

namespace ProximityPrize.SubmissionLower.AlignmentProtocol6533Conditional

open ProximityPrize.Benchmark
open CoreDefinitions ProximityGap ToyProblem
open scoped NNReal

noncomputable section

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

def radius6533 : ℝ≥0 := ContactScore6533.radius6533
def errors6533 : ℕ := ContactScore6533.errors6533
def budget6533 : ℕ := 137490364055697543

theorem budget6533_lt_field : budget6533 < Fintype.card IRSProfile.Field := by
  rw [AlignmentProtocol6401Conditional.field_cardinality]
  norm_num [budget6533]

theorem sixteen_row_separation_gate6533 :
    15 * (budget6533 + 1).choose 2 < Fintype.card IRSProfile.Field := by
  rw [AlignmentProtocol6401Conditional.field_cardinality,
    Nat.choose_eq_descFactorial_div_factorial]
  norm_num [budget6533, Nat.descFactorial_succ, Nat.factorial_succ]

theorem doubled_budget6533_nat :
    2 ^ (128 : ℕ) * (budget6533 + budget6533) ≤
      Fintype.card IRSProfile.Field := by
  rw [AlignmentProtocol6401Conditional.field_cardinality]
  norm_num [budget6533]

theorem radius6533_floor :
    ⌊(radius6533 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ = errors6533 := by
  simpa [radius6533, errors6533] using ContactScore6533.radius6533_floor

theorem radius6533_cell_cross :
    313823 * Fintype.card IRSProfile.Index < (errors6533 + 1) * 1048576 := by
  simpa [errors6533] using ContactScore6533.radius6533_cell_cross

theorem radius6533_gap :
    131071 < Fintype.card IRSProfile.Index - errors6533 := by
  simpa [errors6533] using ContactScore6533.radius6533_gap

theorem base_mca6533_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6533 budget6533) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (radius6533 : ℝ) ≤
      ENNReal.ofReal ((budget6533 : ℝ) / Fintype.card IRSProfile.Field) := by
  apply mcaError_affineLine_le_of_givenSetsBound
  apply givenSetsBound_of_alignmentBound IRSProfile.baseCode
    (radius6533 : ℝ) errors6533 budget6533
  · intro A hA
    have hcomp :=
      (mul_one_sub_le_card_iff_sub_card_le_floor A
        (show (0 : ℝ) ≤ (radius6533 : ℝ) by positivity)).mp hA
    rw [radius6533_floor] at hcomp
    have hn : Fintype.card IRSProfile.Index = 262144 := by
      norm_num [IRSProfile.Index]
    rw [hn]
    norm_num [errors6533] at hcomp ⊢
    omega
  · exact halign

theorem mca6533_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6533 budget6533) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
        (radius6533 : ℝ) ≤
      (budget6533 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) := by
  calc
    _ ≤ mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (radius6533 : ℝ) := by
      rw [AlignmentProtocol6401Conditional.irs_code_eq_base_interleaved]
      exact ProximityGap.mcaError_interleaved_le IRSProfile.baseCode
        IRSProfile.interleaving radius6533
        (by norm_num [IRSProfile.interleaving])
        (by norm_num [radius6533, ContactScore6533.radius6533,
          claimedRadius])
        (by norm_num [radius6533, ContactScore6533.radius6533,
          claimedRadius])
    _ ≤ ENNReal.ofReal
        ((budget6533 : ℝ) / Fintype.card IRSProfile.Field) :=
      base_mca6533_le_of_alignment halign
    _ = (budget6533 : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]

theorem lambda6533_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6533 budget6533) :
    Code.Lambda
      ((IRSProfile.code ^⋈ (Fin 2) :
        ModuleCode IRSProfile.Index IRSProfile.Field
          (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
        Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
          IRSProfile.Field))
      (radius6533 : ℝ) ≤ (budget6533 : ℕ∞) := by
  exact AlignmentInterleavedLambda.irs_squared_claimedRadius_lambda_le
    313823 1048576 errors6533 budget6533 (by norm_num)
    radius6533_cell_cross radius6533_gap halign
    budget6533_lt_field sixteen_row_separation_gate6533

theorem certifiedGammaError6533_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6533 budget6533) :
    certifiedGammaError IRSProfile.code radius6533 ≤
      (1 : ℝ≥0) / 2 ^ (128 : ℕ) := by
  rw [← ENNReal.coe_le_coe, coe_certifiedGammaError]
  push_cast
  have hLambdaNat := ENat.toNat_le_of_le_coe
    (lambda6533_le_of_alignment halign)
  have hList :
      ((Code.Lambda
        ((IRSProfile.code ^⋈ (Fin 2) :
          ModuleCode IRSProfile.Index IRSProfile.Field
            (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
          Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
            IRSProfile.Field))
        (radius6533 : ℝ)).toNat : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) ≤
        (budget6533 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) :=
    ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
  calc
    _ ≤ (budget6533 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) +
        (budget6533 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) :=
      add_le_add (mca6533_le_of_alignment halign) hList
    _ = ((budget6533 + budget6533 : ℕ) : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [← ENNReal.add_div, Nat.cast_add]
    _ ≤ (1 : ENNReal) / 2 ^ (128 : ℕ) := by
      apply AlignmentProtocol6401Conditional.nat_div_le_inv_pow
      · norm_num [budget6533]
      · rw [Nat.mul_comm]
        exact doubled_budget6533_nat

theorem protocolClaim6533_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode
      errors6533 budget6533) :
    ProtocolClaim 6567 313823 1048576 where
  admissible := ContactScore6533.radius6533_admissible
  reduction := by
    change certifiedGammaError IRSProfile.code radius6533 ≤ reductionTarget
    exact (certifiedGammaError6533_le_of_alignment halign).trans
      (by norm_num [reductionTarget, ProximityGap.prizeThreshold, div_le_iff₀])
  score := ContactScore6533.radius6533_score

end

end ProximityPrize.SubmissionLower.AlignmentProtocol6533Conditional
