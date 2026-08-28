import ProximityPrize.SubmissionLower.AlignmentProtocol6401Conditional
import ProximityPrize.SubmissionLower.ContactScore6630Research

/-!
# Conditional protocol certificate at 66.41 bits

The sole mathematical premise is an affine-line alignment bound at `79194`
errors with the exact field-compatible budget `137490364055697543`.  This
module derives the radius cell, MCA transfer, squared-interleaving list
transfer, field-capacity inequalities, reduction target, and fractional
score conversion.  It asserts no counting theorem.
-/

namespace ProximityPrize.SubmissionLower.AlignmentProtocol6630ConditionalResearch

open ProximityPrize.Benchmark
open CoreDefinitions ProximityGap ToyProblem
open scoped NNReal

noncomputable section

def radius6630 : ℝ≥0 := ContactScore6630Research.radius6630
def errors6630 : ℕ := ContactScore6630Research.errors6630
def budget6630 : ℕ := 137490364055697543

theorem radius6630_floor :
    ⌊(radius6630 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ =
      errors6630 := by
  simpa [radius6630, errors6630] using ContactScore6630Research.radius6630_floor

theorem radius6630_cell_cross :
    316779 * Fintype.card IRSProfile.Index <
      (errors6630 + 1) * 1048576 := by
  simpa [errors6630] using ContactScore6630Research.radius6630_cell_cross

theorem radius6630_gap :
    131071 < Fintype.card IRSProfile.Index - errors6630 := by
  simpa [errors6630] using ContactScore6630Research.radius6630_gap

theorem field_cardinality :
    Fintype.card IRSProfile.Field = (2130706433 : ℕ) ^ 6 :=
  AlignmentProtocol6401Conditional.field_cardinality

theorem budget6630_lt_field :
    budget6630 < Fintype.card IRSProfile.Field := by
  rw [field_cardinality]
  norm_num [budget6630]

theorem sixteen_row_separation_gate6630 :
    15 * (budget6630 + 1).choose 2 < Fintype.card IRSProfile.Field := by
  rw [field_cardinality, Nat.choose_eq_descFactorial_div_factorial]
  norm_num [budget6630, Nat.descFactorial_succ, Nat.factorial_succ]

/-- Exact field capacity for the sum of MCA and list allowances. -/
theorem doubled_budget6630_nat :
    2 ^ (128 : ℕ) * (budget6630 + budget6630) ≤
      Fintype.card IRSProfile.Field := by
  rw [field_cardinality]
  norm_num [budget6630]

theorem base_mca6630_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6630 budget6630) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (radius6630 : ℝ) ≤
      ENNReal.ofReal ((budget6630 : ℝ) / Fintype.card IRSProfile.Field) := by
  apply mcaError_affineLine_le_of_givenSetsBound
  apply givenSetsBound_of_alignmentBound IRSProfile.baseCode
    (radius6630 : ℝ) errors6630 budget6630
  · intro A hA
    have hcomp :=
      (mul_one_sub_le_card_iff_sub_card_le_floor A
        (show (0 : ℝ) ≤ (radius6630 : ℝ) by positivity)).mp hA
    rw [radius6630_floor] at hcomp
    have hn : Fintype.card IRSProfile.Index = 262144 := by
      norm_num [IRSProfile.Index]
    rw [hn]
    norm_num [errors6630, ContactScore6630Research.errors6630] at hcomp ⊢
    omega
  · exact halign

theorem mca6630_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6630 budget6630) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
        (radius6630 : ℝ) ≤
      (budget6630 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) := by
  calc
    _ ≤ mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (radius6630 : ℝ) := by
      rw [AlignmentProtocol6401Conditional.irs_code_eq_base_interleaved]
      exact ProximityGap.mcaError_interleaved_le IRSProfile.baseCode
        IRSProfile.interleaving radius6630
        (by norm_num [IRSProfile.interleaving])
        (by norm_num [radius6630, ContactScore6630Research.radius6630,
          claimedRadius])
        (by norm_num [radius6630, ContactScore6630Research.radius6630,
          claimedRadius])
    _ ≤ ENNReal.ofReal
        ((budget6630 : ℝ) / Fintype.card IRSProfile.Field) :=
      base_mca6630_le_of_alignment halign
    _ = (budget6630 : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]

theorem lambda6630_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6630 budget6630) :
    Code.Lambda
      ((IRSProfile.code ^⋈ (Fin 2) :
        ModuleCode IRSProfile.Index IRSProfile.Field
          (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
        Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
          IRSProfile.Field))
      (radius6630 : ℝ) ≤ (budget6630 : ℕ∞) := by
  exact AlignmentInterleavedLambda.irs_squared_claimedRadius_lambda_le
    316779 1048576 errors6630 budget6630 (by norm_num)
    radius6630_cell_cross radius6630_gap halign budget6630_lt_field
    sixteen_row_separation_gate6630

theorem certifiedGammaError6630_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6630 budget6630) :
    certifiedGammaError IRSProfile.code radius6630 ≤
      (1 : ℝ≥0) / 2 ^ (128 : ℕ) := by
  rw [← ENNReal.coe_le_coe, coe_certifiedGammaError]
  push_cast
  have hLambdaNat := ENat.toNat_le_of_le_coe
    (lambda6630_le_of_alignment halign)
  have hList :
      ((Code.Lambda
        ((IRSProfile.code ^⋈ (Fin 2) :
          ModuleCode IRSProfile.Index IRSProfile.Field
            (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
          Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
            IRSProfile.Field))
        (radius6630 : ℝ)).toNat : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) ≤
        (budget6630 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) :=
    ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
  calc
    _ ≤ (budget6630 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) +
        (budget6630 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) :=
      add_le_add (mca6630_le_of_alignment halign) hList
    _ = ((budget6630 + budget6630 : ℕ) : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [← ENNReal.add_div, Nat.cast_add]
    _ ≤ (1 : ENNReal) / 2 ^ (128 : ℕ) := by
      apply AlignmentProtocol6401Conditional.nat_div_le_inv_pow
      · norm_num [budget6630]
      · simpa only [Nat.mul_comm] using doubled_budget6630_nat

theorem protocolClaim6630_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode
      errors6630 budget6630) :
    ProtocolClaim 6642 316779 1048576 where
  admissible := ContactScore6630Research.radius6630_admissible
  reduction := by
    change certifiedGammaError IRSProfile.code radius6630 ≤ reductionTarget
    exact (certifiedGammaError6630_le_of_alignment halign).trans
      (by norm_num [reductionTarget, ProximityGap.prizeThreshold, div_le_iff₀])
  score := ContactScore6630Research.radius6630_score

end


end ProximityPrize.SubmissionLower.AlignmentProtocol6630ConditionalResearch

#print axioms ProximityPrize.SubmissionLower.AlignmentProtocol6630ConditionalResearch.field_cardinality
#print axioms ProximityPrize.SubmissionLower.AlignmentProtocol6630ConditionalResearch.budget6630_lt_field
#print axioms ProximityPrize.SubmissionLower.AlignmentProtocol6630ConditionalResearch.sixteen_row_separation_gate6630
#print axioms ProximityPrize.SubmissionLower.AlignmentProtocol6630ConditionalResearch.doubled_budget6630_nat
#print axioms ProximityPrize.SubmissionLower.AlignmentProtocol6630ConditionalResearch.protocolClaim6630_of_alignment
