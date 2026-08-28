import ProximityPrize.SubmissionLower.AlignmentInterleavedLambda

/-!
# Conditional protocol certificate at 64.54 bits

Model label: gpt-5.

The sole mathematical premise of the final theorem is the explicit strong
alignment bound at 77324 errors with budget 10^17. The actual squared-eight
Code.Lambda, scalar-to-interleaved MCA transfer, field capacity and score
conversion are derived below. No old Contact parameter or 6400 list module
is imported, and no Benchmark.candidate is declared.

The score proof uses a separately checked upper rational approximation to
2^(1/100) and a 128th-power rational inequality. It does not reuse the old
half-square 6400 argument or assume the historical 12800th-power witness.
-/

namespace ProximityPrize.SubmissionLower.AlignmentProtocol6454Conditional

open ProximityPrize.Benchmark
open CoreDefinitions ProximityGap ToyProblem
open scoped NNReal

noncomputable section ProtocolProofs

def radius6454 : ℝ≥0 := claimedRadius 309299 1048576
def errors6454 : ℕ := 77324
def budget6454 : ℕ := 100000000000000000

theorem radius6454_floor :
    ⌊(radius6454 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ = errors6454 := by
  norm_num [radius6454, claimedRadius, errors6454, IRSProfile.Index]

theorem radius6454_cell_cross :
    309299 * Fintype.card IRSProfile.Index < (errors6454 + 1) * 1048576 := by
  norm_num [IRSProfile.Index, errors6454]

theorem radius6454_gap : 131071 < Fintype.card IRSProfile.Index - errors6454 := by
  norm_num [IRSProfile.Index, errors6454]

theorem field_cardinality :
    Fintype.card IRSProfile.Field = (2130706433 : ℕ) ^ 6 := by
  norm_num [IRSProfile.Field, KoalaBear.Ext6, KoalaBear.fieldSize]

theorem budget6454_lt_field : budget6454 < Fintype.card IRSProfile.Field := by
  rw [field_cardinality]
  norm_num [budget6454]

theorem sixteen_row_separation_gate :
    15 * (budget6454 + 1).choose 2 < Fintype.card IRSProfile.Field := by
  rw [field_cardinality, Nat.choose_eq_descFactorial_div_factorial]
  norm_num [budget6454, Nat.descFactorial_succ, Nat.factorial_succ]

/-- Both the MCA allowance and the newly derived list allowance are B. -/
theorem doubled_budget6454_nat :
    2 ^ (128 : ℕ) * (budget6454 + budget6454) ≤ Fintype.card IRSProfile.Field := by
  rw [field_cardinality]
  norm_num [budget6454]

/-- Upper, not lower, rational approximation to the hundredth root of two. -/
theorem two_rpow_one_hundred_le :
    (2 : ℝ≥0) ^ ((1 : ℝ) / 100) ≤ (100696 : ℝ≥0) / 100000 := by
  have hroot :
      ((2 : ℝ≥0) ^ (1 : ℕ)) ^ ((100 : ℝ)⁻¹) ≤ (100696 : ℝ≥0) / 100000 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 100)]
    norm_num [NNReal.rpow_natCast, div_pow, le_div_iff₀]
  calc
    (2 : ℝ≥0) ^ ((1 : ℝ) / 100) =
        ((2 : ℝ≥0) ^ (1 : ℕ)) ^ ((100 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ (100696 : ℝ≥0) / 100000 := hroot

/-- This exact rational inequality involves only the actual 128 repetitions. -/
theorem radius6454_power_rational_bound :
    (1 - radius6454) ^ IRSProfile.repetitions ≤
      ((1 : ℝ≥0) / 2 ^ (64 : ℕ)) * (100000 / 100696) ^ (54 : ℕ) := by
  rw [← NNReal.coe_le_coe]
  norm_num [radius6454, claimedRadius, IRSProfile.repetitions, div_le_iff₀]

theorem radius6454_score :
    (1 - radius6454) ^ IRSProfile.repetitions ≤ claimedError 6454 := by
  have hscaleOne :
      (100000 : ℝ≥0) / 100696 ≤ (2 : ℝ≥0) ^ (-((1 : ℝ) / 100)) := by
    calc
      (100000 : ℝ≥0) / 100696 = 1 / ((100696 : ℝ≥0) / 100000) := by norm_num
      _ ≤ 1 / ((2 : ℝ≥0) ^ ((1 : ℝ) / 100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_one_hundred_le
      _ = (2 : ℝ≥0) ^ (-((1 : ℝ) / 100)) := by
        rw [one_div, NNReal.rpow_neg]
  have hscale :
      ((100000 : ℝ≥0) / 100696) ^ (54 : ℕ) ≤
        (2 : ℝ≥0) ^ (-((54 : ℝ) / 100)) := by
    calc
      ((100000 : ℝ≥0) / 100696) ^ (54 : ℕ) ≤
          ((2 : ℝ≥0) ^ (-((1 : ℝ) / 100))) ^ (54 : ℕ) :=
        pow_le_pow_left₀ (by positivity) hscaleOne 54
      _ = (2 : ℝ≥0) ^ (-((54 : ℝ) / 100)) := by
        rw [← NNReal.rpow_mul_natCast]
        norm_num
  calc
    (1 - radius6454) ^ IRSProfile.repetitions ≤
        ((1 : ℝ≥0) / 2 ^ (64 : ℕ)) * (100000 / 100696) ^ (54 : ℕ) :=
      radius6454_power_rational_bound
    _ ≤ ((1 : ℝ≥0) / 2 ^ (64 : ℕ)) *
        (2 : ℝ≥0) ^ (-((54 : ℝ) / 100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError 6454 := by
      unfold claimedError
      rw [show -((((6454 : ℕ) : ℝ) / 100)) =
          -((64 : ℕ) : ℝ) + -((54 : ℝ) / 100) by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0)]
      simp only [NNReal.rpow_neg, NNReal.rpow_natCast, one_div]

/-- An actual module-code identity, proved using the verified row interface. -/
theorem irs_code_eq_base_interleaved :
    IRSProfile.code =
      (IRSProfile.baseCode ^⋈ (Fin IRSProfile.interleaving) :
        ModuleCode IRSProfile.Index IRSProfile.Field
          (Fin IRSProfile.interleaving → IRSProfile.Field)) := by
  ext v
  change v ∈ IRSProfile.code ↔
    ∀ b : Fin IRSProfile.interleaving, (fun i => v i b) ∈ IRSProfile.baseCode
  exact AlignmentInterleavedLambda.irs_code_mem_iff_rows v

theorem base_mca6454_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6454 budget6454) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode (radius6454 : ℝ) ≤
      ENNReal.ofReal ((budget6454 : ℝ) / Fintype.card IRSProfile.Field) := by
  apply mcaError_affineLine_le_of_givenSetsBound
  apply givenSetsBound_of_alignmentBound IRSProfile.baseCode
    (radius6454 : ℝ) errors6454 budget6454
  · intro A hA
    have hcomp :=
      (mul_one_sub_le_card_iff_sub_card_le_floor A
        (show (0 : ℝ) ≤ (radius6454 : ℝ) by positivity)).mp hA
    rw [radius6454_floor] at hcomp
    have hn : Fintype.card IRSProfile.Index = 262144 := by norm_num [IRSProfile.Index]
    rw [hn]
    norm_num [errors6454] at hcomp ⊢
    omega
  · exact halign

theorem mca6454_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6454 budget6454) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code (radius6454 : ℝ) ≤
      (budget6454 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) := by
  calc
    _ ≤ mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (radius6454 : ℝ) := by
      rw [irs_code_eq_base_interleaved]
      exact ProximityGap.mcaError_interleaved_le IRSProfile.baseCode
        IRSProfile.interleaving radius6454
        (by norm_num [IRSProfile.interleaving])
        (by norm_num [radius6454, claimedRadius])
        (by norm_num [radius6454, claimedRadius])
    _ ≤ ENNReal.ofReal ((budget6454 : ℝ) / Fintype.card IRSProfile.Field) :=
      base_mca6454_le_of_alignment halign
    _ = (budget6454 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]

/-- The new finite list allowance, on exactly the protected squared alphabet. -/
theorem lambda6454_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6454 budget6454) :
    Code.Lambda
      ((IRSProfile.code ^⋈ (Fin 2) :
        ModuleCode IRSProfile.Index IRSProfile.Field
          (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
        Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
      (radius6454 : ℝ) ≤ (budget6454 : ℕ∞) :=
  AlignmentInterleavedLambda.irs_squared_claimedRadius_lambda_le
    309299 1048576 errors6454 budget6454 (by norm_num) radius6454_cell_cross
    radius6454_gap halign budget6454_lt_field sixteen_row_separation_gate

/-- A local copy of the elementary generic ENNReal field-budget calculation;
no 6400 parameter module or old list estimate is needed. -/
theorem nat_div_le_inv_pow {m q t : ℕ} (hm : 0 < m) (hq : m * 2 ^ t ≤ q) :
    (m : ENNReal) / (q : ENNReal) ≤ 1 / 2 ^ t := by
  have hm0 : (m : ENNReal) ≠ 0 := by exact_mod_cast hm.ne'
  have hmtop : (m : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top m
  have hqE : ((m * 2 ^ t : ℕ) : ENNReal) ≤ (q : ENNReal) := by exact_mod_cast hq
  have hcast : ((m * 2 ^ t : ℕ) : ENNReal) = (m : ENNReal) * 2 ^ t := by
    push_cast
    ring
  calc
    (m : ENNReal) / (q : ENNReal) ≤
        (m : ENNReal) / ((m * 2 ^ t : ℕ) : ENNReal) := ENNReal.div_le_div_left hqE _
    _ = (m : ENNReal) / ((m : ENNReal) * 2 ^ t) := by rw [hcast]
    _ = (m : ENNReal) * 1 / ((m : ENNReal) * 2 ^ t) := by rw [mul_one]
    _ = 1 / 2 ^ t := ENNReal.mul_div_mul_left 1 (2 ^ t) hm0 hmtop

theorem certifiedGammaError6454_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6454 budget6454) :
    certifiedGammaError IRSProfile.code radius6454 ≤ (1 : ℝ≥0) / 2 ^ (128 : ℕ) := by
  rw [← ENNReal.coe_le_coe, coe_certifiedGammaError]
  push_cast
  have hLambdaNat := ENat.toNat_le_of_le_coe (lambda6454_le_of_alignment halign)
  have hList :
      ((Code.Lambda
        ((IRSProfile.code ^⋈ (Fin 2) :
          ModuleCode IRSProfile.Index IRSProfile.Field
            (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
          Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
        (radius6454 : ℝ)).toNat : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) ≤
        (budget6454 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) :=
    ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
  calc
    _ ≤ (budget6454 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) +
        (budget6454 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) :=
      add_le_add (mca6454_le_of_alignment halign) hList
    _ = ((budget6454 + budget6454 : ℕ) : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [← ENNReal.add_div, Nat.cast_add]
    _ ≤ (1 : ENNReal) / 2 ^ (128 : ℕ) := by
      apply nat_div_le_inv_pow
      · norm_num [budget6454]
      · simpa only [Nat.mul_comm] using doubled_budget6454_nat

/-- Exact protected target, conditional only on the new strong alignment
theorem. This module does not itself assert that alignment premise. -/
theorem protocolClaim6454_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode
      77324 100000000000000000) :
    ProtocolClaim 6454 309299 1048576 where
  admissible := by
    constructor <;> norm_num [claimedRadius, IRSProfile.minRelativeDistance]
  reduction := by
    have h : certifiedGammaError IRSProfile.code radius6454 ≤ reductionTarget :=
      (certifiedGammaError6454_le_of_alignment halign).trans
        (by norm_num [reductionTarget, ProximityGap.prizeThreshold, div_le_iff₀])
    have hc : ReedSolomon.Interleaved.irsCode IRSProfile.domain
        IRSProfile.totalDimension IRSProfile.interleaving = IRSProfile.code := rfl
    rw [ToyProblem.Impl.IRS.certifiedGammaError, hc]
    exact h
  score := radius6454_score

end ProtocolProofs

#print axioms radius6454_floor
#print axioms radius6454_cell_cross
#print axioms radius6454_gap
#print axioms field_cardinality
#print axioms budget6454_lt_field
#print axioms sixteen_row_separation_gate
#print axioms doubled_budget6454_nat
#print axioms two_rpow_one_hundred_le
#print axioms radius6454_power_rational_bound
#print axioms radius6454_score
#print axioms irs_code_eq_base_interleaved
#print axioms base_mca6454_le_of_alignment
#print axioms mca6454_le_of_alignment
#print axioms lambda6454_le_of_alignment
#print axioms nat_div_le_inv_pow
#print axioms certifiedGammaError6454_le_of_alignment
#print axioms protocolClaim6454_of_alignment

end ProximityPrize.SubmissionLower.AlignmentProtocol6454Conditional
