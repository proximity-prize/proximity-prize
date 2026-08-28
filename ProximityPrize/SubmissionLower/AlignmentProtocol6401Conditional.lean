import ProximityPrize.SubmissionLower.AlignmentInterleavedLambda

/-!
# Conditional protocol certificate at 64.88 bits

Model label: gpt-5.

The sole mathematical premise of the final theorem is the explicit strong
alignment bound at 77665 errors with budget 10^17. The actual squared-eight
Code.Lambda, scalar-to-interleaved MCA transfer, field capacity and score
conversion are derived below. No old Contact parameter or 6400 list module
is imported, and no Benchmark.candidate is declared.

The score proof uses a separately checked upper rational approximation to
2^(1/100) and a 128th-power rational inequality. It does not reuse the old
half-square 6400 argument or assume the historical 12800th-power witness.
-/

namespace ProximityPrize.SubmissionLower.AlignmentProtocol6401Conditional

open ProximityPrize.Benchmark
open CoreDefinitions ProximityGap ToyProblem
open scoped NNReal

noncomputable section ProtocolProofs

def radius6401 : ℝ≥0 := claimedRadius 313547 1048576
def errors6401 : ℕ := 78386
def budget6401 : ℕ := 137490364055697543

theorem radius6401_floor :
    ⌊(radius6401 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ = errors6401 := by
  norm_num [radius6401, claimedRadius, errors6401, IRSProfile.Index]

theorem radius6401_cell_cross :
    313547 * Fintype.card IRSProfile.Index < (errors6401 + 1) * 1048576 := by
  norm_num [IRSProfile.Index, errors6401]

theorem radius6401_gap : 131071 < Fintype.card IRSProfile.Index - errors6401 := by
  norm_num [IRSProfile.Index, errors6401]

theorem field_cardinality :
    Fintype.card IRSProfile.Field = (2130706433 : ℕ) ^ 6 := by
  norm_num [IRSProfile.Field, KoalaBear.Ext6, KoalaBear.fieldSize]

theorem budget6401_lt_field : budget6401 < Fintype.card IRSProfile.Field := by
  rw [field_cardinality]
  norm_num [budget6401]

theorem sixteen_row_separation_gate :
    15 * (budget6401 + 1).choose 2 < Fintype.card IRSProfile.Field := by
  rw [field_cardinality, Nat.choose_eq_descFactorial_div_factorial]
  norm_num [budget6401, Nat.descFactorial_succ, Nat.factorial_succ]

/-- Both the MCA allowance and the newly derived list allowance are B. -/
theorem doubled_budget6401_nat :
    2 ^ (128 : ℕ) * (budget6401 + budget6401) ≤ Fintype.card IRSProfile.Field := by
  rw [field_cardinality]
  norm_num [budget6401]

/-- Upper, not lower, rational approximation to the hundredth root of two. -/
theorem two_rpow_one_hundred_le :
    (2 : ℝ≥0) ^ ((1 : ℝ) / 100) ≤ (1006955551 : ℝ≥0) / 1000000000 := by
  have hroot :
      ((2 : ℝ≥0) ^ (1 : ℕ)) ^ ((100 : ℝ)⁻¹) ≤ (1006955551 : ℝ≥0) / 1000000000 := by
    rw [NNReal.rpow_inv_le_iff (by norm_num : (0 : ℝ) < 100)]
    norm_num [NNReal.rpow_natCast, div_pow, le_div_iff₀]
  calc
    (2 : ℝ≥0) ^ ((1 : ℝ) / 100) =
        ((2 : ℝ≥0) ^ (1 : ℕ)) ^ ((100 : ℝ)⁻¹) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]
    _ ≤ (1006955551 : ℝ≥0) / 1000000000 := hroot

/-- This exact rational inequality involves only the actual 128 repetitions. -/
theorem radius6401_power_rational_bound :
    (1 - radius6401) ^ IRSProfile.repetitions ≤
      ((1 : ℝ≥0) / 2 ^ (65 : ℕ)) * ((1000000000 : ℝ≥0) / 1006955551) ^ (60 : ℕ) := by
  rw [← NNReal.coe_le_coe]
  norm_num [radius6401, claimedRadius, IRSProfile.repetitions, div_pow,
    div_le_iff₀]

theorem radius6401_score :
    (1 - radius6401) ^ IRSProfile.repetitions ≤ claimedError 6560 := by
  have hbase : (1000000000 : ℝ≥0) / 1006955551 ≤ (2 : ℝ≥0) ^ (-((1 : ℝ) / 100)) := by
    calc
      (1000000000 : ℝ≥0) / 1006955551 = 1 / ((1006955551 : ℝ≥0) / 1000000000) := by norm_num
      _ ≤ 1 / ((2 : ℝ≥0) ^ ((1 : ℝ) / 100)) :=
        one_div_le_one_div_of_le (by positivity) two_rpow_one_hundred_le
      _ = (2 : ℝ≥0) ^ (-((1 : ℝ) / 100)) := by
        rw [one_div, NNReal.rpow_neg]
  have hscale :
      ((1000000000 : ℝ≥0) / 1006955551) ^ (60 : ℕ) ≤
        (2 : ℝ≥0) ^ (-((60 : ℝ) / 100)) := by
    calc
      ((1000000000 : ℝ≥0) / 1006955551) ^ (60 : ℕ) ≤
          ((2 : ℝ≥0) ^ (-((1 : ℝ) / 100))) ^ (60 : ℕ) :=
        pow_le_pow_left₀ (by positivity) hbase 60
      _ = (2 : ℝ≥0) ^ (-((60 : ℝ) / 100)) := by
        rw [← NNReal.rpow_natCast (((2 : ℝ≥0) ^ (-((1 : ℝ) / 100)))) 60,
          ← NNReal.rpow_mul]
        norm_num
  calc
    (1 - radius6401) ^ IRSProfile.repetitions ≤
        ((1 : ℝ≥0) / 2 ^ (65 : ℕ)) * ((1000000000 : ℝ≥0) / 1006955551) ^ (60 : ℕ) :=
      radius6401_power_rational_bound
    _ ≤ ((1 : ℝ≥0) / 2 ^ (65 : ℕ)) *
        (2 : ℝ≥0) ^ (-((60 : ℝ) / 100)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = claimedError 6560 := by
      unfold claimedError
      rw [show -((((6560 : ℕ) : ℝ) / 100)) =
          -((65 : ℕ) : ℝ) + -((60 : ℝ) / 100) by norm_num,
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

theorem base_mca6401_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6401 budget6401) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode (radius6401 : ℝ) ≤
      ENNReal.ofReal ((budget6401 : ℝ) / Fintype.card IRSProfile.Field) := by
  apply mcaError_affineLine_le_of_givenSetsBound
  apply givenSetsBound_of_alignmentBound IRSProfile.baseCode
    (radius6401 : ℝ) errors6401 budget6401
  · intro A hA
    have hcomp :=
      (mul_one_sub_le_card_iff_sub_card_le_floor A
        (show (0 : ℝ) ≤ (radius6401 : ℝ) by positivity)).mp hA
    rw [radius6401_floor] at hcomp
    have hn : Fintype.card IRSProfile.Index = 262144 := by norm_num [IRSProfile.Index]
    rw [hn]
    norm_num [errors6401] at hcomp ⊢
    omega
  · exact halign

theorem mca6401_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6401 budget6401) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code (radius6401 : ℝ) ≤
      (budget6401 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) := by
  calc
    _ ≤ mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (radius6401 : ℝ) := by
      rw [irs_code_eq_base_interleaved]
      exact ProximityGap.mcaError_interleaved_le IRSProfile.baseCode
        IRSProfile.interleaving radius6401
        (by norm_num [IRSProfile.interleaving])
        (by norm_num [radius6401, claimedRadius])
        (by norm_num [radius6401, claimedRadius])
    _ ≤ ENNReal.ofReal ((budget6401 : ℝ) / Fintype.card IRSProfile.Field) :=
      base_mca6401_le_of_alignment halign
    _ = (budget6401 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]

/-- The new finite list allowance, on exactly the protected squared alphabet. -/
theorem lambda6401_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6401 budget6401) :
    Code.Lambda
      ((IRSProfile.code ^⋈ (Fin 2) :
        ModuleCode IRSProfile.Index IRSProfile.Field
          (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
        Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
      (radius6401 : ℝ) ≤ (budget6401 : ℕ∞) :=
  AlignmentInterleavedLambda.irs_squared_claimedRadius_lambda_le
    313547 1048576 errors6401 budget6401 (by norm_num) radius6401_cell_cross
    radius6401_gap halign budget6401_lt_field sixteen_row_separation_gate

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

theorem certifiedGammaError6401_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6401 budget6401) :
    certifiedGammaError IRSProfile.code radius6401 ≤ (1 : ℝ≥0) / 2 ^ (128 : ℕ) := by
  rw [← ENNReal.coe_le_coe, coe_certifiedGammaError]
  push_cast
  have hLambdaNat := ENat.toNat_le_of_le_coe (lambda6401_le_of_alignment halign)
  have hList :
      ((Code.Lambda
        ((IRSProfile.code ^⋈ (Fin 2) :
          ModuleCode IRSProfile.Index IRSProfile.Field
            (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
          Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
        (radius6401 : ℝ)).toNat : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) ≤
        (budget6401 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) :=
    ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
  calc
    _ ≤ (budget6401 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) +
        (budget6401 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) :=
      add_le_add (mca6401_le_of_alignment halign) hList
    _ = ((budget6401 + budget6401 : ℕ) : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [← ENNReal.add_div, Nat.cast_add]
    _ ≤ (1 : ENNReal) / 2 ^ (128 : ℕ) := by
      apply nat_div_le_inv_pow
      · norm_num [budget6401]
      · simpa only [Nat.mul_comm] using doubled_budget6401_nat

/-- Exact protected target, conditional only on the new strong alignment
theorem. This module does not itself assert that alignment premise. -/
theorem protocolClaim6401_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode
      78386 137490364055697543) :
    ProtocolClaim 6560 313547 1048576 where
  admissible := by
    constructor <;> norm_num [claimedRadius, IRSProfile.minRelativeDistance]
  reduction := by
    have h : certifiedGammaError IRSProfile.code radius6401 ≤ reductionTarget :=
      (certifiedGammaError6401_le_of_alignment halign).trans
        (by norm_num [reductionTarget, ProximityGap.prizeThreshold, div_le_iff₀])
    have hc : ReedSolomon.Interleaved.irsCode IRSProfile.domain
        IRSProfile.totalDimension IRSProfile.interleaving = IRSProfile.code := rfl
    rw [ToyProblem.Impl.IRS.certifiedGammaError, hc]
    exact h
  score := radius6401_score

end ProtocolProofs

#print axioms radius6401_floor
#print axioms radius6401_cell_cross
#print axioms radius6401_gap
#print axioms field_cardinality
#print axioms budget6401_lt_field
#print axioms sixteen_row_separation_gate
#print axioms doubled_budget6401_nat
#print axioms two_rpow_one_hundred_le
#print axioms radius6401_power_rational_bound
#print axioms radius6401_score
#print axioms irs_code_eq_base_interleaved
#print axioms base_mca6401_le_of_alignment
#print axioms mca6401_le_of_alignment
#print axioms lambda6401_le_of_alignment
#print axioms nat_div_le_inv_pow
#print axioms certifiedGammaError6401_le_of_alignment
#print axioms protocolClaim6401_of_alignment

end ProximityPrize.SubmissionLower.AlignmentProtocol6401Conditional
