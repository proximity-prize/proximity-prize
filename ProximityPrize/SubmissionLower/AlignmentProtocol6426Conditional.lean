import ProximityPrize.SubmissionLower.AlignmentInterleavedLambda
import ProximityPrize.SubmissionLower.NearbyScoreCertificate

/-!
# Conditional protocol certificate at 64.26 bits

Model label: gpt-5.
Research source base: cb4383c9414a5aff86809df81cbb33a02a193824.

This isolated draft changes no accepted candidate or protected source.
The sole mathematical premise of the final theorem is the explicit strong
alignment bound at 77045 errors with budget 110000000000000000. The actual
squared-eight Code.Lambda, scalar-to-interleaved MCA transfer, field capacity
and protected score conversion are derived using the accepted generic route.

The integer constants were checked remotely in job 229522. This new source
still requires remote Lean verification and a complete dependency-closed build.
The score proof instantiates NearbyScoreCertificate with d=26, u=120, v=100:
an upper rational root certificate and the actual 128th-power certificate.
It does not assume the separate 12800th-power diagnostic, an alignment
premise without proof, or an accepted new submission.
-/

namespace ProximityPrize.SubmissionLower.AlignmentProtocol6426Conditional

open ProximityPrize.Benchmark
open CoreDefinitions ProximityGap ToyProblem
open scoped NNReal

noncomputable section ProtocolProofs

def radius6426 : ℝ≥0 := claimedRadius 308183 1048576
def errors6426 : ℕ := 77045
def budget6426 : ℕ := 110000000000000000

theorem radius6426_floor :
    ⌊(radius6426 : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ = errors6426 := by
  norm_num [radius6426, claimedRadius, errors6426, IRSProfile.Index]

theorem radius6426_cell_cross :
    308183 * Fintype.card IRSProfile.Index < (errors6426 + 1) * 1048576 := by
  norm_num [IRSProfile.Index, errors6426]

theorem radius6426_gap : 131071 < Fintype.card IRSProfile.Index - errors6426 := by
  norm_num [IRSProfile.Index, errors6426]

theorem field_cardinality :
    Fintype.card IRSProfile.Field = (2130706433 : ℕ) ^ 6 := by
  norm_num [IRSProfile.Field, KoalaBear.Ext6, KoalaBear.fieldSize]

theorem budget6426_lt_field : budget6426 < Fintype.card IRSProfile.Field := by
  rw [field_cardinality]
  norm_num [budget6426]

theorem sixteen_row_separation_gate :
    15 * (budget6426 + 1).choose 2 < Fintype.card IRSProfile.Field := by
  rw [field_cardinality, Nat.choose_eq_descFactorial_div_factorial]
  norm_num [budget6426, Nat.descFactorial_succ, Nat.factorial_succ]

/-- Both the MCA allowance and the newly derived list allowance are B. -/
theorem doubled_budget6426_nat :
    2 ^ (128 : ℕ) * (budget6426 + budget6426) ≤ Fintype.card IRSProfile.Field := by
  rw [field_cardinality]
  norm_num [budget6426]

/-- Upper rational certificate for 2^(26/100), proved as a Nat inequality. -/
theorem score6426_root_certificate :
    (2 : ℕ) ^ 26 * 100 ^ (100 : ℕ) ≤ 120 ^ (100 : ℕ) := by
  norm_num

/-- The 128-repetition certificate, with the natural radius gap explicit. -/
theorem score6426_spot_certificate :
    (2 : ℕ) ^ (64 : ℕ) * 120 * (1048576 - 308183) ^ (128 : ℕ) ≤
      100 * 1048576 ^ (128 : ℕ) := by
  norm_num

theorem radius6426_score :
    (1 - radius6426) ^ IRSProfile.repetitions ≤ claimedError 6426 := by
  change (1 - claimedRadius 308183 1048576) ^ IRSProfile.repetitions ≤
    claimedError (6400 + 26)
  exact NearbyScoreCertificate.protected_score_of_certificates
    26 308183 1048576 120 100
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    score6426_root_certificate score6426_spot_certificate

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

theorem base_mca6426_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6426 budget6426) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode (radius6426 : ℝ) ≤
      ENNReal.ofReal ((budget6426 : ℝ) / Fintype.card IRSProfile.Field) := by
  apply mcaError_affineLine_le_of_givenSetsBound
  apply givenSetsBound_of_alignmentBound IRSProfile.baseCode
    (radius6426 : ℝ) errors6426 budget6426
  · intro A hA
    have hcomp :=
      (mul_one_sub_le_card_iff_sub_card_le_floor A
        (show (0 : ℝ) ≤ (radius6426 : ℝ) by positivity)).mp hA
    rw [radius6426_floor] at hcomp
    have hn : Fintype.card IRSProfile.Index = 262144 := by norm_num [IRSProfile.Index]
    rw [hn]
    norm_num [errors6426] at hcomp ⊢
    omega
  · exact halign

theorem mca6426_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6426 budget6426) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code (radius6426 : ℝ) ≤
      (budget6426 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) := by
  calc
    _ ≤ mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (radius6426 : ℝ) := by
      rw [irs_code_eq_base_interleaved]
      exact ProximityGap.mcaError_interleaved_le IRSProfile.baseCode
        IRSProfile.interleaving radius6426
        (by norm_num [IRSProfile.interleaving])
        (by norm_num [radius6426, claimedRadius])
        (by norm_num [radius6426, claimedRadius])
    _ ≤ ENNReal.ofReal ((budget6426 : ℝ) / Fintype.card IRSProfile.Field) :=
      base_mca6426_le_of_alignment halign
    _ = (budget6426 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]

/-- The new finite list allowance, on exactly the protected squared alphabet. -/
theorem lambda6426_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6426 budget6426) :
    Code.Lambda
      ((IRSProfile.code ^⋈ (Fin 2) :
        ModuleCode IRSProfile.Index IRSProfile.Field
          (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
        Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
      (radius6426 : ℝ) ≤ (budget6426 : ℕ∞) :=
  AlignmentInterleavedLambda.irs_squared_claimedRadius_lambda_le
    308183 1048576 errors6426 budget6426 (by norm_num) radius6426_cell_cross
    radius6426_gap halign budget6426_lt_field sixteen_row_separation_gate

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

theorem certifiedGammaError6426_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors6426 budget6426) :
    certifiedGammaError IRSProfile.code radius6426 ≤ (1 : ℝ≥0) / 2 ^ (128 : ℕ) := by
  rw [← ENNReal.coe_le_coe, coe_certifiedGammaError]
  push_cast
  have hLambdaNat := ENat.toNat_le_of_le_coe (lambda6426_le_of_alignment halign)
  have hList :
      ((Code.Lambda
        ((IRSProfile.code ^⋈ (Fin 2) :
          ModuleCode IRSProfile.Index IRSProfile.Field
            (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
          Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field))
        (radius6426 : ℝ)).toNat : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) ≤
        (budget6426 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) :=
    ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
  calc
    _ ≤ (budget6426 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) +
        (budget6426 : ENNReal) / (Fintype.card IRSProfile.Field : ENNReal) :=
      add_le_add (mca6426_le_of_alignment halign) hList
    _ = ((budget6426 + budget6426 : ℕ) : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [← ENNReal.add_div, Nat.cast_add]
    _ ≤ (1 : ENNReal) / 2 ^ (128 : ℕ) := by
      apply nat_div_le_inv_pow
      · norm_num [budget6426]
      · simpa only [Nat.mul_comm] using doubled_budget6426_nat

/-- Exact protected target, conditional only on the new strong alignment
theorem. This module does not itself assert that alignment premise. -/
theorem protocolClaim6426_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode
      77045 110000000000000000) :
    ProtocolClaim 6426 308183 1048576 where
  admissible := by
    constructor <;> norm_num [claimedRadius, IRSProfile.minRelativeDistance]
  reduction := by
    have h : certifiedGammaError IRSProfile.code radius6426 ≤ reductionTarget :=
      (certifiedGammaError6426_le_of_alignment halign).trans
        (by norm_num [reductionTarget, ProximityGap.prizeThreshold, div_le_iff₀])
    have hc : ReedSolomon.Interleaved.irsCode IRSProfile.domain
        IRSProfile.totalDimension IRSProfile.interleaving = IRSProfile.code := rfl
    rw [ToyProblem.Impl.IRS.certifiedGammaError, hc]
    exact h
  score := radius6426_score

end ProtocolProofs

#print axioms radius6426_floor
#print axioms radius6426_cell_cross
#print axioms radius6426_gap
#print axioms field_cardinality
#print axioms budget6426_lt_field
#print axioms sixteen_row_separation_gate
#print axioms doubled_budget6426_nat
#print axioms score6426_root_certificate
#print axioms score6426_spot_certificate
#print axioms radius6426_score
#print axioms irs_code_eq_base_interleaved
#print axioms base_mca6426_le_of_alignment
#print axioms mca6426_le_of_alignment
#print axioms lambda6426_le_of_alignment
#print axioms nat_div_le_inv_pow
#print axioms certifiedGammaError6426_le_of_alignment
#print axioms protocolClaim6426_of_alignment

end ProximityPrize.SubmissionLower.AlignmentProtocol6426Conditional
