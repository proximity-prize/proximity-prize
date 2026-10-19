import ProximityPrize.SubmissionBinaryLower.BCHKSList

namespace ProximityPrize.SubmissionBinaryLower

open ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open CoreDefinitions ProximityGap ToyProblem
open scoped NNReal

lemma bchks_nat_div_le_inv_pow {m q t : ℕ} (hm : 0 < m) (hq : m * 2 ^ t ≤ q) :
    (m : ENNReal) / (q : ENNReal) ≤ 1 / 2 ^ t := by
  have hm0 : (m : ENNReal) ≠ 0 := by exact_mod_cast hm.ne'
  have hmtop : (m : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top m
  have hqE : ((m * 2 ^ t : ℕ) : ENNReal) ≤ (q : ENNReal) := by exact_mod_cast hq
  have hcast : ((m * 2 ^ t : ℕ) : ENNReal) = (m : ENNReal) * 2 ^ t := by
    push_cast
    ring
  calc
    (m : ENNReal) / (q : ENNReal) ≤
        (m : ENNReal) / ((m * 2 ^ t : ℕ) : ENNReal) :=
      ENNReal.div_le_div_left hqE _
    _ = (m : ENNReal) / ((m : ENNReal) * 2 ^ t) := by rw [hcast]
    _ = (m : ENNReal) * 1 / ((m : ENNReal) * 2 ^ t) := by rw [mul_one]
    _ = 1 / 2 ^ t := ENNReal.mul_div_mul_left 1 (2 ^ t) hm0 hmtop

lemma mca_bchks_le_of_alignment
    (halign : AffineLineAlignmentBound BinaryIRSProfile.baseCode bchksErrors bchksNumerator) :
    mcaError (AffineLineGenerator BinaryIRSProfile.Field) BinaryIRSProfile.code
        (bchksRadius : ℝ) ≤
      (bchksNumerator : ENNReal) / (Fintype.card BinaryIRSProfile.Field : ENNReal) := by
  calc
    _ ≤ mcaError (AffineLineGenerator BinaryIRSProfile.Field) BinaryIRSProfile.baseCode
        (bchksRadius : ℝ) := by
      simpa [BinaryIRSProfile.code, BinaryIRSProfile.baseCode,
        ReedSolomon.Interleaved.irsCode,
        BinaryIRSProfile.totalDimension_div_interleaving] using
        (ProximityGap.mcaError_interleaved_le BinaryIRSProfile.baseCode
          BinaryIRSProfile.interleaving bchksRadius
          (by norm_num [BinaryIRSProfile.interleaving])
          (by norm_num [bchksRadius]) (by norm_num [bchksRadius]))
    _ ≤ ENNReal.ofReal ((bchksNumerator : ℝ) /
          Fintype.card BinaryIRSProfile.Field) := base_mca_bchks_le_of_alignment halign
    _ = (bchksNumerator : ENNReal) /
          (Fintype.card BinaryIRSProfile.Field : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]

/-- All reduction and score arithmetic is complete; only the BCHKS alignment extractor remains. -/
theorem certifiedGammaError_bchks_le_of_alignment
    (halign : AffineLineAlignmentBound BinaryIRSProfile.baseCode bchksErrors bchksNumerator) :
    certifiedGammaError BinaryIRSProfile.code bchksRadius ≤
      (1 : ℝ≥0) / 2 ^ (128 : ℕ) := by
  rw [← ENNReal.coe_le_coe, coe_certifiedGammaError]
  push_cast
  have hLambdaNat :
      (Code.Lambda BCHKSSquaredCode (bchksRadius : ℝ)).toNat ≤ bchksListBound :=
    ENat.toNat_le_of_le_coe bchks_lambda_le
  have hList :
      ((Code.Lambda BCHKSSquaredCode (bchksRadius : ℝ)).toNat : ENNReal) /
          (Fintype.card BinaryIRSProfile.Field : ENNReal) ≤
        (bchksListBound : ENNReal) /
          (Fintype.card BinaryIRSProfile.Field : ENNReal) :=
    ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
  calc
    mcaError (AffineLineGenerator BinaryIRSProfile.Field) BinaryIRSProfile.code
          (bchksRadius : ℝ) +
        ((Code.Lambda
          ((BinaryIRSProfile.code ^⋈ (Fin 2) :
            ModuleCode BinaryIRSProfile.Index BinaryIRSProfile.Field
              (Fin 2 → Fin BinaryIRSProfile.interleaving → BinaryIRSProfile.Field)) :
            Set (BinaryIRSProfile.Index → Fin 2 → Fin BinaryIRSProfile.interleaving → BinaryIRSProfile.Field))
          (bchksRadius : ℝ)).toNat : ENNReal) /
            (Fintype.card BinaryIRSProfile.Field : ENNReal) ≤
      (bchksNumerator : ENNReal) /
          (Fintype.card BinaryIRSProfile.Field : ENNReal) +
        (bchksListBound : ENNReal) /
          (Fintype.card BinaryIRSProfile.Field : ENNReal) := by
      apply add_le_add (mca_bchks_le_of_alignment halign)
      simpa [BCHKSSquaredCode] using hList
    _ = ((bchksNumerator + bchksListBound : ℕ) : ENNReal) /
          (Fintype.card BinaryIRSProfile.Field : ENNReal) := by
      rw [← ENNReal.add_div]
      norm_num
    _ ≤ (1 : ENNReal) / 2 ^ (128 : ℕ) := by
      apply bchks_nat_div_le_inv_pow
      · norm_num [bchksNumerator, bchksListBound]
      · rw [show Fintype.card BinaryIRSProfile.Field = 2 ^ (192 : ℕ) from BF64.card_ext3]
        simpa [Nat.mul_comm] using bchks_budget_nat

end ProximityPrize.SubmissionBinaryLower
