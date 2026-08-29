import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactSeedlessLambdaResearch
import ProximityPrize.SubmissionLower.ContactScore6630Research
import ProximityPrize.SubmissionLower.ContactSeedlessListBoundResearch

/-! # Split-budget protocol bridge

The affine-line count controls only MCA.  The seedless fixed-centre theorem
controls Lambda independently, so the two terms no longer have to share the
same allowance.
-/

namespace ProximityPrize.SubmissionLower.ContactSeedlessProtocolResearch

open ProximityPrize.Benchmark
open CoreDefinitions ProximityGap ToyProblem
open scoped NNReal

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000

def radius : ℝ≥0 := ContactScore6630Research.radius6630
def errors : ℕ := ContactScore6630Research.errors6630
def mcaBudget : ℕ := 274980727111395087

theorem field_cardinality :
    Fintype.card IRSProfile.Field = (2130706433 : ℕ) ^ 6 := by
  norm_num [IRSProfile.Field, KoalaBear.Ext6, KoalaBear.fieldSize]

theorem irs_code_eq_base_interleaved :
    IRSProfile.code =
      (IRSProfile.baseCode ^⋈ (Fin IRSProfile.interleaving) :
        ModuleCode IRSProfile.Index IRSProfile.Field
          (Fin IRSProfile.interleaving → IRSProfile.Field)) := by
  ext v
  change v ∈ IRSProfile.code ↔
    ∀ b : Fin IRSProfile.interleaving, (fun i => v i b) ∈ IRSProfile.baseCode
  exact AlignmentInterleavedLambda.irs_code_mem_iff_rows v

theorem nat_div_le_inv_pow {m q t : ℕ} (hm : 0 < m)
    (hq : m * 2 ^ t ≤ q) :
    (m : ENNReal) / (q : ENNReal) ≤ 1 / 2 ^ t := by
  have hm0 : (m : ENNReal) ≠ 0 := by exact_mod_cast hm.ne'
  have hmtop : (m : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top m
  have hqE : ((m * 2 ^ t : ℕ) : ENNReal) ≤ (q : ENNReal) := by
    exact_mod_cast hq
  have hcast : ((m * 2 ^ t : ℕ) : ENNReal) = (m : ENNReal) * 2 ^ t := by
    push_cast
    ring
  calc
    (m : ENNReal) / (q : ENNReal) ≤
        (m : ENNReal) / ((m * 2 ^ t : ℕ) : ENNReal) :=
      ENNReal.div_le_div_left (by positivity) hqE
    _ = (m : ENNReal) / ((m : ENNReal) * 2 ^ t) := by rw [hcast]
    _ = 1 / 2 ^ t := by
      rw [ENNReal.div_eq_inv_mul, mul_inv, ← mul_assoc,
        ENNReal.inv_mul_cancel hm0 hmtop, one_mul, one_div]

theorem field_capacity_split :
    (mcaBudget + ContactSeedlessListBoundResearch.listBudget) * 2 ^ 128 ≤
      (2130706433 : ℕ) ^ 6 := by
  decide

theorem mca_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget) :
    ((Code.Mca IRSProfile.code (radius : ℝ)).toNat : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) ≤
      (mcaBudget : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
  have hmcaNat := AlignmentInterleavedLambda.mca_interleaved_le_mca_base
    IRSProfile.baseCode (Fin IRSProfile.interleaving) (radius : ℝ)
  have hfloor :
      ⌊(radius : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ = errors :=
    ContactScore6630Research.radius6630_floor
  have hbaseNat :
      (Code.Mca IRSProfile.baseCode (radius : ℝ)).toNat ≤ mcaBudget := by
    rw [Code.mca_toNat_eq_mcaBound_floor IRSProfile.baseCode (radius : ℝ) hfloor]
    exact halign
  have htotalNat : (Code.Mca IRSProfile.code (radius : ℝ)).toNat ≤ mcaBudget :=
    hmcaNat.trans hbaseNat
  exact ENNReal.div_le_div_right (by exact_mod_cast htotalNat) _

theorem certifiedGammaError_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget) :
    certifiedGammaError IRSProfile.code radius ≤
      (1 : ℝ≥0) / 2 ^ (128 : ℕ) := by
  rw [← ENNReal.coe_le_coe, coe_certifiedGammaError]
  push_cast
  have hLambdaNat := ENat.toNat_le_of_le_coe lambda_le
  have hList :
      ((Code.Lambda
        ((IRSProfile.code ^⋈ (Fin 2) :
          ModuleCode IRSProfile.Index IRSProfile.Field
            (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
          Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
          IRSProfile.Field))
        (radius : ℝ)).toNat : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) ≤
        (ContactSeedlessListBoundResearch.listBudget : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) :=
    ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
  calc
    _ ≤ (mcaBudget : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) +
        (ContactSeedlessListBoundResearch.listBudget : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) :=
      add_le_add (mca_le_of_alignment halign) hList
    _ = ((mcaBudget + ContactSeedlessListBoundResearch.listBudget : ℕ) : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [← ENNReal.add_div, Nat.cast_add]
    _ ≤ (1 : ENNReal) / 2 ^ (128 : ℕ) := by
      apply nat_div_le_inv_pow
      · norm_num [mcaBudget, ContactSeedlessListBoundResearch.listBudget]
      · simpa only [Nat.mul_comm] using field_capacity_split

theorem protocolClaim6740_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget) :
    ProtocolClaim 6740 320651 1048576 where
  admissible := ContactScore6630Research.radius6630_admissible
  reduction := by
    change certifiedGammaError IRSProfile.code radius ≤ reductionTarget
    exact (certifiedGammaError_le_of_alignment halign).trans
      (by norm_num [reductionTarget, ProximityGap.prizeThreshold, div_le_iff₀])
  score := ContactScore6630Research.radius6630_score

theorem protocolClaim6750_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget) :
    ProtocolClaim 6740 320651 1048576 :=
  protocolClaim6740_of_alignment halign

theorem protocolClaim6730_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode errors mcaBudget) :
    ProtocolClaim 6740 320651 1048576 :=
  protocolClaim6740_of_alignment halign

end

end ProximityPrize.SubmissionLower.ContactSeedlessProtocolResearch
