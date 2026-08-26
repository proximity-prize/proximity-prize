import ProximityPrize.SubmissionLower.BCHKSSphericalL3IncidenceBridge6401

/-!
# Conditional analytic endpoint at score 64.01

The radius, score, squared-list bound, interleaving transport, and exact
`2^-128` field ledger are closed here.  The only hypothesis is the direct
chosen-set/MCA statement at the largest numerator left after reserving the
proved spherical list bound.  In particular, this helper imports no
unfinished alignment extractor.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSFinalConditional6401

open ProximityPrize.Benchmark
open CoreDefinitions ProximityGap ToyProblem
open BCHKSList6401
open BCHKSSphericalL3IncidenceBridge6401
open scoped NNReal

/-- Largest MCA numerator compatible with the exact spherical list term. -/
def mcaNumerator6401 : ℕ := maxMCANumeratorAfterList6401

/-- The single direct code-theoretic premise of the score-64.01 wrapper. -/
def GivenSetsClosure6401 : Prop :=
  AffineLineGivenSetsBound IRSProfile.baseCode
    (bchksRadius6401 : ℝ) mcaNumerator6401

/-- Stronger alignment interface retained only as a convenience for an
extractor that happens to produce a global codeword line. -/
def AlignmentClosure6401 : Prop :=
  AffineLineAlignmentBound IRSProfile.baseCode
    bchksErrors6401 mcaNumerator6401

private lemma nat_div_le_inv_pow {m q t : ℕ}
    (hm : 0 < m) (hq : m * 2 ^ t ≤ q) :
    (m : ENNReal) / (q : ENNReal) ≤ 1 / 2 ^ t := by
  have hm0 : (m : ENNReal) ≠ 0 := by exact_mod_cast hm.ne'
  have hmtop : (m : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top m
  have hqE : ((m * 2 ^ t : ℕ) : ENNReal) ≤ (q : ENNReal) := by
    exact_mod_cast hq
  have hcast : ((m * 2 ^ t : ℕ) : ENNReal) =
      (m : ENNReal) * 2 ^ t := by
    push_cast
    ring
  calc
    (m : ENNReal) / (q : ENNReal) ≤
        (m : ENNReal) / ((m * 2 ^ t : ℕ) : ENNReal) :=
      ENNReal.div_le_div_left hqE _
    _ = (m : ENNReal) / ((m : ENNReal) * 2 ^ t) := by rw [hcast]
    _ = (m : ENNReal) * 1 / ((m : ENNReal) * 2 ^ t) := by rw [mul_one]
    _ = 1 / 2 ^ t := ENNReal.mul_div_mul_left 1 (2 ^ t) hm0 hmtop

/-- Independent recomputation of the exact field/list allowance used by the
wrapper. -/
theorem field_and_list_ledger_exact6401 :
    mcaNumerator6401 = 274980728094349243 ∧
    mcaNumerator6401 + listBound6401 = 274980728111395087 ∧
    2 ^ (128 : ℕ) * (mcaNumerator6401 + listBound6401) ≤
      (2130706433 : ℕ) ^ 6 := by
  norm_num [mcaNumerator6401, maxMCANumeratorAfterList6401,
    BCHKSSubfieldListBudgetAudit6401.exactFieldNumerator6401,
    listBound6401]

/-- `274980728111395087` is not merely a convenient lower bound: it is the
exact floor of `2130706433^6 / 2^128`. -/
theorem field_numerator_floor_exact6401 :
    (2130706433 : ℕ) ^ 6 =
        2 ^ (128 : ℕ) * 274980728111395087 +
          301186360634199111531904678745128042497 ∧
    (2130706433 : ℕ) ^ 6 <
      2 ^ (128 : ℕ) * (274980728111395087 + 1) := by
  norm_num

/-- Independent wrapper-facing check of the radius cell, agreement count,
and score inequality. -/
theorem radius_agreement_score_exact6401 :
    ProximityPrize.Benchmark.claimedRadius 307161 1048576 =
        bchksRadius6401 ∧
    ⌊(bchksRadius6401 : ℝ) *
        (Fintype.card IRSProfile.Index : ℝ)⌋₊ = 76790 ∧
    262144 - 76790 = 185354 ∧
    (1 - bchksRadius6401) ^ IRSProfile.repetitions ≤
      ProximityPrize.Benchmark.claimedError 6401 := by
  refine ⟨?_, bchksRadius6401_floor, by norm_num,
    bchksRadius6401_score⟩
  norm_num [ProximityPrize.Benchmark.claimedRadius, bchksRadius6401]

/-- A conventional global alignment extractor implies the direct chosen-set
premise, with the radius-to-error conversion checked at the exact rational
radius. -/
theorem givenSetsClosure_of_alignment
    (halign : AlignmentClosure6401) : GivenSetsClosure6401 := by
  apply givenSetsBound_of_alignmentBound IRSProfile.baseCode
    (bchksRadius6401 : ℝ) bchksErrors6401 mcaNumerator6401
  · intro A hA
    have hcomp :=
      (mul_one_sub_le_card_iff_sub_card_le_floor A
        (show (0 : ℝ) ≤ (bchksRadius6401 : ℝ) by positivity)).mp hA
    rw [bchksRadius6401_floor] at hcomp
    have hn : Fintype.card IRSProfile.Index = 262144 := by
      norm_num [IRSProfile.Index]
    rw [hn]
    norm_num [bchksErrors6401] at hcomp ⊢
    omega
  · exact halign

/-- The direct chosen-set premise gives the base-code MCA numerator. -/
lemma base_mca_le_of_givenSets (hgiven : GivenSetsClosure6401) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (bchksRadius6401 : ℝ) ≤
      ENNReal.ofReal
        ((mcaNumerator6401 : ℝ) / Fintype.card IRSProfile.Field) := by
  exact mcaError_affineLine_le_of_givenSetsBound IRSProfile.baseCode
    (bchksRadius6401 : ℝ) mcaNumerator6401 hgiven

/-- Lift the base-code MCA estimate through the benchmark's eight-fold
interleaving. -/
lemma mca_le_of_givenSets (hgiven : GivenSetsClosure6401) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
        (bchksRadius6401 : ℝ) ≤
      (mcaNumerator6401 : ENNReal) /
        (Fintype.card IRSProfile.Field : ENNReal) := by
  calc
    _ ≤ mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (bchksRadius6401 : ℝ) := by
      simpa [IRSProfile.code, IRSProfile.baseCode,
        ReedSolomon.Interleaved.irsCode,
        IRSProfile.totalDimension_div_interleaving] using
        (ProximityGap.mcaError_interleaved_le IRSProfile.baseCode
          IRSProfile.interleaving bchksRadius6401
          (by norm_num [IRSProfile.interleaving])
          (by norm_num [bchksRadius6401])
          (by norm_num [bchksRadius6401]))
    _ ≤ ENNReal.ofReal ((mcaNumerator6401 : ℝ) /
          Fintype.card IRSProfile.Field) := base_mca_le_of_givenSets hgiven
    _ = (mcaNumerator6401 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]

/-- Completed analytic reduction at score 64.01, conditional only on the
direct chosen-set theorem. -/
theorem certifiedGammaError_le_of_givenSets
    (hgiven : GivenSetsClosure6401) :
    certifiedGammaError IRSProfile.code bchksRadius6401 ≤
      (1 : ℝ≥0) / 2 ^ (128 : ℕ) := by
  rw [← ENNReal.coe_le_coe, coe_certifiedGammaError]
  push_cast
  have hLambdaNat :
      (Code.Lambda SquaredCode6401 (bchksRadius6401 : ℝ)).toNat ≤
        listBound6401 :=
    ENat.toNat_le_of_le_coe bchks6401_lambda_le
  have hList :
      ((Code.Lambda SquaredCode6401
        (bchksRadius6401 : ℝ)).toNat : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) ≤
        (listBound6401 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) :=
    ENNReal.div_le_div_right (by exact_mod_cast hLambdaNat) _
  calc
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.code
          (bchksRadius6401 : ℝ) +
        ((Code.Lambda
          ((IRSProfile.code ^⋈ (Fin 2) :
            ModuleCode IRSProfile.Index IRSProfile.Field
              (Fin 2 → Fin IRSProfile.interleaving → IRSProfile.Field)) :
            Set (IRSProfile.Index → Fin 2 → Fin IRSProfile.interleaving →
              IRSProfile.Field))
          (bchksRadius6401 : ℝ)).toNat : ENNReal) /
            (Fintype.card IRSProfile.Field : ENNReal) ≤
      (mcaNumerator6401 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) +
        (listBound6401 : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) := by
      apply add_le_add (mca_le_of_givenSets hgiven)
      simpa [SquaredCode6401] using hList
    _ = ((mcaNumerator6401 + listBound6401 : ℕ) : ENNReal) /
          (Fintype.card IRSProfile.Field : ENNReal) := by
      rw [← ENNReal.add_div]
      norm_num
    _ ≤ (1 : ENNReal) / 2 ^ (128 : ℕ) := by
      apply nat_div_le_inv_pow
      · norm_num [mcaNumerator6401, maxMCANumeratorAfterList6401,
          BCHKSSubfieldListBudgetAudit6401.exactFieldNumerator6401,
          listBound6401]
      · simpa [IRSProfile.Field, KoalaBear.Ext6, KoalaBear.fieldSize,
          Nat.mul_comm] using field_and_list_ledger_exact6401.2.2

/-- Alignment-flavoured corollary for a prospective extractor. -/
theorem certifiedGammaError_le_of_alignment
    (halign : AlignmentClosure6401) :
    certifiedGammaError IRSProfile.code bchksRadius6401 ≤
      (1 : ℝ≥0) / 2 ^ (128 : ℕ) :=
  certifiedGammaError_le_of_givenSets (givenSetsClosure_of_alignment halign)

end BCHKSFinalConditional6401
end ProximityPrize.SubmissionLower

namespace ProximityPrize.Benchmark

open ToyProblem
open scoped NNReal

/-- Score-64.01 `ProtocolClaim`, conditional only on the isolated direct
chosen-set premise. -/
theorem protocolClaim6401_of_givenSets
    (hgiven :
      ProximityPrize.SubmissionLower.BCHKSFinalConditional6401.GivenSetsClosure6401) :
    ProtocolClaim 6401 307161 1048576 where
  admissible := by
    constructor <;>
      norm_num [claimedRadius, IRSProfile.minRelativeDistance]
  reduction := by
    have h : ToyProblem.certifiedGammaError IRSProfile.code
        ProximityPrize.SubmissionLower.bchksRadius6401 ≤ reductionTarget :=
      (ProximityPrize.SubmissionLower.BCHKSFinalConditional6401.certifiedGammaError_le_of_givenSets
        hgiven).trans (by
          norm_num [reductionTarget, ProximityGap.prizeThreshold, div_le_iff₀])
    have hr : claimedRadius 307161 1048576 =
        ProximityPrize.SubmissionLower.bchksRadius6401 := by
      norm_num [claimedRadius, ProximityPrize.SubmissionLower.bchksRadius6401]
    have hc :
        ReedSolomon.Interleaved.irsCode IRSProfile.domain
            IRSProfile.totalDimension IRSProfile.interleaving =
          IRSProfile.code := by
      rfl
    rw [ToyProblem.Impl.IRS.certifiedGammaError, hr, hc]
    exact h
  score := by
    have hr : claimedRadius 307161 1048576 =
        ProximityPrize.SubmissionLower.bchksRadius6401 := by
      norm_num [claimedRadius, ProximityPrize.SubmissionLower.bchksRadius6401]
    rw [hr]
    exact ProximityPrize.SubmissionLower.bchksRadius6401_score

end ProximityPrize.Benchmark
