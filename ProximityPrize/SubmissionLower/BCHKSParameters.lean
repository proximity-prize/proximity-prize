import ProximityPrize.SubmissionLower.BCHKSBridge

namespace ProximityPrize.SubmissionLower

open ProximityPrize.Benchmark
open CoreDefinitions ProximityGap
open scoped NNReal

/-- Radius chosen for a 63.94-bit claim after the specialized BCHKS extraction. -/
noncomputable def bchksRadius : ℝ≥0 := (306887 : ℝ≥0) / 1048576

def bchksErrors : ℕ := 76721

def bchksNumerator : ℕ := 274980000000000000

def bchksListBound : ℕ := 5000

/-- Slack reserved for bad specializations without changing the sharp multiplicity target. -/
def bchksBadBudget : ℕ := 1000000000000

lemma bchksRadius_floor :
    ⌊(bchksRadius : ℝ) * (Fintype.card IRSProfile.Index : ℝ)⌋₊ = bchksErrors := by
  norm_num [bchksRadius, bchksErrors, IRSProfile.Index]

lemma bchksRadius_floor_nnreal :
    ⌊bchksRadius * (Fintype.card IRSProfile.Index : ℝ≥0)⌋₊ = bchksErrors := by
  norm_num [bchksRadius, bchksErrors, IRSProfile.Index]

/-- The MCA numerator and Johnson-list contribution fit the 128-bit field budget. -/
lemma bchks_budget_nat :
    2 ^ (128 : ℕ) * (bchksNumerator + bchksListBound) ≤
      (2130706433 : ℕ) ^ 6 := by
  norm_num [bchksNumerator, bchksListBound]

/-- Rational lower approximation to `2^(6/100)`, used by the score certificate. -/
theorem two_rpow_six_hundred_ge :
    (521 : ℝ≥0) / 500 ≤ (2 : ℝ≥0) ^ ((6 : ℝ) / 100) := by
  have hroot :
      (521 : ℝ≥0) / 500 ≤
        ((2 : ℝ≥0) ^ (6 : ℕ)) ^ ((100 : ℝ)⁻¹) := by
    rw [NNReal.le_rpow_inv_iff (by norm_num : (0 : ℝ) < 100)]
    norm_num [div_pow, div_le_iff₀]
  calc
    (521 : ℝ≥0) / 500 ≤
        ((2 : ℝ≥0) ^ (6 : ℕ)) ^ ((100 : ℝ)⁻¹) := hroot
    _ = (2 : ℝ≥0) ^ ((6 : ℝ) / 100) := by
      rw [← NNReal.rpow_natCast_mul]
      norm_num [div_eq_mul_inv]

/-- Standalone score arithmetic for the intended `ProtocolClaim 6394`. -/
lemma bchksRadius_score :
    (1 - bchksRadius) ^ IRSProfile.repetitions ≤
      ProximityPrize.Benchmark.claimedError 6394 := by
  calc
    (1 - bchksRadius) ^ IRSProfile.repetitions ≤
        ((1 : ℝ≥0) / 2 ^ (64 : ℕ)) * (521 / 500) := by
      rw [← NNReal.coe_le_coe]
      norm_num [bchksRadius, IRSProfile.repetitions, div_le_iff₀]
    _ ≤ ((1 : ℝ≥0) / 2 ^ (64 : ℕ)) *
          (2 : ℝ≥0) ^ ((6 : ℝ) / 100) := by
      exact mul_le_mul_of_nonneg_left two_rpow_six_hundred_ge (by positivity)
    _ = ProximityPrize.Benchmark.claimedError 6394 := by
      unfold ProximityPrize.Benchmark.claimedError
      rw [show -((((6394 : ℕ) : ℝ) / 100)) =
          -((64 : ℕ) : ℝ) + (6 : ℝ) / 100 by norm_num,
        NNReal.rpow_add (by norm_num : (2 : ℝ≥0) ≠ 0),
        NNReal.rpow_neg, NNReal.rpow_natCast]
      norm_num



/-- The optimized all-factor BCHKS accounting: summing the pair-specific
`2*DX*DZ*deg(R)*deg(H)` bounds costs only `DY²`, rather than a worst-case
extra factor of `DY`. -/
lemma bchks_all_factor_budget :
    632176 * 519143 * 852 ^ 2 + (bchksErrors + 1) * 852 <
      bchksNumerator := by
  norm_num [bchksErrors, bchksNumerator]




set_option maxRecDepth 100000 in
lemma bchksBadBudget_lt_field :
    bchksBadBudget < Fintype.card IRSProfile.Field := by
  have h := bchks_budget_nat
  have hp : 2 ^ (128 : ℕ) ≤ (2130706433 : ℕ) ^ 6 := by
    have hm : 1 ≤ bchksNumerator + bchksListBound := by
      norm_num [bchksNumerator, bchksListBound]
    exact (Nat.le_mul_of_pos_right (2 ^ (128 : ℕ)) (by omega)).trans h
  have hb : bchksBadBudget < 2 ^ (128 : ℕ) := by
    norm_num [bchksBadBudget]
  rw [CompPoly.Extension.Ext.card_ext]
  change bchksBadBudget < (2130706433 : ℕ) ^ 6
  exact hb.trans_le hp

lemma bchks_all_factor_budget_with_bad :
    632176 * 519143 * 852 ^ 2 + (bchksErrors + 1) * 852 +
      bchksBadBudget < bchksNumerator := by
  norm_num [bchksErrors, bchksBadBudget, bchksNumerator]

lemma card_sdiff_large_for_bchks {α : Type*} [DecidableEq α]
    (S Bad : Finset α) (hS : bchksNumerator < S.card)
    (hBad : (S ∩ Bad).card ≤ bchksBadBudget) :
    632176 * 519143 * 852 ^ 2 + (bchksErrors + 1) * 852 <
      (S \ Bad).card := by
  rw [Finset.card_sdiff]
  let M : ℕ := 632176 * 519143 * 852 ^ 2 + (bchksErrors + 1) * 852
  let B : ℕ := bchksBadBudget
  let N : ℕ := bchksNumerator
  have hbudget : M + B < N := by
    simpa [M, B, N] using bchks_all_factor_budget_with_bad
  change M < S.card - (Bad ∩ S).card
  change N < S.card at hS
  have hBad' : (Bad ∩ S).card ≤ B := by
    simpa [Finset.inter_comm] using hBad
  apply Nat.lt_sub_of_add_lt
  exact (Nat.add_le_add_left hBad' M) |>.trans_lt (hbudget.trans hS)

/-- A pair-specific BCHKS fiber above its `2*DX` weight budget has enough
incidences to provide `k+1` coordinates above the Claim-5.10 threshold. -/
lemma bchks_top_points_arithmetic (r T : ℕ)
    (hT : 2 * 111624646 * r + (bchksErrors + 1) < T) :
    (262144 - bchksErrors - 131072) * T >
      (262144 - 131072) * ((2 * 131071 + 1) * r) := by
  norm_num [bchksErrors] at hT ⊢
  nlinarith

/-- Once the BCHKS alignment extractor is supplied, its exact MCA consequence at the
optimized radius is immediate. -/
theorem base_mca_bchks_le_of_alignment
    (halign : AffineLineAlignmentBound IRSProfile.baseCode bchksErrors bchksNumerator) :
    mcaError (AffineLineGenerator IRSProfile.Field) IRSProfile.baseCode
        (bchksRadius : ℝ) ≤
      ENNReal.ofReal ((bchksNumerator : ℝ) / Fintype.card IRSProfile.Field) := by
  apply mcaError_affineLine_le_of_givenSetsBound
  apply givenSetsBound_of_alignmentBound IRSProfile.baseCode
    (bchksRadius : ℝ) bchksErrors bchksNumerator
  · intro A hA
    have hcomp :=
      (mul_one_sub_le_card_iff_sub_card_le_floor A
        (show (0 : ℝ) ≤ (bchksRadius : ℝ) by positivity)).mp hA
    rw [bchksRadius_floor] at hcomp
    have hn : Fintype.card IRSProfile.Index = 262144 := by
      norm_num [IRSProfile.Index]
    rw [hn]
    norm_num [bchksErrors] at hcomp ⊢
    omega
  · exact halign

end ProximityPrize.SubmissionLower
