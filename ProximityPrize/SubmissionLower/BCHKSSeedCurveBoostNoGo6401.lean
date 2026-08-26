import ProximityPrize.SubmissionLower.BCHKSList6401
import ProximityPrize.SubmissionLower.BCHKSParameters6399
namespace ProximityPrize.SubmissionLower
namespace BCHKSSeedCurveBoostNoGo6401
open ProximityPrize.Benchmark
open BCHKSList6401
open scoped NNReal
def weakCurveOutput6401 : ℕ := 3839
noncomputable def inflatedSeedListRadius6401 : ℝ≥0 :=
  bchksRadius6399 * weakCurveOutput6401 / (weakCurveOutput6401 - 1)
def inclusiveSeedInput6401 : ℕ := bchksNumerator6399 + 1
def boostedMCAInput6401 : ℕ :=
  262144 * listBound6401 + inclusiveSeedInput6401
def boostedCertifiedNumerator6401 : ℕ :=
  boostedMCAInput6401 + listBound6401
theorem inflatedSeedListRadius_floor6401 :
    ⌊inflatedSeedListRadius6401 *
        (Fintype.card IRSProfile.Index : ℝ≥0)⌋₊ = bchksErrors6401 := by
  rw [Nat.floor_eq_iff (by positivity)]
  constructor
  · rw [← NNReal.coe_le_coe]
    norm_num [inflatedSeedListRadius6401, weakCurveOutput6401,
      bchksRadius6399, IRSProfile.Index, bchksErrors6401, div_eq_mul_inv]
  · rw [← NNReal.coe_lt_coe]
    norm_num [inflatedSeedListRadius6401, weakCurveOutput6401,
      bchksRadius6399, IRSProfile.Index, bchksErrors6401, div_eq_mul_inv]
def SourceFaithfulLineBoost
    (Curve : ℝ≥0 → ℕ → ℕ → Prop)
    (List : ℝ≥0 → ℕ → Prop) : Prop :=
  ∀ (delta : ℝ≥0) (a b T L : ℕ),
    1 < b →
    List (delta * b / (b - 1)) L →
    Curve delta a b →
    Curve delta ((T - 1) * L + a) T
theorem sourceFaithfulBoost_concludes_at_seedRadius6401
    (Curve : ℝ≥0 → ℕ → ℕ → Prop)
    (List : ℝ≥0 → ℕ → Prop)
    (hboost : SourceFaithfulLineBoost Curve List)
    (hlist : List inflatedSeedListRadius6401 listBound6401)
    (hseed : Curve bchksRadius6399 inclusiveSeedInput6401
      weakCurveOutput6401) :
    Curve bchksRadius6399 boostedMCAInput6401 262145 := by
  simpa [inflatedSeedListRadius6401, boostedMCAInput6401] using
    hboost bchksRadius6399 inclusiveSeedInput6401 weakCurveOutput6401
      262145 listBound6401 (by norm_num [weakCurveOutput6401]) hlist hseed
theorem targetConclusion_of_sourceFaithfulBoost_and_radiusTransfer6401
    (Curve : ℝ≥0 → ℕ → ℕ → Prop)
    (List : ℝ≥0 → ℕ → Prop)
    (hboost : SourceFaithfulLineBoost Curve List)
    (hlist : List inflatedSeedListRadius6401 listBound6401)
    (hseed : Curve bchksRadius6399 inclusiveSeedInput6401
      weakCurveOutput6401)
    (htransfer : Curve bchksRadius6399 boostedMCAInput6401 262145 →
      Curve bchksRadius6401 boostedMCAInput6401 262145) :
    Curve bchksRadius6401 boostedMCAInput6401 262145 :=
  htransfer (sourceFaithfulBoost_concludes_at_seedRadius6401
    Curve List hboost hlist hseed)
theorem proposedSeedBoost_exactLedger6401 :
    weakCurveOutput6401 ≤ bchksErrors6399 + 2 ∧
    ⌊inflatedSeedListRadius6401 *
        (Fintype.card IRSProfile.Index : ℝ≥0)⌋₊ = bchksErrors6401 ∧
    ⌊bchksRadius6401 *
        (Fintype.card IRSProfile.Index : ℝ≥0)⌋₊ = bchksErrors6401 ∧
    (listBound6401 + 1) ^ 2 < (2130706433 : ℕ) ^ 6 ∧
    boostedMCAInput6401 = 87795196510381448 ∧
    boostedCertifiedNumerator6401 = 87795196527427292 ∧
    boostedCertifiedNumerator6401 < 274980728111395087 ∧
    bchksRadius6399 < bchksRadius6401 ∧
    bchksErrors6399 + 20 = bchksErrors6401 := by
  rw [inflatedSeedListRadius_floor6401, bchksRadius6401_floor_nnreal]
  norm_num [weakCurveOutput6401, inflatedSeedListRadius6401,
    bchksRadius6399, bchksRadius6401, IRSProfile.Index,
    bchksErrors6399, bchksErrors6401, listBound6401,
    boostedMCAInput6401, inclusiveSeedInput6401,
    boostedCertifiedNumerator6401, bchksNumerator6399]
end BCHKSSeedCurveBoostNoGo6401
end ProximityPrize.SubmissionLower
