import ProximityPrize.SubmissionLower.BCHKSList6401
import ProximityPrize.SubmissionLower.BCHKSParameters6399

/-!
# Exact audit of the 63.99-seed curve boost at score 64.01

Goyal--Guruswami, Theorem 3.6 (restated as Goyal--Guruswami--Sun--
Wootters, Theorem 2.8), has the following radius profile.  A weak
`(ell, delta, a, b)` curve-decoding theorem and list decoding at

`delta * (1 + ell / (b - ell))`

give a stronger curve-decoding theorem **at the original radius `delta`**.
The list radius is inflated; the conclusion radius is not.

At the present integers, `ell = 1` and `b = 3839` do place the inflated
63.99 list radius in the same Hamming cell as the score-64.01 radius.  The
field condition and the final numerator also fit by a wide margin.  But the
unconditional seed has only `76770` errors, whereas score 64.01 permits
`76790`.  Consequently the source theorem returns a strengthened result at
the 63.99 radius and does not prove the required 64.01 result without a new
radius-transfer lemma.

Primary sources:

* R. Goyal and V. Guruswami, *Optimal Proximity Gaps for Subspace-Design
  Codes and (Random) Reed-Solomon Codes*, Theorem 3.6.
* R. Goyal, V. Guruswami, Y. Sun, and M. Wootters, *Locality of
  Curve-Decoding and Improved Proximity Gaps*, Theorem 2.8.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSSeedCurveBoostNoGo6401

open ProximityPrize.Benchmark
open BCHKSList6401
open scoped NNReal

/-- A legal weakening of the `76772`-point output of the unconditional
score-63.99 alignment seed. -/
def weakCurveOutput6401 : ℕ := 3839

/-- The list radius occurring in the source-faithful line (`ell = 1`)
boost, starting from the exact score-63.99 radius. -/
noncomputable def inflatedSeedListRadius6401 : ℝ≥0 :=
  bchksRadius6399 * weakCurveOutput6401 / (weakCurveOutput6401 - 1)

/-- `AffineLineAlignmentBound` uses the strict premise
`bchksNumerator6399 < |S|`, so its inclusive curve-decoding input threshold
is one larger. -/
def inclusiveSeedInput6401 : ℕ := bchksNumerator6399 + 1

/-- Theorem 3.6 with final output `n+1` charges `n * L` in addition to the
inclusive weak-seed threshold. -/
def boostedMCAInput6401 : ℕ :=
  262144 * listBound6401 + inclusiveSeedInput6401

/-- The protocol additionally charges one standalone copy of the squared
list bound. -/
def boostedCertifiedNumerator6401 : ℕ :=
  boostedMCAInput6401 + listBound6401

/-- The inflated exact 63.99 radius lands strictly between `76790` and
`76791` errors. -/
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

/-- A proposition-valued rendering of the radius profile in the primary
source theorem.  The abstract predicates keep this audit independent of a
particular formalization of curve- and list-decodability.

Crucially, both occurrences of `Curve` use the very same `delta`. -/
def SourceFaithfulLineBoost
    (Curve : ℝ≥0 → ℕ → ℕ → Prop)
    (List : ℝ≥0 → ℕ → Prop) : Prop :=
  ∀ (delta : ℝ≥0) (a b T L : ℕ),
    1 < b →
    List (delta * b / (b - 1)) L →
    Curve delta a b →
    Curve delta ((T - 1) * L + a) T

/-- Direct specialization of the source theorem.  Its conclusion is visibly
at `bchksRadius6399`; the inflated radius occurs only in the list premise. -/
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

/-- The exact additional hypothesis needed to turn the source-faithful
conclusion into the score-64.01 conclusion.  Neither GG Theorem 3.6 nor its
GGSW restatement supplies this radius transfer. -/
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

/-- Everything numerical in the proposed boost works:

* the seed output can be weakened to `3839`;
* the inflated exact 63.99 radius and the 64.01 radius both allow `76790`
  errors;
* the degree-one field condition holds over the six-degree challenge field;
* the boosted MCA numerator, including the standalone list charge, fits the
  exact 128-bit field numerator.

The final two clauses isolate the fatal seam: the seed radius is strictly
smaller and its Hamming cell allows twenty fewer errors. -/
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
