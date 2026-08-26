import ProximityPrize.SubmissionLower.BCHKSDeepQuadraticAudit6400

namespace ProximityPrize.SubmissionLower

/-!
First audit of the genuine post-quadratic residual (`degY ≥ 3`).

For an irreducible degree-`d` factor, every nonzero identity slice has root
multiplicity at most `d`.  Thus its global ramification excess satisfies
`t ≤ (d-1)b ≤ (d-1)n`.  Combining this with failure of the hybrid repeated
repair gives an explicit weight cap.  The cubic endpoint is already too
large for a naive discriminant-resultant ledger, and, more fundamentally, a
cubic polynomial root does not force its discriminant to be a square.
-/

/-- Hybrid failure always bounds the factor weight by `k+ell+t` when the
initial margin exceeds the line overhead. -/
theorem deepHybridFailure_weight_lt
    (e w ell t : ℕ) (he : 2 ≤ e) (hell : ell < 868689)
    (hfail : (e - 1) * w + 868689 <
      ell + (e - 1) * (131071 + ell + t)) :
    w < 131071 + ell + t := by
  have hepos : 0 < e - 1 := by omega
  have hright :
      ell + (e - 1) * (131071 + ell + t) <
        868689 + (e - 1) * (131071 + ell + t) := by
    omega
  have hprod :
      (e - 1) * w < (e - 1) * (131071 + ell + t) := by
    omega
  exact (Nat.mul_lt_mul_left hepos).mp hprod

/-- Degree-sensitive cap obtained from `ν_i≤d` on at most `n` identity
coordinates. -/
theorem deepResidual_weight_lt_of_degree
    (d e w ell t : ℕ) (he : 2 ≤ e) (hell : ell ≤ 87382)
    (ht : t ≤ (d - 1) * 262144)
    (hfail : (e - 1) * w + 868689 <
      ell + (e - 1) * (131071 + ell + t)) :
    w < 131071 + 87382 + (d - 1) * 262144 := by
  have hw := deepHybridFailure_weight_lt e w ell t he (by omega) hfail
  omega

/-- Every residual cubic therefore has weight below `742741`. -/
lemma deepResidualCubic_weight_lt6400
    (e w ell t : ℕ) (he : 17 ≤ e) (hell : ell ≤ 87382)
    (ht : t ≤ 2 * 262144)
    (hfail : (e - 1) * w + 868689 <
      ell + (e - 1) * (131071 + ell + t)) :
    w < 742741 := by
  have hw := deepResidual_weight_lt_of_degree 3 e w ell t
    (by omega) hell (by norm_num at ht ⊢; exact ht) hfail
  norm_num at hw ⊢
  exact hw

/-- The weighted coefficient formula bounds the `X` degree of a cubic
discriminant by `(d-1)(2w-dk)`.  At the residual weight cap this is
`2184534`. -/
lemma deepResidualCubic_discriminantXCap6400 :
    2 * (2 * 742740 - 3 * 131071) = 2184534 := by
  norm_num

def bchksDeepCubicNaiveParityResultant6400 : ℕ := 64430642408574200

/-- Even granting a quadratic-style square-specialization property (which a
cubic root does not provide), the naive parity resultant would already cost
over five times all field room left after the global radical. -/
lemma bchksDeepCubicNaiveParity_noGo6400 :
    bchksDeepCubicNaiveParityResultant6400 =
        (2 * 2184534 - 1) * 4 * bchksDeepRepeatedZMass6400 ∧
      bchksWeightedNumerator6400 -
          bchksSixteenthDerivativeTwoLedgerCover6400 <
        bchksDeepCubicNaiveParityResultant6400 := by
  norm_num [bchksDeepCubicNaiveParityResultant6400,
    bchksDeepRepeatedZMass6400, bchksWeightedNumerator6400,
    bchksSixteenthDerivativeTwoLedgerCover6400]

/-- Endpoint check: for `d=3,e=17` and full overhead, the first residual
ramification excess is `223592`. -/
lemma bchksDeepCubicE17_firstResidual6400 :
    16 * (3 * 131071) + 868689 <
        87382 + 16 * (131071 + 87382 + 223592) ∧
      ¬ (16 * (3 * 131071) + 868689 <
        87382 + 16 * (131071 + 87382 + 223591)) := by
  norm_num

end ProximityPrize.SubmissionLower
