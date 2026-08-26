import ProximityPrize.SubmissionLower.BCHKSParameters6401

/-!
# Polynomial-generator MCA theorem: exact score-6401 Johnson obstruction

The Reed--Solomon theorem of Bordage--Chiesa--Guan--Manzur (CCC 2026,
Theorem 5 / full-version Theorem 9.2) assumes, for some integer `m >= 3`,
agreement fraction at least

`(1 + 1 / (2*m)) * sqrt(rate)`.

For the score-6401 row the Reed--Solomon length is `262144`, its dimension is
`131072`, and the guaranteed agreement is `185354`.  This file records the
fatal comparison without real-number rounding: even the limiting Johnson
condition fails by `3633052` after squaring.  The least integral agreement
strictly above the square-root threshold is `185364`, ten coordinates larger
than the benchmark guarantee.  Consequently the paper's stronger finite-`m`
hypothesis fails for every allowed tradeoff parameter.

This is only a route audit.  It does not assert that the desired weak curve
seed is false.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSPolynomialGeneratorMCAJohnsonNoGo6401

def paperRSLength6401 : Nat := 262144
def paperRSDimension6401 : Nat := 131072
def paperAgreement6401 : Nat := bchksAgreements6401
def paperErrors6401 : Nat := bchksErrors6401

theorem paperRSParameters_exact6401 :
    paperRSLength6401 = 262144 /\
      paperRSDimension6401 = 131072 /\
      paperAgreement6401 = 185354 /\
      paperErrors6401 = 76790 /\
      paperRSLength6401 - paperAgreement6401 = paperErrors6401 := by
  norm_num [paperRSLength6401, paperRSDimension6401, paperAgreement6401,
    paperErrors6401, bchksAgreements6401, bchksErrors6401]

/-- Exact failure of the limiting Johnson agreement condition. -/
theorem paperJohnsonSquare_deficit_exact6401 :
    paperAgreement6401 ^ 2 = 34356105316 /\
      paperRSLength6401 * paperRSDimension6401 = 34359738368 /\
      paperRSLength6401 * paperRSDimension6401 -
          paperAgreement6401 ^ 2 = 3633052 /\
      paperAgreement6401 ^ 2 <
          paperRSLength6401 * paperRSDimension6401 := by
  norm_num [paperAgreement6401, paperRSLength6401,
    paperRSDimension6401, bchksAgreements6401]

/-- The exact integral square-root ledger: `185364` is the first agreement
whose square is strictly above `n*k`, so score 6401 is ten agreements short. -/
theorem paperJohnson_firstIntegralAgreement_exact6401 :
    185363 ^ 2 <= paperRSLength6401 * paperRSDimension6401 /\
      paperRSLength6401 * paperRSDimension6401 < 185364 ^ 2 /\
      185364 - paperAgreement6401 = 10 := by
  norm_num [paperAgreement6401, paperRSLength6401,
    paperRSDimension6401, bchksAgreements6401]

/-- After clearing the positive denominator and squaring, the paper's
finite-`m` agreement premise would require the reverse of this inequality:

`(2*m*a)^2 >= (2*m+1)^2*n*k`.

It fails for every `m >= 3` (indeed, for every positive `m`). -/
theorem paperTheorem9_finiteTradeoff_threshold_fails6401
    (m : Nat) (hm : 3 <= m) :
    (2 * m * paperAgreement6401) ^ 2 <
      (2 * m + 1) ^ 2 * paperRSLength6401 * paperRSDimension6401 := by
  have hbase : paperAgreement6401 ^ 2 <
      paperRSLength6401 * paperRSDimension6401 :=
    paperJohnsonSquare_deficit_exact6401.2.2.2
  norm_num [paperAgreement6401, paperRSLength6401,
    paperRSDimension6401, bchksAgreements6401] at hbase ⊢
  nlinarith

end BCHKSPolynomialGeneratorMCAJohnsonNoGo6401
end ProximityPrize.SubmissionLower
