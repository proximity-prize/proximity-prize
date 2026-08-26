import ProximityPrize.SubmissionLower.BCHKSCoreQuotientHenselAudit6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSBranchwiseHybridAudit6400

open BCHKSHybridHighDegreeAudit6400

/-!
Branchwise audit of the degree-129 hybrid ledger.

The order-stability, full-order leading-coefficient, and global-radical
exceptions are needed by the low-degree mixed-Gao branch; the ordinary
universal-Hensel branch does not use them.  The common-core transformed
universal branch needs leading survival only on its actual core.  Consequently
these costs must not be charged on the full `Y+Z` mass independently of the
branch partition.

For the low factors, write `zL` and `yL` for their aggregate `Y+Z` and
`Y` degrees.  The three low-only `Z`-linear charges are

* `162224689 * zL` for the expensive mixed-Gao rows;
* `131072 * zL` for full-core leading-coefficient survival;
* `262144 * zL` for the `Z` part of order stability.

If the squarefree-radical obstruction is built only from the low factors,
its degree is at most `2*yL*zL`, hence at most `2*84607*zL`.  Their combined
`Z` coefficient is therefore `162787119`.  The remaining low `Y` coefficient
is `344071635 + 262144 = 344333779` (cheap rows plus the `Y` part of order
stability).

This restriction of the radical is semantically sound only after a mixed
selector routes every challenge having a high-factor owner to the high
branch; a low-routed challenge then needs separability/collision control only
among the low factors.  The theorems below deliberately take the restricted
radical bound as a hypothesis.  They do not assert that the missing mixed
selector has already been assembled.

Combining this accounting with the common-core quotient transform changes
the exact degree-129 endpoint from codimension `130229` to `130680`, i.e. a
full-order core of only `391` coordinates.  Codimension `130681` is the first
miss for this linear branchwise envelope.
-/

def branchwiseCoordinateCount6400 : Nat := 262144
def branchwiseFullCoreCoefficient6400 : Nat := 131072
def branchwiseCheapYCoefficient6400 : Nat := 344071635

def branchwiseLowZCoefficient6400 : Nat := 162787119
def branchwiseLowYCoefficient6400 : Nat := 344333779

def branchwiseUniversalDegree129Coefficient6400 : Nat := 163276977
def branchwiseUniversalDegree129Total6400 : Nat := 275799943344346504

def branchwiseCoreCodimEndpoint6400 : Nat := 130680
def branchwiseCoreCardEndpoint6400 : Nat := 391
def branchwiseCoreExponentEndpoint6400 : Nat := 261359
def branchwiseCoreCoefficientEndpoint6400 : Nat := 162789825
def branchwiseCoreEffectiveCoefficientEndpoint6400 : Nat := 162790216
def branchwiseCoreTotalEndpoint6400 : Nat := 274977815976037796

def branchwiseCoreFirstMissCodim6400 : Nat := 130681
def branchwiseCoreFirstMissCard6400 : Nat := 390
def branchwiseCoreFirstMissCoefficient6400 : Nat := 162791070
def branchwiseCoreFirstMissEffectiveCoefficient6400 : Nat := 162791460
def branchwiseCoreFirstMissTotal6400 : Nat := 274979917061470228

lemma branchwise_low_coefficients_exact6400 :
    branchwiseLowZCoefficient6400 =
        bchksHybridLowZCoefficient6400 +
          branchwiseFullCoreCoefficient6400 +
          branchwiseCoordinateCount6400 +
          2 * bchksHybridYMass6400 /\
      branchwiseLowYCoefficient6400 =
        branchwiseCheapYCoefficient6400 + branchwiseCoordinateCount6400 /\
      branchwiseLowZCoefficient6400 <
        branchwiseCoreCoefficientEndpoint6400 := by
  norm_num [branchwiseLowZCoefficient6400,
    bchksHybridLowZCoefficient6400,
    branchwiseFullCoreCoefficient6400,
    branchwiseCoordinateCount6400, bchksHybridYMass6400,
    branchwiseLowYCoefficient6400, branchwiseCheapYCoefficient6400,
    branchwiseCoreCoefficientEndpoint6400]

/-- Abstract branchwise aggregation.  `radicalLow` is explicitly the
restricted low-factor radical charge; no common-core coverage is assumed.
-/
theorem branchwise_charge_le
    (highCoefficient zLow zHigh yLow expensiveLow universalHigh cheapLow
      fullCoreLow orderLow radicalLow : Nat)
    (hzMass : zLow + zHigh <= bchksHybridZMass6400)
    (hyMass : yLow <= bchksHybridYMass6400)
    (hexpensive : expensiveLow <=
      bchksHybridLowZCoefficient6400 * zLow)
    (huniversal : universalHigh <= highCoefficient * zHigh)
    (hcheap : cheapLow <= branchwiseCheapYCoefficient6400 * yLow)
    (hfullCore : fullCoreLow <= branchwiseFullCoreCoefficient6400 * zLow)
    (horder : orderLow <=
      branchwiseCoordinateCount6400 * (zLow + yLow))
    (hradical : radicalLow <= 2 * yLow * zLow)
    (hcoefficient : branchwiseLowZCoefficient6400 <= highCoefficient) :
    expensiveLow + universalHigh + cheapLow + fullCoreLow + orderLow +
        radicalLow <=
      highCoefficient * bchksHybridZMass6400 +
        branchwiseLowYCoefficient6400 * bchksHybridYMass6400 := by
  have hradical' : radicalLow <= 2 * bchksHybridYMass6400 * zLow := by
    calc
      radicalLow <= 2 * yLow * zLow := hradical
      _ <= 2 * bchksHybridYMass6400 * zLow := by
        exact Nat.mul_le_mul_right zLow (Nat.mul_le_mul_left 2 hyMass)
  have hlow :
      expensiveLow + cheapLow + fullCoreLow + orderLow + radicalLow <=
        branchwiseLowZCoefficient6400 * zLow +
          branchwiseLowYCoefficient6400 * yLow := by
    norm_num [branchwiseLowZCoefficient6400,
      bchksHybridLowZCoefficient6400,
      branchwiseFullCoreCoefficient6400,
      branchwiseCoordinateCount6400, bchksHybridYMass6400,
      branchwiseLowYCoefficient6400,
      branchwiseCheapYCoefficient6400] at *
    omega
  calc
    expensiveLow + universalHigh + cheapLow + fullCoreLow + orderLow +
        radicalLow <=
      branchwiseLowZCoefficient6400 * zLow +
        highCoefficient * zHigh +
        branchwiseLowYCoefficient6400 * yLow := by omega
    _ <= highCoefficient * (zLow + zHigh) +
        branchwiseLowYCoefficient6400 * yLow := by
      simpa [Nat.mul_add, Nat.add_assoc] using
        Nat.add_le_add_right
          (Nat.add_le_add_right
            (Nat.mul_le_mul_right zLow hcoefficient)
            (highCoefficient * zHigh))
          (branchwiseLowYCoefficient6400 * yLow)
    _ <= highCoefficient * bchksHybridZMass6400 +
        branchwiseLowYCoefficient6400 * bchksHybridYMass6400 := by
      gcongr

/-- The honest branchwise degree-129 universal envelope still misses.  It
refunds the low-only global charges but does not pretend that this alone is
a solution. -/
lemma branchwise_degree129_universal_noGo6400 :
    branchwiseLowZCoefficient6400 <
        branchwiseUniversalDegree129Coefficient6400 /\
      branchwiseUniversalDegree129Total6400 =
        branchwiseUniversalDegree129Coefficient6400 *
            bchksHybridZMass6400 +
          branchwiseLowYCoefficient6400 * bchksHybridYMass6400 +
          bchksHybridPairCardCover6400 + bchksHybridQBadCover6400 /\
      bchksWeightedNumerator6400 < branchwiseUniversalDegree129Total6400 /\
      branchwiseUniversalDegree129Total6400 - bchksWeightedNumerator6400 =
        820943344346504 := by
  norm_num [branchwiseLowZCoefficient6400,
    branchwiseUniversalDegree129Coefficient6400,
    branchwiseUniversalDegree129Total6400,
    bchksHybridZMass6400, branchwiseLowYCoefficient6400,
    bchksHybridYMass6400, bchksHybridPairCardCover6400,
    bchksHybridQBadCover6400, bchksWeightedNumerator6400]

/-- Exact common-core quotient endpoint after the branchwise refund. -/
lemma branchwise_core_endpoint6400 :
    branchwiseCoreCodimEndpoint6400 + branchwiseCoreCardEndpoint6400 =
        131071 /\
      branchwiseCoreExponentEndpoint6400 =
        2 * branchwiseCoreCodimEndpoint6400 - 1 /\
      branchwiseCoreCoefficientEndpoint6400 =
        ((262144 - 131071) *
              (branchwiseCoreExponentEndpoint6400 * (2 * 129)) +
            (262144 - bchksErrors6400 - 131071) - 1) /
            (262144 - bchksErrors6400 - 131071) + 2 * 129 /\
      branchwiseCoreEffectiveCoefficientEndpoint6400 =
        branchwiseCoreCoefficientEndpoint6400 +
          branchwiseCoreCardEndpoint6400 /\
      branchwiseCoreTotalEndpoint6400 =
        branchwiseCoreEffectiveCoefficientEndpoint6400 *
            bchksHybridZMass6400 +
          branchwiseLowYCoefficient6400 * bchksHybridYMass6400 +
          bchksHybridPairCardCover6400 + bchksHybridQBadCover6400 /\
      branchwiseCoreTotalEndpoint6400 < bchksWeightedNumerator6400 /\
      bchksWeightedNumerator6400 - branchwiseCoreTotalEndpoint6400 =
        1184023962204 := by
  norm_num [branchwiseCoreCodimEndpoint6400,
    branchwiseCoreCardEndpoint6400, branchwiseCoreExponentEndpoint6400,
    branchwiseCoreCoefficientEndpoint6400,
    branchwiseCoreEffectiveCoefficientEndpoint6400,
    branchwiseCoreTotalEndpoint6400,
    bchksErrors6400, bchksHybridZMass6400,
    branchwiseLowYCoefficient6400, bchksHybridYMass6400,
    bchksHybridPairCardCover6400, bchksHybridQBadCover6400,
    bchksWeightedNumerator6400]

/-- One further codimension step is the first arithmetic miss for the same
linear envelope. -/
lemma branchwise_core_firstMiss6400 :
    branchwiseCoreFirstMissCoefficient6400 =
        ((262144 - 131071) *
              ((2 * branchwiseCoreFirstMissCodim6400 - 1) * (2 * 129)) +
            (262144 - bchksErrors6400 - 131071) - 1) /
            (262144 - bchksErrors6400 - 131071) + 2 * 129 /\
      branchwiseLowZCoefficient6400 <
        branchwiseCoreFirstMissCoefficient6400 /\
      branchwiseCoreFirstMissEffectiveCoefficient6400 =
        branchwiseCoreFirstMissCoefficient6400 +
          branchwiseCoreFirstMissCard6400 /\
      branchwiseCoreFirstMissTotal6400 =
        branchwiseCoreFirstMissEffectiveCoefficient6400 *
            bchksHybridZMass6400 +
          branchwiseLowYCoefficient6400 * bchksHybridYMass6400 +
          bchksHybridPairCardCover6400 + bchksHybridQBadCover6400 /\
      bchksWeightedNumerator6400 < branchwiseCoreFirstMissTotal6400 /\
      branchwiseCoreFirstMissTotal6400 - bchksWeightedNumerator6400 =
        917061470228 := by
  norm_num [branchwiseCoreFirstMissCodim6400,
    branchwiseCoreFirstMissCard6400,
    branchwiseCoreFirstMissCoefficient6400,
    branchwiseCoreFirstMissEffectiveCoefficient6400,
    branchwiseCoreFirstMissTotal6400, branchwiseLowZCoefficient6400,
    bchksErrors6400, bchksHybridZMass6400,
    branchwiseLowYCoefficient6400, bchksHybridYMass6400,
    bchksHybridPairCardCover6400, bchksHybridQBadCover6400,
    bchksWeightedNumerator6400]

end BCHKSBranchwiseHybridAudit6400
end ProximityPrize.SubmissionLower
