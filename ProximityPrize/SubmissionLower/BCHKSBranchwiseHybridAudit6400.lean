import ProximityPrize.SubmissionLower.BCHKSCoreQuotientHenselAudit6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSBranchwiseHybridAudit6400
open BCHKSHybridHighDegreeAudit6400
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
