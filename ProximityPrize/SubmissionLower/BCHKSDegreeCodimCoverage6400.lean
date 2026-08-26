import ProximityPrize.SubmissionLower.BCHKSRaisedNumeratorEndpoint6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSDegreeCodimCoverage6400
open BCHKSBranchwiseHybridAudit6400
open BCHKSHybridHighDegreeAudit6400
open BCHKSRaisedNumeratorEndpoint6400
open BCHKSTopEdgeSplitJetCap6400
def raisedSplitFixedCover6400 : Nat :=
  branchwiseSplitLowYCoefficient6400 * bchksHybridYMass6400 +
    bchksHybridPairCardCover6400 + bchksHybridQBadCover6400
def raisedSplitCoreCoefficientLimit6400 : Nat := 162792401
def quotientExponent6400 (s : Nat) : Nat := 2 * s - 1
def quotientRawCoefficient6400 (d s : Nat) : Nat :=
  ((262144 - 131071) *
        (quotientExponent6400 s * (2 * d)) +
      (262144 - bchksErrors6400 - 131071) - 1) /
      (262144 - bchksErrors6400 - 131071) +
    2 * d
def quotientEffectiveCoefficient6400 (d s : Nat) : Nat :=
  quotientRawCoefficient6400 d s + (131071 - s)
def quotientRaisedSplitTotal6400 (d s : Nat) : Nat :=
  quotientEffectiveCoefficient6400 d s * bchksHybridZMass6400 +
    raisedSplitFixedCover6400
lemma raisedSplit_coefficientLimit_exact6400 :
    raisedSplitFixedCover6400 = 28334726220011 /\
      raisedSplitCoreCoefficientLimit6400 * bchksHybridZMass6400 +
          raisedSplitFixedCover6400 = 274980699880342639 /\
      bchksResidualNumerator6400 -
          (raisedSplitCoreCoefficientLimit6400 * bchksHybridZMass6400 +
            raisedSplitFixedCover6400) = 119657361 := by
  norm_num [raisedSplitFixedCover6400,
    raisedSplitCoreCoefficientLimit6400,
    branchwiseSplitLowYCoefficient6400, bchksHybridYMass6400,
    bchksHybridPairCardCover6400, bchksHybridQBadCover6400,
    bchksHybridZMass6400, bchksResidualNumerator6400]
theorem quotientRaisedSplitTotal_lt_of_coefficient_le6400
    (d s : Nat)
    (h : quotientEffectiveCoefficient6400 d s <=
      raisedSplitCoreCoefficientLimit6400) :
    quotientRaisedSplitTotal6400 d s < bchksResidualNumerator6400 := by
  calc
    quotientRaisedSplitTotal6400 d s <=
        raisedSplitCoreCoefficientLimit6400 * bchksHybridZMass6400 +
          raisedSplitFixedCover6400 := by
      unfold quotientRaisedSplitTotal6400
      exact Nat.add_le_add_right
        (Nat.mul_le_mul_right bchksHybridZMass6400 h) _
    _ < bchksResidualNumerator6400 := by
      norm_num [raisedSplitCoreCoefficientLimit6400,
        bchksHybridZMass6400, raisedSplitFixedCover6400,
        branchwiseSplitLowYCoefficient6400, bchksHybridYMass6400,
        bchksHybridPairCardCover6400, bchksHybridQBadCover6400,
        bchksResidualNumerator6400]
lemma degree128_allCodim_coefficient6400 :
    quotientEffectiveCoefficient6400 128 131071 = 162011187 /\
      quotientEffectiveCoefficient6400 128 131071 <
        raisedSplitCoreCoefficientLimit6400 := by
  norm_num [quotientEffectiveCoefficient6400,
    quotientRawCoefficient6400, quotientExponent6400,
    raisedSplitCoreCoefficientLimit6400, bchksErrors6400]
lemma degree129_exactCoreEndpoint6400 :
    quotientEffectiveCoefficient6400 129 130681 = 162791460 /\
      quotientRaisedSplitTotal6400 129 130681 = 274979110554464891 /\
      quotientRaisedSplitTotal6400 129 130681 <
        bchksResidualNumerator6400 /\
      quotientEffectiveCoefficient6400 129 130682 = 162792705 /\
      bchksResidualNumerator6400 <
        quotientRaisedSplitTotal6400 129 130682 /\
      quotientRaisedSplitTotal6400 129 130682 -
          bchksResidualNumerator6400 = 513328872751 := by
  norm_num [quotientEffectiveCoefficient6400,
    quotientRawCoefficient6400, quotientExponent6400,
    quotientRaisedSplitTotal6400, raisedSplitFixedCover6400,
    branchwiseSplitLowYCoefficient6400, bchksHybridYMass6400,
    bchksHybridPairCardCover6400, bchksHybridQBadCover6400,
    bchksHybridZMass6400, bchksResidualNumerator6400,
    bchksErrors6400]
lemma quotientCoverage_endpointTable6400 :
    quotientEffectiveCoefficient6400 130 129675 = 162791508 /\
    quotientEffectiveCoefficient6400 130 129676 = 162792762 /\
    quotientEffectiveCoefficient6400 131 128685 = 162792350 /\
    quotientEffectiveCoefficient6400 131 128686 = 162793614 /\
    quotientEffectiveCoefficient6400 256 65825 = 162791750 /\
    quotientEffectiveCoefficient6400 256 65826 = 162794221 /\
    quotientEffectiveCoefficient6400 512 32906 = 162791807 /\
    quotientEffectiveCoefficient6400 512 32907 = 162796750 /\
    quotientEffectiveCoefficient6400 1000 16846 = 162788410 /\
    quotientEffectiveCoefficient6400 1000 16847 = 162798065 /\
    quotientEffectiveCoefficient6400 84607 199 = 162479677 /\
    quotientEffectiveCoefficient6400 84607 200 = 163296701 := by
  norm_num [quotientEffectiveCoefficient6400,
    quotientRawCoefficient6400, quotientExponent6400,
    bchksErrors6400]
end BCHKSDegreeCodimCoverage6400
end ProximityPrize.SubmissionLower
