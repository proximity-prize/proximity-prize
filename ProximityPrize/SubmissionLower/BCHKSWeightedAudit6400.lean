import ProximityPrize.SubmissionLower.BCHKSParameters6400
namespace ProximityPrize.SubmissionLower
def bchksWeightedMultiplicity6400 : ℕ := 5150
def bchksWeightedEffectiveAgreement6400 : ℕ := 185371
def bchksWeightedXCap6400 : ℕ := 954660650
def bchksWeightedYCap6400 : ℕ := 7284
def bchksWeightedZCap6400 : ℕ := 29830000
def bchksWeightedNumerator6400 : ℕ := 274979000000000000
def bchksResidualNumerator6400 : ℕ := 274980700000000000
def bchksResidualDimension6400 : ℕ := 36050
def bchksWeightedVariableCount6400 : ℕ :=
  103714378617196277534
def bchksWeightedUniformConstraintCount6400 : ℕ :=
  103713901013899673600
def bchksWeightedPerturbationAllowance6400 : ℕ :=
  477603296603933
def bchksWeightedBalancedExtra6400 : ℕ := 50983
def bchksWeightedNextCost6400 : ℕ := 153641066175
def bchksWeightedCoordinateCost6400 (r : ℕ) : ℕ :=
  ∑ t ∈ Finset.range r,
    (r - t) * (bchksWeightedZCap6400 - t)
def BCHKSWeightedMultiplicityFeasible6400
    {ι ζ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq ζ]
    (S : Finset ζ) (A : ζ → Finset ι) (μ : ι → ℕ) : Prop :=
  (∀ i, μ i ≤ bchksWeightedZCap6400) ∧
  (∀ z ∈ S, bchksWeightedXCap6400 ≤ ∑ i ∈ A z, μ i) ∧
  (∑ i, bchksWeightedCoordinateCost6400 (μ i)) <
    bchksWeightedVariableCount6400
lemma bchksWeightedXCap_eq :
    bchksWeightedXCap6400 =
      bchksWeightedMultiplicity6400 *
        bchksWeightedEffectiveAgreement6400 := by
  norm_num [bchksWeightedXCap6400, bchksWeightedMultiplicity6400,
    bchksWeightedEffectiveAgreement6400]
lemma bchksWeightedRootBoost6400 :
    bchksWeightedXCap6400 -
        bchksWeightedMultiplicity6400 * 185364 = 36050 := by
  norm_num [bchksWeightedXCap6400, bchksWeightedMultiplicity6400]
lemma bchksWeightedBalancedExtra_eq6400 :
    (262144 * bchksWeightedXCap6400 + 185364 - 1) / 185364 -
        262144 * bchksWeightedMultiplicity6400 =
      bchksWeightedBalancedExtra6400 := by
  norm_num [bchksWeightedXCap6400, bchksWeightedMultiplicity6400,
    bchksWeightedBalancedExtra6400]
lemma bchksWeightedNextCost_eq6400 :
    (bchksWeightedMultiplicity6400 + 1) * bchksWeightedZCap6400 -
        bchksWeightedMultiplicity6400 *
          (bchksWeightedMultiplicity6400 + 1) / 2 =
      bchksWeightedNextCost6400 := by
  norm_num [bchksWeightedMultiplicity6400, bchksWeightedZCap6400,
    bchksWeightedNextCost6400]
lemma bchksWeightedBalancedCost_obstruction6400 :
    bchksWeightedVariableCount6400 <
      bchksWeightedUniformConstraintCount6400 +
        bchksWeightedBalancedExtra6400 * bchksWeightedNextCost6400 := by
  norm_num [bchksWeightedVariableCount6400,
    bchksWeightedUniformConstraintCount6400,
    bchksWeightedBalancedExtra6400, bchksWeightedNextCost6400]
lemma bchksWeightedDimensionAllowance6400 :
    bchksWeightedUniformConstraintCount6400 +
        bchksWeightedPerturbationAllowance6400 <
      bchksWeightedVariableCount6400 := by
  norm_num [bchksWeightedUniformConstraintCount6400,
    bchksWeightedPerturbationAllowance6400,
    bchksWeightedVariableCount6400]
lemma bchksWeightedUniformConstraintFormula6400 :
    262144 *
        (bchksWeightedMultiplicity6400 *
            (bchksWeightedMultiplicity6400 + 1) / 2 *
              bchksWeightedZCap6400 -
          bchksWeightedMultiplicity6400 *
            (bchksWeightedMultiplicity6400 - 1) *
            (bchksWeightedMultiplicity6400 + 1) / 6) =
      bchksWeightedUniformConstraintCount6400 := by
  norm_num [bchksWeightedMultiplicity6400, bchksWeightedZCap6400,
    bchksWeightedUniformConstraintCount6400]
lemma bchksWeightedSeedBudget6400 :
    bchksIncidenceCoefficient6400 *
          (bchksWeightedYCap6400 - 1) *
          (bchksWeightedZCap6400 - 1) +
        (bchksErrors6400 + 1) * (bchksWeightedYCap6400 - 1) +
        2 * bchksWeightedZCap6400 * (bchksWeightedYCap6400 - 1) +
        bchksWeightedZCap6400 <
      bchksWeightedNumerator6400 := by
  norm_num [bchksIncidenceCoefficient6400, bchksWeightedYCap6400,
    bchksWeightedZCap6400, bchksErrors6400,
    bchksWeightedNumerator6400]
lemma bchksWeightedFieldBudget6400 :
    2 ^ (128 : ℕ) *
        (bchksWeightedNumerator6400 + bchksListBound6400) ≤
      (2130706433 : ℕ) ^ 6 := by
  norm_num [bchksWeightedNumerator6400, bchksListBound6400]
lemma bchksResidualTwoFamilySeedBudget6400 :
    bchksIncidenceCoefficient6400 *
          (bchksWeightedYCap6400 - 1) *
          (bchksWeightedZCap6400 - 1) +
        (bchksErrors6400 + 1) * (bchksWeightedYCap6400 - 1) +
        2 * bchksWeightedZCap6400 * (bchksWeightedYCap6400 - 1) +
        bchksWeightedZCap6400 +
        2 * bchksResidualDimension6400 * bchksWeightedZCap6400 <
      bchksResidualNumerator6400 := by
  norm_num [bchksIncidenceCoefficient6400, bchksWeightedYCap6400,
    bchksWeightedZCap6400, bchksErrors6400,
    bchksResidualDimension6400, bchksResidualNumerator6400]
lemma bchksResidualFieldBudget6400 :
    2 ^ (128 : ℕ) *
        (bchksResidualNumerator6400 + bchksListBound6400) ≤
      (2130706433 : ℕ) ^ 6 := by
  norm_num [bchksResidualNumerator6400, bchksListBound6400]
end ProximityPrize.SubmissionLower
