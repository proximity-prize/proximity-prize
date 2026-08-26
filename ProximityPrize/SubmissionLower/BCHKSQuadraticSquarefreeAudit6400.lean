import ProximityPrize.SubmissionLower.BCHKSQuadraticBranchCover6400
namespace ProximityPrize.SubmissionLower
open scoped BigOperators
def bchksQuadraticSquarefreeObstructionCap6400 : ℕ :=
  1873231207096848
def bchksQuadraticTwoCoordinateLedgers6400 : ℕ :=
  936624535896064
def bchksQuadraticSquarefreeTotalCap6400 : ℕ :=
  2809874904836140
theorem bchksQuadratic_resultant_degree_bound6400
    (r d e e' : ℕ)
    (hr : r ≤ 2 * 131071)
    (he : e ≤ 2 * d) (he' : e' ≤ 2 * d) :
    r * e' + (r - 1) * e ≤ (4 * 131071 - 1) * (2 * d) := by
  have hrpred : r - 1 ≤ 2 * 131071 - 1 := Nat.sub_le_sub_right hr 1
  calc
    r * e' + (r - 1) * e ≤
        r * (2 * d) + (r - 1) * (2 * d) :=
      Nat.add_le_add (Nat.mul_le_mul_left r he')
        (Nat.mul_le_mul_left (r - 1) he)
    _ ≤ (2 * 131071) * (2 * d) +
        (2 * 131071 - 1) * (2 * d) :=
      Nat.add_le_add (Nat.mul_le_mul_right (2 * d) hr)
        (Nat.mul_le_mul_right (2 * d) hrpred)
    _ = (4 * 131071 - 1) * (2 * d) := by ring
theorem bchksQuadratic_resultant_degree_sum_bound6400
    {γ : Type*} (T : Finset γ) (d obstruction : γ → ℕ)
    (hmass : (∑ q ∈ T, d q) ≤ bchksStableRootMass6400)
    (hobs : ∀ q ∈ T,
      obstruction q ≤ (4 * 131071 - 1) * (2 * d q)) :
    (∑ q ∈ T, obstruction q) ≤
      bchksQuadraticSquarefreeObstructionCap6400 := by
  calc
    (∑ q ∈ T, obstruction q) ≤
        ∑ q ∈ T, (4 * 131071 - 1) * (2 * d q) :=
      Finset.sum_le_sum hobs
    _ = ((4 * 131071 - 1) * 2) * (∑ q ∈ T, d q) := by
      simp_rw [mul_assoc, Finset.mul_sum]
    _ ≤ ((4 * 131071 - 1) * 2) * bchksStableRootMass6400 :=
      Nat.mul_le_mul_left _ hmass
    _ = bchksQuadraticSquarefreeObstructionCap6400 := by
      norm_num [bchksQuadraticSquarefreeObstructionCap6400,
        bchksStableRootMass6400]
lemma bchksQuadraticTwoCoordinateLedgers_eq6400 :
    bchksQuadraticTwoCoordinateLedgers6400 =
      2 * 262144 * bchksStableRootMass6400 := by
  norm_num [bchksQuadraticTwoCoordinateLedgers6400,
    bchksStableRootMass6400]
lemma bchksQuadraticSquarefreeTotalCap_eq6400 :
    bchksQuadraticSquarefreeTotalCap6400 =
      bchksQuadraticSquarefreeObstructionCap6400 +
        bchksQuadraticTwoCoordinateLedgers6400 +
        bchksStableQuadraticCoverCap6400 := by
  norm_num [bchksQuadraticSquarefreeTotalCap6400,
    bchksQuadraticSquarefreeObstructionCap6400,
    bchksQuadraticTwoCoordinateLedgers6400,
    bchksStableQuadraticCoverCap6400]
lemma bchksQuadraticSquarefreeTotalCap_lt_numerator6400 :
    bchksQuadraticSquarefreeTotalCap6400 < bchksNumerator6400 := by
  norm_num [bchksQuadraticSquarefreeTotalCap6400, bchksNumerator6400]
lemma bchksQuadraticSquarefreeFieldBudget6400 :
    2 ^ (128 : ℕ) *
        (bchksQuadraticSquarefreeTotalCap6400 + bchksListBound6400) ≤
      (2130706433 : ℕ) ^ 6 := by
  norm_num [bchksQuadraticSquarefreeTotalCap6400, bchksListBound6400]
end ProximityPrize.SubmissionLower
