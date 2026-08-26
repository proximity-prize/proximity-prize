import ProximityPrize.SubmissionLower.BCHKSHigherDerivativeRoot6400
import ProximityPrize.SubmissionLower.BCHKSWeightedAudit6400
import ProximityPrize.SubmissionLower.BCHKSStableParameters6400

namespace ProximityPrize.SubmissionLower

open BCHKSSubstitutionVanish
open BCHKSDerivativeRoot6400
open BCHKSHigherDerivativeRoot6400

/-!
Two-ledger global-radical derivative point.

Factorwise accounting uses one product for pair collisions and two products
for self-discriminants.  A single discriminant of the global squarefree
radical detects both phenomena simultaneously:

`Disc(prod R_q) = (prod Disc(R_q)) * (prod_{q<r} Res(R_q,R_r)^2)`.

Accordingly one global `Res(rad Q,(rad Q)_Y)` has a conservative degree below
`2*DY*DZ`, not `3*DY*DZ`.  Conditional on the primitive-radical
specialization bridge, the exact point below supports derivatives through
order sixteen inside the near-maximal field numerator.  The recorded
order-seventeen candidate does not fit the same two-product ledger.
-/

def bchksSixteenthDerivativeMultiplicity6400 : ℕ := 1482080
def bchksSixteenthDerivativeXCap6400 : ℕ := 274723408431
def bchksSixteenthDerivativeYCap6400 : ℕ := 2095978
def bchksSixteenthDerivativeZCap6400 : ℕ := 62674761067
def bchksSixteenthDerivativeVariableCount6400 : ℕ :=
  18044413738407541364071099697
def bchksSixteenthDerivativeConstraintCount6400 : ℕ :=
  18044413738407541286046269440
def bchksSixteenthDerivativeSlack6400 : ℕ := 78024830257
def bchksSixteenthDerivativeProduct6400 : ℕ := 131364857674831482
def bchksSixteenthDerivativeBaseCover6400 : ℕ := 463545038061
def bchksSixteenthDerivativeTwoLedgerCover6400 : ℕ := 262730178894701025

lemma bchksSixteenthDerivative_exactMarginAndGap6400 :
    bchksSixteenthDerivativeXCap6400 + 868689 =
        bchksSixteenthDerivativeMultiplicity6400 * 185364 ∧
      868689 = 16 * (185364 - 131071) + 1 ∧
      bchksSixteenthDerivativeXCap6400 - 16 * 131071 + 1 =
        (bchksSixteenthDerivativeMultiplicity6400 - 16) * 185364 := by
  norm_num [bchksSixteenthDerivativeXCap6400,
    bchksSixteenthDerivativeMultiplicity6400]

lemma bchksSixteenthDerivativeVariableFormula6400 :
    6 * bchksSixteenthDerivativeVariableCount6400 =
      bchksSixteenthDerivativeYCap6400 *
        (6 * bchksSixteenthDerivativeXCap6400 *
            bchksSixteenthDerivativeZCap6400 -
          3 * (bchksSixteenthDerivativeXCap6400 +
            131071 * bchksSixteenthDerivativeZCap6400) *
              (bchksSixteenthDerivativeYCap6400 - 1) +
          131071 * (bchksSixteenthDerivativeYCap6400 - 1) *
            (2 * bchksSixteenthDerivativeYCap6400 - 1)) := by
  norm_num [bchksSixteenthDerivativeVariableCount6400,
    bchksSixteenthDerivativeYCap6400, bchksSixteenthDerivativeXCap6400,
    bchksSixteenthDerivativeZCap6400]

lemma bchksSixteenthDerivativeConstraintFormula6400 :
    6 * bchksSixteenthDerivativeConstraintCount6400 =
      262144 * bchksSixteenthDerivativeMultiplicity6400 *
        (6 * bchksSixteenthDerivativeMultiplicity6400 *
            bchksSixteenthDerivativeZCap6400 -
          3 * (bchksSixteenthDerivativeMultiplicity6400 +
            bchksSixteenthDerivativeZCap6400) *
              (bchksSixteenthDerivativeMultiplicity6400 - 1) +
          (bchksSixteenthDerivativeMultiplicity6400 - 1) *
            (2 * bchksSixteenthDerivativeMultiplicity6400 - 1)) := by
  norm_num [bchksSixteenthDerivativeConstraintCount6400,
    bchksSixteenthDerivativeMultiplicity6400,
    bchksSixteenthDerivativeZCap6400]

lemma bchksSixteenthDerivativeFeasible6400 :
    bchksSixteenthDerivativeConstraintCount6400 +
        bchksSixteenthDerivativeSlack6400 =
      bchksSixteenthDerivativeVariableCount6400 := by
  norm_num [bchksSixteenthDerivativeConstraintCount6400,
    bchksSixteenthDerivativeSlack6400,
    bchksSixteenthDerivativeVariableCount6400]

lemma bchksSixteenthDerivativeLedger6400 :
    bchksSixteenthDerivativeProduct6400 =
        (bchksSixteenthDerivativeYCap6400 - 1) *
          (bchksSixteenthDerivativeZCap6400 - 1) ∧
      bchksSixteenthDerivativeTwoLedgerCover6400 =
        2 * bchksSixteenthDerivativeProduct6400 +
          bchksSixteenthDerivativeBaseCover6400 := by
  norm_num [bchksSixteenthDerivativeProduct6400,
    bchksSixteenthDerivativeYCap6400, bchksSixteenthDerivativeZCap6400,
    bchksSixteenthDerivativeTwoLedgerCover6400,
    bchksSixteenthDerivativeBaseCover6400]

lemma bchksSixteenthDerivativeBudget6400 :
    bchksSixteenthDerivativeTwoLedgerCover6400 <
        bchksWeightedNumerator6400 ∧
      2 ^ (128 : ℕ) *
          (bchksSixteenthDerivativeTwoLedgerCover6400 + bchksListBound6400) ≤
        (2130706433 : ℕ) ^ 6 := by
  norm_num [bchksSixteenthDerivativeTwoLedgerCover6400,
    bchksWeightedNumerator6400, bchksListBound6400]

/-- The order-sixteen derivative substitution vanishes at every challenge
for this exact point. -/
theorem triEval_sixteenthDerivative_eq_zero6400
    {F ι : Type*} [Field F] [DecidableEq F] [DecidableEq ι]
    (Q : Polynomial (Polynomial (Polynomial F))) (z : F)
    (P : Polynomial F) (omega : ι ↪ F) (A : Finset ι)
    (yZ : ι → Polynomial F)
    (hvan : ∀ i ∈ A, ∀ s t h,
      s + t < bchksSixteenthDerivativeMultiplicity6400 →
      shiftedScalarCoeff Q (omega i) (yZ i) t s h = 0)
    (hmatch : ∀ i ∈ A,
      Polynomial.eval (omega i) P = Polynomial.eval z (yZ i))
    (hP : P.natDegree ≤ 131071)
    (hcap : ∀ y x, ((Q.coeff y).coeff x) ≠ 0 →
      x + 131071 * y < bchksSixteenthDerivativeXCap6400)
    (hA : 185364 ≤ A.card) :
    triEval (iterYDerivative 16 Q) z P = 0 := by
  apply triEval_iterYDerivative_eq_zero Q 16
    bchksSixteenthDerivativeMultiplicity6400 131071
    bchksSixteenthDerivativeXCap6400 z P omega A yZ
  · norm_num [bchksSixteenthDerivativeMultiplicity6400]
  · norm_num [bchksSixteenthDerivativeXCap6400]
  · exact hvan
  · exact hmatch
  · exact hP
  · exact hcap
  · have hgap : bchksSixteenthDerivativeXCap6400 - 16 * 131071 <
        (bchksSixteenthDerivativeMultiplicity6400 - 16) * 185364 := by
      have h := bchksSixteenthDerivative_exactMarginAndGap6400.2.2
      rw [← h]
      omega
    exact hgap.trans_le (Nat.mul_le_mul_left
      (bchksSixteenthDerivativeMultiplicity6400 - 16) hA)

/-- Best recorded order-seventeen point exceeds the two-product budget. -/
lemma bchksSeventeenthScannedCandidate_noGo6400 :
    bchksWeightedNumerator6400 < 295541294833601101 := by
  norm_num [bchksWeightedNumerator6400]

end ProximityPrize.SubmissionLower
