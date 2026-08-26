import ProximityPrize.SubmissionLower.BCHKSParameters6401

/-!
# Exact source-theorem gate audit at score 64.01

This file records the arithmetic needed to compare the score-64.01 row with
the unconditional Reed--Solomon MCA bounds in the `rs-mca` theorem bank.
Here `sourceDimension6401 = 131072`, while `sourceDegree6401 = 131071` is
the largest permitted polynomial degree.  Keeping both constants explicit
avoids the degree-versus-dimension shift in the Johnson and MDS formulas.

The audit is deliberately only arithmetic.  In particular, it does not
promote the parameter-retained factor-lifting assumption in the source paper
to a theorem.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSRSMCASourceAudit6401

def sourceN6401 : Nat := 262144
def sourceDimension6401 : Nat := 131072
def sourceDegree6401 : Nat := 131071
def sourceAgreement6401 : Nat := 185354
def sourceErrors6401 : Nat := 76790
def sourceBaseFieldCard6401 : Nat := 2130706433
def sourceChallengeCard6401 : Nat := sourceBaseFieldCard6401 ^ 6

/-- The MCA allowance after charging the already-certified spherical list
bound once in the final reduction ledger. -/
def postListMCABudget6401 : Nat := 274980728094349243

def sourcePrefixWidth6401 : Nat :=
  sourceAgreement6401 - sourceDimension6401 - 1

/-- Exact field and post-list budget arithmetic. -/
theorem source_field_and_budget_exact6401 :
    sourceChallengeCard6401 =
      93571093019388561295270373781649880353786165192103559169 ∧
    sourceChallengeCard6401 / 2 ^ 128 = 274980728111395087 ∧
    sourceChallengeCard6401 / 2 ^ 128 - 17045844 =
      postListMCABudget6401 := by
  norm_num [sourceChallengeCard6401, sourceBaseFieldCard6401,
    postListMCABudget6401]

/-- The four clean unconditional gates all miss the target row.  The first
identity is the exact full-domain Johnson deficit (using the degree cap),
the second is the quadratic mean-overlap deficit (using code dimension),
the third is the half-distance overrun, and the fourth is the gap past the
published rate-half staircase endpoint. -/
theorem unconditional_source_gates_fail_exact6401 :
    sourceAgreement6401 ^ 2 + 3370908 =
        sourceN6401 * sourceDegree6401 ∧
    sourceAgreement6401 ^ 2 + 20133670812 =
        sourceN6401 * (sourceDimension6401 + sourceErrors6401) ∧
    2 * sourceErrors6401 =
        (sourceN6401 - sourceDimension6401) + 22508 ∧
    sourceErrors6401 = (sourceN6401 / 4 - 3) + 11257 := by
  norm_num [sourceAgreement6401, sourceN6401, sourceDegree6401,
    sourceDimension6401, sourceErrors6401]

/-- Agreement-set shortening first crosses the strict Johnson inequality at
exactly `t = 150`: `t = 149` still misses by `17365`, while `t = 150`
has surplus `5142`. -/
theorem shortening_Johnson_transition_exact6401 :
    (sourceAgreement6401 - 149) ^ 2 + 17365 =
        (sourceN6401 - 149) * (sourceDegree6401 - 149) ∧
    (sourceN6401 - 150) * (sourceDegree6401 - 150) + 5142 =
        (sourceAgreement6401 - 150) ^ 2 := by
  norm_num [sourceAgreement6401, sourceN6401, sourceDegree6401]

/-- A coarse rational lower bound already rules out the shortest shortening
certificate.  For every `0 <= i < 150`, the corresponding falling-factorial
ratio `(n-i)/(a-i)` is strictly larger than `7/5`; this theorem records that
even `(7/5)^150` is larger than the entire post-list MCA budget. -/
theorem shortening_coefficient_budget_barrier6401 :
    (postListMCABudget6401 + 1) * 5 ^ 150 < 7 ^ 150 := by
  norm_num [postListMCABudget6401]

/-- The pointwise `7/5` comparison used in the preceding certificate. -/
theorem first_150_shortening_factors_gt_seven_fifths6401
    (i : Nat) (hi : i < 150) :
    7 * (sourceAgreement6401 - i) <
      5 * (sourceN6401 - i) := by
  norm_num [sourceAgreement6401, sourceN6401] at hi ⊢
  omega

/-- The base-domain prefix width is macroscopic, not a shallow-prefix
quantity: even the crude lower bound `log2 |B| > 30` gives more than six
bits of prefix mass per coordinate. -/
theorem shallow_prefix_scale_no_go6401 :
    sourcePrefixWidth6401 = 54281 ∧
    6 * sourceN6401 < 30 * sourcePrefixWidth6401 ∧
    2 ^ 30 < sourceBaseFieldCard6401 := by
  norm_num [sourcePrefixWidth6401, sourceAgreement6401,
    sourceDimension6401, sourceN6401, sourceBaseFieldCard6401]

end BCHKSRSMCASourceAudit6401
end ProximityPrize.SubmissionLower
