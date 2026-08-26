import ProximityPrize.SubmissionLower.BCHKSParameters6401

/-!
# Two-Frobenius polynomial-module audit at score 64.01

For the two-conjugate interpolation equation

`A₀(X,Z) + A₁(X,Z) P(X) + A₂(X,Z) P⁽ᵠ⁾(X) = 0`,

the three `X` boxes have respectively `174763`, `43692`, and `43692`
coefficients.  The received affine line has ordinary `Z`-degrees `0`, `1`,
and `q` in these three blocks.  Balancing all output coefficients below a
common `Z` depth `L` therefore gives depths `L`, `L-1`, and `L-q`.

The first strictly underdetermined rectangle has exactly three surplus
coefficients.  Its determinant and conditional rank-two incidence caps are
tiny compared with the score-64.01 challenge numerator.  The honest
remaining branch is rank one over `F(X,Z)`: the three scalar kernel vectors
may merely be `A, Z*A, Z^2*A`, leaving one affine `q`-polynomial equation.
No pruning theorem for that periodic branch is asserted here.
-/

namespace ProximityPrize.SubmissionLower
namespace BCHKSTwoFrobeniusModuleAudit6401

def q6401 : Nat := 2130706433
def n6401 : Nat := 262144
def a6401 : Nat := 185354
def ownerDegreeCap6401 : Nat := 131071

def a0XSlots6401 : Nat := 174763
def a1XSlots6401 : Nat := 43692
def a2XSlots6401 : Nat := 43692

/-- The constant term in the eventual Hilbert function `3*L-C`. -/
def moduleIndexSum6401 : Nat := a1XSlots6401 * (q6401 + 1)

/-- At `L0` the balanced variable and equation counts are equal. -/
def balancedThreshold6401 : Nat := moduleIndexSum6401 / 3

/-- The first strictly underdetermined balanced depth. -/
def balancedDepth6401 : Nat := balancedThreshold6401 + 1

def balancedVariables6401 (L : Nat) : Nat :=
  a0XSlots6401 * L + a1XSlots6401 * (L - 1) +
    a2XSlots6401 * (L - q6401)

def balancedConstraints6401 (L : Nat) : Nat := n6401 * L

/-- `Z`-degree cap for a nonzero determinant of three small solutions. -/
def rankThreeDetZCap6401 : Nat := 3 * balancedDepth6401 - q6401 - 4

/-- `Z`-degree cap of the `A₁,A₂` minor used as a denominator in the
rank-two branch. -/
def rankTwoDenomZCap6401 : Nat :=
  2 * balancedDepth6401 - q6401 - 3

/-- After subtracting an affine received coordinate, the numerator has one
more possible `Z` degree than the denominator. -/
def rankTwoMismatchZCap6401 : Nat :=
  2 * balancedDepth6401 - q6401 - 2

def nonidentityAgreementFloor6401 : Nat :=
  a6401 - ownerDegreeCap6401

def ceilDiv (u v : Nat) : Nat := (u + v - 1) / v

/-- This is the conditional incidence cap when at most `131071` coordinate
lines are identities of the selected rational branch.  The denominator-bad
specializations are paid once. -/
def rankTwoConditionalOwnerCap6401 : Nat :=
  rankTwoDenomZCap6401 +
    ceilDiv (n6401 * rankTwoMismatchZCap6401)
      nonidentityAgreementFloor6401

def conservativeChallengeNumerator6401 : Nat := 274980700000000000

theorem twoFrobenius_balanced_rectangle_exact6401 :
    moduleIndexSum6401 = 93094825514328 ∧
      balancedThreshold6401 = 31031608504776 ∧
      balancedDepth6401 = 31031608504777 ∧
      balancedVariables6401 balancedThreshold6401 =
        balancedConstraints6401 balancedThreshold6401 ∧
      balancedVariables6401 balancedDepth6401 =
        8134749979876261891 ∧
      balancedConstraints6401 balancedDepth6401 =
        8134749979876261888 ∧
      balancedVariables6401 balancedDepth6401 -
          balancedConstraints6401 balancedDepth6401 = 3 := by
  norm_num [moduleIndexSum6401, balancedThreshold6401,
    balancedDepth6401, balancedVariables6401, balancedConstraints6401,
    a0XSlots6401, a1XSlots6401, a2XSlots6401, q6401, n6401]

/-- The substituted owner polynomial has degree at most `174762`, so the
`185354` agreements exceed that degree by `10592`. -/
theorem twoFrobenius_owner_root_margin_exact6401 :
    a0XSlots6401 - 1 = 174762 ∧
      a1XSlots6401 - 1 + ownerDegreeCap6401 = 174762 ∧
      a2XSlots6401 - 1 + ownerDegreeCap6401 = 174762 ∧
      a6401 - 174762 = 10592 := by
  norm_num [a0XSlots6401, a1XSlots6401, a2XSlots6401,
    ownerDegreeCap6401, a6401]

/-- A `3×3` determinant uses one entry from each block.  Its `X` degree
is at most `174762 + 43691 + 43691 = 262144`; its much more important
ordinary `Z` degree is only about `9.31e13`. -/
theorem rankThree_determinant_caps_exact6401 :
    (a0XSlots6401 - 1) + (a1XSlots6401 - 1) +
        (a2XSlots6401 - 1) = 262144 ∧
      rankThreeDetZCap6401 = 93092694807894 ∧
      rankThreeDetZCap6401 < conservativeChallengeNumerator6401 ∧
      conservativeChallengeNumerator6401 - rankThreeDetZCap6401 =
        274887607305192106 := by
  norm_num [a0XSlots6401, a1XSlots6401, a2XSlots6401,
    rankThreeDetZCap6401, balancedDepth6401,
    balancedThreshold6401, moduleIndexSum6401, q6401,
    conservativeChallengeNumerator6401]

/-- Exact conditional rank-two ledger.  If the rational branch has at most
`131071` coordinate identities, every good owner supplies at least `54283`
nonidentity agreement incidences.  Each fixed coordinate contributes at
most `rankTwoMismatchZCap6401` roots.  This statement records the numerical
ledger only; constructing the rational branch and splitting off the larger
identity branch are separate algebraic steps. -/
theorem rankTwo_conditional_ledger_exact6401 :
    nonidentityAgreementFloor6401 = 54283 ∧
      rankTwoDenomZCap6401 = 62061086303118 ∧
      rankTwoMismatchZCap6401 = 62061086303119 ∧
      ceilDiv (n6401 * rankTwoMismatchZCap6401)
          nonidentityAgreementFloor6401 = 299706011234546 ∧
      rankTwoConditionalOwnerCap6401 = 361767097537664 ∧
      rankTwoConditionalOwnerCap6401 <
          conservativeChallengeNumerator6401 ∧
      conservativeChallengeNumerator6401 -
          rankTwoConditionalOwnerCap6401 = 274618932902462336 := by
  norm_num [nonidentityAgreementFloor6401, rankTwoDenomZCap6401,
    rankTwoMismatchZCap6401, rankTwoConditionalOwnerCap6401, ceilDiv,
    n6401, a6401, ownerDegreeCap6401, balancedDepth6401,
    balancedThreshold6401, moduleIndexSum6401, a1XSlots6401, q6401,
    conservativeChallengeNumerator6401]

/-!
For a free rank-three kernel module with balanced Forney indices
`μ₁ ≤ μ₂ ≤ μ₃` and sum `moduleIndexSum6401 = 3*L0`, the
three extremal profiles below all produce exactly three vectors at depth
`L0+1`:

* `(L0,L0,L0)` gives three genuine module directions;
* `(L0-1,L0,L0+1)` gives two directions;
* `(L0-2,L0+1,L0+1)` gives only `A,Z*A,Z²*A`.

Thus coefficient surplus three alone cannot rule out rank one.
-/

def forneyRankThreeProfile6401 : Nat × Nat × Nat :=
  (balancedThreshold6401, balancedThreshold6401,
    balancedThreshold6401)

def forneyRankTwoProfile6401 : Nat × Nat × Nat :=
  (balancedThreshold6401 - 1, balancedThreshold6401,
    balancedThreshold6401 + 1)

def forneyRankOneProfile6401 : Nat × Nat × Nat :=
  (balancedThreshold6401 - 2, balancedThreshold6401 + 1,
    balancedThreshold6401 + 1)

def truncatedContribution6401 (mu : Nat) : Nat :=
  balancedDepth6401 - mu

theorem forney_extremal_profiles_exact6401 :
    let L0 := balancedThreshold6401
    forneyRankThreeProfile6401 = (L0, L0, L0) ∧
      forneyRankTwoProfile6401 = (L0 - 1, L0, L0 + 1) ∧
      forneyRankOneProfile6401 = (L0 - 2, L0 + 1, L0 + 1) ∧
      L0 + L0 + L0 = moduleIndexSum6401 ∧
      (L0 - 1) + L0 + (L0 + 1) = moduleIndexSum6401 ∧
      (L0 - 2) + (L0 + 1) + (L0 + 1) = moduleIndexSum6401 ∧
      truncatedContribution6401 L0 = 1 ∧
      truncatedContribution6401 (L0 - 1) = 2 ∧
      truncatedContribution6401 (L0 - 2) = 3 ∧
      truncatedContribution6401 (L0 + 1) = 0 := by
  norm_num [forneyRankThreeProfile6401, forneyRankTwoProfile6401,
    forneyRankOneProfile6401, truncatedContribution6401,
    balancedDepth6401, balancedThreshold6401, moduleIndexSum6401,
    a1XSlots6401, q6401]

end BCHKSTwoFrobeniusModuleAudit6401
end ProximityPrize.SubmissionLower
