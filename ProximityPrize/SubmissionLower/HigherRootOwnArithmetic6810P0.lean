import ProximityPrize.SubmissionLower.HigherRootProfileCount6810P0

namespace ProximityPrize.SubmissionLower.HigherRootOwnArithmetic6810P0
open RCN095 RCN260 RCN294 HigherRootNumericGeometry6810P0 AsymmetricHelper
open DualCutBridge6807Arithmetic
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- Exact affine numerator used by the reproduced root-source ledger, before
its additional nonnegative full-surface charge. -/
abbrev ownPolynomial := HigherRootArithmetic6810.P0.ownPolynomial
abbrev helperSlack := HigherRootArithmetic6810.P0.helperSlack

def coefficientNumerator (a b c : ℕ) : ℕ :=
  leftRegularNumerator (parameters (a+3) (a+3+(b+2)) (a+3+(b+2)+c) 54 180 1800)

def helperNumerator (a b c : ℕ) : ℕ :=
  leftRegularNumerator (properParameters (a+3) (b+2) c 54 180 1800 24)

theorem own_polynomial_identity (a b c : ℕ) :
    ownPolynomial a b c =
      50223 * graphNumerator ⟨c,b+2,a+3⟩ 6 1620 133 52 a b c +
        36 * coefficientNumerator a b c := by
  have hR : 2*(a+3)-1 = 2*a+5 := by omega
  norm_num only [coefficientNumerator, parameters, leftRegularNumerator,
    UnequalParameters.errors, UnequalParameters.gap, UnequalParameters.leftAgreement,
    UnequalParameters.mixedCost, dot, hR]
  simp only [ownPolynomial, HigherRootArithmetic6810.P0.ownPolynomial, graphNumerator, mixed, firstFlag, secondFlag]
  ring

theorem helper_slack_identity (a b c : ℕ) :
    ownPolynomial a b c = 36 * helperNumerator a b c + helperSlack a b c +
      36 * coefficientNumerator a b c := by
  have hR : 2*(a+3)-1 = 2*a+5 := by omega
  have hr : a+3-1 = a+2 := by omega
  have hy : a+3+(b+2)-1 = a+b+4 := by omega
  have ht : a+3+(b+2)+c-1 = a+b+c+4 := by omega
  norm_num only [helperNumerator, properParameters, coefficientNumerator, parameters, leftRegularNumerator,
    UnequalParameters.errors, UnequalParameters.gap, UnequalParameters.leftAgreement,
    UnequalParameters.mixedCost, dot, hR, hr, hy, ht]
  simp only [ownPolynomial, helperSlack, HigherRootArithmetic6810.P0.ownPolynomial, HigherRootArithmetic6810.P0.helperSlack]
  ring

theorem rounded_sum_le (x y : ℕ) :
    x / 36 + y / 50223 ≤ (50223*x+36*y)/1808028 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 1808028)).mpr
  have hx := Nat.div_mul_le_self x 36
  have hy := Nat.div_mul_le_self y 50223
  nlinarith

theorem helper_cap_le (a b c : ℕ) :
    leftRegularCountCap (properParameters (a+3) (b+2) c 54 180 1800 24) ≤
      ownPolynomial a b c / 1808028 := by
  have hgap : (properParameters (a+3) (b+2) c 54 180 1800 24).gap = 50223 := by
    norm_num [properParameters, UnequalParameters.gap]
  rw [leftRegularCountCap,hgap]
  change helperNumerator a b c / 50223 ≤ _
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 1808028)).mpr
  have h := Nat.div_mul_le_self (helperNumerator a b c) 50223
  rw [helper_slack_identity]
  nlinarith

theorem retained_cap_le (a b c : ℕ) :
    graphNumerator ⟨c,b+2,a+3⟩ 6 1620 133 52 a b c / 36 +
      leftRegularCountCap (parameters (a+3) (a+3+(b+2)) (a+3+(b+2)+c) 54 180 1800) ≤
      ownPolynomial a b c / 1808028 := by
  have hgap : (parameters (a+3) (a+3+(b+2)) (a+3+(b+2)+c) 54 180 1800).gap = 50223 := by
    norm_num [parameters, UnequalParameters.gap]
  rw [own_polynomial_identity,leftRegularCountCap,hgap]
  exact rounded_sum_le _ _

end ProximityPrize.SubmissionLower.HigherRootOwnArithmetic6810P0
