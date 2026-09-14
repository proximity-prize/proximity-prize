import ProximityPrize.SubmissionLower.HigherRootProfileCount6810P2

namespace ProximityPrize.SubmissionLower.HigherRootOwnArithmetic6810P2
open RCN095 RCN260 RCN294 HigherRootNumericGeometry6810P2 AsymmetricHelper
open DualCutBridge6807Arithmetic
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- Exact affine numerator used by the reproduced root-source ledger, before
its additional nonnegative full-surface charge. -/
abbrev ownPolynomial := HigherRootArithmetic6810.P2.ownPolynomial
abbrev helperSlack := HigherRootArithmetic6810.P2.helperSlack

def coefficientNumerator (a b c : ℕ) : ℕ :=
  leftRegularNumerator (parameters (a+3) (a+3+(b+2)) (a+3+(b+2)+c) 56 185 2526)

def helperNumerator (a b c : ℕ) : ℕ :=
  leftRegularNumerator (properParameters (a+3) (b+2) c 56 185 2526 25)

theorem own_polynomial_identity (a b c : ℕ) :
    ownPolynomial a b c =
      50223 * graphNumerator ⟨c,b+2,a+3⟩ 7 2341 137 54 a b c +
        49 * coefficientNumerator a b c := by
  have hR : 2*(a+3)-1 = 2*a+5 := by omega
  norm_num only [coefficientNumerator, parameters, leftRegularNumerator,
    UnequalParameters.errors, UnequalParameters.gap, UnequalParameters.leftAgreement,
    UnequalParameters.mixedCost, dot, hR]
  simp only [ownPolynomial, HigherRootArithmetic6810.P2.ownPolynomial, graphNumerator, mixed, firstFlag, secondFlag]
  ring

theorem helper_slack_identity (a b c : ℕ) :
    ownPolynomial a b c = 49 * helperNumerator a b c + helperSlack a b c +
      49 * coefficientNumerator a b c := by
  have hR : 2*(a+3)-1 = 2*a+5 := by omega
  have hr : a+3-1 = a+2 := by omega
  have hy : a+3+(b+2)-1 = a+b+4 := by omega
  have ht : a+3+(b+2)+c-1 = a+b+c+4 := by omega
  norm_num only [helperNumerator, properParameters, coefficientNumerator, parameters, leftRegularNumerator,
    UnequalParameters.errors, UnequalParameters.gap, UnequalParameters.leftAgreement,
    UnequalParameters.mixedCost, dot, hR, hr, hy, ht]
  simp only [ownPolynomial, helperSlack, HigherRootArithmetic6810.P2.ownPolynomial, HigherRootArithmetic6810.P2.helperSlack]
  ring

theorem rounded_sum_le (x y : ℕ) :
    x / 49 + y / 50223 ≤ (50223*x+49*y)/2460927 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2460927)).mpr
  have hx := Nat.div_mul_le_self x 49
  have hy := Nat.div_mul_le_self y 50223
  nlinarith

theorem helper_cap_le (a b c : ℕ) :
    leftRegularCountCap (properParameters (a+3) (b+2) c 56 185 2526 25) ≤
      ownPolynomial a b c / 2460927 := by
  have hgap : (properParameters (a+3) (b+2) c 56 185 2526 25).gap = 50223 := by
    norm_num [properParameters, UnequalParameters.gap]
  rw [leftRegularCountCap,hgap]
  change helperNumerator a b c / 50223 ≤ _
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2460927)).mpr
  have h := Nat.div_mul_le_self (helperNumerator a b c) 50223
  rw [helper_slack_identity]
  nlinarith

theorem retained_cap_le (a b c : ℕ) :
    graphNumerator ⟨c,b+2,a+3⟩ 7 2341 137 54 a b c / 49 +
      leftRegularCountCap (parameters (a+3) (a+3+(b+2)) (a+3+(b+2)+c) 56 185 2526) ≤
      ownPolynomial a b c / 2460927 := by
  have hgap : (parameters (a+3) (a+3+(b+2)) (a+3+(b+2)+c) 56 185 2526).gap = 50223 := by
    norm_num [parameters, UnequalParameters.gap]
  rw [own_polynomial_identity,leftRegularCountCap,hgap]
  exact rounded_sum_le _ _

end ProximityPrize.SubmissionLower.HigherRootOwnArithmetic6810P2
