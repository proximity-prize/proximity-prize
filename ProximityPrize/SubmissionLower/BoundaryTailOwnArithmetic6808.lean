import ProximityPrize.SubmissionLower.BoundaryTailProfileCount6808

namespace ProximityPrize.SubmissionLower.BoundaryTailOwnArithmetic6808
open RCN095 RCN260 RCN294 BoundaryTailNumericGeometry6808 AsymmetricHelper
open DualCutBridge6807Arithmetic
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- Exact affine numerator used by the reproduced root-source ledger, before
its additional nonnegative full-surface charge. -/
def ownPolynomial (a b c : ℕ) : ℕ :=
    31067869266681840*a^3 +
    93203607800045520*a^2*b +
    93203607800045520*a^2*c +
    14335300768852679736*a^2 +
    93203607800045520*a*b^2 +
    186407215600091040*a*b*c +
    28665703213403902512*a*b +
    3495758509557934224*a*c +
    381904462571006257339*a +
    590429269453206912*b^2 +
    1180724948243646816*b*c +
    147296043129036432948*b +
    15862429272104771604*c +
    1140566771397383052849

def helperSlack (a b c : ℕ) : ℕ :=
    30889748382992496*a^3 +
    92847366032666832*a^2*b +
    93025486916356176*a^2*c +
    14323122157469992824*a^2 +
    93025486916356176*a*b^2 +
    186229094716401696*a*b*c +
    28652812118486458224*a*b +
    3493324190587685712*a*c +
    381817763416967329867*a +
    589716785918449536*b^2 +
    1180012464708889440*b*c +
    147262270731080679780*b +
    15856580968681124292*c +
    1140415574079165940737

def coefficientNumerator (a b c : ℕ) : ℕ :=
  leftRegularNumerator (parameters (a+3) (a+3+(b+2)) (a+3+(b+2)+c) 54 180 1800)

def helperNumerator (a b c : ℕ) : ℕ :=
  leftRegularNumerator (properParameters (a+3) (b+2) c 54 180 1800 24)

theorem own_polynomial_identity (a b c : ℕ) :
    ownPolynomial a b c =
      50233 * graphNumerator ⟨c,b+2,a+3⟩ 6 1620 133 52 a b c +
        36 * coefficientNumerator a b c := by
  have hR : 2*(a+3)-1 = 2*a+5 := by omega
  norm_num only [coefficientNumerator, parameters, leftRegularNumerator,
    UnequalParameters.errors, UnequalParameters.gap, UnequalParameters.leftAgreement,
    UnequalParameters.mixedCost, dot, hR]
  simp only [ownPolynomial, graphNumerator, mixed, firstFlag, secondFlag]
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
  simp only [ownPolynomial, helperSlack]
  ring

theorem rounded_sum_le (x y : ℕ) :
    x / 36 + y / 50233 ≤ (50233*x+36*y)/1808388 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 1808388)).mpr
  have hx := Nat.div_mul_le_self x 36
  have hy := Nat.div_mul_le_self y 50233
  nlinarith

theorem helper_cap_le (a b c : ℕ) :
    leftRegularCountCap (properParameters (a+3) (b+2) c 54 180 1800 24) ≤
      ownPolynomial a b c / 1808388 := by
  have hgap : (properParameters (a+3) (b+2) c 54 180 1800 24).gap = 50233 := by
    norm_num [properParameters, UnequalParameters.gap]
  rw [leftRegularCountCap,hgap]
  change helperNumerator a b c / 50233 ≤ _
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 1808388)).mpr
  have h := Nat.div_mul_le_self (helperNumerator a b c) 50233
  rw [helper_slack_identity]
  nlinarith

theorem retained_cap_le (a b c : ℕ) :
    graphNumerator ⟨c,b+2,a+3⟩ 6 1620 133 52 a b c / 36 +
      leftRegularCountCap (parameters (a+3) (a+3+(b+2)) (a+3+(b+2)+c) 54 180 1800) ≤
      ownPolynomial a b c / 1808388 := by
  have hgap : (parameters (a+3) (a+3+(b+2)) (a+3+(b+2)+c) 54 180 1800).gap = 50233 := by
    norm_num [parameters, UnequalParameters.gap]
  rw [own_polynomial_identity,leftRegularCountCap,hgap]
  exact rounded_sum_le _ _

end ProximityPrize.SubmissionLower.BoundaryTailOwnArithmetic6808
