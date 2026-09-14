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
    31074054019586640*a^3 +
    93222162058759920*a^2*b +
    93222162058759920*a^2*c +
    14338153528762278696*a^2 +
    93222162058759920*a*b^2 +
    186444324117519840*a*b*c +
    28671408733223100432*a*b +
    3496454303083442544*a*c +
    381980481352162115369*a +
    590546780985225792*b^2 +
    1180959971307684576*b*c +
    147325362746006092908*b +
    15865586665996727244*c +
    1140793812586650154779

def helperSlack (a b c : ℕ) : ℕ :=
    30895933135897296*a^3 +
    92865920291381232*a^2*b +
    93044041175070576*a^2*c +
    14325974916850858344*a^2 +
    93044041175070576*a*b^2 +
    186266203233830496*a*b*c +
    28658517637776922704*a*b +
    3494019984113194032*a*c +
    381893782189266902777*a +
    589834297450468416*b^2 +
    1180247487772927200*b*c +
    147291590345538855900*b +
    15859738362573079932*c +
    1140642615244772221227

def coefficientNumerator (a b c : ℕ) : ℕ :=
  leftRegularNumerator (parameters (a+3) (a+3+(b+2)) (a+3+(b+2)+c) 54 180 1800)

def helperNumerator (a b c : ℕ) : ℕ :=
  leftRegularNumerator (properParameters (a+3) (b+2) c 54 180 1800 24)

theorem own_polynomial_identity (a b c : ℕ) :
    ownPolynomial a b c =
      50243 * graphNumerator ⟨c,b+2,a+3⟩ 6 1620 133 52 a b c +
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
    x / 36 + y / 50243 ≤ (50243*x+36*y)/1808748 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 1808748)).mpr
  have hx := Nat.div_mul_le_self x 36
  have hy := Nat.div_mul_le_self y 50243
  nlinarith

theorem helper_cap_le (a b c : ℕ) :
    leftRegularCountCap (properParameters (a+3) (b+2) c 54 180 1800 24) ≤
      ownPolynomial a b c / 1808748 := by
  have hgap : (properParameters (a+3) (b+2) c 54 180 1800 24).gap = 50243 := by
    norm_num [properParameters, UnequalParameters.gap]
  rw [leftRegularCountCap,hgap]
  change helperNumerator a b c / 50243 ≤ _
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 1808748)).mpr
  have h := Nat.div_mul_le_self (helperNumerator a b c) 50243
  rw [helper_slack_identity]
  nlinarith

theorem retained_cap_le (a b c : ℕ) :
    graphNumerator ⟨c,b+2,a+3⟩ 6 1620 133 52 a b c / 36 +
      leftRegularCountCap (parameters (a+3) (a+3+(b+2)) (a+3+(b+2)+c) 54 180 1800) ≤
      ownPolynomial a b c / 1808748 := by
  have hgap : (parameters (a+3) (a+3+(b+2)) (a+3+(b+2)+c) 54 180 1800).gap = 50243 := by
    norm_num [parameters, UnequalParameters.gap]
  rw [own_polynomial_identity,leftRegularCountCap,hgap]
  exact rounded_sum_le _ _

end ProximityPrize.SubmissionLower.BoundaryTailOwnArithmetic6808
