import ProximityPrize.SubmissionLower.BoundaryTailProfileCount6807

namespace ProximityPrize.SubmissionLower.BoundaryTailOwnArithmetic6807
open RCN095 RCN260 RCN294 BoundaryTailNumericGeometry6807 AsymmetricHelper
open DualCutBridge6807Arithmetic
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- Exact affine numerator used by the reproduced root-source ledger, before
its additional nonnegative full-surface charge. -/
def ownPolynomial (a b c : ℕ) : ℕ :=
    1141020853775911424709 +
    15868744059888682884*c +
    147354682362975364068*b +
    1181194994371722336*b*c +
    590664292517244672*b^2 +
    382056500133316288599*a +
    3497150096608950864*a*c +
    28677114253042298352*a*b +
    186481432634948640*a*b*c +
    93240716317474320*a*b^2 +
    14341006288671877656*a^2 +
    93240716317474320*a^2*c +
    93240716317474320*a^2*b +
    31080238772491440*a^3

def helperSlack (a b c : ℕ) : ℕ :=
    1140869656410388135317 +
    15862895756465035572*c +
    147320909959998284820*b +
    1180482510836964960*b*c +
    589951808982487296*b^2 +
    381969800961570579687*a +
    3494715777638702352*a*c +
    28664223157067732784*a*b +
    186303311751259296*a*b*c +
    93062595433784976*a*b^2 +
    14328827676232069464*a^2 +
    93062595433784976*a^2*c +
    92884474550095632*a^2*b +
    30902117888802096*a^3

def coefficientNumerator (a b c : ℕ) : ℕ :=
  leftRegularNumerator (parameters (a+3) (a+3+(b+2)) (a+3+(b+2)+c) 54 180 1800)

def helperNumerator (a b c : ℕ) : ℕ :=
  leftRegularNumerator (properParameters (a+3) (b+2) c 54 180 1800 24)

theorem own_polynomial_identity (a b c : ℕ) :
    ownPolynomial a b c =
      50253 * graphNumerator ⟨c,b+2,a+3⟩ 6 1620 133 52 a b c +
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
    x / 36 + y / 50253 ≤ (50253*x+36*y)/1809108 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 1809108)).mpr
  have hx := Nat.div_mul_le_self x 36
  have hy := Nat.div_mul_le_self y 50253
  nlinarith

theorem helper_cap_le (a b c : ℕ) :
    leftRegularCountCap (properParameters (a+3) (b+2) c 54 180 1800 24) ≤
      ownPolynomial a b c / 1809108 := by
  have hgap : (properParameters (a+3) (b+2) c 54 180 1800 24).gap = 50253 := by
    norm_num [properParameters, UnequalParameters.gap]
  rw [leftRegularCountCap,hgap]
  change helperNumerator a b c / 50253 ≤ _
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 1809108)).mpr
  have h := Nat.div_mul_le_self (helperNumerator a b c) 50253
  rw [helper_slack_identity]
  nlinarith

theorem retained_cap_le (a b c : ℕ) :
    graphNumerator ⟨c,b+2,a+3⟩ 6 1620 133 52 a b c / 36 +
      leftRegularCountCap (parameters (a+3) (a+3+(b+2)) (a+3+(b+2)+c) 54 180 1800) ≤
      ownPolynomial a b c / 1809108 := by
  have hgap : (parameters (a+3) (a+3+(b+2)) (a+3+(b+2)+c) 54 180 1800).gap = 50253 := by
    norm_num [parameters, UnequalParameters.gap]
  rw [own_polynomial_identity,leftRegularCountCap,hgap]
  exact rounded_sum_le _ _

end ProximityPrize.SubmissionLower.BoundaryTailOwnArithmetic6807
