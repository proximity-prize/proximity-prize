import ProximityPrize.SubmissionLower.LowerGeometry
import ProximityPrize.SubmissionLower.BoundaryTailCounting
namespace ProximityPrize.SubmissionLower.AsymmetricChainPolynomial80899
open scoped BigOperators
open RCN238 RCN223 RCN260 RCN313 RCN294 BoundaryTailChainHelper AsymmetricHelper
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

def stage (y z d j : ℕ) : UnequalParameters :=
  ⟨262144,131071,181245,y,d-j,z,y,d,z⟩

def kTerm (y z : ℕ) : ℕ :=
  131073 * (z + y + 524284*y*z) + 50174*80900*y
def mTerm (y z : ℕ) : ℕ := 131073*131071*y*z

theorem stageNumerator (y z d j : ℕ) (hj : j ≤ d) :
    leftRegularNumerator (stage y z d j) =
      (2*d-j)*kTerm y z + (2*(d-j)-1)*2*mTerm y z := by
  simp only [stage, leftRegularNumerator, UnequalParameters.gap,
    UnequalParameters.errors, UnequalParameters.leftAgreement,
    UnequalParameters.mixedCost, dot]
  norm_num only
  have hsub : (d-j)+d = 2*d-j := by omega
  dsimp [kTerm, mTerm]
  calc
    _ = ((d-j)+d) * (131073*(z+y+524284*y*z)+50174*80900*y) +
        (2*(d-j)-1)*2*(131073*131071*y*z) := by ring
    _ = _ := by rw [hsub]

def numerator (y z d : ℕ) : ℕ :=
  (d-1)*(3*d*kTerm y z + 4*mTerm y z*(d-1)) + 2*50174*9000000000000

def constant (y d : ℕ) : ℕ :=
  (d-1)*3*d*(131073+50174*80900)*y + 2*50174*9000000000000

private theorem le_roundUp_mul (a b : ℕ) (hb : 0 < b) : a ≤ (a/b+1)*b := by
  have hm := Nat.mod_lt a hb
  have he := Nat.mod_add_div a b
  nlinarith

end ProximityPrize.SubmissionLower.AsymmetricChainPolynomial80899
