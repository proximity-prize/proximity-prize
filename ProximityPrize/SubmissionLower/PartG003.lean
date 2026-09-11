import ProximityPrize.SubmissionLower.PartG002


section Compact_AsymmetricLinear
namespace ProximityPrize.SubmissionLower.AsymmetricHelper
open RCN260
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- A linear allowance for a carrier confined to a fixed degree box. -/
theorem leftRegularCountCap_le_linear (P : UnequalParameters)
    (ay ar az qT qM qR : ℕ) (hgap : 0 < P.gap)
    (hy : P.leftAgreement.y ≤ ay) (hr : P.leftAgreement.r ≤ ar)
    (hz : P.leftAgreement.z ≤ az)
    (hT : (P.n-P.w)*(ay*P.rightR+ar*P.rightY) ≤ P.gap*qT)
    (hM : (P.n-P.w)*(ar*P.rightZ+az*P.rightR) +
      (P.errors+1)*P.gap*P.rightR ≤ P.gap*qM)
    (hR : (P.n-P.w)*(ay*P.rightZ+az*P.rightY) +
      (P.errors+1)*P.gap*P.rightY ≤ P.gap*qR) :
    leftRegularCountCap P ≤ qT*P.leftZ+qM*P.leftY+qR*P.leftR := by
  have hd : RCN294.dot P.leftAgreement P.mixedCost ≤
      ay*P.mixedCost.y+ar*P.mixedCost.r+az*P.mixedCost.z := by
    unfold RCN294.dot
    exact Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul_right _ hy) (Nat.mul_le_mul_right _ hr))
      (Nat.mul_le_mul_right _ hz)
  have hn : leftRegularNumerator P ≤
      (P.n-P.w)*(ay*P.mixedCost.y+ar*P.mixedCost.r+az*P.mixedCost.z) +
        (P.errors+1)*P.gap*P.mixedCost.z :=
    Nat.add_le_add_right (Nat.mul_le_mul_left _ hd) _
  have he : (P.n-P.w)*(ay*P.mixedCost.y+ar*P.mixedCost.r+az*P.mixedCost.z) +
        (P.errors+1)*P.gap*P.mixedCost.z =
      ((P.n-P.w)*(ay*P.rightR+ar*P.rightY))*P.leftZ +
      ((P.n-P.w)*(ar*P.rightZ+az*P.rightR)+(P.errors+1)*P.gap*P.rightR)*P.leftY +
      ((P.n-P.w)*(ay*P.rightZ+az*P.rightY)+(P.errors+1)*P.gap*P.rightY)*P.leftR := by
    simp only [UnequalParameters.mixedCost]
    ring
  rw [he] at hn
  have hh := Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_right P.leftZ hT) (Nat.mul_le_mul_right P.leftY hM))
    (Nat.mul_le_mul_right P.leftR hR)
  have hb : leftRegularNumerator P ≤
      P.gap*(qT*P.leftZ+qM*P.leftY+qR*P.leftR) := by
    calc
      _ ≤ _ := hn.trans hh
      _ = _ := by ring
  have hdiv := Nat.div_le_div_right (c := P.gap) hb
  simpa only [leftRegularCountCap, Nat.mul_div_right _ hgap] using hdiv

end ProximityPrize.SubmissionLower.AsymmetricHelper

end Compact_AsymmetricLinear
