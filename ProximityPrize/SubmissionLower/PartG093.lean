import ProximityPrize.SubmissionLower.PartG092


section Compact_SecondJetAffineCeiling
/-! Affine upper bounds for the rounded moving cost. They allow checking a
piecewise affine base certificate with no residue-class enumeration. -/
namespace ProximityPrize.SubmissionLower.SecondJetAffineCeiling
open RCN095
set_option autoImplicit false
set_option maxHeartbeats 2000000

def moving (r v z : ℕ) (q : FlagDegree) : ℕ :=
  flagMixed ⟨z,v,r⟩ ⟨262144*z,1+262144*v,262144*(r-1)⟩ q

def movingSlope (r v : ℕ) (q : FlagDegree) : ℕ :=
  q.all*(1+262144*v+262144*(r-1))+q.yz*(262144*(r-1))+
    262144*(v*q.all+r*q.all+r*q.yz)

theorem moving_add (r v z h : ℕ) (q : FlagDegree) :
    moving r v (z+h) q = moving r v z q+h*movingSlope r v q := by
  simp only [moving,movingSlope,flagMixed]
  ring

theorem ceil_add_mul_le (M step h k : ℕ) :
    (M+h*step+k)/(k+1) ≤ (M+k)/(k+1)+h*((step+k)/(k+1)) := by
  have hM := SecondJetRounding.le_scaled_ceiling M k
  have hs := Nat.mul_le_mul_left h (SecondJetRounding.le_scaled_ceiling step k)
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < k+1)).mpr
  nlinarith

theorem moving_ceil_add_le (r v z h k : ℕ) (q : FlagDegree) :
    (moving r v (z+h) q+k)/(k+1) ≤
      (moving r v z q+k)/(k+1)+h*((movingSlope r v q+k)/(k+1)) := by
  rw [moving_add]
  exact ceil_add_mul_le _ _ _ _

end ProximityPrize.SubmissionLower.SecondJetAffineCeiling

end Compact_SecondJetAffineCeiling
