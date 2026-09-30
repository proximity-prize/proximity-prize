import ProximityPrize.SubmissionLower.MovingSourceOwnerSplit6814
namespace ProximityPrize.SubmissionLower.MovingSourceNativeEnvelope6814
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open RCN095 SecondJetRelaxedFlag

def copies3 (m : ℕ) : ℕ := (m+2)/m
def parentFlag : FlagDegree := ⟨3504,45,12⟩
def coefficientZ3 : ℕ := 4*131072*(131074*3504)+3*65539*(131073*3504)
def coefficientU3 : ℕ := 4*131072*(131074*45-131072)+3*65539*(131073*45)
def coefficientA3 : ℕ := 4*131072*(131074*11)+3*65539*(131073*12-1)

theorem copies3_le (m e : ℕ) (hm : 0<m) (h : 3≤e*m) : copies3 m≤e := by
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hm).mpr
  nlinarith

theorem copies3_pos (m : ℕ) (hm : 0<m) : 0<copies3 m := by
  change 0<(m+2)/m
  exact Nat.div_pos (by omega) hm

end ProximityPrize.SubmissionLower.MovingSourceNativeEnvelope6814
