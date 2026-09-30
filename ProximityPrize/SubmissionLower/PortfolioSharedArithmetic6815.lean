import ProximityPrize.SubmissionLower.PortfolioCost6815
import ProximityPrize.SubmissionLower.RetainedSharedRemainder6815
namespace ProximityPrize.SubmissionLower.PortfolioSharedArithmetic6815
set_option autoImplicit false
set_option maxHeartbeats 1200000
open RCN095

def middle (p : FlagDegree) := p.yz+p.all
def total (p : FlagDegree) := p.zOnly+p.yz+p.all
def weighted (u v : ℕ) (p q : FlagDegree) :=
  u*flagMixed p q unitYZFlag+v*flagMixed p q unitAllFlag

theorem mixed_u (p q : FlagDegree) :
    flagMixed p q unitYZFlag+p.all*q.all=p.all*total q+q.all*total p := by
  simp only [flagMixed,unitYZFlag,total]
  ring
theorem mixed_v (p q : FlagDegree) :
    flagMixed p q unitAllFlag+middle p*middle q=middle p*total q+middle q*total p := by
  simp only [flagMixed,unitAllFlag,total,middle]
  ring

theorem triple_u (p q s : FlagDegree) (capB capT : ℕ)
    (hb : p.all+q.all+s.all≤capB) (ht : total p+total q+total s≤capT) :
    flagMixed p q unitYZFlag+flagMixed p s unitYZFlag+flagMixed q s unitYZFlag≤capB*capT := by
  have h := Nat.mul_le_mul hb ht
  have h1 := mixed_u p q
  have h2 := mixed_u p s
  have h3 := mixed_u q s
  nlinarith only [h,h1,h2,h3,Nat.zero_le (p.all*total p),Nat.zero_le (q.all*total q),
    Nat.zero_le (s.all*total s),Nat.zero_le (p.all*q.all),Nat.zero_le (p.all*s.all),Nat.zero_le (q.all*s.all)]

theorem triple_v (p q s : FlagDegree) (capM capT : ℕ)
    (hb : middle p+middle q+middle s≤capM) (ht : total p+total q+total s≤capT) :
    flagMixed p q unitAllFlag+flagMixed p s unitAllFlag+flagMixed q s unitAllFlag≤capM*capT := by
  have h := Nat.mul_le_mul hb ht
  have h1 := mixed_v p q
  have h2 := mixed_v p s
  have h3 := mixed_v q s
  nlinarith only [h,h1,h2,h3,Nat.zero_le (middle p*total p),Nat.zero_le (middle q*total q),
    Nat.zero_le (middle s*total s),Nat.zero_le (middle p*middle q),Nat.zero_le (middle p*middle s),
    Nat.zero_le (middle q*middle s)]

theorem triple_pair (p q s : FlagDegree) (u v capB capM capT : ℕ)
    (hb : p.all+q.all+s.all≤capB) (hm : middle p+middle q+middle s≤capM)
    (ht : total p+total q+total s≤capT) :
    weighted u v p q≤capT*(u*capB+v*capM)/3 ∨
    weighted u v p s≤capT*(u*capB+v*capM)/3 ∨
    weighted u v q s≤capT*(u*capB+v*capM)/3 := by
  have hu := Nat.mul_le_mul_left u (triple_u p q s capB capT hb ht)
  have hv := Nat.mul_le_mul_left v (triple_v p q s capM capT hm ht)
  have hsum : weighted u v p q+weighted u v p s+weighted u v q s≤capT*(u*capB+v*capM) := by
    dsimp only [weighted]
    nlinarith only [hu,hv]
  omega

theorem repeated_pair (p q : FlagDegree) (u v capB capM capT : ℕ)
    (hb : 2*p.all+q.all≤capB) (hm : 2*middle p+middle q≤capM)
    (ht : 2*total p+total q≤capT) :
    2*weighted u v p q≤capT*(u*capB+v*capM) := by
  have hbu := Nat.mul_le_mul hb ht
  have hmv := Nat.mul_le_mul hm ht
  have hu := mixed_u p q
  have hv := mixed_v p q
  have hu' : 2*flagMixed p q unitYZFlag≤capB*capT := by
    nlinarith only [hbu,hu,Nat.zero_le (p.all*total p),Nat.zero_le (q.all*total q),Nat.zero_le (p.all*q.all)]
  have hv' : 2*flagMixed p q unitAllFlag≤capM*capT := by
    nlinarith only [hmv,hv,Nat.zero_le (middle p*total p),Nat.zero_le (middle q*total q),Nat.zero_le (middle p*middle q)]
  have h1 := Nat.mul_le_mul_left u hu'
  have h2 := Nat.mul_le_mul_left v hv'
  dsimp only [weighted]
  nlinarith only [h1,h2]

end ProximityPrize.SubmissionLower.PortfolioSharedArithmetic6815
