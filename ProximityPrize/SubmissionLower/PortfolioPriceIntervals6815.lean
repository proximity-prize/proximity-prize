import ProximityPrize.SubmissionLower.PortfolioCost6815
import ProximityPrize.SubmissionLower.PortfolioChord6815
namespace ProximityPrize.SubmissionLower.PortfolioPriceIntervals6815
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000
open RCN095 RCN260
open PortfolioCost6815 PortfolioChord6815 MovingSourceBandLeading6815
open MovingSourcePairRetainedStage6814 MovingSourceBandPairArithmetic6814

theorem mixed_chord {lo hi : ℕ} {f g : ℕ → ℕ}
    (hf : Chord lo hi f) (hg : Chord lo hi g)
    (a b c d : ℕ) (W : FlagDegree) :
    Chord lo hi (fun x => flagMixed ⟨f x,a,b⟩ ⟨g x,c,d⟩ W) := by
  have he : (fun x => flagMixed ⟨f x,a,b⟩ ⟨g x,c,d⟩ W)=
      (fun x => (d*W.all+c*W.all+W.yz*d)*f x+
        (b*W.all+a*W.all+W.yz*b)*g x+flagMixed ⟨0,a,b⟩ ⟨0,c,d⟩ W) := by
    funext x
    simp only [flagMixed]
    ring
  rw [he]
  exact add (add (mul_left hf _) (mul_left hg _)) (constant lo hi _)

def numerator (z : Degrees) (delta : ℕ) (p q : FlagDegree) (t y r : ℕ) : ℕ :=
  pairNumerator (z.d*delta) (delta*flagMixed (parent t y r) unitZFlag z.flag)
    (z.d*flagMixed p q unitYZFlag) (z.d*flagMixed p q unitAllFlag) t y r (parent t y r)

def leadingNumerator (z : Degrees) (t y r : ℕ) : ℕ :=
  AsymmetricHelper.leftRegularNumerator (pair t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0))

def totalNumerator (z : Degrees) (delta : ℕ) (p q : FlagDegree) (t y r : ℕ) : ℕ :=
  50174*numerator z delta p q t y r+3*(z.d*delta)*leadingNumerator z t y r

theorem price_le_of_total (z : Degrees) (delta : ℕ) (hd : 0<delta)
    (p q : FlagDegree) (t y r cap : ℕ)
    (h : totalNumerator z delta p q t y r≤50174*(3*(z.d*delta))*cap) :
    pairCost z delta p q t y r+leading z t y r≤cap := by
  have hn : pairCost z delta p q t y r*(3*(z.d*delta))≤numerator z delta p q t y r :=
    Nat.div_mul_le_self _ _
  have hl : leading z t y r*50174≤leadingNumerator z t y r := by
    change AsymmetricHelper.leftRegularCountCap (pair t y r _ _ _)*50174≤_
    simpa only [AsymmetricHelper.leftRegularCountCap,pair,UnequalParameters.gap,Nat.reduceSub,
      leadingNumerator] using
      Nat.div_mul_le_self (leadingNumerator z t y r) 50174
  have h1 := Nat.mul_le_mul_left 50174 hn
  have h2 := Nat.mul_le_mul_left (3*(z.d*delta)) hl
  have hdz : 0<z.d := by dsimp [Degrees.d]; omega
  apply Nat.le_of_mul_le_mul_left (c:=50174*(3*(z.d*delta))) ?_
    (by positivity)
  dsimp only [totalNumerator] at h
  nlinarith only [h,h1,h2]

theorem numerator_chord {lo hi : ℕ} {f g : ℕ → ℕ}
    (hf : Chord lo hi f) (hg : Chord lo hi g)
    (a b c d : ℕ) (z : Degrees) (delta t y r : ℕ) :
    Chord lo hi (fun x => numerator z delta ⟨f x,a,b⟩ ⟨g x,c,d⟩ t y r) := by
  simp only [numerator,pairNumerator_eq]
  exact add (add (constant lo hi _) (mul_left (mul_left (mixed_chord hf hg a b c d unitYZFlag) z.d) _))
    (mul_left (mul_left (mixed_chord hf hg a b c d unitAllFlag) z.d) _)

theorem total_chord {lo hi : ℕ} {f g : ℕ → ℕ}
    (hf : Chord lo hi f) (hg : Chord lo hi g)
    (a b c d : ℕ) (z : Degrees) (delta t y r : ℕ) :
    Chord lo hi (fun x => totalNumerator z delta ⟨f x,a,b⟩ ⟨g x,c,d⟩ t y r) :=
  add (mul_left (numerator_chord hf hg a b c d z delta t y r) 50174) (constant lo hi _)

def ownerFlag (s b u x : ℕ) : FlagDegree := ⟨x-u,u+s-b,b⟩
def cofactorFlag (B U L S e s b u x : ℕ) : FlagDegree :=
  let rb := B-e*b
  let ru := Max.max rb (U-e*u)
  ⟨L-(e*x+ru),ru+(S-e*s)-rb,rb⟩

theorem cofactor_total_chord (lo hi s b u B U L S e : ℕ) (z : Degrees) (delta t y r : ℕ) :
    Chord lo hi (fun x => totalNumerator z delta (ownerFlag s b u x)
      (cofactorFlag B U L S e s b u x) t y r) := by
  have hf : Chord lo hi (fun x => x-u) := by
    simpa only [Nat.one_mul,Nat.zero_mul,Nat.add_zero,Nat.zero_add] using sub_affine lo hi 1 0 0 u
  have hg : Chord lo hi (fun x => L-(e*x+Max.max (B-e*b) (U-e*u))) := by
    simpa only [Nat.zero_mul,Nat.zero_add] using sub_affine lo hi 0 L e (Max.max (B-e*b) (U-e*u))
  exact total_chord hf hg _ _ _ _ z delta t y r

theorem cofactor_interval_price (lo hi s b u B U L S e : ℕ) (z : Degrees)
    (delta t y r cap : ℕ) (hd : 0<delta)
    (hlo : totalNumerator z delta (ownerFlag s b u lo) (cofactorFlag B U L S e s b u lo) t y r≤
      50174*(3*(z.d*delta))*cap)
    (hhi : totalNumerator z delta (ownerFlag s b u hi) (cofactorFlag B U L S e s b u hi) t y r≤
      50174*(3*(z.d*delta))*cap)
    (x : ℕ) (hx : lo≤x) (hx' : x≤hi) :
    pairCost z delta (ownerFlag s b u x) (cofactorFlag B U L S e s b u x) t y r+
      leading z t y r≤cap :=
  price_le_of_total z delta hd _ _ t y r cap
    (le_of_endpoints (cofactor_total_chord lo hi s b u B U L S e z delta t y r) _ hlo hhi x hx hx')

end ProximityPrize.SubmissionLower.PortfolioPriceIntervals6815
