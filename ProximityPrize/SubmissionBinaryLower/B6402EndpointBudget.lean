import ProximityPrize.SubmissionBinaryLower.B6402OrderProfile
import ProximityPrize.SubmissionBinaryLower.B6402ProfileBudget

/-! The normalized endpoint inequality charged by the original-label price
table. Each term has the same scale N·m² after clearing denominators. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402EndpointBudget
open B6401Params B6401ContactKerD B6402ProfileBudget B6402ProfileCosts B6402OrderProfile
open B6402InterpolationPrice B6402DimensionBudget
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2200000

structure Plan where
  W : ℕ
  WFhi : ℕ
  m : ℕ
  s : ℕ
  b : ℕ
  J : ℕ
  q : ℕ
  cap : ℕ
  lo : ℚ
  hi : ℚ
deriving Repr

def slope (p : Plan) : ℚ :=
  (B6402ProfileSecant.vquotLbQ p.W 1 p.m p.s p.hi-B6402ProfileSecant.vquotLbQ p.W 1 p.m p.s p.lo)/(p.hi-p.lo)

def cost (p : Plan) (t h : ℚ) (k : ℕ) : ℚ :=
  let m := primaryOrder p.m p.b k
  let r := (rankKerD (m-k) (p.s-1):ℚ)
  ((rankKerD m p.s:ℚ)-r)*(t+1)+h*r -
    (p.q:ℚ)*((B6402LocalMoments.localMoment m p.s:ℚ)-B6402LocalMoments.localMoment (m-k) (p.s-1))

def excess (p : Plan) (t : ℚ) : ℚ :=
  (rankKerD (p.m-p.b-2) (p.s-1)-rankKerD (p.m-p.b-3) (p.s-1):ℕ)*(t+1)

def regCost (p : Plan) (t h : ℚ) : ℚ := (regularCost p.J p.s p.m p.b:ℚ)*(t+1+p.s*h)
def badCost (p : Plan) (t h : ℚ) : ℚ := (exceptionalCost p.s p.b:ℚ)*(t+1+(p.J+16*p.b+2:ℕ)*h)

def lhs (p : Plan) (h x0 x1 x2 x3 xt c v : ℚ) : ℚ :=
  let t := (p.cap:ℚ)-p.s*h
  let m2 := (p.m:ℚ)*p.m
  x0*(cost p t h 0/m2)+x1*(cost p t h 1/m2)+x2*((cost p t h 2+regCost p t h)/m2)+
    x3*(cost p t h 3/m2)+xt*(excess p t/m2)-c*(slope p*(t+1))+v*((badCost p t h-regCost p t h)/m2)

def rhs (p : Plan) (h : ℚ) : ℚ :=
  let t := (p.cap:ℚ)-p.s*h
  (B6402ProfileSecant.vquotLbQ p.W 1 p.m p.s p.lo-slope p*p.lo)*(t+1)+
    (h*varsKerDExact wY (p.W-p.WFhi) (p.s-1) -
     (p.q:ℚ)*((gMoment wY p.W p.s:ℚ)-gMoment wY (p.W-p.WFhi) (p.s-1)))/((N:ℚ)*p.m*p.m)

theorem between (p : Plan) (x0 x1 x2 x3 xt c v h h0 h1 : ℚ)
    (lo : h0≤h) (hi : h≤h1)
    (sourceL : lhs p h0 x0 x1 x2 x3 xt c v<rhs p h0) (sourceH : lhs p h1 x0 x1 x2 x3 xt c v<rhs p h1) :
    lhs p h x0 x1 x2 x3 xt c v<rhs p h := by
  by_cases eq : h0=h1
  · have he : h=h0 := by linarith
    simpa only [he] using sourceL
  let t := (h-h0)/(h1-h0)
  have pos : 0<h1-h0 := sub_pos.mpr (lt_of_le_of_ne (lo.trans hi) eq)
  have t0 : 0≤t := div_nonneg (by linarith) pos.le
  have t1 : t≤1 := (div_le_one pos).mpr (by linarith)
  have he : h=(1-t)*h0+t*h1 := by dsimp [t]; field_simp; ring
  let f (z : ℚ) := rhs p z-lhs p z x0 x1 x2 x3 xt c v
  have aff : f h=(1-t)*f h0+t*f h1 := by
    rw [he]
    unfold f rhs lhs cost regCost badCost excess
    ring
  have h0p : 0<f h0 := sub_pos.mpr sourceL
  have h1p : 0<f h1 := sub_pos.mpr sourceH
  apply sub_pos.mp
  change 0<f h
  rw [aff]
  by_cases z : t=0
  · simpa only [z,sub_zero,one_mul,zero_mul,add_zero] using h0p
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) h0p.le) (mul_pos (lt_of_le_of_ne t0 (Ne.symm z)) h1p)

theorem cost_nat (p : Plan) (T H k : ℕ) (ht : H≤T) :
    cost p T H k=(fee (primaryOrder p.m p.b k) p.s p.q T H k : ℚ) := by
  rw [fee_formula _ _ _ _ _ _ ht]
  unfold cost; push_cast; rfl

#print axioms between
end ProximityPrize.SubmissionBinaryLower.B6402EndpointBudget
