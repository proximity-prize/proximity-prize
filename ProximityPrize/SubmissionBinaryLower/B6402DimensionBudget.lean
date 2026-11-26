import ProximityPrize.SubmissionBinaryLower.B6402InterpolationPrice

/-! Exact graded dimensions and a sufficient scalar budget for the
combined regular and exceptional interpolation map. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402DimensionBudget
open B6401ContactKerD B6401QuotInterp B6402QuotientSpace B6402PrimarySystem B6402Moments
open B6402JointMissSystem B6402LocalMoments B6402InterpolationPrice
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000

def gMoment (w W s : ℕ) := yWeightSumClosed w W s+globalSlope w W s
def sourceSize (w W s q T : ℕ) : ℤ :=
  (varsKerDExact w W s : ℤ)*(T+1)-(q : ℤ)*gMoment w W s
def localSize (m s q T : ℕ) : ℤ :=
  (rankKerD m s : ℤ)*(T+1)-(q : ℤ)*localMoment m s

theorem sourceSize_eq (w W s q T : ℕ) (hw : 1<w) (cap : q*(W/(w-1))≤T+1) :
    (Fintype.card (Slots w W s q T) : ℤ)=sourceSize w W s q T := by
  have h := global_dim w W s q T hw cap
  rw [global_moment _ _ _ (by omega)] at h
  have he := congrArg (fun n : ℕ => (n:ℤ)) h
  push_cast at he
  unfold sourceSize gMoment
  push_cast
  linarith only [he]

theorem localSize_eq (m s q T : ℕ) (cap : q*(s+2*m)≤T+1) :
    (Fintype.card (Seeds m s q T) : ℤ)=localSize m s q T := by
  have h := local_dim m s q T cap
  rw [local_moment] at h
  have he := congrArg (fun n : ℕ => (n:ℤ)) h
  push_cast at he
  unfold localSize
  linarith only [he]

theorem surplus {I R B : Type*} [Fintype I] [Fintype R] [Fintype B]
    (w W WF s q T H m2 b J : ℕ) (m k : I → ℕ) (hw : 1<w) (hT : H≤T)
    (hc : q*(W/(w-1))≤T-H+1) (hl : ∀ i,q*(s+2*m i)≤T-H+1)
    (hJ : 2≤J) (hm : 2*m2≤J+s) (hb : b≤m2)
    (budget :
      (∑ i,(localSize (m i) s q T - localSize (m i-k i) (s-1) q (T-H))) +
      (Fintype.card R : ℤ)*(regularCost J s m2 b*(T+s*H+1) : ℕ) +
      (Fintype.card B : ℤ)*(exceptionalCost s b*(T+1+(J+16*b+2)*H) : ℕ) <
      sourceSize w W s q T-sourceSize w (W-WF) (s-1) q (T-H)) :
    (∑ i,Fintype.card (Seeds (m i) s q T))+Fintype.card (Targets R B s m2 b J T H)+
      Fintype.card (Slots w (W-WF) (s-1) q (T-H)) <
      Fintype.card (Slots w W s q T)+(∑ i,Fintype.card (Seeds (m i-k i) (s-1) q (T-H)))+
      Fintype.card (Columns B s J T H b (fun _=>2)) := by
  have hg := sourceSize_eq w W s q T hw (by omega)
  have hc' := sourceSize_eq w (W-WF) (s-1) q (T-H) hw
    ((Nat.mul_le_mul_left q (Nat.div_le_div_right (Nat.sub_le W WF))).trans hc)
  have h1 (i : I) := localSize_eq (m i) s q T (by have := hl i; omega)
  have h2 (i : I) := localSize_eq (m i-k i) (s-1) q (T-H)
    ((Nat.mul_le_mul_left q (by omega : s-1+2*(m i-k i)≤s+2*m i)).trans (hl i))
  have hcost := extra_price R B s m2 b J T H hJ hT hm hb
  have hi := (Int.ofNat_le.mpr hcost)
  rw [Finset.sum_sub_distrib] at budget
  simp_rw [←h1,←h2] at budget
  rw [←hg,←hc'] at budget
  apply Int.ofNat_lt.mp
  push_cast at hi ⊢
  push_cast at budget
  linarith only [hi,budget]

#print axioms surplus
end ProximityPrize.SubmissionBinaryLower.B6402DimensionBudget
