import ProximityPrize.SubmissionLower.MovingFiberCount6811
import ProximityPrize.SubmissionLower.MovingFiberShape6811
import ProximityPrize.SubmissionLower.MovingFiberTenPhase6811

namespace ProximityPrize.SubmissionLower.MovingFiberSingleCore6811
open RCN095 LocatorFactorAggregate LocatorPhase6800Oracle
open MovingFiberShape6811 Lower80860.TenPhase
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def cap (slope intercept z : ℕ) : ℕ := slope*z+intercept
def rootIndex (w : ℕ) : Fin 20 := ⟨(w-1)%20,Nat.mod_lt _ (by decide)⟩
def phasePotential (j : ℕ) : Potential := (Lower80860.TenPhase.sound j).potential
def thresholdAt (q : Array ℕ) (j : ℕ) : ℕ := (q[j]?).getD 10170

structure Carrier where
  c0 : ℕ
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
  c4 : ℕ
  deriving DecidableEq, Repr

def Carrier.Correct (c : Carrier) (r v : ℕ) : Prop :=
  c.c0=cost r v 0 ∧ c.c1=cost r v 1 ∧ c.c2=cost r v 2 ∧
  c.c3=cost r v 3 ∧ c.c4=cost r v 4
instance (c : Carrier) (r v : ℕ) : Decidable (c.Correct r v) := by
  unfold Carrier.Correct; infer_instance

def Carrier.eval (c : Carrier) (z : ℕ) : ℕ :=
  if z=0 then c.c0 else if z=1 then c.c1 else if z=2 then c.c2
  else c.c3+(c.c4-c.c3)*(z-3)

theorem Carrier.eval_correct (c : Carrier) (r v z : ℕ)
    (hr : 1 ≤ r) (hc : c.Correct r v) : c.eval z = cost r v z := by
  rcases hc with ⟨h0,h1,h2,h3,h4⟩
  unfold Carrier.eval
  split_ifs with hz0 hz1 hz2
  · simpa only [hz0] using h0
  · simpa only [hz1] using h1
  · simpa only [hz2] using h2
  · rw [h3,h4,raw_affine r v z hr (by omega)]

theorem Carrier.eval_affine (c : Carrier) (lo z : ℕ) (hl : 3 ≤ lo) (hz : lo ≤ z) :
    c.eval z = c.eval lo+(c.c4-c.c3)*(z-lo) := by
  simp only [Carrier.eval,if_neg (show z≠0 by omega),if_neg (show z≠1 by omega),
    if_neg (show z≠2 by omega),if_neg (show lo≠0 by omega),
    if_neg (show lo≠1 by omega),if_neg (show lo≠2 by omega)]
  rw [show z-3=(lo-3)+(z-lo) by omega,Nat.mul_add]
  omega

def rootSlope (w r v : ℕ) : ℕ :=
  (MovingFiberCount6811.receipt (rootIndex w)).slope (r-3) (v-2)
def rootIntercept (w r v : ℕ) : ℕ :=
  (MovingFiberCount6811.receipt (rootIndex w)).intercept (r-3) (v-2)
def rootL (w : ℕ) : ℕ := MovingFiberCount6811.sourceLimit (rootIndex w)
def rootUpper (w r v z : ℕ) : ℕ := rootSlope w r v*z+rootIntercept w r v

def choice (c : Carrier) (w r v z : ℕ) : ℕ :=
  if w=0 then c.eval z else if w≤20 then rootUpper w r v z
  else (phasePotential (w-21)).eval (rawFlag r v z)

def Active (thresholds : Array ℕ) (w r v lo hi : ℕ) : Prop :=
  if w=0 then r≤32 ∧ r+v≤149 ∧ r+v+hi≤8121 ∧ BoundaryTailGates6808.Safe r (r+v)
  else if w≤20 then 3 ≤ r ∧ r ≤ 31 ∧ 2 ≤ v ∧ 3 ≤ lo ∧
    rootL w < r+v+lo ∧ r+v ≤ 142 ∧ r+v+hi ≤ 7501
  else w-21 < 7 ∧ thresholdAt thresholds (w-21) ≤ lo
instance (thresholds : Array ℕ) (w r v lo hi : ℕ) : Decidable (Active thresholds w r v lo hi) := by
  unfold Active; infer_instance

def choiceSlope (c : Carrier) (w r v : ℕ) : ℕ :=
  if w=0 then c.c4-c.c3 else if w≤20 then rootSlope w r v
  else (phasePotential (w-21)).totalCoeff

theorem choice_affine (c : Carrier) (w r v lo z : ℕ)
    (hlo : 3 ≤ lo) (hz : lo ≤ z) :
    choice c w r v z = choice c w r v lo + choiceSlope c w r v*(z-lo) := by
  by_cases hw0 : w=0
  · simpa only [choice,choiceSlope,if_pos hw0] using c.eval_affine lo z hlo hz
  by_cases hw1 : w≤20
  · simp only [choice,choiceSlope,if_neg hw0,if_pos hw1,rootUpper]
    conv_lhs => rw [show z=lo+(z-lo) by omega]
    ring
  · simp only [choice,choiceSlope,if_neg hw0,if_neg hw1,Potential.eval,
      rawFlag_total,rawFlag_middle,rawFlag_all]
    conv_lhs => rw [show z=lo+(z-lo) by omega]
    ring

theorem affine_le_between (a A m M d finish : ℕ) (hd : d ≤ finish)
    (hstart : a ≤ A) (hend : a+m*finish ≤ A+M*finish) : a+m*d ≤ A+M*d := by
  by_cases hm : m ≤ M
  · exact Nat.add_le_add hstart (Nat.mul_le_mul_right d hm)
  · have hMm : M ≤ m := (Nat.lt_of_not_ge hm).le
    have hdecomp : M+(m-M)=m := Nat.add_sub_of_le hMm
    have hdelta : a+(m-M)*finish ≤ A := by
      rw [← hdecomp,Nat.add_mul] at hend
      omega
    have hh := (Nat.add_le_add_left (Nat.mul_le_mul_left (m-M) hd) a).trans hdelta
    nlinarith [hdecomp]

theorem choice_between (c : Carrier) (w slope intercept r v lo hi z : ℕ)
    (hlo : 3 ≤ lo) (hz : lo ≤ z) (hzi : z ≤ hi)
    (h0 : choice c w r v lo ≤ cap slope intercept lo)
    (h1 : choice c w r v hi ≤ cap slope intercept hi) :
    choice c w r v z ≤ cap slope intercept z := by
  have hi0 : lo ≤ hi := hz.trans hzi
  rw [choice_affine c w r v lo hi hlo hi0] at h1
  rw [choice_affine c w r v lo z hlo hz]
  have hc (x : ℕ) (hx : lo ≤ x) : cap slope intercept x = cap slope intercept lo+slope*(x-lo) := by
    unfold cap
    conv_lhs => rw [show x=lo+(x-lo) by omega]
    ring
  rw [hc hi hi0] at h1
  rw [hc z hz]
  exact affine_le_between _ _ _ _ _ _ (Nat.sub_le_sub_right hzi lo) h0 h1

structure Run where
  stop : ℕ
  who : ℕ
  deriving DecidableEq, Repr

def Cover (c : Carrier) (slope intercept r v : ℕ) (thresholds : Array ℕ) (finish : ℕ) :
    ℕ → List Run → Prop
  | lo,[] => lo=finish
  | lo,x::xs => lo<x.stop ∧ x.stop≤finish ∧ (3≤lo ∨ x.stop=lo+1) ∧
    Active thresholds x.who r v lo (x.stop-1) ∧
    choice c x.who r v lo ≤ cap slope intercept lo ∧
    choice c x.who r v (x.stop-1) ≤ cap slope intercept (x.stop-1) ∧
    Cover c slope intercept r v thresholds finish x.stop xs
instance (c : Carrier) (slope intercept r v : ℕ) (thresholds : Array ℕ) (finish lo : ℕ) (xs : List Run) :
    Decidable (Cover c slope intercept r v thresholds finish lo xs) := by
  induction xs generalizing lo with
  | nil => simp only [Cover]; infer_instance
  | cons x xs ih => simp only [Cover]; infer_instance

theorem active_at (th : Array ℕ) (w r v lo hi z : ℕ)
    (h : Active th w r v lo hi) (hz : lo ≤ z) (hzi : z ≤ hi) : Active th w r v z z := by
  unfold Active at h ⊢
  by_cases h0 : w=0
  · simp only [if_pos h0] at h ⊢
    exact ⟨h.1,h.2.1,by omega,h.2.2.2⟩
  · simp only [if_neg h0] at h ⊢
    split_ifs at h ⊢ <;> omega

#print axioms choice_between

theorem cover_sound (c : Carrier) (slope intercept r v : ℕ) (th : Array ℕ)
    (finish lo : ℕ) (xs : List Run) (h : Cover c slope intercept r v th finish lo xs)
    (z : ℕ) (hz : lo ≤ z) (hzi : z < finish) :
    ∃ w, Active th w r v z z ∧ choice c w r v z ≤ cap slope intercept z := by
  induction xs generalizing lo with
  | nil => simp only [Cover] at h; omega
  | cons x xs ih =>
    rcases h with ⟨hstop,hfin,hlow,hact,h0,h1,hrest⟩
    by_cases hzs : z<x.stop
    · refine ⟨x.who,active_at th x.who r v lo (x.stop-1) z hact hz (by omega),?_⟩
      rcases hlow with hlo | hlo
      · exact choice_between c x.who slope intercept r v lo (x.stop-1) z hlo hz (by omega) h0 h1
      · have he : z=lo := by omega
        simpa only [he] using h0
    · exact ih x.stop hrest (by omega)

#print axioms cover_sound
end ProximityPrize.SubmissionLower.MovingFiberSingleCore6811
