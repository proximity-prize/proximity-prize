import ProximityPrize.SubmissionLower.HigherRootArithmetic6810
import ProximityPrize.SubmissionLower.HigherShape6810
import ProximityPrize.SubmissionLower.HigherPhaseCore6810
import ProximityPrize.SubmissionLower.AffineFactorAggregate6808

namespace ProximityPrize.SubmissionLower.HigherAffineSingleton6810
open RCN095 LocatorFactorAggregate LocatorPhase6800Oracle
open HigherShape6810 Lower80850.PhaseRows
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def slope : ℕ := 26000000000000
def cap (rate r z : ℕ) : ℕ := slope*z+r*rate

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
  if w=1 then HigherRootArithmetic6810.P0.fullSlope (r-3) (v-2)/1808028+1 else if w=2 then HigherRootArithmetic6810.P1.fullSlope (r-3) (v-2)/2460927+1 else if w=3 then HigherRootArithmetic6810.P2.fullSlope (r-3) (v-2)/2460927+1 else HigherRootArithmetic6810.P3.fullSlope (r-3) (v-2)/1808028+1
def rootIntercept (w r v : ℕ) : ℕ :=
  if w=1 then HigherRootArithmetic6810.P0.fullIntercept (r-3) (v-2)/1808028+1 else if w=2 then HigherRootArithmetic6810.P1.fullIntercept (r-3) (v-2)/2460927+1 else if w=3 then HigherRootArithmetic6810.P2.fullIntercept (r-3) (v-2)/2460927+1 else HigherRootArithmetic6810.P3.fullIntercept (r-3) (v-2)/1808028+1
def rootL (w : ℕ) : ℕ :=
  if w=1 then 1800 else if w=2 then 2749 else if w=3 then 2526 else 2695
def rootUpper (w r v z : ℕ) : ℕ := rootSlope w r v*z+rootIntercept w r v

def choice (c : Carrier) (w r v z : ℕ) : ℕ :=
  if w=0 then c.eval z else if w≤4 then rootUpper w r v z
  else (phasePotential (w-5)).eval (rawFlag r v z)

def Active (thresholds : Array ℕ) (w r v lo hi : ℕ) : Prop :=
  if w=0 then r≤32 ∧ r+v≤149 ∧ r+v+hi≤8121 ∧ BoundaryTailGates6808.Safe r (r+v)
  else if w≤4 then 3 ≤ r ∧ r ≤ 31 ∧ 2 ≤ v ∧ 3 ≤ lo ∧
    rootL w < r+v+lo ∧ r+v ≤ 142 ∧ r+v+hi ≤ 7501
  else w-5 < 10 ∧ thresholdAt thresholds (w-5) ≤ lo
instance (thresholds : Array ℕ) (w r v lo hi : ℕ) : Decidable (Active thresholds w r v lo hi) := by
  unfold Active; infer_instance

def choiceSlope (c : Carrier) (w r v : ℕ) : ℕ :=
  if w=0 then c.c4-c.c3 else if w≤4 then rootSlope w r v
  else (phasePotential (w-5)).totalCoeff

theorem choice_affine (c : Carrier) (w r v lo z : ℕ)
    (hlo : 3 ≤ lo) (hz : lo ≤ z) :
    choice c w r v z = choice c w r v lo + choiceSlope c w r v*(z-lo) := by
  by_cases hw0 : w=0
  · simpa only [choice,choiceSlope,if_pos hw0] using c.eval_affine lo z hlo hz
  by_cases hw1 : w≤4
  · simp only [choice,choiceSlope,if_neg hw0,if_pos hw1,rootUpper]
    conv_lhs => rw [show z=lo+(z-lo) by omega]
    ring
  · simp only [choice,choiceSlope,if_neg hw0,if_neg hw1,Potential.eval,
      rawFlag_total,rawFlag_middle,rawFlag_all]
    conv_lhs => rw [show z=lo+(z-lo) by omega]
    ring

theorem choice_between (c : Carrier) (w rate r v lo hi z : ℕ)
    (hlo : 3 ≤ lo) (hz : lo ≤ z) (hzi : z ≤ hi)
    (h0 : choice c w r v lo ≤ cap rate r lo)
    (h1 : choice c w r v hi ≤ cap rate r hi) :
    choice c w r v z ≤ cap rate r z := by
  have hi0 : lo ≤ hi := hz.trans hzi
  rw [choice_affine c w r v lo hi hlo hi0] at h1
  rw [choice_affine c w r v lo z hlo hz]
  have hc (x : ℕ) (hx : lo ≤ x) : cap rate r x = cap rate r lo+slope*(x-lo) := by
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

def Cover (c : Carrier) (rate r v : ℕ) (thresholds : Array ℕ) (finish : ℕ) :
    ℕ → List Run → Prop
  | lo,[] => lo=finish
  | lo,x::xs => lo<x.stop ∧ x.stop≤finish ∧ (3≤lo ∨ x.stop=lo+1) ∧
    Active thresholds x.who r v lo (x.stop-1) ∧
    choice c x.who r v lo ≤ cap rate r lo ∧
    choice c x.who r v (x.stop-1) ≤ cap rate r (x.stop-1) ∧
    Cover c rate r v thresholds finish x.stop xs
instance (c : Carrier) (rate r v : ℕ) (thresholds : Array ℕ) (finish lo : ℕ) (xs : List Run) :
    Decidable (Cover c rate r v thresholds finish lo xs) := by
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

theorem cover_sound (c : Carrier) (rate r v : ℕ) (th : Array ℕ)
    (finish lo : ℕ) (xs : List Run) (h : Cover c rate r v th finish lo xs)
    (z : ℕ) (hz : lo ≤ z) (hzi : z < finish) :
    ∃ w, Active th w r v z z ∧ choice c w r v z ≤ cap rate r z := by
  induction xs generalizing lo with
  | nil => simp only [Cover] at h; omega
  | cons x xs ih =>
    rcases h with ⟨hstop,hfin,hlow,hact,h0,h1,hrest⟩
    by_cases hzs : z<x.stop
    · refine ⟨x.who,active_at th x.who r v lo (x.stop-1) z hact hz (by omega),?_⟩
      rcases hlow with hlo | hlo
      · exact choice_between c x.who rate r v lo (x.stop-1) z hlo hz (by omega) h0 h1
      · have he : z=lo := by omega
        simpa only [he] using h0
    · exact ih x.stop hrest (by omega)

end ProximityPrize.SubmissionLower.HigherAffineSingleton6810
