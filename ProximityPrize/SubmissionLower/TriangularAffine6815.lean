import Mathlib.Tactic
namespace ProximityPrize.SubmissionLower.TriangularAffine6815
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem affine_between (a b m n d finish : ℕ) (hd : d≤finish)
    (h0 : a≤b) (h1 : a+m*finish≤b+n*finish) : a+m*d≤b+n*d := by
  by_cases hmn : m≤n
  · exact Nat.add_le_add h0 (Nat.mul_le_mul_right d hmn)
  · have hnm : n≤m := by omega
    have he : n+(m-n)=m := Nat.add_sub_of_le hnm
    have hh := Nat.mul_le_mul_left (m-n) hd
    nlinarith only [h1,he,hh]

theorem shifted_between (lo hi z p q a b m n : ℕ)
    (hp : p≤lo) (hq : q≤lo) (hz : lo≤z) (hh : z≤hi)
    (h0 : a+m*(lo-p)≤b+n*(lo-q))
    (h1 : a+m*(hi-p)≤b+n*(hi-q)) :
    a+m*(z-p)≤b+n*(z-q) := by
  have hhi : a+m*(lo-p)+m*(hi-lo)≤b+n*(lo-q)+n*(hi-lo) := by
    rw [show hi-p=(lo-p)+(hi-lo) by omega,show hi-q=(lo-q)+(hi-lo) by omega,
      Nat.mul_add,Nat.mul_add] at h1
    simpa only [Nat.add_assoc] using h1
  have h := affine_between (a+m*(lo-p)) (b+n*(lo-q)) m n (z-lo) (hi-lo) (by omega) h0 hhi
  rwa [show z-p=(lo-p)+(z-lo) by omega,show z-q=(lo-q)+(z-lo) by omega,
    Nat.mul_add,Nat.mul_add,←Nat.add_assoc,←Nat.add_assoc]

def left (cc cs clo charge slope x z : ℕ) := cc+cs*(x-clo)+charge+slope*(z-x)
def right (pc ps plo z : ℕ) := pc+ps*(z-plo)
def EndAt (cc cs clo chi charge slope pc ps plo z : ℕ) : Prop :=
  left cc cs clo charge slope clo z≤right pc ps plo z ∧
  left cc cs clo charge slope (min chi z) z≤right pc ps plo z

theorem triangle (cc cs clo chi charge slope pc ps plo phi x z : ℕ)
    (hchild : clo≤chi) (hparent : max plo clo≤phi)
    (h0 : EndAt cc cs clo chi charge slope pc ps plo (max plo clo))
    (h1 : EndAt cc cs clo chi charge slope pc ps plo phi)
    (hm : EndAt cc cs clo chi charge slope pc ps plo (min phi (max (max plo clo) chi)))
    (hx : clo≤x) (hxh : x≤chi) (hxp : x≤z) (hz : plo≤z) (hzh : z≤phi) :
    left cc cs clo charge slope x z≤right pc ps plo z := by
  let lo := max plo clo
  have hlo : lo≤z := by dsimp only [lo]; omega
  by_cases hc : cs≤slope
  · have hc' := Nat.mul_le_mul_right (x-clo) hc
    have hdecomp : (x-clo)+(z-x)=z-clo := by omega
    have hmul := congrArg (fun n => slope*n) hdecomp
    have hbound : left cc cs clo charge slope x z≤cc+charge+slope*(z-clo) := by
      unfold left
      rw [Nat.mul_add] at hmul
      omega
    have he0 : cc+charge+slope*(lo-clo)≤pc+ps*(lo-plo) := by
      have h := h0.1
      simpa only [left,right,Nat.sub_self,Nat.mul_zero,Nat.add_zero,lo] using h
    have he1 : cc+charge+slope*(phi-clo)≤pc+ps*(phi-plo) := by
      have h := h1.1
      simpa only [left,right,Nat.sub_self,Nat.mul_zero,Nat.add_zero] using h
    exact hbound.trans (shifted_between lo phi z clo plo (cc+charge) pc slope ps
      (le_max_right _ _) (le_max_left _ _) hlo hzh he0 he1)
  have hc : slope≤cs := by omega
  let top := min chi z
  have htop : x≤top := le_min hxh hxp
  have hc' := Nat.mul_le_mul_right (top-x) hc
  have e1 : top-clo=(x-clo)+(top-x) := by omega
  have e2 : z-x=(z-top)+(top-x) := by dsimp only [top]; omega
  have hbound : left cc cs clo charge slope x z≤left cc cs clo charge slope top z := by
    unfold left
    rw [e1,e2,Nat.mul_add,Nat.mul_add]
    omega
  apply hbound.trans
  by_cases hzc : z≤chi
  · have hloc : lo≤chi := hlo.trans hzc
    have hpivot : min phi (max lo chi)=min phi chi := by rw [max_eq_right hloc]
    have hmid : min phi chi≤chi := min_le_right _ _
    have he0 : cc+charge+cs*(lo-clo)≤pc+ps*(lo-plo) := by
      have h := h0.2
      change left cc cs clo charge slope (min chi lo) lo≤_ at h
      rw [min_eq_right hloc] at h
      simpa only [left,right,Nat.sub_self,Nat.mul_zero,Nat.add_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    have he1 : cc+charge+cs*(min phi chi-clo)≤pc+ps*(min phi chi-plo) := by
      have h := hm.2
      change left cc cs clo charge slope (min chi (min phi (max lo chi))) (min phi (max lo chi))≤_ at h
      rw [hpivot,min_eq_right hmid] at h
      simpa only [left,right,Nat.sub_self,Nat.mul_zero,Nat.add_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    have h := shifted_between lo (min phi chi) z clo plo (cc+charge) pc cs ps
      (le_max_right _ _) (le_max_left _ _) hlo (le_min hzh hzc) he0 he1
    simpa only [left,right,top,min_eq_right hzc,Nat.sub_self,Nat.mul_zero,Nat.add_zero,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  · have hcz : chi≤z := by omega
    have hpivot : min phi (max lo chi)=max lo chi := min_eq_right (by omega)
    have he0 : cc+cs*(chi-clo)+charge+slope*(max lo chi-chi)≤pc+ps*(max lo chi-plo) := by
      have h := hm.2
      change left cc cs clo charge slope (min chi (min phi (max lo chi))) (min phi (max lo chi))≤_ at h
      rw [hpivot,min_eq_left (le_max_right _ _)] at h
      exact h
    have he1 : cc+cs*(chi-clo)+charge+slope*(phi-chi)≤pc+ps*(phi-plo) := by
      have h := h1.2
      rw [min_eq_left (hcz.trans hzh)] at h
      exact h
    have h := shifted_between (max lo chi) phi z chi plo (cc+cs*(chi-clo)+charge) pc slope ps
      (le_max_right _ _) ((le_max_left plo clo).trans (le_max_left _ _)) (by omega) hzh he0 he1
    simpa only [left,right,top,min_eq_left hcz] using h

instance (cc cs clo chi charge slope pc ps plo z : ℕ) :
    Decidable (EndAt cc cs clo chi charge slope pc ps plo z) := by unfold EndAt; infer_instance

def check (cc cs clo chi charge slope pc ps plo phi : ℕ) : Bool :=
  if clo≤chi ∧ max plo clo≤phi then
    decide (EndAt cc cs clo chi charge slope pc ps plo (max plo clo) ∧
      EndAt cc cs clo chi charge slope pc ps plo phi ∧
      EndAt cc cs clo chi charge slope pc ps plo (min phi (max (max plo clo) chi)))
  else true

theorem check_sound (cc cs clo chi charge slope pc ps plo phi x z : ℕ)
    (h : check cc cs clo chi charge slope pc ps plo phi=true)
    (hx : clo≤x) (hxh : x≤chi) (hxp : x≤z) (hz : plo≤z) (hzh : z≤phi) :
    left cc cs clo charge slope x z≤right pc ps plo z := by
  have hc : clo≤chi ∧ max plo clo≤phi := by omega
  simp only [check,if_pos hc,decide_eq_true_eq] at h
  exact triangle cc cs clo chi charge slope pc ps plo phi x z hc.1 hc.2 h.1 h.2.1 h.2.2 hx hxh hxp hz hzh

end ProximityPrize.SubmissionLower.TriangularAffine6815
