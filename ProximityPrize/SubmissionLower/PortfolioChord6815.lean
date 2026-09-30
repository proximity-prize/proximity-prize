import Mathlib.Tactic
namespace ProximityPrize.SubmissionLower.PortfolioChord6815
set_option autoImplicit false
set_option maxHeartbeats 1200000

def Chord (lo hi : ℕ) (f : ℕ → ℕ) : Prop :=
  ∀ x, lo≤x → x≤hi → (hi-lo)*f x≤(hi-x)*f lo+(x-lo)*f hi

private theorem weights (lo x hi : ℕ) (hl : lo≤x) (hh : x≤hi) :
    (hi-x)+(x-lo)=hi-lo ∧ (hi-x)*lo+(x-lo)*hi=(hi-lo)*x := by
  constructor
  · omega
  · have ha := Nat.sub_add_cancel hh
    have hb := Nat.sub_add_cancel hl
    have hc := Nat.sub_add_cancel (hl.trans hh)
    nlinarith

theorem constant (lo hi c : ℕ) : Chord lo hi (fun _ => c) := by
  intro x hl hh
  have h := (weights lo x hi hl hh).1
  rw [←Nat.add_mul,h]

theorem affine (lo hi a b : ℕ) : Chord lo hi (fun x => a*x+b) := by
  intro x hl hh
  have hw := weights lo x hi hl hh
  have ha := congrArg (fun z => a*z) hw.2
  have hb := congrArg (fun z => b*z) hw.1
  nlinarith only [ha,hb]

theorem add {lo hi : ℕ} {f g : ℕ → ℕ} (hf : Chord lo hi f) (hg : Chord lo hi g) :
    Chord lo hi (fun x => f x+g x) := by
  intro x hl hh
  have h := Nat.add_le_add (hf x hl hh) (hg x hl hh)
  simpa only [Nat.mul_add,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

theorem mul_left {lo hi : ℕ} {f : ℕ → ℕ} (hf : Chord lo hi f) (c : ℕ) :
    Chord lo hi (fun x => c*f x) := by
  intro x hl hh
  have h := Nat.mul_le_mul_left c (hf x hl hh)
  simpa only [Nat.mul_add,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using h

theorem max {lo hi : ℕ} {f g : ℕ → ℕ} (hf : Chord lo hi f) (hg : Chord lo hi g) :
    Chord lo hi (fun x => Max.max (f x) (g x)) := by
  intro x hl hh
  dsimp only
  rcases le_total (f x) (g x) with h | h
  · rw [Nat.max_eq_right h]
    exact (hg x hl hh).trans (Nat.add_le_add
      (Nat.mul_le_mul_left _ (le_max_right _ _)) (Nat.mul_le_mul_left _ (le_max_right _ _)))
  · rw [Nat.max_eq_left h]
    exact (hf x hl hh).trans (Nat.add_le_add
      (Nat.mul_le_mul_left _ (le_max_left _ _)) (Nat.mul_le_mul_left _ (le_max_left _ _)))

theorem sub_affine (lo hi a b c d : ℕ) :
    Chord lo hi (fun x => (a*x+b)-(c*x+d)) := by
  intro x hl hh
  by_cases hx : a*x+b≤c*x+d
  · simp only [Nat.sub_eq_zero_of_le hx,Nat.mul_zero]
    exact Nat.zero_le _
  have he := Nat.sub_add_cancel (show c*x+d≤a*x+b by omega)
  have h0 : a*lo+b≤((a*lo+b)-(c*lo+d))+(c*lo+d) := by omega
  have h1 : a*hi+b≤((a*hi+b)-(c*hi+d))+(c*hi+d) := by omega
  have hsum := Nat.add_le_add (Nat.mul_le_mul_left (hi-x) h0) (Nat.mul_le_mul_left (x-lo) h1)
  have hw := weights lo x hi hl hh
  have ha := congrArg (fun z => a*z) hw.2
  have hc := congrArg (fun z => c*z) hw.2
  have hb := congrArg (fun z => b*z) hw.1
  have hd := congrArg (fun z => d*z) hw.1
  have he' := congrArg (fun z => (hi-lo)*z) he
  nlinarith only [hsum,ha,hb,hc,hd,he']

theorem le_of_endpoints {lo hi : ℕ} {f : ℕ → ℕ} (hf : Chord lo hi f)
    (cap : ℕ) (hlo : f lo≤cap) (hhi : f hi≤cap)
    (x : ℕ) (hl : lo≤x) (hh : x≤hi) : f x≤cap := by
  by_cases he : lo=hi
  · have hx : x=lo := by omega
    simpa only [hx] using hlo
  have h := (hf x hl hh).trans (Nat.add_le_add
    (Nat.mul_le_mul_left (hi-x) hlo) (Nat.mul_le_mul_left (x-lo) hhi))
  rw [←Nat.add_mul,(weights lo x hi hl hh).1] at h
  exact Nat.le_of_mul_le_mul_left h (by omega : 0<hi-lo)

end ProximityPrize.SubmissionLower.PortfolioChord6815
