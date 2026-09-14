import ProximityPrize.SubmissionLower.MovingFiberPackingData6811S7

namespace ProximityPrize.SubmissionLower.MovingFiberPackingCheck6811
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

/-- Scan two list spines once, without indexed lookup at every comparison. -/
def shifted (a : Nat) : List Nat → List Nat → Bool
  | [],_ => true
  | _,[] => true
  | b::bs,c::cs => decide (a+b≤c) && shifted a bs cs

/-- Check every pair whose combined index remains in the output budget. -/
def convolution : List Nat → List Nat → List Nat → Bool
  | [],_,_ => true
  | _,_,[] => true
  | a::xs,ys,c::cs => shifted a ys (c::cs) && convolution xs ys cs

theorem shifted_sound (a : Nat) (xs ys : List Nat) (h : shifted a xs ys=true)
    (i : Nat) (hi : i<xs.length) (hj : i<ys.length) :
    a+(xs[i]?).getD 0 ≤ (ys[i]?).getD 0 := by
  induction xs generalizing ys i with
  | nil => simp only [List.length_nil] at hi; omega
  | cons x xs ih =>
    cases ys with
    | nil => simp only [List.length_nil] at hj; omega
    | cons y ys =>
      simp only [shifted,Bool.and_eq_true,decide_eq_true_eq] at h
      cases i with
      | zero => simpa using h.1
      | succ i =>
        have hh := ih ys h.2 i (by simpa using hi) (by simpa using hj)
        simpa using hh

theorem convolution_sound (xs ys zs : List Nat) (h : convolution xs ys zs=true)
    (i j : Nat) (hi : i<xs.length) (hj : j<ys.length) (hk : i+j<zs.length) :
    (xs[i]?).getD 0+(ys[j]?).getD 0 ≤ (zs[i+j]?).getD 0 := by
  induction xs generalizing zs i with
  | nil => simp only [List.length_nil] at hi; omega
  | cons x xs ih =>
    cases zs with
    | nil => simp only [List.length_nil] at hk; omega
    | cons z zs =>
      simp only [convolution,Bool.and_eq_true] at h
      cases i with
      | zero =>
        simpa using shifted_sound x ys (z::zs) h.1 j hj (by simpa using hk)
      | succ i =>
        have hh := ih zs h.2 i (by simpa using hi) (by simpa [Nat.succ_add] using hk)
        simpa [Nat.succ_add] using hh

#print axioms convolution_sound
end ProximityPrize.SubmissionLower.MovingFiberPackingCheck6811
