import ProximityPrize.SubmissionLower.Final50SharedPrice

set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 900000

namespace Final50SharedPrice

open K1_13 (Shape chart difference volume32)
open K1_13_8 (Valid)
open Final50Price (taylorLength)
open K1_13_8_2 (signedMixed signed_rotate signed_nonneg)

/-- Extract the three coefficients with the same probes as `weights`. The sign
conditions ensure that every subtraction in the natural-number probes is exact. -/
theorem surface_eq_weights_of_signed (kind : Surface) (f : Shape) (b j t : ℤ)
    (hb : 0 ≤ b) (hj : 0 ≤ j) (ht : 0 ≤ t)
    (h : ∀ q : Shape, (surface kind f q : ℤ) = b*q.b + j*q.j + t*q.t) (q : Shape) :
    surface kind f q = (weights kind f).b*q.b + (weights kind f).j*q.j +
      (weights kind f).t*q.t := by
  have hn (u : Shape) : surface kind f u = b.toNat*u.b + j.toNat*u.j + t.toNat*u.t := by
    apply Int.ofNat.inj
    change (surface kind f u : ℤ) = ((b.toNat*u.b + j.toNat*u.j + t.toNat*u.t : ℕ) : ℤ)
    rw [h u]
    push_cast
    rw [Int.toNat_of_nonneg hb, Int.toNat_of_nonneg hj, Int.toNat_of_nonneg ht]
  have hw : weights kind f = ⟨b.toNat,j.toNat,t.toNat⟩ := by
    unfold weights
    simp only [hn ⟨1,0,0⟩, hn ⟨1,1,0⟩, hn ⟨3,3,1⟩, Nat.mul_one, Nat.mul_zero,
      Nat.add_zero, Nat.add_sub_cancel_left]
    congr 1
    omega
  rw [hw]
  exact hn q



end Final50SharedPrice
