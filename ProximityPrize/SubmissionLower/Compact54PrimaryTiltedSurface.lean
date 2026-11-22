import ProximityPrize.SubmissionLower.Final50SurfaceLinearFive

set_option Elab.async false
set_option autoImplicit false

namespace Final50SharedPrice

open K1_13 (Shape)
open Final50Price (bentGraph bentLift taylorLength tiltedFits)
open private signedFive signed_five_coeffs coeffB coeffJ coeffT
  from ProximityPrize.SubmissionLower.Final50SurfaceLinearFive

/-- Evaluate the tilted surface at the primary box with a Horner polynomial. -/
def primaryTiltedSurface (x : Shape) : ℕ :=
  let b : ℤ := x.b
  let j : ℤ := x.j
  let t : ℤ := x.t
  (if x.t = 1 then
    b * (j * (56445557899104000 * j - 188150591050752000) + 122297316837696000) +
      j * (j * (367607022303095040 - 28222778949552000 * j) - 1621951576765077120) +
      2279842793464147200
  else
    b * (j * (84668283990576000 * j - 338671726393440000) + 263410841577312000) +
      j * (j * (532948362137043840 * t - 42334141995288000 * j - 48712995487786560) +
        t * (-1598845086411131520 * t - 710601365223498240) + 276169676217283200) +
      t * (t * (1598845086411131520 * t + 1065902047835247360) + 236868304759188480)).toNat

private theorem lifted_clip_one (k : ℕ) :
    min (1+k) ((2+k)/2) = (2+k)/2 := by
  apply min_eq_right
  omega

private theorem lifted_clip {k t : ℕ} (ht : 2 ≤ t) :
    min (1+k) ((2+k*t)/2) = 1+k := by
  apply min_eq_left
  have h := Nat.mul_le_mul_left k ht
  rw [Nat.mul_comm k 2] at h
  omega

set_option maxHeartbeats 2500000 in
theorem primaryTiltedSurface_eq (x : Shape) (hf : tiltedFits x) (ht : 0 < x.t) :
    primaryTiltedSurface x = Final50Price.tiltedSurface x.chamber Final50Price.primaryBox := by
  have hb : 1 ≤ x.b := by have := hf.2; omega
  have hj : 2 ≤ x.j := by have := hf.1; omega
  have hc : x.chamber = x := by
    cases x with
    | mk b j t =>
      have hh : j ≤ b := by have := hf.2; exact Nat.le_trans (Nat.le_succ j) this
      simp only [Shape.chamber, max_eq_left hh]
  have hg : bentGraph x = (⟨x.b, x.j+1, x.t+1⟩,1) := by
    simp only [bentGraph, max_eq_left hf.2]
  rw [hc]
  change primaryTiltedSurface x =
    (signedFive (x,0) (Final50Price.primaryBox,0) (bentGraph x)
      (bentLift (taylorLength-4) x) (bentLift (taylorLength-3) x)).toNat
  rw [signed_five_coeffs, hg]
  unfold primaryTiltedSurface
  apply congrArg Int.toNat
  by_cases h : x.t = 1
  · simp only [if_pos h, h, bentLift, Nat.mul_one, lifted_clip_one, coeffB, coeffJ, coeffT,
      Final50Price.primaryBox, taylorLength, Final50Price.physicalDegree,
      Nat.cast_add, Nat.cast_mul, Nat.cast_sub hb, Nat.cast_sub hj]
    norm_num <;> ring
  · have h2 : 2 ≤ x.t := by omega
    simp only [if_neg h, bentLift, lifted_clip h2, coeffB, coeffJ, coeffT,
      Final50Price.primaryBox, taylorLength, Final50Price.physicalDegree,
      Nat.cast_add, Nat.cast_mul, Nat.cast_sub hb, Nat.cast_sub hj]
    norm_num <;> ring

end Final50SharedPrice
