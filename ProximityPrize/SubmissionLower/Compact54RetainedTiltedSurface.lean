import ProximityPrize.SubmissionLower.Final50SurfaceLinearFive

set_option Elab.async false
set_option autoImplicit false

namespace Final50SharedPrice

open K1_13 (Shape)
open Final50Price (bentGraph bentLift taylorLength tiltedFits)
open private signedFive signed_five_coeffs coeffB coeffJ coeffT
  from ProximityPrize.SubmissionLower.Final50SurfaceLinearFive

private def hornerB (j t : ℤ) (one : Prop) [Decidable one] : ℤ :=
  if one then
    j * (76971743905920 * j - 444724499525760) + 658533446985600
  else
    j * (j * (153942334528320 * t - 68418217346880) +
      t * (-461827003584960 * t - 205257471179520) + 136836434697600) +
    t * (t * (461827003584960 * t + 307886206769280) + 68419498775040)

private def hornerJ (b j t : ℤ) (one : Prop) [Decidable one] : ℤ :=
  if one then
    b * (153943487811840 * j - 444724499525760) +
    j * (491762520503040 - 115457615858880 * j) - 478933191739200
  else
    b * (j * (307884669056640 * t - 136836434693760) +
      t * (-461827003584960 * t - 205257471179520) + 136836434697600) +
    j * (j * (102627326020320 - 230913501792480 * t) +
      t * (538798170849120 * t + 205257471179520) - 153941053106880) +
    t * (t * (-384855836320800 * t - 205257471179520) - 34209749387520)

private def hornerT (b j t : ℤ) (one : Prop) [Decidable one] : ℤ :=
  if one then
    b * (j * (102628287089280 * j - 803922447164160) + 1556532256464000) +
    j * (j * (453275367126720 - 51314143544640 * j) - 1180227351814080) + 778266128232000
  else
    b * (j * (153942334528320 * j - 923654007169920 * t - 205257471179520) +
      t * (1385481010754880 * t + 615772413538560) + 68419498775040) +
    j * (j * (538798170849120 * t - 76971167264160 * j + 102628735589760) +
      t * (-1154567508962400 * t - 410514942359040) - 34209749387520) +
    t * (t * (692740505377440 * t + 307886206769280) + 34209749387520)

/-- Evaluate the signed surface from its three cutter coordinates, then clip to a natural number. -/
def tiltedSurfaceHorner (x q : Shape) : ℕ :=
  (hornerB x.j x.t (x.t = 1) * q.b + hornerJ x.b x.j x.t (x.t = 1) * q.j +
    hornerT x.b x.j x.t (x.t = 1) * q.t).toNat

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
theorem tiltedSurfaceHorner_eq (x q : Shape) (hf : tiltedFits x) (ht : 0 < x.t) :
    tiltedSurfaceHorner x q = Final50Price.tiltedSurface x.chamber q := by
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
  change tiltedSurfaceHorner x q =
    (signedFive (x,0) (q,0) (bentGraph x)
      (bentLift (taylorLength-4) x) (bentLift (taylorLength-3) x)).toNat
  rw [signed_five_coeffs, hg]
  unfold tiltedSurfaceHorner
  apply congrArg Int.toNat
  let g : Final50Price.BentCap := (⟨x.b, x.j+1, x.t+1⟩,1)
  let l := bentLift (taylorLength-4) x
  let r := bentLift (taylorLength-3) x
  suffices h : hornerB x.j x.t (x.t = 1) = coeffB (x,0) g l r ∧
      hornerJ x.b x.j x.t (x.t = 1) = coeffJ (x,0) g l r ∧
      hornerT x.b x.j x.t (x.t = 1) = coeffT (x,0) g l r by
    change hornerB x.j x.t (x.t = 1) * q.b + hornerJ x.b x.j x.t (x.t = 1) * q.j +
      hornerT x.b x.j x.t (x.t = 1) * q.t =
        coeffB (x,0) g l r * q.b + coeffJ (x,0) g l r * q.j + coeffT (x,0) g l r * q.t
    rw [h.1, h.2.1, h.2.2]
  by_cases h : x.t = 1
  · refine ⟨?_,?_,?_⟩ <;>
      simp only [hornerB, hornerJ, hornerT, if_pos h, h,
        g, l, r, bentLift, Nat.mul_one, lifted_clip_one, coeffB, coeffJ, coeffT,
        taylorLength, Final50Price.physicalDegree,
        Nat.cast_add, Nat.cast_mul, Nat.cast_sub hb, Nat.cast_sub hj] <;>
      norm_num <;> ring
  · have h2 : 2 ≤ x.t := by omega
    refine ⟨?_,?_,?_⟩ <;>
      simp only [hornerB, hornerJ, hornerT, if_neg h,
        g, l, r, bentLift, lifted_clip h2, coeffB, coeffJ, coeffT,
        taylorLength, Final50Price.physicalDegree,
        Nat.cast_add, Nat.cast_mul, Nat.cast_sub hb, Nat.cast_sub hj] <;>
      norm_num <;> ring

end Final50SharedPrice
