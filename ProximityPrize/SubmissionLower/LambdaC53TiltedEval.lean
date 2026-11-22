import ProximityPrize.SubmissionLower.Final50SurfaceLinearFive

set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 16000

namespace LambdaC53Tilted
open K1_13 (Shape)
open Final50Price (tiltedSurface bentGraph bentLift taylorLength)
open Final50SharedPrice (signedFive signed_five_coeffs coeffB coeffJ coeffT)

private def polynomial (b j t : ℤ) (q : Shape) : ℤ :=
  (j * (j * (t * (153889288079040) + 239383934907840) + t * (t * ((-461667864237120)) + (-1436301047036160)) + (-1162719919620480)) + t * (t * (t * (461667864237120) + 2154451570554240) + 3351371501337600) + 1778279634362880) * q.b +
  (b * (j * (t * (307778576158080) + 478767869815680) + t * (t * ((-461667864237120)) + (-1436301047036160)) + (-1162719919620480)) + j * (j * (t * ((-230833932118560)) + (-359075902361760)) + t * (t * (538612508276640) + 1744079623194240) + 1453399771404480) + t * (t * (t * ((-384723220197600)) + (-1897968911273280)) + (-3111986797704960)) + (-1744081160649600)) * q.j +
  (b * (j * (j * (153889288079040) + t * ((-923335728474240)) + (-1436301047036160)) + t * (t * (1385003592711360) + 4308903141108480) + 3351371501337600) + j * (j * (j * ((-76944644039520)) + t * (538612508276640) + 872039811597120) + t * (t * ((-1154169660592800)) + (-3795937822546560)) + (-3111986797704960)) + t * (t * (t * (692501796355680) + 3539455163265600) + 5984588891777280) + 3351371501337600) * q.t

def tiltedFast (p q : Shape) : ℕ :=
  (polynomial (↑(p.b-1 : ℕ)) (↑(p.j-2 : ℕ)) (↑(p.t-2 : ℕ)) q).toNat

theorem tiltedFast_eq (p q : Shape)
    (hb : p.j + 1 ≤ p.b) (hj : 2 ≤ p.j) (ht : 2 ≤ p.t) :
    tiltedFast p q = tiltedSurface p q := by
  rcases p with ⟨b,j,t⟩
  change j+1 ≤ b at hb
  change 2 ≤ j at hj
  change 2 ≤ t at ht
  have hb₁ : 1 ≤ b := by omega
  have hGraph : bentGraph ⟨b,j,t⟩ = (⟨b,j+1,t+1⟩,1) := by
    simp only [bentGraph, max_eq_left hb]
  have hMin (k : ℕ) : min (1+k) ((2+k*t)/2) = 1+k := by
    apply min_eq_left
    have hkt := Nat.mul_le_mul_left k ht
    omega
  have hk : taylorLength-4 = 133458 := rfl
  have hl : taylorLength-3 = 133459 := rfl
  have hB : (b : ℤ) = (↑(b-1 : ℕ) : ℤ)+1 := by omega
  have hJ : (j : ℤ) = (↑(j-2 : ℕ) : ℤ)+2 := by omega
  have hT : (t : ℤ) = (↑(t-2 : ℕ) : ℤ)+2 := by omega
  unfold tiltedFast
  change (polynomial _ _ _ q).toNat =
    (signedFive (⟨b,j,t⟩,0) (q,0) (bentGraph ⟨b,j,t⟩)
      (bentLift (taylorLength-4) ⟨b,j,t⟩) (bentLift (taylorLength-3) ⟨b,j,t⟩)).toNat
  apply congrArg Int.toNat
  rw [hGraph, signed_five_coeffs]
  simp only [bentLift, hk, hl, hMin, coeffB, coeffJ, coeffT, polynomial, Nat.cast_add,
    Nat.cast_mul, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, mul_zero, zero_mul, add_zero, zero_add]
  rw [hB, hJ, hT]
  ring

end LambdaC53Tilted
