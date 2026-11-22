import ProximityPrize.SubmissionLower.Final50SurfaceLinearFive

set_option maxHeartbeats 6000000
set_option maxRecDepth 16000

/-! Horner form of the five-slot tilted surface on the guarded chamber (b ≥ j+1, j ≥ 2, t ≥ 2).
Same value as `Final50Price.tiltedSurface`, proved below; only the kernel's evaluation cost changes. -/
namespace Compact54Tilted
open K1_13 (Shape)
open Final50Price (tiltedSurface bentGraph bentLift taylorLength)
open private signedFive signed_five_coeffs coeffB coeffJ coeffT
  from ProximityPrize.SubmissionLower.Final50SurfaceLinearFive

private def polynomial (b j t : ℤ) (q : Shape) : ℤ :=
  (j * (j * (t * (153942334528320) + 239466451709760) + t * (t * ((-461827003584960)) + (-1436796147406080)) + (-1163120715162240)) + t * (t * (t * (461827003584960) + 2155194221109120) + 3352526735946240) + 1778892616143360) * q.b +
  (b * (j * (t * (307884669056640) + 478932903419520) + t * (t * ((-461827003584960)) + (-1436796147406080)) + (-1163120715162240)) + j * (j * (t * ((-230913501792480)) + (-359199677564640)) + t * (t * (538798170849120) + 1744680816462720) + 1453900765809600) + t * (t * (t * ((-384855836320800)) + (-1898623150991040)) + (-3113059515379200)) + (-1744682354183040)) * q.j +
  (b * (j * (j * (153942334528320) + t * ((-923654007169920)) + (-1436796147406080)) + t * (t * (1385481010754880) + 4310388442218240) + 3352526735946240) + j * (j * (j * ((-76971167264160)) + t * (538798170849120) + 872340408231360) + t * (t * ((-1154567508962400)) + (-3797246301982080)) + (-3113059515379200)) + t * (t * (t * (692740505377440) + 3540675231864000) + 5986651810191360) + 3352526735946240) * q.t

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
  have hk : taylorLength-4 = 133481 := rfl
  have hl : taylorLength-3 = 133482 := rfl
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

/-! The same surface on the flat slice `t = 1` (b ≥ j+1, j ≥ 2): the lifts have constant top and height. -/
private def polynomial1 (b j : ℤ) (q : Shape) : ℤ :=
  (j * (j * (76971743905920) + (-136837523902080)) + 76971423557760) * q.b +
  (b * (j * (153943487811840) + (-136837523902080)) + j * (j * ((-115457615858880)) + 183875544879360) + (-94076138070720)) * q.j +
  (b * (j * (j * (102628287089280) + (-393409298807040)) + 359200510492800) + j * (j * (j * ((-51314143544640)) + 248018792948160) + (-376304904649920)) + 179600255246400) * q.t

def tiltedFast1 (p q : Shape) : ℕ :=
  (polynomial1 (↑(p.b-1 : ℕ)) (↑(p.j-2 : ℕ)) q).toNat

theorem tiltedFast1_eq (p q : Shape)
    (hb : p.j + 1 ≤ p.b) (hj : 2 ≤ p.j) (ht : p.t = 1) :
    tiltedFast1 p q = tiltedSurface p q := by
  rcases p with ⟨b,j,t⟩
  change j+1 ≤ b at hb
  change 2 ≤ j at hj
  change t = 1 at ht
  subst ht
  have hb₁ : 1 ≤ b := by omega
  have hGraph : bentGraph ⟨b,j,1⟩ = (⟨b,j+1,1+1⟩,1) := by
    simp only [bentGraph, max_eq_left hb]
  have hk : taylorLength-4 = 133481 := rfl
  have hl : taylorLength-3 = 133482 := rfl
  have hK : bentLift (taylorLength-4) ⟨b,j,1⟩ =
      (⟨1 + 133481 * (b - 1), 4 + 133481 * (j - 2), 133483⟩, 66741) := by
    simp only [bentLift, hk] <;> first | rfl | norm_num
  have hL : bentLift (taylorLength-3) ⟨b,j,1⟩ =
      (⟨1 + 133482 * (b - 1), 4 + 133482 * (j - 2), 133484⟩, 66742) := by
    simp only [bentLift, hl] <;> first | rfl | norm_num
  have hB : (b : ℤ) = (↑(b-1 : ℕ) : ℤ)+1 := by omega
  have hJ : (j : ℤ) = (↑(j-2 : ℕ) : ℤ)+2 := by omega
  unfold tiltedFast1
  change (polynomial1 _ _ q).toNat =
    (signedFive (⟨b,j,1⟩,0) (q,0) (bentGraph ⟨b,j,1⟩)
      (bentLift (taylorLength-4) ⟨b,j,1⟩) (bentLift (taylorLength-3) ⟨b,j,1⟩)).toNat
  apply congrArg Int.toNat
  rw [hGraph, hK, hL, signed_five_coeffs]
  simp only [coeffB, coeffJ, coeffT, polynomial1, Nat.cast_add,
    Nat.cast_mul, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, mul_zero, zero_mul, add_zero, zero_add]
  rw [hB, hJ]
  ring

end Compact54Tilted
