import ProximityPrize.SubmissionLower.Final50SurfaceLinearFive

set_option Elab.async false
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
  (j * (j * (t * (153979241797440) + 239523863088960) + t * (t * ((-461937725392320)) + (-1437140615374080)) + (-1163399570186880)) + t * (t * (t * (461937725392320) + 2155710923061120) + 3353330494824960) + 1779319100551680) * q.b +
  (b * (j * (t * (307958483594880) + 479047726177920) + t * (t * ((-461937725392320)) + (-1437140615374080)) + (-1163399570186880)) + j * (j * (t * ((-230968862696160)) + (-359285794633440)) + t * (t * (538927346291040) + 1745099098968960) + 1454249334575040) + t * (t * (t * ((-384948104493600)) + (-1899078340766400)) + (-3113805862786560)) + (-1745100636873600)) * q.j +
  (b * (j * (j * (153979241797440) + t * ((-923875450784640)) + (-1437140615374080)) + t * (t * (1385813176176960) + 4311421846122240) + 3353330494824960) + j * (j * (j * ((-76989620898720)) + t * (538927346291040) + 872549549484480) + t * (t * ((-1154844313480800)) + (-3798156681532800)) + (-3113805862786560)) + t * (t * (t * (692906588088480) + 3541524099238080) + 5988087093534720) + 3353330494824960) * q.t

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
  have hk : taylorLength-4 = 133497 := rfl
  have hl : taylorLength-3 = 133498 := rfl
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
  (j * (j * (76990197609600) + (-136870330350720)) + 76989877223040) * q.b +
  (b * (j * (153980395219200) + (-136870330350720)) + j * (j * ((-115485296414400)) + 183919628559360) + (-94098692544960)) * q.j +
  (b * (j * (j * (102652891943040) + (-393503617516800)) + 359286627661440) + j * (j * (j * ((-51326445971520)) + 248078254729920) + (-376395122589120)) + 179643313830720) * q.t

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
  have hk : taylorLength-4 = 133497 := rfl
  have hl : taylorLength-3 = 133498 := rfl
  have hK : bentLift (taylorLength-4) ⟨b,j,1⟩ =
      (⟨1 + 133497 * (b - 1), 4 + 133497 * (j - 2), 133499⟩, 66749) := by
    simp only [bentLift, hk] <;> first | rfl | norm_num
  have hL : bentLift (taylorLength-3) ⟨b,j,1⟩ =
      (⟨1 + 133498 * (b - 1), 4 + 133498 * (j - 2), 133500⟩, 66750) := by
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
