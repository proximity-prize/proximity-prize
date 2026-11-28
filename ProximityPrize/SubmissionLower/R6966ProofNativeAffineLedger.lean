import ProximityPrize.SubmissionLower.R6966ProofWordSurfacePrice

set_option Elab.async false

namespace Research6966.NativeAffineLedger
open WordSurfacePrice (side)
set_option maxHeartbeats 300000

/-- Turn a scaled word count into its integer fee and rounded-down regular price. -/
theorem floor {marks fee scale bill : ℕ} (pos : 0 < scale)
    (count : marks*scale ≤ fee*scale+bill) : marks ≤ fee+bill/scale := by
  have h : (marks-fee)*scale ≤ bill := by rw [Nat.sub_mul]; omega
  have q := (Nat.le_div_iff_mul_le pos).mpr h
  omega

theorem side_mono {n a d h H : ℕ} (hh : h ≤ H) : side n a d h ≤ side n a d H :=
  Nat.add_le_add_right (Nat.mul_le_mul_left _ hh) _

theorem side_one {n a d : ℕ} (gap : d < a) (an : a ≤ n) : side n a d 1 = n-d := by
  unfold side
  rw [Nat.mul_one]
  omega

theorem side_ratio {n a d h : ℕ} (gap : d < a) (an : a ≤ n) :
    side n a d h ≤ max 1 h*(n-d) := by
  have hm : 1 ≤ max 1 h := le_max_left _ _
  have h1 : a-d ≤ (a-d)*max 1 h := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (a-d) hm
  calc
    side n a d h ≤ side n a d (max 1 h) := side_mono (le_max_right _ _)
    _ ≤ (n-a)*max 1 h+(a-d)*max 1 h := Nat.add_le_add_left h1 _
    _ = max 1 h*(n-d) := by rw [← Nat.add_mul, show n-a+(a-d)=n-d by omega, Nat.mul_comm]

/-- The three-coordinate affine ledger accepts both the degree-six box
price and the degree-three common-total-degree price. -/
theorem three_floor {n a d marks fee c h₀ h₁ : ℕ} (gap : d < a) (an : a ≤ n)
    (count : marks*(a-d)^3 ≤ fee*(a-d)^3+c*side n a d 1*side n a d h₀*side n a d h₁) :
    marks ≤ fee+(c*max 1 h₀*max 1 h₁*(n-d)^3)/(a-d)^3 := by
  apply floor (pow_pos (by omega) 3)
  refine count.trans (Nat.add_le_add_left ?_ _)
  rw [side_one gap an]
  calc
    c*(n-d)*side n a d h₀*side n a d h₁ ≤
        c*(n-d)*(max 1 h₀*(n-d))*(max 1 h₁*(n-d)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (side_ratio gap an)) (side_ratio gap an)
    _ = _ := by ring



/-- The projected ledger keeps the individual side lengths. This variant
permits the width-zero padding used by the numerical ledger. -/
theorem projected_floor {n a d marks fee g v₀ v₁ h₀ h₁ : ℕ} (gap : d < a)
    (count : marks*(a-d)^2 ≤ fee*(a-d)^2+2*
      (g*side n a d h₀*side n a d h₁+v₀*side n a d 1*side n a d h₁+v₁*side n a d 1*side n a d h₀)) :
    marks ≤ fee+2*
      (g*side n a d (max 1 h₀)*side n a d (max 1 h₁)+
        v₀*side n a d 1*side n a d (max 1 h₁)+v₁*side n a d 1*side n a d (max 1 h₀))/(a-d)^2 := by
  apply floor (pow_pos (by omega) 2)
  have z : side n a d h₀ ≤ side n a d (max 1 h₀) := side_mono (le_max_right _ _)
  have o : side n a d h₁ ≤ side n a d (max 1 h₁) := side_mono (le_max_right _ _)
  exact count.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_left _ z) o) (Nat.mul_le_mul_left _ o))
    (Nat.mul_le_mul_left _ z))) _)

end Research6966.NativeAffineLedger
