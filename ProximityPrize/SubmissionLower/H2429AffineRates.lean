import Mathlib.Tactic

set_option autoImplicit false
set_option Elab.async false

namespace H2429AffineRates

def ratio (s : ℕ) : ℚ := (262144 - (s : ℚ)) / (179876 - (s : ℚ))

def order (s : ℕ) : ℕ := max 1 (128644 - s)

theorem ratio_le_three {s : ℕ} (hs : s ≤ 133500) : ratio s ≤ 3 := by
  have h : (s : ℚ) ≤ 133500 := by exact_mod_cast hs
  unfold ratio
  exact (div_le_iff₀ (by linarith)).mpr (by linarith)

theorem affine {s : ℕ} (hs : s ≤ 133500) {m c : ℚ}
    (hsize : m ≤ 179876*c) (hpos : 0 ≤ m - c*s) :
    ratio s * (m - c*s) ≤ ratio 0 * m := by
  have hs0 : (0 : ℚ) ≤ s := Nat.cast_nonneg s
  have hsn : (s : ℚ) ≤ 133500 := by exact_mod_cast hs
  have hA : 0 < 179876 - (s : ℚ) := by linarith
  have h : (m-c*s)/(179876-s) ≤ m/179876 := by
    apply (div_le_div_iff₀ hA (by norm_num : (0 : ℚ)<179876)).mpr
    have hh := mul_nonneg (sub_nonneg.mpr hsize) hs0
    nlinarith only [hh]
  calc
    _ = (262144-(s:ℚ))*((m-c*s)/(179876-s)) := by unfold ratio; ring
    _ ≤ 262144*((m-c*s)/(179876-s)) :=
      mul_le_mul_of_nonneg_right (by linarith) (div_nonneg hpos hA.le)
    _ ≤ 262144*(m/179876) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by simp [ratio]; ring

theorem curve {s : ℕ} (hs : s ≤ 133500) {q : ℚ} (hq : 1 ≤ q) :
    ratio s * ((2*(order s : ℚ)-1)*q+1) ≤ ratio 0 * (257287*q+1) := by
  by_cases h : s < 128644
  · have ho : order s = 128644-s :=
      max_eq_right (by omega)
    have ho' : (order s : ℚ) = 128644-(s:ℚ) := by
      rw [ho,Nat.cast_sub h.le]
      norm_num
    have hs' : (s : ℚ) < 128644 := by exact_mod_cast h
    have hm : 257287*q + 1 ≤ 179876 * (2*q) := by linarith
    have hp : 0 ≤ 257287*q+1-(2*q)*s := by
      rw [show 257287*q+1-(2*q)*s=(2*(128644-(s:ℚ))-1)*q+1 by ring, ← ho']
      have hn : (1 : ℚ) ≤ (order s : ℚ) := by
        exact_mod_cast (le_max_left 1 (128644-s))
      exact add_nonneg (mul_nonneg (by linarith) (by linarith)) zero_le_one
    have hform : (2*(order s : ℚ)-1)*q+1 = 257287*q+1-(2*q)*s := by
      rw [ho']; ring
    rw [hform]
    exact affine hs hm hp
  · have ho : order s = 1 := by
      unfold order
      rw [Nat.sub_eq_zero_of_le (by omega), max_eq_left (by decide)]
    rw [ho]
    simp only [Nat.cast_one, mul_one, show (2 : ℚ)-1=1 by norm_num, one_mul]
    apply (mul_le_mul_of_nonneg_right (ratio_le_three hs) (by linarith : 0 ≤ q+1)).trans
    unfold ratio
    norm_num
    linarith

#print axioms affine
#print axioms curve
end H2429AffineRates
