import ProximityPrize.SubmissionLower.Koala6831IntrinsicGauss
import Mathlib.Algebra.Polynomial.Eval.Degree


namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open scoped Polynomial BigOperators

noncomputable section

variable {E Γ₀ : Type*} [CommRing E] [LinearOrderedCommGroupWithZero Γ₀]

theorem valuation_mul_root_le (v : Valuation E Γ₀) (a x : E) (A : ℕ → E)
    (d : ℕ) (B : Γ₀) (ha : v a ≤ B) (hlead : v a ≤ v (A d))
    (hlower : ∀ i < d, v (A i) ≤ B)
    (hroot : ∑ i ∈ Finset.range (d + 1), A i * x ^ i = 0) :
    v (a * x) ≤ B := by
  by_contra! hbig
  rw [map_mul] at hbig
  have hx : 1 < v x := by
    by_contra! h
    have hval : v a * v x ≤ v a * 1 := mul_le_mul_of_nonneg_left h zero_le
    exact (not_le_of_gt hbig) ((by simpa only [mul_one] using hval : v a * v x ≤ v a).trans ha)
  have hxp : 0 < v x := zero_lt_one.trans hx
  have hap : 0 < v a := by
    by_contra! h
    have hz : v a = 0 := le_antisymm h zero_le
    rw [hz, zero_mul] at hbig
    exact (not_lt_of_ge zero_le) hbig
  let f := fun i ↦ A i * x ^ i
  let s := Finset.range (d + 1)
  have hd : d ∈ s := Finset.mem_range.mpr (Nat.lt_succ_self _)
  have hsmaller : ∀ i ∈ s \ {d}, v (f i) < v (f d) := by
    intro i hi
    obtain ⟨hm, hne⟩ := Finset.mem_sdiff.mp hi
    have hiD : i < d := lt_of_le_of_ne (Nat.le_of_lt_succ (Finset.mem_range.mp hm))
      (by simpa only [Finset.mem_singleton] using hne)
    simp only [f, map_mul, map_pow]
    calc
      v (A i) * v x ^ i ≤ B * v x ^ i :=
        mul_le_mul_of_nonneg_right (hlower i hiD) zero_le
      _ < (v a * v x) * v x ^ i := mul_lt_mul_of_pos_right hbig (pow_pos hxp _)
      _ = v a * v x ^ (i + 1) := by rw [pow_succ, mul_assoc, mul_comm (v x) _]
      _ ≤ v (A d) * v x ^ d :=
        mul_le_mul hlead (pow_le_pow_right₀ hx.le hiD) zero_le zero_le
  have h := v.map_sum_eq_of_lt hd hsmaller
  change v (∑ i ∈ Finset.range (d + 1), A i * x ^ i) = v (A d * x ^ d) at h
  rw [hroot, map_zero, map_mul, map_pow] at h
  exact (mul_pos (hap.trans_le hlead) (pow_pos hxp _)).ne' h.symm

theorem cleared_coefficients_le_of_root (v : Valuation E Γ₀) (A : ℕ → E[X])
    (d n : ℕ) (P : E[X]) (B : Γ₀)
    (hcoeff : ∀ i ≤ d, ∀ j, v ((A i).coeff j) ≤ B)
    (hroot : ∑ i ∈ Finset.range (d + 1), A i * P ^ i = 0) :
    ∀ j, v ((Polynomial.C ((A d).coeff n) * P).coeff j) ≤ B := by
  let a := (A d).coeff n
  have h := valuation_mul_root_le (gaussValuation v) (Polynomial.C a) P A d B
    (by simpa only [gaussValuation_apply, gaussMaximum_C] using hcoeff d le_rfl n)
    (by simpa only [gaussValuation_apply, gaussMaximum_C] using coefficient_le_gaussMaximum v (A d) n)
    (fun i hi ↦ (gaussMaximum_le_iff v (A i) B).mpr (hcoeff i (Nat.le_of_lt hi)))
    hroot
  exact (gaussMaximum_le_iff _ _ _).mp h

private theorem evaluation_le_of_coefficients_le (v : Valuation E Γ₀) (P : E[X])
    (x : E) (B : Γ₀) (hx : v x ≤ 1) (hcoeff : ∀ i, v (P.coeff i) ≤ B) :
    v (P.eval x) ≤ B := by
  rw [Polynomial.eval_eq_sum_range]
  apply v.map_sum_le
  intro i _
  rw [map_mul, map_pow]
  exact (mul_le_mul (hcoeff i) (pow_le_one₀ zero_le hx) zero_le zero_le).trans_eq (mul_one _)

theorem normalized_value_le_of_root (v : Valuation E Γ₀) (A : ℕ → E[X])
    (d n t z : ℕ) (P : E[X]) (x u₀ u₁ z₀ z₁ : E)
    (hroot : ∑ i ∈ Finset.range (d + 1), A i * P ^ i = 0)
    (hcoeff : ∀ i ≤ d, ∀ j, v ((A i).coeff j) ≤ (max (v z₀) 1)^t * (max (v z₁) 1)^z)
    (hx : v x ≤ 1) (hu₀ : v u₀ ≤ 1) (hu₁ : v u₁ ≤ 1) :
    v (((A d).coeff n) * (P.eval x - u₀ - u₁ * z₀)) ≤
      (max (v z₀) 1)^(t + 1) * (max (v z₁) 1)^z := by
  let a := (A d).coeff n
  let M₀ := max (v z₀) 1
  let M₁ := max (v z₁) 1
  let B := M₀ ^ t * M₁ ^ z
  change v (a * (P.eval x - u₀ - u₁ * z₀)) ≤ M₀ ^ (t + 1) * M₁ ^ z
  have hbound : B ≤ B * M₀ := by
    have h₀ : (1 : Γ₀) ≤ M₀ := le_max_right _ _
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h₀ (zero_le : 0 ≤ B)
  have hP : v (a * P.eval x) ≤ B := by
    have h := evaluation_le_of_coefficients_le v (Polynomial.C a * P) x B hx
      (cleared_coefficients_le_of_root v A d n P B hcoeff hroot)
    simpa only [Polynomial.eval_mul, Polynomial.eval_C] using h
  have ha : v a ≤ B := hcoeff d le_rfl n
  have hu0 : v (a * u₀) ≤ B := by
    rw [map_mul]
    exact (mul_le_mul ha hu₀ zero_le zero_le).trans_eq (mul_one _)
  have hu1 : v (a * (u₁ * z₀)) ≤ B * M₀ := by
    simp only [map_mul]
    have hu : v u₁ * v z₀ ≤ M₀ :=
      (mul_le_mul hu₁ (le_max_left _ _) zero_le zero_le).trans_eq (one_mul _)
    exact mul_le_mul ha hu zero_le zero_le
  calc
    v (a * (P.eval x - u₀ - u₁ * z₀)) =
        v ((a * P.eval x - a * u₀) - a * (u₁ * z₀)) := by rw [mul_sub, mul_sub]
    _ ≤ B * M₀ := v.map_sub_le (v.map_sub_le (hP.trans hbound) (hu0.trans hbound)) hu1
    _ = M₀ ^ (t + 1) * M₁ ^ z := by dsimp only [B]; rw [pow_succ]; ac_rfl

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic
