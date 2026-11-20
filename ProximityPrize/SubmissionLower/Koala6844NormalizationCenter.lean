import ProximityPrize.SubmissionLower.Koala6844NormalizationNorm
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination


namespace ProximityPrize.SubmissionLower.Koala6844Normalization

open Polynomial

noncomputable section

variable {K I : Type*} [Field K]

def centerAffine (A : Fin 2 → Polynomial K) (g0 : K) : Fin 2 → Polynomial K :=
  ![specializeAffine A g0, A 1]

@[simp] theorem specialize_centerAffine (A : Fin 2 → Polynomial K) (g0 g : K) :
    specializeAffine (centerAffine A g0) g = specializeAffine A (g0 + g) := by
  simp only [specializeAffine, centerAffine, Matrix.cons_val_zero, Matrix.cons_val_one, map_add]
  ring

theorem center_affine_coprime {A : Fin 2 → Polynomial K} (g0 : K)
    (h : IsCoprime (A 0) (A 1)) : IsCoprime (centerAffine A g0 0) (centerAffine A g0 1) := by
  obtain ⟨s, t, hst⟩ := h
  refine ⟨s, t - C g0 * s, ?_⟩
  simp only [centerAffine, Matrix.cons_val_zero, Matrix.cons_val_one, specializeAffine]
  linear_combination hst

theorem specializeAffine_natDegree_le (A : Fin 2 → Polynomial K) (g : K) :
    (specializeAffine A g).natDegree ≤ affineDegree A :=
  (natDegree_add_le _ _).trans
    (max_le (le_max_left _ _) ((natDegree_C_mul_le _ _).trans (le_max_right _ _)))

theorem affine_degree_center {A : Fin 2 → Polynomial K} {g0 : K}
    (h : (specializeAffine A g0).natDegree = affineDegree A) :
    affineDegree (centerAffine A g0) = affineDegree A := by
  unfold affineDegree
  simp only [centerAffine, Matrix.cons_val_zero, Matrix.cons_val_one, h]
  exact max_eq_left (le_max_right _ _)

theorem center_left_equation (A C0 : Fin 2 → Polynomial K) (d0 : Polynomial K)
    (g0 g : K) (P0 P Q0 Q : Polynomial K)
    (h0 : specializeAffine A g0 * Q0 = d0 * P0 + specializeAffine C0 g0)
    (h : specializeAffine A (g0 + g) * Q = d0 * P + specializeAffine C0 (g0 + g)) :
    specializeAffine (centerAffine A g0) g * (Q - Q0) =
      d0 * (P - P0) + C g * (C0 1 - A 1 * Q0) := by
  rw [specialize_centerAffine]
  simp only [specializeAffine, map_add] at h0 h ⊢
  linear_combination h - h0

theorem center_right_equation (σ : K →+* K) (A D : Fin 2 → Polynomial K)
    (d1 : Polynomial K) (g0 g : K) (P0 P Q0 Q : Polynomial K)
    (h0 : (specializeAffine A g0).map σ * Q0 =
      d1 * P0.map σ - specializeAffine D (σ g0))
    (h : (specializeAffine A (g0 + g)).map σ * Q =
      d1 * P.map σ - specializeAffine D (σ (g0 + g))) :
    (specializeAffine (centerAffine A g0) g).map σ * (Q - Q0) =
      d1 * (P - P0).map σ + C (σ g) * (-D 1 - (A 1).map σ * Q0) := by
  rw [specialize_centerAffine]
  simp only [specializeAffine, map_add, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_sub] at h0 h ⊢
  linear_combination h - h0

def centerReceived (received : Fin 2 → I → K) (x : I → K) (g0 : K) (P0 : Polynomial K) :
    Fin 2 → I → K :=
  ![fun i => received 0 i + g0 * received 1 i - P0.eval (x i), received 1]

theorem center_agrees_at (received : Fin 2 → I → K) (x : I → K) (i : I)
    (g0 g : K) (P0 P : Polynomial K)
    (h : P.eval (x i) = received 0 i + (g0 + g) * received 1 i) :
    (P - P0).eval (x i) =
      centerReceived received x g0 P0 0 i + g * centerReceived received x g0 P0 1 i := by
  simp only [eval_sub, h, centerReceived, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem center_fixed_word (received : Fin 2 → I → K) (x : I → K) (i : I)
    (d0 : Polynomial K) (A C0 : Fin 2 → Polynomial K) (g0 u : K) (P0 Q0 : Polynomial K)
    (hw : ∀ j,
      d0.eval (x i) * received j i + (C0 j).eval (x i) = u * (A j).eval (x i))
    (h0 : specializeAffine A g0 * Q0 = d0 * P0 + specializeAffine C0 g0) :
    ∀ j : Fin 2,
      d0.eval (x i) * centerReceived received x g0 P0 j i +
        (j.val : K) * (C0 1 - A 1 * Q0).eval (x i) =
      (u - Q0.eval (x i)) * (centerAffine A g0 j).eval (x i) := by
  rw [Fin.forall_fin_two]
  have h := congrArg (eval (x i)) h0
  have hW0 := hw 0
  have hW1 := hw 1
  simp only [specializeAffine, eval_add, eval_mul, eval_C] at h
  constructor
  · simp only [Fin.val_zero, Nat.cast_zero, centerReceived, centerAffine,
      Matrix.cons_val_zero, zero_mul, add_zero, specializeAffine, eval_add, eval_mul, eval_C]
    linear_combination hW0 + g0 * hW1 + h
  · simp only [Fin.val_one, Nat.cast_one, centerReceived, centerAffine,
      Matrix.cons_val_one, Matrix.cons_val_zero, one_mul, eval_sub, eval_mul]
    linear_combination hW1

end

end ProximityPrize.SubmissionLower.Koala6844Normalization
