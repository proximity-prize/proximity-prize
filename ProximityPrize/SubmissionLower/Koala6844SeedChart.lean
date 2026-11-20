import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import ProximityPrize.SubmissionLower.Koala6844NormalizationData


namespace ProximityPrize.SubmissionLower.Koala6844SeedChart

open Polynomial
open Koala6844Normalization
open scoped Classical

noncomputable section

set_option autoImplicit false

variable {K : Type} [Field K]

def forward (ℓ g : K) : K := g / (1 - ℓ * g)
def backward (ℓ t : K) : K := t / (1 + ℓ * t)
def scale (ℓ t : K) : K := 1 + ℓ * t

theorem scale_forward (ℓ g : K) (h : 1 - ℓ * g ≠ 0) :
    scale ℓ (forward ℓ g) = (1 - ℓ * g)⁻¹ := by
  unfold scale forward
  field_simp [h]
  ring

theorem scale_forward_ne_zero (ℓ g : K) (h : 1 - ℓ * g ≠ 0) :
    scale ℓ (forward ℓ g) ≠ 0 := by
  rw [scale_forward ℓ g h]
  exact inv_ne_zero h

theorem backward_forward (ℓ g : K) (h : 1 - ℓ * g ≠ 0) :
    backward ℓ (forward ℓ g) = g := by
  change forward ℓ g / scale ℓ (forward ℓ g) = g
  rw [scale_forward ℓ g h, forward, div_inv_eq_mul, div_mul_cancel₀ _ h]

theorem scale_mul_backward (ℓ t : K) (h : scale ℓ t ≠ 0) :
    scale ℓ t * backward ℓ t = t := by
  unfold backward
  exact mul_div_cancel₀ t h

def shear (A : Fin 2 → Polynomial K) (ℓ : K) : Fin 2 → Polynomial K :=
  fun j => if j = 0 then A 0 else A 1 + C ℓ * A 0

@[simp] theorem shear_zero (A : Fin 2 → Polynomial K) (ℓ : K) : shear A ℓ 0 = A 0 := by
  simp [shear]

@[simp] theorem shear_one (A : Fin 2 → Polynomial K) (ℓ : K) :
    shear A ℓ 1 = A 1 + C ℓ * A 0 := by
  simp [shear]

theorem specialize_shear (A : Fin 2 → Polynomial K) (ℓ t : K) (ht : scale ℓ t ≠ 0) :
    specializeAffine (shear A ℓ) t =
      C (scale ℓ t) * specializeAffine A (backward ℓ t) := by
  have ht' : scale ℓ t * backward ℓ t = t := scale_mul_backward ℓ t ht
  have hcoeff : C (scale ℓ t) * C (backward ℓ t) = (C t : Polynomial K) := by
    rw [← map_mul, ht']
  simp only [specializeAffine, shear_zero, shear_one, scale, map_add, map_mul, map_one] at *
  linear_combination -hcoeff * A 1

theorem exist_admissible_shear {I : Type} [DecidableEq I] [Fintype K]
    (x : I → K) (nodes : Finset I) (A : Fin 2 → Polynomial K)
    (hA : ∀ i ∈ nodes, (A 0).eval (x i) ≠ 0)
    (hsize : nodes.card < Fintype.card K) :
    ∃ ℓ, ∀ i ∈ nodes, (shear A ℓ 1).eval (x i) ≠ 0 := by
  classical
  let forbidden := nodes.image fun i => -(A 1).eval (x i) / (A 0).eval (x i)
  have hlt : forbidden.card < Fintype.card K :=
    (Finset.card_image_le (s := nodes)).trans_lt hsize
  have hExists : ∃ ℓ : K, ℓ ∉ forbidden := by
    by_contra! hall
    have heq : forbidden = Finset.univ := Finset.eq_univ_of_forall hall
    exact (lt_irrefl _) (by simpa only [heq, Finset.card_univ] using hlt)
  obtain ⟨ℓ, hℓ⟩ := hExists
  refine ⟨ℓ, ?_⟩
  intro i hi hz
  apply hℓ
  refine Finset.mem_image.mpr ⟨i, hi, ?_⟩
  symm
  apply (eq_div_iff (hA i hi)).mpr
  simp only [shear_one, eval_add, eval_mul, eval_C] at hz
  linear_combination hz

theorem affineDegree_shear (A : Fin 2 → Polynomial K) (ℓ : K) :
    affineDegree (shear A ℓ) = affineDegree A := by
  unfold affineDegree
  rw [shear_zero, shear_one]
  apply le_antisymm
  · apply max_le (le_max_left _ _)
    exact (natDegree_add_le _ _).trans <|
      max_le (le_max_right _ _) ((natDegree_C_mul_le _ _).trans (le_max_left _ _))
  · apply max_le (le_max_left _ _)
    have hEq : A 1 = (A 1 + C ℓ * A 0) - C ℓ * A 0 := by ring
    conv_lhs => rw [hEq]
    exact (natDegree_sub_le _ _).trans <|
      max_le (le_max_right _ _) ((natDegree_C_mul_le _ _).trans (le_max_left _ _))

theorem card_le_chart_add_one [DecidableEq K] (ℓ : K) (seeds : Finset K) :
    seeds.card ≤ ((seeds.filter fun g => 1 - ℓ * g ≠ 0).image (forward ℓ)).card + 1 := by
  classical
  let good := seeds.filter fun g => 1 - ℓ * g ≠ 0
  let excluded := seeds.filter fun g => 1 - ℓ * g = 0
  have hinj : Set.InjOn (forward ℓ) (↑good : Set K) := by
    intro a ha b hb hab
    have hna := (Finset.mem_filter.mp ha).2
    have hnb := (Finset.mem_filter.mp hb).2
    calc
      a = backward ℓ (forward ℓ a) := (backward_forward ℓ a hna).symm
      _ = backward ℓ (forward ℓ b) := congrArg (backward ℓ) hab
      _ = b := backward_forward ℓ b hnb
  have hexExcluded : excluded.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have h₁ : ℓ * a = 1 := by
      have h := sub_eq_zero.mp (Finset.mem_filter.mp ha).2
      exact h.symm
    have h₂ : ℓ * b = 1 := by
      have h := sub_eq_zero.mp (Finset.mem_filter.mp hb).2
      exact h.symm
    have hℓ : ℓ ≠ 0 := by
      intro h
      simp [h] at h₁
    exact mul_left_cancel₀ hℓ (h₁.trans h₂.symm)
  have hcard : good.card + excluded.card = seeds.card := by
    simpa only [good, excluded, not_not] using
      Finset.card_filter_add_card_filter_not (s := seeds) (p := fun g => 1 - ℓ * g ≠ 0)
  rw [Finset.card_image_of_injOn hinj]
  omega

end

end ProximityPrize.SubmissionLower.Koala6844SeedChart
