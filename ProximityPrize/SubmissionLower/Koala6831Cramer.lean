import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.Ring

namespace ProximityPrize.SubmissionLower.Koala6831Cramer

open Polynomial
open scoped BigOperators Classical Matrix Polynomial

variable {K ι : Type*} [Field K]

theorem equation_of_node_agreement (domain : ι ↪ K) (nodes : Finset ι)
    (denominator selected numerator₀ numerator₁ : K[X]) (g : K) (w deg : ℕ)
    (hden : denominator.natDegree ≤ deg) (hsel : selected.natDegree ≤ w)
    (hnum₀ : numerator₀.natDegree ≤ w + deg) (hnum₁ : numerator₁.natDegree ≤ w + deg)
    (hcard : w + deg < nodes.card)
    (heval : ∀ i ∈ nodes, denominator.eval (domain i) * selected.eval (domain i) =
      numerator₀.eval (domain i) + g * numerator₁.eval (domain i)) :
    denominator * selected = numerator₀ + C g * numerator₁ := by
  classical
  let difference := denominator * selected - (numerator₀ + C g * numerator₁)
  have hdegree : difference.natDegree ≤ w + deg := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · simpa only [Nat.add_comm deg w] using natDegree_mul_le_of_le hden hsel
    · exact (natDegree_add_le _ _).trans
        (max_le hnum₀ ((natDegree_C_mul_le _ _).trans hnum₁))
  suffices difference = 0 from sub_eq_zero.mp this
  by_contra hnonzero
  have hroots : (nodes.image domain).card ≤ difference.natDegree := by
    apply card_le_degree_of_subset_roots
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    apply (mem_roots hnonzero).mpr
    simpa only [IsRoot, difference, eval_sub, eval_mul, eval_add, eval_C, sub_eq_zero] using
      heval i hi
  rw [Finset.card_image_of_injective _ domain.injective] at hroots
  exact (not_le_of_gt hcard) (hroots.trans hdegree)

theorem polynomial_pencil_of_common_denominator [DecidableEq K]
    (seeds : Finset K) (selected : K → K[X]) (denominator numerator₀ numerator₁ : K[X])
    (hden : denominator ≠ 0) (hsize : 1 < seeds.card) (w : ℕ)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hrelation : ∀ g ∈ seeds, denominator * selected g = numerator₀ + C g * numerator₁) :
    ∃ endpoint₀ endpoint₁ : K[X], endpoint₀.natDegree ≤ w ∧ endpoint₁.natDegree ≤ w ∧
      ∀ g ∈ seeds, selected g = endpoint₀ + C g * endpoint₁ := by
  obtain ⟨g, hg, h, hh, hne⟩ := Finset.one_lt_card.mp hsize
  let inverseDifference := C ((h - g)⁻¹)
  let endpoint₁ := inverseDifference * (selected h - selected g)
  let endpoint₀ := selected g - C g * endpoint₁
  have hdeg₁ : endpoint₁.natDegree ≤ w :=
    (natDegree_C_mul_le _ _).trans ((natDegree_sub_le _ _).trans
      (max_le (hdegree h hh) (hdegree g hg)))
  have hdeg₀ : endpoint₀.natDegree ≤ w := (natDegree_sub_le _ _).trans
    (max_le (hdegree g hg) ((natDegree_C_mul_le _ _).trans hdeg₁))
  have hcoeff : inverseDifference * (C h - C g) = 1 := by
    dsimp only [inverseDifference]
    rw [← map_sub, ← map_mul, inv_mul_cancel₀ (sub_ne_zero.mpr hne.symm), map_one]
  have hendpoint₁ : denominator * endpoint₁ = numerator₁ := by
    calc
      denominator * endpoint₁ =
          inverseDifference * (denominator * selected h - denominator * selected g) := by
        dsimp only [endpoint₁]
        ring
      _ = (inverseDifference * (C h - C g)) * numerator₁ := by
        rw [hrelation h hh, hrelation g hg]
        ring
      _ = numerator₁ := by rw [hcoeff, one_mul]
  have hendpoint₀ : denominator * endpoint₀ = numerator₀ := by
    calc
      denominator * endpoint₀ = denominator * selected g - C g * (denominator * endpoint₁) := by
        dsimp only [endpoint₀]
        ring
      _ = numerator₀ := by rw [hrelation g hg, hendpoint₁, add_sub_cancel_right]
  refine ⟨endpoint₀, endpoint₁, hdeg₀, hdeg₁, ?_⟩
  intro t ht
  apply mul_left_cancel₀ hden
  rw [hrelation t ht, mul_add, show denominator * (C t * endpoint₁) =
    C t * (denominator * endpoint₁) by ring, hendpoint₀, hendpoint₁]

theorem card_le_of_common_denominator [DecidableEq K]
    (seeds : Finset K) (selected : K → K[X]) (denominator numerator₀ numerator₁ : K[X])
    (hden : denominator ≠ 0) (w e : ℕ)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hrelation : ∀ g ∈ seeds, denominator * selected g = numerator₀ + C g * numerator₁)
    (hno : ∀ P₀ P₁ : K[X], P₀.natDegree ≤ w → P₁.natDegree ≤ w →
      (seeds.filter (fun γ ↦ selected γ = P₀ + C γ * P₁)).card ≤ e + 1) :
    seeds.card ≤ e + 1 := by
  classical
  by_cases hsmall : seeds.card ≤ 1
  · exact hsmall.trans (Nat.succ_le_succ (Nat.zero_le e))
  obtain ⟨P₀, P₁, h₀, h₁, hp⟩ := polynomial_pencil_of_common_denominator
    seeds selected denominator numerator₀ numerator₁ hden (lt_of_not_ge hsmall) w hdegree hrelation
  have hfilter : (seeds.filter (fun γ ↦ selected γ = P₀ + C γ * P₁)) = seeds := by
    ext g
    exact Finset.mem_filter.trans ⟨fun h ↦ h.1, fun hg ↦ ⟨hg, hp g hg⟩⟩
  simpa only [hfilter] using hno P₀ P₁ h₀ h₁

theorem det_natDegree_le_of_column_bounds {m : ℕ} (M : Matrix (Fin m) (Fin m) K[X])
    (bound : Fin m → ℕ) (hbound : ∀ i j, (M i j).natDegree ≤ bound j) :
    M.det.natDegree ≤ ∑ j, bound j := by
  rw [Matrix.det_apply']
  apply natDegree_sum_le_of_forall_le
  intro σ _
  have hprod : (∏ j, M (σ j) j).natDegree ≤ ∑ j, bound j :=
    (natDegree_prod_le (s := Finset.univ) (f := fun j ↦ M (σ j) j)).trans
      (Finset.sum_le_sum fun j _ ↦ hbound (σ j) j)
  have hsign : (((Equiv.Perm.sign σ : ℤ) : K[X])).natDegree ≤ 0 := by simp
  simpa only [Nat.zero_add] using natDegree_mul_le_of_le hsign hprod

theorem cramer_natDegree_le {m : ℕ} (M : Matrix (Fin m) (Fin m) K[X])
    (rhs : Fin m → K[X]) (col : Fin m) (w δ : ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ δ) (hrhs : ∀ i, (rhs i).natDegree ≤ w + δ) :
    ((M.updateCol col rhs).det).natDegree ≤ w + m * δ := by
  let bounds : Fin m → ℕ := fun j ↦ δ + if j = col then w else 0
  have hdet := det_natDegree_le_of_column_bounds (M.updateCol col rhs) bounds (by
    intro i j
    by_cases h : j = col
    · subst j
      simpa [Matrix.updateCol_apply, bounds, Nat.add_comm] using hrhs i
    · simpa [Matrix.updateCol_apply, bounds, h] using hM i j)
  simpa [bounds, Finset.sum_add_distrib, Nat.add_comm] using hdet

theorem eval_cramer_identity {m : ℕ} (M : Matrix (Fin m) (Fin m) K[X])
    (rhs : Fin m → K[X]) (x : K) (values : Fin m → K) (col : Fin m)
    (hrow : (evalRingHom x).mapMatrix M *ᵥ values = fun i ↦ (rhs i).eval x) :
    M.det.eval x * values col = ((M.updateCol col rhs).det).eval x := by
  let f := evalRingHom x
  let A := f.mapMatrix M
  have hmap : f.mapMatrix (M.updateCol col rhs) = A.updateCol col (fun i ↦ f (rhs i)) := by
    exact Matrix.map_updateCol (f := f) (M := M) (j := col) (c := rhs)
  have hrow' : A *ᵥ values = fun i ↦ f (rhs i) := hrow
  have hcramer : A.cramer (fun i ↦ f (rhs i)) = A.det • values := by
    rw [Matrix.cramer_eq_adjugate_mulVec, ← hrow', Matrix.mulVec_mulVec, Matrix.adjugate_mul,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  change f M.det * values col = f ((M.updateCol col rhs).det)
  rw [f.map_det, f.map_det, hmap, ← Matrix.cramer_apply, hcramer]
  rfl

theorem augmented_minor_eq_zero (domain : ι ↪ K) (nodes : Finset ι)
    (M : Matrix (Fin 4) (Fin 4) K[X]) (rhs : Fin 4 → K[X]) (values : ι → Fin 4 → K)
    (w δ : ℕ) (col : Fin 4) (hdet : M.det = 0)
    (hM : ∀ i j, (M i j).natDegree ≤ δ) (hrhs : ∀ i, (rhs i).natDegree ≤ w + δ)
    (hcard : w + 4 * δ < nodes.card)
    (hrow : ∀ i ∈ nodes,
      (evalRingHom (domain i)).mapMatrix M *ᵥ values i = fun j ↦ (rhs j).eval (domain i)) :
    (M.updateCol col rhs).det = 0 := by
  classical
  by_contra hnonzero
  have hroots : (nodes.image domain).card ≤ ((M.updateCol col rhs).det).natDegree := by
    apply card_le_degree_of_subset_roots
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    apply (mem_roots hnonzero).mpr
    simpa only [IsRoot, hdet, eval_zero, zero_mul] using
      (eval_cramer_identity M rhs (domain i) (values i) col (hrow i hi)).symm
  rw [Finset.card_image_of_injective _ domain.injective] at hroots
  exact (not_le_of_gt hcard) (hroots.trans (cramer_natDegree_le M rhs col w δ hM hrhs))

theorem card_le_of_rank_four [DecidableEq K] (domain : ι ↪ K)
    (seeds : Finset K) (agreement : K → Finset ι) (selected : K → K[X])
    (M : Matrix (Fin 4) (Fin 4) K[X]) (rhs : Fin 4 → K[X]) (values : ι → Fin 4 → K)
    (w δ e : ℕ) (hdet : M.det ≠ 0) (hM : ∀ i j, (M i j).natDegree ≤ δ)
    (hrhs : ∀ i, (rhs i).natDegree ≤ w + δ)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hagree : ∀ g ∈ seeds, w + 4 * δ < (agreement g).card)
    (hrow : ∀ g ∈ seeds, ∀ i ∈ agreement g,
      (evalRingHom (domain i)).mapMatrix M *ᵥ values i = fun j ↦ (rhs j).eval (domain i))
    (hfit : ∀ g ∈ seeds, ∀ i ∈ agreement g,
      (selected g).eval (domain i) = values i 0 + g * values i 1)
    (hno : ∀ P₀ P₁ : K[X], P₀.natDegree ≤ w → P₁.natDegree ≤ w →
      (seeds.filter (fun γ ↦ selected γ = P₀ + C γ * P₁)).card ≤ e + 1) :
    seeds.card ≤ e + 1 := by
  let numerator₀ := (M.updateCol 0 rhs).det
  let numerator₁ := (M.updateCol 1 rhs).det
  apply card_le_of_common_denominator seeds selected M.det numerator₀ numerator₁ hdet w e hdegree
    _ hno
  intro g hg
  refine equation_of_node_agreement domain (agreement g) M.det (selected g) numerator₀ numerator₁
    g w (4 * δ) ?_ (hdegree g hg) (cramer_natDegree_le M rhs 0 w δ hM hrhs)
    (cramer_natDegree_le M rhs 1 w δ hM hrhs) (hagree g hg) ?_
  · simpa using det_natDegree_le_of_column_bounds M (fun _ ↦ δ) hM
  · intro i hi
    have h₀ := eval_cramer_identity M rhs (domain i) (values i) 0 (hrow g hg i hi)
    have h₁ := eval_cramer_identity M rhs (domain i) (values i) 1 (hrow g hg i hi)
    rw [hfit g hg i hi, show numerator₀.eval (domain i) = _ from h₀.symm,
      show numerator₁.eval (domain i) = _ from h₁.symm]
    ring

end ProximityPrize.SubmissionLower.Koala6831Cramer
