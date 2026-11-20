import ProximityPrize.SubmissionLower.Koala6844NormalizationPrelude
import Mathlib.FieldTheory.Minpoly.Field


namespace ProximityPrize.SubmissionLower.Koala6844Normalization

open Polynomial
open Koala6844Comparison (SymbolicRow IsPrimitiveRow)
open Koala6844Separation (Seeds NormalForm regroup primitive_regroup)
open Koala6844SeparationFactors (affine)
open Koala6844Moving (affineDenominator normalForm_specialized_compatibility)
open scoped Polynomial

noncomputable section

variable {K : Type*} [Field K]

private theorem degreeOf_affine_le (i j : Fin 2) (a b : K) :
    (affine j a b).degreeOf i ≤ if i = j then 1 else 0 := by
  classical
  unfold affine
  refine (MvPolynomial.degreeOf_add_le _ _ _).trans ?_
  apply max_le
  · simp
  · exact (MvPolynomial.degreeOf_C_mul_le _ _ _).trans (by
      rw [MvPolynomial.degreeOf_X])

private theorem degreeOf_separated_beta (A B C0 D : Fin 2 → K) (i : Fin 2) :
    (affine 0 (C0 0) (C0 1) * affine 1 (B 0) (B 1) +
      affine 0 (A 0) (A 1) * affine 1 (D 0) (D 1)).degreeOf i ≤ 1 := by
  classical
  refine (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
    have h0 := degreeOf_affine_le i 0 (C0 0) (C0 1)
    have h1 := degreeOf_affine_le i 1 (B 0) (B 1)
    fin_cases i <;> simp_all
  · refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
    have h0 := degreeOf_affine_le i 0 (A 0) (A 1)
    have h1 := degreeOf_affine_le i 1 (D 0) (D 1)
    fin_cases i <;> simp_all

theorem common_content_card_le {p w δ : ℕ} (hp : 2 ≤ p)
    {q : SymbolicRow (Seeds K)} (N : NormalForm q w δ)
    (hPrimitive : IsPrimitiveRow q) (σ : K →+* K)
    (seeds : Finset K) (selected : K → Polynomial K)
    (hWitness : ∀ g ∈ seeds, Koala6844Comparison.primitiveSelected σ p q selected g = 0)
    (hContent : ¬ IsCoprime N.d₀ N.d₁) :
    seeds.card ≤ p + 1 := by
  classical
  let c := algebraMap K (AlgebraicClosure K)
  have hNotRelPrime : ¬ IsRelPrime N.d₀ N.d₁ := fun h => hContent h.isCoprime
  obtain ⟨ζ, h0, h1⟩ :=
    Koala6844Moving.common_root_of_not_relPrime N.d₀ N.d₁ N.d₀_ne hNotRelPrime
  let evalζ := eval₂RingHom c ζ
  let β := MvPolynomial.map evalζ (regroup q.beta)
  have heval0 : evalζ N.d₀ = 0 := h0
  have heval1 : evalζ N.d₁ = 0 := h1
  have hβ : β ≠ 0 := by
    intro hz
    let m := minpoly K ζ
    have hmd0 : m ∣ N.d₀ := minpoly.dvd K ζ (by exact h0)
    have hmd1 : m ∣ N.d₁ := minpoly.dvd K ζ (by exact h1)
    have hmBeta : MvPolynomial.C m ∣ regroup q.beta := by
      rw [MvPolynomial.C_dvd_iff_dvd_coeff]
      intro i
      apply minpoly.dvd K ζ
      have hcoeff := congrArg (fun P : MvPolynomial (Fin 2) (AlgebraicClosure K) => P.coeff i) hz
      change evalζ ((regroup q.beta).coeff i) = 0
      simpa only [β, MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hcoeff
    have hmFirst : MvPolynomial.C m ∣ regroup q.first := by
      rw [N.first_eq]
      exact dvd_mul_of_dvd_left (_root_.map_dvd MvPolynomial.C hmd0) _
    have hmSecond : MvPolynomial.C m ∣ regroup q.second := by
      rw [N.second_eq]
      have he : MvPolynomial.C m ∣ MvPolynomial.C N.d₁ * affine 0 (N.A 0) (N.A 1) :=
        dvd_mul_of_dvd_left (_root_.map_dvd MvPolynomial.C hmd1) _
      obtain ⟨v, hv⟩ := he
      exact ⟨-v, by rw [hv]; ring⟩
    have hm := primitive_regroup q.beta q.first q.second hPrimitive
      (MvPolynomial.C m) hmBeta hmFirst hmSecond
    have hEval := hm.map (MvPolynomial.eval fun _ : Fin 2 => (0 : Polynomial K))
    have hmUnit : IsUnit m := by simpa only [MvPolynomial.eval_C] using hEval
    have hMap := hmUnit.map evalζ
    have he : evalζ m = 0 := minpoly.aeval K ζ
    exact hMap.ne_zero he
  have hShape : β =
      affine 0 (evalζ (N.C 0)) (evalζ (N.C 1)) *
        affine 1 (evalζ (N.B 0)) (evalζ (N.B 1)) +
      affine 0 (evalζ (N.A 0)) (evalζ (N.A 1)) *
        affine 1 (evalζ (N.D 0)) (evalζ (N.D 1)) := by
    simp only [β, N.beta_eq, map_add, map_mul, Koala6844Separation.map_affine]
  have hDeg (i : Fin 2) : β.degreeOf i ≤ 1 := by
    rw [hShape]
    exact degreeOf_separated_beta (evalζ ∘ N.A) (evalζ ∘ N.B)
      (evalζ ∘ N.C) (evalζ ∘ N.D) i
  have hz : ∀ g ∈ seeds.image c,
      MvPolynomial.eval (Koala6844BivariateSeeds.coordinates g (g ^ p)) β = 0 := by
    intro t ht
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp ht
    have h := congrArg evalζ (normalForm_specialized_compatibility N σ p selected g (hWitness g hg))
    simp only [map_add, map_mul, map_sub, heval0, heval1, zero_mul, zero_sub, zero_add] at h
    simp only [hShape, affine, map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      Koala6844BivariateSeeds.coordinates, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]
    have hc (r : K) : evalζ (C r) = c r := eval₂_C _ _
    simp only [affineDenominator, map_add, map_mul, hc, map_pow] at h
    linear_combination -h
  have hcard := Koala6844BivariateSeeds.card_le_of_vanishing (b := 2) (c := 2)
    (by omega : 0 < p) hp hβ (Nat.lt_succ_of_le (hDeg 0)) (Nat.lt_succ_of_le (hDeg 1)) _ hz
  rw [Finset.card_image_of_injective _ c.injective] at hcard
  simpa [add_comm] using hcard

end

end ProximityPrize.SubmissionLower.Koala6844Normalization
