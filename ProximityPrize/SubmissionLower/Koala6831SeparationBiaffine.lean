import ProximityPrize.SubmissionLower.Koala6831SeparationDegree
import ProximityPrize.SubmissionLower.Koala6831SeparationFactors

namespace ProximityPrize.SubmissionLower.Koala6831Separation

open Koala6831SeparationFactors (affine)
open scoped Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

noncomputable def corner (i j : Fin 2) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 i.val + Finsupp.single 1 j.val

@[simp] private theorem corner_apply_zero (i j : Fin 2) : corner i j 0 = i.val := by
  simp [corner]

@[simp] private theorem corner_apply_one (i j : Fin 2) : corner i j 1 = j.val := by
  simp [corner]

private theorem corner_eq_corner {i j i' j' : Fin 2} :
    corner i j = corner i' j' ↔ i = i' ∧ j = j' := by
  constructor
  · intro h
    exact ⟨Fin.ext (by simpa using congrArg (· 0) h),
      Fin.ext (by simpa using congrArg (· 1) h)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

noncomputable def biform (β : Fin 2 → Fin 2 → R) : MvPolynomial (Fin 2) R :=
  ∑ i, ∑ j, MvPolynomial.monomial (corner i j) (β i j)

@[simp] theorem coeff_biform (β : Fin 2 → Fin 2 → R) (i j : Fin 2) :
    (biform β).coeff (corner i j) = β i j := by
  classical
  fin_cases i <;> fin_cases j <;> simp [biform, MvPolynomial.coeff_monomial, corner_eq_corner]

@[simp] theorem map_biform (φ : R →+* S) (β : Fin 2 → Fin 2 → R) :
    MvPolynomial.map φ (biform β) = biform (fun i j ↦ φ (β i j)) := by
  simp only [biform, map_sum, MvPolynomial.map_monomial]

theorem biform_add (β γ : Fin 2 → Fin 2 → R) :
    biform (fun i j ↦ β i j + γ i j) = biform β + biform γ := by
  simp only [biform, map_add, Finset.sum_add_distrib]

@[simp] theorem map_affine (φ : R →+* S) (i : Fin 2) (a b : R) :
    MvPolynomial.map φ (affine i a b) = affine i (φ a) (φ b) := by
  simp only [affine, map_add, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]

private theorem affine_eq_sum (i : Fin 2) (A : Fin 2 → R) :
    affine i (A 0) (A 1) = ∑ j : Fin 2, MvPolynomial.monomial (Finsupp.single i j.val) (A j) := by
  rw [Fin.sum_univ_two]
  simp [affine, MvPolynomial.C_apply, MvPolynomial.X, MvPolynomial.monomial_mul_monomial,
    -MvPolynomial.monomial_zero']

theorem biform_mul_affine (A B : Fin 2 → R) :
    biform (fun i j ↦ A i * B j) = affine 0 (A 0) (A 1) * affine 1 (B 0) (B 1) := by
  rw [affine_eq_sum 0 A, affine_eq_sum 1 B, Finset.sum_mul]
  simp only [biform, corner, Finset.mul_sum, MvPolynomial.monomial_mul_monomial]

private theorem biform_decomposition (A B C D : Fin 2 → R) :
    biform (fun i j ↦ C i * B j + A i * D j) =
      affine 0 (C 0) (C 1) * affine 1 (B 0) (B 1) +
        affine 0 (A 0) (A 1) * affine 1 (D 0) (D 1) := by
  rw [biform_add, biform_mul_affine, biform_mul_affine]

theorem exists_biaffine_decomposition_with_degree {K : Type*} [Field K]
    (φ : K[X] →+* S) (hφ : Function.Injective φ) (A B : Fin 2 → K[X])
    (beta : MvPolynomial (Fin 2) K[X]) (hA : IsCoprime (A 0) (A 1))
    (hB : IsCoprime (B 0) (B 1)) (lim : ℕ) (hlim : pairDegree A + pairDegree B ≤ lim)
    (hβ : ∀ i j, (beta.coeff (corner i j)).natDegree ≤ lim)
    (h : ∃ C D : Fin 2 → S, MvPolynomial.map φ beta =
      affine 0 (C 0) (C 1) * affine 1 (φ (B 0)) (φ (B 1)) +
        affine 0 (φ (A 0)) (φ (A 1)) * affine 1 (D 0) (D 1)) :
    ∃ C D : Fin 2 → K[X], pairDegree B + pairDegree C ≤ lim ∧
      pairDegree A + pairDegree D ≤ lim ∧
      beta = affine 0 (C 0) (C 1) * affine 1 (B 0) (B 1) +
        affine 0 (A 0) (A 1) * affine 1 (D 0) (D 1) := by
  obtain ⟨C, D, h⟩ := h
  have he := biform_decomposition (φ ∘ A) (φ ∘ B) C D
  simp only [Function.comp_apply] at he
  rw [← he] at h
  let β (i j : Fin 2) := beta.coeff (corner i j)
  have hcoeff (i j : Fin 2) : φ (β i j) = C i * φ (B j) + φ (A i) * D j := by
    have heq := congrArg (fun q : MvPolynomial (Fin 2) S ↦ q.coeff (corner i j)) h
    simpa only [MvPolynomial.coeff_map, coeff_biform, β, Function.comp_apply] using heq
  have hshape : beta = biform β := by
    apply MvPolynomial.map_injective φ hφ
    rw [h, map_biform]
    exact congrArg biform (funext fun i ↦ funext fun j ↦ (hcoeff i j).symm)
  have hw : wedge A B β = 0 := by
    apply hφ
    rw [map_zero]
    simpa only [wedge, map_mul, map_sub, Function.comp_apply] using
      wedge_eq_zero_of_decomposition (φ ∘ A) (φ ∘ B) C D (fun i j ↦ φ (β i j)) hcoeff
  obtain ⟨C', D', hC', hD', hCD⟩ :=
    exists_decomposition_with_degree A B β hA hB lim hlim hβ hw
  refine ⟨C', D', hC', hD', ?_⟩
  rw [← biform_decomposition A B C' D', hshape]
  exact congrArg biform (funext fun i ↦ funext fun j ↦ hCD i j)

theorem fixed_word_of_affine_identity (A B C D U V : Fin 2 → R) (d₀ d₁ : R)
    (hA : IsCoprime (A 0) (A 1)) (hB : IsCoprime (B 0) (B 1))
    (h : (affine 0 (C 0) (C 1) * affine 1 (B 0) (B 1) +
          affine 0 (A 0) (A 1) * affine 1 (D 0) (D 1)) +
        (MvPolynomial.C d₀ * affine 1 (B 0) (B 1)) * affine 0 (U 0) (U 1) +
        (-(MvPolynomial.C d₁ * affine 0 (A 0) (A 1))) * affine 1 (V 0) (V 1) = 0) :
    ∃ u : R, (∀ i, d₀ * U i + C i = u * A i) ∧
      ∀ j, d₁ * V j - D j = u * B j := by
  let C' (i : Fin 2) := d₀ * U i + C i
  let D' (j : Fin 2) := D j - d₁ * V j
  have h' : affine 0 (C' 0) (C' 1) * affine 1 (B 0) (B 1) +
      affine 0 (A 0) (A 1) * affine 1 (D' 0) (D' 1) = 0 := by
    dsimp only [C', D']
    simp only [affine, map_add, map_sub, map_mul] at h ⊢
    linear_combination h
  rw [← biform_decomposition A B C' D'] at h'
  apply fixed_word A B C D U V d₀ d₁ hA hB
  intro i j
  have hcoeff := congrArg (fun P : MvPolynomial (Fin 2) R ↦ P.coeff (corner i j)) h'
  simpa only [coeff_biform, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, C', D'] using hcoeff

theorem fixed_word_at_node {K : Type*} [Field K] (x : K)
    (A B C D : Fin 2 → K[X]) (d₀ d₁ : K[X]) (U V : Fin 2 → K)
    (beta first second : MvPolynomial (Fin 2) K[X])
    (hA : IsCoprime (A 0) (A 1)) (hB : IsCoprime (B 0) (B 1))
    (hbeta : beta = affine 0 (C 0) (C 1) * affine 1 (B 0) (B 1) +
      affine 0 (A 0) (A 1) * affine 1 (D 0) (D 1))
    (hfirst : first = MvPolynomial.C d₀ * affine 1 (B 0) (B 1))
    (hsecond : second = -(MvPolynomial.C d₁ * affine 0 (A 0) (A 1)))
    (hnode : MvPolynomial.map (Polynomial.evalRingHom x) beta +
      MvPolynomial.map (Polynomial.evalRingHom x) first * affine 0 (U 0) (U 1) +
      MvPolynomial.map (Polynomial.evalRingHom x) second * affine 1 (V 0) (V 1) = 0) :
    ∃ u : K, (∀ i, d₀.eval x * U i + (C i).eval x = u * (A i).eval x) ∧
      ∀ j, d₁.eval x * V j - (D j).eval x = u * (B j).eval x := by
  let e := Polynomial.evalRingHom x
  exact fixed_word_of_affine_identity (e ∘ A) (e ∘ B) (e ∘ C) (e ∘ D) U V (e d₀) (e d₁)
    (hA.map e) (hB.map e) (by
      simpa only [e, Function.comp_apply, hbeta, hfirst, hsecond, map_affine,
        map_add, map_mul, map_neg, MvPolynomial.map_C] using hnode)

end ProximityPrize.SubmissionLower.Koala6831Separation
