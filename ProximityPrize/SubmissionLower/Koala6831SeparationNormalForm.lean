import ProximityPrize.SubmissionLower.Koala6831SeparationSystem
import ProximityPrize.SubmissionLower.Koala6831SeparationBiaffine
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Mathlib.RingTheory.Polynomial.UniqueFactorization

namespace ProximityPrize.SubmissionLower.Koala6831Separation

open Polynomial
open Koala6831Comparison (SymbolicRow)
open Koala6831SeparationFactors (affine coeff_affine_zero coeff_affine_one integral_separation)
open scoped BigOperators Matrix Polynomial

set_option maxHeartbeats 1600000

variable {K I : Type*} [Field K]

structure NormalForm (q : SymbolicRow (Seeds K)) (w δ : ℕ) where
  A : Fin 2 → K[X]
  B : Fin 2 → K[X]
  C : Fin 2 → K[X]
  D : Fin 2 → K[X]
  d₀ : K[X]
  d₁ : K[X]
  d₀_ne : d₀ ≠ 0
  d₁_ne : d₁ ≠ 0
  A_coprime : IsCoprime (A 0) (A 1)
  B_coprime : IsCoprime (B 0) (B 1)
  first_eq : regroup q.first = MvPolynomial.C d₀ * affine 1 (B 0) (B 1)
  second_eq : regroup q.second = -(MvPolynomial.C d₁ * affine 0 (A 0) (A 1))
  beta_eq : regroup q.beta = affine 0 (C 0) (C 1) * affine 1 (B 0) (B 1) +
    affine 0 (A 0) (A 1) * affine 1 (D 0) (D 1)
  first_degree : d₀.natDegree + pairDegree B ≤ δ
  second_degree : d₁.natDegree + pairDegree A ≤ δ
  left_degree : pairDegree B + pairDegree C ≤ w + δ
  right_degree : pairDegree A + pairDegree D ≤ w + δ

private theorem degree_of_integral_factor (P : (Seeds K)[X]) (i : Fin 2)
    (A : Fin 2 → K[X]) (d : K[X]) (δ : ℕ) (hd : d ≠ 0)
    (hA : IsCoprime (A 0) (A 1)) (hP : P.natDegree ≤ δ)
    (he : regroup P = MvPolynomial.C d * affine i (A 0) (A 1)) :
    d.natDegree + pairDegree A ≤ δ := by
  have bound (j : Fin 2) : (d * A j).natDegree ≤ δ := by
    let key := Finsupp.single i j.val
    have hkey := coeff_regroup_eq P key δ hP
    have hdeg := Koala6831CoefficientSystem.coefficientPolynomial_degree P key δ
    rw [← hkey, he, MvPolynomial.coeff_C_mul] at hdeg
    fin_cases j
    · change (d * A 0).natDegree ≤ δ
      simpa only [key, Fin.val_zero, Finsupp.single_zero, coeff_affine_zero] using hdeg
    · change (d * A 1).natDegree ≤ δ
      simpa only [key, show (1 : Fin 2).val = 1 by decide, coeff_affine_one] using hdeg
  have hn : A 0 ≠ 0 ∨ A 1 ≠ 0 := by
    by_contra! hz
    obtain ⟨u, v, hu⟩ := hA
    simp [hz.1, hz.2] at hu
  unfold pairDegree
  rcases hn with hne | hne
  · have b₀ := bound (0 : Fin 2)
    rw [Polynomial.natDegree_mul hd hne] at b₀
    have b₁ : d.natDegree + (A 1).natDegree ≤ δ := by
      by_cases hz : A 1 = 0
      · simp only [hz, natDegree_zero, Nat.add_zero]
        omega
      · simpa only [natDegree_mul hd hz] using bound (1 : Fin 2)
    omega
  · have b₁ := bound (1 : Fin 2)
    rw [Polynomial.natDegree_mul hd hne] at b₁
    have b₀ : d.natDegree + (A 0).natDegree ≤ δ := by
      by_cases hz : A 0 = 0
      · simp only [hz, natDegree_zero, Nat.add_zero]
        omega
      · simpa only [natDegree_mul hd hz] using bound (0 : Fin 2)
    omega

theorem normalForm_of_singular (domain : I ↪ K) (nodes : Finset I)
    (q : SymbolicRow (Seeds K)) (word : I → Fin 4 → K) (w δ : ℕ)
    (hfirst0 : q.first ≠ 0) (hsecond0 : q.second ≠ 0)
    (hfirst : q.first.natDegree ≤ δ) (hsecond : q.second.natDegree ≤ δ)
    (hbeta : q.beta.natDegree ≤ w + δ) (hsmall : δ ≤ w) (hcard : w + 4 * δ < nodes.card)
    (hgood : ∀ i ∈ nodes,
      q.atNode (MvPolynomial.C (domain i))
        (MvPolynomial.C (word i 0) + MvPolynomial.X 0 * MvPolynomial.C (word i 1))
        (MvPolynomial.C (word i 2) + MvPolynomial.X 1 * MvPolynomial.C (word i 3)) = 0)
    (hsingular : ∀ keys : Fin 4 → (Fin 2 →₀ ℕ), (Koala6831RankFour.matrix q keys δ).det = 0)
    (hprimitive : ∀ P, P ∣ q.beta → P ∣ q.first → P ∣ q.second → IsUnit P) :
    Nonempty (NormalForm q w δ) := by
  classical
  let _ : GCDMonoid (Seeds K[X]) := UniqueFactorizationMonoid.toGCDMonoid _
  obtain ⟨⟨v, hv, hrel⟩, hspan⟩ := rational_relation_and_span domain nodes q word w δ
    hfirst0 hsecond0 hfirst hsecond hbeta hcard hgood hsingular
  obtain ⟨hv', hrelation⟩ := exists_affine_relation v hv hrel
  obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hspan
  have hbetaF : asRational q.beta =
      affine 0 (u 0) (u 1) * asRational q.first + affine 1 (u 2) (u 3) * asRational q.second := by
    simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
      seedColumns, Matrix.cons_val_zero, Matrix.cons_val_succ, MvPolynomial.smul_eq_C_mul] at hu
    change MvPolynomial.C (u 0) * asRational q.first +
      (MvPolynomial.C (u 1) * (MvPolynomial.X 0 * asRational q.first) +
        (MvPolynomial.C (u 2) * asRational q.second +
          MvPolynomial.C (u 3) * (MvPolynomial.X 1 * asRational q.second))) = asRational q.beta at hu
    unfold affine
    linear_combination -hu
  have hp := primitive_regroup q.beta q.first q.second hprimitive
  have hf0 : regroup q.first ≠ 0 :=
    fun h ↦ hfirst0 (regroup_injective (by simpa using h))
  have hf1 : regroup q.second ≠ 0 :=
    fun h ↦ hsecond0 (regroup_injective (by simpa using h))
  obtain ⟨A, B, d₀, d₁, hd₀, hd₁, hA, hB, h₀, h₁⟩ := integral_separation
    (v 0) (v 1) (v 2) (v 3) (regroup q.beta) (regroup q.first) (regroup q.second)
    (affine 0 (u 0) (u 1)) (affine 1 (u 2) (u 3)) hf0 hf1 hv' hrelation hbetaF hp
  have hdeg₀ := degree_of_integral_factor q.first 1 B d₀ δ hd₀ hB hfirst h₀
  have hdeg₁ := degree_of_integral_factor (-q.second) 0 A d₁ δ hd₁ hA
    (by simpa using hsecond) (by rw [map_neg, h₁, neg_neg])
  let φ := algebraMap K[X] (NodeField K)
  have hfirstF : asRational q.first = MvPolynomial.C (φ d₀) * affine 1 (φ (B 0)) (φ (B 1)) := by
    change MvPolynomial.map φ (regroup q.first) = _
    rw [h₀, map_mul, MvPolynomial.map_C, map_affine]
  have hsecondF : asRational q.second = -(MvPolynomial.C (φ d₁) * affine 0 (φ (A 0)) (φ (A 1))) := by
    change MvPolynomial.map φ (regroup q.second) = _
    rw [h₁, map_neg, map_mul, MvPolynomial.map_C, map_affine]
  have hlim : pairDegree A + pairDegree B ≤ w + δ := by omega
  have hcb (i j : Fin 2) : ((regroup q.beta).coeff (corner i j)).natDegree ≤ w + δ := by
    rw [coeff_regroup_eq _ _ _ hbeta]
    exact Koala6831CoefficientSystem.coefficientPolynomial_degree _ _ _
  obtain ⟨C', D', hC', hD', hβ⟩ := exists_biaffine_decomposition_with_degree φ
    (IsFractionRing.injective _ _) A B (regroup q.beta) hA hB (w + δ) hlim hcb (by
      refine ⟨![u 0 * φ d₀, u 1 * φ d₀], ![-(u 2 * φ d₁), -(u 3 * φ d₁)], ?_⟩
      change asRational q.beta = _
      rw [hbetaF, hfirstF, hsecondF]
      simp only [affine, Matrix.cons_val_zero, Matrix.cons_val_one, map_mul, map_neg]
      ring)
  exact ⟨⟨A, B, C', D', d₀, d₁, hd₀, hd₁, hA, hB, h₀, h₁, hβ, hdeg₀, hdeg₁, hC', hD'⟩⟩

theorem NormalForm.fixedWord {q : SymbolicRow (Seeds K)} {w δ : ℕ}
    (N : NormalForm q w δ) (x : K) (U V : Fin 2 → K)
    (h : q.atNode (MvPolynomial.C x) (affine 0 (U 0) (U 1)) (affine 1 (V 0) (V 1)) = 0) :
    ∃ u : K, (∀ i, N.d₀.eval x * U i + (N.C i).eval x = u * (N.A i).eval x) ∧
      ∀ j, N.d₁.eval x * V j - (N.D j).eval x = u * (N.B j).eval x := by
  exact fixed_word_at_node x N.A N.B N.C N.D N.d₀ N.d₁ U V (regroup q.beta) (regroup q.first)
    (regroup q.second) N.A_coprime N.B_coprime N.beta_eq N.first_eq N.second_eq (by
      simpa only [map_eval_regroup, SymbolicRow.atNode] using h)

end ProximityPrize.SubmissionLower.Koala6831Separation
