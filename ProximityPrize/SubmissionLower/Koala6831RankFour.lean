import ProximityPrize.SubmissionLower.Koala6831ComparisonRank
import ProximityPrize.SubmissionLower.Koala6831CoefficientSystem
import Mathlib.Tactic.LinearCombination

namespace ProximityPrize.SubmissionLower.Koala6831RankFour

open Polynomial
open scoped BigOperators Classical Matrix Polynomial
open Koala6831Comparison (SymbolicRow)
open Koala6831CoefficientSystem (SeedRing SeedMonomial coefficientPolynomial)

set_option maxHeartbeats 1800000

variable {K I : Type*} [Field K]

noncomputable def columns (q : SymbolicRow (SeedRing K)) : Fin 4 → (SeedRing K)[X] :=
  ![q.first, Polynomial.C (MvPolynomial.X 0) * q.first,
    q.second, Polynomial.C (MvPolynomial.X 1) * q.second]

noncomputable def matrix (q : SymbolicRow (SeedRing K)) (keys : Fin 4 → SeedMonomial)
    (δ : ℕ) : Matrix (Fin 4) (Fin 4) K[X] :=
  Matrix.of fun i j ↦ coefficientPolynomial (columns q j) (keys i) δ

private theorem columns_degree (q : SymbolicRow (SeedRing K)) (δ : ℕ)
    (hfirst : q.first.natDegree ≤ δ) (hsecond : q.second.natDegree ≤ δ) :
    ∀ j, (columns q j).natDegree ≤ δ := by
  intro j
  fin_cases j
  · exact hfirst
  · exact (Polynomial.natDegree_C_mul_le _ _).trans hfirst
  · exact hsecond
  · exact (Polynomial.natDegree_C_mul_le _ _).trans hsecond

theorem equation_of_good_node (q : SymbolicRow (SeedRing K)) (x : K) (word : Fin 4 → K)
    (h : q.atNode (MvPolynomial.C x)
      (MvPolynomial.C (word 0) + MvPolynomial.X 0 * MvPolynomial.C (word 1))
      (MvPolynomial.C (word 2) + MvPolynomial.X 1 * MvPolynomial.C (word 3)) = 0) :
    (∑ j, MvPolynomial.C (word j) * (columns q j).eval (MvPolynomial.C x)) =
      (-q.beta).eval (MvPolynomial.C x) := by
  unfold SymbolicRow.atNode at h
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    columns, Matrix.cons_val_zero, Matrix.cons_val_succ, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_neg]
  simp only [show (0 : Fin 3).succ = (1 : Fin 4) by decide,
    show (0 : Fin 2).succ.succ = (2 : Fin 4) by decide,
    show (0 : Fin 1).succ.succ.succ = (3 : Fin 4) by decide]
  linear_combination h

theorem retained_card_le [DecidableEq K] (domain : I ↪ K)
    (retained : Finset K) (agreement : K → Finset I) (selected : K → K[X])
    (q : SymbolicRow (SeedRing K)) (keys : Fin 4 → SeedMonomial) (word : I → Fin 4 → K)
    (δ : ℕ) (hδ : δ ≤ 12503) (hdet : (matrix q keys δ).det ≠ 0)
    (hbeta : q.beta.natDegree ≤ 131071 + δ)
    (hfirst : q.first.natDegree ≤ δ) (hsecond : q.second.natDegree ≤ δ)
    (hdegree : ∀ g ∈ retained, (selected g).natDegree ≤ 131071)
    (hcard : ∀ g ∈ retained, 181084 ≤ (agreement g).card)
    (hgood : ∀ g ∈ retained, ∀ i ∈ agreement g,
      q.atNode (MvPolynomial.C (domain i))
        (MvPolynomial.C (word i 0) + MvPolynomial.X 0 * MvPolynomial.C (word i 1))
        (MvPolynomial.C (word i 2) + MvPolynomial.X 1 * MvPolynomial.C (word i 3)) = 0)
    (hfit : ∀ g ∈ retained, ∀ i ∈ agreement g, (selected g).eval (domain i) = word i 0 + g * word i 1)
    (hno : ∀ P₀ P₁ : K[X], P₀.natDegree ≤ 131071 → P₁.natDegree ≤ 131071 →
      (retained.filter (fun g ↦ selected g = P₀ + C g * P₁)).card ≤ 81061) :
    retained.card ≤ 81061 := by
  have hneg : (-q.beta).natDegree ≤ 131071 + δ := by simpa using hbeta
  apply Koala6831CoefficientSystem.card_le_of_nonsingular_coefficients domain retained agreement
    selected (columns q) (-q.beta) keys word 131071 δ 81060 hdet
    (columns_degree q δ hfirst hsecond) hneg hdegree ?_ ?_ hfit hno
  · intro g hg
    have hn := hcard g hg
    omega
  · exact fun g hg i hi ↦ equation_of_good_node q (domain i) (word i) (hgood g hg i hi)

end ProximityPrize.SubmissionLower.Koala6831RankFour
