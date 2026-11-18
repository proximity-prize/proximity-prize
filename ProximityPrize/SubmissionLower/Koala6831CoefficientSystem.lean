import ProximityPrize.SubmissionLower.Koala6831Cramer
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Eval.Degree

namespace ProximityPrize.SubmissionLower.Koala6831CoefficientSystem

open Polynomial
open scoped BigOperators Classical Matrix Polynomial

variable {K : Type*} [Field K]

abbrev SeedRing (K : Type*) [CommRing K] := MvPolynomial (Fin 2) K
abbrev SeedMonomial := Fin 2 →₀ ℕ

noncomputable def coefficientPolynomial (P : (SeedRing K)[X])
    (key : SeedMonomial) (cap : ℕ) : K[X] :=
  ∑ i ∈ Finset.range (cap + 1), monomial i ((P.coeff i).coeff key)

theorem coefficientPolynomial_degree (P : (SeedRing K)[X])
    (key : SeedMonomial) (cap : ℕ) : (coefficientPolynomial P key cap).natDegree ≤ cap := by
  unfold coefficientPolynomial
  apply natDegree_sum_le_of_forall_le
  intro i hi
  exact (natDegree_monomial_le _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

theorem eval_coefficientPolynomial (P : (SeedRing K)[X])
    (key : SeedMonomial) (cap : ℕ) (x : K) (hP : P.natDegree ≤ cap) :
    (coefficientPolynomial P key cap).eval x = (P.eval (MvPolynomial.C x)).coeff key := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hP), MvPolynomial.coeff_sum]
  simp only [coefficientPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro i _
  symm
  calc
    _ = (MvPolynomial.C (x ^ i) * P.coeff i).coeff key := by rw [map_pow, mul_comm]
    _ = _ := by rw [MvPolynomial.coeff_C_mul, mul_comm]

theorem matrix_node_equation {m : ℕ} (cols : Fin m → (SeedRing K)[X])
    (rhs : (SeedRing K)[X]) (keys : Fin m → SeedMonomial) (w δ : ℕ) (x : K)
    (word : Fin m → K) (hcols : ∀ j, (cols j).natDegree ≤ δ) (hrhs : rhs.natDegree ≤ w + δ)
    (h : (∑ j, MvPolynomial.C (word j) * (cols j).eval (MvPolynomial.C x)) =
      rhs.eval (MvPolynomial.C x)) :
    (evalRingHom x).mapMatrix (Matrix.of fun i j ↦ coefficientPolynomial (cols j) (keys i) δ)
        *ᵥ word = fun i ↦ (coefficientPolynomial rhs (keys i) (w + δ)).eval x := by
  funext i
  change (∑ j, (coefficientPolynomial (cols j) (keys i) δ).eval x * word j) =
    (coefficientPolynomial rhs (keys i) (w + δ)).eval x
  rw [eval_coefficientPolynomial _ _ _ _ hrhs]
  simp_rw [eval_coefficientPolynomial _ _ _ _ (hcols _)]
  have hcoeff := congrArg (fun p : SeedRing K ↦ p.coeff (keys i)) h
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul] at hcoeff
  simpa only [mul_comm] using hcoeff

theorem card_le_of_nonsingular_coefficients {ι : Type*} [DecidableEq K] (domain : ι ↪ K)
    (seeds : Finset K) (agreement : K → Finset ι) (selected : K → K[X])
    (cols : Fin 4 → (SeedRing K)[X]) (rhs : (SeedRing K)[X]) (keys : Fin 4 → SeedMonomial)
    (word : ι → Fin 4 → K) (w δ e : ℕ)
    (hdet : (Matrix.of fun i j ↦ coefficientPolynomial (cols j) (keys i) δ).det ≠ 0)
    (hcols : ∀ j, (cols j).natDegree ≤ δ) (hrhs : rhs.natDegree ≤ w + δ)
    (hdegree : ∀ g ∈ seeds, (selected g).natDegree ≤ w)
    (hagree : ∀ g ∈ seeds, w + 4 * δ < (agreement g).card)
    (hnode : ∀ g ∈ seeds, ∀ i ∈ agreement g,
      (∑ j, MvPolynomial.C (word i j) * (cols j).eval (MvPolynomial.C (domain i))) =
        rhs.eval (MvPolynomial.C (domain i)))
    (hfit : ∀ g ∈ seeds, ∀ i ∈ agreement g, (selected g).eval (domain i) = word i 0 + g * word i 1)
    (hno : ∀ P₀ P₁ : K[X], P₀.natDegree ≤ w → P₁.natDegree ≤ w →
      (seeds.filter (fun g ↦ selected g = P₀ + C g * P₁)).card ≤ e + 1) :
    seeds.card ≤ e + 1 := by
  apply Koala6831Cramer.card_le_of_rank_four domain seeds agreement selected
    (Matrix.of fun i j ↦ coefficientPolynomial (cols j) (keys i) δ)
    (fun i ↦ coefficientPolynomial rhs (keys i) (w + δ)) word w δ e hdet
    (fun _ _ ↦ coefficientPolynomial_degree _ _ _) (fun _ ↦ coefficientPolynomial_degree _ _ _)
    hdegree hagree ?_ hfit hno
  intro g hg i hi
  exact matrix_node_equation cols rhs keys w δ (domain i) (word i) hcols hrhs (hnode g hg i hi)

end ProximityPrize.SubmissionLower.Koala6831CoefficientSystem
