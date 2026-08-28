import ProximityPrize.Benchmark.TargetLower

namespace ProximityPrize.SubmissionLower

open Polynomial

variable {F : Type} [Field F]

/-- A family whose coefficients are affine functions of the parameter is an
affine line in the polynomial space.  Only coefficients through the common
degree bound have to be specified. -/
theorem affine_polynomial_family_of_coefficients
    (P : F → F[X]) (S : Finset F) (k : ℕ) (a b : ℕ → F)
    (hPdeg : ∀ z ∈ S, (P z).natDegree ≤ k)
    (hcoeff : ∀ z ∈ S, ∀ i ≤ k, (P z).coeff i = a i + z * b i) :
    ∃ p₀ p₁ : F[X],
      p₀.natDegree ≤ k ∧ p₁.natDegree ≤ k ∧
      ∀ z ∈ S, P z = p₀ + Polynomial.C z * p₁ := by
  classical
  set p₀ : F[X] := ∑ i ∈ Finset.range (k + 1), Polynomial.monomial i (a i) with hp₀
  set p₁ : F[X] := ∑ i ∈ Finset.range (k + 1), Polynomial.monomial i (b i) with hp₁
  have hp₀coeff (i : ℕ) : p₀.coeff i = if i ≤ k then a i else 0 := by
    rw [hp₀, Polynomial.finsetSum_coeff]
    simp_rw [Polynomial.coeff_monomial]
    simp [Finset.mem_range]
  have hp₁coeff (i : ℕ) : p₁.coeff i = if i ≤ k then b i else 0 := by
    rw [hp₁, Polynomial.finsetSum_coeff]
    simp_rw [Polynomial.coeff_monomial]
    simp [Finset.mem_range]
  have hp₀deg : p₀.natDegree ≤ k := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [hp₀coeff]
    simp [Nat.not_le_of_lt hi]
  have hp₁deg : p₁.natDegree ≤ k := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [hp₁coeff]
    simp [Nat.not_le_of_lt hi]
  refine ⟨p₀, p₁, hp₀deg, hp₁deg, ?_⟩
  intro z hz
  ext i
  by_cases hi : i ≤ k
  · simp [hp₀coeff, hp₁coeff, hi, hcoeff z hz i hi]
  · have hPi : (P z).coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hPdeg z hz) (by omega))
    simp [hp₀coeff, hp₁coeff, hi, hPi]

/-- Packaging of a coefficient-by-coefficient polynomial dependence on the
parameter.  This is the direct target of a simple-root/Hensel recursion: the
`i`-th coefficient of `P z` is represented by a polynomial `q i` of degree at
most `i * D`. -/
def HasPolynomialCoefficientLift
    (P : F → F[X]) (S : Finset F) (k D : ℕ) : Prop :=
  ∃ q : ℕ → F[X],
    (∀ i ≤ k, (q i).natDegree ≤ i * D) ∧
    ∀ z ∈ S, ∀ i ≤ k, (P z).coeff i = (q i).eval z

/-- A Hensel-style coefficient lift with degree-one coefficient functions
immediately yields an affine line.  This isolates the exact strengthening of
the usual weighted bounds needed for the affine conclusion. -/
theorem affine_polynomial_family_of_coefficient_lifts_degree_one
    (P : F → F[X]) (S : Finset F) (k : ℕ) (q : ℕ → F[X])
    (hPdeg : ∀ z ∈ S, (P z).natDegree ≤ k)
    (hqdeg : ∀ i ≤ k, (q i).natDegree ≤ 1)
    (hcoeff : ∀ z ∈ S, ∀ i ≤ k, (P z).coeff i = (q i).eval z) :
    ∃ p₀ p₁ : F[X],
      p₀.natDegree ≤ k ∧ p₁.natDegree ≤ k ∧
      ∀ z ∈ S, P z = p₀ + Polynomial.C z * p₁ := by
  apply affine_polynomial_family_of_coefficients P S k
    (fun i => (q i).coeff 0) (fun i => (q i).coeff 1) hPdeg
  intro z hz i hi
  rw [hcoeff z hz i hi]
  have hform := Polynomial.eq_X_add_C_of_natDegree_le_one (hqdeg i hi)
  rw [hform]
  simp
  ring


/-- Coefficient functions of a bounded degree are uniquely determined by enough
specializations.  This is the root-counting step normally used after each
coefficient equation in a Hensel lift. -/
theorem coefficient_polynomial_unique_of_many_values
    (S : Finset F) (q r : F[X]) (N : ℕ)
    (hqdeg : q.natDegree ≤ N) (hrdeg : r.natDegree ≤ N)
    (hcard : N < S.card) (heval : ∀ z ∈ S, q.eval z = r.eval z) :
    q = r := by
  exact Polynomial.eq_of_natDegree_lt_card_of_eval_eq' q r S heval
    ((max_le hqdeg hrdeg).trans_lt hcard)

/-- Weighted version matching the `i * D` coefficient bound produced by a
simple-root recursion. -/
theorem weighted_coefficient_polynomial_unique_of_many_values
    (S : Finset F) (q r : ℕ → F[X]) (i D : ℕ)
    (hqdeg : (q i).natDegree ≤ i * D) (hrdeg : (r i).natDegree ≤ i * D)
    (hcard : i * D < S.card)
    (heval : ∀ z ∈ S, (q i).eval z = (r i).eval z) :
    q i = r i :=
  coefficient_polynomial_unique_of_many_values S (q i) (r i) (i * D)
    hqdeg hrdeg hcard heval

end ProximityPrize.SubmissionLower
