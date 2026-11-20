/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833FrobeniusModule
import Mathlib.RingTheory.Coprime.Lemmas

namespace KoalaFrontier
open Polynomial
open scoped Polynomial
variable {K : Type*} [Field K] (σ : K →+* K)

/-- Coefficient shifts and their cumulative products. -/
noncomputable def shift (P : K[X]) : ℕ → K[X]
  | 0 => P
  | j+1 => (shift P j).map σ

noncomputable def orbitProduct (P : K[X]) : ℕ → K[X]
  | 0 => 1
  | j+1 => P * (orbitProduct P j).map σ

theorem orbit_relation {L R H : K[X]} (hs : Solves σ L R H) (j : ℕ) :
    orbitProduct σ L j * shift σ H j = orbitProduct σ R j * H := by
  induction j with
  | zero => simp [orbitProduct,shift]
  | succ j ih =>
    have e := congrArg (Polynomial.map σ) ih
    simp only [Polynomial.map_mul] at e
    unfold Solves at hs
    simp only [orbitProduct,shift]
    linear_combination L*e+(orbitProduct σ R j).map σ*hs

/-- Each reduced denominator in each iterated Frobenius equation divides the
    primitive polynomial. Distinct coprime factors can be accumulated. -/
theorem orbit_denominator_dvd {L R H C D N : K[X]} (hs : Solves σ L R H) (j : ℕ)
    (cn : C≠0) (left : orbitProduct σ L j=C*D) (right : orbitProduct σ R j=C*N)
    (cop : IsCoprime D N) : D ∣ H := by
  have eq := orbit_relation σ hs j
  rw [left,right,mul_assoc,mul_assoc] at eq
  exact cop.dvd_of_dvd_mul_left ⟨_,(mul_left_cancel₀ cn eq).symm⟩

theorem orbit_factor_product {I : Type*} {L R H : K[X]} (hs : Solves σ L R H)
    (s : Finset I) (D : I → K[X])
    (cert : ∀ i ∈ s, ∃ (j : ℕ) (C N : K[X]), C≠0 ∧
      orbitProduct σ L j=C*D i ∧ orbitProduct σ R j=C*N ∧ IsCoprime (D i) N)
    (cop : (s : Set I).Pairwise (fun i j => IsCoprime (D i) (D j))) :
    (∏ i ∈ s, D i) ∣ H := by
  apply Finset.prod_dvd_of_coprime cop
  intro i hi
  obtain ⟨j,C,N,cn,el,er,co⟩ := cert i hi
  exact orbit_denominator_dvd σ hs j cn el er co

/-- The data-independent guaranteed degree saving is zero even for nonzero
    coefficients in both positions: with L=R, 1 solves, whatever deg L is. -/
theorem equal_rows_have_zero_saving (L H : K[X])
    (minim : ∀ U : K[X], U ≠ 0 → Solves σ L L U → H.natDegree ≤ U.natDegree) :
    H.natDegree = 0 := by
  have h := minim 1 one_ne_zero (by simp [Solves])
  simpa using h

theorem quotient_degree_bound {H T : K[X]} (hH : H≠0) (D : ℕ)
    (deg : (H*T).natDegree ≤ D) : T.natDegree ≤ D-H.natDegree := by
  by_cases z : T=0
  · simp [z]
  · rw [natDegree_mul hH z] at deg
    omega

theorem fixed_coefficients_iff (T : K[X]) :
    T.map σ = T ↔ ∀ k, σ (T.coeff k) = T.coeff k := by
  constructor
  · intro h k
    simpa only [coeff_map] using congrArg (fun P : K[X] => P.coeff k) h
  · intro h
    ext k
    simp [h]

#print axioms orbit_relation
#print axioms orbit_denominator_dvd
#print axioms orbit_factor_product
#print axioms equal_rows_have_zero_saving
#print axioms quotient_degree_bound
#print axioms fixed_coefficients_iff
end KoalaFrontier
