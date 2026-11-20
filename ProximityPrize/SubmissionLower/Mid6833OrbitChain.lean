/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833OrbitFactors
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.BigOperators

namespace KoalaFrontier
open Polynomial Finset
open scoped Polynomial BigOperators
variable {K : Type*} [Field K] (σ : K →+* K)

/-- Consecutive distinct orbit points force the entire intervening pole chain.
    A chain with m+1 points and endpoint multiplicity d has generator degree m*d.
    In a degree-six extension m=5 is possible. -/
theorem orbit_chain (m d : ℕ) (a : ℕ → K)
    (fresh : ∀ i ≤ m, ∀ j ≤ m, i ≠ j → a i ≠ a j)
    (step : ∀ i < m, σ (a i)=a (i+1)) :
    let U := fun i => ((X : K[X])-C (a i))^d
    let H := ∏ i ∈ range m, U i
    Solves σ (U 0) (U m) H ∧ H.natDegree=m*d ∧
      ∀ V : K[X], Solves σ (U 0) (U m) V → H ∣ V := by
  classical
  let U (i : ℕ) := ((X : K[X])-C (a i))^d
  let H (k : ℕ) := ∏ i ∈ range k, U i
  change Solves σ (U 0) (U m) (H m) ∧ (H m).natDegree=m*d ∧ _
  have su i (hi : i<m) : (U i).map σ=U (i+1) := by simp [U,step i hi]
  have cp i (hi : i ≤ m) j (hj : j ≤ m) (ne : i≠j) : IsCoprime (U i) (U j) :=
    (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr (fresh i hi j hj ne)).isUnit).pow
  have recurrence (k : ℕ) (hk : k ≤ m) : Solves σ (U 0) (U k) (H k) := by
    induction k with
    | zero => simp [H,Solves]
    | succ k ih =>
      have e := ih (by omega)
      unfold Solves at *
      simp only [H,Finset.prod_range_succ,Polynomial.map_mul,su k (by omega)]
      change U 0 * ((H k).map σ * U (k+1)) = U (k+1) * (H k * U k)
      linear_combination U (k+1)*e
  refine ⟨recurrence m (le_refl m),?_,?_⟩
  · unfold H
    rw [Polynomial.natDegree_prod (range m) U (fun i _ => pow_ne_zero d (X_sub_C_ne_zero (a i)))]
    simp [U,natDegree_pow]
  · intro V eqn
    change H m ∣ V
    have divs (i : ℕ) (hi : i<m) : U i ∣ V := by
      induction i with
      | zero =>
        apply (cp 0 (by omega) m (by omega) (by omega)).dvd_of_dvd_mul_left
        exact ⟨_,eqn.symm⟩
      | succ i ih =>
        have old := Polynomial.map_dvd σ (ih (by omega))
        rw [su i (by omega)] at old
        apply (cp (i+1) (by omega) m (by omega) (by omega)).dvd_of_dvd_mul_left
        change U (i+1) ∣ U m*V
        rw [← eqn]
        exact dvd_mul_of_dvd_right old _
    exact Finset.prod_dvd_of_coprime
      (fun i hi j hj ne => cp i (Finset.mem_range.mp hi).le j (Finset.mem_range.mp hj).le ne)
      (fun i hi => divs i (Finset.mem_range.mp hi))

#print axioms orbit_chain
end KoalaFrontier
