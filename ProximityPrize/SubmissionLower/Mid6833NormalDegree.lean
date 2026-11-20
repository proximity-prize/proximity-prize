/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833Global
namespace ProximityPrize.SubmissionLower.K6969Global
open Koala6831Comparison Koala6831Ordinary Koala6831Separation Koala6831SeparationFactors
open Koala6831CoefficientSystem (coefficientPolynomial)
open MvPolynomial
open scoped Polynomial Classical
noncomputable section
variable {K : Type} [Field K]

private theorem same_coeff (P : SeedCoefficients K) (m : Fin 2 →₀ ℕ) (j : ℕ) :
    ((regroup P).coeff m).coeff j=(P.coeff j).coeff m := by
  rw [coeff_regroup_eq _ _ _ le_rfl]
  unfold coefficientPolynomial
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial,Finset.sum_ite_eq',Finset.mem_range]
  split_ifs with h
  · rfl
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree<j)]
    simp

private theorem seed_degree (P : SeedCoefficients K) (i : Fin 2) (j : ℕ) :
    (P.coeff j).degreeOf i≤(regroup P).degreeOf i := by
  apply degreeOf_le_iff.mpr
  intro m hm
  apply le_degreeOf_of_mem_support i
  apply MvPolynomial.mem_support_iff.mpr
  intro z
  apply (MvPolynomial.mem_support_iff.mp hm)
  rw [←same_coeff P m j,z,Polynomial.coeff_zero]

private theorem aff_degree (a b : K[X]) (i j : Fin 2) :
    (affine i a b).degreeOf j ≤ if i=j then 1 else 0 := by
  unfold affine
  refine (degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
  · simp
  · refine (degreeOf_mul_le _ _ _).trans ?_
    by_cases eq : i=j
    · subst i; simp
    · simp [eq,degreeOf_X_of_ne (Ne.symm eq)]

/-- Normal forms have combined seed/value degree at most two, regardless of their x degree. -/
theorem normal_degree {q : SymbolicRow (SeedRing K)} {w δ : ℕ} (N : NormalForm q w δ) :
    combinedDegree q≤2 := by
  have fa (i : Fin 2) : (regroup q.first).degreeOf i≤ (if (1:Fin 2)=i then 1 else 0) := by
    rw [N.first_eq]
    exact (degreeOf_mul_le _ _ _).trans (by simpa using aff_degree (N.B 0) (N.B 1) 1 i)
  have fb (i : Fin 2) : (regroup q.second).degreeOf i≤ (if (0:Fin 2)=i then 1 else 0) := by
    rw [N.second_eq,degreeOf_neg]
    exact (degreeOf_mul_le _ _ _).trans (by simpa using aff_degree (N.A 0) (N.A 1) 0 i)
  have bz (i : Fin 2) : (regroup q.beta).degreeOf i≤1 := by
    rw [N.beta_eq]
    apply (degreeOf_add_le _ _ _).trans
    apply max_le
    · apply (degreeOf_mul_le _ _ _).trans
      have d := Nat.add_le_add (aff_degree (N.C 0) (N.C 1) 0 i) (aff_degree (N.B 0) (N.B 1) 1 i)
      fin_cases i <;> simpa using d
    · apply (degreeOf_mul_le _ _ _).trans
      have d := Nat.add_le_add (aff_degree (N.A 0) (N.A 1) 0 i) (aff_degree (N.D 0) (N.D 1) 1 i)
      fin_cases i <;> simpa using d
  have b := liftedCoefficient_total_weight_le q.beta 1 1 (fun j => (seed_degree _ _ j).trans (bz 0))
    (fun j => (seed_degree _ _ j).trans (bz 1))
  have a := liftedCoefficient_total_weight_le q.first 0 1 (fun j => (seed_degree _ _ j).trans (fa 0))
    (fun j => (seed_degree _ _ j).trans (fa 1))
  have c := liftedCoefficient_total_weight_le q.second 1 0 (fun j => (seed_degree _ _ j).trans (fb 0))
    (fun j => (seed_degree _ _ j).trans (fb 1))
  unfold combinedDegree
  rw [primitiveRowLift_weight_max]
  apply max_le (max_le b ?_) ?_
  · exact (weight_mul_le _ _ _).trans (by rw [weight_X];exact Nat.add_le_add a (show totalWeights 1≤1 by decide))
  · exact (weight_mul_le _ _ _).trans (by rw [weight_X];exact Nat.add_le_add c (show totalWeights 2≤1 by decide))

#print axioms normal_degree
end
end ProximityPrize.SubmissionLower.K6969Global
