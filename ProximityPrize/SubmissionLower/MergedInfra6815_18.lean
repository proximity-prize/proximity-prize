import ProximityPrize.SubmissionLower.MergedInfra6815_10

set_option Elab.async false
section MergedPart0
namespace ProximityPrize.SubmissionLower.MovingFiberLeadingCoefficient6815
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetSpecialize
open SecondJetCoefficients SecondJetCoefficientSpecialization SecondJetDifferentiation
open SecondJetRelaxedDifferentiation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K N : Type*} [Field K]

theorem coefficient_monomial_degree (f : Polynomial K) (z : K) (w : ℕ)
    (hf : f.natDegree ≤ w) (e : Fin 4 →₀ ℕ) (c : K) :
    (coefficientSpecialize f z (MvPolynomial.monomial e c)).natDegree ≤
      e 0+w*e 1+(w-1)*e 2 := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  · simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, map_mul, map_pow]
    have hc : (coefficientSpecialize f z (MvPolynomial.C c)).natDegree ≤ 0 := by
      simp [coefficientSpecialize]
    have h0 : (coefficientSpecialize f z (MvPolynomial.X 0)^e 0).natDegree ≤ e 0 := by
      simp [coefficientSpecialize]
    have h1 : (coefficientSpecialize f z (MvPolynomial.X 1)^e 1).natDegree ≤ e 1*w := by
      simpa [coefficientSpecialize] using Polynomial.natDegree_pow_le_of_le (e 1) hf
    have h2 : (coefficientSpecialize f z (MvPolynomial.X 2)^e 2).natDegree ≤ e 2*(w-1) := by
      simpa [coefficientSpecialize] using Polynomial.natDegree_pow_le_of_le (e 2)
        ((Polynomial.natDegree_derivative_le f).trans (Nat.sub_le_sub_right hf 1))
    have h3 : (coefficientSpecialize f z (MvPolynomial.X 3)^e 3).natDegree ≤ 0 := by
      simp [coefficientSpecialize]
    have hh := Polynomial.natDegree_mul_le_of_le hc (Polynomial.natDegree_mul_le_of_le h0
      (Polynomial.natDegree_mul_le_of_le h1 (Polynomial.natDegree_mul_le_of_le h2 h3)))
    simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc,Nat.mul_comm] using hh
  · intro i
    simp

theorem coefficient_degree (P : MvPolynomial (Fin 4) K) (f : Polynomial K)
    (z : K) (w D : ℕ) (hf : f.natDegree ≤ w) (hD : 0 < D)
    (hP : ∀ e ∈ P.support, e 0+w*e 1+(w-1)*e 2 < D) :
    (coefficientSpecialize f z P).natDegree < D := by
  classical
  have ht : ∀ e ∈ P.support,
      (coefficientSpecialize f z (MvPolynomial.monomial e (AddMonoidAlgebra.coeff P e))).natDegree ≤ D-1 := by
    intro e he
    have hh := coefficient_monomial_degree f z w hf e (AddMonoidAlgebra.coeff P e)
    have hb := hP e he
    omega
  rw [MvPolynomial.as_sum P, map_sum]
  have hh := Polynomial.natDegree_sum_le_of_forall_le P.support
    (fun e => coefficientSpecialize f z (MvPolynomial.monomial e (AddMonoidAlgebra.coeff P e))) ht
  omega

theorem iterate_derivative_top {R : Type*} [CommRing R] (P : Polynomial R) (d : ℕ)
    (hh : ∀ j, d < j → P.coeff j = 0) :
    (Polynomial.derivative)^[d] P = Polynomial.C (d.factorial • P.coeff d) := by
  ext j
  rw [Polynomial.coeff_iterate_derivative]
  by_cases hj : j = 0
  · subst j
    simp [Nat.descFactorial_self]
  · rw [hh (j+d) (by omega)]
    simp [hj]

theorem specialize_top (P : Poly (K := K)) (f : Polynomial K) (z : K) (d : ℕ)
    (hh : ∀ j, d < j → coefficientSpecialize f z ((asS P).coeff j) = 0) :
    specialize f z ((pderiv 1)^[d] P) =
      d.factorial • coefficientSpecialize f z ((asS P).coeff d) := by
  rw [specialize_eq, asS_iterate, ← Polynomial.eval_map, ← Polynomial.iterate_derivative_map]
  rw [iterate_derivative_top _ d (by intro j hj; simpa using hh j hj)]
  simp

end
end ProximityPrize.SubmissionLower.MovingFiberLeadingCoefficient6815
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.MovingFiberTotalAvoidance6815
open MvPolynomial SecondJetSupport SecondJetCoefficients SecondJetCoefficientSpecialization
open SecondJetClearedHelper SecondJetHelperWeights
open SecondJetRelaxedCoefficientsReceipt RCN234 RCN156
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option maxRecDepth 100000
variable {K N : Type*} [Field K] [Fintype N]

end
end ProximityPrize.SubmissionLower.MovingFiberTotalAvoidance6815
end MergedPart1
section MergedPart2
namespace ProximityPrize.SubmissionLower.Lower80899.Selection
open ProximityPrize.Benchmark RCN100 RCN119 RCN101 RCN180 RCN181 RCN137 RCN183
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

end
end ProximityPrize.SubmissionLower.Lower80899.Selection

namespace ProximityPrize.SubmissionLower.Lower80899.Caps
open ProximityPrize.Benchmark RCN100 RCN119 RCN180 RCN081 RCN234 RCN156 RCN130
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

end
end Caps
end ProximityPrize.SubmissionLower.Lower80899

namespace ProximityPrize.SubmissionLower.Lower80899.Selection.SelectedPair
open RCN100 RCN180 RCN234 RCN156
noncomputable section

end
end ProximityPrize.SubmissionLower.Lower80899.Selection.SelectedPair
end MergedPart2
