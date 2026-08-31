import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactTaylorNumerators
import ProximityPrize.SubmissionLower.ContactTranslation

 












namespace ProximityPrize.SubmissionLower
namespace ContactIteratedDerivativeDegree6700Research

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

variable {K : Type*} [Field K]

 

theorem support_before_iterate_pderiv
    (i : Fin 4) (q : ℕ) (F : MvPolynomial (Fin 4) K)
    (d : Fin 4 →₀ ℕ)
    (hd : d ∈ ((MvPolynomial.pderiv i)^[q] F).support) :
    d + Finsupp.single i q ∈ F.support := by
  induction q generalizing d F with
  | zero => simpa using hd
  | succ q ih =>
      rw [Function.iterate_succ_apply'] at hd
      have hprev := ContactTaylorNumerators.support_before_pderiv
        i ((MvPolynomial.pderiv i)^[q] F) d hd
      have hsource := ih (F := F) (d := d + Finsupp.single i 1) hprev
      convert hsource using 1
      ext j
      simp only [Finsupp.add_apply, Finsupp.single_apply]
      split_ifs <;> omega

 




theorem specialization_iterate_pderiv_R_natDegree_add_lt
    (D w seedCap slopeCap q : ℕ)
    (F : MvPolynomial (Fin 4) K) (P : Polynomial K) (gamma : K)
    (hweight : q * (w - 1) < D)
    (hcaps : F ∈ ContactInterpolation.globalCoefficientBox K
      D w seedCap slopeCap)
    (hP : P.natDegree ≤ w) :
    (ContactTranslation.specialization K P gamma
      ((MvPolynomial.pderiv (2 : Fin 4))^[q] F)).natDegree +
        q * (w - 1) < D := by
  classical
  let G := (MvPolynomial.pderiv (2 : Fin 4))^[q] F
  have hsupport : ∀ d ∈ F.support,
      d 1 + d 3 ≤ seedCap ∧ d 2 ≤ slopeCap ∧
        d 0 + w * d 1 + (w - 1) * d 2 < D := hcaps
  have hterms : ∀ d ∈ G.support,
      (ContactTranslation.specialization K P gamma
        (MvPolynomial.monomial d (MvPolynomial.coeff d G))).natDegree ≤
          D - q * (w - 1) - 1 := by
    intro d hd
    have hdsource := support_before_iterate_pderiv
      (K := K) (2 : Fin 4) q F d hd
    have hsource :=
      (hsupport (d + Finsupp.single (2 : Fin 4) q) hdsource).2.2
    have hmonomial :=
      ContactTranslation.specialization_monomial_natDegree_le
        K P gamma w hP d (MvPolynomial.coeff d G)
    simp [Finsupp.add_apply] at hsource
    rw [Nat.mul_add] at hsource
    rw [Nat.mul_comm (w - 1) q] at hsource
    omega
  change (ContactTranslation.specialization K P gamma G).natDegree +
    q * (w - 1) < D
  rw [MvPolynomial.as_sum G, map_sum]
  have hsum := Polynomial.natDegree_sum_le_of_forall_le G.support
    (fun d => ContactTranslation.specialization K P gamma
      (MvPolynomial.monomial d (MvPolynomial.coeff d G))) hterms
  omega

 

theorem specialization_iterate_pderiv_R_6700
    (F : MvPolynomial (Fin 4) K) (P : Polynomial K) (gamma : K)
    (q : ℕ) (hq : q ≤ 13)
    (hcaps : F ∈ ContactInterpolation.globalCoefficientBox K
      8206965 131071 937 13)
    (hP : P.natDegree ≤ 131071) :
    (ContactTranslation.specialization K P gamma
      ((MvPolynomial.pderiv (2 : Fin 4))^[q] F)).natDegree +
        q * 131070 < 8206965 := by
  have hweight : q * (131071 - 1) < 8206965 := by omega
  simpa using specialization_iterate_pderiv_R_natDegree_add_lt
    (K := K) 8206965 131071 937 13 q F P gamma hweight hcaps hP

end

end ContactIteratedDerivativeDegree6700Research
end ProximityPrize.SubmissionLower

#print axioms ProximityPrize.SubmissionLower.ContactIteratedDerivativeDegree6700Research.support_before_iterate_pderiv
#print axioms ProximityPrize.SubmissionLower.ContactIteratedDerivativeDegree6700Research.specialization_iterate_pderiv_R_natDegree_add_lt
#print axioms ProximityPrize.SubmissionLower.ContactIteratedDerivativeDegree6700Research.specialization_iterate_pderiv_R_6700
