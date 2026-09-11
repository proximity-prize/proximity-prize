import ProximityPrize.SubmissionLower.Part.G040


section Compact_SecondJetFlagCoefficients
/-! Frozen coefficient flags for the second-jet interpolant. -/
namespace ProximityPrize.SubmissionLower.SecondJetFlagCoefficients
open scoped BigOperators
open MvPolynomial RCN095 SecondJetCoefficients SecondJetSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K : Type*} [Field K]

def freeze (x : K) : MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 3) K :=
  MvPolynomial.aeval ![MvPolynomial.C x,MvPolynomial.X 0,MvPolynomial.X 1,MvPolynomial.X 2]

theorem freeze_monomial (x : K) (d : Fin 4 →₀ ℕ) (c : K) :
    freeze x (MvPolynomial.monomial d c) = MvPolynomial.monomial d.tail (c*x^d 0) := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  · rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
    · simp [freeze, Fin.prod_univ_four, Fin.prod_univ_three, Finsupp.tail_apply,
        map_mul, map_pow, mul_assoc]
    · intro i
      simp
  · intro i
    simp

theorem freeze_inFlag (P : MvPolynomial (Fin 4) K) (x : K) (p : FlagDegree)
    (hP : ∀ d ∈ P.support, InFlag p d.tail) : PolynomialInFlag p (freeze x P) := by
  rw [MvPolynomial.as_sum P, map_sum]
  intro e he
  obtain ⟨d,hd,hed⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum he)
  rw [freeze_monomial] at hed
  have heq : e = d.tail := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hed)
  subst e
  exact hP d hd

theorem frozen_coefficient_flag (P : Poly (K := K)) (x : K)
    (hP : ∀ e ∈ P.support, e 1+e 3 ≤ 39 ∧ e 1 ≤ 18 ∧ e 1+e 2+e 3+e 4 ≤ 2160 ∧
      e 0+131071*e 2+131070*e 3+131069*e 1 < 21611508) (j : ℕ) :
    PolynomialInFlag (⟨1996,125,39-j⟩ : FlagDegree) (freeze x ((asS (K := K) P).coeff j)) := by
  apply freeze_inFlag
  intro d hd
  have hb := coefficient_bounds P hP j d hd
  change d 2 ≤ 39-j ∧ d 1+d 2 ≤ 125+(39-j) ∧ d 1+d 2+d 3 ≤ 1996+125+(39-j)
  omega

end
end ProximityPrize.SubmissionLower.SecondJetFlagCoefficients

end Compact_SecondJetFlagCoefficients
