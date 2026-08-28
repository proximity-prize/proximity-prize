import ProximityPrize.Benchmark.TargetLower

namespace ProximityPrize.SubmissionLower

open Polynomial
open Polynomial.Bivariate

variable {F : Type} [Field F]

/-- Specialize the coefficient variable `Z` of a bivariate polynomial. -/
noncomputable def specializeZ (A : F[X][Y]) (z : F) : F[X] :=
  A.map (Polynomial.evalRingHom z)

/-- Evaluation of a bivariate polynomial at the pair `(z,t)`. -/
noncomputable def pairEvalRingHom (z t : F) : F[X][Y] →+* F :=
  (Polynomial.evalRingHom t).comp
    (Polynomial.mapRingHom (Polynomial.evalRingHom z))

@[simp] theorem pairEvalRingHom_apply (A : F[X][Y]) (z t : F) :
    pairEvalRingHom z t A = (specializeZ A z).eval t := by
  rfl

/-- Evaluation on the specialized adjoin-root quotient.  Unlike total
`RatFunc.eval`, this homomorphism has no pole issue: all coefficients are still
polynomial coefficients, and the only required condition is `H(z,t)=0`. -/
noncomputable def specializedAdjoinRootEval
    (H : F[X][Y]) (z t : F) (hroot : (specializeZ H z).eval t = 0) :
    AdjoinRoot (specializeZ H z) →+* F :=
  AdjoinRoot.lift (RingHom.id F) t (by simpa using hroot)

@[simp] theorem specializedAdjoinRootEval_root
    (H : F[X][Y]) (z t : F) (hroot : (specializeZ H z).eval t = 0) :
    specializedAdjoinRootEval H z t hroot
      (AdjoinRoot.root (specializeZ H z)) = t := by
  exact AdjoinRoot.lift_root (by simpa using hroot)

/-- A polynomial coefficient representative in the quotient specializes by
ordinary pair evaluation. -/
theorem specializedAdjoinRootEval_mk
    (H A : F[X][Y]) (z t : F) (hroot : (specializeZ H z).eval t = 0) :
    specializedAdjoinRootEval H z t hroot
      (AdjoinRoot.mk (specializeZ H z) (specializeZ A z)) =
        pairEvalRingHom z t A := by
  rw [specializedAdjoinRootEval, AdjoinRoot.lift_mk]
  rfl

/-- A representative with a polynomial denominator.  It can be specialized at
any pair where that denominator does not vanish, without invoking evaluation
of arbitrary rational functions at a possible pole. -/
structure ClearedPairRepresentative (F : Type) [Field F] where
  numerator : F[X][Y]
  denominator : F[X]

noncomputable def ClearedPairRepresentative.evalAt
    (β : ClearedPairRepresentative F) (z t : F) : F :=
  pairEvalRingHom z t β.numerator / β.denominator.eval z

/-- Cross-multiplication invariance of cleared representatives modulo `H`.
If `e*A-d*B` is a multiple of `H`, then `A/d` and `B/e` have the same value at
every common-root pair away from the two denominator zero sets. -/
theorem clearedRepresentative_evalAt_eq_of_cross_sub_dvd
    (H : F[X][Y]) (β γ : ClearedPairRepresentative F) (z t : F)
    (hroot : pairEvalRingHom z t H = 0)
    (hβden : β.denominator.eval z ≠ 0)
    (hγden : γ.denominator.eval z ≠ 0)
    (hdvd : H ∣ Polynomial.C γ.denominator * β.numerator -
      Polynomial.C β.denominator * γ.numerator) :
    β.evalAt z t = γ.evalAt z t := by
  obtain ⟨Q, hQ⟩ := hdvd
  have hcross := congrArg (pairEvalRingHom z t) hQ
  simp only [map_sub, map_mul] at hcross
  simp only [pairEvalRingHom_apply, specializeZ, Polynomial.map_C,
    Polynomial.eval_C] at hcross
  have hroot' : (specializeZ H z).eval t = 0 := by
    exact hroot
  have hroot'' : (H.map (Polynomial.evalRingHom z)).eval t = 0 := by
    simpa [specializeZ] using hroot'
  rw [hroot'', zero_mul] at hcross
  have hcross' : γ.denominator.eval z * pairEvalRingHom z t β.numerator -
      β.denominator.eval z * pairEvalRingHom z t γ.numerator = 0 := by
    simpa [pairEvalRingHom, specializeZ] using hcross
  have hmul : γ.denominator.eval z * pairEvalRingHom z t β.numerator =
      β.denominator.eval z * pairEvalRingHom z t γ.numerator :=
    sub_eq_zero.mp hcross' 
  unfold ClearedPairRepresentative.evalAt
  apply (div_eq_div_iff hβden hγden).2
  simpa [mul_comm] using hmul

/-- Polynomial identity underlying comparison of a cleared coefficient
`β/d` with a finite Hensel/Taylor coefficient `a`: enough specializations of
`β(z)=d(z)a(z)` force the cleared identity globally. -/
theorem cleared_coefficient_identity_of_many_specializations
    (β d a : F[X]) (S : Finset F) (N : ℕ)
    (hβdeg : β.natDegree ≤ N) (hdadeg : (d * a).natDegree ≤ N)
    (hcard : N < S.card)
    (hvalues : ∀ z ∈ S, β.eval z = d.eval z * a.eval z) :
    β = d * a := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq' β (d * a) S
  · intro z hz
    simpa using hvalues z hz
  · exact (max_le hβdeg hdadeg).trans_lt hcard

/-- After the uniqueness identity has been established, specialization of the
cleared representative equals the Taylor coefficient at every non-pole. -/
theorem cleared_specialization_eq_taylorCoeff
    (β d a : F[X]) (z : F) (hidentity : β = d * a)
    (hden : d.eval z ≠ 0) :
    β.eval z / d.eval z = a.eval z := by
  rw [hidentity, Polynomial.eval_mul]
  exact mul_div_cancel_left₀ (a.eval z) hden

/-- Combined finite-uniqueness form used after a Hensel construction. -/
theorem cleared_specialization_eq_taylorCoeff_of_many
    (β d a : F[X]) (S : Finset F) (N : ℕ)
    (hβdeg : β.natDegree ≤ N) (hdadeg : (d * a).natDegree ≤ N)
    (hcard : N < S.card)
    (hvalues : ∀ z ∈ S, β.eval z = d.eval z * a.eval z)
    (z : F) (hden : d.eval z ≠ 0) :
    β.eval z / d.eval z = a.eval z := by
  apply cleared_specialization_eq_taylorCoeff β d a z
  · exact cleared_coefficient_identity_of_many_specializations β d a S N
      hβdeg hdadeg hcard hvalues
  · exact hden

/-- Standard resultant vanishing for two polynomials with a common root, with
one polynomial known nonzero. -/
theorem resultant_eq_zero_of_common_root_right_ne
    {p q : F[X]} {t : F} (hqne : q ≠ 0)
    (hp : p.eval t = 0) (hq : q.eval t = 0) :
    Polynomial.resultant p q = 0 := by
  rw [Polynomial.resultant_eq_zero_iff]
  refine ⟨Or.inr hqne, ?_⟩
  rintro ⟨a, b, hab⟩
  have heval := congrArg (fun r : F[X] => r.eval t) hab
  simp [Polynomial.eval_add, Polynomial.eval_mul, hp, hq] at heval

/-- Common-root/resultant-zero criterion after specialization.  Monicity of
`H` prevents its declared degree from dropping under specialization. -/
theorem bivariate_resultant_specialization_eq_zero_of_common_root
    (B H : F[X][Y]) (n m : ℕ) (z t : F)
    (hBdeg : B.natDegree ≤ n) (hHmonic : H.Monic)
    (hHdeg : H.natDegree = m)
    (hBroot : (specializeZ B z).eval t = 0)
    (hHroot : (specializeZ H z).eval t = 0) :
    (Polynomial.resultant B H n m).eval z = 0 := by
  rw [show (Polynomial.resultant B H n m).eval z =
      Polynomial.resultant (specializeZ B z) (specializeZ H z) n m by
    simp [specializeZ]]
  have hstd : Polynomial.resultant (specializeZ B z) (specializeZ H z) = 0 :=
    resultant_eq_zero_of_common_root_right_ne
      ((hHmonic.map (Polynomial.evalRingHom z)).ne_zero) hBroot hHroot
  have hn : (specializeZ B z).natDegree +
      (n - (specializeZ B z).natDegree) = n :=
    Nat.add_sub_of_le (Polynomial.natDegree_map_le.trans hBdeg)
  have hm : (specializeZ H z).natDegree = m :=
    (hHmonic.natDegree_map (Polynomial.evalRingHom z)).trans hHdeg
  rw [← hn, ← hm, Polynomial.resultant_add_left_deg]
  · simp [hstd]
  · exact le_rfl

end ProximityPrize.SubmissionLower
