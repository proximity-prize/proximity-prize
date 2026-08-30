import ProximityPrize.SubmissionLower.PlaneResultantPointCount

namespace ProximityPrize.SubmissionLower.PlaneResultantIrreducible

noncomputable section

variable {K : Type} [Field K] [DecidableEq K]

omit [DecidableEq K] in
theorem inner_linear_C_dvd_of_specialization_eq_zero
    (P : Polynomial (Polynomial K)) (alpha : K)
    (hzero : P.map (Polynomial.evalRingHom alpha) = 0) :
    Polynomial.C (Polynomial.X - Polynomial.C alpha) ∣ P := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro i
  apply Polynomial.dvd_iff_isRoot.mpr
  have hcoeff := congrArg (fun Q : Polynomial K => Q.coeff i) hzero
  simpa using hcoeff

omit [DecidableEq K] in
theorem primitive_specialization_ne_zero
    (P : Polynomial (Polynomial K)) (hprimitive : P.IsPrimitive) (alpha : K) :
    P.map (Polynomial.evalRingHom alpha) ≠ 0 := by
  intro hzero
  exact Polynomial.not_isUnit_X_sub_C alpha
    (hprimitive _ (inner_linear_C_dvd_of_specialization_eq_zero P alpha hzero))

omit [DecidableEq K] in
theorem primitive_irreducible_dvd_of_resultant_eq_zero
    (P Q : Polynomial (Polynomial K))
    (hprimitive : P.IsPrimitive) (hirreducible : Irreducible P)
    (hresultant : Polynomial.resultant P Q P.natDegree Q.natDegree = 0) : P ∣ Q := by
  classical
  let F := FractionRing (Polynomial K)
  let f : Polynomial K →+* F := algebraMap (Polynomial K) F
  have hf : Function.Injective f := IsFractionRing.injective (Polynomial K) F
  have hPdegree : (P.map f).natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf P
  have hQdegree : (Q.map f).natDegree = Q.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hf Q
  have hfixed : Polynomial.resultant (P.map f) (Q.map f)
      P.natDegree Q.natDegree = 0 := by
    rw [Polynomial.resultant_map_map, hresultant, map_zero]
  have hresF : Polynomial.resultant (P.map f) (Q.map f) = 0 := by
    simpa only [hPdegree, hQdegree] using hfixed
  have hnotCoprime : ¬ IsCoprime (P.map f) (Q.map f) :=
    (Polynomial.resultant_eq_zero_iff.mp hresF).2
  have hirreducibleF : Irreducible (P.map f) :=
    hprimitive.irreducible_iff_irreducible_map_fraction_map.mp hirreducible
  have hdivF : P.map f ∣ Q.map f :=
    (Irreducible.dvd_iff_not_isCoprime hirreducibleF).mpr hnotCoprime
  exact hprimitive.dvd_of_fraction_map_dvd_fraction_map hdivF

omit [DecidableEq K] in
theorem irreducible_resultant_ne_zero_of_not_dvd
    (P Q : Polynomial (Polynomial K)) (hirreducible : Irreducible P)
    (hdegree : 0 < P.natDegree) (hproper : ¬ P ∣ Q) :
    Polynomial.resultant P Q P.natDegree Q.natDegree ≠ 0 := by
  intro hresultant
  exact hproper (primitive_irreducible_dvd_of_resultant_eq_zero P Q
    (hirreducible.isPrimitive (Nat.ne_of_gt hdegree)) hirreducible hresultant)

end

end ProximityPrize.SubmissionLower.PlaneResultantIrreducible
