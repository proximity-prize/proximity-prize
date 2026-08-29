import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.PlaneResultantPointCount


/-!
# Proper cuts of irreducible positive-outer-degree plane curves

Model label: gpt-5.

The previous point-count theorem requires a nonzero resultant and excludes
whole zero fibers explicitly. Here both conditions are proved for an
irreducible first polynomial of positive outer degree and a second
polynomial not divisible by it. No monicity assumption is used.

The intermediate specialization theorem holds for every primitive
polynomial over K[X]. Gauss's lemma transfers irreducibility to K(X),
where vanishing resultant forces divisibility; primitivity descends that
divisibility. Resultants use the actual original outer degrees: padding
both caps arbitrarily is not asserted to preserve nonvanishing.

This proves a finite planar distinct-point bound. It does not supply the
remaining mixed three-factor curve-degree ledger or an alignment theorem.
-/

namespace ProximityPrize.SubmissionLower.PlaneResultantIrreducible

noncomputable section

variable {K : Type} [Field K] [DecidableEq K]

/-- If every outer coefficient vanishes at alpha, the inner linear factor
divides every coefficient and hence divides the whole polynomial as an
outer constant. -/
theorem inner_linear_C_dvd_of_specialization_eq_zero
    (P : Polynomial (Polynomial K)) (alpha : K)
    (hzero : P.map (Polynomial.evalRingHom alpha) = 0) :
    Polynomial.C (Polynomial.X - Polynomial.C alpha) ∣ P := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro i
  apply Polynomial.dvd_iff_isRoot.mpr
  have hcoeff := congrArg (fun Q : Polynomial K => Q.coeff i) hzero
  simpa using hcoeff

/-- A primitive polynomial over K[X] has no identically zero scalar fiber.
This is stronger than only excluding zero fibers of irreducible curves. -/
theorem primitive_specialization_ne_zero
    (P : Polynomial (Polynomial K)) (hprimitive : P.IsPrimitive) (alpha : K) :
    P.map (Polynomial.evalRingHom alpha) ≠ 0 := by
  intro hzero
  exact Polynomial.not_isUnit_X_sub_C alpha
    (hprimitive _ (inner_linear_C_dvd_of_specialization_eq_zero P alpha hzero))

/-- Positive outer degree makes an irreducible bivariate polynomial
primitive, so none of its scalar fibers is the whole zero polynomial. -/
theorem irreducible_specialization_ne_zero
    (P : Polynomial (Polynomial K)) (hirreducible : Irreducible P)
    (hdegree : 0 < P.natDegree) (alpha : K) :
    P.map (Polynomial.evalRingHom alpha) ≠ 0 := by
  exact primitive_specialization_ne_zero P
    (hirreducible.isPrimitive (Nat.ne_of_gt hdegree)) alpha

/-- Non-monic primitive version of the stock fraction-field resultant
argument. Vanishing of the actual-degree resultant forces an irreducible
primitive first polynomial to divide the second. -/
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

/-- A proper cut of an irreducible positive-outer-degree plane curve has
a nonzero resultant at the actual original degrees, without monicity. -/
theorem irreducible_resultant_ne_zero_of_not_dvd
    (P Q : Polynomial (Polynomial K)) (hirreducible : Irreducible P)
    (hdegree : 0 < P.natDegree) (hproper : ¬ P ∣ Q) :
    Polynomial.resultant P Q P.natDegree Q.natDegree ≠ 0 := by
  intro hresultant
  exact hproper (primitive_irreducible_dvd_of_resultant_eq_zero P Q
    (hirreducible.isPrimitive (Nat.ne_of_gt hdegree)) hirreducible hresultant)

/-- Actual finite planar Bezout bound for a proper cut of an irreducible
positive-outer-degree curve. Nonzero resultant and absence of whole vertical
fibers are conclusions of the preceding algebra, not extra assumptions. -/
theorem irreducible_common_points_card_le_bidegree_bound
    (P Q : Polynomial (Polynomial K)) (points : Finset (K × K))
    (hirreducible : Irreducible P) (hdegree : 0 < P.natDegree)
    (hproper : ¬ P ∣ Q)
    (hroots : ∀ point ∈ points,
      (P.map (Polynomial.evalRingHom point.1)).eval point.2 = 0 ∧
      (Q.map (Polynomial.evalRingHom point.1)).eval point.2 = 0) :
    points.card ≤ Q.natDegree * Polynomial.Bivariate.degreeX P +
      P.natDegree * Polynomial.Bivariate.degreeX Q := by
  apply PlaneResultantPointCount.common_points_card_le_bidegree_bound
    P Q P.natDegree Q.natDegree points le_rfl le_rfl
  · exact irreducible_resultant_ne_zero_of_not_dvd P Q hirreducible hdegree hproper
  · intro point _
    exact Or.inl (irreducible_specialization_ne_zero P hirreducible hdegree point.1)
  · exact hroots

end

end ProximityPrize.SubmissionLower.PlaneResultantIrreducible
