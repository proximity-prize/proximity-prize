import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveGraphGaugeSupportFork6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveAllSeedsGcdSupport6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSFrobeniusHilbert90Normalization6401
open BCHKSFrobeniusGraphHilbert90Audit6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveNormDivisorFork6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveGraphGaugeFork6401
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
noncomputable def primitiveFailureLaneGcd6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (z : F) : Polynomial F :=
  EuclideanDomain.gcd
    (primitiveFailureLaneZero6401 W z)
    (primitiveFailureLaneOne6401 W z)
theorem primitiveFailureLanes_eval_eq_zero_of_allGraphSeedsZero6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hsix : (6 : F) ≠ 0)
    (hall : ∀ t : F, primitiveFamilyGraphGaugeNumerator6401 W t = 0)
    (z : F) (hz : z ∈ rowTwoGoodChallenges6401 W.commonDirection S)
    (i : W.PuncturedIndex) (hi : i ∈ puncturedErrorSupport6401 W z) :
    Polynomial.eval (W.puncturedAlpha i)
          (primitiveFailureLaneZero6401 W z) = 0 ∧
      Polynomial.eval (W.puncturedAlpha i)
          (primitiveFailureLaneOne6401 W z) = 0 := by
  let E := W.puncturedOwnerError z i
  let A0 := primitiveFailureLaneZero6401 W z
  let B0 := primitiveFailureLaneOne6401 W z
  let x := W.puncturedAlpha i
  have hE : E ≠ 0 := (Finset.mem_filter.mp hi).2
  have hx : sigma x = x := hfixed i.1
  have hrel : Polynomial.eval x A0 * sigma E =
      Polynomial.eval x B0 * E := by
    simpa only [A0, B0, E, x, primitiveFailureLaneZero6401,
      primitiveFailureLaneOne6401] using
      (W.puncturedTwoLaneFailureRelation hsigma hfixed z hz i)
  have hordinaryZero : hilbert90Numerator6401 sigma A0 B0 E = 0 := by
    have hgraphZero := congrArg (specializeCoeffZ z) (hall E)
    rw [map_zero] at hgraphZero
    have hspecialize := graphHilbert90Numerator_specialize6401 sigma q6401
      (primitiveBivariateFailureLaneZero6401 W)
      (primitiveBivariateFailureLaneOne6401 W) E z (hsigma z)
    have hmappedZero :
        (graphHilbert90Numerator6401 sigma q6401
          (primitiveBivariateFailureLaneZero6401 W)
          (primitiveBivariateFailureLaneOne6401 W) E).map
            (Polynomial.evalRingHom z) = 0 := by
      simpa [primitiveFamilyGraphGaugeNumerator6401,
        specializeCoeffZ_apply] using hgraphZero
    rw [hspecialize] at hmappedZero
    simpa [A0, B0, ← primitiveBivariateFailureLaneZero_specialize6401 W z,
      ← primitiveBivariateFailureLaneOne_specialize6401 W z,
      specializeCoeffZ_apply] using hmappedZero
  have hevalZero : Polynomial.eval x
      (hilbert90Numerator6401 sigma A0 B0 E) = 0 := by
    rw [hordinaryZero, Polynomial.eval_zero]
  have hproductZero : (6 : F) *
      (Polynomial.eval x (hilbert90Denominator6401 sigma B0) * E) = 0 := by
    rw [← hilbert90Numerator_eval_errorSeed6401 sigma A0 B0 x E hx hrel]
    exact hevalZero
  have hdenominatorZero :
      Polynomial.eval x (hilbert90Denominator6401 sigma B0) = 0 := by
    have hinner :
        Polynomial.eval x (hilbert90Denominator6401 sigma B0) * E = 0 :=
      (mul_eq_zero.mp hproductZero).resolve_left hsix
    exact (mul_eq_zero.mp hinner).resolve_right hE
  have hBzero : Polynomial.eval x B0 = 0 :=
    base_eval_eq_zero_of_hilbert90Denominator_eval_eq_zero6401
      sigma B0 x hx hdenominatorZero
  have hsigmaE : sigma E ≠ 0 := by
    intro hzero
    exact hE (sigma.injective (by simpa using hzero))
  have hAzero : Polynomial.eval x A0 = 0 := by
    rw [hBzero, zero_mul] at hrel
    exact (mul_eq_zero.mp hrel).resolve_right hsigmaE
  exact ⟨hAzero, hBzero⟩
theorem puncturedErrorSupport_subset_laneGcdRoots_of_allGraphSeedsZero6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hsix : (6 : F) ≠ 0)
    (hall : ∀ t : F, primitiveFamilyGraphGaugeNumerator6401 W t = 0)
    (z : F) (hz : z ∈ rowTwoGoodChallenges6401 W.commonDirection S) :
    ∀ i ∈ puncturedErrorSupport6401 W z,
      Polynomial.eval (W.puncturedAlpha i)
        (primitiveFailureLaneGcd6401 W z) = 0 := by
  intro i hi
  have hboth :=
    primitiveFailureLanes_eval_eq_zero_of_allGraphSeedsZero6401
      W hsigma hfixed hsix hall z hz i hi
  exact Polynomial.eval_gcd_eq_zero hboth.1 hboth.2
theorem puncturedErrorSupport_card_le_laneGcdDegree_le_22507_of_allGraphSeedsZero6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hsix : (6 : F) ≠ 0)
    (hall : ∀ t : F, primitiveFamilyGraphGaugeNumerator6401 W t = 0)
    (z : F) (hz : z ∈ rowTwoGoodChallenges6401 W.commonDirection S)
    (hlane : primitiveFailureLaneZero6401 W z ≠ 0 ∨
      primitiveFailureLaneOne6401 W z ≠ 0) :
    (puncturedErrorSupport6401 W z).card ≤
        (primitiveFailureLaneGcd6401 W z).natDegree ∧
      (primitiveFailureLaneGcd6401 W z).natDegree ≤ 22507 := by
  classical
  let D := primitiveFailureLaneGcd6401 W z
  let roots : Finset F :=
    (puncturedErrorSupport6401 W z).map W.puncturedAlpha
  have hDne : D ≠ 0 := by
    intro hzero
    have hboth := (EuclideanDomain.gcd_eq_zero_iff.mp hzero)
    exact hlane.elim (fun h ↦ h hboth.1) (fun h ↦ h hboth.2)
  have hroot : ∀ x ∈ roots, Polynomial.eval x D = 0 := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
    exact puncturedErrorSupport_subset_laneGcdRoots_of_allGraphSeedsZero6401
      W hsigma hfixed hsix hall z hz i hi
  have hcard : roots.card ≤ D.natDegree := by
    by_contra hnot
    have hdegree : D.natDegree < roots.card := by omega
    exact hDne (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      D roots hroot hdegree)
  have hsupportCard : (puncturedErrorSupport6401 W z).card ≤
      D.natDegree := by
    simpa [roots] using hcard
  have hdegrees := primitiveFailureLane_degree_le_22507_6401 W z
  have hDdegree : D.natDegree ≤ 22507 := by
    rcases hlane with hA | hB
    · exact (Polynomial.natDegree_le_of_dvd
        (EuclideanDomain.gcd_dvd_left
          (primitiveFailureLaneZero6401 W z)
          (primitiveFailureLaneOne6401 W z)) hA).trans hdegrees.1
    · exact (Polynomial.natDegree_le_of_dvd
        (EuclideanDomain.gcd_dvd_right
          (primitiveFailureLaneZero6401 W z)
          (primitiveFailureLaneOne6401 W z)) hB).trans hdegrees.2
  exact ⟨by simpa [D] using hsupportCard, by simpa [D] using hDdegree⟩
theorem bothLanesZero_or_errorSupport_card_le_22507_of_allGraphSeedsZero6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hsix : (6 : F) ≠ 0)
    (hall : ∀ t : F, primitiveFamilyGraphGaugeNumerator6401 W t = 0)
    (z : F) (hz : z ∈ rowTwoGoodChallenges6401 W.commonDirection S) :
    (primitiveFailureLaneZero6401 W z = 0 ∧
        primitiveFailureLaneOne6401 W z = 0) ∨
      (puncturedErrorSupport6401 W z).card ≤ 22507 := by
  by_cases hzero : primitiveFailureLaneZero6401 W z = 0 ∧
      primitiveFailureLaneOne6401 W z = 0
  · exact Or.inl hzero
  · right
    have hlane : primitiveFailureLaneZero6401 W z ≠ 0 ∨
        primitiveFailureLaneOne6401 W z ≠ 0 := by
      push_neg at hzero
      by_cases hA : primitiveFailureLaneZero6401 W z = 0
      · exact Or.inr (hzero hA)
      · exact Or.inl hA
    exact (puncturedErrorSupport_card_le_laneGcdDegree_le_22507_of_allGraphSeedsZero6401
      W hsigma hfixed hsix hall z hz hlane).1.trans
        (puncturedErrorSupport_card_le_laneGcdDegree_le_22507_of_allGraphSeedsZero6401
          W hsigma hfixed hsix hall z hz hlane).2
end BCHKSExtremePrimitiveAllSeedsGcdSupport6401
end ProximityPrize.SubmissionLower
