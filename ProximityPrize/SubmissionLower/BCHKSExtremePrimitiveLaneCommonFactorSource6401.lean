import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveLaneResultantFork6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveLaneCommonFactorSource6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSTwoFrobeniusThreeShiftPrimitive6401
open BCHKSThreeShiftSourceWindow6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveGraphGaugeSupportFork6401
open BCHKSExtremePrimitiveLaneResultantFork6401
set_option maxHeartbeats 5000000
set_option maxRecDepth 1000000
noncomputable def primitiveCommonFactorFixedRootCoordinates6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (H : F[X][X]) : Finset (Fin n6401) :=
  Finset.univ.filter fun i => evalOuterAt (alpha i) H = 0
theorem integralCommonFactor_nonzeroAt_unpuncturedCoordinate6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (H : F[X][X])
    (hH0 : H ∣ primitiveBivariateFailureLaneZero6401 W)
    (hH1 : H ∣ primitiveBivariateFailureLaneOne6401 W)
    (i : Fin n6401) (hi : i ∉ W.sourcePuncture.badCoordinates) :
    evalOuterAt (alpha i) H ≠ 0 := by
  intro hHzero
  have htwo : evalOuterAt (alpha i)
      (W.sourcePuncture.frame.reduced 2) = 0 := by
    rcases hH0 with ⟨Q, hQ⟩
    have hQeval := congrArg (evalOuterAt (alpha i)) hQ
    simp only [primitiveBivariateFailureLaneZero6401, evalOuterAt,
      Polynomial.eval_mul] at hQeval
    unfold evalOuterAt at hHzero ⊢
    rw [hHzero, zero_mul] at hQeval
    exact hQeval
  have hone : evalOuterAt (alpha i)
      (W.sourcePuncture.frame.reduced 1) = 0 := by
    rcases hH1 with ⟨Q, hQ⟩
    have hQeval := congrArg (evalOuterAt (alpha i)) hQ
    simp only [primitiveBivariateFailureLaneOne6401, evalOuterAt,
      Polynomial.eval_neg, Polynomial.eval_mul] at hQeval
    unfold evalOuterAt at hHzero ⊢
    rw [hHzero, zero_mul] at hQeval
    exact neg_eq_zero.mp hQeval
  rcases primitive_homogeneous_evaluations_not_both_zero
      W.sourcePuncture.frame sigma i (Finset.mem_univ i) (u0 i) (u1 i)
        (W.sourcePuncture.source_relation i hi) with h | h
  · exact h hone
  · exact h htwo
theorem primitiveCommonFactorFixedRootCoordinates_subset_bad6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (H : F[X][X])
    (hH0 : H ∣ primitiveBivariateFailureLaneZero6401 W)
    (hH1 : H ∣ primitiveBivariateFailureLaneOne6401 W) :
    primitiveCommonFactorFixedRootCoordinates6401 W H ⊆
      W.sourcePuncture.badCoordinates := by
  intro i hi
  by_contra hibad
  have hroot : evalOuterAt (alpha i) H = 0 := by
    exact (Finset.mem_filter.mp hi).2
  exact integralCommonFactor_nonzeroAt_unpuncturedCoordinate6401
    W H hH0 hH1 i hibad hroot
theorem primitiveCommonFactorFixedRootCoordinates_card_le_22507_6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (H : F[X][X])
    (hH0 : H ∣ primitiveBivariateFailureLaneZero6401 W)
    (hH1 : H ∣ primitiveBivariateFailureLaneOne6401 W) :
    (primitiveCommonFactorFixedRootCoordinates6401 W H).card ≤ 22507 := by
  exact (Finset.card_le_card
    (primitiveCommonFactorFixedRootCoordinates_subset_bad6401
      W H hH0 hH1)).trans W.sourcePuncture.badCoordinates_card
theorem integralCommonFactor_specializes_dvd_homogeneous6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (H : F[X][X])
    (hH0 : H ∣ primitiveBivariateFailureLaneZero6401 W)
    (hH1 : H ∣ primitiveBivariateFailureLaneOne6401 W)
    (z : F) :
    specializeCoeffZ z H ∣
        specializeRow z W.sourcePuncture.frame.reduced 1 ∧
      specializeCoeffZ z H ∣
        specializeRow z W.sourcePuncture.frame.reduced 2 := by
  constructor
  · have hmap := Polynomial.map_dvd (Polynomial.evalRingHom z) hH1
    simpa [primitiveBivariateFailureLaneOne6401, specializeRow,
      specializeCoeffZ] using hmap
  · have hmap := Polynomial.map_dvd (Polynomial.evalRingHom z) hH0
    simpa [primitiveBivariateFailureLaneZero6401, specializeRow,
      specializeCoeffZ] using hmap
theorem integralCommonFactor_specializes_dvd_ownerRow6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (H : F[X][X])
    (hH0 : H ∣ primitiveBivariateFailureLaneZero6401 W)
    (hH1 : H ∣ primitiveBivariateFailureLaneOne6401 W)
    (z : F) (hz : z ∈ rowTwoGoodChallenges6401 W.commonDirection S) :
    ∀ j, specializeCoeffZ z H ∣
      specializeRow z W.sourcePuncture.frame.reduced j := by
  rcases integralCommonFactor_specializes_dvd_homogeneous6401
    W H hH0 hH1 z with ⟨hone, htwo⟩
  intro j
  fin_cases j
  · have hsum : specializeCoeffZ z H ∣
        specializeRow z W.sourcePuncture.frame.reduced 1 * P z +
          specializeRow z W.sourcePuncture.frame.reduced 2 *
            (P z).map sigma :=
      dvd_add (dvd_mul_of_dvd_left hone _) (dvd_mul_of_dvd_left htwo _)
    have hrelation := W.owner_relation z hz
    unfold symbolicRelation at hrelation
    have hzero : specializeRow z W.sourcePuncture.frame.reduced 0 =
        -(specializeRow z W.sourcePuncture.frame.reduced 1 * P z +
          specializeRow z W.sourcePuncture.frame.reduced 2 *
            (P z).map sigma) := by
      linear_combination hrelation
    have hdivzero : specializeCoeffZ z H ∣
        specializeRow z W.sourcePuncture.frame.reduced 0 := by
      rw [hzero]
      exact dvd_neg.mpr hsum
    simpa using hdivzero
  · exact hone
  · exact htwo
structure PrimitiveLaneCommonFactorSource6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P) where
  factor : F[X][X]
  primitive : factor.IsPrimitive
  positiveLocatorDegree : 0 < factor.natDegree
  locatorDegree_le : factor.natDegree ≤ 22507
  dividesLaneZero : factor ∣ primitiveBivariateFailureLaneZero6401 W
  dividesLaneOne : factor ∣ primitiveBivariateFailureLaneOne6401 W
  fixedRoots_subset_bad :
    primitiveCommonFactorFixedRootCoordinates6401 W factor ⊆
      W.sourcePuncture.badCoordinates
  specializes_dvd_ownerRow : ∀ z ∈
      rowTwoGoodChallenges6401 W.commonDirection S, ∀ j,
    specializeCoeffZ z factor ∣
      specializeRow z W.sourcePuncture.frame.reduced j
theorem exists_primitiveLaneCommonFactorSource_of_resultant_eq_zero6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (hresultant : primitiveLaneResultant6401 W = 0) :
    Nonempty (PrimitiveLaneCommonFactorSource6401 W) := by
  obtain ⟨H, hprimitive, hpositive, hdegree, hH0, hH1⟩ :=
    exists_integralPrimitiveCommonFactor_of_primitiveLaneResultant_eq_zero6401
      W hresultant
  exact ⟨{
    factor := H
    primitive := hprimitive
    positiveLocatorDegree := hpositive
    locatorDegree_le := hdegree
    dividesLaneZero := hH0
    dividesLaneOne := hH1
    fixedRoots_subset_bad :=
      primitiveCommonFactorFixedRootCoordinates_subset_bad6401
        W H hH0 hH1
    specializes_dvd_ownerRow :=
      integralCommonFactor_specializes_dvd_ownerRow6401
        W H hH0 hH1 }⟩
theorem primitiveLaneResultant_or_sourceCommonFactor6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (T : Finset F) :
    ((primitiveBivariateFailureLaneZero6401 W).natDegree = 0 ∧
      (primitiveBivariateFailureLaneOne6401 W).natDegree = 0) ∨
    (primitiveLaneResultant6401 W = 0 ∧
      Nonempty (PrimitiveLaneCommonFactorSource6401 W)) ∨
    (primitiveLaneResultant6401 W ≠ 0 ∧
      (noncoprimePrimitiveOwners6401 W T).card ≤
        primitiveLaneResultantChallengeCap6401) := by
  rcases primitiveLaneResultant_or_fractionCommonFactor6401 W T with
    hconstant | hzero | hnonzero
  · exact Or.inl hconstant
  · exact Or.inr (Or.inl ⟨hzero.1,
      exists_primitiveLaneCommonFactorSource_of_resultant_eq_zero6401
        W hzero.1⟩)
  · exact Or.inr (Or.inr hnonzero)
end BCHKSExtremePrimitiveLaneCommonFactorSource6401
end ProximityPrize.SubmissionLower
