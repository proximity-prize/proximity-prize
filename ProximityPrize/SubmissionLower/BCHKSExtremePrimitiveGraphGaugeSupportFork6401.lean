import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveGraphGaugeFork6401
import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveSupportEnvelope6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveGraphGaugeSupportFork6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveNormDivisorFork6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveGraphGaugeFork6401
open BCHKSExtremePrimitiveSupportEnvelope6401
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
theorem puncturedErrorSupport_eq_empty_of_allGraphSeedsZero_of_coprime6401
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
    (hcoprime : IsCoprime
      (specializeCoeffZ z (primitiveBivariateFailureLaneZero6401 W))
      (specializeCoeffZ z (primitiveBivariateFailureLaneOne6401 W))) :
    puncturedErrorSupport6401 W z = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have herror : W.puncturedOwnerError z i ≠ 0 :=
    (Finset.mem_filter.mp hi).2
  exact (primitiveFamilyGraphGaugeNumerator_ne_zero_of_anchor6401
    W hsigma hfixed z hz i herror hsix hcoprime)
      (hall (W.puncturedOwnerError z i))
noncomputable def noncoprimePrimitiveOwners6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (T : Finset F) : Finset F := by
  classical
  exact T.filter fun z => ¬ IsCoprime
    (specializeCoeffZ z (primitiveBivariateFailureLaneZero6401 W))
    (specializeCoeffZ z (primitiveBivariateFailureLaneOne6401 W))
theorem supportUnion_noncoprimeOwners_eq_of_allGraphSeedsZero6401
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
    (T : Finset F)
    (hTgood : T ⊆ rowTwoGoodChallenges6401 W.commonDirection S) :
    puncturedErrorSupportUnion6401 W (noncoprimePrimitiveOwners6401 W T) =
      puncturedErrorSupportUnion6401 W T := by
  classical
  apply Finset.Subset.antisymm
  · intro i hi
    rcases Finset.mem_biUnion.mp hi with ⟨z, hz, hi⟩
    have hz' := hz
    rw [noncoprimePrimitiveOwners6401] at hz'
    exact Finset.mem_biUnion.mpr
      ⟨z, (Finset.mem_filter.mp hz').1, hi⟩
  · intro i hi
    rcases Finset.mem_biUnion.mp hi with ⟨z, hz, hi⟩
    have hnoncoprime : ¬ IsCoprime
        (specializeCoeffZ z (primitiveBivariateFailureLaneZero6401 W))
        (specializeCoeffZ z (primitiveBivariateFailureLaneOne6401 W)) := by
      intro hcoprime
      have hempty :=
        puncturedErrorSupport_eq_empty_of_allGraphSeedsZero_of_coprime6401
          W hsigma hfixed hsix hall z (hTgood hz) hcoprime
      rw [hempty] at hi
      simp at hi
    have hz' : z ∈ noncoprimePrimitiveOwners6401 W T := by
      rw [noncoprimePrimitiveOwners6401]
      exact Finset.mem_filter.mpr ⟨hz, hnoncoprime⟩
    exact Finset.mem_biUnion.mpr ⟨z, hz', hi⟩
theorem noCurve_noncoprimeOwners_supportUnion_card_ge_108566_6401
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
    (T : Finset F)
    (hTgood : T ⊆ rowTwoGoodChallenges6401 W.commonDirection S)
    (hTcard : weakCurveOutput6401 ≤ T.card)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P) :
    108566 ≤ (puncturedErrorSupportUnion6401 W
      (noncoprimePrimitiveOwners6401 W T)).card := by
  rw [supportUnion_noncoprimeOwners_eq_of_allGraphSeedsZero6401
    W hsigma hfixed hsix hall T hTgood]
  exact noCurve_supportUnion_card_ge_108566_6401
    W T hTgood hTcard hPdegree hfail
theorem curveWitness_of_allGraphSeedsZero_of_coprimeOwners6401
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
    (T : Finset F)
    (hTgood : T ⊆ rowTwoGoodChallenges6401 W.commonDirection S)
    (hTcard : weakCurveOutput6401 ≤ T.card)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hcoprime : ∀ z ∈ T, IsCoprime
      (specializeCoeffZ z (primitiveBivariateFailureLaneZero6401 W))
      (specializeCoeffZ z (primitiveBivariateFailureLaneOne6401 W))) :
    PolynomialAffineCurveWitness6401 S P := by
  classical
  apply curveWitness_of_puncturedErrorSupportEnvelope6401 W T ∅
    hTgood hTcard hPdegree
  · intro z hz
    rw [puncturedErrorSupport_eq_empty_of_allGraphSeedsZero_of_coprime6401
      W hsigma hfixed hsix hall z (hTgood hz) (hcoprime z hz)]
  · simp only [Finset.sdiff_empty, Finset.card_univ]
    have hcard := W.puncturedIndex_card_ge_239637
    have hdegree : ownerDegreeCap6401 = 131071 := by native_decide
    omega
end BCHKSExtremePrimitiveGraphGaugeSupportFork6401
end ProximityPrize.SubmissionLower
