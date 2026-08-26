import ProximityPrize.SubmissionLower.BCHKSExtremePrimitivePuncturedOwnerWindow6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusPrimitiveCleanup6401
import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusRationalOwnerLocator6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveNormDivisorFork6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSTwoFrobeniusThreeShiftPrimitive6401
open BCHKSTwoFrobeniusRationalOwnerLocator6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSFrobeniusPrimitiveCleanup6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
noncomputable def primitiveFailureLaneZero6401
    {F : Type*} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (z : F) : Polynomial F :=
  specializeRow z W.sourcePuncture.frame.reduced 2
noncomputable def primitiveFailureLaneOne6401
    {F : Type*} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (z : F) : Polynomial F :=
  -(specializeRow z W.sourcePuncture.frame.reduced 1)
theorem primitiveFailureLane_degree_le_22507_6401
    {F : Type*} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (z : F) :
    (primitiveFailureLaneZero6401 W z).natDegree ≤ 22507 ∧
      (primitiveFailureLaneOne6401 W z).natDegree ≤ 22507 := by
  have hzero : (specializeRow z W.sourcePuncture.frame.reduced 2).natDegree ≤
      primitiveThreeShiftXCap6401 2 :=
    Polynomial.natDegree_map_le.trans (W.sourcePuncture.reduced_caps 2)
  have hone : (specializeRow z W.sourcePuncture.frame.reduced 1).natDegree ≤
      primitiveThreeShiftXCap6401 1 :=
    Polynomial.natDegree_map_le.trans (W.sourcePuncture.reduced_caps 1)
  constructor
  · simpa [primitiveFailureLaneZero6401, primitiveThreeShiftXCap6401]
      using hzero
  · simpa [primitiveFailureLaneOne6401, primitiveThreeShiftXCap6401]
      using hone
noncomputable def puncturedErrorSupport6401
    {F : Type*} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (z : F) : Finset W.PuncturedIndex :=
  Finset.univ.filter fun i => W.puncturedOwnerError z i ≠ 0
def puncturedIndexEmbedding6401
    {F : Type*} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P) :
    W.PuncturedIndex ↪ Fin n6401 where
  toFun i := i.1
  inj' := Subtype.val_injective
theorem puncturedErrorSupport_card_le_76790_6401
    {F : Type*} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (z : F) (_hz : z ∈ rowTwoGoodChallenges6401 W.commonDirection S)
    (hrow : a6401 ≤ (A z).card)
    (howner : ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i) :
    (puncturedErrorSupport6401 W z).card ≤ 76790 := by
  classical
  let image : Finset (Fin n6401) :=
    (puncturedErrorSupport6401 W z).map (puncturedIndexEmbedding6401 W)
  have hsub : image ⊆ Finset.univ \ A z := by
    intro i hi
    rcases Finset.mem_map.mp hi with ⟨j, hj, rfl⟩
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro hjA
    have herr : W.puncturedOwnerError z j ≠ 0 :=
      (Finset.mem_filter.mp hj).2
    apply herr
    dsimp [PrimitivePuncturedOwnerWindow6401.puncturedOwnerError]
    rw [howner j.1 hjA]
    exact sub_self _
  have himage : image.card = (puncturedErrorSupport6401 W z).card := by
    exact Finset.card_map _
  have hcomplement : (Finset.univ \ A z).card = n6401 - (A z).card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      Fintype.card_fin]
  have hle : (puncturedErrorSupport6401 W z).card ≤
      n6401 - (A z).card := by
    rw [← himage, ← hcomplement]
    exact Finset.card_le_card hsub
  have hsub : n6401 - (A z).card ≤ n6401 - a6401 :=
    Nat.sub_le_sub_left hrow n6401
  exact hle.trans <| by
    simpa [n6401, a6401] using hsub
noncomputable def puncturedErrorLocator6401
    {F : Type*} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (z : F) : Polynomial F :=
  ownerLocator W.puncturedAlpha (puncturedErrorSupport6401 W z)
noncomputable def primitiveOwnerNormObstruction6401
    {F : Type*} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (z : F) : Polynomial F :=
  polynomialFrobeniusNormSix sigma (primitiveFailureLaneZero6401 W z) -
    polynomialFrobeniusNormSix sigma (primitiveFailureLaneOne6401 W z)
theorem primitiveOwnerNormObstruction_natDegree_le_135042_6401
    {F : Type*} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (z : F) :
    (primitiveOwnerNormObstruction6401 W z).natDegree ≤ 135042 := by
  rcases primitiveFailureLane_degree_le_22507_6401 W z with ⟨h0, h1⟩
  simpa [primitiveOwnerNormObstruction6401] using
    normDifference_natDegree_le sigma
      (primitiveFailureLaneZero6401 W z)
      (primitiveFailureLaneOne6401 W z) 22507 h0 h1
private theorem ownerLocator_dvd_of_eval_zero
    {F ι : Type*} [Field F] [DecidableEq ι]
    (alpha : ι ↪ F) (T : Finset ι) (N : Polynomial F)
    (hzero : ∀ i ∈ T, Polynomial.eval (alpha i) N = 0) :
    ownerLocator alpha T ∣ N := by
  classical
  unfold ownerLocator
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    exact Polynomial.pairwise_coprime_X_sub_C alpha.injective hij
  · intro i hi
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
    exact hzero i hi
theorem puncturedErrorLocator_dvd_normObstruction6401
    {F : Type*} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (horder : ∀ x,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (z : F) (hz : z ∈ rowTwoGoodChallenges6401 W.commonDirection S) :
    puncturedErrorLocator6401 W z ∣
      primitiveOwnerNormObstruction6401 W z := by
  classical
  let W0 := primitiveFailureLaneZero6401 W z
  let W1 := primitiveFailureLaneOne6401 W z
  have hfailure := W.puncturedTwoLaneFailureRelation hsigma hfixed z hz
  apply ownerLocator_dvd_of_eval_zero W.puncturedAlpha
    (puncturedErrorSupport6401 W z)
  intro i hi
  have herror : W.puncturedOwnerError z i ≠ 0 :=
    (Finset.mem_filter.mp hi).2
  have hvalue := scalarFrobeniusNormSix_eq_of_relation sigma horder
    (Polynomial.eval (W.puncturedAlpha i) W0)
    (Polynomial.eval (W.puncturedAlpha i) W1)
    (W.puncturedOwnerError z i) herror (hfailure i)
  have hfixedAt : sigma (W.puncturedAlpha i) = W.puncturedAlpha i := by
    exact hfixed i.1
  have hnorm0 := polynomialFrobeniusNormSix_eval_of_fixed
    sigma W0 (W.puncturedAlpha i) hfixedAt
  have hnorm1 := polynomialFrobeniusNormSix_eval_of_fixed
    sigma W1 (W.puncturedAlpha i) hfixedAt
  dsimp [primitiveOwnerNormObstruction6401]
  rw [Polynomial.eval_sub, hnorm0, hnorm1, hvalue, sub_self]
theorem normDegenerate_or_splitErrorDivisor6401
    {F : Type*} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (horder : ∀ x,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (z : F) (hz : z ∈ rowTwoGoodChallenges6401 W.commonDirection S)
    (hrow : a6401 ≤ (A z).card)
    (howner : ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i) :
    primitiveOwnerNormObstruction6401 W z = 0 ∨
      ∃ Q : Polynomial F,
        primitiveOwnerNormObstruction6401 W z =
            puncturedErrorLocator6401 W z * Q ∧
        (puncturedErrorLocator6401 W z).natDegree ≤ 76790 ∧
        (puncturedErrorLocator6401 W z).natDegree + Q.natDegree ≤ 135042 := by
  classical
  by_cases hnorm : primitiveOwnerNormObstruction6401 W z = 0
  · exact Or.inl hnorm
  right
  obtain ⟨Q, hQ⟩ := puncturedErrorLocator_dvd_normObstruction6401
    W hsigma hfixed horder z hz
  have hlocatorMonic : (puncturedErrorLocator6401 W z).Monic :=
    ownerLocator_monic W.puncturedAlpha (puncturedErrorSupport6401 W z)
  have hQne : Q ≠ 0 := by
    intro hzero
    apply hnorm
    rw [hQ, hzero, mul_zero]
  have hdegree := primitiveOwnerNormObstruction_natDegree_le_135042_6401 W z
  rw [hQ, Polynomial.natDegree_mul hlocatorMonic.ne_zero hQne] at hdegree
  refine ⟨Q, hQ, ?_, hdegree⟩
  rw [puncturedErrorLocator6401, ownerLocator_natDegree]
  exact puncturedErrorSupport_card_le_76790_6401
    W z hz hrow howner
end BCHKSExtremePrimitiveNormDivisorFork6401
end ProximityPrize.SubmissionLower
