import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveFixedLaneRecurrence6401
import ProximityPrize.SubmissionLower.BCHKSTwoFrobeniusRankOneSpherical6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveFixedLanePunctureSeam6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRank6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSThreeShiftSourceWindow6401
open BCHKSTwoFrobeniusThreeShiftPrimitive6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveRecursiveFactorClosure6401
open BCHKSExtremePrimitiveFixedLaneRecurrence6401
set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
section PunctureLocator
variable {F : Type} [Field F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {Owner : F → Polynomial F}
noncomputable def fixedSourcePunctureLocator6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner) : F[X] :=
  ∏ i ∈ W.sourcePuncture.badCoordinates,
    (Polynomial.X - Polynomial.C (alpha i))
theorem fixedSourcePunctureLocator_monic6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner) :
    (fixedSourcePunctureLocator6401 W).Monic := by
  classical
  simpa [fixedSourcePunctureLocator6401] using
    Polynomial.monic_prod_X_sub_C alpha
      W.sourcePuncture.badCoordinates
theorem fixedSourcePunctureLocator_ne_zero6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner) :
    fixedSourcePunctureLocator6401 W ≠ 0 :=
  (fixedSourcePunctureLocator_monic6401 W).ne_zero
theorem fixedSourcePunctureLocator_natDegree6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner) :
    (fixedSourcePunctureLocator6401 W).natDegree =
      W.sourcePuncture.badCoordinates.card := by
  classical
  rw [fixedSourcePunctureLocator6401,
    Polynomial.natDegree_prod_of_monic]
  · simp
  · intro i _hi
    exact Polynomial.monic_X_sub_C _
theorem fixedSourcePunctureLocator_eval_eq_zero6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (i : Fin n6401) (hi : i ∈ W.sourcePuncture.badCoordinates) :
    (fixedSourcePunctureLocator6401 W).eval (alpha i) = 0 := by
  classical
  rw [fixedSourcePunctureLocator6401, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (i := i)
  · exact hi
  · simp
noncomputable def fullOwnerError6401
    (_W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner) (z : F) : Fin n6401 → F :=
  fun i ↦ (Owner z).eval (alpha i) - (u0 i + z * u1 i)
theorem puncturedFailureRelation_extends_fullDomain6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (z : F) (U0 U1 : F[X])
    (hrel : TwoLaneFailureRelation sigma W.puncturedAlpha
      (W.puncturedOwnerError z) U0 U1) :
    TwoLaneFailureRelation sigma alpha (fullOwnerError6401 W z)
      (fixedSourcePunctureLocator6401 W * U0)
      (fixedSourcePunctureLocator6401 W * U1) := by
  classical
  intro i
  by_cases hi : i ∈ W.sourcePuncture.badCoordinates
  · have hD := fixedSourcePunctureLocator_eval_eq_zero6401 W i hi
    simp only [Polynomial.eval_mul, hD, zero_mul]
  · let ip : W.PuncturedIndex :=
      ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩⟩
    have hip := hrel ip
    change U0.eval (alpha i) * sigma (fullOwnerError6401 W z i) =
      U1.eval (alpha i) * fullOwnerError6401 W z i at hip
    simp only [Polynomial.eval_mul]
    change
      (fixedSourcePunctureLocator6401 W).eval (alpha i) * U0.eval (alpha i) *
          sigma (fullOwnerError6401 W z i) =
        (fixedSourcePunctureLocator6401 W).eval (alpha i) * U1.eval (alpha i) *
          fullOwnerError6401 W z i
    calc
      _ = (fixedSourcePunctureLocator6401 W).eval (alpha i) *
          (U0.eval (alpha i) * sigma (fullOwnerError6401 W z i)) := by ring
      _ = (fixedSourcePunctureLocator6401 W).eval (alpha i) *
          (U1.eval (alpha i) * fullOwnerError6401 W z i) := by rw [hip]
      _ = _ := by ring
theorem punctureMultipliedLane_natDegree_le_45014_6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (U : F[X]) (hU : U.natDegree ≤ homogeneousDirectionCap6401) :
    (fixedSourcePunctureLocator6401 W * U).natDegree ≤ 45014 := by
  have hD : (fixedSourcePunctureLocator6401 W).natDegree ≤
      homogeneousDirectionCap6401 := by
    rw [fixedSourcePunctureLocator_natDegree6401]
    exact W.sourcePuncture.badCoordinates_card
  exact Polynomial.natDegree_mul_le.trans (by
    norm_num [homogeneousDirectionCap6401] at hD hU ⊢
    omega)
theorem punctureMultipliedLane_mem_semilinearWidth_of_degree_sum_lt6401
    (D U : F[X]) (hsum : D.natDegree + U.natDegree < semilinearWidth) :
    D * U ∈ Polynomial.degreeLT F semilinearWidth := by
  rw [Polynomial.mem_degreeLT]
  by_cases hDU : D * U = 0
  · simp [hDU]
  · apply (Polynomial.natDegree_lt_iff_degree_lt hDU).1
    exact Polynomial.natDegree_mul_le.trans_lt hsum
theorem canonicalPunctureEnvelope_overruns_semilinearWidth6401 :
    22507 + 22507 = 45014 ∧
      semilinearWidth - 1 = 43691 ∧
      45014 = (semilinearWidth - 1) + 1323 ∧
      ¬ 45014 < semilinearWidth := by
  native_decide
theorem exists_terminalFullDomainFixedFailurePair_le_45014_6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (hresultant : R.laneResultant6401 ≠ 0)
    (hnorm : graphFrobeniusNormSix6401 sigma q6401 R.laneZero6401 =
      graphFrobeniusNormSix6401 sigma q6401 R.laneOne6401)
    (horder : ∀ x : F,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i) :
    ∃ G U0 U1 : F[X],
      G ≠ 0 ∧ U0 ≠ 0 ∧ U1 ≠ 0 ∧
      U0.natDegree ≤ homogeneousDirectionCap6401 ∧
      U1.natDegree ≤ homogeneousDirectionCap6401 ∧
      ∀ z ∈ R.goodChallenges6401, G.eval z ≠ 0 →
        TwoLaneFailureRelation sigma alpha (fullOwnerError6401 W z)
          (fixedSourcePunctureLocator6401 W * U0)
          (fixedSourcePunctureLocator6401 W * U1) ∧
        (fixedSourcePunctureLocator6401 W * U0).natDegree ≤ 45014 ∧
        (fixedSourcePunctureLocator6401 W * U1).natDegree ≤ 45014 := by
  obtain ⟨G, U0, U1, hG, hU0, hU1, hzero, hone, hrel⟩ :=
    exists_recursiveCommonContentFixedFailurePair6401
      W R hresultant hnorm horder hsigma hfixed
  have hzeroMap : U0.map Polynomial.C ≠ 0 :=
    (Polynomial.map_ne_zero_iff Polynomial.C_injective).2 hU0
  have honeMap : U1.map Polynomial.C ≠ 0 :=
    (Polynomial.map_ne_zero_iff Polynomial.C_injective).2 hU1
  have hzeroDegree : R.laneZero6401.natDegree = U0.natDegree := by
    rw [hzero, Polynomial.natDegree_mul
      (Polynomial.C_ne_zero.mpr hG) hzeroMap,
      Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective]
    simp
  have honeDegree : R.laneOne6401.natDegree = U1.natDegree := by
    rw [hone, Polynomial.natDegree_mul
      (Polynomial.C_ne_zero.mpr hG) honeMap,
      Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective]
    simp
  have hU0degree : U0.natDegree ≤ homogeneousDirectionCap6401 := by
    rw [← hzeroDegree]
    simpa [RecursivePrimitiveLaneState6401.laneZero6401,
      primitiveThreeShiftXCap6401, homogeneousDirectionCap6401] using
        R.quotient_caps6401 (2 : Fin 3)
  have hU1degree : U1.natDegree ≤ homogeneousDirectionCap6401 := by
    rw [← honeDegree]
    simpa [RecursivePrimitiveLaneState6401.laneOne6401,
      primitiveThreeShiftXCap6401, homogeneousDirectionCap6401] using
        R.quotient_caps6401 (1 : Fin 3)
  refine ⟨G, U0, U1, hG, hU0, hU1, hU0degree, hU1degree, ?_⟩
  intro z hz hGz
  refine ⟨puncturedFailureRelation_extends_fullDomain6401
      W z U0 U1 (hrel z hz hGz),
    punctureMultipliedLane_natDegree_le_45014_6401 W U0 hU0degree,
    punctureMultipliedLane_natDegree_le_45014_6401 W U1 hU1degree⟩
end PunctureLocator
end BCHKSExtremePrimitiveFixedLanePunctureSeam6401
end ProximityPrize.SubmissionLower
