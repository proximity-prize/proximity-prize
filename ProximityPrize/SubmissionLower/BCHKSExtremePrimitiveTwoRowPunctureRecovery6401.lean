import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveFixedLanePunctureSeam6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveTwoRowPunctureRecovery6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRank6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSTwoFrobeniusSymbolicKernel6401
open BCHKSTwoFrobeniusThreeShiftPrimitive6401
open BCHKSThreeShiftSourceWindow6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveLaneFactorDescent6401
open BCHKSExtremePrimitiveRecursiveFactorClosure6401
open BCHKSExtremePrimitiveFixedLaneRecurrence6401
open BCHKSExtremePrimitiveFixedLanePunctureSeam6401
set_option maxHeartbeats 5000000
set_option maxRecDepth 1000000
section TwoRowPuncture
variable {F : Type} [Field F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {Owner : F → Polynomial F}
noncomputable def twoRowSourceBadCoordinates6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner) : Finset (Fin n6401) :=
  Finset.univ.filter fun i ↦
    evalOuterAt (alpha i) W.sourcePuncture.frame.commonFactor = 0 ∨
      (evalOuterAt (alpha i) (W.commonDirection.multiplier 1) = 0 ∧
        evalOuterAt (alpha i) (W.commonDirection.multiplier 2) = 0)
noncomputable def twoRowSourcePunctureLocator6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner) : F[X] :=
  ∏ i ∈ twoRowSourceBadCoordinates6401 W,
    (Polynomial.X - Polynomial.C (alpha i))
theorem twoRowSourcePunctureLocator_monic6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner) :
    (twoRowSourcePunctureLocator6401 W).Monic := by
  classical
  simpa [twoRowSourcePunctureLocator6401] using
    Polynomial.monic_prod_X_sub_C alpha
      (twoRowSourceBadCoordinates6401 W)
theorem twoRowSourcePunctureLocator_ne_zero6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner) :
    twoRowSourcePunctureLocator6401 W ≠ 0 :=
  (twoRowSourcePunctureLocator_monic6401 W).ne_zero
theorem twoRowSourcePunctureLocator_natDegree6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner) :
    (twoRowSourcePunctureLocator6401 W).natDegree =
      (twoRowSourceBadCoordinates6401 W).card := by
  classical
  rw [twoRowSourcePunctureLocator6401,
    Polynomial.natDegree_prod_of_monic]
  · simp
  · intro i _hi
    exact Polynomial.monic_X_sub_C _
theorem twoRowSourcePunctureLocator_eval_eq_zero6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (i : Fin n6401) (hi : i ∈ twoRowSourceBadCoordinates6401 W) :
    (twoRowSourcePunctureLocator6401 W).eval (alpha i) = 0 := by
  classical
  simp only [twoRowSourcePunctureLocator6401, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (i := i)
  · exact hi
  · simp
private theorem map_splitLocator_to_bivariate6401
    (T : Finset (Fin n6401)) :
    (∏ i ∈ T, (Polynomial.X - Polynomial.C (alpha i))).map
        Polynomial.C =
      ∏ i ∈ T,
        (Polynomial.X - Polynomial.C (Polynomial.C (alpha i))) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T ha ih =>
      rw [Finset.prod_insert ha, Polynomial.map_mul, ih,
        Finset.prod_insert ha]
      simp
private theorem mappedLocator_dvd_of_evalOuterAt_zero6401
    (T : Finset (Fin n6401)) (M : F[X][X])
    (hzero : ∀ i ∈ T, evalOuterAt (alpha i) M = 0) :
    (∏ i ∈ T, (Polynomial.X - Polynomial.C (alpha i))).map
        Polynomial.C ∣ M := by
  classical
  rw [map_splitLocator_to_bivariate6401 T]
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    have hne : alpha i ≠ alpha j := fun h ↦ hij (alpha.injective h)
    have hunit : IsUnit
        ((Polynomial.C (alpha i) : Polynomial F) -
          Polynomial.C (alpha j)) := by
      rw [← Polynomial.C_sub]
      exact Polynomial.isUnit_C.mpr (sub_ne_zero.mpr hne).isUnit
    exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub hunit
  · intro i hi
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
    simpa [evalOuterAt] using hzero i hi
theorem twoRowSourcePunctureLocator_map_dvd_both6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner) :
    (twoRowSourcePunctureLocator6401 W).map Polynomial.C ∣
        W.commonDirection.multiplier 1 *
          W.sourcePuncture.frame.commonFactor ∧
      (twoRowSourcePunctureLocator6401 W).map Polynomial.C ∣
        W.commonDirection.multiplier 2 *
          W.sourcePuncture.frame.commonFactor := by
  classical
  constructor
  · apply mappedLocator_dvd_of_evalOuterAt_zero6401
    intro i hi
    have hibad := (Finset.mem_filter.mp hi).2
    rcases hibad with hcommon | hboth
    · unfold evalOuterAt at hcommon ⊢
      simp only [Polynomial.eval_mul]
      exact mul_eq_zero.mpr (Or.inr hcommon)
    · unfold evalOuterAt at hboth ⊢
      simp only [Polynomial.eval_mul]
      exact mul_eq_zero.mpr (Or.inl hboth.1)
  · apply mappedLocator_dvd_of_evalOuterAt_zero6401
    intro i hi
    have hibad := (Finset.mem_filter.mp hi).2
    rcases hibad with hcommon | hboth
    · unfold evalOuterAt at hcommon ⊢
      simp only [Polynomial.eval_mul]
      exact mul_eq_zero.mpr (Or.inr hcommon)
    · unfold evalOuterAt at hboth ⊢
      simp only [Polynomial.eval_mul]
      exact mul_eq_zero.mpr (Or.inl hboth.2)
theorem twoRowSource_relation6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (i : Fin n6401) (hi : i ∉ twoRowSourceBadCoordinates6401 W) :
    symbolicCoordinateRelation sigma (alpha i) (u0 i) (u1 i)
      W.sourcePuncture.frame.reduced = 0 := by
  have hgood : ¬ (
      evalOuterAt (alpha i) W.sourcePuncture.frame.commonFactor = 0 ∨
        (evalOuterAt (alpha i) (W.commonDirection.multiplier 1) = 0 ∧
          evalOuterAt (alpha i) (W.commonDirection.multiplier 2) = 0)) := by
    simpa [twoRowSourceBadCoordinates6401] using hi
  have hcommon :
      evalOuterAt (alpha i) W.sourcePuncture.frame.commonFactor ≠ 0 := by
    intro hzero
    exact hgood (Or.inl hzero)
  have hsource := sourceRelations_of_rows_eq_selected6401
    sigma alpha u0 u1 W.commonDirection W.rows_eq_selected
  have hdirection : symbolicCoordinateRelation sigma (alpha i)
      (u0 i) (u1 i) W.commonDirection.direction = 0 := by
    by_cases hmult1 :
        evalOuterAt (alpha i) (W.commonDirection.multiplier 1) = 0
    · have hmult2 :
          evalOuterAt (alpha i) (W.commonDirection.multiplier 2) ≠ 0 := by
        intro hzero
        exact hgood (Or.inr ⟨hmult1, hzero⟩)
      exact cancel_sourceRelation_of_commonDirection W.commonDirection
        sigma (alpha i) (u0 i) (u1 i) 2 hmult2 (hsource 2 i)
    · exact cancel_sourceRelation_of_commonDirection W.commonDirection
        sigma (alpha i) (u0 i) (u1 i) 1 hmult1 (hsource 1 i)
  exact W.sourcePuncture.frame.cancel_coordinate_relation
    sigma (alpha i) (u0 i) (u1 i) hcommon hdirection
theorem recursiveTwoRowSource_relation6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (i : Fin n6401) (hi : i ∉ twoRowSourceBadCoordinates6401 W) :
    symbolicCoordinateRelation sigma (alpha i) (u0 i) (u1 i)
      R.quotient = 0 := by
  have hsource := twoRowSource_relation6401 W i hi
  have hfactorAt : evalOuterAt (alpha i) R.cumulativeFactor ≠ 0 := by
    intro hzero
    have hone : evalOuterAt (alpha i)
        (W.sourcePuncture.frame.reduced 1) = 0 := by
      have h := congrArg (evalOuterAt (alpha i)) (R.component_factor 1)
      unfold evalOuterAt at hzero
      simp only [evalOuterAt, Polynomial.eval_mul] at h
      rw [hzero, zero_mul] at h
      simpa [evalOuterAt] using h
    have htwo : evalOuterAt (alpha i)
        (W.sourcePuncture.frame.reduced 2) = 0 := by
      have h := congrArg (evalOuterAt (alpha i)) (R.component_factor 2)
      unfold evalOuterAt at hzero
      simp only [evalOuterAt, Polynomial.eval_mul] at h
      rw [hzero, zero_mul] at h
      simpa [evalOuterAt] using h
    rcases primitive_homogeneous_evaluations_not_both_zero
        W.sourcePuncture.frame sigma i (Finset.mem_univ i)
          (u0 i) (u1 i) hsource with h | h
    · exact h hone
    · exact h htwo
  have hrow : W.sourcePuncture.frame.reduced =
      fun j ↦ R.cumulativeFactor * R.quotient j := by
    funext j
    exact R.component_factor j
  rw [hrow, symbolicCoordinateRelation_factorRow6401] at hsource
  exact (mul_eq_zero.mp hsource).resolve_left hfactorAt
theorem recursiveFixedFailureRelation_twoRow_fullDomain6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (G U0 U1 : F[X])
    (hzero : R.laneZero6401 =
      Polynomial.C G * U0.map Polynomial.C)
    (hone : R.laneOne6401 =
      Polynomial.C G * U1.map Polynomial.C)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (z : F) (hz : z ∈ R.goodChallenges6401)
    (hGz : G.eval z ≠ 0) :
    TwoLaneFailureRelation sigma alpha (fullOwnerError6401 W z)
      (twoRowSourcePunctureLocator6401 W * U0)
      (twoRowSourcePunctureLocator6401 W * U1) := by
  classical
  have hspecZero : specializeCoeffZ z R.laneZero6401 =
      Polynomial.C (G.eval z) * U0 := by
    have h := congrArg (specializeCoeffZ z) hzero
    simpa [specializeCoeffZ, Polynomial.map_mul] using h
  have hspecOne : specializeCoeffZ z R.laneOne6401 =
      Polynomial.C (G.eval z) * U1 := by
    have h := congrArg (specializeCoeffZ z) hone
    simpa [specializeCoeffZ, Polynomial.map_mul] using h
  intro i
  by_cases hi : i ∈ twoRowSourceBadCoordinates6401 W
  · have hD := twoRowSourcePunctureLocator_eval_eq_zero6401 W i hi
    simp only [Polynomial.eval_mul, hD, zero_mul]
  · have hsource := recursiveTwoRowSource_relation6401 W R i hi
    have howner := R.owner_relation6401 z hz
    have hrel := twoLaneErrorRelation_of_owner_and_source6401
      sigma (alpha i) z (u0 i) (u1 i) (Owner z) R.quotient
        (hsigma z) (hfixed i) howner hsource
    simp only [specializeRow] at hrel
    have hfixedRel : U0.eval (alpha i) *
          sigma (fullOwnerError6401 W z i) =
        U1.eval (alpha i) * fullOwnerError6401 W z i := by
      simp only [RecursivePrimitiveLaneState6401.laneZero6401,
        RecursivePrimitiveLaneState6401.laneOne6401] at hspecZero hspecOne
      rw [map_neg] at hspecOne
      have hq1 : specializeCoeffZ z (R.quotient 1) =
          -(Polynomial.C (G.eval z) * U1) := by
        linear_combination -hspecOne
      rw [hq1, hspecZero] at hrel
      simp only [Polynomial.eval_neg, Polynomial.eval_mul,
        Polynomial.eval_C] at hrel
      apply mul_left_cancel₀ hGz
      dsimp [fullOwnerError6401]
      linear_combination hrel
    simp only [Polynomial.eval_mul]
    calc
      _ = (twoRowSourcePunctureLocator6401 W).eval (alpha i) *
          (U0.eval (alpha i) * sigma (fullOwnerError6401 W z i)) := by ring
      _ = (twoRowSourcePunctureLocator6401 W).eval (alpha i) *
          (U1.eval (alpha i) * fullOwnerError6401 W z i) := by
        rw [hfixedRel]
      _ = _ := by ring
theorem twoRowPuncture_augmentedFixedLanes_dvd_diagonals6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (G U0 U1 : F[X])
    (hzero : R.laneZero6401 =
      Polynomial.C G * U0.map Polynomial.C)
    (hone : R.laneOne6401 =
      Polynomial.C G * U1.map Polynomial.C) :
    (twoRowSourcePunctureLocator6401 W * U1).map Polynomial.C ∣
        W.commonDirection.rows 1 1 ∧
      (twoRowSourcePunctureLocator6401 W * U0).map Polynomial.C ∣
        W.commonDirection.rows 2 2 := by
  rcases twoRowSourcePunctureLocator_map_dvd_both6401 W with
    ⟨⟨Q1, hQ1⟩, ⟨Q2, hQ2⟩⟩
  constructor
  · refine ⟨Q1 * R.cumulativeFactor * (-Polynomial.C G), ?_⟩
    simp only [RecursivePrimitiveLaneState6401.laneOne6401] at hone
    have hq1 : R.quotient 1 =
        -(Polynomial.C G * U1.map Polynomial.C) := by
      linear_combination -hone
    calc
      W.commonDirection.rows 1 1 =
          W.commonDirection.multiplier 1 *
            W.commonDirection.direction 1 :=
        W.commonDirection.row_factor 1 1
      _ = W.commonDirection.multiplier 1 *
          (W.sourcePuncture.frame.commonFactor *
            W.sourcePuncture.frame.reduced 1) := by
        rw [W.sourcePuncture.frame.component_factor 1]
      _ = W.commonDirection.multiplier 1 *
          (W.sourcePuncture.frame.commonFactor *
            (R.cumulativeFactor * R.quotient 1)) := by
        rw [R.component_factor 1]
      _ = (W.commonDirection.multiplier 1 *
            W.sourcePuncture.frame.commonFactor) *
          (R.cumulativeFactor *
            -(Polynomial.C G * U1.map Polynomial.C)) := by
        rw [hq1]
        ring
      _ = ((twoRowSourcePunctureLocator6401 W).map Polynomial.C * Q1) *
          (R.cumulativeFactor *
            -(Polynomial.C G * U1.map Polynomial.C)) := by
        rw [hQ1]
      _ = (twoRowSourcePunctureLocator6401 W * U1).map Polynomial.C *
          (Q1 * R.cumulativeFactor * (-Polynomial.C G)) := by
        rw [Polynomial.map_mul]
        ring
  · refine ⟨Q2 * R.cumulativeFactor * Polynomial.C G, ?_⟩
    simp only [RecursivePrimitiveLaneState6401.laneZero6401] at hzero
    calc
      W.commonDirection.rows 2 2 =
          W.commonDirection.multiplier 2 *
            W.commonDirection.direction 2 :=
        W.commonDirection.row_factor 2 2
      _ = W.commonDirection.multiplier 2 *
          (W.sourcePuncture.frame.commonFactor *
            W.sourcePuncture.frame.reduced 2) := by
        rw [W.sourcePuncture.frame.component_factor 2]
      _ = W.commonDirection.multiplier 2 *
          (W.sourcePuncture.frame.commonFactor *
            (R.cumulativeFactor * R.quotient 2)) := by
        rw [R.component_factor 2]
      _ = (W.commonDirection.multiplier 2 *
            W.sourcePuncture.frame.commonFactor) *
          (R.cumulativeFactor *
            (Polynomial.C G * U0.map Polynomial.C)) := by
        rw [hzero]
        ring
      _ = ((twoRowSourcePunctureLocator6401 W).map Polynomial.C * Q2) *
          (R.cumulativeFactor *
            (Polynomial.C G * U0.map Polynomial.C)) := by
        rw [hQ2]
      _ = (twoRowSourcePunctureLocator6401 W * U0).map Polynomial.C *
          (Q2 * R.cumulativeFactor * Polynomial.C G) := by
        rw [Polynomial.map_mul]
        ring
theorem twoRowPuncture_augmentedFixedLanes_natDegree_le_22507_6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (G U0 U1 : F[X])
    (hG : G ≠ 0) (hU0 : U0 ≠ 0) (hU1 : U1 ≠ 0)
    (hzero : R.laneZero6401 =
      Polynomial.C G * U0.map Polynomial.C)
    (hone : R.laneOne6401 =
      Polynomial.C G * U1.map Polynomial.C) :
    (twoRowSourcePunctureLocator6401 W * U0).natDegree ≤
        homogeneousDirectionCap6401 ∧
      (twoRowSourcePunctureLocator6401 W * U1).natDegree ≤
        homogeneousDirectionCap6401 := by
  have hdvd := twoRowPuncture_augmentedFixedLanes_dvd_diagonals6401
    W R G U0 U1 hzero hone
  have hCG : Polynomial.C G ≠ 0 := Polynomial.C_ne_zero.mpr hG
  have hmapU0 : U0.map Polynomial.C ≠ 0 :=
    (Polynomial.map_ne_zero_iff Polynomial.C_injective).2 hU0
  have hmapU1 : U1.map Polynomial.C ≠ 0 :=
    (Polynomial.map_ne_zero_iff Polynomial.C_injective).2 hU1
  have hq1 : R.quotient 1 ≠ 0 := by
    simp only [RecursivePrimitiveLaneState6401.laneOne6401] at hone
    have heq : R.quotient 1 =
        -(Polynomial.C G * U1.map Polynomial.C) := by
      linear_combination -hone
    rw [heq]
    exact neg_ne_zero.mpr (mul_ne_zero hCG hmapU1)
  have hq2 : R.quotient 2 ≠ 0 := by
    simp only [RecursivePrimitiveLaneState6401.laneZero6401] at hzero
    rw [hzero]
    exact mul_ne_zero hCG hmapU0
  have hdirection1 : W.commonDirection.direction 1 ≠ 0 := by
    rw [W.sourcePuncture.frame.component_factor 1,
      R.component_factor 1]
    exact mul_ne_zero W.sourcePuncture.frame.commonFactor_monic.ne_zero
      (mul_ne_zero R.cumulativeFactor_ne_zero hq1)
  have hdirection2 : W.commonDirection.direction 2 ≠ 0 := by
    rw [W.sourcePuncture.frame.component_factor 2,
      R.component_factor 2]
    exact mul_ne_zero W.sourcePuncture.frame.commonFactor_monic.ne_zero
      (mul_ne_zero R.cumulativeFactor_ne_zero hq2)
  have hrow1 : W.commonDirection.rows 1 1 ≠ 0 := by
    rw [W.commonDirection.row_factor 1 1]
    exact mul_ne_zero (W.commonDirection.multiplier_ne_zero 1) hdirection1
  have hrow2 : W.commonDirection.rows 2 2 ≠ 0 := by
    rw [W.commonDirection.row_factor 2 2]
    exact mul_ne_zero (W.commonDirection.multiplier_ne_zero 2) hdirection2
  constructor
  · have hdeg := Polynomial.natDegree_le_of_dvd hdvd.2 hrow2
    rw [Polynomial.natDegree_map_eq_of_injective
      Polynomial.C_injective] at hdeg
    exact hdeg.trans (W.commonDirection.row_caps 2 2)
  · have hdeg := Polynomial.natDegree_le_of_dvd hdvd.1 hrow1
    rw [Polynomial.natDegree_map_eq_of_injective
      Polynomial.C_injective] at hdeg
    exact hdeg.trans (W.commonDirection.row_caps 1 1)
theorem twoRowPuncture_augmentedFixedLanes_mem_semilinearWidth6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (R : RecursivePrimitiveLaneState6401 W)
    (G U0 U1 : F[X])
    (hG : G ≠ 0) (hU0 : U0 ≠ 0) (hU1 : U1 ≠ 0)
    (hzero : R.laneZero6401 =
      Polynomial.C G * U0.map Polynomial.C)
    (hone : R.laneOne6401 =
      Polynomial.C G * U1.map Polynomial.C) :
    twoRowSourcePunctureLocator6401 W * U0 ∈
        Polynomial.degreeLT F semilinearWidth ∧
      twoRowSourcePunctureLocator6401 W * U1 ∈
        Polynomial.degreeLT F semilinearWidth := by
  have hcaps :=
    twoRowPuncture_augmentedFixedLanes_natDegree_le_22507_6401
      W R G U0 U1 hG hU0 hU1 hzero hone
  constructor <;> rw [Polynomial.mem_degreeLT]
  · exact (Polynomial.natDegree_lt_iff_degree_lt
      (mul_ne_zero (twoRowSourcePunctureLocator_ne_zero6401 W) hU0)).1
      (hcaps.1.trans_lt (by native_decide))
  · exact (Polynomial.natDegree_lt_iff_degree_lt
      (mul_ne_zero (twoRowSourcePunctureLocator_ne_zero6401 W) hU1)).1
      (hcaps.2.trans_lt (by native_decide))
theorem exists_recursiveTwoRowFullDomainFixedFailurePair6401
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
      R.laneZero6401 = Polynomial.C G * U0.map Polynomial.C ∧
      R.laneOne6401 = Polynomial.C G * U1.map Polynomial.C ∧
      (twoRowSourcePunctureLocator6401 W * U0).natDegree ≤
        homogeneousDirectionCap6401 ∧
      (twoRowSourcePunctureLocator6401 W * U1).natDegree ≤
        homogeneousDirectionCap6401 ∧
      twoRowSourcePunctureLocator6401 W * U0 ∈
        Polynomial.degreeLT F semilinearWidth ∧
      twoRowSourcePunctureLocator6401 W * U1 ∈
        Polynomial.degreeLT F semilinearWidth ∧
      ∀ z ∈ R.goodChallenges6401, G.eval z ≠ 0 →
        TwoLaneFailureRelation sigma alpha (fullOwnerError6401 W z)
          (twoRowSourcePunctureLocator6401 W * U0)
          (twoRowSourcePunctureLocator6401 W * U1) := by
  obtain ⟨G, U0, U1, hG, hU0, hU1, hzero, hone, _hpunctured⟩ :=
    exists_recursiveCommonContentFixedFailurePair6401
      W R hresultant hnorm horder hsigma hfixed
  have hdegrees :=
    twoRowPuncture_augmentedFixedLanes_natDegree_le_22507_6401
      W R G U0 U1 hG hU0 hU1 hzero hone
  have hwidth := twoRowPuncture_augmentedFixedLanes_mem_semilinearWidth6401
    W R G U0 U1 hG hU0 hU1 hzero hone
  refine ⟨G, U0, U1, hG, hU0, hU1, hzero, hone,
    hdegrees.1, hdegrees.2, hwidth.1, hwidth.2, ?_⟩
  intro z hz hGz
  exact recursiveFixedFailureRelation_twoRow_fullDomain6401
    W R G U0 U1 hzero hone hsigma hfixed z hz hGz
end TwoRowPuncture
end BCHKSExtremePrimitiveTwoRowPunctureRecovery6401
end ProximityPrize.SubmissionLower
