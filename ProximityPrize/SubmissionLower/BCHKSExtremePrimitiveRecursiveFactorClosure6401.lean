import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveInhomogeneousResultantFork6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveRecursiveFactorClosure6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSTwoFrobeniusRankTwoClosure6401
open BCHKSTwoFrobeniusSymbolicKernel6401
open BCHKSTwoFrobeniusThreeShiftPrimitive6401
open BCHKSThreeShiftSourceWindow6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveLaneCommonFactorSource6401
open BCHKSExtremePrimitiveLaneFactorDescent6401
open BCHKSFrobeniusGraphInjectivity6401
set_option maxHeartbeats 5000000
set_option maxRecDepth 1000000
section RecursiveState
variable {F : Type} [Field F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {Owner : F → Polynomial F}
structure RecursivePrimitiveLaneState6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner) where
  cumulativeFactor : F[X][X]
  cumulativeFactor_ne_zero : cumulativeFactor ≠ 0
  quotient : SymbolicRow F
  component_factor : ∀ j,
    W.sourcePuncture.frame.reduced j = cumulativeFactor * quotient j
  quotient_pivot_ne_zero : quotient W.sourcePuncture.pivot ≠ 0
noncomputable def RecursivePrimitiveLaneState6401.initial
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner) :
    RecursivePrimitiveLaneState6401 W where
  cumulativeFactor := 1
  cumulativeFactor_ne_zero := one_ne_zero
  quotient := W.sourcePuncture.frame.reduced
  component_factor := by intro j; simp
  quotient_pivot_ne_zero := W.sourcePuncture.frame.pivot_ne_zero
theorem RecursivePrimitiveLaneState6401.cumulativeFactor_dvd_pivot6401
    {W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner}
    (C : RecursivePrimitiveLaneState6401 W) :
    C.cumulativeFactor ∣
      W.sourcePuncture.frame.reduced W.sourcePuncture.pivot := by
  exact ⟨C.quotient W.sourcePuncture.pivot,
    C.component_factor W.sourcePuncture.pivot⟩
theorem RecursivePrimitiveLaneState6401.quotient_caps6401
    {W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner}
    (C : RecursivePrimitiveLaneState6401 W) (j : Fin 3) :
    (C.quotient j).natDegree ≤ primitiveThreeShiftXCap6401 j := by
  by_cases hQ : C.quotient j = 0
  · simp [hQ]
  · have hrow : W.sourcePuncture.frame.reduced j ≠ 0 := by
      rw [C.component_factor j]
      exact mul_ne_zero C.cumulativeFactor_ne_zero hQ
    exact (Polynomial.natDegree_le_of_dvd
      ⟨C.cumulativeFactor, by
        rw [C.component_factor j, mul_comm]⟩ hrow).trans
        (W.sourcePuncture.reduced_caps j)
theorem RecursivePrimitiveLaneState6401.quotient_swap_natDegree_le6401
    {W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner}
    (C : RecursivePrimitiveLaneState6401 W) (j : Fin 3) :
    (Polynomial.Bivariate.swap (C.quotient j)).natDegree ≤
      (Polynomial.Bivariate.swap
        (W.sourcePuncture.frame.reduced j)).natDegree := by
  by_cases hQ : C.quotient j = 0
  · simp [hQ]
  · have hfactor : Polynomial.Bivariate.swap
          (W.sourcePuncture.frame.reduced j) =
        Polynomial.Bivariate.swap C.cumulativeFactor *
          Polynomial.Bivariate.swap (C.quotient j) := by
      simpa only [map_mul] using
        congrArg Polynomial.Bivariate.swap (C.component_factor j)
    have hfactorNe : Polynomial.Bivariate.swap C.cumulativeFactor ≠ 0 :=
      (map_ne_zero_iff Polynomial.Bivariate.swap
        Polynomial.Bivariate.swap.injective).2 C.cumulativeFactor_ne_zero
    have hQswap : Polynomial.Bivariate.swap (C.quotient j) ≠ 0 :=
      (map_ne_zero_iff Polynomial.Bivariate.swap
        Polynomial.Bivariate.swap.injective).2 hQ
    rw [hfactor, Polynomial.natDegree_mul hfactorNe hQswap]
    exact Nat.le_add_left _ _
noncomputable def RecursivePrimitiveLaneState6401.goodChallenges6401
    {W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner}
    (C : RecursivePrimitiveLaneState6401 W) : Finset F :=
  (rowTwoGoodChallenges6401 W.commonDirection S).filter fun z ↦
    specializeCoeffZ z C.cumulativeFactor ≠ 0
theorem RecursivePrimitiveLaneState6401.goodChallenges_card_floor6401
    {W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner}
    (C : RecursivePrimitiveLaneState6401 W) :
    primitiveLaneFactorDescentGoodFloor6401 ≤ C.goodChallenges6401.card := by
  classical
  let G := rowTwoGoodChallenges6401 W.commonDirection S
  let bad := G.filter fun z ↦
    specializeCoeffZ z C.cumulativeFactor = 0
  have hswap := homogeneousPivotFactor_swap_natDegree_le6401 W
    C.cumulativeFactor C.cumulativeFactor_ne_zero
      C.cumulativeFactor_dvd_pivot6401
  have hbad : bad.card ≤ primitiveLaneFactorDescentExceptionCap6401 := by
    obtain ⟨a, _ha, hcard⟩ :=
      card_zero_specializations_le_coefficient_degree G
        C.cumulativeFactor C.cumulativeFactor_ne_zero
    exact hcard.trans
      ((coeff_natDegree_le_swap_natDegree C.cumulativeFactor a).trans hswap)
  have hsplit : bad.card + C.goodChallenges6401.card = G.card := by
    dsimp only [bad, G, RecursivePrimitiveLaneState6401.goodChallenges6401]
    simpa only [ne_eq] using Finset.card_filter_add_card_filter_not
      (s := rowTwoGoodChallenges6401 W.commonDirection S)
      (fun z ↦ specializeCoeffZ z C.cumulativeFactor = 0)
  have hgood : extremeOwnerGoodChallengeFloor6401 ≤ G.card := by
    simpa only [G] using W.goodChallenges_card
  rw [primitiveLaneFactorDescentLedger_exact6401.1] at hbad
  rw [extremeOwnerWindow_exact6401.2.1] at hgood
  rw [primitiveLaneFactorDescentLedger_exact6401.2]
  omega
theorem RecursivePrimitiveLaneState6401.source_relation6401
    {W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner}
    (C : RecursivePrimitiveLaneState6401 W)
    (i : Fin n6401) (hi : i ∉ W.sourcePuncture.badCoordinates) :
    symbolicCoordinateRelation sigma (alpha i) (u0 i) (u1 i)
      C.quotient = 0 := by
  have hdiv2 : C.cumulativeFactor ∣
      W.sourcePuncture.frame.reduced 2 :=
    ⟨C.quotient 2, C.component_factor 2⟩
  have hdiv1 : C.cumulativeFactor ∣
      W.sourcePuncture.frame.reduced 1 :=
    ⟨C.quotient 1, C.component_factor 1⟩
  have hdivLane1 : C.cumulativeFactor ∣
      primitiveBivariateFailureLaneOne6401 W := by
    refine ⟨-C.quotient 1, ?_⟩
    rw [primitiveBivariateFailureLaneOne6401, C.component_factor 1]
    ring
  have hfactorAt :=
    integralCommonFactor_nonzeroAt_unpuncturedCoordinate6401 W
      C.cumulativeFactor hdiv2 hdivLane1 i hi
  have hsource := W.sourcePuncture.source_relation i hi
  have hrow : W.sourcePuncture.frame.reduced =
      fun j ↦ C.cumulativeFactor * C.quotient j := by
    funext j
    exact C.component_factor j
  rw [hrow, symbolicCoordinateRelation_factorRow6401] at hsource
  exact (mul_eq_zero.mp hsource).resolve_left hfactorAt
theorem RecursivePrimitiveLaneState6401.owner_relation6401
    {W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner}
    (C : RecursivePrimitiveLaneState6401 W)
    (z : F) (hz : z ∈ C.goodChallenges6401) :
    symbolicRelation sigma (specializeRow z C.quotient) (Owner z) = 0 := by
  have hzmem := Finset.mem_filter.mp hz
  have horiginal := W.owner_relation z hzmem.1
  have hrow : W.sourcePuncture.frame.reduced =
      fun j ↦ C.cumulativeFactor * C.quotient j := by
    funext j
    exact C.component_factor j
  rw [hrow, symbolicRelation_specializedFactorRow6401] at horiginal
  exact (mul_eq_zero.mp horiginal).resolve_left hzmem.2
theorem RecursivePrimitiveLaneState6401.retained_agreements6401
    {W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner}
    (C : RecursivePrimitiveLaneState6401 W)
    (z : F) (hz : z ∈ C.goodChallenges6401) :
    primitiveSourceWindow6401 ≤
      ((Aset z) \ W.sourcePuncture.badCoordinates).card :=
  W.retained_agreements z (Finset.mem_filter.mp hz).1
noncomputable def RecursivePrimitiveLaneState6401.extend
    {W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner}
    (C : RecursivePrimitiveLaneState6401 W)
    (H : F[X][X]) (hHpositive : 0 < H.natDegree)
    (hHdiv : ∀ j, H ∣ C.quotient j) :
    RecursivePrimitiveLaneState6401 W := by
  classical
  let Q : SymbolicRow F := fun j ↦ Classical.choose (hHdiv j)
  have hHne : H ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hHpositive
    omega
  have hQfactor : ∀ j, C.quotient j = H * Q j := by
    intro j
    exact Classical.choose_spec (hHdiv j)
  have hQpivot : Q W.sourcePuncture.pivot ≠ 0 := by
    intro hzero
    apply C.quotient_pivot_ne_zero
    rw [hQfactor W.sourcePuncture.pivot, hzero, mul_zero]
  exact {
    cumulativeFactor := C.cumulativeFactor * H
    cumulativeFactor_ne_zero :=
      mul_ne_zero C.cumulativeFactor_ne_zero hHne
    quotient := Q
    component_factor := by
      intro j
      rw [C.component_factor j, hQfactor j]
      ring
    quotient_pivot_ne_zero := hQpivot }
theorem RecursivePrimitiveLaneState6401.extend_pivot_degree_strict6401
    {W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner}
    (C : RecursivePrimitiveLaneState6401 W)
    (H : F[X][X]) (hHpositive : 0 < H.natDegree)
    (hHdiv : ∀ j, H ∣ C.quotient j) :
    ((C.extend H hHpositive hHdiv).quotient
        W.sourcePuncture.pivot).natDegree <
      (C.quotient W.sourcePuncture.pivot).natDegree := by
  let E := C.extend H hHpositive hHdiv
  change (E.quotient W.sourcePuncture.pivot).natDegree <
    (C.quotient W.sourcePuncture.pivot).natDegree
  have hHne : H ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hHpositive
    omega
  have hEpivot := E.quotient_pivot_ne_zero
  have hfactor : C.quotient W.sourcePuncture.pivot =
      H * E.quotient W.sourcePuncture.pivot := by
    exact Classical.choose_spec (hHdiv W.sourcePuncture.pivot)
  rw [hfactor, Polynomial.natDegree_mul hHne hEpivot]
  omega
noncomputable def RecursivePrimitiveLaneState6401.laneZero6401
    {W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner}
    (C : RecursivePrimitiveLaneState6401 W) : F[X][X] := C.quotient 2
noncomputable def RecursivePrimitiveLaneState6401.laneOne6401
    {W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner}
    (C : RecursivePrimitiveLaneState6401 W) : F[X][X] := -C.quotient 1
noncomputable def RecursivePrimitiveLaneState6401.laneResultant6401
    {W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner}
    (C : RecursivePrimitiveLaneState6401 W) : F[X] :=
  Polynomial.resultant C.laneZero6401 C.laneOne6401
theorem RecursivePrimitiveLaneState6401.laneResultant_ne_zero_of_pivot_degree_zero6401
    {W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner}
    (C : RecursivePrimitiveLaneState6401 W)
    (hdegree : (C.quotient W.sourcePuncture.pivot).natDegree = 0) :
    C.laneResultant6401 ≠ 0 := by
  rcases W.sourcePuncture.pivot_homogeneous with hpivot | hpivot
  · have hQ : C.quotient 1 ≠ 0 := by
      simpa [hpivot] using C.quotient_pivot_ne_zero
    have hdeg : (C.quotient 1).natDegree = 0 := by
      simpa [hpivot] using hdegree
    have hconst := Polynomial.eq_C_of_natDegree_eq_zero hdeg
    have hc : (C.quotient 1).coeff 0 ≠ 0 := by
      intro hc
      apply hQ
      rw [hconst, hc, Polynomial.C_0]
    have hnegconst : -C.quotient 1 =
        Polynomial.C (-(C.quotient 1).coeff 0) := by
      rw [hconst]
      simp
    unfold RecursivePrimitiveLaneState6401.laneResultant6401
      RecursivePrimitiveLaneState6401.laneZero6401
      RecursivePrimitiveLaneState6401.laneOne6401
    rw [hnegconst]
    simpa using pow_ne_zero (C.quotient 2).natDegree (neg_ne_zero.mpr hc)
  · have hQ : C.quotient 2 ≠ 0 := by
      simpa [hpivot] using C.quotient_pivot_ne_zero
    have hdeg : (C.quotient 2).natDegree = 0 := by
      simpa [hpivot] using hdegree
    have hconst := Polynomial.eq_C_of_natDegree_eq_zero hdeg
    have hc : (C.quotient 2).coeff 0 ≠ 0 := by
      intro hc
      apply hQ
      rw [hconst, hc, Polynomial.C_0]
    unfold RecursivePrimitiveLaneState6401.laneResultant6401
      RecursivePrimitiveLaneState6401.laneZero6401
      RecursivePrimitiveLaneState6401.laneOne6401
    rw [hconst]
    simpa using pow_ne_zero (-C.quotient 1).natDegree hc
def ReapplicableGlobalFactorProducer6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner) : Prop :=
  ∀ C : RecursivePrimitiveLaneState6401 W,
    0 < (C.quotient W.sourcePuncture.pivot).natDegree →
      ∃ H : F[X][X], 0 < H.natDegree ∧ ∀ j, H ∣ C.quotient j
theorem exists_locatorDegreeZero_recursiveState6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (hproducer : ReapplicableGlobalFactorProducer6401 W)
    (C0 : RecursivePrimitiveLaneState6401 W) :
    ∃ C : RecursivePrimitiveLaneState6401 W,
      (C.quotient W.sourcePuncture.pivot).natDegree = 0 ∧
        primitiveLaneFactorDescentGoodFloor6401 ≤
          C.goodChallenges6401.card := by
  let rec descend (C : RecursivePrimitiveLaneState6401 W) :
      ∃ D : RecursivePrimitiveLaneState6401 W,
        (D.quotient W.sourcePuncture.pivot).natDegree = 0 ∧
          primitiveLaneFactorDescentGoodFloor6401 ≤
            D.goodChallenges6401.card := by
    by_cases hd : (C.quotient W.sourcePuncture.pivot).natDegree = 0
    · exact ⟨C, hd, C.goodChallenges_card_floor6401⟩
    · have hdpos : 0 <
          (C.quotient W.sourcePuncture.pivot).natDegree :=
        Nat.pos_of_ne_zero hd
      obtain ⟨H, hHpositive, hHdiv⟩ := hproducer C hdpos
      exact descend (C.extend H hHpositive hHdiv)
  termination_by (C.quotient W.sourcePuncture.pivot).natDegree
  decreasing_by
    exact C.extend_pivot_degree_strict6401 H hHpositive hHdiv
  exact descend C0
theorem exists_nonzeroLaneResultant_of_reapplicableGlobalFactorProducer6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (hproducer : ReapplicableGlobalFactorProducer6401 W)
    (C0 : RecursivePrimitiveLaneState6401 W) :
    ∃ C : RecursivePrimitiveLaneState6401 W,
      C.laneResultant6401 ≠ 0 ∧
        primitiveLaneFactorDescentGoodFloor6401 ≤
          C.goodChallenges6401.card := by
  obtain ⟨C, hdegree, hfloor⟩ :=
    exists_locatorDegreeZero_recursiveState6401 W hproducer C0
  exact ⟨C, C.laneResultant_ne_zero_of_pivot_degree_zero6401 hdegree,
    hfloor⟩
theorem not_all_recursiveLaneResultants_zero6401
    (W : PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S Aset Owner)
    (hproducer : ReapplicableGlobalFactorProducer6401 W)
    (C0 : RecursivePrimitiveLaneState6401 W) :
    ¬ (∀ C : RecursivePrimitiveLaneState6401 W,
      C.laneResultant6401 = 0) := by
  intro hall
  obtain ⟨C, hresultant, _hfloor⟩ :=
    exists_nonzeroLaneResultant_of_reapplicableGlobalFactorProducer6401
      W hproducer C0
  exact hresultant (hall C)
theorem recursiveOwnerFloor_interface_gap6401 :
    extremeOwnerGoodChallengeFloor6401 = 273543241402362822 ∧
      primitiveLaneFactorDescentGoodFloor6401 = 273495283461914576 ∧
      extremeOwnerGoodChallengeFloor6401 -
          primitiveLaneFactorDescentGoodFloor6401 = 47957940448246 := by
  native_decide
end RecursiveState
end BCHKSExtremePrimitiveRecursiveFactorClosure6401
end ProximityPrize.SubmissionLower
