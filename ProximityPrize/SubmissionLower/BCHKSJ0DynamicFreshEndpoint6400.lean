import ProximityPrize.SubmissionLower.BCHKSJ0MixedGlobalAlignment6400
import ProximityPrize.SubmissionLower.BCHKSFreshQuotientFirstStage6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSJ0DynamicFreshEndpoint6400
open ProximityPrize.Benchmark
open Polynomial Polynomial.Bivariate
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators
open UniversalNumerator
open BCHKSJ0MixedGlobalAlignment6400
open BCHKSExplicitMixedInnerPairs6400
open BCHKSExplicitPairAlignment6400
open BCHKSFreshQuotientUniversalSelector6400
open BCHKSFreshQuotientFirstStage6400
open BCHKSDynamicCoreArithmetic6400
open BCHKSHybridHighDegreeAudit6400
open BCHKSRaisedNumeratorEndpoint6400
open BCHKSMixedUniversalTag6400
open BCHKSCoreTransformedUniversalTag6400
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000
structure DynamicSelectorLedger (M : CurrentMixedFamily) where
  degree : Nat
  degree_le : degree <= 209
  outerBad_sum :
    (∑ R : CoveredJ0Factor M.Q, (M.bad R).card) <=
      2 * degree * bchksHybridZMass6400
  tagCharge :
    (∑ R : CoveredJ0Factor M.Q,
      2 * FiniteHenselWeight.denominatorExponent
          (M.tag R).rootDegreeCap *
        (M.tag R).source.natDegree * (M.data R).supportCap) <=
      2 * (2 * dynamicRootCap6400 - 1) * degree *
        bchksHybridZMass6400
noncomputable def CurrentMixedFamily.dynamicGlobalSelectorData
    (M : CurrentMixedFamily) (L : DynamicSelectorLedger M)
    (hresidual : ResidualCover210 M) :
    GlobalSelectorData J0Field (CoveredJ0Factor M.Q) := {
  S := M.S
  quotientBad := badZSpecializations M.Q M.S
  outer := Finset.univ
  outerBad := M.bad
  tag := M.tag
  data := M.data
  exponent := fun R =>
    FiniteHenselWeight.denominatorExponent (M.tag R).rootDegreeCap
  exponent_eq := fun _ => rfl
  coordinateCount := 262144
  commonTarget := 20230
  rowLower := 185364
  errors := freshSelectorThreshold
  quotientBadCap := bchksHybridQBadCover6400
  outerBadCap := 2 * L.degree * bchksHybridZMass6400
  resultCap := 2 * (2 * dynamicRootCap6400 - 1) * L.degree *
    bchksHybridZMass6400
  pairCap := bchksHybridYMass6400
  fusedCap := freshFirstStageUnit6400 * L.degree *
    bchksHybridZMass6400
  quotientBad_card :=
    j0_badZSpecializations_card_le M.Q M.S M.Q_ne M.support_caps
  outerBad_sum := by simpa using L.outerBad_sum
  tagCharge := by simpa using L.tagCharge
  sourceMass := by simpa using M.sourceMass_le
  fused := by
    have hbase :
        (262144 - 20230) * (2 * (2 * dynamicRootCap6400 - 1)) <=
          (185364 - 20230) * freshFirstStageUnit6400 := by
      norm_num [dynamicRootCap6400, freshFirstStageUnit6400,
        freshQuotientN6400, freshQuotientA6400, ceilDiv]
    calc
      (262144 - 20230) *
          (2 * (2 * dynamicRootCap6400 - 1) * L.degree *
            bchksHybridZMass6400) =
        ((262144 - 20230) *
          (2 * (2 * dynamicRootCap6400 - 1))) *
            (L.degree * bchksHybridZMass6400) := by ring
      _ <= ((185364 - 20230) * freshFirstStageUnit6400) *
          (L.degree * bchksHybridZMass6400) :=
        Nat.mul_le_mul_right (L.degree * bchksHybridZMass6400) hbase
      _ = (185364 - 20230) *
          (freshFirstStageUnit6400 * L.degree *
            bchksHybridZMass6400) := by ring
  cover := by
    intro z hz
    obtain ⟨R, hR⟩ := M.cover_of_residual210 hresidual z hz
    exact ⟨R, Finset.mem_univ R, hR⟩
  large := by
    have hbudget := freshNested_corrected_fits_of_degree_le2096400
      L.degree L.degree_le
    have htotal :
        bchksHybridQBadCover6400 +
            2 * L.degree * bchksHybridZMass6400 +
            (freshFirstStageUnit6400 * L.degree *
                bchksHybridZMass6400 +
              (freshSelectorThreshold + 1) * bchksHybridYMass6400) =
          freshNestedTotalCorrected6400 L.degree := by
      have hthreshold : freshSelectorThreshold =
          freshUniversalThresholdCorrected6400 := by
        norm_num [freshSelectorThreshold, freshUniversalThresholdCorrected6400,
          freshUniversalThreshold6400, freshOuterBadCap6400,
          freshUniversalFusedResultant6400, freshUniversalRawResultant6400,
          freshFactorMass6400, freshFactorZMass6400, freshQuotientN6400,
          freshQuotientK6400, freshQuotientA6400, freshYCap6400,
          freshZCap6400, dynamicLineCap6400, freshErrors, freshFactorMass,
          freshFactorZMass, freshFusedResultantCap, ceilDiv]
      rw [hthreshold]
      unfold freshNestedTotalCorrected6400
      ring
    rw [htotal]
    exact hbudget.trans M.seed_large
}
noncomputable def dynamicSelectorData
    (M : CurrentMixedFamily) (L : DynamicSelectorLedger M)
    (hresidual : ResidualCover210 M) :
    GlobalSelectorData J0Field (CoveredJ0Factor M.Q) :=
  BCHKSJ0DynamicFreshEndpoint6400.CurrentMixedFamily.dynamicGlobalSelectorData
    M L hresidual
@[simp] theorem dynamicGlobalSelectorData_errors
    (M : CurrentMixedFamily) (L : DynamicSelectorLedger M)
    (hresidual : ResidualCover210 M) :
    (dynamicSelectorData M L hresidual).errors =
      freshSelectorThreshold := rfl
structure DynamicEvaluationInput (M : CurrentMixedFamily) where
  agreementRows : J0Field -> Finset IRSProfile.Index
  received : Fin 2 -> IRSProfile.Index -> J0Field
  agreement_card : ∀ z ∈ M.S, 185364 <= (agreementRows z).card
  support_caps : ∀ R : CoveredJ0Factor M.Q,
    0 < (M.data R).supportCap
  original_agrees : ∀ z ∈ M.S, ∀ i ∈ agreementRows z,
    (M.P z).eval (IRSProfile.domain i) =
      received 0 i + z * received 1 i
theorem CurrentMixedFamily.data_supportCap_pos
    (M : CurrentMixedFamily) (R : CoveredJ0Factor M.Q) :
    0 < (M.data R).supportCap := by
  let D := M.data R
  have hne : D.inner ≠ 0 :=
    Polynomial.ne_zero_of_natDegree_gt D.inner_degree_pos
  have hmem : D.inner.natDegree ∈ D.inner.support :=
    Polynomial.mem_support_iff.mpr
      (Polynomial.leadingCoeff_ne_zero.mpr hne)
  have hdegree : D.inner.natDegree ≤
      Polynomial.Bivariate.totalDegree D.inner := by
    have hcoeff := Polynomial.Bivariate.coeff_totalDegree_le D.inner hmem
    omega
  exact D.inner_degree_pos.trans_le
    (hdegree.trans D.inner_totalDegree_le)
structure SelectedCoreProfile
    (M : CurrentMixedFamily) (L : DynamicSelectorLedger M)
    (hresidual : ResidualCover210 M)
    (W : SelectedExplicitPairFiber
      (dynamicSelectorData M L hresidual)) where
  existingCore : Finset IRSProfile.Index
  codim : Nat
  core_card : existingCore.card = codim
  rootCap_add_codim :
    (M.tag W.pair.1).rootDegreeCap + codim = 131071
  codim_le : codim <= 20230
  locator_nonzero : ∀ i ∈ (Finset.univ \ existingCore :
      Finset IRSProfile.Index),
    (M.lift W.pair.1).locator.eval (IRSProfile.domain i) ≠ 0
theorem CurrentMixedFamily.lift_locator_ne_zero
    (M : CurrentMixedFamily) (R : CoveredJ0Factor M.Q) :
    (M.lift R).locator ≠ 0 := by
  by_cases hlow : R.1.natDegree ≤ 53
  · rw [M.lift_locator_eq_low R hlow]
    exact one_ne_zero
  · rw [M.lift_locator_eq_high R hlow]
    exact (M.high R hlow).locator_ne_zero
theorem exists_selectedCoreProfile_of_rootCap_floor
    (M : CurrentMixedFamily) (L : DynamicSelectorLedger M)
    (hresidual : ResidualCover210 M)
    (W : SelectedExplicitPairFiber
      (dynamicSelectorData M L hresidual))
    (hfloor : freshRootCap ≤ (M.tag W.pair.1).rootDegreeCap) :
    Nonempty (SelectedCoreProfile M L hresidual W) := by
  classical
  let G : J0Field[X] := (M.lift W.pair.1).locator
  let zeroIdx : Finset IRSProfile.Index :=
    Finset.univ.filter fun i => G.eval (IRSProfile.domain i) = 0
  have hG : G ≠ 0 := by
    simpa [G] using CurrentMixedFamily.lift_locator_ne_zero
      (M := M) W.pair.1
  have hZimage :
      (zeroIdx.image IRSProfile.domain).card = zeroIdx.card :=
    Finset.card_image_iff.mpr fun i _hi j _hj hij =>
      IRSProfile.domain.injective hij
  have hZsub : zeroIdx.image IRSProfile.domain ⊆ G.roots.toFinset := by
    intro x hx
    obtain ⟨i, hiZ, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hG]
    exact (Finset.mem_filter.mp hiZ).2
  have hZdegree : zeroIdx.card ≤ G.natDegree := by
    calc
      zeroIdx.card = (zeroIdx.image IRSProfile.domain).card := hZimage.symm
      _ ≤ G.roots.toFinset.card := Finset.card_le_card hZsub
      _ ≤ G.roots.card := Multiset.toFinset_card_le _
      _ ≤ G.natDegree := Polynomial.card_roots' G
  have hlocatorDegree :
      G.natDegree + (M.tag W.pair.1).rootDegreeCap ≤ 131071 := by
    simpa [G, M.lift_degreeCap W.pair.1] using
      (M.lift W.pair.1).locator_degree_add_rootCap
  let c := 131071 - (M.tag W.pair.1).rootDegreeCap
  have hZc : zeroIdx.card ≤ c := by
    dsimp [c]
    omega
  have hcUniverse : c ≤ Fintype.card IRSProfile.Index := by
    dsimp [c]
    norm_num [IRSProfile.Index]
    omega
  obtain ⟨E, hZE, hEcard⟩ :=
    Finset.exists_superset_card_eq hZc hcUniverse
  refine ⟨{
    existingCore := E
    codim := c
    core_card := hEcard
    rootCap_add_codim := ?_
    codim_le := ?_
    locator_nonzero := ?_
  }⟩
  · dsimp [c]
    omega
  · dsimp [c]
    norm_num [freshRootCap] at hfloor ⊢
    omega
  · intro i hi hzero
    have hiZ : i ∈ zeroIdx := Finset.mem_filter.mpr ⟨Finset.mem_univ i, by
      simpa [G] using hzero⟩
    exact (Finset.mem_sdiff.mp hi).2 (hZE hiZ)
noncomputable def SelectedCoreProfile.coordinateData
    (M : CurrentMixedFamily) (L : DynamicSelectorLedger M)
    (hresidual : ResidualCover210 M)
    (E : DynamicEvaluationInput M)
    (W : SelectedExplicitPairFiber
      (dynamicSelectorData M L hresidual))
    (C : SelectedCoreProfile M L hresidual W) :
    DynamicCoreCoordinateData W IRSProfile.Index := {
  coords := Finset.univ \ C.existingCore
  domain := IRSProfile.domain
  lift := M.lift W.pair.1
  agreementRows := fun z => E.agreementRows z \ C.existingCore
  received0 := E.received 0
  received1 := E.received 1
  rowLower := 185364 - C.codim
  row_large := by
    intro z hz
    have hzS : z ∈ M.S := W.fiber_subset hz
    have hdiff := Finset.le_card_sdiff C.existingCore (E.agreementRows z)
    rw [C.core_card] at hdiff
    rw [Finset.filter_attach
      (fun i : IRSProfile.Index =>
        i ∈ E.agreementRows z \ C.existingCore)
      (Finset.univ \ C.existingCore),
      Finset.card_map, Finset.card_attach]
    have heq :
        (Finset.univ \ C.existingCore).filter
            (fun i => i ∈ E.agreementRows z \ C.existingCore) =
          E.agreementRows z \ C.existingCore := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
        true_and]
      tauto
    rw [heq]
    have hzcard := E.agreement_card z hzS
    omega
  support_cap := by
    simpa only [dynamicSelectorData,
      BCHKSJ0DynamicFreshEndpoint6400.CurrentMixedFamily.dynamicGlobalSelectorData]
      using
      E.support_caps W.pair.1
  locator_nonzero := C.locator_nonzero
  original_agrees := by
    intro z hz i hi
    have hzS : z ∈ M.S := W.fiber_subset hz
    rw [show (M.lift W.pair.1).originalRoot = M.P by
      exact M.lift_originalRoot_eq W.pair.1]
    exact E.original_agrees z hzS i (Finset.mem_sdiff.mp hi).1
}
theorem SelectedCoreProfile.fresh_gaps
    (M : CurrentMixedFamily) (L : DynamicSelectorLedger M)
    (hresidual : ResidualCover210 M)
    (E : DynamicEvaluationInput M)
    (W : SelectedExplicitPairFiber
      (dynamicSelectorData M L hresidual))
    (C : SelectedCoreProfile M L hresidual W) :
    let D := C.coordinateData M L hresidual E W
    freshRootCap <= (M.tag W.pair.1).rootDegreeCap ∧
      D.coords.card -
          ((M.tag W.pair.1).rootDegreeCap - freshRootCap) = 241914 ∧
      D.rowLower -
          ((M.tag W.pair.1).rootDegreeCap - freshRootCap) = 165134 := by
  dsimp only
  have hcoordCard :
      (Finset.univ \ C.existingCore : Finset IRSProfile.Index).card +
          C.codim = 262144 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, C.core_card]
    norm_num [IRSProfile.Index]
    have hc := C.codim_le
    omega
  have hrowCard : (185364 - C.codim) + C.codim = 185364 := by
    have hc := C.codim_le
    omega
  exact dynamic_profile_gaps_of_codim_le20230
    (M.tag W.pair.1).rootDegreeCap C.codim
    (Finset.univ \ C.existingCore : Finset IRSProfile.Index).card
    (185364 - C.codim) C.rootCap_add_codim hcoordCard hrowCard
      C.codim_le
structure CompleteFreshOutcome
    (M : CurrentMixedFamily) (L : DynamicSelectorLedger M)
    (hresidual : ResidualCover210 M)
    (W : SelectedExplicitPairFiber
      (dynamicSelectorData M L hresidual)) where
  Core : Finset J0Field
  U0 : J0Field -> J0Field
  U1 : J0Field -> J0Field
  omega : Fin 241914 ↪ J0Field
  B0 : J0Field[X]
  B1 : J0Field[X]
  Q : W.fiber -> J0Field[X]
  Qfresh : J0Field[X][X][Y]
  x1 : J0Field
  RH : BCHKSFreshQuotientUniversalSelector6400.Pair
  T1 : Finset J0Field
  Coord : Finset (Fin 241914)
  core_degree : Core.card + freshRootCap =
    (M.tag W.pair.1).rootDegreeCap
  outside : ∀ i, omega i ∉ Core
  base0_degree : B0.natDegree ≤ (M.tag W.pair.1).rootDegreeCap
  base1_degree : B1.natDegree ≤ (M.tag W.pair.1).rootDegreeCap
  quotient_degree : ∀ z : W.fiber, (Q z).natDegree <= freshRootCap
  quotient_shape : ∀ z : W.fiber,
    (M.tag W.pair.1).root z =
      B0 + Polynomial.C (z : J0Field) * B1 +
        BCHKSFullCoreLineArrangement6400.coreLocator Core * Q z
  fresh_ne : Qfresh ≠ 0
  fresh_roots : ∀ z : W.fiber, triEval Qfresh (z : J0Field) (Q z) = 0
  fresh_caps : BCHKSFreshQuotientUniversalSelector6400.SupportCaps Qfresh
  pair_mem : RH ∈ UniversalOuterCover6399.pairs Qfresh x1
  pair_good :
    (triSpecializeX RH.1 x1).IsPrimitive ∧
      Polynomial.eval (Polynomial.C x1)
        (factorXObstruction RH.1) ≠ 0 ∧
      triSpecializeX RH.1 x1 ≠ 0 ∧
      (triSpecializeX RH.1 x1).natDegree = RH.1.natDegree ∧
      Polynomial.eval (Polynomial.C x1)
        (rawSepResultant RH.1) ≠ 0
  fibre_subset : T1 ⊆ W.fiber
  fibre_large : freshErrors + 1 < T1.card
  coordinate_large : freshRootCap + 1 <= Coord.card
  pair_relation : ∀ z ∈ T1,
    UniversalOuterCover6399.pairRel
      (fun w ↦ if hw : w ∈ W.fiber then Q ⟨w, hw⟩ else 0)
      x1 z RH
  obstruction_divisibility : ∀ i ∈ Coord, RH.2 ∣
    concreteUniversalAffineObstruction x1 RH.1
      freshExponent freshRootCap (omega i - x1)
      (BCHKSDynamicCoreSelector6400.quotientReceived0 Core B0 U0 (omega i))
      (BCHKSDynamicCoreSelector6400.quotientReceived1 Core B1 U1 (omega i))
theorem exists_completeFreshOutcome_of_degree_le209
    (M : CurrentMixedFamily) (L : DynamicSelectorLedger M)
    (hresidual : ResidualCover210 M)
    (E : DynamicEvaluationInput M)
    (profile : ∀ W : SelectedExplicitPairFiber
      (dynamicSelectorData M L hresidual),
      SelectedCoreProfile M L hresidual W) :
    ∃ W : SelectedExplicitPairFiber
        (dynamicSelectorData M L hresidual),
      Nonempty (CompleteFreshOutcome M L hresidual W) := by
  classical
  let G := dynamicSelectorData M L hresidual
  let W : SelectedExplicitPairFiber G :=
    Classical.choice G.exists_selectedExplicitPairFiber
  let C := profile W
  let D := C.coordinateData M L hresidual E W
  have hgaps := C.fresh_gaps M L hresidual E W
  obtain ⟨Core, U0, U1, omega, B0, B1, Q, Qfresh, x1, RH,
      T1, Coord, hcore, houtside, hB0degree, hB1degree, hQdegree,
      hQshape, hQfresh,
      hQeval, hcaps, hpair, hgood, hTsub, hTlarge, hCoord, hrel,
      hdiv⟩ :=
    BCHKSFreshQuotientFirstStage6400.SelectedExplicitPairFiber.exists_completeFreshQuotientChain20230
      W D rfl rfl rfl rfl hgaps.1 hgaps.2.1 hgaps.2.2
  refine ⟨W, ⟨{
    Core := Core
    U0 := U0
    U1 := U1
    omega := omega
    B0 := B0
    B1 := B1
    Q := Q
    Qfresh := Qfresh
    x1 := x1
    RH := RH
    T1 := T1
    Coord := Coord
    core_degree := hcore
    outside := houtside
    base0_degree := hB0degree
    base1_degree := hB1degree
    quotient_degree := hQdegree
    quotient_shape := hQshape
    fresh_ne := hQfresh
    fresh_roots := hQeval
    fresh_caps := hcaps
    pair_mem := hpair
    pair_good := hgood
    fibre_subset := hTsub
    fibre_large := hTlarge
    coordinate_large := hCoord
    pair_relation := hrel
    obstruction_divisibility := hdiv
  }⟩⟩
theorem CurrentMixedFamily.tag_rootCap_floor_of_high
    (M : CurrentMixedFamily)
    (hhigh : ∀ R : CoveredJ0Factor M.Q,
      ∀ h : ¬ R.1.natDegree ≤ 53,
        freshRootCap ≤ (M.high R h).rootDegreeCap) :
    ∀ R : CoveredJ0Factor M.Q,
      freshRootCap ≤ (M.tag R).rootDegreeCap := by
  intro R
  by_cases hlow : R.1.natDegree ≤ 53
  · rw [M.tag_eq_low R hlow]
    norm_num [OrdinaryTagInput.toTag, ordinaryUniversalTag, freshRootCap]
  · rw [M.tag_eq_high R hlow,
      CoreTransformedTagInput.toTag_rootDegreeCap]
    exact hhigh R hlow
theorem exists_completeFreshOutcome_of_degree_le209_of_rootCap_floor
    (M : CurrentMixedFamily) (L : DynamicSelectorLedger M)
    (hresidual : ResidualCover210 M)
    (E : DynamicEvaluationInput M)
    (hfloor : ∀ R : CoveredJ0Factor M.Q,
      freshRootCap ≤ (M.tag R).rootDegreeCap) :
    ∃ W : SelectedExplicitPairFiber
        (dynamicSelectorData M L hresidual),
      Nonempty (CompleteFreshOutcome M L hresidual W) := by
  apply exists_completeFreshOutcome_of_degree_le209 M L hresidual E
  intro W
  exact Classical.choice
    (exists_selectedCoreProfile_of_rootCap_floor M L hresidual W
      (hfloor W.pair.1))
end BCHKSJ0DynamicFreshEndpoint6400
end ProximityPrize.SubmissionLower
