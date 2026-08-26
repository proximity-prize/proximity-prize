import ProximityPrize.SubmissionLower.BCHKSExplicitPairAlignment6400
import ProximityPrize.SubmissionLower.BCHKSJ0PrimitiveTransform6400
import ProximityPrize.SubmissionLower.BCHKSRaisedNumeratorEndpoint6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSJ0MixedGlobalAlignment6400
open ProximityPrize.Benchmark
open Polynomial Polynomial.Bivariate
open BCHKSHybridHighDegreeAudit6400
open BCHKSRaisedNumeratorEndpoint6400
open BCHKSTransformedUniversalTag6400
open BCHKSCoreTransformedUniversalTag6400
open BCHKSMixedUniversalTag6400
open BCHKSExplicitMixedInnerPairs6400
open BCHKSExplicitPairAlignment6400
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
abbrev J0Field := IRSProfile.Field
abbrev J0TriPoly := Polynomial (Polynomial (Polynomial J0Field))
noncomputable def positiveJ0Factors (Q : J0TriPoly) : Finset J0TriPoly :=
  (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
    (fun R => 0 < R.natDegree)
noncomputable def coveredJ0Factors (Q : J0TriPoly) : Finset J0TriPoly :=
  (positiveJ0Factors Q).filter (fun R => R.natDegree <= 209)
abbrev CoveredJ0Factor (Q : J0TriPoly) := ↥(coveredJ0Factors Q)
theorem mem_positiveJ0Factors_iff
    (Q R : J0TriPoly) :
    R ∈ positiveJ0Factors Q ↔
      R ∈ UniqueFactorizationMonoid.normalizedFactors Q ∧
        0 < R.natDegree := by
  classical
  simp [positiveJ0Factors]
theorem mem_coveredJ0Factors_iff
    (Q R : J0TriPoly) :
    R ∈ coveredJ0Factors Q ↔
      R ∈ UniqueFactorizationMonoid.normalizedFactors Q ∧
        0 < R.natDegree ∧ R.natDegree <= 209 := by
  classical
  simp [coveredJ0Factors, positiveJ0Factors, and_assoc]
theorem j0_natDegree_le_84607
    (Q : J0TriPoly) (hQ : Q ≠ 0)
    (hcaps : ∀ j a, (Q.coeff j).coeff a ≠ 0 ->
      j < 84608 ∧ a + 131071 * j < 11089586663 ∧
        ((Q.coeff j).coeff a).natDegree + j < 1688975429) :
    Q.natDegree <= 84607 := by
  have hlead : Q.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hQ
  obtain ⟨a, ha⟩ := Polynomial.support_nonempty.mpr hlead
  have hca : (Q.coeff Q.natDegree).coeff a ≠ 0 := by
    simpa only [Polynomial.leadingCoeff] using
      Polynomial.mem_support_iff.mp ha
  have hj := (hcaps Q.natDegree a hca).1
  omega
theorem j0_badZSpecializations_card_le
    (Q : J0TriPoly) (S : Finset J0Field) (hQ : Q ≠ 0)
    (hcaps : ∀ j a, (Q.coeff j).coeff a ≠ 0 ->
      j < 84608 ∧ a + 131071 * j < 11089586663 ∧
        ((Q.coeff j).coeff a).natDegree + j < 1688975429) :
    (badZSpecializations Q S).card <= bchksHybridQBadCover6400 := by
  have hlead : Q.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hQ
  obtain ⟨a, ha⟩ := Polynomial.support_nonempty.mpr hlead
  have hca : (Q.coeff Q.natDegree).coeff a ≠ 0 := by
    simpa only [Polynomial.leadingCoeff] using
      Polynomial.mem_support_iff.mp ha
  have hdeg := (hcaps Q.natDegree a hca).2.2
  have hcard := badZSpecializations_card_le_natDegree_coeff
    Q S Q.natDegree a hca
  dsimp [bchksHybridQBadCover6400]
  omega
structure CurrentMixedFamily where
  S : Finset J0Field
  P : J0Field -> Polynomial J0Field
  Q : J0TriPoly
  Q_ne : Q ≠ 0
  seed_large : bchksResidualNumerator6400 < S.card
  vanishing : ∀ z ∈ S, triEval Q z (P z) = 0
  support_caps : ∀ j a, (Q.coeff j).coeff a ≠ 0 ->
    j < 84608 ∧ a + 131071 * j < 11089586663 ∧
      ((Q.coeff j).coeff a).natDegree + j < 1688975429
  high : ∀ R : CoveredJ0Factor Q, Not (R.1.natDegree <= 53) ->
    CoreTransformedTagInput J0Field
  low : ∀ R : CoveredJ0Factor Q, R.1.natDegree <= 53 ->
    OrdinaryTagInput J0Field
  highData : ∀ R h, ExplicitInnerData (high R h).toTag
  lowData : ∀ R h, ExplicitInnerData (low R h).toTag
  highBad : ∀ R : CoveredJ0Factor Q,
    Not (R.1.natDegree <= 53) -> Finset J0Field
  lowBad : ∀ R : CoveredJ0Factor Q,
    R.1.natDegree <= 53 -> Finset J0Field
  low_source : ∀ R h, (low R h).source = R.1
  high_source : ∀ R h, (high R h).source = R.1
  low_root : ∀ R h, (low R h).root = P
  high_root : ∀ R h, (high R h).originalRoot = P
  low_owns : ∀ R h,
    ∀ z ∈ S, triEval R.1 z (P z) = 0 -> z ∉ lowBad R h ->
      (low R h).toTag.owns z
  high_owns : ∀ R h,
    ∀ z ∈ S, triEval R.1 z (P z) = 0 -> z ∉ highBad R h ->
      (high R h).toTag.owns z
noncomputable def CurrentMixedFamily.tag
    (M : CurrentMixedFamily) (R : CoveredJ0Factor M.Q) :
    TransformedUniversalTag J0Field :=
  if h : R.1.natDegree <= 53 then (M.low R h).toTag
  else (M.high R h).toTag
noncomputable def CurrentMixedFamily.data
    (M : CurrentMixedFamily) (R : CoveredJ0Factor M.Q) :
    ExplicitInnerData (M.tag R) := by
  classical
  unfold CurrentMixedFamily.tag
  split <;> rename_i h
  · exact M.lowData R h
  · exact M.highData R h
noncomputable def CurrentMixedFamily.bad
    (M : CurrentMixedFamily) (R : CoveredJ0Factor M.Q) : Finset J0Field :=
  if h : R.1.natDegree <= 53 then M.lowBad R h else M.highBad R h
noncomputable def CurrentMixedFamily.lift
    (M : CurrentMixedFamily) (R : CoveredJ0Factor M.Q) :
    AffineRootLift (M.tag R) := by
  classical
  let hlow : Prop := R.1.natDegree <= 53
  let originalRoot : J0Field -> Polynomial J0Field :=
    if h : hlow then (M.low R h).root else (M.high R h).originalRoot
  let base0 : Polynomial J0Field :=
    if h : hlow then 0 else (M.high R h).base0
  let base1 : Polynomial J0Field :=
    if h : hlow then 0 else (M.high R h).base1
  let locator : Polynomial J0Field :=
    if h : hlow then 1 else (M.high R h).locator
  exact {
    originalRoot := originalRoot
    degreeCap := 131071
    base0 := base0
    base1 := base1
    locator := locator
    base0_degree_le := by
      by_cases h : hlow
      · simp [base0, h]
      · simpa [base0, h] using (M.high R h).base0_degree_le
    base1_degree_le := by
      by_cases h : hlow
      · simp [base1, h]
      · simpa [base1, h] using (M.high R h).base1_degree_le
    locator_degree_add_rootCap := by
      by_cases h : hlow
      · simp [locator, CurrentMixedFamily.tag, OrdinaryTagInput.toTag,
          ordinaryUniversalTag, hlow, h]
      · simpa [locator, CurrentMixedFamily.tag, hlow, h] using
          (M.high R h).locator_degree_add_cap
    root_shape := by
      intro z hz
      by_cases h : hlow
      · simp [originalRoot, base0, base1, locator,
          CurrentMixedFamily.tag, hlow, h]
      · simpa [originalRoot, base0, base1, locator,
          CurrentMixedFamily.tag, hlow, h] using
          (M.high R h).quotient_shape (M.high R h).center z
            (by simpa [CurrentMixedFamily.tag, hlow, h] using hz)
  }
@[simp]
theorem CurrentMixedFamily.tag_eq_low
    (M : CurrentMixedFamily) (R : CoveredJ0Factor M.Q)
    (hR : R.1.natDegree <= 53) :
    M.tag R = (M.low R hR).toTag := by
  simp [CurrentMixedFamily.tag, hR]
@[simp]
theorem CurrentMixedFamily.tag_eq_high
    (M : CurrentMixedFamily) (R : CoveredJ0Factor M.Q)
    (hR : Not (R.1.natDegree <= 53)) :
    M.tag R = (M.high R hR).toTag := by
  simp [CurrentMixedFamily.tag, hR]
theorem CurrentMixedFamily.tag_source_eq
    (M : CurrentMixedFamily) (R : CoveredJ0Factor M.Q) :
    (M.tag R).source = R.1 := by
  by_cases hlow : R.1.natDegree <= 53
  · rw [M.tag_eq_low R hlow, OrdinaryTagInput.toTag_source,
      M.low_source R hlow]
  · rw [M.tag_eq_high R hlow, CoreTransformedTagInput.toTag_source,
      M.high_source R hlow]
theorem CurrentMixedFamily.lift_originalRoot_eq
    (M : CurrentMixedFamily) (R : CoveredJ0Factor M.Q) :
    (M.lift R).originalRoot = M.P := by
  by_cases hlow : R.1.natDegree <= 53
  · simpa [CurrentMixedFamily.lift, hlow] using M.low_root R hlow
  · simpa [CurrentMixedFamily.lift, hlow] using M.high_root R hlow
theorem CurrentMixedFamily.lift_degreeCap
    (M : CurrentMixedFamily) (R : CoveredJ0Factor M.Q) :
    (M.lift R).degreeCap = 131071 := by
  rfl
theorem CurrentMixedFamily.lift_locator_eq_low
    (M : CurrentMixedFamily) (R : CoveredJ0Factor M.Q)
    (hlow : R.1.natDegree <= 53) :
    (M.lift R).locator = 1 := by
  simp [CurrentMixedFamily.lift, hlow]
theorem CurrentMixedFamily.lift_locator_eq_high
    (M : CurrentMixedFamily) (R : CoveredJ0Factor M.Q)
    (hlow : Not (R.1.natDegree <= 53)) :
    (M.lift R).locator = (M.high R hlow).locator := by
  simp [CurrentMixedFamily.lift, hlow]
theorem CurrentMixedFamily.sourceMass_le
    (M : CurrentMixedFamily) :
    (∑ R : CoveredJ0Factor M.Q, (M.tag R).source.natDegree) <=
      bchksHybridYMass6400 := by
  classical
  calc
    (∑ R : CoveredJ0Factor M.Q, (M.tag R).source.natDegree) =
        ∑ R : CoveredJ0Factor M.Q, R.1.natDegree := by
      apply Finset.sum_congr rfl
      intro R _hR
      rw [M.tag_source_eq R]
    _ = ∑ R ∈ coveredJ0Factors M.Q, R.natDegree := by
      have h := Finset.sum_attach (coveredJ0Factors M.Q)
        (fun R => R.natDegree)
      rw [Finset.attach_eq_univ] at h
      exact h
    _ <= ∑ R ∈
        (UniqueFactorizationMonoid.normalizedFactors M.Q).toFinset,
          R.natDegree := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro R hR
        exact Multiset.mem_toFinset.mpr
          (mem_coveredJ0Factors_iff M.Q R |>.mp hR).1
      · simp
    _ <= M.Q.natDegree :=
      normalizedFactors_toFinset_sum_natDegree_le M.Q M.Q_ne
    _ <= bchksHybridYMass6400 := by
      simpa [bchksHybridYMass6400] using
        j0_natDegree_le_84607 M.Q M.Q_ne M.support_caps
def ResidualCover210 (M : CurrentMixedFamily) : Prop :=
  ∀ z ∈ M.S,
    z ∉ (Finset.univ : Finset (CoveredJ0Factor M.Q)).biUnion M.bad ->
    ∀ R ∈ positiveJ0Factors M.Q, 210 <= R.natDegree ->
      triEval R z (M.P z) = 0 ->
      ∃ A : CoveredJ0Factor M.Q, (M.tag A).owns z
theorem CurrentMixedFamily.cover_of_residual210
    (M : CurrentMixedFamily) (hresidual : ResidualCover210 M)
    (z : J0Field)
    (hz : z ∈ M.S \
      (badZSpecializations M.Q M.S ∪
        (Finset.univ : Finset (CoveredJ0Factor M.Q)).biUnion M.bad)) :
    ∃ R : CoveredJ0Factor M.Q, (M.tag R).owns z := by
  classical
  have hzS : z ∈ M.S := (Finset.mem_sdiff.mp hz).1
  have hznot : z ∉ badZSpecializations M.Q M.S ∪
      (Finset.univ : Finset (CoveredJ0Factor M.Q)).biUnion M.bad :=
    (Finset.mem_sdiff.mp hz).2
  have hzQbad : z ∉ badZSpecializations M.Q M.S := by
    intro h
    exact hznot (Finset.mem_union_left _ h)
  have hzOuterBad :
      z ∉ (Finset.univ : Finset (CoveredJ0Factor M.Q)).biUnion M.bad := by
    intro h
    exact hznot (Finset.mem_union_right _ h)
  have hQz : triSpecializeZ M.Q z ≠ 0 := by
    intro hzero
    apply hzQbad
    exact Finset.mem_filter.mpr ⟨hzS, hzero⟩
  obtain ⟨R, hRQ, hRpos, hRroot⟩ :=
    exists_positive_normalizedFactor_triEval_eq_zero
      M.Q z (M.P z) hQz (M.vanishing z hzS)
  have hRpositive : R ∈ positiveJ0Factors M.Q :=
    (mem_positiveJ0Factors_iff M.Q R).mpr ⟨hRQ, hRpos⟩
  by_cases hcovered : R.natDegree <= 209
  · have hRcovered : R ∈ coveredJ0Factors M.Q := by
      exact (mem_coveredJ0Factors_iff M.Q R).mpr
        ⟨hRQ, hRpos, hcovered⟩
    let A : CoveredJ0Factor M.Q := ⟨R, hRcovered⟩
    have hzRbad : z ∉ M.bad A := by
      intro hbad
      exact hzOuterBad (Finset.mem_biUnion.mpr ⟨A, Finset.mem_univ A, hbad⟩)
    by_cases hlow : R.natDegree <= 53
    · refine ⟨A, ?_⟩
      rw [M.tag_eq_low A hlow]
      apply M.low_owns A hlow z hzS hRroot
      simpa [CurrentMixedFamily.bad, A, hlow] using hzRbad
    · refine ⟨A, ?_⟩
      rw [M.tag_eq_high A hlow]
      apply M.high_owns A hlow z hzS hRroot
      simpa [CurrentMixedFamily.bad, A, hlow] using hzRbad
  · have hlarge : 210 <= R.natDegree := by omega
    exact hresidual z hzS hzOuterBad R hRpositive hlarge hRroot
structure SelectorLedger (M : CurrentMixedFamily) where
  coordinateCount : Nat
  commonTarget : Nat
  rowLower : Nat
  outerBadCap : Nat
  resultCap : Nat
  fusedCap : Nat
  outerBad_sum :
    (∑ R : CoveredJ0Factor M.Q, (M.bad R).card) <= outerBadCap
  tagCharge :
    (∑ R : CoveredJ0Factor M.Q,
      2 * FiniteHenselWeight.denominatorExponent (M.tag R).rootDegreeCap *
        (M.tag R).source.natDegree * (M.data R).supportCap) <= resultCap
  fused :
    (coordinateCount - commonTarget) * resultCap <=
      (rowLower - commonTarget) * fusedCap
  total_le_residual :
    bchksHybridQBadCover6400 + outerBadCap +
      (fusedCap + (bchksErrors6400 + 1) * bchksHybridYMass6400) <=
        bchksResidualNumerator6400
noncomputable def CurrentMixedFamily.globalSelectorData
    (M : CurrentMixedFamily) (L : SelectorLedger M)
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
  coordinateCount := L.coordinateCount
  commonTarget := L.commonTarget
  rowLower := L.rowLower
  errors := bchksErrors6400
  quotientBadCap := bchksHybridQBadCover6400
  outerBadCap := L.outerBadCap
  resultCap := L.resultCap
  pairCap := bchksHybridYMass6400
  fusedCap := L.fusedCap
  quotientBad_card :=
    j0_badZSpecializations_card_le M.Q M.S M.Q_ne M.support_caps
  outerBad_sum := L.outerBad_sum
  tagCharge := L.tagCharge
  sourceMass := M.sourceMass_le
  fused := L.fused
  cover := by
    intro z hz
    obtain ⟨R, hR⟩ := M.cover_of_residual210 hresidual z hz
    exact ⟨R, Finset.mem_univ R, hR⟩
  large := L.total_le_residual.trans_lt M.seed_large
}
structure AlignmentInput
    (M : CurrentMixedFamily) (L : SelectorLedger M) where
  coords : Finset IRSProfile.Index
  agreementRows : J0Field -> Finset IRSProfile.Index
  received : Fin 2 -> IRSProfile.Index -> J0Field
  coordinate_card : L.coordinateCount = coords.card
  rowLower_le : L.rowLower <= coords.card
  commonTarget_lt : L.commonTarget < L.rowLower
  row_large : ∀ z ∈ M.S, L.rowLower <=
    (coords.attach.filter fun i : coords =>
      (i : IRSProfile.Index) ∈ agreementRows z).card
  low_commonTarget : 131071 <= L.commonTarget
  high_root_caps : ∀ R : CoveredJ0Factor M.Q,
    ∀ h : Not (R.1.natDegree <= 53),
      0 < (M.high R h).rootDegreeCap ∧
      (M.high R h).rootDegreeCap <= L.commonTarget
  support_caps : ∀ R : CoveredJ0Factor M.Q,
    0 < (M.data R).supportCap
  high_locator_nonzero : ∀ R : CoveredJ0Factor M.Q,
    ∀ h : Not (R.1.natDegree <= 53), ∀ i ∈ coords,
      (M.high R h).locator.eval (IRSProfile.domain i) ≠ 0
  original_agrees : ∀ z ∈ M.S, ∀ i ∈ agreementRows z,
    (M.P z).eval (IRSProfile.domain i) =
      received 0 i + z * received 1 i
noncomputable def AlignmentInput.globalAlignmentData
    (M : CurrentMixedFamily) (L : SelectorLedger M)
    (hresidual : ResidualCover210 M) (C : AlignmentInput M L) :
    GlobalAlignmentData (M.globalSelectorData L hresidual)
      IRSProfile.Index := {
  lift := M.lift
  coords := C.coords
  domain := IRSProfile.domain
  domain_injective := IRSProfile.domain.injective
  agreementRows := C.agreementRows
  received0 := C.received 0
  received1 := C.received 1
  coordinate_card := C.coordinate_card
  rowLower_le := C.rowLower_le
  commonTarget_lt := C.commonTarget_lt
  row_large := C.row_large
  root_caps := by
    intro R _hR
    change 0 < (M.tag R).rootDegreeCap ∧
      (M.tag R).rootDegreeCap <= L.commonTarget ∧
      (M.tag R).rootDegreeCap < Fintype.card J0Field
    by_cases hlow : R.1.natDegree <= 53
    · rw [M.tag_eq_low R hlow]
      change 0 < 131071 ∧ 131071 <= L.commonTarget ∧
        131071 < Fintype.card J0Field
      exact ⟨by norm_num, C.low_commonTarget, by
        norm_num [J0Field, IRSProfile.Field, KoalaBear.Ext6,
          KoalaBear.fieldSize]⟩
    · rw [M.tag_eq_high R hlow,
        CoreTransformedTagInput.toTag_rootDegreeCap]
      have hcoord : C.coords.card <= 262144 := by
        have h := Finset.card_le_univ C.coords
        simpa [IRSProfile.Index] using h
      have htarget : L.commonTarget < 262144 :=
        C.commonTarget_lt.trans_le (C.rowLower_le.trans hcoord)
      have hfield : 262144 < Fintype.card J0Field := by
        norm_num [J0Field, IRSProfile.Field, KoalaBear.Ext6,
          KoalaBear.fieldSize]
      exact ⟨(C.high_root_caps R hlow).1,
        (C.high_root_caps R hlow).2,
        (C.high_root_caps R hlow).2.trans_lt
          (htarget.trans hfield)⟩
  support_caps := by
    intro R _hR
    exact C.support_caps R
  locator_nonzero := by
    intro R _hR i hi
    change (M.lift R).locator.eval (IRSProfile.domain i) ≠ 0
    by_cases hlow : R.1.natDegree <= 53
    · rw [M.lift_locator_eq_low R hlow]
      simp
    · rw [M.lift_locator_eq_high R hlow]
      exact C.high_locator_nonzero R hlow i hi
  original_agrees := by
    intro R _hR z hzS _hzowns i hi
    rw [M.lift_originalRoot_eq R]
    exact C.original_agrees z hzS i hi
}
theorem exists_j0_originalRoot_affine_alignment_of_residual210
    (M : CurrentMixedFamily) (L : SelectorLedger M)
    (C : AlignmentInput M L) (hresidual : ResidualCover210 M) :
    ∃ R ∈ coveredJ0Factors M.Q, ∃ T : Finset J0Field,
      T ⊆ M.S ∧ bchksErrors6400 + 1 < T.card ∧
      ∃ p0 p1 : Polynomial J0Field,
        p0.natDegree <= 131071 ∧ p1.natDegree <= 131071 ∧
        ∀ z ∈ T, M.P z = p0 + Polynomial.C z * p1 := by
  let G := M.globalSelectorData L hresidual
  let A := C.globalAlignmentData M L hresidual
  obtain ⟨R, hR, T, hTS, hTcard, p0, p1, hp0, hp1, halign⟩ :=
    exists_originalRoot_affine_alignment_of_global_selector G A
  change T ⊆ M.S at hTS
  change bchksErrors6400 + 1 < T.card at hTcard
  change p0.natDegree <= (M.lift R).degreeCap at hp0
  change p1.natDegree <= (M.lift R).degreeCap at hp1
  change ∀ z ∈ T, (M.lift R).originalRoot z =
    p0 + Polynomial.C z * p1 at halign
  refine ⟨R.1, R.property, T, hTS, ?_, p0, p1, ?_, ?_, ?_⟩
  · exact hTcard
  · simpa [M.lift_degreeCap R] using hp0
  · simpa [M.lift_degreeCap R] using hp1
  · intro z hz
    have h := halign z hz
    rw [M.lift_originalRoot_eq R] at h
    exact h
end BCHKSJ0MixedGlobalAlignment6400
end ProximityPrize.SubmissionLower
