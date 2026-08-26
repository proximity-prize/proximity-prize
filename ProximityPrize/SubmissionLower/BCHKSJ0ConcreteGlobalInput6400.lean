import ProximityPrize.SubmissionLower.BCHKSJ0Interpolation6400
import ProximityPrize.SubmissionLower.BCHKSJ0MixedGlobalAlignment6400
import ProximityPrize.SubmissionLower.BCHKSJ0DynamicFreshEndpoint6400

namespace ProximityPrize.SubmissionLower
namespace BCHKSJ0ConcreteGlobalInput6400

open ProximityPrize.Benchmark
open Polynomial Polynomial.Bivariate
open BCHKSSubstitutionVanish
open BCHKSJ0MixedGlobalAlignment6400
open BCHKSCoreTransformedUniversalTag6400
open BCHKSMixedUniversalTag6400
open BCHKSExplicitMixedInnerPairs6400
open BCHKSJ0DynamicFreshEndpoint6400

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

/-!
This file separates the genuinely concrete J0/IRS front end from the
factor-local branch certificates still needed by the mixed selector.

`exists_j0BenchmarkInterpolant` constructs a total root family, the J0
interpolant, all support caps, and the benchmark agreement identities
directly from the hypotheses of `AffineLineAlignmentBound`.  The subsequent
constructor shows exactly which factor-local objects are not yet supplied by
that interpolation theorem; those objects are recorded in
`MixedBranchCertificates` rather than hidden inside a claimed benchmark
closure.
-/

abbrev Field := IRSProfile.Field
abbrev Index := IRSProfile.Index
abbrev TriPoly := Polynomial (Polynomial (Polynomial Field))

/-- Extend the subtype-indexed polynomial family returned by J0
interpolation to the whole challenge field.  Only values on `S` are used. -/
noncomputable def extendRootFamily
    (S : Finset Field) (P : ↑S → Polynomial Field) :
    Field → Polynomial Field := fun z ↦
  if hz : z ∈ S then P ⟨z, hz⟩ else 0

@[simp]
theorem extendRootFamily_apply_mem
    (S : Finset Field) (P : ↑S → Polynomial Field)
    (z : Field) (hz : z ∈ S) :
    extendRootFamily S P z = P ⟨z, hz⟩ := by
  simp [extendRootFamily, hz]

/-- The complete output of the compiled J0 interpolation/root-counting
front end, with roots exposed as a total function. -/
structure J0BenchmarkInterpolant
    (U : Fin 2 → Index → Field)
    (S : Finset Field) (A : Field → Finset Index) where
  P : Field → Polynomial Field
  Q : TriPoly
  Q_ne : Q ≠ 0
  root_degree : ∀ z ∈ S, (P z).natDegree ≤ 131071
  agrees : ∀ z ∈ S, ∀ i ∈ A z,
    (P z).eval (IRSProfile.domain i) = U 0 i + z * U 1 i
  vanishing : ∀ z ∈ S,
    BCHKSSubstitutionVanish.triEval Q z (P z) = 0
  support_caps : ∀ j a, (Q.coeff j).coeff a ≠ 0 →
    j < 84608 ∧ a + 131071 * j < 11089586663 ∧
      ((Q.coeff j).coeff a).natDegree + j < 1688975429

/-- Unconditional constructor of all global interpolation and agreement
fields used downstream. -/
theorem exists_j0BenchmarkInterpolant
    (U : Fin 2 → Index → Field)
    (S : Finset Field) (A : Field → Finset Index)
    (hA : ∀ z ∈ S, 185364 ≤ (A z).card)
    (hcomb : ∀ z ∈ S,
      LinearCode.projectedWord (fun i ↦ U 0 i + z * U 1 i) (A z) ∈
        LinearCode.projectedCodeSubmod IRSProfile.baseCode (A z)) :
    Nonempty (J0BenchmarkInterpolant U S A) := by
  classical
  obtain ⟨Psub, Q, hQ, hPdegree, hPagree, hvanishing, hcaps⟩ :=
    exists_bchks_j0_interpolant_vanishing6400 U S A hA hcomb
  let P : Field → Polynomial Field := extendRootFamily S Psub
  refine ⟨{
    P := P
    Q := Q
    Q_ne := hQ
    root_degree := ?_
    agrees := ?_
    vanishing := ?_
    support_caps := hcaps
  }⟩
  · intro z hz
    simpa [P, extendRootFamily, hz] using hPdegree ⟨z, hz⟩
  · intro z hz i hi
    simpa [P, extendRootFamily, hz] using hPagree ⟨z, hz⟩ i hi
  · intro z hz
    simpa [P, extendRootFamily, hz] using hvanishing ⟨z, hz⟩

/-- Exact list of factor-local certificates not manufactured by J0
interpolation.  The low and high constructors are requested only in their
actual degree branches. -/
structure MixedBranchCertificates
    {U : Fin 2 → Index → Field}
    {S : Finset Field} {A : Field → Finset Index}
    (J : J0BenchmarkInterpolant U S A) where
  high : ∀ R : CoveredJ0Factor J.Q,
    ¬ R.1.natDegree ≤ 53 → CoreTransformedTagInput Field
  low : ∀ R : CoveredJ0Factor J.Q,
    R.1.natDegree ≤ 53 → OrdinaryTagInput Field
  highData : ∀ R h, ExplicitInnerData (high R h).toTag
  lowData : ∀ R h, ExplicitInnerData (low R h).toTag
  highBad : ∀ R : CoveredJ0Factor J.Q,
    ¬ R.1.natDegree ≤ 53 → Finset Field
  lowBad : ∀ R : CoveredJ0Factor J.Q,
    R.1.natDegree ≤ 53 → Finset Field
  low_source : ∀ R h, (low R h).source = R.1
  high_source : ∀ R h, (high R h).source = R.1
  low_root : ∀ R h, (low R h).root = J.P
  high_root : ∀ R h, (high R h).originalRoot = J.P
  low_owns : ∀ R h, ∀ z ∈ S,
    BCHKSSubstitutionVanish.triEval R.1 z (J.P z) = 0 →
      z ∉ lowBad R h →
      (low R h).toTag.owns z
  high_owns : ∀ R h, ∀ z ∈ S,
    BCHKSSubstitutionVanish.triEval R.1 z (J.P z) = 0 →
      z ∉ highBad R h →
      (high R h).toTag.owns z

/-- The low certificate is stronger than merely choosing a primitive
factor-local center: its one stored inner polynomial must contain every good
owner root routed to this tag.  This theorem makes that still-unconstructed
coverage obligation explicit. -/
theorem MixedBranchCertificates.low_fixedInner_covers_good_root
    {U : Fin 2 → Index → Field}
    {S : Finset Field} {A : Field → Finset Index}
    {J : J0BenchmarkInterpolant U S A}
    (B : MixedBranchCertificates J)
    (R : CoveredJ0Factor J.Q) (h : R.1.natDegree ≤ 53)
    (z : Field) (hzS : z ∈ S)
    (hzroot : BCHKSSubstitutionVanish.triEval R.1 z (J.P z) = 0)
    (hzbad : z ∉ B.lowBad R h) :
    biEval (B.lowData R h).inner
      (((B.low R h).root z).eval (B.low R h).center) z = 0 := by
  exact (B.lowData R h).owner_root z
    (B.low_owns R h z hzS hzroot hzbad)

/-- High-branch analogue: the explicitly transported inner polynomial must
cover every good owner assigned to the transformed tag. -/
theorem MixedBranchCertificates.high_fixedInner_covers_good_root
    {U : Fin 2 → Index → Field}
    {S : Finset Field} {A : Field → Finset Index}
    {J : J0BenchmarkInterpolant U S A}
    (B : MixedBranchCertificates J)
    (R : CoveredJ0Factor J.Q) (h : ¬ R.1.natDegree ≤ 53)
    (z : Field) (hzS : z ∈ S)
    (hzroot : BCHKSSubstitutionVanish.triEval R.1 z (J.P z) = 0)
    (hzbad : z ∉ B.highBad R h) :
    biEval (B.highData R h).inner
      (((B.high R h).quotientRoot z).eval (B.high R h).center) z = 0 := by
  exact (B.highData R h).owner_root z
    (B.high_owns R h z hzS hzroot hzbad)

/-- Assemble `CurrentMixedFamily` once the explicitly listed factor-local
certificates have been proved.  All J0 polynomial and root-agreement fields
are filled by `J`. -/
noncomputable def J0BenchmarkInterpolant.currentMixedFamily
    {U : Fin 2 → Index → Field}
    {S : Finset Field} {A : Field → Finset Index}
    (J : J0BenchmarkInterpolant U S A)
    (hlarge : bchksResidualNumerator6400 < S.card)
    (B : MixedBranchCertificates J) : CurrentMixedFamily := {
  S := S
  P := J.P
  Q := J.Q
  Q_ne := J.Q_ne
  seed_large := hlarge
  vanishing := J.vanishing
  support_caps := J.support_caps
  high := B.high
  low := B.low
  highData := B.highData
  lowData := B.lowData
  highBad := B.highBad
  lowBad := B.lowBad
  low_source := B.low_source
  high_source := B.high_source
  low_root := B.low_root
  high_root := B.high_root
  low_owns := B.low_owns
  high_owns := B.high_owns
}

/-! ## Canonical exact selector ledger

The next constructor removes the bookkeeping fields of `SelectorLedger`.
Both aggregate caps are defined to be the actual finite sums, and the fused
cap is the quotient plus one.  Thus only the final numerical fit of these
actual sums remains to be established by the branch-specific arithmetic.
-/

noncomputable def actualOuterBadTotal (M : CurrentMixedFamily) : Nat :=
  ∑ R : CoveredJ0Factor M.Q, (M.bad R).card

noncomputable def actualTagCharge (M : CurrentMixedFamily) : Nat :=
  ∑ R : CoveredJ0Factor M.Q,
    2 * FiniteHenselWeight.denominatorExponent (M.tag R).rootDegreeCap *
      (M.tag R).source.natDegree * (M.data R).supportCap

/-- One-above-floor fused cap.  The possible one-unit slack is global, not
per factor. -/
noncomputable def actualFusedCap (M : CurrentMixedFamily) : Nat :=
  (131073 * actualTagCharge M) / 54293 + 1

theorem actualTagCharge_fused
    (M : CurrentMixedFamily) :
    131073 * actualTagCharge M ≤ 54293 * actualFusedCap M := by
  let a := 131073 * actualTagCharge M
  have hmod : a % 54293 < 54293 := Nat.mod_lt _ (by norm_num)
  calc
    131073 * actualTagCharge M = a := rfl
    _ = 54293 * (a / 54293) + a % 54293 :=
      (Nat.div_add_mod a 54293).symm
    _ ≤ 54293 * (a / 54293) + 54293 :=
      Nat.add_le_add_left hmod.le _
    _ = 54293 * actualFusedCap M := by
      simp [actualFusedCap, a, Nat.mul_add]

/-- Canonical benchmark constants and exact finite sums instantiate the
whole selector ledger.  The displayed `htotal` is now the single honest
arithmetic obligation, rather than four independently chosen caps. -/
noncomputable def selectorLedgerOfActualTotals
    (M : CurrentMixedFamily)
    (htotal :
      BCHKSHybridHighDegreeAudit6400.bchksHybridQBadCover6400 +
        actualOuterBadTotal M +
      (actualFusedCap M +
        (bchksErrors6400 + 1) *
          BCHKSHybridHighDegreeAudit6400.bchksHybridYMass6400) ≤
          bchksResidualNumerator6400) :
    SelectorLedger M := {
  coordinateCount := 262144
  commonTarget := 131071
  rowLower := 185364
  outerBadCap := actualOuterBadTotal M
  resultCap := actualTagCharge M
  fusedCap := actualFusedCap M
  outerBad_sum := le_rfl
  tagCharge := le_rfl
  fused := by
    norm_num
    exact actualTagCharge_fused M
  total_le_residual := htotal
}

/-- On the full IRS coordinate domain, the attached-row cardinality is
exactly the cardinality of the original agreement set. -/
theorem fullDomain_attachedRow_card
    (A : Field → Finset Index) (z : Field) :
    ((Finset.univ : Finset Index).attach.filter
      fun i : (Finset.univ : Finset Index) ↦ (i : Index) ∈ A z).card =
        (A z).card := by
  rw [Finset.filter_attach']
  rw [Finset.card_map, Finset.card_attach]
  congr
  ext i
  simp

/-! ## Selected-pair dynamic coordinate input

Unlike `AlignmentInput`, the fresh quotient endpoint does not ask one
coordinate set to avoid every factor-local locator simultaneously.  Its raw
evaluation package is independent of the selected factor, and can therefore
be constructed directly from the J0 interpolation output.
-/

/-- Positivity of the support cap is already contained in
`ExplicitInnerData`: its positive-`Y`-degree inner factor has total degree at
least one, and that total degree is bounded by the stored cap. -/
theorem explicitInnerData_supportCap_pos
    {F : Type} [_root_.Field F]
    {tag : BCHKSTransformedUniversalTag6400.TransformedUniversalTag F}
    (D : ExplicitInnerData tag) :
    0 < D.supportCap := by
  have hinner0 : D.inner ≠ 0 :=
    Polynomial.ne_zero_of_natDegree_gt D.inner_degree_pos
  have hcoeff : D.inner.coeff D.inner.natDegree ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hinner0
  have hmem : D.inner.natDegree ∈ D.inner.support :=
    Polynomial.mem_support_iff.mpr hcoeff
  have hdegree :
      (D.inner.coeff D.inner.natDegree).natDegree +
          D.inner.natDegree ≤
        Polynomial.Bivariate.totalDegree D.inner :=
    Polynomial.Bivariate.coeff_totalDegree_le D.inner hmem
  have hpos := D.inner_degree_pos
  have hcap := D.inner_totalDegree_le
  omega

/-- The actual received words, row sets, row lower bound, support positivity,
and root-agreement identities required by the dynamic/fresh endpoint.  No
tag-local locator hypothesis remains here. -/
noncomputable def J0BenchmarkInterpolant.dynamicEvaluationInput
    {U : Fin 2 → Index → Field}
    {S : Finset Field} {A : Field → Finset Index}
    (J : J0BenchmarkInterpolant U S A)
    (hA : ∀ z ∈ S, 185364 ≤ (A z).card)
    (hlarge : bchksResidualNumerator6400 < S.card)
    (B : MixedBranchCertificates J) :
    DynamicEvaluationInput (J.currentMixedFamily hlarge B) := {
  agreementRows := A
  received := U
  agreement_card := hA
  support_caps := by
    intro R
    exact explicitInnerData_supportCap_pos
      ((J.currentMixedFamily hlarge B).data R)
  original_agrees := by
    intro z hz i hi
    exact J.agrees z hz i hi
}

/-- If the first selector returns an ordinary (`d ≤ 53`) tag, its selected
core profile is completely canonical: delete no coordinates.  Thus all
remaining selected-profile work is confined to the transformed branch. -/
noncomputable def selectedCoreProfileOfLow
    (M : CurrentMixedFamily)
    (L : DynamicSelectorLedger M)
    (hresidual : ResidualCover210 M)
    (W : BCHKSExplicitPairAlignment6400.SelectedExplicitPairFiber
      (dynamicSelectorData M L hresidual))
    (hlow : W.pair.1.1.natDegree ≤ 53) :
    SelectedCoreProfile M L hresidual W := {
  existingCore := ∅
  codim := 0
  core_card := by simp
  rootCap_add_codim := by
    rw [M.tag_eq_low W.pair.1 hlow]
    rfl
  codim_le := by norm_num
  locator_nonzero := by
    intro i hi
    rw [M.lift_locator_eq_low W.pair.1 hlow]
    simp
}

/-- Assemble the selected-pair profile function once profiles have been
proved only for genuinely transformed tags.  The ordinary branch is filled
by `selectedCoreProfileOfLow`. -/
noncomputable def selectedCoreProfilesOfHigh
    (M : CurrentMixedFamily)
    (L : DynamicSelectorLedger M)
    (hresidual : ResidualCover210 M)
    (highProfile : ∀ W :
      BCHKSExplicitPairAlignment6400.SelectedExplicitPairFiber
        (dynamicSelectorData M L hresidual),
      ¬ W.pair.1.1.natDegree ≤ 53 →
        SelectedCoreProfile M L hresidual W) :
    ∀ W : BCHKSExplicitPairAlignment6400.SelectedExplicitPairFiber
      (dynamicSelectorData M L hresidual),
      SelectedCoreProfile M L hresidual W := by
  intro W
  by_cases hlow : W.pair.1.1.natDegree ≤ 53
  · exact selectedCoreProfileOfLow M L hresidual W hlow
  · exact highProfile W hlow

/-- Benchmark-row instantiation of the complete dynamic/fresh endpoint.
The received words and all row/support facts are now theorem-produced.  The
remaining profile argument is needed only if the selected tag is
transformed. -/
theorem J0BenchmarkInterpolant.exists_completeFreshOutcome_of_degree_le209
    {U : Fin 2 → Index → Field}
    {S : Finset Field} {A : Field → Finset Index}
    (J : J0BenchmarkInterpolant U S A)
    (hA : ∀ z ∈ S, 185364 ≤ (A z).card)
    (hlarge : bchksResidualNumerator6400 < S.card)
    (B : MixedBranchCertificates J)
    (L : DynamicSelectorLedger (J.currentMixedFamily hlarge B))
    (hresidual : ResidualCover210 (J.currentMixedFamily hlarge B))
    (highProfile : ∀ W :
      BCHKSExplicitPairAlignment6400.SelectedExplicitPairFiber
        (dynamicSelectorData (J.currentMixedFamily hlarge B) L hresidual),
      ¬ W.pair.1.1.natDegree ≤ 53 →
        SelectedCoreProfile (J.currentMixedFamily hlarge B) L hresidual W) :
    ∃ W : BCHKSExplicitPairAlignment6400.SelectedExplicitPairFiber
        (dynamicSelectorData (J.currentMixedFamily hlarge B) L hresidual),
      Nonempty (CompleteFreshOutcome
        (J.currentMixedFamily hlarge B) L hresidual W) := by
  exact BCHKSJ0DynamicFreshEndpoint6400.exists_completeFreshOutcome_of_degree_le209
    (J.currentMixedFamily hlarge B) L hresidual
      (J.dynamicEvaluationInput hA hlarge B)
      (selectedCoreProfilesOfHigh
        (J.currentMixedFamily hlarge B) L hresidual highProfile)

/-- Concrete full-domain constructor for the benchmark row portion of
`AlignmentInput`.

The only remaining arguments are tag-local: positivity of the retained
inner cap, the high quotient root caps, and nonvanishing of every high
locator on the chosen coordinate domain.  The last condition is intentionally
visible: a nontrivial core locator cannot satisfy it on the full IRS domain,
so high tags with factor-dependent cores must instead use the
selected-pair-specific coordinate interface in
`BCHKSFreshQuotientFirstStage6400`. -/
noncomputable def J0BenchmarkInterpolant.fullDomainAlignmentInput
    {U : Fin 2 → Index → Field}
    {S : Finset Field} {A : Field → Finset Index}
    (J : J0BenchmarkInterpolant U S A)
    (hA : ∀ z ∈ S, 185364 ≤ (A z).card)
    (hlarge : bchksResidualNumerator6400 < S.card)
    (B : MixedBranchCertificates J)
    (L : SelectorLedger (J.currentMixedFamily hlarge B))
    (hcoordinateCount : L.coordinateCount = 262144)
    (hcommonTarget : L.commonTarget = 131071)
    (hrowLower : L.rowLower = 185364)
    (hhighRoot : ∀ R : CoveredJ0Factor J.Q,
      ∀ h : ¬ R.1.natDegree ≤ 53,
        0 < (B.high R h).rootDegreeCap ∧
        (B.high R h).rootDegreeCap ≤ L.commonTarget)
    (hsupport : ∀ R : CoveredJ0Factor J.Q,
      0 < ((J.currentMixedFamily hlarge B).data R).supportCap)
    (hhighLocator : ∀ R : CoveredJ0Factor J.Q,
      ∀ h : ¬ R.1.natDegree ≤ 53, ∀ i : Index,
        (B.high R h).locator.eval (IRSProfile.domain i) ≠ 0) :
    AlignmentInput (J.currentMixedFamily hlarge B) L := {
  coords := Finset.univ
  agreementRows := A
  received := U
  coordinate_card := by
    rw [hcoordinateCount]
    norm_num [Index]
  rowLower_le := by
    rw [hrowLower]
    norm_num [Index]
  commonTarget_lt := by
    rw [hcommonTarget, hrowLower]
    norm_num
  row_large := by
    intro z hz
    rw [hrowLower, fullDomain_attachedRow_card]
    exact hA z hz
  low_commonTarget := by
    rw [hcommonTarget]
  high_root_caps := hhighRoot
  support_caps := hsupport
  high_locator_nonzero := by
    intro R h i _hi
    exact hhighLocator R h i
  original_agrees := by
    intro z hz i hi
    exact J.agrees z hz i hi
}

end BCHKSJ0ConcreteGlobalInput6400
end ProximityPrize.SubmissionLower
