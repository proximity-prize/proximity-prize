import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveAllSeedsResultantMultiplicity6401
import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveOwnerMassAmplification6401
import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveRecursiveFactorClosure6401
import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveSupportEnvelope6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveRecursiveOwnerMassResultantZero6401
open Polynomial
open Polynomial.Bivariate
open scoped BigOperators
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSTwoFrobeniusRankTwoClosure6401
open BCHKSTwoFrobeniusThreeShiftPrimitive6401
open BCHKSTwoFrobeniusExtremeKernelCounter6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
open BCHKSFrobeniusHilbert90Normalization6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSFrobeniusGraphHilbert90Audit6401
open BCHKSFrobeniusGraphInjectivity6401
open BCHKSFrobeniusResultantMultiplicity6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremeThreeRectangleProducer6401
open BCHKSExtremePrimitiveNormDivisorFork6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveGraphGaugeFork6401
open BCHKSExtremePrimitiveLaneResultantFork6401
open BCHKSExtremePrimitiveLaneFactorDescent6401
open BCHKSExtremePrimitiveAllSeedsResultantMultiplicity6401
open BCHKSExtremePrimitiveOwnerMassAmplification6401
open BCHKSExtremePrimitiveSupportEnvelope6401
open BCHKSExtremePrimitiveRecursiveFactorClosure6401
set_option maxHeartbeats 6000000
set_option maxRecDepth 1000000
section RecursiveMass
variable {F : Type} [Field F] [DecidableEq F]
variable {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
variable {u0 u1 : Fin n6401 → F}
variable {S : Finset F} {Aset : F → Finset (Fin n6401)}
variable {P : F → Polynomial F}
variable (W : PrimitivePuncturedOwnerWindow6401
  sigma alpha u0 u1 S Aset P)
noncomputable def recursiveFamilyGraphGaugeNumerator6401
    (C : RecursivePrimitiveLaneState6401 W) (t : F) : F[X][X] :=
  graphHilbert90Numerator6401 sigma q6401
    C.laneZero6401 C.laneOne6401 t
noncomputable def recursiveMassCore6401
    (C : RecursivePrimitiveLaneState6401 W) : Finset F :=
  (rowTwoGoodChallenges6401 W.commonDirection S).filter fun z ↦
    specializeCoeffZ z
      (W.sourcePuncture.frame.reduced W.sourcePuncture.pivot) ≠ 0
theorem recursiveMassCore_card_floor6401
    (C : RecursivePrimitiveLaneState6401 W) :
    primitiveLaneFactorDescentGoodFloor6401 ≤
      (recursiveMassCore6401 W C).card := by
  classical
  let G := rowTwoGoodChallenges6401 W.commonDirection S
  let H := W.sourcePuncture.frame.reduced W.sourcePuncture.pivot
  let bad := G.filter fun z ↦ specializeCoeffZ z H = 0
  have hHne : H ≠ 0 := by
    simpa [H] using W.sourcePuncture.frame.pivot_ne_zero
  have hswap : (Polynomial.Bivariate.swap H).natDegree ≤
      primitiveLaneFactorDescentExceptionCap6401 := by
    exact homogeneousPivotFactor_swap_natDegree_le6401 W H hHne (dvd_refl H)
  have hbad : bad.card ≤ primitiveLaneFactorDescentExceptionCap6401 := by
    obtain ⟨a, _ha, hcard⟩ :=
      card_zero_specializations_le_coefficient_degree G H hHne
    exact hcard.trans
      ((coeff_natDegree_le_swap_natDegree H a).trans hswap)
  have hsplit : bad.card + (recursiveMassCore6401 W C).card = G.card := by
    dsimp only [bad, G, H,
      recursiveMassCore6401]
    simpa only [ne_eq] using Finset.card_filter_add_card_filter_not
      (s := rowTwoGoodChallenges6401 W.commonDirection S)
      (fun z ↦ specializeCoeffZ z
        (W.sourcePuncture.frame.reduced W.sourcePuncture.pivot) = 0)
  have hgood : extremeOwnerGoodChallengeFloor6401 ≤ G.card := by
    simpa only [G] using W.goodChallenges_card
  rw [primitiveLaneFactorDescentLedger_exact6401.1] at hbad
  rw [extremeOwnerWindow_exact6401.2.1] at hgood
  rw [primitiveLaneFactorDescentLedger_exact6401.2]
  omega
theorem mem_recursiveGoodChallenges_of_mem_massCore6401
    (C : RecursivePrimitiveLaneState6401 W) {z : F}
    (hz : z ∈ recursiveMassCore6401 W C) :
    z ∈ C.goodChallenges6401 := by
  have hzparts := Finset.mem_filter.mp hz
  apply Finset.mem_filter.mpr
  refine ⟨hzparts.1, ?_⟩
  intro hfactor
  apply hzparts.2
  rw [C.component_factor W.sourcePuncture.pivot]
  rw [map_mul]
  exact mul_eq_zero.mpr (Or.inl (by
    simpa [specializeCoeffZ_apply] using hfactor))
theorem recursiveSpecializedLanes_not_both_zero_of_mem_massCore6401
    (C : RecursivePrimitiveLaneState6401 W) {z : F}
    (hz : z ∈ recursiveMassCore6401 W C) :
    specializeCoeffZ z C.laneZero6401 ≠ 0 ∨
      specializeCoeffZ z C.laneOne6401 ≠ 0 := by
  have hzparts := Finset.mem_filter.mp hz
  have hquotientPivot :
      specializeCoeffZ z (C.quotient W.sourcePuncture.pivot) ≠ 0 := by
    intro hquotient
    apply hzparts.2
    rw [C.component_factor W.sourcePuncture.pivot]
    rw [map_mul]
    exact mul_eq_zero.mpr (Or.inr (by
      simpa [specializeCoeffZ_apply] using hquotient))
  rcases W.sourcePuncture.pivot_homogeneous with hpivot | hpivot
  · right
    simpa [RecursivePrimitiveLaneState6401.laneOne6401, hpivot,
      specializeCoeffZ_apply] using hquotientPivot
  · left
    simpa [RecursivePrimitiveLaneState6401.laneZero6401, hpivot,
      specializeCoeffZ_apply] using hquotientPivot
theorem recursivePuncturedTwoLaneFailureRelation6401
    (C : RecursivePrimitiveLaneState6401 W)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (z : F) (hz : z ∈ C.goodChallenges6401) :
    TwoLaneFailureRelation sigma W.puncturedAlpha
      (W.puncturedOwnerError z)
      (specializeCoeffZ z C.laneZero6401)
      (specializeCoeffZ z C.laneOne6401) := by
  intro i
  have hi : i.1 ∉ W.sourcePuncture.badCoordinates :=
    (Finset.mem_sdiff.mp i.2).2
  have hrel := twoLaneErrorRelation_of_owner_and_source6401
    sigma (alpha i.1) z (u0 i.1) (u1 i.1) (P z) C.quotient
      (hsigma z) (hfixed i.1) (C.owner_relation6401 z hz)
      (C.source_relation6401 i.1 hi)
  simp only [specializeRow, specializeCoeffZ_apply] at hrel
  change Polynomial.eval (alpha i.1)
        (specializeCoeffZ z C.laneZero6401) *
        sigma (W.puncturedOwnerError z i) =
      Polynomial.eval (alpha i.1)
        (specializeCoeffZ z C.laneOne6401) *
        W.puncturedOwnerError z i
  dsimp [PrimitivePuncturedOwnerWindow6401.puncturedOwnerError]
  simp only [RecursivePrimitiveLaneState6401.laneZero6401,
    RecursivePrimitiveLaneState6401.laneOne6401,
    specializeCoeffZ_apply, Polynomial.map_neg, Polynomial.eval_neg]
  linear_combination hrel
theorem recursiveFailureLanes_eval_eq_zero_of_allGraphSeedsZero6401
    (C : RecursivePrimitiveLaneState6401 W)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hsix : (6 : F) ≠ 0)
    (hall : ∀ t : F, recursiveFamilyGraphGaugeNumerator6401 W C t = 0)
    (z : F) (hz : z ∈ C.goodChallenges6401)
    (i : W.PuncturedIndex) (hi : i ∈ puncturedErrorSupport6401 W z) :
    Polynomial.eval (W.puncturedAlpha i)
          (specializeCoeffZ z C.laneZero6401) = 0 ∧
      Polynomial.eval (W.puncturedAlpha i)
          (specializeCoeffZ z C.laneOne6401) = 0 := by
  let E := W.puncturedOwnerError z i
  let A0 := specializeCoeffZ z C.laneZero6401
  let B0 := specializeCoeffZ z C.laneOne6401
  let x := W.puncturedAlpha i
  have hE : E ≠ 0 := (Finset.mem_filter.mp hi).2
  have hx : sigma x = x := hfixed i.1
  have hrel : Polynomial.eval x A0 * sigma E =
      Polynomial.eval x B0 * E := by
    simpa only [A0, B0, E, x] using
      (recursivePuncturedTwoLaneFailureRelation6401
        W C hsigma hfixed z hz i)
  have hordinaryZero : hilbert90Numerator6401 sigma A0 B0 E = 0 := by
    have hgraphZero := congrArg (specializeCoeffZ z) (hall E)
    rw [map_zero] at hgraphZero
    have hspecialize := graphHilbert90Numerator_specialize6401 sigma q6401
      C.laneZero6401 C.laneOne6401 E z (hsigma z)
    have hmappedZero :
        (graphHilbert90Numerator6401 sigma q6401
          C.laneZero6401 C.laneOne6401 E).map
            (Polynomial.evalRingHom z) = 0 := by
      simpa [recursiveFamilyGraphGaugeNumerator6401,
        specializeCoeffZ_apply] using hgraphZero
    rw [hspecialize] at hmappedZero
    simpa [A0, B0, specializeCoeffZ_apply] using hmappedZero
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
theorem puncturedErrorSupport_card_le_recursiveLaneGcdDegree6401
    (C : RecursivePrimitiveLaneState6401 W)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hsix : (6 : F) ≠ 0)
    (hall : ∀ t : F, recursiveFamilyGraphGaugeNumerator6401 W C t = 0)
    (z : F) (hz : z ∈ C.goodChallenges6401)
    (hlane : specializeCoeffZ z C.laneZero6401 ≠ 0 ∨
      specializeCoeffZ z C.laneOne6401 ≠ 0) :
    (puncturedErrorSupport6401 W z).card ≤
      (EuclideanDomain.gcd
        (specializeCoeffZ z C.laneZero6401)
        (specializeCoeffZ z C.laneOne6401)).natDegree := by
  classical
  let D := EuclideanDomain.gcd
    (specializeCoeffZ z C.laneZero6401)
    (specializeCoeffZ z C.laneOne6401)
  let roots : Finset F :=
    (puncturedErrorSupport6401 W z).map W.puncturedAlpha
  have hDne : D ≠ 0 := by
    intro hzero
    have hboth := EuclideanDomain.gcd_eq_zero_iff.mp hzero
    exact hlane.elim (fun h ↦ h hboth.1) (fun h ↦ h hboth.2)
  have hroot : ∀ x ∈ roots, Polynomial.eval x D = 0 := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
    have hboth := recursiveFailureLanes_eval_eq_zero_of_allGraphSeedsZero6401
      W C hsigma hfixed hsix hall z hz i hi
    exact Polynomial.eval_gcd_eq_zero hboth.1 hboth.2
  have hcard : roots.card ≤ D.natDegree := by
    by_contra hnot
    have hdegree : D.natDegree < roots.card := by omega
    exact hDne (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      D roots hroot hdegree)
  simpa [roots, D] using hcard
theorem errorSupportPower_dvd_recursiveLaneResultant_of_allGraphSeedsZero6401
    (C : RecursivePrimitiveLaneState6401 W)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hsix : (6 : F) ≠ 0)
    (hall : ∀ t : F, recursiveFamilyGraphGaugeNumerator6401 W C t = 0)
    (z : F) (hz : z ∈ recursiveMassCore6401 W C) :
    (Polynomial.X - Polynomial.C z) ^
        (puncturedErrorSupport6401 W z).card ∣ C.laneResultant6401 := by
  classical
  let L0 := C.laneZero6401
  let L1 := C.laneOne6401
  let f := specializeCoeffZ z L0
  let g := specializeCoeffZ z L1
  let d := EuclideanDomain.gcd f g
  have hzgood := mem_recursiveGoodChallenges_of_mem_massCore6401 W C hz
  have hlaneRaw :=
    recursiveSpecializedLanes_not_both_zero_of_mem_massCore6401 W C hz
  have hlane : f ≠ 0 ∨ g ≠ 0 := by simpa [f, g, L0, L1] using hlaneRaw
  have hd : d ≠ 0 := by
    intro hzero
    have hboth := EuclideanDomain.gcd_eq_zero_iff.mp hzero
    exact hlane.elim (fun h ↦ h hboth.1) (fun h ↦ h hboth.2)
  obtain ⟨a, haFactor⟩ := EuclideanDomain.gcd_dvd_left f g
  obtain ⟨b, hbFactor⟩ := EuclideanDomain.gcd_dvd_right f g
  have hsupport : (puncturedErrorSupport6401 W z).card ≤ d.natDegree := by
    simpa [d, f, g, L0, L1] using
      puncturedErrorSupport_card_le_recursiveLaneGcdDegree6401
        W C hsigma hfixed hsix hall z hzgood hlaneRaw
  have hsmall : (Polynomial.X - Polynomial.C z) ^
      (puncturedErrorSupport6401 W z).card ∣
        (Polynomial.X - Polynomial.C z) ^ d.natDegree :=
    pow_dvd_pow _ hsupport
  rcases hlane with hfne | hgne
  · have hane : a ≠ 0 := by
      intro hzero
      apply hfne
      rw [haFactor, hzero, mul_zero]
    have hraw :=
      X_sub_C_pow_commonFactorDegree_dvd_resultant_fullyPadded6401
        L0 L1 L0.natDegree L1.natDegree z d a b hd hane
        (by simpa [d, f, g, specializeCoeffZ_apply] using haFactor)
        (by simpa [d, f, g, specializeCoeffZ_apply] using hbFactor)
        Polynomial.natDegree_map_le Polynomial.natDegree_map_le
    exact hsmall.trans (by
      simpa [RecursivePrimitiveLaneState6401.laneResultant6401,
        L0, L1, specializeCoeffZ_apply] using hraw)
  · have hbne : b ≠ 0 := by
      intro hzero
      apply hgne
      rw [hbFactor, hzero, mul_zero]
    have hraw :=
      X_sub_C_pow_commonFactorDegree_dvd_resultant_fullyPadded6401
        L1 L0 L1.natDegree L0.natDegree z d b a hd hbne
        (by simpa [d, f, g, specializeCoeffZ_apply] using hbFactor)
        (by simpa [d, f, g, specializeCoeffZ_apply] using haFactor)
        Polynomial.natDegree_map_le Polynomial.natDegree_map_le
    apply hsmall.trans
    rw [RecursivePrimitiveLaneState6401.laneResultant6401,
      Polynomial.resultant_comm]
    exact dvd_mul_of_dvd_right (by
      simpa [L0, L1, specializeCoeffZ_apply] using hraw) _
theorem recursiveLanes_coeffDegreeLE6401
    (C : RecursivePrimitiveLaneState6401 W) :
    BivariateCoeffDegreeLE C.laneZero6401
        primitiveLaneZeroChallengeCap6401 ∧
      BivariateCoeffDegreeLE C.laneOne6401
        primitiveLaneOneChallengeCap6401 := by
  constructor
  · intro n
    apply (coeff_natDegree_le_swap_natDegree (C.quotient 2) n).trans
    apply (C.quotient_swap_natDegree_le6401 2).trans
    apply (reduced_swap_natDegree_le_thirdRow6401 W 2).trans
    rw [W.rows_eq_selected]
    simpa [RecursivePrimitiveLaneState6401.laneZero6401,
      primitiveLaneZeroChallengeCap6401, selectedExtremeRow6401] using
      extremeCoefficientRowMap_two_inner_natDegree_le6401 2
        (selectedExtremeKernelCoefficient6401 2 sigma alpha u0 u1).1
  · intro n
    rw [RecursivePrimitiveLaneState6401.laneOne6401,
      Polynomial.coeff_neg, Polynomial.natDegree_neg]
    apply (coeff_natDegree_le_swap_natDegree (C.quotient 1) n).trans
    apply (C.quotient_swap_natDegree_le6401 1).trans
    apply (reduced_swap_natDegree_le_thirdRow6401 W 1).trans
    rw [W.rows_eq_selected]
    simpa [primitiveLaneOneChallengeCap6401, selectedExtremeRow6401] using
      extremeCoefficientRowMap_one_inner_natDegree_le6401 2
        (selectedExtremeKernelCoefficient6401 2 sigma alpha u0 u1).1
theorem recursiveLaneResultant_natDegree_le6401
    (C : RecursivePrimitiveLaneState6401 W) :
    C.laneResultant6401.natDegree ≤
      primitiveLaneResultantChallengeCap6401 := by
  let L0 := C.laneZero6401
  let L1 := C.laneOne6401
  have hL0X : L0.natDegree ≤ 22507 := by
    simpa [L0, RecursivePrimitiveLaneState6401.laneZero6401,
      primitiveThreeShiftXCap6401] using C.quotient_caps6401 2
  have hL1X : L1.natDegree ≤ 22507 := by
    simpa [L1, RecursivePrimitiveLaneState6401.laneOne6401,
      primitiveThreeShiftXCap6401] using C.quotient_caps6401 1
  rcases recursiveLanes_coeffDegreeLE6401 W C with ⟨hL0Z, hL1Z⟩
  have hdegreeZ0 : degreeX L0 ≤ primitiveLaneZeroChallengeCap6401 := by
    unfold degreeX
    apply Finset.sup_le
    intro n hn
    exact hL0Z n
  have hdegreeZ1 : degreeX L1 ≤ primitiveLaneOneChallengeCap6401 := by
    unfold degreeX
    apply Finset.sup_le
    intro n hn
    exact hL1Z n
  have hraw := bivariate_resultant_natDegree_le
    L0 L1 L0.natDegree L1.natDegree
  change C.laneResultant6401.natDegree ≤ _
  apply hraw.trans
  exact Nat.add_le_add
    (Nat.mul_le_mul hL1X hdegreeZ0)
    (Nat.mul_le_mul hL0X hdegreeZ1)
theorem recursiveLaneResultant_eq_zero_of_allGraphSeedsZero_of_noCurve6401
    (C : RecursivePrimitiveLaneState6401 W)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (hsix : (6 : F) ≠ 0)
    (hall : ∀ t : F, recursiveFamilyGraphGaugeNumerator6401 W C t = 0)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hfail : ¬ PolynomialAffineCurveWitness6401 S P) :
    C.laneResultant6401 = 0 := by
  classical
  let core := recursiveMassCore6401 W C
  have hUcard : primitiveLaneFactorDescentGoodFloor6401 ≤ core.card := by
    simpa [core] using recursiveMassCore_card_floor6401 W C
  by_contra hresultant
  have hlocal : ∀ z ∈ core,
      (Polynomial.X - Polynomial.C ((Function.Embedding.refl F) z)) ^
          (puncturedErrorSupport6401 W z).card ∣ C.laneResultant6401 := by
    intro z hz
    exact errorSupportPower_dvd_recursiveLaneResultant_of_allGraphSeedsZero6401
      W C hsigma hfixed hsix hall z (by simpa [core] using hz)
  have hmassRaw := sum_localPowers_le_natDegree6401
    C.laneResultant6401 hresultant
    (Function.Embedding.refl F) core
    (fun z ↦ (puncturedErrorSupport6401 W z).card) hlocal
  have hmass : ∑ z ∈ core, (puncturedErrorSupport6401 W z).card ≤
      primitiveLaneResultantChallengeCap6401 :=
    hmassRaw.trans (recursiveLaneResultant_natDegree_le6401 W C)
  have hlower : ∀ T ∈ core.powersetCard weakCurveOutput6401,
      108566 ≤ ∑ z ∈ T, (puncturedErrorSupport6401 W z).card := by
    intro T hT
    have hTparts := Finset.mem_powersetCard.mp hT
    have hTgood : T ⊆
        rowTwoGoodChallenges6401 W.commonDirection S := by
      intro z hz
      exact (Finset.mem_filter.mp (hTparts.1 hz)).1
    have hTcard : weakCurveOutput6401 ≤ T.card := by
      rw [hTparts.2]
    have hunion := noCurve_supportUnion_card_ge_108566_6401
      W T hTgood hTcard hPdegree hfail
    exact hunion.trans (by
      simpa [puncturedErrorSupportUnion6401] using
        (Finset.card_biUnion_le :
          (T.biUnion (puncturedErrorSupport6401 W)).card ≤
            ∑ z ∈ T, (puncturedErrorSupport6401 W z).card))
  exact no_largeOwnerFamily_of_subsetMass_and_resultantCap6401
    core (fun z ↦ (puncturedErrorSupport6401 W z).card)
      hUcard hlower hmass
end RecursiveMass
end BCHKSExtremePrimitiveRecursiveOwnerMassResultantZero6401
end ProximityPrize.SubmissionLower
