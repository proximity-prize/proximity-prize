import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveLaneCommonFactorSource6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveLaneFactorDescent6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSTwoFrobeniusRankTwoClosure6401
open BCHKSTwoFrobeniusSymbolicKernel6401
open BCHKSTwoFrobeniusThreeShiftPrimitive6401
open BCHKSThreeShiftSourceWindow6401
open BCHKSExtremeThreeRectangleProducer6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSExtremePrimitiveLaneResultantFork6401
open BCHKSExtremePrimitiveLaneCommonFactorSource6401
open scoped BigOperators
set_option maxHeartbeats 6000000
set_option maxRecDepth 1000000
def primitiveLaneFactorDescentExceptionCap6401 : Nat :=
  primitiveLaneOneChallengeCap6401
def primitiveLaneFactorDescentGoodFloor6401 : Nat :=
  extremeOwnerGoodChallengeFloor6401 -
    primitiveLaneFactorDescentExceptionCap6401
theorem primitiveLaneFactorDescentLedger_exact6401 :
    primitiveLaneFactorDescentExceptionCap6401 = 47957940448246 ∧
      primitiveLaneFactorDescentGoodFloor6401 = 273495283461914576 := by
  native_decide
noncomputable def primitiveLaneFactorQuotientRow6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (H : F[X][X])
    (hdiv : ∀ j, H ∣ W.sourcePuncture.frame.reduced j) :
    SymbolicRow F :=
  fun j => Classical.choose (hdiv j)
theorem primitiveLaneFactor_mul_quotientRow6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (H : F[X][X])
    (hdiv : ∀ j, H ∣ W.sourcePuncture.frame.reduced j)
    (j : Fin 3) :
    W.sourcePuncture.frame.reduced j =
      H * primitiveLaneFactorQuotientRow6401 W H hdiv j := by
  exact Classical.choose_spec (hdiv j)
theorem symbolicCoordinateRelation_factorRow6401
    {F : Type*} [Field F]
    (sigma : F →+* F) (x u0 u1 : F) (H : F[X][X])
    (Q : SymbolicRow F) :
    symbolicCoordinateRelation sigma x u0 u1 (fun j => H * Q j) =
      evalOuterAt x H * symbolicCoordinateRelation sigma x u0 u1 Q := by
  simp [symbolicCoordinateRelation, evalOuterAt]
  ring
theorem symbolicRelation_specializedFactorRow6401
    {F : Type*} [Field F]
    (sigma : F →+* F) (z : F) (P : Polynomial F)
    (H : F[X][X]) (Q : SymbolicRow F) :
    symbolicRelation sigma (specializeRow z (fun j => H * Q j)) P =
      specializeCoeffZ z H *
        symbolicRelation sigma (specializeRow z Q) P := by
  simp [symbolicRelation, specializeRow]
  ring
noncomputable def primitiveLaneFactorDescentGoodChallenges6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (H : F[X][X]) : Finset F :=
  (rowTwoGoodChallenges6401 W.commonDirection S).filter fun z =>
    specializeCoeffZ z H ≠ 0
structure PrimitiveLaneFactorDescent6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P) where
  factor : F[X][X]
  factor_positiveLocatorDegree : 0 < factor.natDegree
  quotient : SymbolicRow F
  component_factor : ∀ j,
    W.sourcePuncture.frame.reduced j = factor * quotient j
  quotient_caps : ∀ j,
    (quotient j).natDegree ≤ primitiveThreeShiftXCap6401 j
  quotient_pivot_ne_zero : quotient W.sourcePuncture.pivot ≠ 0
  source_relation : ∀ i, i ∉ W.sourcePuncture.badCoordinates →
    symbolicCoordinateRelation sigma (alpha i) (u0 i) (u1 i) quotient = 0
  goodChallenges : Finset F
  goodChallenges_eq : goodChallenges =
    primitiveLaneFactorDescentGoodChallenges6401 W factor
  goodChallenges_card : primitiveLaneFactorDescentGoodFloor6401 ≤
    goodChallenges.card
  owner_relation : ∀ z ∈ goodChallenges,
    symbolicRelation sigma (specializeRow z quotient) (P z) = 0
  retained_agreements : ∀ z ∈ goodChallenges,
    primitiveSourceWindow6401 ≤
      ((A z) \ W.sourcePuncture.badCoordinates).card
  pivot_degree_strict :
    (quotient W.sourcePuncture.pivot).natDegree <
      (W.sourcePuncture.frame.reduced W.sourcePuncture.pivot).natDegree
theorem commonHomogeneousFactor_swap_natDegree_le6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (H : F[X][X]) (hHne : H ≠ 0)
    (hH1 : H ∣ W.sourcePuncture.frame.reduced 1)
    (hH2 : H ∣ W.sourcePuncture.frame.reduced 2) :
    (Polynomial.Bivariate.swap H).natDegree ≤
      primitiveLaneFactorDescentExceptionCap6401 := by
  rcases W.sourcePuncture.pivot_homogeneous with hpivot | hpivot
  · have hred : W.sourcePuncture.frame.reduced 1 ≠ 0 := by
      simpa [hpivot] using W.sourcePuncture.frame.pivot_ne_zero
    have hswapH : Polynomial.Bivariate.swap H ≠ 0 :=
      (map_ne_zero_iff Polynomial.Bivariate.swap
        Polynomial.Bivariate.swap.injective).2 hHne
    have hswapRed : Polynomial.Bivariate.swap
        (W.sourcePuncture.frame.reduced 1) ≠ 0 :=
      (map_ne_zero_iff Polynomial.Bivariate.swap
        Polynomial.Bivariate.swap.injective).2 hred
    have hdvd := map_dvd Polynomial.Bivariate.swap hH1
    apply (Polynomial.natDegree_le_of_dvd hdvd hswapRed).trans
    apply (reduced_swap_natDegree_le_thirdRow6401 W 1).trans
    rw [W.rows_eq_selected]
    simpa [primitiveLaneFactorDescentExceptionCap6401,
      primitiveLaneOneChallengeCap6401, selectedExtremeRow6401] using
      extremeCoefficientRowMap_one_inner_natDegree_le6401 2
        (selectedExtremeKernelCoefficient6401 2 sigma alpha u0 u1).1
  · have hred : W.sourcePuncture.frame.reduced 2 ≠ 0 := by
      simpa [hpivot] using W.sourcePuncture.frame.pivot_ne_zero
    have hswapH : Polynomial.Bivariate.swap H ≠ 0 :=
      (map_ne_zero_iff Polynomial.Bivariate.swap
        Polynomial.Bivariate.swap.injective).2 hHne
    have hswapRed : Polynomial.Bivariate.swap
        (W.sourcePuncture.frame.reduced 2) ≠ 0 :=
      (map_ne_zero_iff Polynomial.Bivariate.swap
        Polynomial.Bivariate.swap.injective).2 hred
    have hdvd := map_dvd Polynomial.Bivariate.swap hH2
    apply (Polynomial.natDegree_le_of_dvd hdvd hswapRed).trans
    apply (reduced_swap_natDegree_le_thirdRow6401 W 2).trans
    rw [W.rows_eq_selected]
    apply (extremeCoefficientRowMap_two_inner_natDegree_le6401 2
      (selectedExtremeKernelCoefficient6401 2 sigma alpha u0 u1).1).trans
    native_decide
theorem homogeneousPivotFactor_swap_natDegree_le6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (K : F[X][X]) (_hKne : K ≠ 0)
    (hKdiv : K ∣
      W.sourcePuncture.frame.reduced W.sourcePuncture.pivot) :
    (Polynomial.Bivariate.swap K).natDegree ≤
      primitiveLaneFactorDescentExceptionCap6401 := by
  rcases W.sourcePuncture.pivot_homogeneous with hpivot | hpivot
  · have hred : W.sourcePuncture.frame.reduced 1 ≠ 0 := by
      simpa [hpivot] using W.sourcePuncture.frame.pivot_ne_zero
    have hswapRed : Polynomial.Bivariate.swap
        (W.sourcePuncture.frame.reduced 1) ≠ 0 :=
      (map_ne_zero_iff Polynomial.Bivariate.swap
        Polynomial.Bivariate.swap.injective).2 hred
    have hdvd : Polynomial.Bivariate.swap K ∣
        Polynomial.Bivariate.swap (W.sourcePuncture.frame.reduced 1) := by
      exact _root_.map_dvd Polynomial.Bivariate.swap
        (by simpa [hpivot] using hKdiv)
    apply (Polynomial.natDegree_le_of_dvd hdvd hswapRed).trans
    apply (reduced_swap_natDegree_le_thirdRow6401 W 1).trans
    rw [W.rows_eq_selected]
    simpa [primitiveLaneFactorDescentExceptionCap6401,
      primitiveLaneOneChallengeCap6401, selectedExtremeRow6401] using
      extremeCoefficientRowMap_one_inner_natDegree_le6401 2
        (selectedExtremeKernelCoefficient6401 2 sigma alpha u0 u1).1
  · have hred : W.sourcePuncture.frame.reduced 2 ≠ 0 := by
      simpa [hpivot] using W.sourcePuncture.frame.pivot_ne_zero
    have hswapRed : Polynomial.Bivariate.swap
        (W.sourcePuncture.frame.reduced 2) ≠ 0 :=
      (map_ne_zero_iff Polynomial.Bivariate.swap
        Polynomial.Bivariate.swap.injective).2 hred
    have hdvd : Polynomial.Bivariate.swap K ∣
        Polynomial.Bivariate.swap (W.sourcePuncture.frame.reduced 2) := by
      exact _root_.map_dvd Polynomial.Bivariate.swap
        (by simpa [hpivot] using hKdiv)
    apply (Polynomial.natDegree_le_of_dvd hdvd hswapRed).trans
    apply (reduced_swap_natDegree_le_thirdRow6401 W 2).trans
    rw [W.rows_eq_selected]
    apply (extremeCoefficientRowMap_two_inner_natDegree_le6401 2
      (selectedExtremeKernelCoefficient6401 2 sigma alpha u0 u1).1).trans
    native_decide
noncomputable def cumulativeLaneDescentFactor6401
    {F ι : Type*} [Field F] [DecidableEq ι]
    (J : Finset ι) (H : ι → F[X][X]) : F[X][X] :=
  ∏ i ∈ J, H i
noncomputable def cumulativeLaneDescentBadChallenges6401
    {F ι : Type} [Field F] [DecidableEq F] [DecidableEq ι]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (J : Finset ι) (H : ι → F[X][X]) : Finset F :=
  (rowTwoGoodChallenges6401 W.commonDirection S).filter fun z =>
    ∃ i ∈ J, specializeCoeffZ z (H i) = 0
noncomputable def cumulativeLaneDescentGoodChallenges6401
    {F ι : Type} [Field F] [DecidableEq F] [DecidableEq ι]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (J : Finset ι) (H : ι → F[X][X]) : Finset F :=
  (rowTwoGoodChallenges6401 W.commonDirection S).filter fun z =>
    ∀ i ∈ J, specializeCoeffZ z (H i) ≠ 0
theorem cumulativeLaneDescent_specialize_product_eq_zero_iff6401
    {F ι : Type} [Field F] [DecidableEq F] [DecidableEq ι]
    (J : Finset ι) (H : ι → F[X][X]) (z : F) :
    specializeCoeffZ z (cumulativeLaneDescentFactor6401 J H) = 0 ↔
      ∃ i ∈ J, specializeCoeffZ z (H i) = 0 := by
  classical
  change ((∏ i ∈ J, H i).map (Polynomial.evalRingHom z) = 0) ↔
    ∃ i ∈ J, (H i).map (Polynomial.evalRingHom z) = 0
  rw [Polynomial.map_prod]
  exact (Finset.prod_eq_zero_iff :
    (∏ i ∈ J, (H i).map (Polynomial.evalRingHom z)) = 0 ↔
      ∃ i ∈ J, (H i).map (Polynomial.evalRingHom z) = 0)
theorem cumulativeLaneDescentBadChallenges_card_le6401
    {F ι : Type} [Field F] [DecidableEq F] [DecidableEq ι]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (J : Finset ι) (H : ι → F[X][X])
    (hproductNe : cumulativeLaneDescentFactor6401 J H ≠ 0)
    (hproductDiv : cumulativeLaneDescentFactor6401 J H ∣
      W.sourcePuncture.frame.reduced W.sourcePuncture.pivot) :
    (cumulativeLaneDescentBadChallenges6401 W J H).card ≤
      primitiveLaneFactorDescentExceptionCap6401 := by
  classical
  let K := cumulativeLaneDescentFactor6401 J H
  let G := rowTwoGoodChallenges6401 W.commonDirection S
  have hbadEq : cumulativeLaneDescentBadChallenges6401 W J H =
      G.filter fun z => specializeCoeffZ z K = 0 := by
    ext z
    simp only [cumulativeLaneDescentBadChallenges6401, G,
      Finset.mem_filter]
    exact and_congr_right (fun _ =>
      (cumulativeLaneDescent_specialize_product_eq_zero_iff6401 J H z).symm)
  rw [hbadEq]
  obtain ⟨a, ha, hcard⟩ :=
    card_zero_specializations_le_coefficient_degree G K hproductNe
  exact hcard.trans ((coeff_natDegree_le_swap_natDegree K a).trans
    (homogeneousPivotFactor_swap_natDegree_le6401
      W K hproductNe hproductDiv))
theorem cumulativeLaneDescentGoodChallenges_card_floor6401
    {F ι : Type} [Field F] [DecidableEq F] [DecidableEq ι]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (J : Finset ι) (H : ι → F[X][X])
    (hproductNe : cumulativeLaneDescentFactor6401 J H ≠ 0)
    (hproductDiv : cumulativeLaneDescentFactor6401 J H ∣
      W.sourcePuncture.frame.reduced W.sourcePuncture.pivot) :
    primitiveLaneFactorDescentGoodFloor6401 ≤
      (cumulativeLaneDescentGoodChallenges6401 W J H).card := by
  classical
  have hbad := cumulativeLaneDescentBadChallenges_card_le6401
    W J H hproductNe hproductDiv
  have hsplit :
      (cumulativeLaneDescentBadChallenges6401 W J H).card +
        (cumulativeLaneDescentGoodChallenges6401 W J H).card =
      (rowTwoGoodChallenges6401 W.commonDirection S).card := by
    rw [cumulativeLaneDescentBadChallenges6401,
      cumulativeLaneDescentGoodChallenges6401]
    have hpred : ∀ z : F,
        (∀ i ∈ J, specializeCoeffZ z (H i) ≠ 0) ↔
          ¬ (∃ i ∈ J, specializeCoeffZ z (H i) = 0) := by
      intro z
      simp only [not_exists, not_and, ne_eq]
    simpa only [hpred] using Finset.card_filter_add_card_filter_not
      (s := rowTwoGoodChallenges6401 W.commonDirection S)
      (fun z => ∃ i ∈ J, specializeCoeffZ z (H i) = 0)
  have hgood := W.goodChallenges_card
  rw [primitiveLaneFactorDescentLedger_exact6401.1] at hbad
  rw [extremeOwnerWindow_exact6401.2.1] at hgood
  rw [primitiveLaneFactorDescentLedger_exact6401.2]
  omega
theorem cumulativeLaneDescent_length_le_22507_6401
    {F ι : Type} [Field F] [DecidableEq F] [DecidableEq ι]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (J : Finset ι) (H : ι → F[X][X])
    (hpositive : ∀ i ∈ J, 0 < (H i).natDegree)
    (hproductDiv : cumulativeLaneDescentFactor6401 J H ∣
      W.sourcePuncture.frame.reduced W.sourcePuncture.pivot) :
    J.card ≤ 22507 := by
  classical
  have hne : ∀ i ∈ J, H i ≠ 0 := by
    intro i hi hzero
    simpa [hzero] using hpositive i hi
  have hproductNe : cumulativeLaneDescentFactor6401 J H ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr hne
  have hdegreeProduct :
      (cumulativeLaneDescentFactor6401 J H).natDegree =
        ∑ i ∈ J, (H i).natDegree := by
    exact Polynomial.natDegree_prod J H hne
  have hcardSum : J.card ≤ ∑ i ∈ J, (H i).natDegree := by
    calc
      J.card = ∑ i ∈ J, 1 := by simp
      _ ≤ ∑ i ∈ J, (H i).natDegree := by
        exact Finset.sum_le_sum fun i hi => hpositive i hi
  have hpivotNe := W.sourcePuncture.frame.pivot_ne_zero
  have hprodDegree : (cumulativeLaneDescentFactor6401 J H).natDegree ≤
      (W.sourcePuncture.frame.reduced W.sourcePuncture.pivot).natDegree :=
    Polynomial.natDegree_le_of_dvd hproductDiv hpivotNe
  have hpivotCap :
      (W.sourcePuncture.frame.reduced W.sourcePuncture.pivot).natDegree ≤
        22507 := by
    apply (W.sourcePuncture.reduced_caps W.sourcePuncture.pivot).trans
    rcases W.sourcePuncture.pivot_homogeneous with hpivot | hpivot
    · simp [hpivot, primitiveThreeShiftXCap6401]
    · simp [hpivot, primitiveThreeShiftXCap6401]
  exact hcardSum.trans (hdegreeProduct.symm.le.trans
    (hprodDegree.trans hpivotCap))
theorem exists_primitiveLaneFactorDescent6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (H : F[X][X]) (hpositive : 0 < H.natDegree)
    (hdiv : ∀ j, H ∣ W.sourcePuncture.frame.reduced j) :
    Nonempty (PrimitiveLaneFactorDescent6401 W) := by
  classical
  let Q := primitiveLaneFactorQuotientRow6401 W H hdiv
  have hHne : H ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hpositive
    omega
  have hfactor : ∀ j, W.sourcePuncture.frame.reduced j = H * Q j :=
    primitiveLaneFactor_mul_quotientRow6401 W H hdiv
  have hQcaps : ∀ j, (Q j).natDegree ≤ primitiveThreeShiftXCap6401 j := by
    intro j
    by_cases hQ : Q j = 0
    · simp [hQ]
    · have hred : W.sourcePuncture.frame.reduced j ≠ 0 := by
        rw [hfactor j]
        exact mul_ne_zero hHne hQ
      exact (Polynomial.natDegree_le_of_dvd ⟨H, by
        rw [hfactor j, mul_comm]⟩ hred).trans
          (W.sourcePuncture.reduced_caps j)
  have hQpivot : Q W.sourcePuncture.pivot ≠ 0 := by
    intro hzero
    apply W.sourcePuncture.frame.pivot_ne_zero
    rw [hfactor W.sourcePuncture.pivot, hzero, mul_zero]
  have hsource : ∀ i, i ∉ W.sourcePuncture.badCoordinates →
      symbolicCoordinateRelation sigma (alpha i) (u0 i) (u1 i) Q = 0 := by
    intro i hi
    have hH0 : H ∣ primitiveBivariateFailureLaneZero6401 W := by
      simpa [primitiveBivariateFailureLaneZero6401] using hdiv 2
    have hH1 : H ∣ primitiveBivariateFailureLaneOne6401 W := by
      change H ∣ -W.sourcePuncture.frame.reduced 1
      exact dvd_neg.mpr (hdiv 1)
    have hHeval := integralCommonFactor_nonzeroAt_unpuncturedCoordinate6401
      W H hH0 hH1 i hi
    have hrelation := W.sourcePuncture.source_relation i hi
    have hrow : W.sourcePuncture.frame.reduced = fun j => H * Q j := by
      funext j
      exact hfactor j
    rw [hrow, symbolicCoordinateRelation_factorRow6401] at hrelation
    exact (mul_eq_zero.mp hrelation).resolve_left hHeval
  have hswap := commonHomogeneousFactor_swap_natDegree_le6401
    W H hHne (hdiv 1) (hdiv 2)
  let G := rowTwoGoodChallenges6401 W.commonDirection S
  let G' := primitiveLaneFactorDescentGoodChallenges6401 W H
  have hzeroCard : (G.filter fun z => specializeCoeffZ z H = 0).card ≤
      primitiveLaneFactorDescentExceptionCap6401 := by
    obtain ⟨a, ha, hcard⟩ :=
      card_zero_specializations_le_coefficient_degree G H hHne
    exact hcard.trans
      ((coeff_natDegree_le_swap_natDegree H a).trans hswap)
  have hsplit : (G.filter fun z => specializeCoeffZ z H = 0).card +
      G'.card = G.card := by
    dsimp only [G, G', primitiveLaneFactorDescentGoodChallenges6401]
    simpa only [ne_eq] using Finset.card_filter_add_card_filter_not
      (s := rowTwoGoodChallenges6401 W.commonDirection S)
      (fun z => specializeCoeffZ z H = 0)
  have hGcard : primitiveLaneFactorDescentGoodFloor6401 ≤ G'.card := by
    have hgood := W.goodChallenges_card
    dsimp only [G] at hzeroCard hsplit
    rw [primitiveLaneFactorDescentLedger_exact6401.1] at hzeroCard
    rw [extremeOwnerWindow_exact6401.2.1] at hgood
    rw [primitiveLaneFactorDescentLedger_exact6401.2]
    omega
  have howner : ∀ z ∈ G',
      symbolicRelation sigma (specializeRow z Q) (P z) = 0 := by
    intro z hz
    have hzmem := Finset.mem_filter.mp hz
    have horiginal := W.owner_relation z hzmem.1
    have hrow : W.sourcePuncture.frame.reduced = fun j => H * Q j := by
      funext j
      exact hfactor j
    rw [hrow, symbolicRelation_specializedFactorRow6401] at horiginal
    exact (mul_eq_zero.mp horiginal).resolve_left hzmem.2
  have hretained : ∀ z ∈ G', primitiveSourceWindow6401 ≤
      ((A z) \ W.sourcePuncture.badCoordinates).card := by
    intro z hz
    exact W.retained_agreements z (Finset.mem_filter.mp hz).1
  have hpivotStrict : (Q W.sourcePuncture.pivot).natDegree <
      (W.sourcePuncture.frame.reduced W.sourcePuncture.pivot).natDegree := by
    rw [hfactor W.sourcePuncture.pivot,
      Polynomial.natDegree_mul hHne hQpivot]
    omega
  exact ⟨{
    factor := H
    factor_positiveLocatorDegree := hpositive
    quotient := Q
    component_factor := hfactor
    quotient_caps := hQcaps
    quotient_pivot_ne_zero := hQpivot
    source_relation := hsource
    goodChallenges := G'
    goodChallenges_eq := rfl
    goodChallenges_card := hGcard
    owner_relation := howner
    retained_agreements := hretained
    pivot_degree_strict := hpivotStrict }⟩
theorem PrimitiveLaneCommonFactorSource6401.descend_of_dvd_inhomogeneous6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    {W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P}
    (C : PrimitiveLaneCommonFactorSource6401 W)
    (hinhomogeneous : C.factor ∣ W.sourcePuncture.frame.reduced 0) :
    Nonempty (PrimitiveLaneFactorDescent6401 W) := by
  apply exists_primitiveLaneFactorDescent6401 W C.factor
    C.positiveLocatorDegree
  intro j
  fin_cases j
  · exact hinhomogeneous
  · simpa [primitiveBivariateFailureLaneOne6401] using
      (dvd_neg.mpr C.dividesLaneOne)
  · simpa [primitiveBivariateFailureLaneZero6401] using C.dividesLaneZero
end BCHKSExtremePrimitiveLaneFactorDescent6401
end ProximityPrize.SubmissionLower
