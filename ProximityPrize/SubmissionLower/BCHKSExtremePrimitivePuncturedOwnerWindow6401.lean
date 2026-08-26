import ProximityPrize.SubmissionLower.BCHKSExtremeThreeRectangleProducer6401
import ProximityPrize.SubmissionLower.BCHKSThreeShiftSourceWindow6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusKeyEquationFork6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitivePuncturedOwnerWindow6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSTwoFrobeniusRankTwoClosure6401
open BCHKSTwoFrobeniusSymbolicKernel6401
open BCHKSTwoFrobeniusThreeShiftPrimitive6401
open BCHKSTwoFrobeniusExtremeKernelCounter6401
open BCHKSTwoFrobeniusWeakCurveSeed6401
open BCHKSExtremeThreeRectangleProducer6401
open BCHKSThreeShiftSourceWindow6401
open BCHKSFrobeniusKeyEquationFork6401
set_option maxHeartbeats 5000000
set_option maxRecDepth 1000000
def extremeOwnerBadChallengeCap6401 : Nat :=
  extremeDepth6401 2 - 2
def extremeOwnerGoodChallengeFloor6401 : Nat :=
  weakCurveSeedInput6401 - extremeOwnerBadChallengeCap6401
theorem extremeOwnerWindow_exact6401 :
    extremeOwnerBadChallengeCap6401 = 47957940448246 ∧
      extremeOwnerGoodChallengeFloor6401 = 273543241402362822 ∧
      primitiveSourceWindow6401 = 162847 := by
  have hcap : extremeOwnerBadChallengeCap6401 = 47957940448246 := by
    native_decide
  refine ⟨hcap, ?_, primitiveSourceWindow_exact6401.1⟩
  rw [extremeOwnerGoodChallengeFloor6401,
    weakCurveSeed_exactParameters6401.1, hcap]
theorem sourceRelations_of_rows_eq_selected6401
    {F : Type*} [Field F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (u0 u1 : Fin n6401 → F)
    (D : ThreeShiftCommonDirection (F := F))
    (hrows : D.rows = selectedExtremeRow6401 sigma alpha u0 u1) :
    ∀ s i,
      symbolicCoordinateRelation sigma (alpha i) (u0 i) (u1 i)
        (D.rows s) = 0 := by
  intro s i
  rw [hrows]
  exact extremeKernel_coordinate_relation_eq_zero6401
    s sigma alpha u0 u1
      (selectedExtremeKernelCoefficient6401 s sigma alpha u0 u1) i
structure PrimitiveSourcePuncture6401
    {F : Type*} [Field F] [DecidableEq F]
    (D : ThreeShiftCommonDirection (F := F))
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (u0 u1 : Fin n6401 → F) where
  pivot : Fin 3
  pivot_homogeneous : pivot = 1 ∨ pivot = 2
  source_pivot_ne_zero : D.direction pivot ≠ 0
  frame : PrimitiveThreeShiftFrame D.direction pivot alpha Finset.univ
  reduced_caps : ∀ j,
    (frame.reduced j).natDegree ≤ primitiveThreeShiftXCap6401 j
  badCoordinates : Finset (Fin n6401)
  badCoordinates_card : badCoordinates.card ≤ homogeneousDirectionCap6401
  source_relation : ∀ i, i ∉ badCoordinates →
    symbolicCoordinateRelation sigma (alpha i) (u0 i) (u1 i)
      frame.reduced = 0
theorem exists_primitiveSourcePuncture6401
    {F : Type*} [Field F] [DecidableEq F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (u0 u1 : Fin n6401 → F)
    (D : ThreeShiftCommonDirection (F := F))
    (hsource : ∀ s i,
      symbolicCoordinateRelation sigma (alpha i) (u0 i) (u1 i)
        (D.rows s) = 0) :
    Nonempty (PrimitiveSourcePuncture6401 D sigma alpha u0 u1) := by
  classical
  obtain ⟨s, hs, hdirection, hmultiplierDegree⟩ :=
    exists_homogeneous_diagonal_multiplier D sigma alpha u0 u1 hsource
  let R : PrimitiveThreeShiftFrame D.direction s alpha Finset.univ :=
    primitiveThreeShiftFrame D.direction s alpha Finset.univ hdirection
  let combinedFactor : XOverZ F := D.multiplier s * R.commonFactor
  have hcombinedNe : combinedFactor ≠ 0 :=
    mul_ne_zero (D.multiplier_ne_zero s) R.commonFactor_monic.ne_zero
  have hrowFactor : D.rows s s = combinedFactor * R.reduced s := by
    calc
      D.rows s s = D.multiplier s * D.direction s := D.row_factor s s
      _ = D.multiplier s * (R.commonFactor * R.reduced s) := by
        rw [R.component_factor s]
      _ = combinedFactor * R.reduced s := by
        simp [combinedFactor, mul_assoc]
  have hcombinedDegree : combinedFactor.natDegree ≤
      homogeneousDirectionCap6401 := by
    have hdegree := D.row_caps s s
    rw [hrowFactor,
      Polynomial.natDegree_mul hcombinedNe R.pivot_ne_zero] at hdegree
    have hcap : threeShiftRowXCap6401 s s =
        homogeneousDirectionCap6401 := by
      rcases hs with rfl | rfl <;> decide
    rw [hcap] at hdegree
    exact (Nat.le_add_right combinedFactor.natDegree
      (R.reduced s).natDegree).trans hdegree
  let bad : Finset (Fin n6401) := Finset.univ.filter fun i =>
    evalOuterAt (alpha i) combinedFactor = 0
  have hbad : bad.card ≤ homogeneousDirectionCap6401 := by
    exact (card_filter_evalOuterAt_eq_zero_le_natDegree alpha Finset.univ
      combinedFactor hcombinedNe).trans hcombinedDegree
  refine ⟨{
    pivot := s
    pivot_homogeneous := hs
    source_pivot_ne_zero := hdirection
    frame := R
    reduced_caps := R.reduced_threeShift_caps D.direction_caps
    badCoordinates := bad
    badCoordinates_card := hbad
    source_relation := ?_ }⟩
  intro i hi
  have hcombinedAt : evalOuterAt (alpha i) combinedFactor ≠ 0 := by
    simpa [bad] using hi
  have hmultiplierAt : evalOuterAt (alpha i) (D.multiplier s) ≠ 0 := by
    intro hzero
    apply hcombinedAt
    have heval : evalOuterAt (alpha i) combinedFactor =
        evalOuterAt (alpha i) (D.multiplier s) *
          evalOuterAt (alpha i) R.commonFactor := by
      simp [combinedFactor, evalOuterAt]
    rw [heval, hzero, zero_mul]
  have hfactorAt : evalOuterAt (alpha i) R.commonFactor ≠ 0 := by
    intro hzero
    apply hcombinedAt
    have heval : evalOuterAt (alpha i) combinedFactor =
        evalOuterAt (alpha i) (D.multiplier s) *
          evalOuterAt (alpha i) R.commonFactor := by
      simp [combinedFactor, evalOuterAt]
    rw [heval, hzero, mul_zero]
  exact R.cancel_coordinate_relation sigma (alpha i) (u0 i) (u1 i)
    hfactorAt
      (cancel_sourceRelation_of_commonDirection D sigma
        (alpha i) (u0 i) (u1 i) s hmultiplierAt (hsource s i))
noncomputable def rowTwoBadChallenges6401
    {F : Type*} [Field F] [DecidableEq F]
    (D : ThreeShiftCommonDirection (F := F)) (S : Finset F) : Finset F :=
  S.filter fun z => specializeCoeffZ z (D.multiplier 2) = 0
noncomputable def rowTwoGoodChallenges6401
    {F : Type*} [Field F] [DecidableEq F]
    (D : ThreeShiftCommonDirection (F := F)) (S : Finset F) : Finset F :=
  S.filter fun z => specializeCoeffZ z (D.multiplier 2) ≠ 0
theorem rowTwo_multiplier_swap_natDegree_le6401
    {F : Type*} [Field F]
    (sigma : F →+* F) (alpha : Fin n6401 → F)
    (u0 u1 : Fin n6401 → F)
    (D : ThreeShiftCommonDirection (F := F))
    (hrows : D.rows = selectedExtremeRow6401 sigma alpha u0 u1)
    (pivot : Fin 3) (hpivot : pivot = 1 ∨ pivot = 2)
    (hpivotNe : D.direction pivot ≠ 0) :
    (Polynomial.Bivariate.swap (D.multiplier 2)).natDegree ≤
      extremeOwnerBadChallengeCap6401 := by
  have hmultiplier : Polynomial.Bivariate.swap (D.multiplier 2) ≠ 0 :=
    (map_ne_zero_iff Polynomial.Bivariate.swap
      Polynomial.Bivariate.swap.injective).2 (D.multiplier_ne_zero 2)
  have hswapDirection (j : Fin 3) (hj : D.direction j ≠ 0) :
      Polynomial.Bivariate.swap (D.direction j) ≠ 0 :=
    (map_ne_zero_iff Polynomial.Bivariate.swap
      Polynomial.Bivariate.swap.injective).2 hj
  rcases hpivot with rfl | rfl
  · have hdegree :
        (Polynomial.Bivariate.swap (D.rows 2 1)).natDegree ≤
          extremeDepth6401 2 - 2 := by
      rw [hrows]
      exact extremeCoefficientRowMap_one_inner_natDegree_le6401 2
        (selectedExtremeKernelCoefficient6401 2 sigma alpha u0 u1).1
    have hfactor := congrArg Polynomial.Bivariate.swap (D.row_factor 2 1)
    simp only [map_mul] at hfactor
    rw [hfactor, Polynomial.natDegree_mul hmultiplier
      (hswapDirection 1 hpivotNe)] at hdegree
    exact (Nat.le_add_right
      (Polynomial.Bivariate.swap (D.multiplier 2)).natDegree
      (Polynomial.Bivariate.swap (D.direction 1)).natDegree).trans <| by
        simpa [extremeOwnerBadChallengeCap6401] using hdegree
  · have hdegree :
        (Polynomial.Bivariate.swap (D.rows 2 2)).natDegree ≤
          (extremeDepth6401 2 - q6401) - 1 := by
      rw [hrows]
      exact extremeCoefficientRowMap_two_inner_natDegree_le6401 2
        (selectedExtremeKernelCoefficient6401 2 sigma alpha u0 u1).1
    have hfactor := congrArg Polynomial.Bivariate.swap (D.row_factor 2 2)
    simp only [map_mul] at hfactor
    rw [hfactor, Polynomial.natDegree_mul hmultiplier
      (hswapDirection 2 hpivotNe)] at hdegree
    have hshort : (extremeDepth6401 2 - q6401) - 1 ≤
        extremeOwnerBadChallengeCap6401 := by native_decide
    exact (Nat.le_add_right
      (Polynomial.Bivariate.swap (D.multiplier 2)).natDegree
      (Polynomial.Bivariate.swap (D.direction 2)).natDegree).trans
        (hdegree.trans hshort)
theorem rowTwoBadChallenges_card_le6401
    {F : Type*} [Field F] [DecidableEq F]
    (D : ThreeShiftCommonDirection (F := F)) (S : Finset F)
    (hmultiplier :
      (Polynomial.Bivariate.swap (D.multiplier 2)).natDegree ≤
        extremeOwnerBadChallengeCap6401) :
    (rowTwoBadChallenges6401 D S).card ≤
      extremeOwnerBadChallengeCap6401 := by
  obtain ⟨a, _ha, hcard⟩ :=
    card_zero_specializations_le_coefficient_degree S (D.multiplier 2)
      (D.multiplier_ne_zero 2)
  exact hcard.trans <|
    (coeff_natDegree_le_swap_natDegree (D.multiplier 2) a).trans hmultiplier
theorem rowTwoGoodChallenges_card_floor6401
    {F : Type*} [Field F] [DecidableEq F]
    (D : ThreeShiftCommonDirection (F := F)) (S : Finset F)
    (hlarge : weakCurveSeedInput6401 ≤ S.card)
    (hbad : (rowTwoBadChallenges6401 D S).card ≤
      extremeOwnerBadChallengeCap6401) :
    extremeOwnerGoodChallengeFloor6401 ≤
      (rowTwoGoodChallenges6401 D S).card := by
  have hsplit : (rowTwoBadChallenges6401 D S).card +
      (rowTwoGoodChallenges6401 D S).card = S.card := by
    rw [rowTwoBadChallenges6401, rowTwoGoodChallenges6401]
    simpa using Finset.card_filter_add_card_filter_not
      (s := S) (fun z => specializeCoeffZ z (D.multiplier 2) = 0)
  dsimp [extremeOwnerGoodChallengeFloor6401]
  omega
theorem cancel_specialized_ownerRelation_of_commonDirection
    {F : Type*} [Field F]
    (D : ThreeShiftCommonDirection (F := F))
    (sigma : F →+* F) (z : F) (P : Polynomial F) (s : Fin 3)
    (hmultiplier : specializeCoeffZ z (D.multiplier s) ≠ 0)
    (hrow : symbolicRelation sigma (specializeRow z (D.rows s)) P = 0) :
    symbolicRelation sigma (specializeRow z D.direction) P = 0 := by
  have h0 := congrArg (specializeCoeffZ z) (D.row_factor s 0)
  have h1 := congrArg (specializeCoeffZ z) (D.row_factor s 1)
  have h2 := congrArg (specializeCoeffZ z) (D.row_factor s 2)
  simp only [map_mul] at h0 h1 h2
  unfold symbolicRelation at hrow ⊢
  simp only [specializeRow] at hrow ⊢
  rw [h0, h1, h2] at hrow
  apply mul_left_cancel₀ hmultiplier
  linear_combination hrow
structure PrimitivePuncturedOwnerWindow6401
    {F : Type*} [Field F] [DecidableEq F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (u0 u1 : Fin n6401 → F)
    (S : Finset F) (A : F → Finset (Fin n6401))
    (P : F → Polynomial F) where
  commonDirection : ThreeShiftCommonDirection (F := F)
  rows_eq_selected : commonDirection.rows =
    selectedExtremeRow6401 sigma alpha u0 u1
  sourcePuncture : PrimitiveSourcePuncture6401 commonDirection
    sigma alpha u0 u1
  goodChallenges_card : extremeOwnerGoodChallengeFloor6401 ≤
    (rowTwoGoodChallenges6401 commonDirection S).card
  owner_relation : ∀ z ∈ rowTwoGoodChallenges6401 commonDirection S,
    symbolicRelation sigma
      (specializeRow z sourcePuncture.frame.reduced) (P z) = 0
  retained_agreements : ∀ z ∈ rowTwoGoodChallenges6401 commonDirection S,
    primitiveSourceWindow6401 ≤
      ((A z) \ sourcePuncture.badCoordinates).card
theorem exists_primitivePuncturedOwnerWindow_of_direction6401
    {F : Type*} [Field F] [DecidableEq F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (u0 u1 : Fin n6401 → F)
    (S : Finset F) (A : F → Finset (Fin n6401))
    (P : F → Polynomial F)
    (D : ThreeShiftCommonDirection (F := F))
    (hrows : D.rows = selectedExtremeRow6401 sigma alpha u0 u1)
    (hlarge : weakCurveSeedInput6401 ≤ S.card)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (hownerRelation : ∀ s z, z ∈ S →
      symbolicRelation sigma (specializeRow z (D.rows s)) (P z) = 0) :
    Nonempty (PrimitivePuncturedOwnerWindow6401
      sigma alpha u0 u1 S A P) := by
  classical
  have hsource := sourceRelations_of_rows_eq_selected6401
    sigma alpha u0 u1 D hrows
  obtain ⟨puncture⟩ :=
    exists_primitiveSourcePuncture6401 sigma alpha u0 u1 D hsource
  have hmultiplier := rowTwo_multiplier_swap_natDegree_le6401
    sigma alpha u0 u1 D hrows puncture.pivot
      puncture.pivot_homogeneous puncture.source_pivot_ne_zero
  have hbad := rowTwoBadChallenges_card_le6401 D S hmultiplier
  have hgood := rowTwoGoodChallenges_card_floor6401 D S hlarge hbad
  refine ⟨{
    commonDirection := D
    rows_eq_selected := hrows
    sourcePuncture := puncture
    goodChallenges_card := hgood
    owner_relation := ?_
    retained_agreements := ?_ }⟩
  · intro z hz
    have hzS : z ∈ S := (Finset.mem_filter.mp hz).1
    have hmult : specializeCoeffZ z (D.multiplier 2) ≠ 0 :=
      (Finset.mem_filter.mp hz).2
    exact puncture.frame.cancel_specialized_relation sigma z (P z)
      (cancel_specialized_ownerRelation_of_commonDirection
        D sigma z (P z) 2 hmult (hownerRelation 2 z hzS))
  · intro z hz
    have hzS : z ∈ S := (Finset.mem_filter.mp hz).1
    let retained := (A z) \ puncture.badCoordinates
    have hcover : A z ⊆ retained ∪ puncture.badCoordinates := by
      intro i hi
      by_cases hibad : i ∈ puncture.badCoordinates
      · exact Finset.mem_union_right retained hibad
      · exact Finset.mem_union_left puncture.badCoordinates
          (Finset.mem_sdiff.mpr ⟨hi, hibad⟩)
    have hcard : (A z).card ≤ retained.card +
        puncture.badCoordinates.card := by
      calc
        (A z).card ≤ (retained ∪ puncture.badCoordinates).card :=
          Finset.card_le_card hcover
        _ ≤ retained.card + puncture.badCoordinates.card :=
          Finset.card_union_le _ _
    have hAz := hrow z hzS
    have hbadCoords := puncture.badCoordinates_card
    change primitiveSourceWindow6401 ≤ retained.card
    norm_num [primitiveSourceWindow6401, homogeneousDirectionCap6401,
      a6401] at hAz hbadCoords ⊢
    omega
theorem twoLaneErrorRelation_of_owner_and_source6401
    {F : Type*} [Field F]
    (sigma : F →+* F) (x z u0 u1 : F) (P : Polynomial F)
    (B : SymbolicRow F)
    (hsigma : sigma z = z ^ q6401)
    (hfixed : sigma x = x)
    (howner : symbolicRelation sigma (specializeRow z B) P = 0)
    (hsource : symbolicCoordinateRelation sigma x u0 u1 B = 0) :
    Polynomial.eval x (specializeRow z B 1) *
          (Polynomial.eval x P - (u0 + z * u1)) +
        Polynomial.eval x (specializeRow z B 2) *
          sigma (Polynomial.eval x P - (u0 + z * u1)) = 0 := by
  have hownerEval := congrArg (Polynomial.eval x) howner
  unfold symbolicRelation at hownerEval
  simp only [Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_zero] at hownerEval
  have htwist : Polynomial.eval x (P.map sigma) =
      sigma (Polynomial.eval x P) := by
    simpa [BCHKSTwoFrobeniusRank6401.twist] using
      BCHKSTwoFrobeniusRank6401.eval_twist_of_fixed sigma x hfixed P
  rw [htwist] at hownerEval
  have hsourceEval := congrArg (Polynomial.eval z) hsource
  unfold symbolicCoordinateRelation at hsourceEval
  simp only [Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_zero] at hsourceEval
  rw [← eval_specializeCoeffZ_comm z x (B 0),
    ← eval_specializeCoeffZ_comm z x (B 1),
    ← eval_specializeCoeffZ_comm z x (B 2)] at hsourceEval
  have hreceived : Polynomial.eval z (receivedZ u0 u1) =
      u0 + z * u1 := by
    simp [receivedZ]
    ring
  rw [hreceived,
    eval_receivedFrobeniusZ sigma z u0 u1 hsigma] at hsourceEval
  rw [map_sub]
  simp only [specializeRow] at hownerEval ⊢
  linear_combination hownerEval - hsourceEval
theorem PrimitivePuncturedOwnerWindow6401.twoLaneErrorRelation
    {F : Type*} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (z : F) (hz : z ∈ rowTwoGoodChallenges6401 W.commonDirection S)
    (i : Fin n6401) (hi : i ∉ W.sourcePuncture.badCoordinates) :
    Polynomial.eval (alpha i)
          (specializeRow z W.sourcePuncture.frame.reduced 1) *
          (Polynomial.eval (alpha i) (P z) - (u0 i + z * u1 i)) +
        Polynomial.eval (alpha i)
          (specializeRow z W.sourcePuncture.frame.reduced 2) *
          sigma (Polynomial.eval (alpha i) (P z) -
            (u0 i + z * u1 i)) = 0 := by
  exact twoLaneErrorRelation_of_owner_and_source6401
    sigma (alpha i) z (u0 i) (u1 i) (P z)
      W.sourcePuncture.frame.reduced (hsigma z) (hfixed i)
      (W.owner_relation z hz) (W.sourcePuncture.source_relation i hi)
noncomputable def PrimitivePuncturedOwnerWindow6401.unpuncturedCoordinates
    {F : Type*} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P) :
    Finset (Fin n6401) :=
  Finset.univ \ W.sourcePuncture.badCoordinates
abbrev PrimitivePuncturedOwnerWindow6401.PuncturedIndex
    {F : Type*} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P) :=
  {i : Fin n6401 // i ∈ W.unpuncturedCoordinates}
def PrimitivePuncturedOwnerWindow6401.puncturedAlpha
    {F : Type*} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P) :
    W.PuncturedIndex ↪ F where
  toFun i := alpha i.1
  inj' := by
    intro i j hij
    apply Subtype.ext
    exact alpha.injective hij
def PrimitivePuncturedOwnerWindow6401.puncturedOwnerError
    {F : Type*} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (z : F) : W.PuncturedIndex → F :=
  fun i => Polynomial.eval (alpha i.1) (P z) - (u0 i.1 + z * u1 i.1)
theorem PrimitivePuncturedOwnerWindow6401.puncturedIndex_card_ge_239637
    {F : Type*} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P) :
    239637 ≤ Fintype.card W.PuncturedIndex := by
  have hpartition : W.unpuncturedCoordinates.card +
      W.sourcePuncture.badCoordinates.card = n6401 := by
    simpa [PrimitivePuncturedOwnerWindow6401.unpuncturedCoordinates]
      using Finset.card_sdiff_add_card_eq_card
        (Finset.subset_univ W.sourcePuncture.badCoordinates)
  have hbad := W.sourcePuncture.badCoordinates_card
  have hunpunctured : 239637 ≤ W.unpuncturedCoordinates.card := by
    norm_num [n6401, homogeneousDirectionCap6401] at hpartition hbad ⊢
    omega
  simpa [PrimitivePuncturedOwnerWindow6401.PuncturedIndex,
    Fintype.card_coe] using hunpunctured
theorem PrimitivePuncturedOwnerWindow6401.puncturedTwoLaneFailureRelation
    {F : Type*} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (z : F) (hz : z ∈ rowTwoGoodChallenges6401 W.commonDirection S) :
    TwoLaneFailureRelation sigma W.puncturedAlpha
      (W.puncturedOwnerError z)
      (specializeRow z W.sourcePuncture.frame.reduced 2)
      (-(specializeRow z W.sourcePuncture.frame.reduced 1)) := by
  intro i
  have hi : i.1 ∉ W.sourcePuncture.badCoordinates :=
    (Finset.mem_sdiff.mp i.2).2
  have hrel := W.twoLaneErrorRelation hsigma hfixed z hz i.1 hi
  change Polynomial.eval (alpha i.1)
        (specializeRow z W.sourcePuncture.frame.reduced 2) *
        sigma (W.puncturedOwnerError z i) =
      Polynomial.eval (alpha i.1)
        (-(specializeRow z W.sourcePuncture.frame.reduced 1)) *
        W.puncturedOwnerError z i
  dsimp [PrimitivePuncturedOwnerWindow6401.puncturedOwnerError]
  simp only [Polynomial.eval_neg]
  linear_combination hrel
theorem curve_or_primitivePuncturedOwnerWindow6401
    {F : Type} [Field F] [DecidableEq F]
    (sigma : F →+* F) (alpha : Fin n6401 ↪ F)
    (u0 u1 : Fin n6401 → F)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (S : Finset F) (A : F → Finset (Fin n6401))
    (P : F → Polynomial F)
    (hSlarge : weakCurveSeedInput6401 ≤ S.card)
    (hPdegree : ∀ z ∈ S, (P z).natDegree ≤ ownerDegreeCap6401)
    (hrow : ∀ z ∈ S, a6401 ≤ (A z).card)
    (howner : ∀ z ∈ S, ∀ i ∈ A z,
      Polynomial.eval (alpha i) (P z) = u0 i + z * u1 i) :
    PolynomialAffineCurveWitness6401 S P ∨
      Nonempty (PrimitivePuncturedOwnerWindow6401
        sigma alpha u0 u1 S A P) := by
  classical
  by_cases hcurve : PolynomialAffineCurveWitness6401 S P
  · exact Or.inl hcurve
  · right
    obtain ⟨D, hrows, hownerRelation, _hnormalized⟩ :=
      exists_sourceFaithfulThreeShiftCommonDirection6401
        sigma alpha u0 u1 hsigma hfixed S A P hSlarge
          hPdegree hrow howner hcurve
    exact exists_primitivePuncturedOwnerWindow_of_direction6401
      sigma alpha u0 u1 S A P D hrows hSlarge hrow hownerRelation
end BCHKSExtremePrimitivePuncturedOwnerWindow6401
end ProximityPrize.SubmissionLower
