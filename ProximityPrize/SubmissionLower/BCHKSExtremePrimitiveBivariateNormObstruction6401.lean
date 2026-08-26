import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveNormDivisorFork6401
import ProximityPrize.SubmissionLower.BCHKSFrobeniusGraphHilbert90Audit6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveBivariateNormObstruction6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSTwoFrobeniusRankTwoClosure6401
open BCHKSTwoFrobeniusRationalOwnerLocator6401
open BCHKSTwoFrobeniusThreeShiftPrimitive6401
open BCHKSTwoFrobeniusExtremeKernelCounter6401
open BCHKSExtremeThreeRectangleProducer6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveNormDivisorFork6401
open BCHKSFrobeniusPrimitiveCleanup6401
open BCHKSFrobeniusGraphInjectivity6401
open BCHKSFrobeniusGraphHilbert90Audit6401
set_option maxHeartbeats 6000000
set_option maxRecDepth 1000000
def primitiveLaneZeroChallengeCap6401 : Nat :=
  (extremeDepth6401 2 - q6401) - 1
def primitiveLaneOneChallengeCap6401 : Nat :=
  (extremeDepth6401 2 - 1) - 1
noncomputable def primitiveBivariateFailureLaneZero6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P) :
    F[X][X] :=
  W.sourcePuncture.frame.reduced 2
noncomputable def primitiveBivariateFailureLaneOne6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P) :
    F[X][X] :=
  -(W.sourcePuncture.frame.reduced 1)
theorem reduced_swap_natDegree_le_thirdRow6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (j : Fin 3) :
    (Polynomial.Bivariate.swap
      (W.sourcePuncture.frame.reduced j)).natDegree ≤
      (Polynomial.Bivariate.swap (W.commonDirection.rows 2 j)).natDegree := by
  by_cases hj : W.sourcePuncture.frame.reduced j = 0
  · simp [hj]
  · have hmultiplier : Polynomial.Bivariate.swap
        (W.commonDirection.multiplier 2) ≠ 0 :=
      (map_ne_zero_iff Polynomial.Bivariate.swap
        Polynomial.Bivariate.swap.injective).2
          (W.commonDirection.multiplier_ne_zero 2)
    have hcommon : Polynomial.Bivariate.swap
        W.sourcePuncture.frame.commonFactor ≠ 0 :=
      (map_ne_zero_iff Polynomial.Bivariate.swap
        Polynomial.Bivariate.swap.injective).2
          W.sourcePuncture.frame.commonFactor_monic.ne_zero
    have hreduced : Polynomial.Bivariate.swap
        (W.sourcePuncture.frame.reduced j) ≠ 0 :=
      (map_ne_zero_iff Polynomial.Bivariate.swap
        Polynomial.Bivariate.swap.injective).2 hj
    have hfactor : W.commonDirection.rows 2 j =
        W.commonDirection.multiplier 2 *
          (W.sourcePuncture.frame.commonFactor *
            W.sourcePuncture.frame.reduced j) := by
      rw [W.commonDirection.row_factor,
        W.sourcePuncture.frame.component_factor]
    have hswap := congrArg Polynomial.Bivariate.swap hfactor
    simp only [map_mul] at hswap
    rw [hswap, Polynomial.natDegree_mul hmultiplier
      (mul_ne_zero hcommon hreduced),
      Polynomial.natDegree_mul hcommon hreduced]
    omega
theorem primitiveBivariateFailureLanes_coeffDegreeLE6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P) :
    BivariateCoeffDegreeLE (primitiveBivariateFailureLaneZero6401 W)
        primitiveLaneZeroChallengeCap6401 ∧
      BivariateCoeffDegreeLE (primitiveBivariateFailureLaneOne6401 W)
        primitiveLaneOneChallengeCap6401 := by
  constructor
  · intro n
    apply (coeff_natDegree_le_swap_natDegree
      (W.sourcePuncture.frame.reduced 2) n).trans
    apply (reduced_swap_natDegree_le_thirdRow6401 W 2).trans
    rw [W.rows_eq_selected]
    simpa [primitiveLaneZeroChallengeCap6401, selectedExtremeRow6401] using
      extremeCoefficientRowMap_two_inner_natDegree_le6401 2
        (selectedExtremeKernelCoefficient6401 2 sigma alpha u0 u1).1
  · intro n
    rw [primitiveBivariateFailureLaneOne6401, Polynomial.coeff_neg,
      Polynomial.natDegree_neg]
    apply (coeff_natDegree_le_swap_natDegree
      (W.sourcePuncture.frame.reduced 1) n).trans
    apply (reduced_swap_natDegree_le_thirdRow6401 W 1).trans
    rw [W.rows_eq_selected]
    simpa [primitiveLaneOneChallengeCap6401, selectedExtremeRow6401] using
      extremeCoefficientRowMap_one_inner_natDegree_le6401 2
        (selectedExtremeKernelCoefficient6401 2 sigma alpha u0 u1).1
theorem primitiveBivariateFailureLaneZero_specialize6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (z : F) :
    specializeCoeffZ z (primitiveBivariateFailureLaneZero6401 W) =
      primitiveFailureLaneZero6401 W z := by
  rfl
theorem primitiveBivariateFailureLaneOne_specialize6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (z : F) :
    specializeCoeffZ z (primitiveBivariateFailureLaneOne6401 W) =
      primitiveFailureLaneOne6401 W z := by
  simp [primitiveBivariateFailureLaneOne6401,
    primitiveFailureLaneOne6401, specializeRow]
noncomputable def graphFrobeniusNormSix6401
    {F : Type} [Field F] (sigma : F →+* F) (q : Nat)
    (B : F[X][X]) : F[X][X] :=
  B * graphTwist6401 sigma q B * graphTwistTwo6401 sigma q B *
    graphTwistThree6401 sigma q B * graphTwistFour6401 sigma q B *
      graphTwistFive6401 sigma q B
def graphFrobeniusNormSixChallengeCap6401 (q D : Nat) : Nat :=
  D + D * q + D * q ^ 2 + D * q ^ 3 + D * q ^ 4 + D * q ^ 5
noncomputable def primitiveFamilyNormObstruction6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P) :
    F[X][X] :=
  graphFrobeniusNormSix6401 sigma q6401
      (primitiveBivariateFailureLaneZero6401 W) -
    graphFrobeniusNormSix6401 sigma q6401
      (primitiveBivariateFailureLaneOne6401 W)
def primitiveFamilyNormChallengeCap6401 : Nat :=
  graphFrobeniusNormSixChallengeCap6401 q6401
    primitiveLaneOneChallengeCap6401
theorem primitiveFamilyNormChallengeCaps_exact6401 :
    primitiveLaneZeroChallengeCap6401 = 47955809741814 ∧
      primitiveLaneOneChallengeCap6401 = 47957940448246 ∧
      primitiveFamilyNormChallengeCap6401 =
        2106098165052670954181333187038364386532010033457403280164804 := by
  native_decide
theorem graphFrobeniusNormSix_specialize6401
    {F : Type} [Field F] (sigma : F →+* F) (q : Nat)
    (B : F[X][X]) (z : F) (hz : sigma z = z ^ q) :
    specializeCoeffZ z (graphFrobeniusNormSix6401 sigma q B) =
      polynomialFrobeniusNormSix sigma (specializeCoeffZ z B) := by
  simp only [specializeCoeffZ_apply, graphFrobeniusNormSix6401,
    Polynomial.map_mul]
  rw [graphTwist_specialize6401 sigma q B z hz,
    graphTwistTwo_specialize6401 sigma q B z hz,
    graphTwistThree_specialize6401 sigma q B z hz,
    graphTwistFour_specialize6401 sigma q B z hz,
    graphTwistFive_specialize6401 sigma q B z hz]
  rfl
theorem primitiveFamilyNormObstruction_specialize6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (z : F) (hz : sigma z = z ^ q6401) :
    specializeCoeffZ z (primitiveFamilyNormObstruction6401 W) =
      primitiveOwnerNormObstruction6401 W z := by
  simp only [primitiveFamilyNormObstruction6401, map_sub]
  rw [graphFrobeniusNormSix_specialize6401 sigma q6401 _ z hz,
    graphFrobeniusNormSix_specialize6401 sigma q6401 _ z hz,
    primitiveBivariateFailureLaneZero_specialize6401 W z,
    primitiveBivariateFailureLaneOne_specialize6401 W z]
  rfl
private theorem sixFactors_coeffDegreeLE6401
    {F : Type} [Field F]
    (P0 P1 P2 P3 P4 P5 : F[X][X])
    (D0 D1 D2 D3 D4 D5 : Nat)
    (h0 : BivariateCoeffDegreeLE P0 D0)
    (h1 : BivariateCoeffDegreeLE P1 D1)
    (h2 : BivariateCoeffDegreeLE P2 D2)
    (h3 : BivariateCoeffDegreeLE P3 D3)
    (h4 : BivariateCoeffDegreeLE P4 D4)
    (h5 : BivariateCoeffDegreeLE P5 D5) :
    BivariateCoeffDegreeLE (P0 * P1 * P2 * P3 * P4 * P5)
      (D0 + D1 + D2 + D3 + D4 + D5) := by
  exact BivariateCoeffDegreeLE_mul
    (BivariateCoeffDegreeLE_mul
      (BivariateCoeffDegreeLE_mul
        (BivariateCoeffDegreeLE_mul
          (BivariateCoeffDegreeLE_mul h0 h1) h2) h3) h4) h5
theorem graphFrobeniusNormSix_coeffDegreeLE6401
    {F : Type} [Field F] (sigma : F →+* F) (q D : Nat)
    (B : F[X][X]) (hB : BivariateCoeffDegreeLE B D) :
    BivariateCoeffDegreeLE (graphFrobeniusNormSix6401 sigma q B)
      (graphFrobeniusNormSixChallengeCap6401 q D) := by
  rcases graphTwist_iterate_coeffDegreeLE6401 sigma q D B hB with
    ⟨h1, h2, h3, h4, h5⟩
  simpa [graphFrobeniusNormSix6401,
    graphFrobeniusNormSixChallengeCap6401] using
      sixFactors_coeffDegreeLE6401 B
        (graphTwist6401 sigma q B)
        (graphTwistTwo6401 sigma q B)
        (graphTwistThree6401 sigma q B)
        (graphTwistFour6401 sigma q B)
        (graphTwistFive6401 sigma q B)
        D (D * q) (D * q ^ 2) (D * q ^ 3) (D * q ^ 4) (D * q ^ 5)
        hB h1 h2 h3 h4 h5
theorem graphFrobeniusNormSix_natDegree_le6401
    {F : Type} [Field F] [DecidableEq F]
    (sigma : F →+* F) (q p : Nat)
    (B : F[X][X]) (hB : B.natDegree ≤ p) :
    (graphFrobeniusNormSix6401 sigma q B).natDegree ≤ 6 * p := by
  rcases graphTwist_iterate_natDegree_le6401 sigma q p B hB with
    ⟨h1, h2, h3, h4⟩
  have h5 : (graphTwistFive6401 sigma q B).natDegree ≤ p := by
    exact Polynomial.natDegree_map_le.trans h4
  have h01 := Polynomial.natDegree_mul_le
    (p := B) (q := graphTwist6401 sigma q B)
  have h012 := Polynomial.natDegree_mul_le
    (p := B * graphTwist6401 sigma q B)
    (q := graphTwistTwo6401 sigma q B)
  have h0123 := Polynomial.natDegree_mul_le
    (p := B * graphTwist6401 sigma q B * graphTwistTwo6401 sigma q B)
    (q := graphTwistThree6401 sigma q B)
  have h01234 := Polynomial.natDegree_mul_le
    (p := B * graphTwist6401 sigma q B * graphTwistTwo6401 sigma q B *
      graphTwistThree6401 sigma q B)
    (q := graphTwistFour6401 sigma q B)
  have h012345 := Polynomial.natDegree_mul_le
    (p := B * graphTwist6401 sigma q B * graphTwistTwo6401 sigma q B *
      graphTwistThree6401 sigma q B * graphTwistFour6401 sigma q B)
    (q := graphTwistFive6401 sigma q B)
  unfold graphFrobeniusNormSix6401
  omega
private theorem BivariateCoeffDegreeLE_neg6401
    {F : Type} [Field F] {B : F[X][X]} {D : Nat}
    (hB : BivariateCoeffDegreeLE B D) :
    BivariateCoeffDegreeLE (-B) D := by
  intro n
  rw [Polynomial.coeff_neg, Polynomial.natDegree_neg]
  exact hB n
private theorem BivariateCoeffDegreeLE_sub6401
    {F : Type} [Field F] {B C : F[X][X]} {D E : Nat}
    (hB : BivariateCoeffDegreeLE B D)
    (hC : BivariateCoeffDegreeLE C E) :
    BivariateCoeffDegreeLE (B - C) (max D E) := by
  rw [sub_eq_add_neg]
  exact BivariateCoeffDegreeLE_add hB (BivariateCoeffDegreeLE_neg6401 hC)
theorem primitiveFamilyNormObstruction_coeffDegreeLE6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P) :
    BivariateCoeffDegreeLE (primitiveFamilyNormObstruction6401 W)
      primitiveFamilyNormChallengeCap6401 := by
  rcases primitiveBivariateFailureLanes_coeffDegreeLE6401 W with
    ⟨hzero, hone⟩
  have hnormZero := graphFrobeniusNormSix_coeffDegreeLE6401 sigma q6401
    primitiveLaneZeroChallengeCap6401
      (primitiveBivariateFailureLaneZero6401 W) hzero
  have hnormOne := graphFrobeniusNormSix_coeffDegreeLE6401 sigma q6401
    primitiveLaneOneChallengeCap6401
      (primitiveBivariateFailureLaneOne6401 W) hone
  have hcap : graphFrobeniusNormSixChallengeCap6401 q6401
      primitiveLaneZeroChallengeCap6401 ≤
      graphFrobeniusNormSixChallengeCap6401 q6401
        primitiveLaneOneChallengeCap6401 := by
    native_decide
  simpa [primitiveFamilyNormObstruction6401,
    primitiveFamilyNormChallengeCap6401, max_eq_right hcap] using
      BivariateCoeffDegreeLE_sub6401 hnormZero hnormOne
theorem primitiveFamilyNormObstruction_natDegree_le_135042_6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P) :
    (primitiveFamilyNormObstruction6401 W).natDegree ≤ 135042 := by
  have hzero : (primitiveBivariateFailureLaneZero6401 W).natDegree ≤
      22507 := by
    exact W.sourcePuncture.reduced_caps 2
  have hone : (primitiveBivariateFailureLaneOne6401 W).natDegree ≤
      22507 := by
    simpa [primitiveBivariateFailureLaneOne6401,
      primitiveThreeShiftXCap6401] using
      W.sourcePuncture.reduced_caps 1
  have hnormZero := graphFrobeniusNormSix_natDegree_le6401 sigma q6401
    22507 (primitiveBivariateFailureLaneZero6401 W) hzero
  have hnormOne := graphFrobeniusNormSix_natDegree_le6401 sigma q6401
    22507 (primitiveBivariateFailureLaneOne6401 W) hone
  unfold primitiveFamilyNormObstruction6401
  norm_num at hnormZero hnormOne
  exact (Polynomial.natDegree_sub_le _ _).trans
    (max_le hnormZero hnormOne)
noncomputable def primitiveFamilyNormDegenerateChallenges6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (T : Finset F) : Finset F :=
  T.filter fun z =>
    specializeCoeffZ z (primitiveFamilyNormObstruction6401 W) = 0
theorem primitiveFamilyNormDegenerateChallenges_card_le6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (T : Finset F) (hnorm : primitiveFamilyNormObstruction6401 W ≠ 0) :
    (primitiveFamilyNormDegenerateChallenges6401 W T).card ≤
      primitiveFamilyNormChallengeCap6401 := by
  have hroot := BCHKSQuadraticKernel6400.specialization_zero_card_le_degreeX
    (primitiveFamilyNormObstruction6401 W) T hnorm
  have hdegree : Polynomial.Bivariate.degreeX
      (primitiveFamilyNormObstruction6401 W) ≤
      primitiveFamilyNormChallengeCap6401 := by
    unfold Polynomial.Bivariate.degreeX
    apply Finset.sup_le
    intro n hn
    exact primitiveFamilyNormObstruction_coeffDegreeLE6401 W n
  simpa [primitiveFamilyNormDegenerateChallenges6401,
    specializeCoeffZ_apply] using hroot.trans hdegree
theorem puncturedErrorLocator_dvd_familyNormSpecialization6401
    {F : Type} [Field F] [DecidableEq F]
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
      specializeCoeffZ z (primitiveFamilyNormObstruction6401 W) := by
  rw [primitiveFamilyNormObstruction_specialize6401 W z (hsigma z)]
  exact puncturedErrorLocator_dvd_normObstruction6401
    W hsigma hfixed horder z hz
theorem eval_familyNormSpecialization_eq_zero_of_mem_errorSupport6401
    {F : Type} [Field F] [DecidableEq F]
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
    (i : W.PuncturedIndex) (hi : i ∈ puncturedErrorSupport6401 W z) :
    Polynomial.eval (W.puncturedAlpha i)
      (specializeCoeffZ z (primitiveFamilyNormObstruction6401 W)) = 0 := by
  obtain ⟨Q, hQ⟩ := puncturedErrorLocator_dvd_familyNormSpecialization6401
    W hsigma hfixed horder z hz
  rw [hQ, Polynomial.eval_mul, puncturedErrorLocator6401,
    ownerLocator_eval_eq_zero W.puncturedAlpha
      (puncturedErrorSupport6401 W z) i hi, zero_mul]
theorem familyNormDegenerate_or_commonSplitObstruction6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (horder : ∀ x,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x) :
    primitiveFamilyNormObstruction6401 W = 0 ∨
      (primitiveFamilyNormObstruction6401 W ≠ 0 ∧
        (primitiveFamilyNormDegenerateChallenges6401 W
          (rowTwoGoodChallenges6401 W.commonDirection S)).card ≤
            primitiveFamilyNormChallengeCap6401 ∧
        ∀ z ∈ rowTwoGoodChallenges6401 W.commonDirection S,
          puncturedErrorLocator6401 W z ∣
            specializeCoeffZ z
              (primitiveFamilyNormObstruction6401 W)) := by
  by_cases hnorm : primitiveFamilyNormObstruction6401 W = 0
  · exact Or.inl hnorm
  · refine Or.inr ⟨hnorm,
      primitiveFamilyNormDegenerateChallenges_card_le6401 W _ hnorm, ?_⟩
    intro z hz
    exact puncturedErrorLocator_dvd_familyNormSpecialization6401
      W hsigma hfixed horder z hz
end BCHKSExtremePrimitiveBivariateNormObstruction6401
end ProximityPrize.SubmissionLower
