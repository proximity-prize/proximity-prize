import ProximityPrize.SubmissionLower.BCHKSExtremePrimitiveBivariateNormObstruction6401
namespace ProximityPrize.SubmissionLower
namespace BCHKSExtremePrimitiveGraphGaugeFork6401
open Polynomial
open BCHKSTwoFrobeniusModuleAudit6401
open BCHKSTwoFrobeniusRankTwoSpecialization6401
open BCHKSFrobeniusKeyEquationFork6401
open BCHKSExtremePrimitivePuncturedOwnerWindow6401
open BCHKSExtremePrimitiveNormDivisorFork6401
open BCHKSExtremePrimitiveBivariateNormObstruction6401
open BCHKSFrobeniusGraphInjectivity6401
open BCHKSFrobeniusGraphHilbert90Audit6401
open BCHKSFrobeniusHilbert90Normalization6401
open BCHKSFrobeniusOffsetProductDegreeAudit6401
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
theorem graphHilbert90Numerator_shift_of_graphNorm_eq6401
    {F : Type} [Field F] [DecidableEq F]
    (sigma : F →+* F) (q : Nat) (A B : F[X][X]) (t : F)
    (ht : sigma (sigma (sigma (sigma (sigma (sigma t))))) = t)
    (hnorm : graphFrobeniusNormSix6401 sigma q A =
      graphFrobeniusNormSix6401 sigma q B) :
    A * graphTwist6401 sigma q
          (graphHilbert90Numerator6401 sigma q A B t) =
      graphTwistFive6401 sigma q B *
        graphHilbert90Numerator6401 sigma q A B t := by
  have hC (s : F) :
      challengeFrobeniusRingHom6401 sigma q (Polynomial.C s) =
        Polynomial.C (sigma s) := by
    rw [challengeFrobeniusRingHom_apply6401]
    simp [challengeFrobenius]
  simp only [graphHilbert90Numerator6401,
    graphHilbert90Denominator6401, graphTwist6401,
    Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
    graphTwistTwo6401, graphTwistThree6401, graphTwistFour6401,
    graphTwistFive6401]
  simp only [hC]
  rw [ht]
  simp only [graphFrobeniusNormSix6401, graphTwist6401,
    graphTwistTwo6401, graphTwistThree6401, graphTwistFour6401,
    graphTwistFive6401] at hnorm
  linear_combination Polynomial.C (Polynomial.C t) * hnorm
theorem graphHilbert90Gauge_cross_of_graphNorm_eq6401
    {F : Type} [Field F] [DecidableEq F]
    (sigma : F →+* F) (q : Nat) (A B : F[X][X]) (t : F)
    (ht : sigma (sigma (sigma (sigma (sigma (sigma t))))) = t)
    (hnorm : graphFrobeniusNormSix6401 sigma q A =
      graphFrobeniusNormSix6401 sigma q B) :
    A * graphTwist6401 sigma q
          (graphHilbert90Numerator6401 sigma q A B t) *
        graphHilbert90Denominator6401 sigma q B =
      B * graphHilbert90Numerator6401 sigma q A B t *
        graphTwist6401 sigma q
          (graphHilbert90Denominator6401 sigma q B) := by
  have hshift := graphHilbert90Numerator_shift_of_graphNorm_eq6401
    sigma q A B t ht hnorm
  rw [hshift]
  simp only [graphHilbert90Denominator6401, graphTwist6401,
    Polynomial.map_mul, graphTwistTwo6401, graphTwistThree6401,
    graphTwistFour6401, graphTwistFive6401]
  ring
noncomputable def primitiveFamilyGraphGaugeNumerator6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (t : F) : F[X][X] :=
  graphHilbert90Numerator6401 sigma q6401
    (primitiveBivariateFailureLaneZero6401 W)
    (primitiveBivariateFailureLaneOne6401 W) t
noncomputable def primitiveFamilyGraphGaugeDenominator6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P) :
    F[X][X] :=
  graphHilbert90Denominator6401 sigma q6401
    (primitiveBivariateFailureLaneOne6401 W)
def primitiveFamilyGraphGaugeChallengeCap6401 : Nat :=
  graphHilbert90OuterCap6401 q6401 primitiveLaneOneChallengeCap6401
theorem primitiveFamilyGraphGauge_degreeLedger6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (t : F) :
    (primitiveFamilyGraphGaugeNumerator6401 W t).natDegree ≤ 112535 ∧
      (primitiveFamilyGraphGaugeDenominator6401 W).natDegree ≤ 112535 ∧
      BivariateCoeffDegreeLE (primitiveFamilyGraphGaugeNumerator6401 W t)
        primitiveFamilyGraphGaugeChallengeCap6401 ∧
      BivariateCoeffDegreeLE (primitiveFamilyGraphGaugeDenominator6401 W)
        primitiveFamilyGraphGaugeChallengeCap6401 := by
  rcases primitiveBivariateFailureLanes_coeffDegreeLE6401 W with
    ⟨hzeroZ, honeZ⟩
  have hcap : primitiveLaneZeroChallengeCap6401 ≤
      primitiveLaneOneChallengeCap6401 := by native_decide
  have hzeroZ' : BivariateCoeffDegreeLE
      (primitiveBivariateFailureLaneZero6401 W)
      primitiveLaneOneChallengeCap6401 :=
    fun n => (hzeroZ n).trans hcap
  have hzeroX : (primitiveBivariateFailureLaneZero6401 W).natDegree ≤
      22507 := W.sourcePuncture.reduced_caps 2
  have honeX : (primitiveBivariateFailureLaneOne6401 W).natDegree ≤
      22507 := by
    simpa [primitiveBivariateFailureLaneOne6401,
      BCHKSTwoFrobeniusThreeShiftPrimitive6401.primitiveThreeShiftXCap6401]
      using W.sourcePuncture.reduced_caps 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [primitiveFamilyGraphGaugeNumerator6401] using
      graphHilbert90Numerator_natDegree_le6401 sigma q6401 22507
        (primitiveBivariateFailureLaneZero6401 W)
        (primitiveBivariateFailureLaneOne6401 W) t hzeroX honeX
  · simpa [primitiveFamilyGraphGaugeDenominator6401] using
      graphHilbert90Denominator_natDegree_le6401 sigma q6401 22507
        (primitiveBivariateFailureLaneOne6401 W) honeX
  · simpa [primitiveFamilyGraphGaugeNumerator6401,
      primitiveFamilyGraphGaugeChallengeCap6401] using
      graphHilbert90Numerator_coeffDegreeLE6401 sigma q6401
        primitiveLaneOneChallengeCap6401
        (primitiveBivariateFailureLaneZero6401 W)
        (primitiveBivariateFailureLaneOne6401 W) t hzeroZ' honeZ
  · simpa [primitiveFamilyGraphGaugeDenominator6401,
      primitiveFamilyGraphGaugeChallengeCap6401] using
      graphHilbert90Denominator_coeffDegreeLE6401 sigma q6401
        primitiveLaneOneChallengeCap6401
        (primitiveBivariateFailureLaneOne6401 W) honeZ
theorem primitiveFamilyGraphGauge_cross6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (horder : ∀ x,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (hnorm : primitiveFamilyNormObstruction6401 W = 0)
    (t : F) :
    primitiveBivariateFailureLaneZero6401 W *
          graphTwist6401 sigma q6401
            (primitiveFamilyGraphGaugeNumerator6401 W t) *
          primitiveFamilyGraphGaugeDenominator6401 W =
      primitiveBivariateFailureLaneOne6401 W *
          primitiveFamilyGraphGaugeNumerator6401 W t *
          graphTwist6401 sigma q6401
            (primitiveFamilyGraphGaugeDenominator6401 W) := by
  apply graphHilbert90Gauge_cross_of_graphNorm_eq6401
    sigma q6401
      (primitiveBivariateFailureLaneZero6401 W)
      (primitiveBivariateFailureLaneOne6401 W) t (horder t)
  exact sub_eq_zero.mp hnorm
theorem allSeedsZero_or_nonzeroPrimitiveFamilyGraphGauge6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (horder : ∀ x,
      sigma (sigma (sigma (sigma (sigma (sigma x))))) = x)
    (hnorm : primitiveFamilyNormObstruction6401 W = 0) :
    (∀ t : F, primitiveFamilyGraphGaugeNumerator6401 W t = 0) ∨
      ∃ t : F,
        primitiveFamilyGraphGaugeNumerator6401 W t ≠ 0 ∧
        primitiveBivariateFailureLaneZero6401 W *
              graphTwist6401 sigma q6401
                (primitiveFamilyGraphGaugeNumerator6401 W t) *
              primitiveFamilyGraphGaugeDenominator6401 W =
          primitiveBivariateFailureLaneOne6401 W *
              primitiveFamilyGraphGaugeNumerator6401 W t *
              graphTwist6401 sigma q6401
                (primitiveFamilyGraphGaugeDenominator6401 W) := by
  by_cases hall : ∀ t : F, primitiveFamilyGraphGaugeNumerator6401 W t = 0
  · exact Or.inl hall
  · push Not at hall
    obtain ⟨t, ht⟩ := hall
    exact Or.inr ⟨t, ht,
      primitiveFamilyGraphGauge_cross6401 W horder hnorm t⟩
theorem primitiveFamilyGraphGaugeNumerator_ne_zero_of_anchor6401
    {F : Type} [Field F] [DecidableEq F]
    {sigma : F →+* F} {alpha : Fin n6401 ↪ F}
    {u0 u1 : Fin n6401 → F}
    {S : Finset F} {A : F → Finset (Fin n6401)}
    {P : F → Polynomial F}
    (W : PrimitivePuncturedOwnerWindow6401 sigma alpha u0 u1 S A P)
    (hsigma : ∀ z : F, sigma z = z ^ q6401)
    (hfixed : ∀ i, sigma (alpha i) = alpha i)
    (z : F) (hz : z ∈ rowTwoGoodChallenges6401 W.commonDirection S)
    (i : W.PuncturedIndex)
    (herror : W.puncturedOwnerError z i ≠ 0)
    (hsix : (6 : F) ≠ 0)
    (hcoprime : IsCoprime
      (specializeCoeffZ z (primitiveBivariateFailureLaneZero6401 W))
      (specializeCoeffZ z (primitiveBivariateFailureLaneOne6401 W))) :
    primitiveFamilyGraphGaugeNumerator6401 W
      (W.puncturedOwnerError z i) ≠ 0 := by
  apply graphHilbert90Numerator_ne_zero_of_anchor6401 sigma q6401
    (primitiveBivariateFailureLaneZero6401 W)
    (primitiveBivariateFailureLaneOne6401 W) z (hsigma z)
    (W.puncturedAlpha i) (W.puncturedOwnerError z i)
      (hfixed i.1) hcoprime herror hsix
  simpa [primitiveBivariateFailureLaneZero6401,
    primitiveBivariateFailureLaneOne6401, specializeRow,
    specializeCoeffZ_apply] using
      W.puncturedTwoLaneFailureRelation hsigma hfixed z hz i
theorem exists_nonzeroPrimitiveFamilyGraphGauge_of_anchor6401
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
    (hnorm : primitiveFamilyNormObstruction6401 W = 0)
    (z : F) (hz : z ∈ rowTwoGoodChallenges6401 W.commonDirection S)
    (i : W.PuncturedIndex)
    (herror : W.puncturedOwnerError z i ≠ 0)
    (hsix : (6 : F) ≠ 0)
    (hcoprime : IsCoprime
      (specializeCoeffZ z (primitiveBivariateFailureLaneZero6401 W))
      (specializeCoeffZ z (primitiveBivariateFailureLaneOne6401 W))) :
    ∃ t : F,
      primitiveFamilyGraphGaugeNumerator6401 W t ≠ 0 ∧
      primitiveBivariateFailureLaneZero6401 W *
            graphTwist6401 sigma q6401
              (primitiveFamilyGraphGaugeNumerator6401 W t) *
            primitiveFamilyGraphGaugeDenominator6401 W =
        primitiveBivariateFailureLaneOne6401 W *
            primitiveFamilyGraphGaugeNumerator6401 W t *
            graphTwist6401 sigma q6401
              (primitiveFamilyGraphGaugeDenominator6401 W) := by
  refine ⟨W.puncturedOwnerError z i,
    primitiveFamilyGraphGaugeNumerator_ne_zero_of_anchor6401
      W hsigma hfixed z hz i herror hsix hcoprime, ?_⟩
  exact primitiveFamilyGraphGauge_cross6401 W horder hnorm _
theorem noncoprimeErrorAnchors_or_nonzeroPrimitiveFamilyGraphGauge6401
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
    (hnorm : primitiveFamilyNormObstruction6401 W = 0)
    (hsix : (6 : F) ≠ 0) :
    (∀ z : F, z ∈ rowTwoGoodChallenges6401 W.commonDirection S →
      ∀ i : W.PuncturedIndex, W.puncturedOwnerError z i ≠ 0 →
        ¬ IsCoprime
          (specializeCoeffZ z (primitiveBivariateFailureLaneZero6401 W))
          (specializeCoeffZ z (primitiveBivariateFailureLaneOne6401 W))) ∨
      ∃ t : F,
        primitiveFamilyGraphGaugeNumerator6401 W t ≠ 0 ∧
        primitiveBivariateFailureLaneZero6401 W *
              graphTwist6401 sigma q6401
                (primitiveFamilyGraphGaugeNumerator6401 W t) *
              primitiveFamilyGraphGaugeDenominator6401 W =
          primitiveBivariateFailureLaneOne6401 W *
              primitiveFamilyGraphGaugeNumerator6401 W t *
              graphTwist6401 sigma q6401
                (primitiveFamilyGraphGaugeDenominator6401 W) := by
  classical
  by_cases hanchor : ∃ z : F,
      z ∈ rowTwoGoodChallenges6401 W.commonDirection S ∧
      ∃ i : W.PuncturedIndex,
        W.puncturedOwnerError z i ≠ 0 ∧
        IsCoprime
          (specializeCoeffZ z (primitiveBivariateFailureLaneZero6401 W))
          (specializeCoeffZ z (primitiveBivariateFailureLaneOne6401 W))
  · rcases hanchor with ⟨z, hz, i, herror, hcoprime⟩
    exact Or.inr (exists_nonzeroPrimitiveFamilyGraphGauge_of_anchor6401
      W hsigma hfixed horder hnorm z hz i herror hsix hcoprime)
  · left
    intro z hz i herror hcoprime
    exact hanchor ⟨z, hz, i, herror, hcoprime⟩
theorem constantSignPair_graphNorm_eq6401 :
    graphFrobeniusNormSix6401 (RingHom.id ℚ) q6401
        (1 : ℚ[X][X]) =
      graphFrobeniusNormSix6401 (RingHom.id ℚ) q6401
        (-1 : ℚ[X][X]) := by
  simp [graphFrobeniusNormSix6401, graphTwist6401,
    graphTwistTwo6401, graphTwistThree6401, graphTwistFour6401,
    graphTwistFive6401, challengeFrobeniusRingHom6401]
  norm_num
theorem constantSignPair_all_graphNumerator_seeds_zero6401 (t : ℚ) :
    graphHilbert90Numerator6401 (RingHom.id ℚ) q6401
      (1 : ℚ[X][X]) (-1 : ℚ[X][X]) t = 0 := by
  simp [graphHilbert90Numerator6401, graphHilbert90Denominator6401,
    graphTwist6401, graphTwistTwo6401, graphTwistThree6401,
    graphTwistFour6401, challengeFrobeniusRingHom6401]
  ring
def arbitrarySupportError6401
    {F I : Type*} [Field F] [DecidableEq I] (T : Finset I) : I → F :=
  fun i => if i ∈ T then 1 else 0
theorem arbitrarySupportError_ne_zero_iff6401
    {F I : Type*} [Field F] [DecidableEq I]
    (T : Finset I) (i : I) :
    arbitrarySupportError6401 (F := F) T i ≠ 0 ↔ i ∈ T := by
  by_cases hi : i ∈ T <;> simp [arbitrarySupportError6401, hi]
theorem unitPair_arbitrarySupport_failureRelation6401
    {F I : Type*} [Field F] [DecidableEq I]
    (sigma : F →+* F) (alpha : I → F) (T : Finset I) :
    TwoLaneFailureRelation sigma alpha
      (arbitrarySupportError6401 (F := F) T)
      (1 : F[X]) (1 : F[X]) := by
  intro i
  by_cases hi : i ∈ T <;>
    simp [arbitrarySupportError6401, hi]
theorem unitPair_graphNumerator_one_ne_zero6401
    {F : Type} [Field F] [DecidableEq F]
    (sigma : F →+* F) (q : Nat) (hsix : (6 : F) ≠ 0) :
    graphHilbert90Numerator6401 sigma q
      (1 : F[X][X]) (1 : F[X][X]) 1 ≠ 0 := by
  have hvalue : graphHilbert90Numerator6401 sigma q
      (1 : F[X][X]) (1 : F[X][X]) 1 =
        (6 : F[X][X]) := by
    simp [graphHilbert90Numerator6401, graphHilbert90Denominator6401,
      graphTwist6401, graphTwistTwo6401, graphTwistThree6401,
      graphTwistFour6401, challengeFrobeniusRingHom6401]
    ring
  rw [hvalue]
  intro hzero
  apply hsix
  have hcoeff := congrArg
    (fun P : F[X][X] => Polynomial.coeff (Polynomial.coeff P 0) 0) hzero
  simpa using hcoeff
theorem unitPair_commonGauge_arbitrarySupport_counterprofile6401
    {F I : Type} [Field F] [DecidableEq F] [DecidableEq I]
    (sigma : F →+* F) (q : Nat) (hsix : (6 : F) ≠ 0)
    (alpha : I → F) (T : Finset I) :
    graphFrobeniusNormSix6401 sigma q (1 : F[X][X]) =
        graphFrobeniusNormSix6401 sigma q (1 : F[X][X]) ∧
      graphHilbert90Numerator6401 sigma q
        (1 : F[X][X]) (1 : F[X][X]) 1 ≠ 0 ∧
      TwoLaneFailureRelation sigma alpha
        (arbitrarySupportError6401 (F := F) T)
        (1 : F[X]) (1 : F[X]) ∧
      ∀ i, arbitrarySupportError6401 (F := F) T i ≠ 0 ↔ i ∈ T := by
  exact ⟨rfl, unitPair_graphNumerator_one_ne_zero6401 sigma q hsix,
    unitPair_arbitrarySupport_failureRelation6401 sigma alpha T,
    arbitrarySupportError_ne_zero_iff6401 T⟩
end BCHKSExtremePrimitiveGraphGaugeFork6401
end ProximityPrize.SubmissionLower
