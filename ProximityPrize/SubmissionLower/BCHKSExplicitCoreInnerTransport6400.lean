import ProximityPrize.SubmissionLower.BCHKSCanonicalGammaCoreQuotient6400
import ProximityPrize.SubmissionLower.BCHKSCoreTransformFiberSetup6400
import ProximityPrize.SubmissionLower.BCHKSTransformedUniversalTag6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSExplicitCoreInnerTransport6400
open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators
open BCHKSCoreQuotientHenselAudit6400
open BCHKSCoreTransformFiberSetup6400
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
noncomputable def coreFiberAffine
    {F : Type} [Field F]
    (B0 B1 G : F[X]) (x0 : F) : F[X][Y] :=
  Polynomial.C (Polynomial.C (G.eval x0)) * Polynomial.X +
    Polynomial.C
      (Polynomial.C (B0.eval x0) +
        Polynomial.X * Polynomial.C (B1.eval x0))
noncomputable def transportedInnerFactor
    {F : Type} [Field F]
    (H : F[X][Y]) (B0 B1 G : F[X]) (x0 : F) : F[X][Y] :=
  H.comp (coreFiberAffine B0 B1 G x0)
theorem coreFiberAffine_eq
    {F : Type} [Field F]
    (B0 B1 G : F[X]) (x0 : F) :
    coreFiberAffine B0 B1 G x0 =
      Polynomial.C
          (Polynomial.C (B0.eval x0) +
            Polynomial.X * Polynomial.C (B1.eval x0)) +
        Polynomial.C (Polynomial.C (G.eval x0)) * Polynomial.X := by
  simp [coreFiberAffine, add_comm]
theorem coreFiberAffine_natDegree
    {F : Type} [Field F]
    (B0 B1 G : F[X]) (x0 : F) (hGx : G.eval x0 ≠ 0) :
    (coreFiberAffine B0 B1 G x0).natDegree = 1 := by
  unfold coreFiberAffine
  apply Polynomial.natDegree_linear
  simpa using hGx
theorem Polynomial.irreducible_comp_C_mul_X_add_C
    {A : Type*} [CommRing A]
    {p : A[X]} (hp : Irreducible p) (a b : A) [Invertible a] :
    Irreducible (p.comp (Polynomial.C a * Polynomial.X + Polynomial.C b)) := by
  let e : A[X] ≃ₐ[A] A[X] := Polynomial.algEquivCMulXAddC a b
  have he : e p =
      p.comp (Polynomial.C a * Polynomial.X + Polynomial.C b) := by
    simp [e, ← Polynomial.comp_eq_aeval]
  rw [← he]
  exact (MulEquiv.irreducible_iff (f := (e : A[X] ≃* A[X])) (x := p)).2 hp
theorem transportedInnerFactor_irreducible
    {F : Type} [Field F]
    (H : F[X][Y]) (B0 B1 G : F[X]) (x0 : F)
    (hH : Irreducible H) (hGx : G.eval x0 ≠ 0) :
    Irreducible (transportedInnerFactor H B0 B1 G x0) := by
  let a : F[X] := Polynomial.C (G.eval x0)
  let b : F[X] :=
    Polynomial.C (B0.eval x0) +
      Polynomial.X * Polynomial.C (B1.eval x0)
  have ha : IsUnit a := Polynomial.isUnit_C.mpr hGx.isUnit
  letI : Invertible a := ha.invertible
  simpa [transportedInnerFactor, coreFiberAffine, a, b] using
    Polynomial.irreducible_comp_C_mul_X_add_C hH a b
theorem transportedInnerFactor_natDegree
    {F : Type} [Field F]
    (H : F[X][Y]) (B0 B1 G : F[X]) (x0 : F)
    (hGx : G.eval x0 ≠ 0) :
    (transportedInnerFactor H B0 B1 G x0).natDegree = H.natDegree := by
  rw [transportedInnerFactor, Polynomial.natDegree_comp,
    coreFiberAffine_natDegree B0 B1 G x0 hGx, Nat.mul_one]
theorem transportedInnerFactor_leadingCoeff
    {F : Type} [Field F]
    (H : F[X][Y]) (B0 B1 G : F[X]) (x0 : F)
    (hGx : G.eval x0 ≠ 0) :
    (transportedInnerFactor H B0 B1 G x0).leadingCoeff =
      H.leadingCoeff * Polynomial.C (G.eval x0) ^ H.natDegree := by
  have ha : Polynomial.C (G.eval x0) ≠ (0 : F[X]) := by
    simpa using hGx
  rw [transportedInnerFactor, Polynomial.leadingCoeff_comp]
  · unfold coreFiberAffine
    rw [Polynomial.leadingCoeff_linear ha]
  · rw [coreFiberAffine_natDegree B0 B1 G x0 hGx]
    omega
theorem transportedInnerFactor_leadingCoeff_eval
    {F : Type} [Field F]
    (H : F[X][Y]) (B0 B1 G : F[X]) (x0 z : F)
    (hGx : G.eval x0 ≠ 0) :
    (transportedInnerFactor H B0 B1 G x0).leadingCoeff.eval z =
      H.leadingCoeff.eval z * (G.eval x0) ^ H.natDegree := by
  rw [transportedInnerFactor_leadingCoeff H B0 B1 G x0 hGx]
  simp
theorem transportedInnerFactor_leadingCoeff_eval_ne_zero
    {F : Type} [Field F]
    (H : F[X][Y]) (B0 B1 G : F[X]) (x0 z : F)
    (hGx : G.eval x0 ≠ 0)
    (hHlead : H.leadingCoeff.eval z ≠ 0) :
    (transportedInnerFactor H B0 B1 G x0).leadingCoeff.eval z ≠ 0 := by
  rw [transportedInnerFactor_leadingCoeff_eval H B0 B1 G x0 z hGx]
  exact mul_ne_zero hHlead (pow_ne_zero _ hGx)
theorem transportedInnerFactor_dvd_transformedFiber
    {F : Type} [Field F]
    (R : F[X][X][Y]) (H : F[X][Y])
    (B0 B1 G : F[X]) (x0 : F)
    (hHdvd : H ∣ triSpecializeX R x0) :
    transportedInnerFactor H B0 B1 G x0 ∣
      triSpecializeX (coreRootTransform R B0 B1 G) x0 := by
  obtain ⟨Q, hQ⟩ := hHdvd
  refine ⟨Q.comp (coreFiberAffine B0 B1 G x0), ?_⟩
  rw [triSpecializeX_coreRootTransform, hQ, Polynomial.mul_comp]
  simp only [transportedInnerFactor, coreFiberAffine_eq]
theorem henselHypotheses_of_primitive_factor
    {F : Type} [Field F]
    (T : F[X][X][Y]) (x0 : F) (H : F[X][Y])
    (hprimitive : (triSpecializeX T x0).IsPrimitive)
    (hHdvd : H ∣ triSpecializeX T x0) :
    HenselNumerators.Hypotheses x0 T H := by
  have hTX : triSpecializeX T x0 =
      Polynomial.Bivariate.evalX (Polynomial.C x0) T := by
    simp [triSpecializeX, Polynomial.Bivariate.evalX_eq_map]
  refine ⟨?_, ?_, ?_⟩
  · simpa [← hTX] using hHdvd
  · simpa [← hTX] using hprimitive.ne_zero
  · intro Q hfac hQdeg
    let q0 : F[X] := Q.coeff 0
    have hQC : Q = Polynomial.C q0 :=
      Polynomial.eq_C_of_natDegree_le_zero hQdeg.le
    apply (Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hprimitive) q0
    refine ⟨H, ?_⟩
    calc
      triSpecializeX T x0 = H * Q := by
        simpa [hTX] using hfac
      _ = H * Polynomial.C q0 := by rw [hQC]
      _ = Polynomial.C q0 * H := mul_comm _ _
theorem transportedInnerFactor_henselSetup
    {F : Type} [Field F]
    (R : F[X][X][Y]) (H : F[X][Y])
    (B0 B1 G : F[X]) (x0 : F)
    (hH : Irreducible H) (hHpos : 0 < H.natDegree)
    (hHdvd : H ∣ triSpecializeX R x0)
    (hprimitive : (triSpecializeX R x0).IsPrimitive)
    (hGx : G.eval x0 ≠ 0) :
    Irreducible (transportedInnerFactor H B0 B1 G x0) ∧
      0 < (transportedInnerFactor H B0 B1 G x0).natDegree ∧
      transportedInnerFactor H B0 B1 G x0 ∣
        triSpecializeX (coreRootTransform R B0 B1 G) x0 ∧
      HenselNumerators.Hypotheses x0
        (coreRootTransform R B0 B1 G)
        (transportedInnerFactor H B0 B1 G x0) := by
  have hprimitive' := triSpecializeX_coreRootTransform_isPrimitive
    R B0 B1 G x0 hprimitive hGx
  have hirr := transportedInnerFactor_irreducible
    H B0 B1 G x0 hH hGx
  have hpos : 0 < (transportedInnerFactor H B0 B1 G x0).natDegree := by
    rw [transportedInnerFactor_natDegree H B0 B1 G x0 hGx]
    exact hHpos
  have hdvd := transportedInnerFactor_dvd_transformedFiber
    R H B0 B1 G x0 hHdvd
  exact ⟨hirr, hpos, hdvd,
    henselHypotheses_of_primitive_factor
      (coreRootTransform R B0 B1 G) x0
      (transportedInnerFactor H B0 B1 G x0) hprimitive' hdvd⟩
theorem biEval_transportedInnerFactor
    {F : Type} [Field F]
    (H : F[X][Y]) (B0 B1 G Q : F[X]) (x0 z : F) :
    biEval (transportedInnerFactor H B0 B1 G x0) (Q.eval x0) z =
      biEval H
        ((B0 + Polynomial.C z * B1 + G * Q).eval x0) z := by
  unfold transportedInnerFactor biEval
  rw [Polynomial.map_comp, Polynomial.eval_comp]
  simp [coreFiberAffine, Polynomial.eval_add, Polynomial.eval_mul]
  ring_nf
theorem biEval_transportedInnerFactor_eq_zero_of_owner
    {F : Type} [Field F]
    (H : F[X][Y]) (B0 B1 G P Q : F[X]) (x0 z : F)
    (hshape : P = B0 + Polynomial.C z * B1 + G * Q)
    (hroot : biEval H (P.eval x0) z = 0) :
    biEval (transportedInnerFactor H B0 B1 G x0) (Q.eval x0) z = 0 := by
  rw [biEval_transportedInnerFactor]
  simpa [hshape] using hroot
theorem transported_owner_predicates
    {F : Type} [Field F]
    (R : F[X][X][Y]) (H : F[X][Y])
    (B0 B1 G P Q : F[X]) (x0 z : F)
    (hGx : G.eval x0 ≠ 0)
    (hshape : P = B0 + Polynomial.C z * B1 + G * Q)
    (hHroot : biEval H (P.eval x0) z = 0)
    (hHlead : H.leadingCoeff.eval z ≠ 0)
    (hsimple : FiniteHensel.IsSimpleRootAt
      (triSpecializeZ R z) x0 (P.eval x0)) :
    biEval (transportedInnerFactor H B0 B1 G x0) (Q.eval x0) z = 0 ∧
      (transportedInnerFactor H B0 B1 G x0).leadingCoeff.eval z ≠ 0 ∧
      FiniteHensel.IsSimpleRootAt
        (triSpecializeZ (coreRootTransform R B0 B1 G) z)
        x0 (Q.eval x0) := by
  refine ⟨biEval_transportedInnerFactor_eq_zero_of_owner
      H B0 B1 G P Q x0 z hshape hHroot,
    transportedInnerFactor_leadingCoeff_eval_ne_zero
      H B0 B1 G x0 z hGx hHlead, ?_⟩
  apply coreRootTransform_isSimpleRootAt R B0 B1 G Q x0 z hGx
  simpa [hshape] using hsimple
theorem coreRootTransform_YZCap
    {F : Type} [Field F]
    (R : F[X][X][Y]) (B0 B1 G : F[X]) (D : ℕ)
    (hG0 : G ≠ 0) (hYZ : YZCap R D) :
    YZCap (coreRootTransform R B0 B1 G) D := by
  have hsourceSupport : YZFactorCap.yzSupportDegree R 1 ≤ D :=
    BCHKSHybridHighDegreeAudit6400.yzSupportDegree_le_of_YZCap R D hYZ
  have htransformSupport :
      YZFactorCap.yzSupportDegree (coreRootTransform R B0 B1 G) 1 ≤ D :=
    (coreRootTransform_yzSupportDegree_le R B0 B1 G hG0).trans
      hsourceSupport
  have hactual := BCHKSHybridHighDegreeAudit6400.YZCap_yzSupportDegree
    (coreRootTransform R B0 B1 G)
  intro j a ha
  exact (hactual j a ha).trans htransformSupport
theorem transportedInnerFactor_totalDegree_le
    {F : Type} [Field F]
    (R : F[X][X][Y]) (H : F[X][Y])
    (B0 B1 G : F[X]) (x0 : F) (D : ℕ)
    (hHpos : 0 < H.natDegree)
    (hHdvd : H ∣ triSpecializeX R x0)
    (hprimitive : (triSpecializeX R x0).IsPrimitive)
    (hG0 : G ≠ 0) (hGx : G.eval x0 ≠ 0)
    (hYZ : YZCap R D) :
    Polynomial.Bivariate.totalDegree
      (transportedInnerFactor H B0 B1 G x0) ≤ D := by
  let T := coreRootTransform R B0 B1 G
  let H' := transportedInnerFactor H B0 B1 G x0
  have hprimitiveT : (triSpecializeX T x0).IsPrimitive := by
    exact triSpecializeX_coreRootTransform_isPrimitive
      R B0 B1 G x0 hprimitive hGx
  have hTYZ : YZCap T D := by
    exact coreRootTransform_YZCap R B0 B1 G D hG0 hYZ
  have hfiberTotal :
      Polynomial.Bivariate.totalDegree (triSpecializeX T x0) ≤ D := by
    have hlt := totalDegree_triSpecializeX_lt T x0 (D + 1)
      (Nat.zero_lt_succ D) (by
        intro j a ha
        have hcap := hTYZ j a ha
        omega)
    omega
  have hH'dvd : H' ∣ triSpecializeX T x0 := by
    exact transportedInnerFactor_dvd_transformedFiber
      R H B0 B1 G x0 hHdvd
  have hH'pos : 0 < H'.natDegree := by
    dsimp [H']
    rw [transportedInnerFactor_natDegree H B0 B1 G x0 hGx]
    exact hHpos
  have hH'0 : H' ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hH'pos
  have hfiber0 : triSpecializeX T x0 ≠ 0 := hprimitiveT.ne_zero
  have hdivTotal : Polynomial.Bivariate.totalDegree H' ≤
      Polynomial.Bivariate.totalDegree (triSpecializeX T x0) := by
    obtain ⟨C, hC⟩ := hH'dvd
    have hC0 : C ≠ 0 := by
      intro hzero
      apply hfiber0
      rw [hC, hzero, mul_zero]
    rw [hC, Polynomial.Bivariate.totalDegree_mul hH'0 hC0]
    exact Nat.le_add_right _ _
  exact hdivTotal.trans hfiberTotal
theorem transported_denominatorExponent_eq
    (s : ℕ) :
    FiniteHenselWeight.denominatorExponent s = 2 * s - 1 := by
  simp [FiniteHenselWeight.denominatorExponent]
theorem betaRegular_at_order_sharpExponent
    {F : Type} [Field F]
    {T : F[X][X][Y]} {H' : F[X][Y]}
    [Fact (Irreducible H')] [Fact (0 < H'.natDegree)]
    (x0 : F) (hHyp : HenselNumerators.Hypotheses x0 T H')
    (hzeta : HenselNumerators.zeta T x0 H' ≠ 0)
    (s N : ℕ) (hsN : s ≤ N) :
    ∃ beta : 𝒪 H',
      embeddingOf𝒪Into𝕃 H' beta =
        betaField (R := T) (H := H') x0 hHyp N s ∧
      FiniteHenselWeight.denominatorExponent s = 2 * s - 1 := by
  refine ⟨betaRegular x0 T H' hHyp hzeta N s hsN,
    embedding_betaRegular x0 T H' hHyp hzeta N s hsN,
    transported_denominatorExponent_eq s⟩
theorem betaRegular_at_order_weight_sharpExponent
    {F : Type} [Field F]
    {T : F[X][X][Y]} {H' : F[X][Y]}
    [Fact (Irreducible H')] [Fact (0 < H'.natDegree)]
    (x0 : F) (hHyp : HenselNumerators.Hypotheses x0 T H')
    (hzeta : HenselNumerators.zeta T x0 H' ≠ 0)
    (D s N : ℕ)
    (hHtotal : Polynomial.Bivariate.totalDegree H' ≤ D)
    (hYZ : YZCap T D)
    (hTdeg : 2 ≤ Polynomial.Bivariate.natDegreeY T)
    (hsN : s ≤ N) :
    ∃ beta : 𝒪 H',
      embeddingOf𝒪Into𝕃 H' beta =
          betaField (R := T) (H := H') x0 hHyp N s ∧
      regularWeight (Fact.out : 0 < H'.natDegree) beta D ≤
          (WithBot.some (numeratorShapeSharp T H' D s) : WithBot ℕ) ∧
      FiniteHenselWeight.denominatorExponent s = 2 * s - 1 := by
  let beta := betaRegular x0 T H' hHyp hzeta N s hsN
  refine ⟨beta,
    embedding_betaRegular x0 T H' hHyp hzeta N s hsN, ?_,
    transported_denominatorExponent_eq s⟩
  exact betaRegular_weight_sharp_yz x0 T H' hHyp hzeta
    (Fact.out : 0 < H'.natDegree) hHtotal hYZ hTdeg N s hsN
theorem zeta_ne_zero_of_simple_factor_owner
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {T : F[X][X][Y]} {H' : F[X][Y]}
    [Fact (Irreducible H')] [Fact (0 < H'.natDegree)]
    (x0 z y : F)
    (hfactor : biEval H' y z = 0)
    (hHlead : H'.leadingCoeff.eval z ≠ 0)
    (hsimple : FiniteHensel.IsSimpleRootAt
      (triSpecializeZ T z) x0 y) :
    HenselNumerators.zeta T x0 H' ≠ 0 := by
  have hfactor' : Polynomial.evalEval z y H' = 0 := by
    exact (eval_map_eval_eq_eval_eval_C H' y z).symm.trans hfactor
  let root := rationalRootOfPair H' (Fact.out : 0 < H'.natDegree) z y hfactor'
  have hx : GoodAt z root (fieldTo𝕃 (H := H') x0) x0 :=
    GoodAt.fieldTo𝕃 (H := H') z root x0
  have hy : GoodAt z root (initialValue (H := H')) y := by
    have hT : GoodAt z root (functionFieldT (H := H'))
        (H'.leadingCoeff.eval z * y) := by
      refine ⟨Ideal.Quotient.mk (Ideal.span {monicize H'}) Polynomial.X,
        1, ?_, by simp, ?_⟩
      · simpa [embedding_mk_X_eq_functionFieldT]
      · simpa [root] using
          (piZ_mk_X_rationalRootOfPair H'
            (Fact.out : 0 < H'.natDegree) z y hfactor').symm
    have hWgood := GoodAt.liftToFunctionField
      (H := H') z root H'.leadingCoeff
    simpa [initialValue, mul_div_cancel_left₀ _ hHlead] using
      GoodAt.div hT hWgood hHlead
  exact zeta_ne_zero_of_selected_slope x0 T z root x0 y hx hy hsimple.2
end BCHKSExplicitCoreInnerTransport6400
end ProximityPrize.SubmissionLower
