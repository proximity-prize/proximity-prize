import ProximityPrize.SubmissionLower.BCHKSTransformedUniversalTag6400
import ProximityPrize.SubmissionLower.BCHKSCoreTransformFiberSetup6400
import ProximityPrize.SubmissionLower.BCHKSPrimitiveSpecialization
namespace ProximityPrize.SubmissionLower
namespace BCHKSCoreTransformedUniversalTag6400
open Polynomial Polynomial.Bivariate
open BCHKSCoreQuotientHenselAudit6400
open BCHKSCoreTransformFiberSetup6400
open BCHKSTransformedUniversalTag6400
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
theorem ySlope_triSpecializeZ_eq_eval_biSpecializeZ_derivative
    {F : Type} [Field F]
    (T : F[X][X][Y]) (x z y : F) :
    FiniteHensel.ySlope (triSpecializeZ T z) x y =
      Polynomial.eval y
        (biSpecializeZ (triSpecializeX T.derivative x) z) := by
  simp only [FiniteHensel.ySlope, triSpecializeZ, triSpecializeX,
    biSpecializeZ, Polynomial.derivative_map]
  induction Polynomial.derivative T using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
      simp [eval_map_eval_eq_eval_eval_C]
theorem biSpecializeZ_triSpecializeX_ne_zero_of_isSimpleRootAt
    {F : Type} [Field F]
    (T : F[X][X][Y]) (x z y : F)
    (hsimple : FiniteHensel.IsSimpleRootAt (triSpecializeZ T z) x y) :
    biSpecializeZ (triSpecializeX T x) z ≠ 0 := by
  intro hzero
  apply hsimple.2
  rw [ySlope_triSpecializeZ_eq_eval_biSpecializeZ_derivative]
  have hder : triSpecializeX T.derivative x =
      (triSpecializeX T x).derivative := by
    simp [triSpecializeX, Polynomial.derivative_map]
  rw [hder]
  have hzder :
      biSpecializeZ (triSpecializeX T x).derivative z = 0 := by
    simpa [biSpecializeZ, Polynomial.derivative_map] using
      congrArg Polynomial.derivative hzero
  rw [hzder]
  simp
theorem exists_primitive_locatorGood_center
    {F : Type} [Field F] [Fintype F]
    (R : F[X][X][Y]) (G : F[X])
    (w : EffectivePrimitiveObstruction F R)
    (hG0 : G ≠ 0)
    (hdegree : w.obstruction.natDegree + G.natDegree < Fintype.card F) :
    ∃ x0 : F, G.eval x0 ≠ 0 ∧ (triSpecializeX R x0).IsPrimitive := by
  classical
  let obstruction : F[X] := w.obstruction * G
  have hobstruction : obstruction ≠ 0 :=
    mul_ne_zero w.ne hG0
  have hmuldegree : obstruction.natDegree ≤
      w.obstruction.natDegree + G.natDegree := by
    simpa [obstruction] using
      (Polynomial.natDegree_mul_le :
        (w.obstruction * G).natDegree ≤
          w.obstruction.natDegree + G.natDegree)
  have hdegree' : obstruction.natDegree < Fintype.card F :=
    hmuldegree.trans_lt hdegree
  have hex : ∃ x0 : F, obstruction.eval x0 ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hobstruction
    exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      obstruction Function.injective_id hnone hdegree'
  obtain ⟨x0, hx0⟩ := hex
  have hw : w.obstruction.eval x0 ≠ 0 := by
    intro hw
    apply hx0
    simp [obstruction, hw]
  have hGx : G.eval x0 ≠ 0 := by
    intro hGx
    apply hx0
    simp [obstruction, hGx]
  exact ⟨x0, hGx, w.property x0 hw⟩
noncomputable def coreTransformedUniversalTag
    {F : Type} [Field F]
    (R : F[X][X][Y]) (P Q : F → F[X])
    (B0 B1 G : F[X]) (x0 : F) (s : Nat)
    (owns : F → Prop)
    (hG0 : G ≠ 0) (hGx : G.eval x0 ≠ 0)
    (hprimitive : (triSpecializeX R x0).IsPrimitive)
    (hQdegree : ∀ z, owns z → (Q z).natDegree ≤ s)
    (hshape : ∀ z, owns z →
      P z = B0 + Polynomial.C z * B1 + G * Q z)
    (hroot : ∀ z, owns z → triEval R z (P z) = 0)
    (hsimple : ∀ z, owns z →
      FiniteHensel.IsSimpleRootAt (triSpecializeZ R z) x0
        ((P z).eval x0))
    (hB0 : B0.natDegree ≤ 131071)
    (hB1 : B1.natDegree ≤ 131071)
    (hGdegree : G.natDegree + s ≤ 131071) :
    TransformedUniversalTag F := {
  source := R
  transformed := coreRootTransform R B0 B1 G
  center := x0
  owns := owns
  root := Q
  rootDegreeCap := s
  primitive := triSpecializeX_coreRootTransform_isPrimitive
    R B0 B1 G x0 hprimitive hGx
  specializeDegree_le_source := by
    rw [triSpecializeX_coreRootTransform_natDegree R B0 B1 G x0 hGx]
    unfold triSpecializeX
    exact Polynomial.natDegree_map_le
  root_degree_le := hQdegree
  exact_root := by
    intro z hz
    rw [triEval_coreRootTransform]
    simpa [hshape z hz] using hroot z hz
  simple_root := by
    intro z hz
    apply coreRootTransform_isSimpleRootAt R B0 B1 G (Q z) x0 z hGx
    simpa [hshape z hz] using hsimple z hz
  second_ne_zero := by
    intro z hz
    exact biSpecializeZ_triSpecializeX_ne_zero_of_isSimpleRootAt
      (coreRootTransform R B0 B1 G) x0 z ((Q z).eval x0)
      (coreRootTransform_isSimpleRootAt R B0 B1 G (Q z) x0 z hGx
        (by simpa [hshape z hz] using hsimple z hz))
  outerDegree_preserved := coreRootTransform_natDegree R B0 B1 G hG0
  yzSupportDegree_le_source :=
    coreRootTransform_yzSupportDegree_le R B0 B1 G hG0
  weightedSupportDegree_le_source :=
    coreRootTransform_weightedSupportDegree_le
      R B0 B1 G s 131071 hB0 hB1 hGdegree hG0
}
theorem exists_coreTransformedUniversalTag_of_obstruction
    {F : Type} [Field F] [Fintype F]
    (R : F[X][X][Y]) (P Q : F → F[X])
    (B0 B1 G : F[X]) (s : Nat)
    (owns : F → F → Prop)
    (w : EffectivePrimitiveObstruction F R)
    (hG0 : G ≠ 0)
    (hcenterDegree :
      w.obstruction.natDegree + G.natDegree < Fintype.card F)
    (hQdegree : ∀ x z, owns x z → (Q z).natDegree ≤ s)
    (hshape : ∀ x z, owns x z →
      P z = B0 + Polynomial.C z * B1 + G * Q z)
    (hroot : ∀ x z, owns x z → triEval R z (P z) = 0)
    (hsimple : ∀ x z, owns x z →
      FiniteHensel.IsSimpleRootAt (triSpecializeZ R z) x
        ((P z).eval x))
    (hB0 : B0.natDegree ≤ 131071)
    (hB1 : B1.natDegree ≤ 131071)
    (hGdegree : G.natDegree + s ≤ 131071) :
    ∃ x0 : F, G.eval x0 ≠ 0 ∧
      ∃ tag : TransformedUniversalTag F,
        tag.source = R ∧
        tag.transformed = coreRootTransform R B0 B1 G ∧
        tag.center = x0 ∧ tag.owns = owns x0 ∧
        tag.root = Q ∧ tag.rootDegreeCap = s := by
  obtain ⟨x0, hGx, hprimitive⟩ :=
    exists_primitive_locatorGood_center R G w hG0 hcenterDegree
  let tag := coreTransformedUniversalTag R P Q B0 B1 G x0 s (owns x0)
    hG0 hGx hprimitive
    (fun z hz => hQdegree x0 z hz)
    (fun z hz => hshape x0 z hz)
    (fun z hz => hroot x0 z hz)
    (fun z hz => hsimple x0 z hz)
    hB0 hB1 hGdegree
  exact ⟨x0, hGx, tag, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem coreTransformedUniversalTag_exact_root
    {F : Type} [Field F]
    (R : F[X][X][Y]) (P Q : F → F[X])
    (B0 B1 G : F[X]) (x0 : F) (s : Nat)
    (owns : F → Prop)
    (hG0 : G ≠ 0) (hGx : G.eval x0 ≠ 0)
    (hprimitive : (triSpecializeX R x0).IsPrimitive)
    (hQdegree : ∀ z, owns z → (Q z).natDegree ≤ s)
    (hshape : ∀ z, owns z →
      P z = B0 + Polynomial.C z * B1 + G * Q z)
    (hroot : ∀ z, owns z → triEval R z (P z) = 0)
    (hsimple : ∀ z, owns z →
      FiniteHensel.IsSimpleRootAt (triSpecializeZ R z) x0
        ((P z).eval x0))
    (hB0 : B0.natDegree ≤ 131071)
    (hB1 : B1.natDegree ≤ 131071)
    (hGdegree : G.natDegree + s ≤ 131071)
    (z : F) (hz : owns z) :
    triEval
      (coreTransformedUniversalTag R P Q B0 B1 G x0 s owns hG0 hGx
        hprimitive hQdegree hshape hroot hsimple hB0 hB1 hGdegree).transformed
      z (Q z) = 0 :=
  (coreTransformedUniversalTag R P Q B0 B1 G x0 s owns hG0 hGx
    hprimitive hQdegree hshape hroot hsimple hB0 hB1 hGdegree).exact_root z hz
structure CoreTransformedTagInput
    (F : Type) [Field F] [Fintype F] where
  source : F[X][X][Y]
  originalRoot : F → F[X]
  quotientRoot : F → F[X]
  base0 : F[X]
  base1 : F[X]
  locator : F[X]
  rootDegreeCap : Nat
  owns : F → F → Prop
  primitiveObstruction : EffectivePrimitiveObstruction F source
  locator_ne_zero : locator ≠ 0
  centerDegree_lt_card :
    primitiveObstruction.obstruction.natDegree + locator.natDegree <
      Fintype.card F
  quotient_degree_le : ∀ x z, owns x z →
    (quotientRoot z).natDegree ≤ rootDegreeCap
  quotient_shape : ∀ x z, owns x z →
    originalRoot z = base0 + Polynomial.C z * base1 +
      locator * quotientRoot z
  original_exact_root : ∀ x z, owns x z →
    triEval source z (originalRoot z) = 0
  original_simple_root : ∀ x z, owns x z →
    FiniteHensel.IsSimpleRootAt (triSpecializeZ source z) x
      ((originalRoot z).eval x)
  base0_degree_le : base0.natDegree ≤ 131071
  base1_degree_le : base1.natDegree ≤ 131071
  locator_degree_add_cap : locator.natDegree + rootDegreeCap ≤ 131071
noncomputable def CoreTransformedTagInput.center
    {F : Type} [Field F] [Fintype F]
    (D : CoreTransformedTagInput F) : F :=
  Classical.choose (exists_primitive_locatorGood_center
    D.source D.locator D.primitiveObstruction D.locator_ne_zero
      D.centerDegree_lt_card)
theorem CoreTransformedTagInput.center_locator_ne_zero
    {F : Type} [Field F] [Fintype F]
    (D : CoreTransformedTagInput F) :
    D.locator.eval D.center ≠ 0 :=
  (Classical.choose_spec (exists_primitive_locatorGood_center
    D.source D.locator D.primitiveObstruction D.locator_ne_zero
      D.centerDegree_lt_card)).1
theorem CoreTransformedTagInput.center_primitive
    {F : Type} [Field F] [Fintype F]
    (D : CoreTransformedTagInput F) :
    (triSpecializeX D.source D.center).IsPrimitive :=
  (Classical.choose_spec (exists_primitive_locatorGood_center
    D.source D.locator D.primitiveObstruction D.locator_ne_zero
      D.centerDegree_lt_card)).2
noncomputable def CoreTransformedTagInput.toTag
    {F : Type} [Field F] [Fintype F]
    (D : CoreTransformedTagInput F) : TransformedUniversalTag F :=
  coreTransformedUniversalTag
    D.source D.originalRoot D.quotientRoot D.base0 D.base1 D.locator
    D.center D.rootDegreeCap (D.owns D.center)
    D.locator_ne_zero D.center_locator_ne_zero D.center_primitive
    (fun z hz => D.quotient_degree_le D.center z hz)
    (fun z hz => D.quotient_shape D.center z hz)
    (fun z hz => D.original_exact_root D.center z hz)
    (fun z hz => D.original_simple_root D.center z hz)
    D.base0_degree_le D.base1_degree_le D.locator_degree_add_cap
@[simp]
theorem CoreTransformedTagInput.toTag_source
    {F : Type} [Field F] [Fintype F]
    (D : CoreTransformedTagInput F) : D.toTag.source = D.source := rfl
@[simp]
theorem CoreTransformedTagInput.toTag_transformed
    {F : Type} [Field F] [Fintype F]
    (D : CoreTransformedTagInput F) :
    D.toTag.transformed =
      coreRootTransform D.source D.base0 D.base1 D.locator := rfl
@[simp]
theorem CoreTransformedTagInput.toTag_center
    {F : Type} [Field F] [Fintype F]
    (D : CoreTransformedTagInput F) : D.toTag.center = D.center := rfl
@[simp]
theorem CoreTransformedTagInput.toTag_owns
    {F : Type} [Field F] [Fintype F]
    (D : CoreTransformedTagInput F) : D.toTag.owns = D.owns D.center := rfl
@[simp]
theorem CoreTransformedTagInput.toTag_root
    {F : Type} [Field F] [Fintype F]
    (D : CoreTransformedTagInput F) :
    D.toTag.root = D.quotientRoot := rfl
@[simp]
theorem CoreTransformedTagInput.toTag_rootDegreeCap
    {F : Type} [Field F] [Fintype F]
    (D : CoreTransformedTagInput F) :
    D.toTag.rootDegreeCap = D.rootDegreeCap := rfl
theorem corePositiveInnerFactorPairs_card_le_sum_sourceDegree
    {F A : Type} [Field F] [Fintype F] [DecidableEq F]
    [NormalizationMonoid F] [DecidableEq A]
    (Outer : Finset A) (input : A → CoreTransformedTagInput F) :
    (positiveInnerFactorPairs Outer (fun a => (input a).toTag)).card ≤
      ∑ a ∈ Outer, (input a).source.natDegree := by
  simpa using positiveInnerFactorPairs_card_le_sum_sourceDegree
    Outer (fun a => (input a).toTag)
theorem exists_corePositiveInnerFactorPair
    {F A : Type} [Field F] [Fintype F] [DecidableEq F]
    [NormalizationMonoid F] [DecidableEq A]
    (Outer : Finset A) (input : A → CoreTransformedTagInput F)
    (z : F)
    (hcover : ∃ a ∈ Outer, (input a).owns (input a).center z) :
    ∃ p ∈ positiveInnerFactorPairs Outer (fun a => (input a).toTag),
      pairRel (fun a => (input a).toTag) z p := by
  apply exists_positiveInnerFactorPair
  simpa using hcover
theorem coreTag_inner_hensel_setup
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [NormalizationMonoid F]
    (D : CoreTransformedTagInput F) (H : F[X][Y])
    (hH : H ∈ UniqueFactorizationMonoid.normalizedFactors
      (triSpecializeX D.toTag.transformed D.toTag.center))
    (hHpos : 0 < H.natDegree) :
    Irreducible H ∧ H ∣ triSpecializeX D.toTag.transformed D.toTag.center ∧
      RationalFunctions.HenselNumerators.Hypotheses
        D.toTag.center D.toTag.transformed H :=
  tag_inner_hensel_setup D.toTag H hH hHpos
end BCHKSCoreTransformedUniversalTag6400
end ProximityPrize.SubmissionLower
