import ProximityPrize.SubmissionLower.BCHKSCoreTransformedUniversalTag6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSMixedUniversalTag6400
open Polynomial Polynomial.Bivariate
open BCHKSTransformedUniversalTag6400
open BCHKSCoreTransformedUniversalTag6400
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
noncomputable def ordinaryUniversalTag
    {F : Type} [Field F]
    (R : F[X][X][Y]) (P : F → F[X]) (x0 : F)
    (owns : F → Prop)
    (hprimitive : (triSpecializeX R x0).IsPrimitive)
    (hPdegree : ∀ z, owns z → (P z).natDegree ≤ 131071)
    (hroot : ∀ z, owns z → triEval R z (P z) = 0)
    (hsimple : ∀ z, owns z →
      FiniteHensel.IsSimpleRootAt (triSpecializeZ R z) x0
        ((P z).eval x0)) :
    TransformedUniversalTag F := {
  source := R
  transformed := R
  center := x0
  owns := owns
  root := P
  rootDegreeCap := 131071
  primitive := hprimitive
  specializeDegree_le_source := by
    unfold triSpecializeX
    exact Polynomial.natDegree_map_le
  root_degree_le := hPdegree
  exact_root := hroot
  simple_root := hsimple
  second_ne_zero := by
    intro z hz
    exact biSpecializeZ_triSpecializeX_ne_zero_of_isSimpleRootAt
      R x0 z ((P z).eval x0) (hsimple z hz)
  outerDegree_preserved := rfl
  yzSupportDegree_le_source := le_rfl
  weightedSupportDegree_le_source := le_rfl
}
theorem exists_primitive_center_of_obstruction
    {F : Type} [Field F] [Fintype F]
    (R : F[X][X][Y]) (w : EffectivePrimitiveObstruction F R)
    (hdegree : w.obstruction.natDegree < Fintype.card F) :
    ∃ x0 : F, (triSpecializeX R x0).IsPrimitive := by
  obtain ⟨x0, _hone, hprimitive⟩ :=
    exists_primitive_locatorGood_center R (1 : F[X]) w one_ne_zero (by
      simpa using hdegree)
  exact ⟨x0, hprimitive⟩
structure OrdinaryTagInput
    (F : Type) [Field F] [Fintype F] where
  source : F[X][X][Y]
  root : F → F[X]
  owns : F → F → Prop
  primitiveObstruction : EffectivePrimitiveObstruction F source
  obstruction_degree_lt_card :
    primitiveObstruction.obstruction.natDegree < Fintype.card F
  root_degree_le : ∀ x z, owns x z → (root z).natDegree ≤ 131071
  exact_root : ∀ x z, owns x z → triEval source z (root z) = 0
  simple_root : ∀ x z, owns x z →
    FiniteHensel.IsSimpleRootAt (triSpecializeZ source z) x
      ((root z).eval x)
noncomputable def OrdinaryTagInput.center
    {F : Type} [Field F] [Fintype F]
    (D : OrdinaryTagInput F) : F :=
  Classical.choose (exists_primitive_center_of_obstruction
    D.source D.primitiveObstruction D.obstruction_degree_lt_card)
theorem OrdinaryTagInput.center_primitive
    {F : Type} [Field F] [Fintype F]
    (D : OrdinaryTagInput F) :
    (triSpecializeX D.source D.center).IsPrimitive :=
  Classical.choose_spec (exists_primitive_center_of_obstruction
    D.source D.primitiveObstruction D.obstruction_degree_lt_card)
noncomputable def OrdinaryTagInput.toTag
    {F : Type} [Field F] [Fintype F]
    (D : OrdinaryTagInput F) : TransformedUniversalTag F :=
  ordinaryUniversalTag D.source D.root D.center (D.owns D.center)
    D.center_primitive
    (fun z hz => D.root_degree_le D.center z hz)
    (fun z hz => D.exact_root D.center z hz)
    (fun z hz => D.simple_root D.center z hz)
@[simp]
theorem OrdinaryTagInput.toTag_source
    {F : Type} [Field F] [Fintype F]
    (D : OrdinaryTagInput F) : D.toTag.source = D.source := rfl
@[simp]
theorem OrdinaryTagInput.toTag_transformed
    {F : Type} [Field F] [Fintype F]
    (D : OrdinaryTagInput F) : D.toTag.transformed = D.source := rfl
@[simp]
theorem OrdinaryTagInput.toTag_center
    {F : Type} [Field F] [Fintype F]
    (D : OrdinaryTagInput F) : D.toTag.center = D.center := rfl
@[simp]
theorem OrdinaryTagInput.toTag_owns
    {F : Type} [Field F] [Fintype F]
    (D : OrdinaryTagInput F) : D.toTag.owns = D.owns D.center := rfl
@[simp]
theorem OrdinaryTagInput.toTag_root
    {F : Type} [Field F] [Fintype F]
    (D : OrdinaryTagInput F) : D.toTag.root = D.root := rfl
noncomputable def mixedUniversalTag
    {F A B : Type} [Field F] [Fintype F]
    (high : A → CoreTransformedTagInput F)
    (low : B → OrdinaryTagInput F) :
    Sum A B → TransformedUniversalTag F
  | Sum.inl a => (high a).toTag
  | Sum.inr b => (low b).toTag
@[simp]
theorem mixedUniversalTag_inl
    {F A B : Type} [Field F] [Fintype F]
    (high : A → CoreTransformedTagInput F)
    (low : B → OrdinaryTagInput F) (a : A) :
    mixedUniversalTag high low (Sum.inl a) = (high a).toTag := rfl
@[simp]
theorem mixedUniversalTag_inr
    {F A B : Type} [Field F] [Fintype F]
    (high : A → CoreTransformedTagInput F)
    (low : B → OrdinaryTagInput F) (b : B) :
    mixedUniversalTag high low (Sum.inr b) = (low b).toTag := rfl
theorem mixedPositiveInnerFactorPairs_card_le_sourceDegree
    {F A B : Type} [Field F] [Fintype F] [DecidableEq F]
    [NormalizationMonoid F] [DecidableEq A] [DecidableEq B]
    (high : A → CoreTransformedTagInput F)
    (low : B → OrdinaryTagInput F)
    (Outer : Finset (Sum A B)) :
    (positiveInnerFactorPairs Outer (mixedUniversalTag high low)).card ≤
      ∑ a ∈ Outer, (mixedUniversalTag high low a).source.natDegree :=
  positiveInnerFactorPairs_card_le_sum_sourceDegree
    Outer (mixedUniversalTag high low)
theorem exists_mixedPositiveInnerFactorPair
    {F A B : Type} [Field F] [Fintype F] [DecidableEq F]
    [NormalizationMonoid F] [DecidableEq A] [DecidableEq B]
    (high : A → CoreTransformedTagInput F)
    (low : B → OrdinaryTagInput F)
    (Outer : Finset (Sum A B)) (z : F)
    (hcover : ∃ a ∈ Outer, (mixedUniversalTag high low a).owns z) :
    ∃ p ∈ positiveInnerFactorPairs Outer (mixedUniversalTag high low),
      pairRel (mixedUniversalTag high low) z p :=
  exists_positiveInnerFactorPair Outer (mixedUniversalTag high low) z hcover
end BCHKSMixedUniversalTag6400
end ProximityPrize.SubmissionLower
