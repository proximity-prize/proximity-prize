import ProximityPrize.SubmissionLower.BCHKSExplicitCoreInnerTransport6400
import ProximityPrize.SubmissionLower.BCHKSMixedUniversalTag6400
import ProximityPrize.SubmissionLower.BCHKSUniversalGlobalCapacity
namespace ProximityPrize.SubmissionLower
namespace BCHKSExplicitMixedInnerPairs6400
open Polynomial Polynomial.Bivariate RationalFunctions
open RationalFunctions.HenselNumerators
open RationalFunctions.HenselNumerators.ConcreteFiniteNumerators
open BCHKSTransformedUniversalTag6400
open BCHKSCoreTransformedUniversalTag6400
open BCHKSMixedUniversalTag6400
open BCHKSExplicitCoreInnerTransport6400
open BCHKSCoreQuotientHenselAudit6400
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
structure ExplicitInnerData
    {F : Type} [Field F]
    (tag : TransformedUniversalTag F) where
  inner : F[X][Y]
  supportCap : Nat
  inner_irreducible : Irreducible inner
  inner_degree_pos : 0 < inner.natDegree
  inner_dvd : inner ∣ triSpecializeX tag.transformed tag.center
  transformed_YZCap : YZCap tag.transformed supportCap
  inner_totalDegree_le :
    Polynomial.Bivariate.totalDegree inner ≤ supportCap
  owner_root : ∀ z, tag.owns z →
    biEval inner ((tag.root z).eval tag.center) z = 0
  owner_leadingCoeff_ne_zero : ∀ z, tag.owns z →
    inner.leadingCoeff.eval z ≠ 0
theorem ExplicitInnerData.henselSetup
    {F : Type} [Field F]
    {tag : TransformedUniversalTag F}
    (D : ExplicitInnerData tag) :
    HenselNumerators.Hypotheses tag.center tag.transformed D.inner :=
  henselHypotheses_of_primitive_factor
    tag.transformed tag.center D.inner tag.primitive D.inner_dvd
theorem ExplicitInnerData.ownerPredicates
    {F : Type} [Field F]
    {tag : TransformedUniversalTag F}
    (D : ExplicitInnerData tag) (z : F) (hz : tag.owns z) :
    biEval D.inner ((tag.root z).eval tag.center) z = 0 ∧
      D.inner.leadingCoeff.eval z ≠ 0 ∧
      FiniteHensel.IsSimpleRootAt
        (triSpecializeZ tag.transformed z) tag.center
          ((tag.root z).eval tag.center) :=
  ⟨D.owner_root z hz, D.owner_leadingCoeff_ne_zero z hz,
    tag.simple_root z hz⟩
theorem ExplicitInnerData.zeta_ne_zero_of_owner
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {tag : TransformedUniversalTag F}
    (D : ExplicitInnerData tag)
    [Fact (Irreducible D.inner)] [Fact (0 < D.inner.natDegree)]
    (z : F) (hz : tag.owns z) :
    HenselNumerators.zeta tag.transformed tag.center D.inner ≠ 0 := by
  exact zeta_ne_zero_of_simple_factor_owner
    tag.center z ((tag.root z).eval tag.center)
      (D.owner_root z hz) (D.owner_leadingCoeff_ne_zero z hz)
      (tag.simple_root z hz)
theorem ExplicitInnerData.exists_beta_weight_sharp_of_owner
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {tag : TransformedUniversalTag F}
    (D : ExplicitInnerData tag)
    [Fact (Irreducible D.inner)] [Fact (0 < D.inner.natDegree)]
    (z : F) (hz : tag.owns z)
    (N : Nat)
    (hdegreeY : 2 ≤ Polynomial.Bivariate.natDegreeY tag.transformed)
    (horder : tag.rootDegreeCap ≤ N) :
    ∃ beta : 𝒪 D.inner,
      embeddingOf𝒪Into𝕃 D.inner beta =
          betaField (R := tag.transformed) (H := D.inner)
            tag.center D.henselSetup N tag.rootDegreeCap ∧
      regularWeight (Fact.out : 0 < D.inner.natDegree) beta
          D.supportCap ≤
        (WithBot.some
          (numeratorShapeSharp tag.transformed D.inner
            D.supportCap tag.rootDegreeCap) : WithBot Nat) ∧
      FiniteHenselWeight.denominatorExponent tag.rootDegreeCap =
        2 * tag.rootDegreeCap - 1 := by
  exact betaRegular_at_order_weight_sharpExponent
    tag.center D.henselSetup (D.zeta_ne_zero_of_owner z hz)
      D.supportCap tag.rootDegreeCap N D.inner_totalDegree_le
      D.transformed_YZCap hdegreeY horder
theorem ExplicitInnerData.exists_beta_weight_sharp_of_source_degree
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {tag : TransformedUniversalTag F}
    (D : ExplicitInnerData tag)
    [Fact (Irreducible D.inner)] [Fact (0 < D.inner.natDegree)]
    (z : F) (hz : tag.owns z)
    (N : Nat) (hsourceDegree : 2 ≤ tag.source.natDegree)
    (horder : tag.rootDegreeCap ≤ N) :
    ∃ beta : 𝒪 D.inner,
      embeddingOf𝒪Into𝕃 D.inner beta =
          betaField (R := tag.transformed) (H := D.inner)
            tag.center D.henselSetup N tag.rootDegreeCap ∧
      regularWeight (Fact.out : 0 < D.inner.natDegree) beta
          D.supportCap ≤
        (WithBot.some
          (numeratorShapeSharp tag.transformed D.inner
            D.supportCap tag.rootDegreeCap) : WithBot Nat) ∧
      FiniteHenselWeight.denominatorExponent tag.rootDegreeCap =
        2 * tag.rootDegreeCap - 1 := by
  apply D.exists_beta_weight_sharp_of_owner z hz N
  · change 2 ≤ tag.transformed.natDegree
    rw [tag.outerDegree_preserved]
    exact hsourceDegree
  · exact horder
noncomputable def explicitCoreInnerData
    {F : Type} [Field F]
    (R : F[X][X][Y]) (P Q : F → F[X])
    (B0 B1 G : F[X]) (x0 : F) (s Dcap : Nat)
    (owns : F → Prop) (H : F[X][Y])
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
    (hHirr : Irreducible H) (hHpos : 0 < H.natDegree)
    (hHdvd : H ∣ triSpecializeX R x0)
    (hHroot : ∀ z, owns z → biEval H ((P z).eval x0) z = 0)
    (hHlead : ∀ z, owns z → H.leadingCoeff.eval z ≠ 0)
    (hYZ : YZCap R Dcap) :
    ExplicitInnerData
      (coreTransformedUniversalTag R P Q B0 B1 G x0 s owns
        hG0 hGx hprimitive hQdegree hshape hroot hsimple
        hB0 hB1 hGdegree) := {
  inner := transportedInnerFactor H B0 B1 G x0
  supportCap := Dcap
  inner_irreducible :=
    transportedInnerFactor_irreducible H B0 B1 G x0 hHirr hGx
  inner_degree_pos := by
    rw [transportedInnerFactor_natDegree H B0 B1 G x0 hGx]
    exact hHpos
  inner_dvd :=
    transportedInnerFactor_dvd_transformedFiber R H B0 B1 G x0 hHdvd
  transformed_YZCap := coreRootTransform_YZCap R B0 B1 G Dcap hG0 hYZ
  inner_totalDegree_le :=
    transportedInnerFactor_totalDegree_le R H B0 B1 G x0 Dcap
      hHpos hHdvd hprimitive hG0 hGx hYZ
  owner_root := by
    intro z hz
    exact biEval_transportedInnerFactor_eq_zero_of_owner
      H B0 B1 G (P z) (Q z) x0 z (hshape z hz) (hHroot z hz)
  owner_leadingCoeff_ne_zero := by
    intro z hz
    exact transportedInnerFactor_leadingCoeff_eval_ne_zero
      H B0 B1 G x0 z hGx (hHlead z hz)
}
noncomputable def CoreTransformedTagInput.explicitInnerData
    {F : Type} [Field F] [Fintype F]
    (D : CoreTransformedTagInput F) (H : F[X][Y]) (Dcap : Nat)
    (hHirr : Irreducible H) (hHpos : 0 < H.natDegree)
    (hHdvd : H ∣ triSpecializeX D.source D.center)
    (hHroot : ∀ z, D.owns D.center z →
      biEval H ((D.originalRoot z).eval D.center) z = 0)
    (hHlead : ∀ z, D.owns D.center z →
      H.leadingCoeff.eval z ≠ 0)
    (hYZ : YZCap D.source Dcap) :
    ExplicitInnerData D.toTag :=
  explicitCoreInnerData
    D.source D.originalRoot D.quotientRoot D.base0 D.base1 D.locator
      D.center D.rootDegreeCap Dcap (D.owns D.center) H
      D.locator_ne_zero D.center_locator_ne_zero D.center_primitive
      (fun z hz ↦ D.quotient_degree_le D.center z hz)
      (fun z hz ↦ D.quotient_shape D.center z hz)
      (fun z hz ↦ D.original_exact_root D.center z hz)
      (fun z hz ↦ D.original_simple_root D.center z hz)
      D.base0_degree_le D.base1_degree_le D.locator_degree_add_cap
      hHirr hHpos hHdvd hHroot hHlead hYZ
theorem explicitInnerFactor_totalDegree_le
    {F : Type} [Field F]
    (R : F[X][X][Y]) (H : F[X][Y]) (x0 : F) (Dcap : Nat)
    (hHpos : 0 < H.natDegree)
    (hHdvd : H ∣ triSpecializeX R x0)
    (hprimitive : (triSpecializeX R x0).IsPrimitive)
    (hYZ : YZCap R Dcap) :
    Polynomial.Bivariate.totalDegree H ≤ Dcap := by
  have hfiberTotal :
      Polynomial.Bivariate.totalDegree (triSpecializeX R x0) ≤ Dcap := by
    have hlt := totalDegree_triSpecializeX_lt R x0 (Dcap + 1)
      (Nat.zero_lt_succ Dcap) (by
        intro j a ha
        have hcap := hYZ j a ha
        omega)
    omega
  have hH0 : H ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hHpos
  have hfiber0 : triSpecializeX R x0 ≠ 0 := hprimitive.ne_zero
  obtain ⟨C, hC⟩ := hHdvd
  have hC0 : C ≠ 0 := by
    intro hzero
    apply hfiber0
    rw [hC, hzero, mul_zero]
  have hdivTotal : Polynomial.Bivariate.totalDegree H ≤
      Polynomial.Bivariate.totalDegree (triSpecializeX R x0) := by
    rw [hC, Polynomial.Bivariate.totalDegree_mul hH0 hC0]
    exact Nat.le_add_right _ _
  exact hdivTotal.trans hfiberTotal
noncomputable def OrdinaryTagInput.explicitInnerData
    {F : Type} [Field F] [Fintype F]
    (D : OrdinaryTagInput F) (H : F[X][Y]) (Dcap : Nat)
    (hHirr : Irreducible H) (hHpos : 0 < H.natDegree)
    (hHdvd : H ∣ triSpecializeX D.source D.center)
    (hHroot : ∀ z, D.owns D.center z →
      biEval H ((D.root z).eval D.center) z = 0)
    (hHlead : ∀ z, D.owns D.center z →
      H.leadingCoeff.eval z ≠ 0)
    (hYZ : YZCap D.source Dcap) :
    ExplicitInnerData D.toTag := {
  inner := H
  supportCap := Dcap
  inner_irreducible := hHirr
  inner_degree_pos := hHpos
  inner_dvd := hHdvd
  transformed_YZCap := hYZ
  inner_totalDegree_le := explicitInnerFactor_totalDegree_le
    D.source H D.center Dcap hHpos hHdvd D.center_primitive hYZ
  owner_root := hHroot
  owner_leadingCoeff_ne_zero := hHlead
}
noncomputable def mixedExplicitInnerData
    {F A B : Type} [Field F] [Fintype F]
    (high : A → CoreTransformedTagInput F)
    (low : B → OrdinaryTagInput F)
    (highData : ∀ a, ExplicitInnerData (high a).toTag)
    (lowData : ∀ b, ExplicitInnerData (low b).toTag) :
    ∀ i, ExplicitInnerData (mixedUniversalTag high low i)
  | Sum.inl a => highData a
  | Sum.inr b => lowData b
noncomputable def explicitInnerPairs
    {F A : Type} [Field F] [DecidableEq A]
    (Outer : Finset A) (tag : A → TransformedUniversalTag F)
    (data : ∀ a, ExplicitInnerData (tag a)) :
    Finset (A × F[X][Y]) := by
  classical
  exact Outer.image fun a ↦ (a, (data a).inner)
theorem explicitInnerPairs_card_eq_outer
    {F A : Type} [Field F] [DecidableEq A]
    (Outer : Finset A) (tag : A → TransformedUniversalTag F)
    (data : ∀ a, ExplicitInnerData (tag a)) :
    (explicitInnerPairs Outer tag data).card = Outer.card := by
  classical
  exact Finset.card_image_of_injective Outer (by
    intro a b hab
    exact congrArg Prod.fst hab)
theorem explicitInnerPairs_card_le_sum_sourceDegree
    {F A : Type} [Field F] [DecidableEq A]
    (Outer : Finset A) (tag : A → TransformedUniversalTag F)
    (data : ∀ a, ExplicitInnerData (tag a)) :
    (explicitInnerPairs Outer tag data).card ≤
      ∑ a ∈ Outer, (tag a).source.natDegree := by
  classical
  rw [explicitInnerPairs_card_eq_outer Outer tag data]
  calc
    Outer.card = Outer.card • (1 : Nat) := by simp
    _ ≤ ∑ a ∈ Outer, (tag a).source.natDegree := by
      apply Finset.card_nsmul_le_sum
      intro a ha
      exact (data a).inner_degree_pos.trans_le
        ((Polynomial.natDegree_le_of_dvd
            (data a).inner_dvd (tag a).primitive.ne_zero).trans
          (tag a).specializeDegree_le_source)
theorem exists_explicitInnerPair
    {F A : Type} [Field F] [DecidableEq A]
    (Outer : Finset A) (tag : A → TransformedUniversalTag F)
    (data : ∀ a, ExplicitInnerData (tag a))
    (z : F) (hcover : ∃ a ∈ Outer, (tag a).owns z) :
    ∃ p ∈ explicitInnerPairs Outer tag data, pairRel tag z p := by
  classical
  obtain ⟨a, ha, hz⟩ := hcover
  refine ⟨(a, (data a).inner), ?_, hz, ?_⟩
  · exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  · exact (data a).owner_root z hz
theorem exists_mixedExplicitInnerPair
    {F A B : Type} [Field F] [Fintype F]
    [DecidableEq A] [DecidableEq B]
    (high : A → CoreTransformedTagInput F)
    (low : B → OrdinaryTagInput F)
    (highData : ∀ a, ExplicitInnerData (high a).toTag)
    (lowData : ∀ b, ExplicitInnerData (low b).toTag)
    (Outer : Finset (Sum A B)) (z : F)
    (hcover : ∃ a ∈ Outer, (mixedUniversalTag high low a).owns z) :
    ∃ p ∈ explicitInnerPairs Outer (mixedUniversalTag high low)
        (mixedExplicitInnerData high low highData lowData),
      pairRel (mixedUniversalTag high low) z p :=
  exists_explicitInnerPair Outer (mixedUniversalTag high low)
    (mixedExplicitInnerData high low highData lowData) z hcover
theorem degreeX_le_totalDegree
    {F : Type} [Field F] (H : F[X][Y]) :
    Polynomial.Bivariate.degreeX H ≤
      Polynomial.Bivariate.totalDegree H := by
  classical
  unfold Polynomial.Bivariate.degreeX Polynomial.Bivariate.totalDegree
  apply Finset.sup_le
  intro j hj
  exact (Nat.le_add_right (H.coeff j).natDegree j).trans
    (Finset.le_sup (f := fun i ↦ (H.coeff i).natDegree + i) hj)
noncomputable def explicitPairResultantCapacity
    {F A : Type} [Field F]
    (tag : A → TransformedUniversalTag F)
    (data : ∀ a, ExplicitInnerData (tag a))
    (E : A → Nat) (p : A × F[X][Y]) : Nat :=
  p.2.natDegree * (E p.1 * (data p.1).supportCap) +
    (E p.1 * (tag p.1).source.natDegree) *
      Polynomial.Bivariate.degreeX p.2
theorem explicitPairResultantCapacity_le
    {F A : Type} [Field F]
    (tag : A → TransformedUniversalTag F)
    (data : ∀ a, ExplicitInnerData (tag a))
    (E : A → Nat) (a : A) :
    explicitPairResultantCapacity tag data E (a, (data a).inner) ≤
      2 * E a * (tag a).source.natDegree * (data a).supportCap := by
  have hinnerDegree : (data a).inner.natDegree ≤
      (tag a).source.natDegree :=
    (Polynomial.natDegree_le_of_dvd
      (data a).inner_dvd (tag a).primitive.ne_zero).trans
        (tag a).specializeDegree_le_source
  have hinnerX : Polynomial.Bivariate.degreeX (data a).inner ≤
      (data a).supportCap :=
    (degreeX_le_totalDegree (data a).inner).trans
      (data a).inner_totalDegree_le
  unfold explicitPairResultantCapacity
  calc
    (data a).inner.natDegree * (E a * (data a).supportCap) +
          (E a * (tag a).source.natDegree) *
            Polynomial.Bivariate.degreeX (data a).inner ≤
        (tag a).source.natDegree * (E a * (data a).supportCap) +
          (E a * (tag a).source.natDegree) * (data a).supportCap := by
      gcongr
    _ = 2 * E a * (tag a).source.natDegree *
        (data a).supportCap := by ring
theorem explicitInner_resultant_natDegree_le
    {F A : Type} [Field F]
    (tag : A → TransformedUniversalTag F)
    (data : ∀ a, ExplicitInnerData (tag a))
    (E : A → Nat) (a : A) (B : F[X][Y])
    (hBY : B.natDegree ≤ E a * (tag a).source.natDegree)
    (hBX : Polynomial.Bivariate.degreeX B ≤
      E a * (data a).supportCap) :
    (Polynomial.resultant B (data a).inner
      B.natDegree (data a).inner.natDegree).natDegree ≤
        explicitPairResultantCapacity tag data E
          (a, (data a).inner) := by
  calc
    (Polynomial.resultant B (data a).inner
        B.natDegree (data a).inner.natDegree).natDegree ≤
      (data a).inner.natDegree * Polynomial.Bivariate.degreeX B +
        B.natDegree * Polynomial.Bivariate.degreeX (data a).inner :=
      bivariate_resultant_natDegree_le B (data a).inner
        B.natDegree (data a).inner.natDegree
    _ ≤ (data a).inner.natDegree *
          (E a * (data a).supportCap) +
        (E a * (tag a).source.natDegree) *
          Polynomial.Bivariate.degreeX (data a).inner := by
      gcongr
    _ = explicitPairResultantCapacity tag data E
        (a, (data a).inner) := rfl
theorem explicitPairResultantCapacity_sum_le
    {F A : Type} [Field F] [DecidableEq A]
    (Outer : Finset A) (tag : A → TransformedUniversalTag F)
    (data : ∀ a, ExplicitInnerData (tag a)) (E : A → Nat) :
    (∑ p ∈ explicitInnerPairs Outer tag data,
      explicitPairResultantCapacity tag data E p) ≤
      ∑ a ∈ Outer,
        2 * E a * (tag a).source.natDegree * (data a).supportCap := by
  classical
  let pair : A → A × F[X][Y] := fun a ↦ (a, (data a).inner)
  have hinj : Set.InjOn pair (↑Outer : Set A) := by
    intro a _ha b _hb hab
    exact congrArg Prod.fst hab
  calc
    (∑ p ∈ explicitInnerPairs Outer tag data,
        explicitPairResultantCapacity tag data E p) =
        ∑ a ∈ Outer,
          explicitPairResultantCapacity tag data E (pair a) := by
      change (∑ p ∈ Outer.image pair,
          explicitPairResultantCapacity tag data E p) = _
      exact Finset.sum_image hinj
    _ ≤ ∑ a ∈ Outer,
        2 * E a * (tag a).source.natDegree * (data a).supportCap := by
      apply Finset.sum_le_sum
      intro a ha
      exact explicitPairResultantCapacity_le tag data E a
theorem exists_explicit_pair_fiber_of_fused_resultant_ledger
    {F A : Type} [Field F] [DecidableEq F] [DecidableEq A]
    (S QBad : Finset F) (Outer : Finset A)
    (OuterBad : A → Finset F)
    (tag : A → TransformedUniversalTag F)
    [DecidableRel (pairRel tag)]
    (data : ∀ a, ExplicitInnerData (tag a))
    (resultantDegree : (A × F[X][Y]) → Nat)
    (nminus gap errors qCap outerCap resultCap pairCap fusedCap : Nat)
    (hQ : QBad.card ≤ qCap)
    (hOuter : (∑ a ∈ Outer, (OuterBad a).card) ≤ outerCap)
    (hresult :
      (∑ p ∈ explicitInnerPairs Outer tag data,
        resultantDegree p) ≤ resultCap)
    (hsourceMass : (∑ a ∈ Outer, (tag a).source.natDegree) ≤ pairCap)
    (hfused : nminus * resultCap ≤ gap * fusedCap)
    (hcover : ∀ z ∈ S \ (QBad ∪ Outer.biUnion OuterBad),
      ∃ a ∈ Outer, (tag a).owns z)
    (hlarge : qCap + outerCap +
        (fusedCap + (errors + 1) * pairCap) < S.card) :
    ∃ p ∈ explicitInnerPairs Outer tag data,
      (nminus * resultantDegree p) / gap + (errors + 1) <
        ((S \ (QBad ∪ Outer.biUnion OuterBad)).filter
          fun z ↦ pairRel tag z p).card := by
  classical
  apply exists_pair_fiber_of_fused_resultant_ledger
    S QBad Outer OuterBad (explicitInnerPairs Outer tag data)
      (pairRel tag) resultantDegree nminus gap errors qCap outerCap
      resultCap pairCap fusedCap hQ hOuter hresult
      ((explicitInnerPairs_card_le_sum_sourceDegree Outer tag data).trans
        hsourceMass)
      hfused
  · intro z hz
    exact exists_explicitInnerPair Outer tag data z (hcover z hz)
  · exact hlarge
theorem exists_explicit_pair_fiber_of_capacity_ledger
    {F A : Type} [Field F] [DecidableEq F] [DecidableEq A]
    (S QBad : Finset F) (Outer : Finset A)
    (OuterBad : A → Finset F)
    (tag : A → TransformedUniversalTag F)
    [DecidableRel (pairRel tag)]
    (data : ∀ a, ExplicitInnerData (tag a))
    (E : A → Nat)
    (resultantDegree : (A × F[X][Y]) → Nat)
    (nminus gap errors qCap outerCap resultCap pairCap fusedCap : Nat)
    (hQ : QBad.card ≤ qCap)
    (hOuter : (∑ a ∈ Outer, (OuterBad a).card) ≤ outerCap)
    (hresultantDegree : ∀ p ∈ explicitInnerPairs Outer tag data,
      resultantDegree p ≤ explicitPairResultantCapacity tag data E p)
    (htagCharge :
      (∑ a ∈ Outer,
        2 * E a * (tag a).source.natDegree * (data a).supportCap) ≤
          resultCap)
    (hsourceMass : (∑ a ∈ Outer, (tag a).source.natDegree) ≤ pairCap)
    (hfused : nminus * resultCap ≤ gap * fusedCap)
    (hcover : ∀ z ∈ S \ (QBad ∪ Outer.biUnion OuterBad),
      ∃ a ∈ Outer, (tag a).owns z)
    (hlarge : qCap + outerCap +
        (fusedCap + (errors + 1) * pairCap) < S.card) :
    ∃ p ∈ explicitInnerPairs Outer tag data,
      (nminus * resultantDegree p) / gap + (errors + 1) <
        ((S \ (QBad ∪ Outer.biUnion OuterBad)).filter
          fun z ↦ pairRel tag z p).card := by
  have hresult :
      (∑ p ∈ explicitInnerPairs Outer tag data, resultantDegree p) ≤
        resultCap := by
    calc
      (∑ p ∈ explicitInnerPairs Outer tag data, resultantDegree p) ≤
          ∑ p ∈ explicitInnerPairs Outer tag data,
            explicitPairResultantCapacity tag data E p := by
        apply Finset.sum_le_sum
        intro p hp
        exact hresultantDegree p hp
      _ ≤ ∑ a ∈ Outer,
          2 * E a * (tag a).source.natDegree *
            (data a).supportCap :=
        explicitPairResultantCapacity_sum_le Outer tag data E
      _ ≤ resultCap := htagCharge
  exact exists_explicit_pair_fiber_of_fused_resultant_ledger
    S QBad Outer OuterBad tag data resultantDegree nminus gap errors
      qCap outerCap resultCap pairCap fusedCap hQ hOuter hresult
      hsourceMass hfused hcover hlarge
theorem exists_explicit_pair_fiber_of_self_capacity_ledger
    {F A : Type} [Field F] [DecidableEq F] [DecidableEq A]
    (S QBad : Finset F) (Outer : Finset A)
    (OuterBad : A → Finset F)
    (tag : A → TransformedUniversalTag F)
    [DecidableRel (pairRel tag)]
    (data : ∀ a, ExplicitInnerData (tag a))
    (E : A → Nat)
    (nminus gap errors qCap outerCap resultCap pairCap fusedCap : Nat)
    (hQ : QBad.card ≤ qCap)
    (hOuter : (∑ a ∈ Outer, (OuterBad a).card) ≤ outerCap)
    (htagCharge :
      (∑ a ∈ Outer,
        2 * E a * (tag a).source.natDegree * (data a).supportCap) ≤
          resultCap)
    (hsourceMass : (∑ a ∈ Outer, (tag a).source.natDegree) ≤ pairCap)
    (hfused : nminus * resultCap ≤ gap * fusedCap)
    (hcover : ∀ z ∈ S \ (QBad ∪ Outer.biUnion OuterBad),
      ∃ a ∈ Outer, (tag a).owns z)
    (hlarge : qCap + outerCap +
        (fusedCap + (errors + 1) * pairCap) < S.card) :
    ∃ p ∈ explicitInnerPairs Outer tag data,
      (nminus * explicitPairResultantCapacity tag data E p) / gap +
          (errors + 1) <
        ((S \ (QBad ∪ Outer.biUnion OuterBad)).filter
          fun z ↦ pairRel tag z p).card := by
  exact exists_explicit_pair_fiber_of_capacity_ledger
    S QBad Outer OuterBad tag data E
      (explicitPairResultantCapacity tag data E)
      nminus gap errors qCap outerCap resultCap pairCap fusedCap
      hQ hOuter (fun _p _hp ↦ le_rfl) htagCharge hsourceMass
      hfused hcover hlarge
end BCHKSExplicitMixedInnerPairs6400
end ProximityPrize.SubmissionLower
