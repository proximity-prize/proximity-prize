import ProximityPrize.SubmissionLower.BCHKSCoreQuotientHenselAudit6400
namespace ProximityPrize.SubmissionLower
namespace BCHKSTransformedUniversalTag6400
open Polynomial
open RationalFunctions
open RationalFunctions.HenselNumerators
open BCHKSCoreQuotientHenselAudit6400
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
structure TransformedUniversalTag
    (F : Type) [Field F] where
  source : Polynomial (Polynomial (Polynomial F))
  transformed : Polynomial (Polynomial (Polynomial F))
  center : F
  owns : F -> Prop
  root : F -> Polynomial F
  rootDegreeCap : Nat
  primitive : (triSpecializeX transformed center).IsPrimitive
  specializeDegree_le_source :
    (triSpecializeX transformed center).natDegree <= source.natDegree
  root_degree_le : forall z, owns z -> (root z).natDegree <= rootDegreeCap
  exact_root : forall z, owns z -> triEval transformed z (root z) = 0
  simple_root : forall z, owns z ->
    FiniteHensel.IsSimpleRootAt (triSpecializeZ transformed z)
      center ((root z).eval center)
  second_ne_zero : forall z, owns z ->
    biSpecializeZ (triSpecializeX transformed center) z ≠ 0
  outerDegree_preserved : transformed.natDegree = source.natDegree
  yzSupportDegree_le_source :
    YZFactorCap.yzSupportDegree transformed 1 <=
      YZFactorCap.yzSupportDegree source 1
  weightedSupportDegree_le_source :
    WeightedFactorCaps.weightedSupportDegree transformed rootDegreeCap <=
      WeightedFactorCaps.weightedSupportDegree source 131071
noncomputable def positiveInnerFactorPairs
    {F A : Type} [Field F] [DecidableEq F] [NormalizationMonoid F]
    [DecidableEq A]
    (Outer : Finset A) (tag : A -> TransformedUniversalTag F) :
    Finset (A × Polynomial (Polynomial F)) := by
  classical
  exact Outer.biUnion fun a =>
    ((UniqueFactorizationMonoid.normalizedFactors
      (triSpecializeX (tag a).transformed (tag a).center)).toFinset.filter
        fun H => 0 < H.natDegree).image fun H => (a, H)
def pairRel
    {F A : Type} [Field F]
    (tag : A -> TransformedUniversalTag F)
    (z : F) (p : A × Polynomial (Polynomial F)) : Prop :=
  (tag p.1).owns z /\
    biEval p.2 ((tag p.1).root z |>.eval (tag p.1).center) z = 0
theorem positiveInnerFactorPairs_card_le_sum_sourceDegree
    {F A : Type} [Field F] [DecidableEq F] [NormalizationMonoid F]
    [DecidableEq A]
    (Outer : Finset A) (tag : A -> TransformedUniversalTag F) :
    (positiveInnerFactorPairs Outer tag).card <=
      ∑ a ∈ Outer, (tag a).source.natDegree := by
  classical
  let inner := fun a : A =>
    (UniqueFactorizationMonoid.normalizedFactors
      (triSpecializeX (tag a).transformed (tag a).center)).toFinset.filter
        fun H => 0 < H.natDegree
  let pairs := fun a : A => (inner a).image fun H => (a, H)
  have hinner : ∀ a ∈ Outer, (pairs a).card <= (tag a).source.natDegree := by
    intro a ha
    calc
      (pairs a).card <= (inner a).card := Finset.card_image_le
      _ = (inner a).card • (1 : Nat) := by simp
      _ <= ∑ H ∈ inner a, H.natDegree := by
        apply Finset.card_nsmul_le_sum
        intro H hH
        exact (Finset.mem_filter.mp hH).2
      _ <= ∑ H ∈
          (UniqueFactorizationMonoid.normalizedFactors
            (triSpecializeX (tag a).transformed (tag a).center)).toFinset,
          H.natDegree := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _)
        simp
      _ <= (triSpecializeX (tag a).transformed
          (tag a).center).natDegree := by
        exact normalizedFactors_toFinset_sum_natDegree_le _
          (tag a).primitive.ne_zero
      _ <= (tag a).source.natDegree :=
        (tag a).specializeDegree_le_source
  calc
    (positiveInnerFactorPairs Outer tag).card =
        (Outer.biUnion pairs).card := by rfl
    _ <= ∑ a ∈ Outer, (pairs a).card := Finset.card_biUnion_le
    _ <= ∑ a ∈ Outer, (tag a).source.natDegree :=
      Finset.sum_le_sum hinner
theorem positiveInnerFactorPairs_card_le
    {F A : Type} [Field F] [DecidableEq F] [NormalizationMonoid F]
    [DecidableEq A]
    (Outer : Finset A) (tag : A -> TransformedUniversalTag F)
    (M : Nat) (hmass : (∑ a ∈ Outer, (tag a).source.natDegree) <= M) :
    (positiveInnerFactorPairs Outer tag).card <= M :=
  (positiveInnerFactorPairs_card_le_sum_sourceDegree Outer tag).trans hmass
theorem exists_positiveInnerFactorPair
    {F A : Type} [Field F] [DecidableEq F] [NormalizationMonoid F]
    [DecidableEq A]
    (Outer : Finset A) (tag : A -> TransformedUniversalTag F)
    (z : F) (hcover : ∃ a ∈ Outer, (tag a).owns z) :
    ∃ p ∈ positiveInnerFactorPairs Outer tag, pairRel tag z p := by
  classical
  obtain ⟨a, ha, haz⟩ := hcover
  have hpoint : biEval
      (triSpecializeX (tag a).transformed (tag a).center)
      ((tag a).root z |>.eval (tag a).center) z = 0 := by
    rw [← eval_triEval_eq_biEval_triSpecializeX]
    rw [(tag a).exact_root z haz]
    simp
  obtain ⟨H, hH, hHpos, hHzero⟩ :=
    exists_positive_normalizedFactor_biEval_eq_zero
      (triSpecializeX (tag a).transformed (tag a).center) z
      ((tag a).root z |>.eval (tag a).center)
      ((tag a).second_ne_zero z haz) hpoint
  refine ⟨(a, H), ?_, haz, hHzero⟩
  simp only [positiveInnerFactorPairs, Finset.mem_biUnion,
    Finset.mem_image, Finset.mem_filter, Multiset.mem_toFinset]
  exact ⟨a, ha, H, ⟨hH, hHpos⟩, rfl⟩
theorem henselHypotheses_of_primitive_normalizedFactor
    {F : Type} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (T : Polynomial (Polynomial (Polynomial F))) (x0 : F)
    (H : Polynomial (Polynomial F))
    (hprimitive : (triSpecializeX T x0).IsPrimitive)
    (hH : H ∈ UniqueFactorizationMonoid.normalizedFactors
      (triSpecializeX T x0))
    (_hHpos : 0 < H.natDegree) :
    Irreducible H /\
      H ∣ triSpecializeX T x0 /\
      HenselNumerators.Hypotheses x0 T H := by
  have hHirr : Irreducible H :=
    (UniqueFactorizationMonoid.prime_of_normalized_factor H hH).irreducible
  have hHd : H ∣ triSpecializeX T x0 :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hH
  have hTX : triSpecializeX T x0 =
      Polynomial.Bivariate.evalX (Polynomial.C x0) T := by
    simp [triSpecializeX, Polynomial.Bivariate.evalX_eq_map]
  have hHyp : HenselNumerators.Hypotheses x0 T H := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [← hTX] using hHd
    · simpa [← hTX] using hprimitive.ne_zero
    · intro Q hfac hQdeg
      let q0 : Polynomial F := Q.coeff 0
      have hQC : Q = Polynomial.C q0 :=
        Polynomial.eq_C_of_natDegree_le_zero hQdeg.le
      apply (Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hprimitive) q0
      refine ⟨H, ?_⟩
      calc
        triSpecializeX T x0 = H * Q := by
          simpa [hTX] using hfac
        _ = H * Polynomial.C q0 := by rw [hQC]
        _ = Polynomial.C q0 * H := mul_comm _ _
  exact ⟨hHirr, hHd, hHyp⟩
theorem tag_inner_hensel_setup
    {F : Type} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (tag : TransformedUniversalTag F) (H : Polynomial (Polynomial F))
    (hH : H ∈ UniqueFactorizationMonoid.normalizedFactors
      (triSpecializeX tag.transformed tag.center))
    (hHpos : 0 < H.natDegree) :
    Irreducible H /\
      H ∣ triSpecializeX tag.transformed tag.center /\
      HenselNumerators.Hypotheses tag.center tag.transformed H :=
  henselHypotheses_of_primitive_normalizedFactor
    tag.transformed tag.center H tag.primitive hH hHpos
end BCHKSTransformedUniversalTag6400
end ProximityPrize.SubmissionLower
