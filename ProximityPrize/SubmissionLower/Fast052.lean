import ProximityPrize.SubmissionLower.Fast049
set_option Elab.async false
set_option autoImplicit true
section
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_7
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2
open scoped Classical
private theorem lift_prime_chain
    {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    [Algebra.IsIntegral B A] [FaithfulSMul B A] (l : LTSeries (PrimeSpectrum B)) :
    ∃ L : LTSeries (PrimeSpectrum A),
      L.length = l.length ∧ L.last.asIdeal.under B = l.last.asIdeal := by
  induction l using RelSeries.inductionOn' with
  | singleton q =>
    have := q.isPrime
    have hle : (⊥ : Ideal A).under B ≤ q.asIdeal := by
      change Ideal.comap (algebraMap B A) ⊥ ≤ q.asIdeal
      rw [← RingHom.ker_eq_comap_bot,
        (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective B A)]
      exact bot_le
    obtain ⟨Q, _, hQ, hQq⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
      q.asIdeal (⊥ : Ideal A) hle
    exact ⟨RelSeries.singleton _ ⟨Q, hQ⟩, rfl, hQq⟩
  | snoc l q hq ih =>
    obtain ⟨L, hlen, hlast⟩ := ih
    have := q.isPrime
    have hlt : l.last < q := hq
    have hle : L.last.asIdeal.under B ≤ q.asIdeal := hlast.trans_le hlt.le
    obtain ⟨Q, hQL, hQ, hQq⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
      q.asIdeal L.last.asIdeal hle
    have hnext : L.last < (⟨Q, hQ⟩ : PrimeSpectrum A) := by
      refine lt_of_le_of_ne hQL ?_
      intro heq
      have heq' := congrArg (fun x : PrimeSpectrum A => x.asIdeal.under B) heq
      exact hlt.ne (PrimeSpectrum.ext_iff.mpr (hlast.symm.trans (heq'.trans hQq)))
    exact ⟨L.snoc ⟨Q, hQ⟩ hnext, by simp [RelSeries.snoc, hlen], by simpa using hQq⟩
private theorem dim_eq_of_integral
    {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    [Algebra.IsIntegral B A] [FaithfulSMul B A]
    {d : ℕ} (hdim : ringKrullDim B = (d : WithBot ℕ∞)) :
    ringKrullDim A = (d : WithBot ℕ∞) := by
  apply le_antisymm
  · rw [← hdim]
    apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap B A))
    intro a b hab
    exact Ideal.IsIntegral.under_lt_under (R := B) (show a.asIdeal < b.asIdeal from hab)
  · obtain ⟨l, hlen⟩ := Order.le_krullDim_iff.mp hdim.ge
    obtain ⟨L, hL, _⟩ := lift_prime_chain (A := A) l
    exact Order.le_krullDim_iff.mpr ⟨L, hL.trans hlen⟩
private theorem dim_eq_of_normalization {k A : Type*} [Field k] [CommRing A]
    [Algebra k A] {d : ℕ}
    (g : MvPolynomial (Fin d) k →ₐ[k] A) (hg_inj : Function.Injective g) (hg_fin : g.Finite) :
    ringKrullDim A = (d : WithBot ℕ∞) := by
  let B := MvPolynomial (Fin d) k
  let _ : Algebra B A := g.toRingHom.toAlgebra
  have : Module.Finite B A := hg_fin
  have : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  have : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hg_inj
  have hdim : ringKrullDim B = (d : WithBot ℕ∞) := by
    simp [B, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field]
  exact dim_eq_of_integral (A := A) hdim
private theorem dim_eq_hilbert_degree {k σ : Type*} [Field k] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) [I.IsPrime] :
    ringKrullDim (MvPolynomial σ k ⧸ I) =
      ((MvPolynomial.affineHilbertPolynomial I).natDegree : WithBot ℕ∞) := by
  obtain ⟨d, g, hg_inj, hg_fin⟩ :=
    exists_finite_inj_algHom_of_fg k (MvPolynomial σ k ⧸ I)
  have hdeg := MvPolynomial.natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective
    g hg_fin hg_inj
  rw [Nat.card_fin] at hdeg
  rw [hdeg]
  exact dim_eq_of_normalization g hg_inj hg_fin
theorem cutComponent_curve {I : Ideal Ambient} {P : Jet} (hI : Active I)
    (hP : toJet P ∉ I) {Q : Ideal Ambient} (hQ : Q ∈ cutComponents I P) :
    Q.IsPrime ∧ ringKrullDim (CoordinateRing Q) = 1 := by
  have := hI.prime
  have hmin : Q ∈ (I ⊔ Ideal.span {toJet P}).minimalPrimes :=
    Ideal.mem_minimalPrimesFinset.mp hQ
  have := hmin.isPrime
  refine ⟨hmin.isPrime, ?_⟩
  have hdim := dim_eq_hilbert_degree I
  rw [hI.dimension] at hdim
  have hd : (MvPolynomial.affineHilbertPolynomial I).natDegree = 2 := by
    exact_mod_cast hdim.symm
  have hcut := MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_add_one hP hmin
  rw [hd] at hcut
  have hdegree : (MvPolynomial.affineHilbertPolynomial Q).natDegree = 1 := by omega
  rw [dim_eq_hilbert_degree Q, hdegree, Nat.cast_one]
theorem mark_on_cut {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ}
    {I : Ideal Ambient} {P : Jet} {γ : K}
    (hI : OnParent M F I γ) (hzero : jetAt P (M.label γ) (F.scalar γ) = 0) :
    ∃ Q ∈ cutComponents I P, OnParent M F Q γ := by
  let e := jetMarkHom (M.label γ) (F.scalar γ)
  have hle : I ⊔ Ideal.span {toJet P} ≤ RingHom.ker e := by
    apply sup_le hI
    exact (Ideal.span_singleton_le_iff_mem _).mpr
      (RingHom.mem_ker.mpr ((eval_toJet _ _ _).trans hzero))
  have : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  obtain ⟨Q, hQ, hmark⟩ := Ideal.exists_minimalPrimes_le hle
  exact ⟨Q, Ideal.mem_minimalPrimesFinset.mpr hQ, hmark⟩
private def markEvaluation {Q : Ideal Ambient} {z : K} {S : Polynomial K}
    (h : OnJet Q z S) : CoordinateRing Q →ₐ[FX] FX :=
  Ideal.Quotient.liftₐ Q
    (MvPolynomial.aeval ![seedEmbedding z, (seedEmbedding z)^p, atX S, atX S.derivative])
    (fun _ ha => RingHom.mem_ker.mp (h ha))
private theorem markEvaluation_first {Q : Ideal Ambient} {z : K} {S : Polynomial K}
    (h : OnJet Q z S) :
    markEvaluation h (Ideal.Quotient.mk Q (MvPolynomial.X 0)) = seedEmbedding z := by
  change MvPolynomial.aeval
    ![seedEmbedding z, (seedEmbedding z)^p, atX S, atX S.derivative]
      (MvPolynomial.X 0) = _
  simp [MvPolynomial.aeval_X]
private theorem seed_value_eq {Q : Ideal Ambient} [Q.IsPrime] (hQ : ConstantSeed Q)
    {z : K} {S : Polynomial K} (h : OnJet Q z S) :
    algebraMap FX (CoordinateRing Q) (seedEmbedding z) =
      Ideal.Quotient.mk Q (MvPolynomial.X 0) := by
  let x := Ideal.Quotient.mk Q ((MvPolynomial.X 0) : Ambient)
  have hx : IsIntegral FX x := (hQ 0).isIntegral
  apply minpoly.root hx
  have hw := congrArg (markEvaluation h) (minpoly.aeval FX x)
  rw [← Polynomial.aeval_algHom_apply, map_zero] at hw
  have hvalue : markEvaluation h x = seedEmbedding z := markEvaluation_first h
  rw [hvalue] at hw
  simpa [Polynomial.IsRoot, Polynomial.aeval_def] using hw
theorem same_label_on_constant {u del} {M : AnchorModel u del} {Γ}
    {F : AnchoredFamily M Γ} {Q : Ideal Ambient} (hprime : Q.IsPrime) (hQ : ConstantSeed Q)
    {γ δ : K} (hγ : OnParent M F Q γ) (hδ : OnParent M F Q δ) : γ = δ := by
  have := hprime
  apply K1_14_3.label_injective M
  apply seedEmbedding.injective
  apply (algebraMap FX (CoordinateRing Q)).injective
  exact (seed_value_eq hQ hγ).trans (seed_value_eq hQ hδ).symm
end
end K1_14_2_2_7
end
section
namespace K1_14_2_2_7
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2
open scoped Classical
def c1 : Prop :=
  ∀ (Q : Ideal Ambient), Q.IsPrime → ringKrullDim (CoordinateRing Q) = 1 →
    ¬ ConstantSeed Q →
    Module.Finite SeedField (JetSeedSection Q) ∧
    0 < Module.finrank SeedField (JetSeedSection Q) ∧
    Module.Finite SeedField (JetYSection Q)
def c2 : Prop :=
  ∀ (s : Shape) (I : Ideal Ambient) (P : Jet),
    s.J ≤ s.B → Active I → RowCaps P s → toJet P ∉ I →
    curveSeedMass (movingComponents I P) ≤ dot (weight s 0) (sectionDegree I)
def c3 : Prop :=
  ∀ (s : Shape) (I : Ideal Ambient) (P : Jet),
    s.J ≤ s.B → Active I → RowCaps P s → toJet P ∉ I →
    curveYMass (movingComponents I P) ≤ dot (weight s 1) (sectionDegree I)
def c4 : Prop :=
  ∀ (s : Shape) (I : Ideal Ambient) (P : Jet),
    s.J ≤ s.B → Active I → RowCaps P s → toJet P ∉ I →
    (constantComponents I P).card ≤ dot (weight s 2) (sectionDegree I)
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) :
    K1_14_2_2.c7 := by
  classical
  intro u del M Γ F s I P hshape hI hcaps hP
  let marked (Q : Ideal Ambient) : Finset K := Γ.filter (OnParent M F Q)
  let direct := (constantComponents I P).biUnion marked
  have hcard : direct.card ≤ (constantComponents I P).card := by
    change ((constantComponents I P).biUnion marked).card ≤ (constantComponents I P).card
    have hsingle (Q : Ideal Ambient) (hQ : Q ∈ constantComponents I P) :
        (marked Q).card ≤ 1 := by
      obtain ⟨hcomp, hconst⟩ := Finset.mem_filter.mp hQ
      apply Finset.card_le_one.mpr
      intro γ hγ δ hδ
      exact same_label_on_constant (cutComponent_curve hI hP hcomp).1 hconst
        (Finset.mem_filter.mp hγ).2 (Finset.mem_filter.mp hδ).2
    calc
      _ ≤ ∑ Q ∈ constantComponents I P, (marked Q).card := Finset.card_biUnion_le
      _ ≤ ∑ _Q ∈ constantComponents I P, 1 := Finset.sum_le_sum hsingle
      _ = _ := by simp
  let C : CutCover :=
    ⟨direct, movingComponents I P, by
      intro Q hQ
      obtain ⟨hcomp, hmov⟩ := Finset.mem_filter.mp hQ
      obtain ⟨hp, hdim⟩ := cutComponent_curve hI hP hcomp
      exact ⟨hp, hdim, h1 Q hp hdim hmov⟩⟩
  refine ⟨C, ?_, ?_⟩
  · intro fee
    fin_cases fee
    · exact h2 s I P hshape hI hcaps hP
    · exact h3 s I P hshape hI hcaps hP
    · exact hcard.trans (h4 s I P hshape hI hcaps hP)
  · intro γ hγ hparent hzero
    obtain ⟨Q, hQ, hmark⟩ := mark_on_cut hparent hzero
    by_cases hc : ConstantSeed Q
    · exact Or.inl (Finset.mem_biUnion.mpr
        ⟨Q, Finset.mem_filter.mpr ⟨hQ, hc⟩, Finset.mem_filter.mpr ⟨hγ, hmark⟩⟩)
    · exact Or.inr ⟨Q, Finset.mem_filter.mpr ⟨hQ, hc⟩, hmark⟩
end
end K1_14_2_2_7
end
section
namespace K1_14_2_2_7_2
noncomputable section
open K1_14 K1_14_2
open scoped RatFunc
attribute [local instance] Polynomial.algebra
abbrev SeedAmbient := MvPolynomial (Fin 4) SeedField
def seedBase : Ambient →+* SeedAmbient :=
  MvPolynomial.map (algebraMap FX SeedField)
abbrev seedIdeal (I : Ideal Ambient) : Ideal SeedAmbient :=
  I.map seedBase ⊔ Ideal.span {seedLine 0 1}
def seedRestrict (I : Ideal Ambient) : Ambient →+* JetSeedSection I :=
  (Ideal.Quotient.mk (seedIdeal I)).comp seedBase
def seedCoord (I : Ideal Ambient) (i : Fin 4) : JetSeedSection I :=
  Ideal.Quotient.mk (seedIdeal I) (MvPolynomial.X i)
abbrev PrincipalCut {A : Type} [CommRing A] (f : A) :=
  A ⧸ Ideal.span {f}
def functionDegree (k E : Type) [Field k] [Field E] [Algebra k E] (f : E) : ℕ := by
  classical
  exact if Transcendental k f then
    Module.finrank (IntermediateField.adjoin k ({f} : Set E)) E
  else 0
def coordinateDegree (k A : Type) [Field k] [CommRing A] [Algebra k A] [IsDomain A]
    (f : A) : ℕ :=
  functionDegree k (FractionRing A) (algebraMap A (FractionRing A) f)
def lineDegree (k A : Type) [Field k] [CommRing A] [Algebra k A] [IsDomain A]
    (y v : A) : ℕ :=
  functionDegree (RatFunc k) (RatFunc (FractionRing A))
    (RatFunc.C (algebraMap A (FractionRing A) y) +
      RatFunc.X * RatFunc.C (algebraMap A (FractionRing A) v))
structure PoleOrder (k A : Type) [Field k] [CommRing A] [Algebra k A] where
  order : A → ℕ
  constant : ∀ c : k, order (algebraMap k A c) = 0
  add_le : ∀ a b, order (a + b) ≤ max (order a) (order b)
  mul_le : ∀ a b, order (a * b) ≤ order a + order b
structure CurvePoles (k A : Type) [Field k] [CommRing A] [Algebra k A] [IsDomain A]
    (y v : A) where
  count : ℕ
  place : Fin count → PoleOrder k A
  residueDegree : Fin count → ℕ
  degree_eq : ∀ f : A, coordinateDegree k A f =
    ∑ q, (place q).order f * residueDegree q
  line_eq : lineDegree k A y v =
    ∑ q, max ((place q).order y) ((place q).order v) * residueDegree q
end
end K1_14_2_2_7_2
end
section
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_7_2
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 Polynomial
open scoped BigOperators
variable {k A : Type} [Field k] [CommRing A] [Algebra k A]
private theorem PoleOrder.zero (d : PoleOrder k A) : d.order 0 = 0 := by
  simpa using d.constant (0 : k)
private theorem PoleOrder.one (d : PoleOrder k A) : d.order 1 = 0 := by
  simpa using d.constant (1 : k)
private theorem PoleOrder.pow_le (d : PoleOrder k A) (a : A) (n : ℕ) :
    d.order (a ^ n) ≤ n * d.order a := by
  induction n with
  | zero => simp [d.one]
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact (d.mul_le _ _).trans (Nat.add_le_add_right ih _)
private theorem PoleOrder.sum_le (d : PoleOrder k A) {ι : Type*}
    (t : Finset ι) (f : ι → A) (N : ℕ) (h : ∀ i ∈ t, d.order (f i) ≤ N) :
    d.order (∑ i ∈ t, f i) ≤ N := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [d.zero]
  | insert i t hi ih =>
    rw [Finset.sum_insert hi]
    exact (d.add_le _ _).trans (max_le
      (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj)))
private theorem seedCoord_eq (I : Ideal Ambient) :
    seedCoord I 0 =
      algebraMap SeedField (JetSeedSection I) (generic 1) -
        algebraMap SeedField (JetSeedSection I) (generic 0) * seedCoord I 1 := by
  let q := Ideal.Quotient.mk (seedIdeal I)
  have h : q (seedLine 0 1) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  change q (MvPolynomial.X 0 + MvPolynomial.C (generic 0) * MvPolynomial.X 1 -
    MvPolynomial.C (generic 1)) = 0 at h
  rw [map_sub, map_add, map_mul, sub_eq_zero] at h
  exact eq_sub_of_add_eq h
private theorem seedCoord_order_le (I : Ideal Ambient)
    (d : PoleOrder SeedField (JetSeedSection I)) :
    d.order (seedCoord I 0) ≤ d.order (seedCoord I 1) := by
  have hneg : algebraMap SeedField (JetSeedSection I) (-generic 0) * seedCoord I 1 =
      -(algebraMap SeedField (JetSeedSection I) (generic 0) * seedCoord I 1) := by
    rw [map_neg, neg_mul]
  rw [seedCoord_eq, sub_eq_add_neg, ← hneg]
  apply (d.add_le _ _).trans
  apply max_le
  · simp [d.constant]
  · exact (d.mul_le _ _).trans_eq (by rw [d.constant, zero_add])
private def seedCoefficient (I : Ideal Ambient) : Seeds →+* JetSeedSection I :=
  MvPolynomial.eval₂Hom
    ((algebraMap SeedField (JetSeedSection I)).comp (algebraMap FX SeedField))
    ![seedCoord I 0, seedCoord I 1]
private theorem seed_eval (I : Ideal Ambient) (P : Jet) :
    seedRestrict I (toJet P) =
      P.eval₂ (Polynomial.eval₂RingHom (seedCoefficient I) (seedCoord I 2)) (seedCoord I 3) := by
  have hbase : (seedRestrict I).comp MvPolynomial.C =
      (algebraMap SeedField (JetSeedSection I)).comp (algebraMap FX SeedField) := by
    apply RingHom.ext
    intro a
    change Ideal.Quotient.mk (seedIdeal I)
        (MvPolynomial.map (algebraMap FX SeedField) (MvPolynomial.C a : Ambient)) =
      Ideal.Quotient.mk (seedIdeal I) (MvPolynomial.C (algebraMap FX SeedField a))
    rw [MvPolynomial.map_C]
  have hx (i : Fin 4) : seedRestrict I (MvPolynomial.X i) = seedCoord I i := by
    change Ideal.Quotient.mk (seedIdeal I)
        (MvPolynomial.map (algebraMap FX SeedField) (MvPolynomial.X i : Ambient)) =
      Ideal.Quotient.mk (seedIdeal I) (MvPolynomial.X i)
    rw [MvPolynomial.map_X]
  have hseed : ((seedRestrict I).comp rootIncl).comp rootSeeds = seedCoefficient I := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simpa [rootSeeds, rootIncl, seedCoefficient] using RingHom.congr_fun hbase a
    · intro i
      fin_cases i <;> simp [rootSeeds, rootIncl, seedCoefficient, hx]
  have hroot : ((seedRestrict I).comp rootIncl).comp toRoot =
      Polynomial.eval₂RingHom (seedCoefficient I) (seedCoord I 2) := by
    apply Polynomial.ringHom_ext
    · intro f
      simpa [toRoot] using RingHom.congr_fun hseed f
    · simp [toRoot, rootIncl, hx]
  change seedRestrict I (P.eval₂ _ _) = _
  rw [Polynomial.hom_eval₂, ← RingHom.comp_assoc, hroot, hx]
private theorem coefficient_order_le (I : Ideal Ambient)
    (d : PoleOrder SeedField (JetSeedSection I)) (g : Seeds) {u : ℕ}
    (hg : g.totalDegree ≤ u) :
    d.order (seedCoefficient I g) ≤ u * d.order (seedCoord I 1) := by
  classical
  change d.order (g.eval₂ _ _) ≤ _
  rw [MvPolynomial.eval₂_eq']
  apply d.sum_le
  intro m hm
  rw [Fin.prod_univ_two]
  have hm' : m 0 + m 1 ≤ u := by
    have h := (MvPolynomial.le_totalDegree hm).trans hg
    rwa [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at h
  apply (d.mul_le _ _).trans
  simp only [RingHom.comp_apply, d.constant, zero_add, Matrix.cons_val_zero, Matrix.cons_val_one]
  calc
    _ ≤ d.order (seedCoord I 0 ^ m 0) + d.order (seedCoord I 1 ^ m 1) := d.mul_le _ _
    _ ≤ m 0 * d.order (seedCoord I 0) + m 1 * d.order (seedCoord I 1) :=
      Nat.add_le_add (d.pow_le _ _) (d.pow_le _ _)
    _ ≤ m 0 * d.order (seedCoord I 1) + m 1 * d.order (seedCoord I 1) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ (seedCoord_order_le I d)) _
    _ ≤ _ := by simpa only [Nat.add_mul] using Nat.mul_le_mul_right (d.order (seedCoord I 1)) hm'
private theorem jet_monomial_le {B J i j a b : ℕ}
    (hJB : J ≤ B) (hij : i + j ≤ B) (hj : j ≤ J) :
    i * a + j * b ≤ (B - J) * a + J * max a b := by
  have hi : i ≤ B - j := by omega
  have hsub : B - j = (B - J) + (J - j) := by omega
  calc
    i * a + j * b ≤ (B - j) * a + j * b :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ hi) _
    _ = (B - J) * a + ((J - j) * a + j * b) := by rw [hsub, Nat.add_mul, Nat.add_assoc]
    _ ≤ (B - J) * a + ((J - j) * max a b + j * max a b) :=
      Nat.add_le_add_left (Nat.add_le_add (Nat.mul_le_mul_left _ (le_max_left _ _))
        (Nat.mul_le_mul_left _ (le_max_right _ _))) _
    _ = _ := by rw [← Nat.add_mul, Nat.sub_add_cancel hj]
theorem row_pole_le (I : Ideal Ambient) (d : PoleOrder SeedField (JetSeedSection I))
    {s : Shape} {P : Jet} (hJB : s.J ≤ s.B) (hcaps : RowCaps P s) :
    d.order (seedRestrict I (toJet P)) ≤
      s.U * d.order (seedCoord I 1) + (s.B - s.J) * d.order (seedCoord I 2) +
        s.J * max (d.order (seedCoord I 2)) (d.order (seedCoord I 3)) := by
  let x := d.order (seedCoord I 1)
  let y := d.order (seedCoord I 2)
  let v := d.order (seedCoord I 3)
  rw [seed_eval, Polynomial.eval₂_eq_sum, Polynomial.sum]
  apply d.sum_le
  intro j _
  have hsum : d.order ((P.coeff j).eval₂ (seedCoefficient I) (seedCoord I 2) *
      seedCoord I 3 ^ j) ≤ s.U * x + (s.B - s.J) * y + s.J * max y v := by
    rw [Polynomial.eval₂_eq_sum, Polynomial.sum, Finset.sum_mul]
    apply d.sum_le
    intro i hi
    obtain ⟨hij, hj, hdeg⟩ := hcaps j i (Polynomial.mem_support_iff.mp hi)
    calc
      _ ≤ (d.order (seedCoefficient I ((P.coeff j).coeff i)) +
            d.order (seedCoord I 2 ^ i)) + d.order (seedCoord I 3 ^ j) :=
        (d.mul_le _ _).trans (Nat.add_le_add_right (d.mul_le _ _) _)
      _ ≤ (s.U * x + i * y) + j * v :=
        Nat.add_le_add (Nat.add_le_add (coefficient_order_le I d _ hdeg) (d.pow_le _ _))
          (d.pow_le _ _)
      _ ≤ _ := by
        rw [Nat.add_assoc, Nat.add_assoc]
        exact Nat.add_le_add_left (jet_monomial_le hJB hij hj) _
  exact hsum
end
end K1_14_2_2_7_2
end
section
namespace K1_14_2_2_7_2
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_7
open scoped BigOperators Classical Function nonZeroDivisors
def c1 : Prop :=
  ∀ I : Ideal Ambient, Active I →
    seedIdeal I ≠ ⊤ ∧ ringKrullDim (JetSeedSection I) = 1
def c2 : Prop :=
  ∀ (I : Ideal Ambient) [IsDomain (JetSeedSection I)], Active I →
    coordinateDegree SeedField (JetSeedSection I) (seedCoord I 1) = sectionDegree I 0 ∧
    coordinateDegree SeedField (JetSeedSection I) (seedCoord I 2) = sectionDegree I 1 ∧
    lineDegree SeedField (JetSeedSection I) (seedCoord I 2) (seedCoord I 3) =
      sectionDegree I 2
def c3 : Prop :=
  ∀ (ell : ℕ) (k A : Type) [Field k] [CharP k ell] [CommRing A] [Algebra k A] [IsDomain A]
    [Algebra.FiniteType k A], ringKrullDim A = 1 →
    ∀ x y v : A, 0 < coordinateDegree k A x → coordinateDegree k A x < ell →
    Nonempty (CurvePoles k A y v)
def c4 : Prop :=
  ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [IsDomain A]
    [Algebra.FiniteType k A], ringKrullDim A = 1 →
    ∀ f : A, f ≠ 0 →
    Module.finrank k (PrincipalCut f) ≤ coordinateDegree k A f
def c5 : Prop :=
  ∀ Q : Ideal Ambient, Q.IsPrime → seedIdeal Q ≠ ⊤ →
    (seedIdeal Q).IsPrime ∧ (seedIdeal Q).comap seedBase = Q
private theorem seedCut_le {I : Ideal Ambient} {P : Jet} {Q : Ideal Ambient}
    (hQ : Q ∈ cutComponents I P) :
    seedIdeal I ⊔ Ideal.span {seedBase (toJet P)} ≤ seedIdeal Q := by
  have h := (Ideal.mem_minimalPrimesFinset.mp hQ).le
  refine sup_le (sup_le_sup_right (Ideal.map_mono (le_sup_left.trans h)) _) ?_
  apply (Ideal.span_singleton_le_iff_mem _).mpr
  exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _
    (h (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))))
private theorem component_mass_le (h5 : c5) (I : Ideal Ambient) (P : Jet)
    [Module.Finite SeedField (PrincipalCut (seedRestrict I (toJet P)))] :
    curveSeedMass (movingComponents I P) ≤
      Module.finrank SeedField (PrincipalCut (seedRestrict I (toJet P))) := by
  classical
  let S := (movingComponents I P).filter (fun Q => seedIdeal Q ≠ ⊤)
  let G : S → Ideal SeedAmbient := fun Q => seedIdeal Q.val
  let J : Ideal SeedAmbient := seedIdeal I ⊔ Ideal.span {seedBase (toJet P)}
  have he : PrincipalCut (seedRestrict I (toJet P)) ≃ₐ[SeedField] (SeedAmbient ⧸ J) := by
    have hm :
        (Ideal.span {seedBase (toJet P)}).map (Ideal.Quotient.mkₐ SeedField (seedIdeal I)) =
          Ideal.span {seedRestrict I (toJet P)} := by
      rw [Ideal.map_span, Set.image_singleton]
      rfl
    let C (L : Ideal (JetSeedSection I)) :=
      (JetSeedSection I ⧸ L) ≃ₐ[SeedField] (SeedAmbient ⧸ J)
    exact (congrArg C hm).mp (DoubleQuot.quotQuotEquivQuotSupₐ SeedField (seedIdeal I)
      (Ideal.span {seedBase (toJet P)}))
  have : Module.Finite SeedField (SeedAmbient ⧸ J) :=
    Module.Finite.of_surjective he.toLinearEquiv.toLinearMap he.surjective
  have hcut (Q : S) : Q.val ∈ cutComponents I P :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp Q.property).1).1
  have hsurv (Q : S) : seedIdeal Q.val ≠ ⊤ := (Finset.mem_filter.mp Q.property).2
  have hprime (Q : S) : Q.val.IsPrime := (Ideal.mem_minimalPrimesFinset.mp (hcut Q)).isPrime
  have hcomp (Q : S) : J ≤ G Q := seedCut_le (hcut Q)
  let project (Q : S) := Ideal.Quotient.factorₐ SeedField (hcomp Q)
  let : ∀ Q : S, Module.Finite SeedField (SeedAmbient ⧸ G Q) := fun Q =>
    Module.Finite.of_surjective (project Q).toLinearMap (Ideal.Quotient.factor_surjective (hcomp Q))
  let : ∀ Q : S, Module.Free SeedField (SeedAmbient ⧸ G Q) := fun _ => inferInstance
  have hmax (Q : S) : (G Q).IsMaximal := by
    have : (G Q).IsPrime := (h5 Q.val (hprime Q) (hsurv Q)).1
    have : Algebra.IsIntegral SeedField (SeedAmbient ⧸ G Q) :=
      Algebra.IsIntegral.of_finite ..
    exact Ideal.Quotient.maximal_of_isField (G Q)
      (isField_of_isIntegral_of_isField' (S := SeedAmbient ⧸ G Q) (Field.toIsField SeedField))
  have hpairs : Pairwise (IsCoprime on G) := by
    intro Q R hne
    have := hmax Q
    have := hmax R
    apply Ideal.isCoprime_of_isMaximal
    intro h
    apply hne
    apply Subtype.ext
    calc
      Q.val = (G Q).comap seedBase := (h5 Q.val (hprime Q) (hsurv Q)).2.symm
      _ = (G R).comap seedBase := by rw [h]
      _ = R.val := (h5 R.val (hprime R) (hsurv R)).2
  let f := LinearMap.pi fun Q : S => (project Q).toLinearMap
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨r, hr⟩ := Ideal.pi_quotient_surjective hpairs a
    refine ⟨Ideal.Quotient.mk J r, funext fun Q => ?_⟩
    exact hr Q
  have hdim := LinearMap.finrank_le_finrank_of_surjective (f := f) hf
  rw [Module.finrank_pi_fintype] at hdim
  rw [he.toLinearEquiv.finrank_eq]
  have hmass : curveSeedMass (movingComponents I P) =
      ∑ Q : S, Module.finrank SeedField (SeedAmbient ⧸ G Q) := by
    calc
      _ = ∑ Q ∈ S, Module.finrank SeedField (JetSeedSection Q) := by
        unfold curveSeedMass
        symm
        apply Finset.sum_subset (Finset.filter_subset ..)
        intro Q hQ hmissing
        have htop : seedIdeal Q = ⊤ := by simpa [S, hQ] using hmissing
        change Module.finrank SeedField (SeedAmbient ⧸ seedIdeal Q) = 0
        rw [htop]
        have : Subsingleton (SeedAmbient ⧸ (⊤ : Ideal SeedAmbient)) :=
          Ideal.Quotient.subsingleton_iff.mpr rfl
        exact Module.finrank_eq_zero_of_subsingleton _ _
      _ = _ := (Finset.sum_attach S
        (fun Q => Module.finrank SeedField (JetSeedSection Q))).symm
  rw [hmass]
  exact hdim
private theorem finite_principalCut (k A : Type) [Field k] [CommRing A]
    [Algebra k A] [IsDomain A] [Algebra.FiniteType k A]
    (hdim : ringKrullDim A = 1) {f : A} (hf : f ≠ 0) :
    Module.Finite k (PrincipalCut f) := by
  apply (Module.finite_iff_krullDimLE_zero k (PrincipalCut f)).mpr
  rw [Ring.krullDimLE_iff, Nat.cast_zero,
    ← ENat.WithBot.add_le_add_one_right_iff, zero_add]
  exact (ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (mem_nonZeroDivisors_iff_ne_zero.mpr hf)).trans_eq hdim
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5) :
    K1_14_2_2_7.c2 := by
  classical
  intro s I P hJB hI hcaps hP
  obtain ⟨hn, hdim⟩ := h1 I hI
  obtain ⟨hp, hc⟩ := h5 I hI.prime hn
  have : (seedIdeal I).IsPrime := hp
  have : IsDomain (JetSeedSection I) :=
    inferInstanceAs (IsDomain (SeedAmbient ⧸ seedIdeal I))
  let f := seedRestrict I (toJet P)
  have hf : f ≠ 0 := by
    intro h
    apply hP
    rw [← hc]
    change seedBase (toJet P) ∈ seedIdeal I
    exact Ideal.Quotient.eq_zero_iff_mem.mp h
  obtain ⟨ha, hy, hz⟩ := h2 I hI
  have : CharP SeedField p := charP_of_injective_ringHom
    ((algebraMap FX SeedField).comp seedEmbedding).injective p
  obtain ⟨D⟩ := h3 p SeedField (JetSeedSection I) hdim
    (seedCoord I 1) (seedCoord I 2) (seedCoord I 3)
    (by rw [ha]; exact hI.seed_size.1) (by rw [ha]; exact hI.seed_size.2)
  have hlength := h4 SeedField (JetSeedSection I) hdim f hf
  have : Module.Finite SeedField (PrincipalCut f) :=
    finite_principalCut SeedField (JetSeedSection I) hdim hf
  have hpoles : coordinateDegree SeedField (JetSeedSection I) f ≤
      s.U * sectionDegree I 0 + (s.B - s.J) * sectionDegree I 1 +
        s.J * sectionDegree I 2 := by
    rw [← ha, ← hy, ← hz, D.degree_eq f, D.degree_eq (seedCoord I 1),
      D.degree_eq (seedCoord I 2), D.line_eq]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro q _
    have hrow := Nat.mul_le_mul_right (D.residueDegree q)
      (row_pole_le I (D.place q) hJB hcaps)
    simpa only [Nat.add_mul, Nat.mul_assoc] using hrow
  refine (component_mass_le h5 I P).trans (hlength.trans (hpoles.trans_eq ?_))
  simp [dot, weight, Fin.sum_univ_succ, Nat.add_assoc]
end
end K1_14_2_2_7_2
end
section
namespace K1_14_2_2_7_4
noncomputable section
open K1_14 K1_14_2
open MvPolynomial
abbrev CurvePoly (k : Type) [Field k] := MvPolynomial (Option (Fin 2)) k
abbrev LineField (k : Type) [Field k] := FractionRing (MvPolynomial (Fin 2) k)
def lineParameter (k : Type) [Field k] (i : Fin 2) : LineField k :=
  algebraMap (MvPolynomial (Fin 2) k) (LineField k) (MvPolynomial.X i)
def jetSliceMap : Ambient →+* CurvePoly SeedField :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (algebraMap FX SeedField))
    ![MvPolynomial.X (some 0), MvPolynomial.X (some 1),
      MvPolynomial.C (generic 1) - MvPolynomial.C (generic 0) * MvPolynomial.X none,
      MvPolynomial.X none]
def jetSliceIdeal (I : Ideal Ambient) : Ideal (CurvePoly SeedField) := I.map jetSliceMap
abbrev JetSlice (I : Ideal Ambient) := CoordinateRing (jetSliceIdeal I)
def ambientCoord (I : Ideal Ambient) (i : Fin 4) : CoordinateRing I :=
  Ideal.Quotient.mk I (MvPolynomial.X i)
def seedFibreIdeal {k : Type} [Field k] (D : Ideal (CurvePoly k)) :
    Ideal (CurvePoly (LineField k)) :=
  D.map (MvPolynomial.map (algebraMap k (LineField k))) ⊔ Ideal.span
    {MvPolynomial.X (some 0) + MvPolynomial.C (lineParameter k 0) *
      MvPolynomial.X (some 1) - MvPolynomial.C (lineParameter k 1)}
abbrev SeedFibre {k : Type} [Field k] (D : Ideal (CurvePoly k)) :=
  CoordinateRing (seedFibreIdeal D)
abbrev VField (k : Type) [Field k] := FractionRing (Polynomial k)
def vFibreMap (k : Type) [Field k] : CurvePoly k →+* MvPolynomial (Fin 2) (VField k) :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (algebraMap k (VField k)))
    (fun i => i.elim
      (MvPolynomial.C (algebraMap (Polynomial k) (VField k) Polynomial.X)) MvPolynomial.X)
abbrev VFibre {k : Type} [Field k] (D : Ideal (CurvePoly k)) :=
  CoordinateRing (D.map (vFibreMap k))
end
end K1_14_2_2_7_4
end
section
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_7_4
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_7
open MvPolynomial
private def seedCoeffMap : Seeds →+* CurvePoly SeedField :=
  (MvPolynomial.rename (Option.some : Fin 2 → Option (Fin 2))).toRingHom.comp
    (MvPolynomial.map (algebraMap FX SeedField))
private abbrev slicedY : CurvePoly SeedField :=
  MvPolynomial.C (generic 1) - MvPolynomial.C (generic 0) * MvPolynomial.X none
private abbrev slicedV : CurvePoly SeedField := MvPolynomial.X none
private theorem slicedRoot (q : Equation) :
    jetSliceMap (rootIncl (toRoot q)) = q.eval₂ seedCoeffMap slicedY := by
  have hseed : (jetSliceMap.comp rootIncl).comp rootSeeds = seedCoeffMap := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [jetSliceMap, rootIncl, rootSeeds, seedCoeffMap, RingHom.comp_apply]
    · intro i
      fin_cases i <;> simp [jetSliceMap, rootIncl, rootSeeds, seedCoeffMap, RingHom.comp_apply]
  change (jetSliceMap.comp rootIncl) (q.eval₂ rootSeeds (MvPolynomial.X 2)) = _
  rw [Polynomial.hom_eval₂, hseed]
  simp [jetSliceMap, rootIncl, RingHom.comp_apply]
private abbrev Bidegree (b u : ℕ) := MvPolynomial.restrictBidegree (Fin 2) SeedField b u
private theorem C_bidegree (x : SeedField) {b u : ℕ} : MvPolynomial.C x ∈ Bidegree b u := by
  rw [mem_restrictBidegree_iff_weightedTotalDegree_le]
  simp
private theorem X_bidegree (i : Option (Fin 2)) :
    MvPolynomial.X i ∈ Bidegree (i.elim 1 fun _ => 0) (i.elim 0 fun _ => 1) := by
  rw [mem_restrictBidegree]
  intro m hm
  rw [support_X, Finset.mem_singleton] at hm
  subst m
  cases i <;> simp [Finsupp.some_single_none, Finsupp.some_single_some]
private theorem slicedY_bidegree : slicedY ∈ Bidegree 1 0 := by
  apply (Bidegree 1 0).sub_mem (C_bidegree _)
  exact mul_mem_restrictBidegree (C_bidegree (b := 0) (u := 0) _) (X_bidegree none)
private theorem pow_bidegree {f : CurvePoly SeedField} {b u : ℕ}
    (hf : f ∈ Bidegree b u) (i : ℕ) : f ^ i ∈ Bidegree (i * b) (i * u) := by
  induction i with
  | zero => simpa only [pow_zero, Nat.zero_mul, ← MvPolynomial.C_1] using
      (C_bidegree (b := 0) (u := 0) 1)
  | succ i ih =>
    rw [pow_succ, Nat.succ_mul, Nat.succ_mul]
    exact mul_mem_restrictBidegree ih hf
private theorem seedCoeff_bidegree (a : Seeds) : seedCoeffMap a ∈ Bidegree 0 a.totalDegree := by
  rw [mem_restrictBidegree_iff_weightedTotalDegree_le]
  unfold seedCoeffMap
  rw [RingHom.comp_apply]
  let q := MvPolynomial.map (algebraMap FX SeedField) a
  change weightedTotalDegree _ (MvPolynomial.rename Option.some q) ≤ 0 ∧
    weightedTotalDegree _ (MvPolynomial.rename Option.some q) ≤ a.totalDegree
  rw [weightedTotalDegree_rename_of_injective (Option.some_injective (Fin 2)),
    weightedTotalDegree_rename_of_injective (Option.some_injective (Fin 2))]
  constructor
  · change weightedTotalDegree (0 : Fin 2 → ℕ) (MvPolynomial.map (algebraMap FX SeedField) a) ≤ 0
    simp [weightedTotalDegree, Finsupp.weight_apply, Finsupp.sum]
  · change weightedTotalDegree (1 : Fin 2 → ℕ) (MvPolynomial.map (algebraMap FX SeedField) a) ≤ _
    rw [weightedTotalDegree_one]
    exact Finset.sup_mono (MvPolynomial.support_map_subset _ _)
theorem sliced_row_bidegree {P : Jet} {s : Shape} (hcaps : RowCaps P s) :
    jetSliceMap (toJet P) ∈ MvPolynomial.restrictBidegree (Fin 2) SeedField s.B s.U := by
  classical
  change jetSliceMap (P.eval₂ (rootIncl.comp toRoot) (MvPolynomial.X 3)) ∈ _
  have hV : jetSliceMap (MvPolynomial.X 3) = slicedV := by simp [jetSliceMap]
  rw [Polynomial.hom_eval₂, hV, Polynomial.eval₂_eq_sum]
  apply (Bidegree s.B s.U).sum_mem
  intro j _
  simp only [RingHom.comp_apply, slicedRoot, Polynomial.eval₂_eq_sum, Polynomial.sum, Finset.sum_mul]
  apply (Bidegree s.B s.U).sum_mem
  intro i hi
  let a := (P.coeff j).coeff i
  obtain ⟨hB, _, hU⟩ := hcaps j i (Polynomial.mem_support_iff.mp hi)
  have hterm := mul_mem_restrictBidegree
    (mul_mem_restrictBidegree (seedCoeff_bidegree a) (pow_bidegree slicedY_bidegree i))
    (pow_bidegree (X_bidegree none) j)
  have hsmall : seedCoeffMap a * slicedY ^ i * slicedV ^ j ∈ Bidegree (i + j) a.totalDegree := by
    simpa using hterm
  exact mem_restrictBidegree_mono hsmall hB hU
theorem active_ordinate {I : Ideal Ambient} (hI : Active I) :
    ¬ IsAlgebraic FX (ambientCoord I 2) := by
  apply transcendental_iff_injective.mpr
  have h : (Polynomial.aeval (ambientCoord I 2) : Polynomial FX →ₐ[FX] CoordinateRing I).toRingHom =
      (Ideal.Quotient.mk I).comp ordinateIncl := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [ordinateIncl, RingHom.comp_apply]
      exact (Ideal.Quotient.mk_algebraMap (R₁ := FX) I a).symm
    · simp [ambientCoord, ordinateIncl, RingHom.comp_apply]
  change Function.Injective
    (Polynomial.aeval (ambientCoord I 2) : Polynomial FX →ₐ[FX] CoordinateRing I).toRingHom
  rw [h]
  exact hI.ordinate_dominant
private theorem dim_zero_of_algebraic_coordinates {k σ : Type} [Field k]
    (Q : Ideal (MvPolynomial σ k)) [Q.IsPrime]
    (halg : ∀ i, IsAlgebraic k (Ideal.Quotient.mk Q (MvPolynomial.X i))) :
    ringKrullDim (CoordinateRing Q) = 0 := by
  let x (i : σ) : CoordinateRing Q := Ideal.Quotient.mk Q (MvPolynomial.X i)
  have heq : MvPolynomial.aeval x = Ideal.Quotient.mkₐ k Q := by
    apply MvPolynomial.algHom_ext
    intro i
    exact MvPolynomial.aeval_X x i
  have htop : Algebra.adjoin k (Set.range x) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval k x, heq, AlgHom.range_eq_top]
    exact Ideal.Quotient.mk_surjective
  have hi : Algebra.IsAlgebraic k (CoordinateRing Q) := by
    apply Algebra.isAlgebraic_iff.mpr
    rw [← htop, Algebra.isAlgebraic_adjoin_iff]
    rintro _ ⟨i, rfl⟩
    exact halg i
  exact ringKrullDim_eq_zero_of_isField
    (isField_of_isIntegral_of_isField' (S := CoordinateRing Q) (Field.toIsField k))
theorem constant_curve_jets {Q : Ideal Ambient} [Q.IsPrime]
    (hdim : ringKrullDim (CoordinateRing Q) = 1) (hseed : ConstantSeed Q) :
    ¬ IsAlgebraic FX (ambientCoord Q 2) ∨ ¬ IsAlgebraic FX (ambientCoord Q 3) := by
  by_contra! h
  have halg (i : Fin 4) : IsAlgebraic FX (ambientCoord Q i) := by
    fin_cases i
    · exact hseed 0
    · exact hseed 1
    · exact h.1
    · exact h.2
  have hzero : ringKrullDim (CoordinateRing Q) = 0 := dim_zero_of_algebraic_coordinates Q halg
  exact one_ne_zero (hdim.symm.trans hzero)
theorem card_le_cut_finrank {k R ι : Type} [Field k] [CommRing R] [Algebra k R] [Fintype ι]
    (C : Ideal R) [Module.Finite k (R ⧸ C)] (M : ι → Ideal R) (hM : ∀ i, (M i).IsMaximal)
    (hCM : ∀ i, C ≤ M i) (hDistinct : Function.Injective M) :
    Fintype.card ι ≤ Module.finrank k (R ⧸ C) := by
  let project : R ⧸ C →ₗ[k] ((i : ι) → R ⧸ M i) :=
    LinearMap.pi fun i => (Ideal.Quotient.factorₐ k (hCM i)).toLinearMap
  have hpair : Pairwise (fun i j => IsCoprime (M i) (M j)) := fun i j hij =>
    Ideal.isCoprime_iff_sup_eq.mpr ((hM i).coprime_of_ne (hM j) (fun h => hij (hDistinct h)))
  have hsurj : Function.Surjective project := by
    intro d
    obtain ⟨r, hr⟩ := Ideal.pi_quotient_surjective hpair d
    exact ⟨Ideal.Quotient.mk C r, funext hr⟩
  let _ := Module.Finite.of_surjective project hsurj
  let includeScalars : (ι → k) →ₗ[k] ((i : ι) → R ⧸ M i) :=
    LinearMap.pi fun i => (Algebra.linearMap k (R ⧸ M i)).comp (LinearMap.proj i)
  have hinj : Function.Injective includeScalars := by
    intro a b hab
    funext i
    have : Nontrivial (R ⧸ M i) := Ideal.Quotient.nontrivial_iff.mpr (hM i).ne_top
    exact (algebraMap k (R ⧸ M i)).injective (congrFun hab i)
  have hle := (LinearMap.finrank_le_finrank_of_injective hinj).trans
    (LinearMap.finrank_le_finrank_of_surjective hsurj)
  simpa only [Module.finrank_fintype_fun_eq_card] using hle
end
end K1_14_2_2_7_4
end
section
set_option autoImplicit false
namespace K1_14_2_2_7_2_2
open K1_14_2 K1_14_2_2 K1_14_2_2_7_2
open scoped Polynomial RatFunc TensorProduct
noncomputable section
attribute [local instance] Polynomial.algebra
abbrev GenericFibre (k A : Type) [Field k] [CommRing A] [Algebra k A] (x : A) :=
  letI : Algebra k[X] A := (Polynomial.aeval x : k[X] →ₐ[k] A).toRingHom.toAlgebra
  RatFunc k ⊗[k[X]] A
abbrev RationalBaseChange (k A : Type) [Field k] [CommRing A] [Algebra k A] :=
  RatFunc k ⊗[k] A
abbrev SlopeRing (I : Ideal Ambient) := RationalBaseChange SeedField (JetSeedSection I)
def rationalLine (k A : Type) [Field k] [CommRing A] [Algebra k A] (y v : A) :
    RationalBaseChange k A :=
  (1 ⊗ₜ[k] y) + (RatFunc.X ⊗ₜ[k] v)
abbrev jetForm (I : Ideal Ambient) : SlopeRing I :=
  rationalLine SeedField (JetSeedSection I) (seedCoord I 2) (seedCoord I 3)
open Algebra.TensorProduct in
def rationalBaseChangeMap (k A E : Type) [Field k] [CommRing A] [Algebra k A]
    [Field E] [Algebra k E] [Algebra A E] [IsScalarTower k A E] :
    RationalBaseChange k A →ₐ[RatFunc k] RatFunc E :=
  lift (Algebra.ofId _ _) (IsScalarTower.toAlgHom k A _) fun _ _ => Commute.all _ _
theorem rationalBaseChangeMap_tmul (k A E : Type) [Field k] [CommRing A] [Algebra k A]
    [Field E] [Algebra k E] [Algebra A E] [IsScalarTower k A E] (r : RatFunc k) (a : A) :
    rationalBaseChangeMap k A E (r ⊗ₜ[k] a) =
      algebraMap (RatFunc k) (RatFunc E) r * RatFunc.C (algebraMap A E a) := by
  simp only [rationalBaseChangeMap, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply,
    IsScalarTower.toAlgHom_apply, IsScalarTower.algebraMap_apply A E (RatFunc E),
    RatFunc.algebraMap_eq_C]
theorem rationalBaseChange_scalar_X (k E : Type) [Field k] [Field E] [Algebra k E] :
    algebraMap (RatFunc k) (RatFunc E) RatFunc.X = RatFunc.X := by
  change IsFractionRing.lift (FaithfulSMul.algebraMap_injective (Polynomial k) (RatFunc E))
    (algebraMap (Polynomial k) (RatFunc k) Polynomial.X) = _
  rw [IsFractionRing.lift_algebraMap]
  change algebraMap (Polynomial E) (RatFunc E) (Polynomial.map (algebraMap k E) Polynomial.X) = _
  rw [Polynomial.map_X, RatFunc.algebraMap_X]
end
end K1_14_2_2_7_2_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 8
namespace K1_14_2_2_7_2_2
open scoped Polynomial RatFunc TensorProduct nonZeroDivisors
open IsScalarTower
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial Polynomial.algebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra
private abbrev OnePoly (R : Type) [CommRing R] := MvPolynomial Unit R
private local instance (priority := high) onePolyToRatFunc (R : Type) [CommRing R] [IsDomain R] :
    Algebra (OnePoly R) (RatFunc R) :=
  Algebra.compHom _ (MvPolynomial.uniqueAlgEquiv R Unit).toRingEquiv.toRingHom
private local instance (priority := high) (R : Type) [CommRing R] [IsDomain R] :
    SMul (OnePoly R) (RatFunc R) := (onePolyToRatFunc R).toSMul
private theorem onePoly_C (R : Type) [CommRing R] [IsDomain R] (a : R) :
    algebraMap (OnePoly R) (RatFunc R) (MvPolynomial.C a) = RatFunc.C a := by
  change algebraMap (Polynomial R) (RatFunc R) (MvPolynomial.uniqueAlgEquiv R Unit (MvPolynomial.C a)) = _
  simp [MvPolynomial.uniqueAlgEquiv_apply]
private theorem onePoly_X (R : Type) [CommRing R] [IsDomain R] :
    algebraMap (OnePoly R) (RatFunc R) (MvPolynomial.X ()) = RatFunc.X := by
  change algebraMap (Polynomial R) (RatFunc R) (MvPolynomial.uniqueAlgEquiv R Unit (MvPolynomial.X ())) = _
  simp [MvPolynomial.uniqueAlgEquiv_apply]
private local instance (R : Type) [CommRing R] [IsDomain R] :
    IsScalarTower R (OnePoly R) (RatFunc R) :=
  IsScalarTower.of_algebraMap_eq fun a => (onePoly_C R a).symm
private local instance (R : Type) [CommRing R] [IsDomain R] : IsFractionRing (OnePoly R) (RatFunc R) :=
  IsFractionRing.of_ringEquiv_left (MvPolynomial.uniqueAlgEquiv R Unit).toRingEquiv fun _ => rfl
private theorem fraction_polynomial_coefficients (A E : Type) [CommRing A] [IsDomain A]
    [Field E] [Algebra A E] [IsFractionRing A E] :
    let : Algebra (OnePoly A) (RatFunc E) := Algebra.compHom _ (algebraMap (OnePoly A) (OnePoly E))
    IsFractionRing (OnePoly A) (RatFunc E) := by
  let P := OnePoly A
  let Q := OnePoly E
  let M : Submonoid P := (nonZeroDivisors A).map MvPolynomial.C
  let : IsLocalization M Q := inferInstance
  let : Algebra P (RatFunc E) := Algebra.compHom _ (algebraMap P Q)
  let := IsScalarTower.of_algebraMap_eq' (R := P) (S := Q) (A := RatFunc E) rfl
  have hinj : Function.Injective (algebraMap P Q) :=
    MvPolynomial.map_injective _ (IsFractionRing.injective A E)
  have hm : Q⁰.comap (algebraMap P Q) = P⁰ := by
    ext x
    simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero, map_ne_zero_iff _ hinj]
  change IsLocalization P⁰ (RatFunc E)
  rw [← hm]
  exact IsLocalization.localization_localization_isLocalization_of_has_all_units M Q⁰ (RatFunc E)
    (fun _ hu => hu.mem_nonZeroDivisors)
theorem rationalBaseChange_fractionRing (k A E : Type) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Field E] [Algebra A E] [Algebra k E] [IsScalarTower k A E] [IsFractionRing A E]
    (f : RationalBaseChange k A →ₐ[RatFunc k] RatFunc E)
    (hf : ∀ a : A, f (1 ⊗ₜ[k] a) = RatFunc.C (algebraMap A E a)) :
    let : Algebra (RationalBaseChange k A) (RatFunc E) := f.toRingHom.toAlgebra
    IsFractionRing (RationalBaseChange k A) (RatFunc E) := by
  let S := RationalBaseChange k A
  let N := RatFunc E
  let P := OnePoly A
  let R := OnePoly k
  let B := RatFunc k
  let : Algebra A S := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower k A S := Algebra.TensorProduct.right_isScalarTower
  let toS : P →ₐ[A] S := MvPolynomial.aeval fun _ => algebraMap B S RatFunc.X
  let : Algebra P S := toS.toRingHom.toAlgebra
  let : IsScalarTower A P S := .of_algebraMap_eq fun a => (toS.commutes a).symm
  let : Algebra R S := Algebra.compHom S (algebraMap R B)
  let := IsScalarTower.of_algebraMap_eq' (R := R) (S := B) (A := S) rfl
  let : IsScalarTower k P S := IsScalarTower.of_algebraMap_eq fun c => by
    rw [algebraMap_apply k A S, algebraMap_apply k A P, algebraMap_apply A P S]
  let := IsScalarTower.of_algebraMap_eq' (R := R) (S := P) (A := S) <| by
    apply MvPolynomial.ringHom_ext
    · intro c
      rw [RingHom.comp_apply, MvPolynomial.algebraMap_def, MvPolynomial.map_C]
      change algebraMap B S (algebraMap R B (MvPolynomial.C c)) =
        toS (MvPolynomial.C (algebraMap k A c))
      rw [onePoly_C, ← RatFunc.algebraMap_eq_C, ← algebraMap_apply k B S]
      change algebraMap k S c = toS (algebraMap A P (algebraMap k A c))
      rw [toS.commutes, ← algebraMap_apply k A S]
    · intro i
      cases i
      rw [RingHom.comp_apply, MvPolynomial.algebraMap_def, MvPolynomial.map_X]
      change algebraMap B S (algebraMap R B (MvPolynomial.X ())) = toS (MvPolynomial.X ())
      rw [onePoly_X, show toS (MvPolynomial.X ()) = _ from MvPolynomial.aeval_X _ _]
  let : Algebra.IsPushout R P B S :=
    ((Algebra.IsPushout.comp_iff (T := B) k R A P).mp inferInstance).symm
  let M := Algebra.algebraMapSubmonoid P (nonZeroDivisors R)
  let : IsLocalization M S :=
    (Algebra.isLocalization_iff_isPushout (nonZeroDivisors R) B).mpr inferInstance
  let : Algebra S N := f.toRingHom.toAlgebra
  let : Algebra P N := Algebra.compHom N (algebraMap P (OnePoly E))
  let : IsFractionRing P N := fraction_polynomial_coefficients A E
  let := IsScalarTower.of_algebraMap_eq' (R := P) (S := S) (A := N) <| by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply]
      change algebraMap (OnePoly E) N (MvPolynomial.map (algebraMap A E) (MvPolynomial.C a)) =
        f (toS (MvPolynomial.C a))
      rw [MvPolynomial.map_C]
      change algebraMap (OnePoly E) N (MvPolynomial.C (algebraMap A E a)) = f (toS (MvPolynomial.C a))
      rw [onePoly_C, show toS (MvPolynomial.C a) = 1 ⊗ₜ[k] a from toS.commutes a, hf]
    · intro i
      cases i
      simp only [RingHom.comp_apply]
      change algebraMap (OnePoly E) N (MvPolynomial.map (algebraMap A E) (MvPolynomial.X ())) =
        f (toS (MvPolynomial.X ()))
      rw [MvPolynomial.map_X]
      change algebraMap (OnePoly E) N (MvPolynomial.X ()) = f (toS (MvPolynomial.X ()))
      rw [onePoly_X, show toS (MvPolynomial.X ()) = _ from MvPolynomial.aeval_X _ _, f.commutes,
        rationalBaseChange_scalar_X]
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M S N
end
end K1_14_2_2_7_2_2
end
section
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_7_4
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_7
def c1 : Prop :=
  ∀ (I : Ideal Ambient) (d : ℕ), I.IsPrime →
    ringKrullDim (CoordinateRing I) = ((d + 1 : ℕ) : WithBot ℕ∞) →
    (¬ IsAlgebraic FX (ambientCoord I 2) ∨ ¬ IsAlgebraic FX (ambientCoord I 3)) →
    (jetSliceIdeal I).IsPrime ∧
    ringKrullDim (JetSlice I) = (d : WithBot ℕ∞) ∧
    (jetSliceIdeal I).comap jetSliceMap = I
def c2 : Prop :=
  ∀ (I : Ideal Ambient), Module.Finite SectionField (OverMixed I) →
    Module.Finite (LineField SeedField) (SeedFibre (jetSliceIdeal I)) ∧
    Module.finrank (LineField SeedField) (SeedFibre (jetSliceIdeal I)) ≤ sectionDegree I 2
def c3 : Prop :=
  ∀ (I : Ideal Ambient), Module.Finite SeedField (OverJets I) →
    Module.Finite (VField SeedField) (VFibre (jetSliceIdeal I)) ∧
    Module.finrank (VField SeedField) (VFibre (jetSliceIdeal I)) ≤ sectionDegree I 3
def c4 : Prop :=
  ∀ (k : Type) [Field k] (q : ℕ) [CharP k q] (D : Ideal (CurvePoly k)) (f : CurvePoly k) (u b : ℕ),
    D.IsPrime → ringKrullDim (CoordinateRing D) = 1 → f ∉ D →
    f ∈ MvPolynomial.restrictBidegree (Fin 2) k b u →
    Module.Finite (LineField k) (SeedFibre D) → Module.Finite (VField k) (VFibre D) →
    Module.finrank (LineField k) (SeedFibre D) < q →
    Module.finrank (VField k) (VFibre D) < q →
    Module.Finite k (CoordinateRing (D ⊔ Ideal.span {f})) ∧
    Module.finrank k (CoordinateRing (D ⊔ Ideal.span {f})) ≤
      u * Module.finrank (LineField k) (SeedFibre D) +
      b * Module.finrank (VField k) (VFibre D)
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) : K1_14_2_2_7.c4 := by
  classical
  intro s I P _ hI hcaps hP
  obtain ⟨hprime, hdim, hcomap⟩ := h1 I 1 hI.prime hI.dimension (Or.inl (active_ordinate hI))
  let f := jetSliceMap (toJet P)
  let C := jetSliceIdeal I ⊔ Ideal.span {f}
  have hf : f ∉ jetSliceIdeal I := by
    intro h
    apply hP
    rw [← hcomap]
    exact h
  obtain ⟨hseedFinite, hseed⟩ := h2 I hI.mixed_finite
  obtain ⟨hvFinite, hv⟩ := h3 I hI.jet_finite
  have : CharP SeedField p := charP_of_injective_ringHom
    ((algebraMap FX SeedField).comp seedEmbedding).injective p
  obtain ⟨hfinite, hlength⟩ := h4 SeedField p (jetSliceIdeal I) f s.U s.B hprime hdim hf
    (sliced_row_bidegree hcaps) hseedFinite hvFinite
    (hseed.trans_lt hI.mixed_lt) (hv.trans_lt hI.jet_lt)
  have : Module.Finite SeedField (CoordinateRing C) := hfinite
  let S := constantComponents I P
  let M (Q : S) := jetSliceIdeal Q.val
  have hmem (Q : S) : Q.val ∈ cutComponents I P ∧ ConstantSeed Q.val :=
    Finset.mem_filter.mp Q.property
  have hgeom (Q : S) : (M Q).IsPrime ∧
      ringKrullDim (CoordinateRing (M Q)) = 0 ∧ (M Q).comap jetSliceMap = Q.val := by
    obtain ⟨hp, hd⟩ := cutComponent_curve hI hP (hmem Q).1
    have : Q.val.IsPrime := hp
    exact h1 Q.val 0 hp hd (constant_curve_jets hd (hmem Q).2)
  have hmax (Q : S) : (M Q).IsMaximal := by
    obtain ⟨hp, hd, _⟩ := hgeom Q
    have : (M Q).IsPrime := hp
    have : Ring.KrullDimLE 0 (CoordinateRing (M Q)) :=
      Ring.krullDimLE_iff.mpr (by rw [hd, Nat.cast_zero])
    exact Ideal.Quotient.maximal_of_isField _ Ring.KrullDimLE.isField_of_isDomain
  have hle (Q : S) : C ≤ M Q := by
    have hmin : (I ⊔ Ideal.span {toJet P}).IsMinimalPrime Q.val :=
      Ideal.mem_minimalPrimesFinset.mp (hmem Q).1
    apply sup_le
    · exact Ideal.map_mono (le_sup_left.trans hmin.le)
    · have hPQ : toJet P ∈ Q.val := hmin.le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      exact (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem jetSliceMap hPQ)
  have hinj : Function.Injective M := by
    intro Q R h
    apply Subtype.ext
    exact (hgeom Q).2.2.symm.trans
      ((congrArg (Ideal.comap jetSliceMap) h).trans (hgeom R).2.2)
  calc
    S.card = Fintype.card S := (Fintype.card_coe S).symm
    _ ≤ Module.finrank SeedField (CoordinateRing C) := card_le_cut_finrank C M hmax hle hinj
    _ ≤ s.U * Module.finrank (LineField SeedField) (SeedFibre (jetSliceIdeal I)) +
        s.B * Module.finrank (VField SeedField) (VFibre (jetSliceIdeal I)) := hlength
    _ ≤ s.U * sectionDegree I 2 + s.B * sectionDegree I 3 :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hseed) (Nat.mul_le_mul_left _ hv)
    _ = dot (weight s 2) (sectionDegree I) := by
      simp [dot, weight, Fin.sum_univ_four]
end
end K1_14_2_2_7_4
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_7_2_2
open K1_14_2_2_7_2 Polynomial
open scoped Polynomial TensorProduct nonZeroDivisors
open scoped IntermediateField.algebraAdjoinAdjoin
noncomputable section
private theorem functionDegree_eq_polynomial_finrank
    (k E : Type) [Field k] [Field E] [Algebra k E] (x : E) :
    let : Algebra k[X] E := (aeval x : k[X] →ₐ[k] E).toRingHom.toAlgebra
    functionDegree k E x = Module.finrank k[X] E := by
  classical
  let : Algebra k[X] E := (aeval x : k[X] →ₐ[k] E).toRingHom.toAlgebra
  by_cases hx : Transcendental k x
  · rw [functionDegree, ite_eq_left hx]
    let B := Algebra.adjoin k ({x} : Set E)
    let F := IntermediateField.adjoin k ({x} : Set E)
    calc
      Module.finrank F E = Module.finrank B E := IsFractionRing.finrank_right_eq B F E
      _ = Module.finrank k[X] E := by
        symm
        refine Algebra.finrank_eq_of_equiv_equiv
          (Polynomial.algEquivOfTranscendental k x hx).toRingEquiv (RingEquiv.refl E) ?_
        apply RingHom.ext
        intro p
        change ((Polynomial.algEquivOfTranscendental k x hx) p : E) = aeval x p
        simp
  · rw [functionDegree, ite_eq_right hx]
    obtain ⟨p, hp, hpx⟩ := not_not.mp hx
    have hz : Module.rank k[X] E = 0 := rank_eq_zero_iff.mpr fun z =>
      ⟨p, hp, by change aeval x p * z = 0; rw [hpx, zero_mul]⟩
    simp [Module.finrank, hz]
theorem genericFibre_length
    (k A E : Type) [Field k] [CommRing A] [Algebra k A] [Field E]
    [Algebra A E] [Algebra k E] [IsScalarTower k A E] [IsFractionRing A E] (x : A) :
    functionDegree k E (algebraMap A E x) = Module.finrank (RatFunc k) (GenericFibre k A x) := by
  let : Algebra k[X] A := (aeval x : k[X] →ₐ[k] A).toRingHom.toAlgebra
  let : Algebra k[X] E := (aeval (algebraMap A E x) : k[X] →ₐ[k] E).toRingHom.toAlgebra
  let : IsScalarTower k[X] A E := IsScalarTower.of_algebraMap_eq fun p =>
    aeval_algebraMap_apply E x p
  let G := GenericFibre k A x
  let : Algebra A G := Algebra.TensorProduct.rightAlgebra
  calc
    functionDegree k E (algebraMap A E x) = Module.finrank k[X] E :=
      functionDegree_eq_polynomial_finrank k E _
    _ = Module.finrank k[X] A := (IsFractionRing.finrank_left_eq k[X] A E).symm
    _ = Module.finrank k[X] G :=
      (IsLocalizedModule.finrank_eq k[X]⁰ (IsScalarTower.toAlgHom k[X] A G).toLinearMap le_rfl).symm
    _ = Module.finrank (RatFunc k) G := (IsFractionRing.finrank_right_eq k[X] (RatFunc k) G).symm
end
end K1_14_2_2_7_2_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace K1_14_2_2_7_2_2
open K1_14_2 K1_14_2_2 K1_14_2_2_7_2
open scoped Polynomial RatFunc TensorProduct
noncomputable section
attribute [local instance] Polynomial.algebra
def c1 : Prop :=
  ∀ I : Ideal Ambient,
    Module.finrank (RatFunc SeedField) (GenericFibre SeedField (JetSeedSection I) (seedCoord I 1)) =
      Module.finrank SeedField (OverSeeds I)
def c2 : Prop :=
  ∀ I : Ideal Ambient,
    Module.finrank (RatFunc (RatFunc SeedField))
      (RationalBaseChange (RatFunc SeedField)
        (GenericFibre SeedField (JetSeedSection I) (seedCoord I 2))) =
      Module.finrank SectionField (OverOrdinate I)
def c3 : Prop :=
  ∀ I : Ideal Ambient,
    Module.finrank (RatFunc (RatFunc SeedField))
      (GenericFibre (RatFunc SeedField) (SlopeRing I) (jetForm I)) =
      Module.finrank SectionField (OverMixed I)
private theorem rationalBaseChangeMap_line (k A E : Type) [Field k] [CommRing A] [Algebra k A]
    [Field E] [Algebra k E] [Algebra A E] [IsScalarTower k A E] (y v : A) :
    rationalBaseChangeMap k A E (rationalLine k A y v) =
      RatFunc.C (algebraMap A E y) + RatFunc.X * RatFunc.C (algebraMap A E v) := by
  simp only [rationalLine, map_add, rationalBaseChangeMap_tmul, rationalBaseChange_scalar_X,
    map_one, one_mul]
private theorem genericLine_length (k A E : Type) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Field E] [Algebra k E] [Algebra A E] [IsScalarTower k A E]
    [IsFractionRing A E] (y v : A) :
    functionDegree (RatFunc k) (RatFunc E)
      (RatFunc.C (algebraMap A E y) + RatFunc.X * RatFunc.C (algebraMap A E v)) =
    Module.finrank (RatFunc (RatFunc k))
      (GenericFibre (RatFunc k) (RationalBaseChange k A) (rationalLine k A y v)) := by
  let : Algebra (RationalBaseChange k A) (RatFunc E) :=
    (rationalBaseChangeMap k A E).toRingHom.toAlgebra
  let := IsScalarTower.of_algHom (rationalBaseChangeMap k A E)
  let : IsFractionRing (RationalBaseChange k A) (RatFunc E) :=
    rationalBaseChange_fractionRing k A E (rationalBaseChangeMap k A E) (fun a => by
      simp only [rationalBaseChangeMap_tmul, map_one, one_mul])
  have h := genericFibre_length (RatFunc k) (RationalBaseChange k A) (RatFunc E) (rationalLine k A y v)
  change functionDegree (RatFunc k) (RatFunc E)
    (rationalBaseChangeMap k A E (rationalLine k A y v)) = _ at h
  rwa [rationalBaseChangeMap_line] at h
private theorem rationalBaseChange_length (k A : Type) [Field k] [CommRing A] [Algebra k A] :
    Module.finrank (RatFunc k) (RationalBaseChange k A) = Module.finrank k A :=
  Module.finrank_baseChange
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) :
    K1_14_2_2_7_2.c2 := by
  intro I _ _
  let A := JetSeedSection I
  let E := FractionRing A
  refine ⟨?_, ?_, ?_⟩
  · exact (genericFibre_length SeedField A E (seedCoord I 1)).trans (h1 I)
  · exact (genericFibre_length SeedField A E (seedCoord I 2)).trans
      ((rationalBaseChange_length (RatFunc SeedField)
        (GenericFibre SeedField A (seedCoord I 2))).symm.trans (h2 I))
  · exact (genericLine_length SeedField A E (seedCoord I 2) (seedCoord I 3)).trans (h3 I)
end
end K1_14_2_2_7_2_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_7_4_4
noncomputable section
open K1_14_2 K1_14_2_2_7_4
open scoped TensorProduct WithZero
abbrev SlopeField (k : Type) [Field k] := FractionRing (Polynomial k)
def slopeMap (k : Type) [Field k] : CurvePoly k →+* CurvePoly (SlopeField k) :=
  MvPolynomial.map (algebraMap k (SlopeField k))
def slopeIdeal {k : Type} [Field k] (D : Ideal (CurvePoly k)) :
    Ideal (CurvePoly (SlopeField k)) :=
  D.map (slopeMap k)
abbrev SlopedCurve {k : Type} [Field k] (D : Ideal (CurvePoly k)) :=
  CoordinateRing (slopeIdeal D)
abbrev CurveField {k : Type} [Field k] (D : Ideal (CurvePoly k)) :=
  FractionRing (SlopedCurve D)
def extendElement {k : Type} [Field k] (D : Ideal (CurvePoly k)) (f : CurvePoly k) :
    SlopedCurve D :=
  Ideal.Quotient.mk (slopeIdeal D) (slopeMap k f)
def fieldEval {k : Type} [Field k] (D : Ideal (CurvePoly k)) :
    CurvePoly k →+* CurveField D :=
  (algebraMap (SlopedCurve D) (CurveField D)).comp
    ((Ideal.Quotient.mk (slopeIdeal D)).comp (slopeMap k))
def fieldCoord {k : Type} [Field k] (D : Ideal (CurvePoly k)) (i : Option (Fin 2)) :
    CurveField D :=
  fieldEval D (MvPolynomial.X i)
def genericSlope (k : Type) [Field k] : SlopeField k :=
  algebraMap (Polynomial k) (SlopeField k) Polynomial.X
def seedParameter {k : Type} [Field k] (D : Ideal (CurvePoly k)) : CurveField D :=
  let line : CurvePoly (SlopeField k) :=
    MvPolynomial.X (some 0) + MvPolynomial.C (genericSlope k) * MvPolynomial.X (some 1)
  algebraMap (SlopedCurve D) (CurveField D) (Ideal.Quotient.mk (slopeIdeal D) line)
def Separating (F K : Type) [Field F] [Field K] [Algebra F K] (x : K) : Prop :=
  Transcendental F x ∧
    Module.Finite (IntermediateField.adjoin F {x}) K ∧
    Algebra.IsSeparable (IntermediateField.adjoin F {x}) K
def ProjectionWithin (F K : Type) [Field F] [Field K] [Algebra F K] (x : K) (n : ℕ) : Prop :=
  IsAlgebraic F x ∨ (Transcendental F x ∧ Module.Finite (IntermediateField.adjoin F {x}) K ∧
    Module.finrank (IntermediateField.adjoin F {x}) K ≤ n)
structure Place (F K : Type) [Field F] [Field K] [Algebra F K] where
  val : Valuation K ℤᵐ⁰
  surj : Function.Surjective val
  trivial : ∀ c : F, c ≠ 0 → val (algebraMap F K c) = 1
variable {F K : Type} [Field F] [Field K] [Algebra F K]
instance (w : Place F K) : Algebra F w.val.valuationSubring :=
  ((algebraMap F K).codRestrict w.val.valuationSubring.toSubring fun c => by
    change (algebraMap F K) c ∈ w.val.valuationSubring
    rw [Valuation.mem_valuationSubring_iff]
    by_cases hc : c = 0
    · simp [hc]
    · rw [w.trivial c hc]).toAlgebra
def residueDegree (w : Place F K) : ℕ :=
  Module.finrank F (IsLocalRing.ResidueField w.val.valuationSubring)
def poleOrder (w : Place F K) (x : K) : ℕ := (WithZero.log (w.val x)).toNat
def zeroOrder (w : Place F K) (x : K) : ℕ := (-WithZero.log (w.val x)).toNat
def poleDegree (S : Finset (Place F K)) (x : K) : ℕ :=
  ∑ w ∈ S, residueDegree w * poleOrder w x
def zeroDegree (S : Finset (Place F K)) (x : K) : ℕ :=
  ∑ w ∈ S, residueDegree w * zeroOrder w x
end
end K1_14_2_2_7_4_4
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_7_2_2_3
open K1_14 K1_14_2 K1_14_2_2 MvPolynomial
open scoped nonZeroDivisors
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev One (A : Type) [CommRing A] := MvPolynomial Unit A
private local instance singleAlgebra (A : Type) [CommRing A] [IsDomain A] :
    Algebra (One A) (RatFunc A) :=
  Algebra.compHom _ (uniqueAlgEquiv A Unit).toRingEquiv.toRingHom
private local instance singleFraction (A : Type) [CommRing A] [IsDomain A] :
    IsFractionRing (One A) (RatFunc A) :=
  IsFractionRing.of_ringEquiv_left (uniqueAlgEquiv A Unit).toRingEquiv fun _ => rfl
private theorem single_C (A : Type) [CommRing A] [IsDomain A] (a : A) :
    algebraMap (One A) (RatFunc A) (C a) = RatFunc.C a := by
  change algebraMap (Polynomial A) (RatFunc A) (uniqueAlgEquiv A Unit (C a)) = _
  simp [uniqueAlgEquiv_apply]
private theorem single_X (A : Type) [CommRing A] [IsDomain A] :
    algebraMap (One A) (RatFunc A) (MvPolynomial.X ()) = RatFunc.X := by
  change algebraMap (Polynomial A) (RatFunc A) (uniqueAlgEquiv A Unit (MvPolynomial.X ())) = _
  simp [uniqueAlgEquiv_apply]
private abbrev extendAlgebra (A E : Type) [CommRing A] [Field E] [Algebra A E] :
    Algebra (One A) (RatFunc E) :=
  Algebra.compHom _ (algebraMap (One A) (One E))
private theorem extendFraction (A E : Type) [CommRing A] [IsDomain A]
    [Field E] [Algebra A E] [IsFractionRing A E] :
    letI := extendAlgebra A E
    IsFractionRing (One A) (RatFunc E) := by
  let P := One A
  let Q := One E
  let M : Submonoid P := A⁰.map MvPolynomial.C
  let : IsLocalization M Q := inferInstance
  let : Algebra P (RatFunc E) := extendAlgebra A E
  let := IsScalarTower.of_algebraMap_eq' (R := P) (S := Q) (A := RatFunc E) rfl
  have hinj : Function.Injective (algebraMap P Q) :=
    MvPolynomial.map_injective _ (IsFractionRing.injective A E)
  have hm : Q⁰.comap (algebraMap P Q) = P⁰ := by
    ext x
    simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero, map_ne_zero_iff _ hinj]
  change IsLocalization P⁰ (RatFunc E)
  rw [← hm]
  exact IsLocalization.localization_localization_isLocalization_of_has_all_units M Q⁰ (RatFunc E)
    (fun _ hu => hu.mem_nonZeroDivisors)
private theorem extend_C (A E : Type) [CommRing A] [Field E] [Algebra A E] (a : A) :
    letI := extendAlgebra A E
    algebraMap (One A) (RatFunc E) (C a) = RatFunc.C (algebraMap A E a) := by
  change algebraMap (One E) (RatFunc E) (MvPolynomial.map (algebraMap A E) (C a)) = _
  rw [map_C, single_C]
private theorem extend_X (A E : Type) [CommRing A] [Field E] [Algebra A E] :
    letI := extendAlgebra A E
    algebraMap (One A) (RatFunc E) (MvPolynomial.X ()) = RatFunc.X := by
  change algebraMap (One E) (RatFunc E) (MvPolynomial.map (algebraMap A E) (MvPolynomial.X ())) = _
  rw [map_X, single_X]
private abbrev Parameters := MvPolynomial (Fin 4) FX
private abbrev Nested := One (One Seeds)
private abbrev SlopeField := RatFunc SeedField
private abbrev InterceptField := RatFunc SlopeField
private local instance innerAlgebra : Algebra (One Seeds) SlopeField := extendAlgebra Seeds SeedField
private local instance innerFraction : IsFractionRing (One Seeds) SlopeField :=
  extendFraction Seeds SeedField
private local instance outerAlgebra : Algebra Nested InterceptField :=
  extendAlgebra (One Seeds) SlopeField
private local instance outerFraction : IsFractionRing Nested InterceptField :=
  extendFraction (One Seeds) SlopeField
private def positions : Fin 4 ≃ Unit ⊕ (Unit ⊕ Fin 2) :=
  Equiv.ofBijective
    ![Sum.inr (Sum.inr 0), Sum.inr (Sum.inl ()), Sum.inr (Sum.inr 1), Sum.inl ()]
    (by decide)
private def nest : Parameters ≃+* Nested :=
  (renameEquiv FX positions).toRingEquiv.trans
    ((sumRingEquiv FX Unit (Unit ⊕ Fin 2)).trans
      (MvPolynomial.mapEquiv Unit (sumRingEquiv FX Unit (Fin 2))))
def coefficients : InterceptField ≃+* SectionField :=
  IsFractionRing.ringEquivOfRingEquiv nest.symm
private theorem coefficients_polynomial (p : Parameters) :
    coefficients (algebraMap Nested InterceptField (nest p)) =
      algebraMap Parameters SectionField p := by
  rw [coefficients, IsFractionRing.ringEquivOfRingEquiv_algebraMap, RingEquiv.symm_apply_apply]
theorem coefficients_seed (i : Fin 2) :
    coefficients (RatFunc.C (RatFunc.C (generic i))) =
      sliceParameter (![0, 2] i) := by
  have h (j : Fin 2) : positions (![0, 2] j) = Sum.inr (Sum.inr j) := by
    fin_cases j <;> rfl
  have hn : nest (MvPolynomial.X (![0, 2] i)) = C (C (MvPolynomial.X i)) := by
    simp [nest, renameEquiv_apply, h, mapEquiv_apply]
  have hp := coefficients_polynomial (MvPolynomial.X (![0, 2] i))
  rwa [hn, extend_C, extend_C] at hp
theorem coefficients_slope :
    coefficients (RatFunc.C RatFunc.X) = sliceParameter 1 := by
  have hn : nest (MvPolynomial.X 1) = C (MvPolynomial.X ()) := by
    simp [nest, renameEquiv_apply, show positions 1 = Sum.inr (Sum.inl ()) from rfl, mapEquiv_apply]
  have hp := coefficients_polynomial (MvPolynomial.X 1)
  rwa [hn, extend_C, extend_X] at hp
theorem coefficients_intercept :
    coefficients RatFunc.X = sliceParameter 3 := by
  have hn : nest (MvPolynomial.X 3) = MvPolynomial.X () := by
    simp [nest, renameEquiv_apply, show positions 3 = Sum.inl () from rfl, mapEquiv_apply]
  have hp := coefficients_polynomial (MvPolynomial.X 3)
  rwa [hn, extend_X] at hp
theorem coefficients_ground (x : FX) :
    coefficients (RatFunc.C (RatFunc.C (algebraMap FX SeedField x))) =
      algebraMap FX SectionField x := by
  have hn : nest (C x) = C (C (C x)) := by
    simp [nest, renameEquiv_apply, mapEquiv_apply]
  have hp := coefficients_polynomial (C x)
  rwa [hn, extend_C, extend_C] at hp
end
end K1_14_2_2_7_2_2_3
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_7_4_4
noncomputable section
open K1_14_2 K1_14_2_2_7_4
open scoped TensorProduct WithZero
variable {k : Type} [Field k]
variable {D : Ideal (CurvePoly k)}
def slopeBaseChange (D : Ideal (CurvePoly k)) :
    (SlopeField k ⊗[k] CoordinateRing D) ≃ₐ[SlopeField k] SlopedCurve D := by
  let B := SlopeField k
  let e : B ⊗[k] CurvePoly k ≃ₐ[B] CurvePoly B := MvPolynomial.algebraTensorAlgEquiv k B
  let i : CurvePoly k →+* B ⊗[k] CurvePoly k :=
    (Algebra.TensorProduct.includeRight (A := B) (R := k)).toRingHom
  have he : e.toAlgHom.toRingHom.comp i = slopeMap k := by
    apply RingHom.ext
    intro p
    change e (1 ⊗ₜ[k] p) = MvPolynomial.map (algebraMap k B) p
    simpa only [e, one_smul] using MvPolynomial.algebraTensorAlgEquiv_tmul k B 1 p
  refine (Algebra.TensorProduct.tensorQuotientEquiv (R := k) B (CurvePoly k) B D).trans
    (Ideal.quotientEquivAlg (D.map i) _ e ?_)
  change slopeIdeal D = (D.map i).map e.toAlgHom.toRingHom
  rw [Ideal.map_map i e.toAlgHom.toRingHom, he]
  rfl
@[simp] theorem slopeBaseChange_mk (D : Ideal (CurvePoly k)) (f : CurvePoly k) :
    slopeBaseChange D (1 ⊗ₜ[k] Ideal.Quotient.mk D f) = extendElement D f := by
  unfold slopeBaseChange
  rw [AlgEquiv.trans_apply, Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul]
  change Ideal.Quotient.mk (slopeIdeal D) (MvPolynomial.algebraTensorAlgEquiv k
    (SlopeField k) (1 ⊗ₜ[k] f)) = _
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
  rfl
theorem fieldEval_ne_zero [IsDomain (SlopedCurve D)] {f : CurvePoly k}
    (hf : f ∉ D) : fieldEval D f ≠ 0 := by
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight (R := k)
      (A := SlopeField k) (B := CoordinateRing D)) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap k (SlopeField k)).injective
  intro hz
  have hx : extendElement D f = 0 := by
    apply IsFractionRing.injective (SlopedCurve D) (CurveField D)
    rw [map_zero]
    exact hz
  have hy : (1 ⊗ₜ[k] Ideal.Quotient.mk D f : SlopeField k ⊗[k] CoordinateRing D) = 0 :=
    (slopeBaseChange D).injective ((slopeBaseChange_mk D f).trans (hx.trans (map_zero _).symm))
  exact hf (Ideal.Quotient.eq_zero_iff_mem.mp (hinj (by
    simpa only [Algebra.TensorProduct.includeRight_apply, TensorProduct.tmul_zero] using hy)))
private theorem fieldEval_eq_eval₂ (f : CurvePoly k) :
    fieldEval D f =
      f.eval₂ ((algebraMap (SlopeField k) (CurveField D)).comp (algebraMap k (SlopeField k)))
        (fieldCoord D) := by
  change fieldEval D f = MvPolynomial.eval₂Hom _ (fieldCoord D) f
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [fieldEval, RingHom.comp_apply, MvPolynomial.eval₂Hom_C, slopeMap,
      MvPolynomial.map_C]
    change algebraMap (SlopedCurve D) (CurveField D)
      (algebraMap (SlopeField k) (SlopedCurve D) (algebraMap k (SlopeField k) c)) = _
    exact (IsScalarTower.algebraMap_apply (SlopeField k) (SlopedCurve D) (CurveField D) _).symm
  · intro i
    simp only [fieldCoord, MvPolynomial.eval₂Hom_X']
private theorem poleOrder_le_iff {F K : Type} [Field F] [Field K] [Algebra F K]
    (w : Place F K) (x : K) (n : ℕ) :
    poleOrder w x ≤ n ↔ w.val x ≤ WithZero.exp (n : ℤ) := by
  by_cases h : w.val x = 0
  · simp [poleOrder, h]
  · rw [← WithZero.log_le_iff_le_exp h]
    unfold poleOrder
    omega
theorem poleDegree_algebraic {F K : Type} [Field F] [Field K] [Algebra F K]
    {x : K} (hx : IsAlgebraic F x) (S : Finset (Place F K)) :
    poleDegree S x = 0 := by
  have h (w : Place F K) : poleOrder w x = 0 := by
    let O := w.val.valuationSubring
    let _ : IsScalarTower F O K := IsScalarTower.of_algebraMap_eq' rfl
    have hi : IsIntegral O x := hx.isIntegral.tower_top
    exact Nat.eq_zero_of_le_zero <| (poleOrder_le_iff w x 0).mpr (by
      simpa using ((Valuation.valuationSubring.integers w.val).isIntegral_iff_v_le_one.mp hi))
  simp [poleDegree, h]
theorem sep_of_small_projection {F K : Type} [Field F] [Field K] [Algebra F K]
    {q : ℕ} [CharP F q] {x : K} (hx : Transcendental F x)
    [Module.Finite (IntermediateField.adjoin F {x}) K]
    (hsize : Module.finrank (IntermediateField.adjoin F {x}) K < q) :
    Separating F K x := by
  let E := IntermediateField.adjoin F {x}
  let _ : CharP E q := charP_of_injective_ringHom (algebraMap F E).injective q
  refine ⟨hx, inferInstance, ⟨fun a => ?_⟩⟩
  have ha : IsIntegral E a := Algebra.IsIntegral.isIntegral a
  let p := minpoly E a
  have hpos : 0 < p.natDegree := minpoly.natDegree_pos ha
  have hlt : p.natDegree < q := (minpoly.natDegree_le a).trans_lt hsize
  have hcast : (p.natDegree : E) ≠ 0 := by
    intro hz
    exact (not_le_of_gt hlt) (Nat.le_of_dvd hpos ((CharP.cast_eq_zero_iff E q _).mp hz))
  change p.Separable
  apply (Polynomial.separable_iff_derivative_ne_zero (minpoly.irreducible ha)).2
  intro hzero
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  have hcoeff := congrArg (fun r : Polynomial E => r.coeff n) hzero
  change p.derivative.coeff n = (0 : Polynomial E).coeff n at hcoeff
  have hmonic : p.coeff p.natDegree = 1 := (minpoly.monic ha).leadingCoeff
  rw [hn] at hmonic
  rw [Polynomial.coeff_derivative, Polynomial.coeff_zero, ← Nat.cast_succ,
    ← hn, hmonic, one_mul] at hcoeff
  exact hcast hcoeff
theorem projection_separable {F K : Type} [Field F] [Field K] [Algebra F K]
    {q : ℕ} [CharP F q] {x : K} {n : ℕ} (h : ProjectionWithin F K x n) (hn : n < q) :
    IsAlgebraic F x ∨
      (Separating F K x ∧ Module.finrank (IntermediateField.adjoin F {x}) K ≤ n) := by
  rcases h with halg | ⟨ht, hfinite, hrank⟩
  · exact Or.inl halg
  · let _ := hfinite
    exact Or.inr ⟨sep_of_small_projection ht (hrank.trans_lt hn), hrank⟩
theorem projection_budget {F K : Type} [Field F] [Field K] [Algebra F K]
    {x : K} {n : ℕ} (S : Finset (Place F K))
    (h : IsAlgebraic F x ∨
      (Separating F K x ∧ Module.finrank (IntermediateField.adjoin F {x}) K ≤ n))
    (hsep : Separating F K x → poleDegree S x ≤ Module.finrank (IntermediateField.adjoin F {x}) K) :
    poleDegree S x ≤ n := by
  rcases h with halg | ⟨hx, hrank⟩
  · rw [poleDegree_algebraic halg]
    exact Nat.zero_le _
  · exact (hsep hx).trans hrank
private theorem poleOrder_bidegree (D : Ideal (CurvePoly k)) [IsDomain (SlopedCurve D)]
    {f : CurvePoly k} {u b : ℕ} (hf : f ∈ MvPolynomial.restrictBidegree (Fin 2) k b u)
    (w : Place (SlopeField k) (CurveField D))
    (hw : max (poleOrder w (fieldCoord D (some 0))) (poleOrder w (fieldCoord D (some 1))) ≤
      poleOrder w (seedParameter D)) :
    poleOrder w (fieldEval D f) ≤
      u * poleOrder w (seedParameter D) + b * poleOrder w (fieldCoord D none) := by
  classical
  let U := poleOrder w (seedParameter D)
  let B := poleOrder w (fieldCoord D none)
  have hnone := (poleOrder_le_iff w (fieldCoord D none) B).mp le_rfl
  have hzero := (poleOrder_le_iff w (fieldCoord D (some 0)) U).mp ((max_le_iff.mp hw).1)
  have hone := (poleOrder_le_iff w (fieldCoord D (some 1)) U).mp ((max_le_iff.mp hw).2)
  apply (poleOrder_le_iff w _ _).mpr
  rw [fieldEval_eq_eval₂, MvPolynomial.eval₂_eq']
  apply w.val.map_sum_le
  intro m hm
  obtain ⟨hb, hu⟩ := MvPolynomial.mem_restrictBidegree.mp hf m hm
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two, Finsupp.some_apply, Finsupp.some_apply] at hu
  have hc (c : SlopeField k) : w.val (algebraMap (SlopeField k) (CurveField D) c) ≤ 1 := by
    by_cases h : c = 0
    · simp [h]
    · rw [w.trivial c h]
  simp only [RingHom.comp_apply, Fintype.prod_option, Fin.prod_univ_two, map_mul, map_pow]
  calc
    _ ≤ 1 * (WithZero.exp (B : ℤ) ^ m none *
        (WithZero.exp (U : ℤ) ^ m (some 0) * WithZero.exp (U : ℤ) ^ m (some 1))) := by
      gcongr <;> first | exact hc _ | exact zero_le
    _ = WithZero.exp (((m (some 0) + m (some 1)) * U + m none * B : ℕ) : ℤ) := by
      simp only [one_mul, ← WithZero.exp_nsmul, ← WithZero.exp_add, WithZero.exp_inj,
        Int.natCast_add, Int.natCast_mul, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      rw [WithZero.exp_le_exp]
      exact_mod_cast Nat.add_le_add (Nat.mul_le_mul_right U hu) (Nat.mul_le_mul_right B hb)
theorem poleDegree_bidegree (D : Ideal (CurvePoly k)) [IsDomain (SlopedCurve D)]
    {f : CurvePoly k} {u b : ℕ} (hf : f ∈ MvPolynomial.restrictBidegree (Fin 2) k b u)
    (S : Finset (Place (SlopeField k) (CurveField D)))
    (hw : ∀ w : Place (SlopeField k) (CurveField D),
      max (poleOrder w (fieldCoord D (some 0))) (poleOrder w (fieldCoord D (some 1))) ≤
        poleOrder w (seedParameter D)) :
    poleDegree S (fieldEval D f) ≤
      u * poleDegree S (seedParameter D) + b * poleDegree S (fieldCoord D none) := by
  unfold poleDegree
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro w _
  calc
    _ ≤ residueDegree w *
        (u * poleOrder w (seedParameter D) + b * poleOrder w (fieldCoord D none)) :=
      Nat.mul_le_mul_left _ (poleOrder_bidegree D hf w (hw w))
    _ = _ := by ring
theorem cut_descend (D : Ideal (CurvePoly k)) (f : CurvePoly k) {n : ℕ}
    (hfinite : Module.Finite (SlopeField k) (SlopedCurve D ⧸ Ideal.span {extendElement D f}))
    (hbound : Module.finrank (SlopeField k) (SlopedCurve D ⧸ Ideal.span {extendElement D f}) ≤ n) :
    Module.Finite k (CoordinateRing (D ⊔ Ideal.span {f})) ∧
      Module.finrank k (CoordinateRing (D ⊔ Ideal.span {f})) ≤ n := by
  let F := SlopeField k
  let J : Ideal (CurvePoly k) := D ⊔ Ideal.span {f}
  let L : Ideal (CurvePoly F) := Ideal.span {slopeMap k f}
  have hJ : slopeIdeal J = slopeIdeal D ⊔ L := by
    simp [slopeIdeal, J, L, Ideal.map_sup, Ideal.map_span]
    rfl
  have hL : L.map (Ideal.Quotient.mkₐ F (slopeIdeal D)) = Ideal.span {extendElement D f} := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  let E : (F ⊗[k] CoordinateRing J) ≃ₐ[F] (SlopedCurve D ⧸ Ideal.span {extendElement D f}) :=
    (slopeBaseChange J).trans ((Ideal.quotientEquivAlgOfEq F hJ).trans
      ((DoubleQuot.quotQuotEquivQuotSupₐ F (slopeIdeal D) L).symm.trans
        (Ideal.quotientEquivAlgOfEq F hL)))
  let _ := hfinite
  let _ := Module.Finite.of_surjective E.symm.toLinearEquiv.toLinearMap E.symm.surjective
  have hfin : Module.Finite k (CoordinateRing J) := by
    apply Module.rank_lt_aleph0_iff.mp
    have hr : Module.rank F (F ⊗[k] CoordinateRing J) = Module.rank k (CoordinateRing J) := by
      simpa only [Cardinal.lift_id] using
        (Module.rank_baseChange (R := F) (S := k) (M' := CoordinateRing J))
    rw [← hr]
    exact Module.rank_lt_aleph0 F (F ⊗[k] CoordinateRing J)
  exact ⟨hfin, (Module.finrank_baseChange (R := F)).symm.trans_le
    (E.toLinearEquiv.finrank_eq.trans_le hbound)⟩
end
end K1_14_2_2_7_4_4
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_7_4_4
noncomputable section
open K1_14_2 K1_14_2_2_7_4
def c1 : Prop :=
  ∀ (k : Type) [Field k] (D : Ideal (CurvePoly k)),
    D.IsPrime → ringKrullDim (CoordinateRing D) = 1 →
      ∃ h : IsDomain (SlopedCurve D), letI := h
        Transcendental (SlopeField k) (seedParameter D) ∨
          Transcendental (SlopeField k) (fieldCoord D none)
def c2 : Prop :=
  ∀ (k : Type) [Field k] (D : Ideal (CurvePoly k)) [IsDomain (SlopedCurve D)],
    Module.Finite (LineField k) (SeedFibre D) →
    ProjectionWithin (SlopeField k) (CurveField D) (seedParameter D)
      (Module.finrank (LineField k) (SeedFibre D))
def c3 : Prop :=
  ∀ (k : Type) [Field k] (D : Ideal (CurvePoly k)) [IsDomain (SlopedCurve D)],
    Module.Finite (VField k) (VFibre D) →
    ProjectionWithin (SlopeField k) (CurveField D) (fieldCoord D none)
      (Module.finrank (VField k) (VFibre D))
def c4 : Prop :=
  ∀ (k : Type) [Field k] (D : Ideal (CurvePoly k)) [IsDomain (SlopedCurve D)],
    D.IsPrime → ringKrullDim (CoordinateRing D) = 1 →
    ∀ w : Place (SlopeField k) (CurveField D),
      max (poleOrder w (fieldCoord D (some 0))) (poleOrder w (fieldCoord D (some 1))) ≤
        poleOrder w (seedParameter D)
def c5 : Prop :=
  ∀ (F A : Type) [Field F] [CommRing A] [IsDomain A] [Algebra F A] [Algebra.FiniteType F A],
    (∃ t : FractionRing A, Separating F (FractionRing A) t) →
    Module.Finite A (integralClosure A (FractionRing A)) ∧
      IsDedekindDomain (integralClosure A (FractionRing A))
def c6 : Prop :=
  ∀ (F A : Type) [Field F] [CommRing A] [IsDomain A] [Algebra F A] [Algebra.FiniteType F A],
    Module.Finite A (integralClosure A (FractionRing A)) →
    IsDedekindDomain (integralClosure A (FractionRing A)) →
    ∀ f : A, f ≠ 0 →
      Module.Finite F (A ⧸ Ideal.span {f}) ∧
      ∃ S : Finset (Place F (FractionRing A)),
        Module.finrank F (A ⧸ Ideal.span {f}) ≤ zeroDegree S (algebraMap A (FractionRing A) f)
def c7 : Prop :=
  ∀ (F K : Type) [Field F] [Field K] [Algebra F K],
    (∃ t : K, Separating F K t) →
    ∀ (g : K), g ≠ 0 → ∀ S : Finset (Place F K),
      ∃ T : Finset (Place F K), zeroDegree S g ≤ poleDegree T g
def c8 : Prop :=
  ∀ (F K : Type) [Field F] [Field K] [Algebra F K]
    (x : K) (S : Finset (Place F K)),
    Separating F K x → poleDegree S x ≤ Module.finrank (IntermediateField.adjoin F {x}) K
set_option maxHeartbeats 1000000 in
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4)
    (h5 : c5) (h6 : c6) (h7 : c7) (h8 : c8) : K1_14_2_2_7_4.c4 := by
  classical
  intro k _ q _ D f u b hprime hdim hf hdeg hsFinite hvFinite hsSize hvSize
  obtain ⟨hDomain, hVary⟩ := h1 k D hprime hdim
  let _ := hDomain
  let F := SlopeField k
  let K := CurveField D
  let A := SlopedCurve D
  let x := seedParameter D
  let v := fieldCoord D none
  let g := fieldEval D f
  let s := Module.finrank (LineField k) (SeedFibre D)
  let e := Module.finrank (VField k) (VFibre D)
  let _ : CharP F q := charP_of_injective_ringHom (algebraMap k F).injective q
  have hx : ProjectionWithin F K x s := h2 k D hsFinite
  have hv : ProjectionWithin F K v e := h3 k D hvFinite
  have hs := projection_separable (F := F) (K := K) hx hsSize
  have he := projection_separable (F := F) (K := K) hv hvSize
  have hsep : ∃ t : K, Separating F K t := by
    rcases hVary with ht | ht
    · exact ⟨x, (hs.resolve_left ht).1⟩
    · exact ⟨v, (he.resolve_left ht).1⟩
  have hg : g ≠ 0 := fieldEval_ne_zero hf
  have hf' : extendElement D f ≠ 0 := fun h => hg (by
    change algebraMap A K (extendElement D f) = 0
    rw [h, map_zero])
  obtain ⟨hnorm, hDedekind⟩ := h5 F A hsep
  obtain ⟨hfinite, S, hzeros⟩ := h6 F A hnorm hDedekind (extendElement D f) hf'
  obtain ⟨T, hpoles⟩ := h7 F K hsep g hg S
  have hsBudget := projection_budget (F := F) (K := K) T hs (h8 F K x T)
  have heBudget := projection_budget (F := F) (K := K) T he (h8 F K v T)
  refine cut_descend D f hfinite ?_
  calc
    Module.finrank F (A ⧸ Ideal.span {extendElement D f}) ≤ zeroDegree S g := hzeros
    _ ≤ poleDegree T g := hpoles
    _ ≤ u * poleDegree T x + b * poleDegree T v :=
      poleDegree_bidegree D hdeg T (h4 k D hprime hdim)
    _ ≤ u * s + b * e :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hsBudget)
        (Nat.mul_le_mul_left _ heBudget)
end
end K1_14_2_2_7_4_4
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace K1_14_2_2_7_4_4_5
noncomputable section
open Polynomial KaehlerDifferential
open scoped TensorProduct IntermediateField.algebraAdjoinAdjoin
private theorem basis_of_separating {F K : Type} [Field F] [Field K] [Algebra F K]
    {t : K} (ht : K1_14_2_2_7_4_4.Separating F K t) :
    IsTranscendenceBasis F (fun _ : Fin 1 => t) := by
  let B := Algebra.adjoin F {t}
  let E := IntermediateField.adjoin F {t}
  have : Module.Finite E K := ht.2.1
  have : Algebra.IsAlgebraic B E := inferInstance
  have : Algebra.IsAlgebraic B K := Algebra.IsAlgebraic.trans B E K
  apply (algebraicIndependent_unique_type_iff.mpr ht.1).isTranscendenceBasis_iff_isAlgebraic.mpr
  rw [Set.range_const]
  exact ‹Algebra.IsAlgebraic B K›
private theorem noether_parameter (F A : Type) [Field F] [CommRing A] [IsDomain A]
    [Algebra F A] [Algebra.FiniteType F A] {t : FractionRing A}
    (ht : K1_14_2_2_7_4_4.Separating F (FractionRing A) t) :
    ∃ r : A, Algebra.IsIntegral (Algebra.adjoin F {r}) A := by
  obtain ⟨n, g, hg, hInt⟩ := exists_integral_inj_algHom_of_fg F A
  let P := MvPolynomial (Fin n) F
  let : Algebra P A := g.toRingHom.toAlgebra
  let : IsScalarTower F P A := IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm
  let : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hg
  have : Algebra.IsIntegral P A := ⟨hInt⟩
  have : Algebra.IsAlgebraic A (FractionRing A) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors A)
  have h := ((IsTranscendenceBasis.mvPolynomial (Fin n) F).algebraMap_comp
    (S := P) (A := A)).algebraMap_comp (A := FractionRing A)
  have hc := h.cardinalMk_eq (basis_of_separating ht)
  have hn : n = 1 := by simpa using hc
  subst n
  let e : F[X] ≃ₐ[F] MvPolynomial (Fin 1) F := (MvPolynomial.uniqueAlgEquiv F (Fin 1)).symm
  let r := g (e Polynomial.X)
  refine ⟨r, ?_⟩
  let B := Algebra.adjoin F {r}
  let rB : B := ⟨r, Algebra.self_mem_adjoin_singleton F r⟩
  have hEq : (aeval (R := F) r) = g.comp e.toAlgHom := by
    ext
    simp [r]
  have hEq' : ((algebraMap B A).comp (aeval (R := F) rB).toRingHom) =
      (aeval (R := F) r).toRingHom := by
    change (((Algebra.ofId B A).restrictScalars F).comp (aeval (R := F) rB)).toRingHom = _
    congr 1
    ext
    simp [rB]
  constructor
  apply RingHom.IsIntegral.tower_top (aeval (R := F) rB).toRingHom (algebraMap B A)
  rw [hEq', hEq]
  exact (RingHom.isIntegral_of_surjective e.toRingEquiv.toRingHom e.surjective).trans
    _ _ hInt
private theorem span_differential {F K : Type} [Field F] [Field K] [Algebra F K]
    (t : K) [Algebra.IsSeparable (IntermediateField.adjoin F {t}) K] :
    Submodule.span K {D F K t} = ⊤ := by
  let E := IntermediateField.adjoin F {t}
  let S := Submodule.span K {D F K t}
  have hElt (x : K) (hx : x ∈ E) : D F K x ∈ S := by
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact Submodule.subset_span (Set.mem_singleton _)
    | algebraMap c => rw [Derivation.map_algebraMap]; exact S.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact S.add_mem hx hy
    | inv x _ hx => rw [Derivation.leibniz_inv]; exact S.smul_mem _ hx
    | mul x y _ _ hx hy =>
      rw [Derivation.leibniz]
      exact S.add_mem (S.smul_mem _ hy) (S.smul_mem _ hx)
  let f := KaehlerDifferential.map F F E K
  have hm (y : KaehlerDifferential F E) : f y ∈ S := by
    change y ∈ (S.restrictScalars E).comap f
    have hle : Submodule.span E (Set.range (D F E)) ≤ (S.restrictScalars E).comap f := by
      apply Submodule.span_le.mpr
      rintro _ ⟨z, rfl⟩
      change f (D F E z) ∈ S
      rw [show f (D F E z) = D F K (z : K) from map_D F F E K z]
      exact hElt z z.property
    exact hle (by rw [span_range_derivation]; trivial)
  have := Algebra.FormallyUnramified.of_isSeparable E K
  have hsurj : Function.Surjective (mapBaseChange F E K) := by
    rw [← LinearMap.range_eq_top, range_mapBaseChange, LinearMap.ker_eq_top]
    ext x
    exact Subsingleton.elim _ _
  apply top_unique
  intro y hy
  clear hy
  obtain ⟨z, rfl⟩ := hsurj y
  induction z with
  | tmul c v => rw [mapBaseChange_tmul]; exact S.smul_mem c (hm v)
  | add z w hz hw => rw [map_add]; exact S.add_mem hz hw
private theorem separating_of_differential {F K : Type} [Field F] [Field K] [Algebra F K]
    [Algebra.EssFiniteType F K] {t s : K} (hspan : Submodule.span K {D F K t} = ⊤)
    (hs : D F K s ≠ 0) : Algebra.IsSeparable (IntermediateField.adjoin F {s}) K := by
  let E := IntermediateField.adjoin F {s}
  let f := KaehlerDifferential.map F E K K
  have hsMem : D F K s ∈ Submodule.span K {D F K t} := by rw [hspan]; trivial
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hsMem
  have hc0 : c ≠ 0 := fun h => hs (by simpa [h] using hc.symm)
  have hfs : f (D F K s) = 0 := by
    change KaehlerDifferential.map F E K K (D F K (algebraMap E K
      (IntermediateField.AdjoinSimple.gen F s))) = 0
    rw [map_D, Algebra.algebraMap_self_apply, Derivation.map_algebraMap]
  have hft : f (D F K t) = 0 := by
    have he := congrArg f hc
    rw [map_smul, hfs, smul_eq_zero] at he
    exact he.resolve_left hc0
  have : Subsingleton (KaehlerDifferential E K) := by
    apply subsingleton_iff_forall_eq 0 |>.mpr
    intro y
    obtain ⟨x, rfl⟩ := map_surjective F E K y
    have hx : x ∈ Submodule.span K {D F K t} := by rw [hspan]; trivial
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    change f (a • D F K t) = 0
    rw [map_smul, hft, smul_zero]
  have : Algebra.EssFiniteType E K := Algebra.EssFiniteType.of_comp F E K
  have : Algebra.FormallyUnramified E K := ⟨inferInstance⟩
  exact Algebra.FormallyUnramified.isSeparable E K
private theorem perturb_parameter {F A : Type} [Field F] [CommRing A] [IsDomain A]
    [Algebra F A] (r a : A) [Algebra.IsIntegral (Algebra.adjoin F {r}) A] :
    ∃ m : ℕ, Algebra.IsIntegral (Algebra.adjoin F {r ^ m - a}) A := by
  classical
  let R := Algebra.adjoin F {r}
  obtain ⟨p, hp, hroot⟩ := Algebra.IsIntegral.isIntegral (R := R) a
  change aeval (R := R) a p = 0 at hroot
  let n := p.natDegree
  have hn : 0 < n := by
    by_contra! h
    have hn0 : p.natDegree = 0 := Nat.eq_zero_of_le_zero h
    have hp1 : p = 1 := by
      rw [eq_C_of_natDegree_eq_zero hn0, ← hn0, hp.coeff_natDegree, C_1]
    rw [hp1, map_one] at hroot
    exact one_ne_zero hroot
  choose q hq using fun i : ℕ => Algebra.adjoin_eq_exists_aeval F r (p.coeff i)
  let m := (Finset.range n).sup (fun i => (q i).natDegree) + 1
  let s := r ^ m - a
  let B := Algebra.adjoin F {s}
  let sB : B := ⟨s, Algebra.self_mem_adjoin_singleton F s⟩
  let v : B[X] := Polynomial.X ^ m - C sB
  let term (i : ℕ) : B[X] := (q i).map (algebraMap F B) * v ^ i
  have hm : m ≠ 0 := Nat.succ_ne_zero _
  have hv : v.Monic := monic_X_pow_sub_C _ hm
  have hdeg : natDegree v = m := natDegree_X_pow_sub_C
  have hlt (i : ℕ) (hi : i ∈ Finset.range n) : (term i).natDegree < m * n := by
    have hqi : (q i).natDegree < m := Nat.lt_succ_of_le (Finset.le_sup (f := fun i => (q i).natDegree) hi)
    calc
      _ ≤ (q i).natDegree + m * i := by
        apply (natDegree_mul_le).trans
        rw [natDegree_map, natDegree_pow v, hdeg, Nat.mul_comm i m]
      _ < m * (i + 1) := by rw [Nat.mul_succ]; omega
      _ ≤ m * n := Nat.mul_le_mul_left _ (Finset.mem_range.mp hi)
  have hsum : (∑ i ∈ Finset.range n, term i).degree < (v ^ n).degree := by
    have hmn : 0 < m * n := Nat.mul_pos (Nat.pos_of_ne_zero hm) hn
    have hd := natDegree_sum_le_of_forall_le (Finset.range n) term
      (n := m * n - 1) (fun i hi => by have := hlt i hi; omega)
    apply lt_of_le_of_lt degree_le_natDegree
    rw [degree_eq_natDegree (hv.pow n).ne_zero, natDegree_pow v, hdeg, Nat.mul_comm n m]
    exact_mod_cast (show (∑ i ∈ Finset.range n, term i).natDegree < m * n by omega)
  have hInt : IsIntegral B r := by
    refine ⟨v ^ n + ∑ i ∈ Finset.range n, term i, (hv.pow n).add_of_left hsum, ?_⟩
    have hvr : aeval (R := B) r v = a := by simp [v, sB, s]
    have heval (i : ℕ) : aeval (R := B) r (term i) = algebraMap R A (p.coeff i) * a ^ i := by
      simp only [term, map_mul, map_pow, hvr, aeval_map_algebraMap]
      rw [hq]
      rfl
    change aeval (R := B) r _ = 0
    rw [map_add, map_pow, hvr, map_sum]
    simp_rw [heval]
    rw [p.as_sum_range_C_mul_X_pow, Finset.sum_range_succ] at hroot
    simpa [n, hp.coeff_natDegree, add_comm] using hroot
  let S := Algebra.adjoin B {r}
  have hle : R ≤ S.restrictScalars F := Algebra.adjoin_le fun x hx =>
    Algebra.subset_adjoin hx
  let : Algebra R S := (Subalgebra.inclusion hle).toAlgebra
  have : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsIntegral B S := Algebra.IsIntegral.adjoin
    (fun x hx => Set.mem_singleton_iff.mp hx ▸ hInt)
  have : Algebra.IsIntegral S A := Algebra.IsIntegral.tower_top R
  exact ⟨m, Algebra.IsIntegral.trans S⟩
private theorem normalization_of_parameter (F A : Type) [Field F] [CommRing A] [IsDomain A]
    [Algebra F A] [Algebra.FiniteType F A] (s : A) (hs : Transcendental F s)
    [Algebra.IsIntegral (Algebra.adjoin F {s}) A]
    [Algebra.IsSeparable (IntermediateField.adjoin F {algebraMap A (FractionRing A) s})
      (FractionRing A)] :
    Module.Finite A (integralClosure A (FractionRing A)) ∧
      IsDedekindDomain (integralClosure A (FractionRing A)) := by
  let K := FractionRing A
  let B := Algebra.adjoin F {s}
  let B' := Algebra.adjoin F {algebraMap A K s}
  let E := IntermediateField.adjoin F {algebraMap A K s}
  let C := integralClosure A K
  have : IsPrincipalIdealRing B :=
    IsPrincipalIdealRing.of_surjective (algEquivOfTranscendental F s hs).toRingEquiv
      (algEquivOfTranscendental F s hs).surjective
  have hFrac : IsFractionRing B' E := by
    have : FaithfulSMul B' E := (faithfulSMul_iff_algebraMap_injective B' E).mpr
      (fun x y h => Subtype.ext (congrArg (fun z : E => (z : K)) h))
    apply IsFractionRing.of_field B' E
    intro z
    obtain ⟨x, hx, y, hy, heq⟩ := IntermediateField.mem_adjoin_iff_div.mp z.property
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, Subtype.ext heq⟩
  let e : B' ≃+* B := (Algebra.RingHom.adjoinAlgebraMapEquiv (A := F) (C := K) s).symm
  let : Algebra B E := ((algebraMap B' E).comp e.symm.toRingHom).toAlgebra
  let : IsFractionRing B E :=
    (IsFractionRing.isFractionRing_iff_of_base_ringEquiv (S := E) e).mp hFrac
  have : IsScalarTower B E K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.EssFiniteType A K := Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors A)
  have : Algebra.EssFiniteType F K := Algebra.EssFiniteType.comp F A K
  have : Algebra.EssFiniteType E K := Algebra.EssFiniteType.of_comp F E K
  have : Algebra.IsAlgebraic E K := inferInstance
  have : Module.Finite E K := Algebra.finite_of_essFiniteType_of_isAlgebraic
  have : IsIntegralClosure C B K := by
    refine ⟨Subtype.val_injective, ?_⟩
    intro x
    rw [← IsIntegralClosure.isIntegral_iff (A := C) (R := A) (B := K)]
    exact ⟨IsIntegral.tower_top (R := B), isIntegral_trans (R := B) x⟩
  have : Module.Finite B C := IsIntegralClosure.finite B E K C
  exact ⟨Module.Finite.of_restrictScalars_finite B A C, IsIntegralClosure.isDedekindDomain B E K C⟩
theorem proof : K1_14_2_2_7_4_4.c5 := by
  intro F A _ _ _ _ _ h
  let K := FractionRing A
  obtain ⟨t, ht, hfin, hsep⟩ := h
  let : Algebra.IsSeparable (IntermediateField.adjoin F {t}) K := hsep
  have : Algebra.EssFiniteType A K := Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors A)
  have : Algebra.EssFiniteType F K := Algebra.EssFiniteType.comp F A K
  have hspan := span_differential (F := F) t
  have hDt : D F K t ≠ 0 := by
    intro hz
    have : Subsingleton (KaehlerDifferential F K) := by
      apply subsingleton_iff_forall_eq 0 |>.mpr
      intro x
      have hx : x ∈ Submodule.span K {D F K t} := by rw [hspan]; trivial
      simpa [hz] using hx
    have : Algebra.FormallyUnramified F K := ⟨inferInstance⟩
    have : Algebra.IsSeparable F K := Algebra.FormallyUnramified.isSeparable F K
    exact ht (Algebra.IsAlgebraic.isAlgebraic t)
  obtain ⟨r, hr⟩ := noether_parameter F A (t := t) ⟨ht, hfin, hsep⟩
  have hparam (s : A) (hInt : Algebra.IsIntegral (Algebra.adjoin F {s}) A)
      (hds : D F K (algebraMap A K s) ≠ 0) :
      Module.Finite A (integralClosure A K) ∧ IsDedekindDomain (integralClosure A K) := by
    have := hInt
    have := separating_of_differential hspan hds
    have hs : Transcendental F s := by
      intro hs
      let B := Algebra.adjoin F {s}
      have : Algebra.IsIntegral F B := Algebra.IsIntegral.adjoin
        (fun x hx => Set.mem_singleton_iff.mp hx ▸ hs.isIntegral)
      have : Algebra.IsIntegral F A := Algebra.IsIntegral.trans B
      have : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic _ (nonZeroDivisors A)
      have : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.trans F A K
      exact ht (Algebra.IsAlgebraic.isAlgebraic t)
    exact normalization_of_parameter F A s hs
  by_cases hdr : D F K (algebraMap A K r) = 0
  · have ha : ∃ a : A, D F K (algebraMap A K a) ≠ 0 := by
      by_contra! hz
      obtain ⟨x, y, _, heq⟩ := IsFractionRing.div_surjective A t
      apply hDt
      rw [← heq, Derivation.leibniz_div, hz, hz]
      simp
    obtain ⟨a, ha⟩ := ha
    have := hr
    obtain ⟨m, hm⟩ := perturb_parameter (F := F) r a
    apply hparam _ hm
    rwa [map_sub, map_pow, map_sub, Derivation.leibniz_pow, hdr, smul_zero, smul_zero,
      zero_sub, neg_ne_zero]
  · exact hparam r hr hdr
end
end K1_14_2_2_7_4_4_5
end
section
namespace K1_14_2_2_7_3
noncomputable section
open K1_14 K1_14_2
abbrev PlaneField (k : Type) [Field k] := FractionRing (MvPolynomial (Fin 2) k)
def planeScalar (k : Type) [Field k] (i : Fin 2) : PlaneField k :=
  algebraMap (MvPolynomial (Fin 2) k) (PlaneField k) (MvPolynomial.X i)
def genericBase (k : Type) [Field k] :
    MvPolynomial (Fin 4) k →+* MvPolynomial (Fin 4) (PlaneField k) :=
  MvPolynomial.map (algebraMap k (PlaneField k))
abbrev SeedFibre {k : Type} [Field k] (H : Ideal (MvPolynomial (Fin 4) k)) :=
  CoordinateRing (H.map (genericBase k) ⊔ Ideal.span
    {MvPolynomial.X 0 + MvPolynomial.C (planeScalar k 0) * MvPolynomial.X 1 -
      MvPolynomial.C (planeScalar k 1)})
abbrev VFibre {k : Type} [Field k] (H : Ideal (MvPolynomial (Fin 4) k)) :=
  CoordinateRing (H.map (genericBase k) ⊔ Ideal.span
    {MvPolynomial.X 3 - MvPolynomial.C (planeScalar k 1)})
abbrev OrdinateAmbient := MvPolynomial (Fin 4) SeedField
def ordinateIdeal (I : Ideal Ambient) : Ideal OrdinateAmbient :=
  I.map (genericBase FX) ⊔ Ideal.span {ySection 2}
def blockEval {k : Type} [Field k] :
    Polynomial (MvPolynomial (Fin 2) k) →+* MvPolynomial (Fin 4) k :=
  Polynomial.eval₂RingHom
    (MvPolynomial.rename (Fin.castLE (by decide : 2 ≤ 4))).toRingHom (MvPolynomial.X 3)
def specializeJet (P : Jet) : Polynomial (MvPolynomial (Fin 2) SeedField) :=
  P.map (Polynomial.eval₂RingHom (MvPolynomial.map (algebraMap FX SeedField))
    (MvPolynomial.C (generic 1)))
end
end K1_14_2_2_7_3
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_7_4_4_2
noncomputable section
open K1_14_2 K1_14_2_2_7_4 K1_14_2_2_7_4_4
private abbrev LinePoly (k : Type) [Field k] := MvPolynomial (Fin 2) k
variable {k : Type} [Field k]
private def interceptChart (k : Type) [Field k] :
    LinePoly k ≃ₐ[k] Polynomial (MvPolynomial (Fin 1) k) :=
  (MvPolynomial.renameEquiv k (Equiv.swap (0 : Fin 2) 1)).trans (MvPolynomial.finSuccEquiv k 1)
private def slopeCoefficients (k : Type) [Field k] : MvPolynomial (Fin 1) k →+* SlopeField k :=
  (algebraMap (Polynomial k) (SlopeField k)).comp (MvPolynomial.uniqueAlgEquiv k (Fin 1)).toRingHom
private def linePolynomial (k : Type) [Field k] : LinePoly k →+* Polynomial (SlopeField k) :=
  (Polynomial.mapRingHom (slopeCoefficients k)).comp (interceptChart k).toRingHom
private theorem linePolynomial_injective (k : Type) [Field k] :
    Function.Injective (linePolynomial k) := by
  have hs : Function.Injective (slopeCoefficients k) := by
    intro p q heq
    apply (MvPolynomial.uniqueAlgEquiv k (Fin 1)).injective
    exact IsFractionRing.injective (Polynomial k) (SlopeField k) heq
  intro p q heq
  apply (interceptChart k).injective
  exact Polynomial.map_injective _ hs heq
private theorem linePolynomial_slope :
    linePolynomial k (MvPolynomial.X 0) = Polynomial.C (genericSlope k) := by
  change Polynomial.map (slopeCoefficients k)
    (MvPolynomial.finSuccEquiv k 1
      (MvPolynomial.renameEquiv k (Equiv.swap (0 : Fin 2) 1) (MvPolynomial.X 0))) = _
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, Equiv.swap_apply_left]
  rw [show (1 : Fin 2) = (0 : Fin 1).succ from rfl, MvPolynomial.finSuccEquiv_X_succ]
  simp [slopeCoefficients, genericSlope]
private theorem linePolynomial_intercept :
    linePolynomial k (MvPolynomial.X 1) = Polynomial.X := by
  change Polynomial.map (slopeCoefficients k)
    (MvPolynomial.finSuccEquiv k 1
      (MvPolynomial.renameEquiv k (Equiv.swap (0 : Fin 2) 1) (MvPolynomial.X 1))) = _
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, Equiv.swap_apply_right,
    MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]
private theorem linePolynomial_C (a : k) :
    linePolynomial k (MvPolynomial.C a) = Polynomial.C (algebraMap k (SlopeField k) a) := by
  change Polynomial.map (slopeCoefficients k) (interceptChart k (algebraMap k (LinePoly k) a)) = _
  rw [AlgEquiv.commutes, IsScalarTower.algebraMap_apply k (MvPolynomial (Fin 1) k)
    (Polynomial (MvPolynomial (Fin 1) k)), Polynomial.algebraMap_eq, Polynomial.map_C]
  change Polynomial.C (algebraMap (Polynomial k) (SlopeField k)
    ((MvPolynomial.uniqueAlgEquiv k (Fin 1)) (algebraMap k (MvPolynomial (Fin 1) k) a))) = _
  rw [AlgEquiv.commutes]
  exact congrArg Polynomial.C (IsScalarTower.algebraMap_apply k (Polynomial k) (SlopeField k) a).symm
private def slopePolynomial (k : Type) [Field k] : Polynomial k →+* LinePoly k :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)
private theorem linePolynomial_slopePolynomial (p : Polynomial k) :
    linePolynomial k (slopePolynomial k p) =
      Polynomial.C (algebraMap (Polynomial k) (SlopeField k) p) := by
  suffices h : (linePolynomial k).comp (slopePolynomial k) =
      Polynomial.C.comp (algebraMap (Polynomial k) (SlopeField k)) by
    exact DFunLike.congr_fun h p
  apply Polynomial.ringHom_ext
  · intro a
    change linePolynomial k (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) (Polynomial.C a)) =
      Polynomial.C (algebraMap (Polynomial k) (SlopeField k) (Polynomial.C a))
    rw [Polynomial.eval₂_C, linePolynomial_C]
    exact congrArg Polynomial.C (IsScalarTower.algebraMap_apply k (Polynomial k) (SlopeField k) a)
  · change linePolynomial k (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) Polynomial.X) = _
    rw [Polynomial.eval₂_X]
    exact linePolynomial_slope
section Curve
variable (D : Ideal (CurvePoly k)) [IsDomain (SlopedCurve D)]
private abbrev ParameterField :=
  IntermediateField.adjoin (SlopeField k) {seedParameter D}
private def parameter : ParameterField D :=
  ⟨seedParameter D, IntermediateField.mem_adjoin_simple_self _ _⟩
private def lineEvaluation : LinePoly k →+* ParameterField D :=
  (Polynomial.aeval (parameter D)).toRingHom.comp (linePolynomial k)
private theorem lineEvaluation_injective (ht : Transcendental (SlopeField k) (seedParameter D)) :
    Function.Injective (lineEvaluation D) := by
  have h : Transcendental (SlopeField k) (parameter D) := by
    intro ha
    exact ht (ha.algHom (ParameterField D).val)
  exact (transcendental_iff_injective.mp h).comp (linePolynomial_injective k)
private def lineHom (ht : Transcendental (SlopeField k) (seedParameter D)) :
    LineField k →+* ParameterField D :=
  IsFractionRing.lift (lineEvaluation_injective D ht)
private theorem lineHom_C (ht : Transcendental (SlopeField k) (seedParameter D)) (a : k) :
    lineHom D ht (algebraMap k (LineField k) a) =
      algebraMap (SlopeField k) (ParameterField D) (algebraMap k (SlopeField k) a) := by
  rw [IsScalarTower.algebraMap_apply k (LinePoly k) (LineField k), MvPolynomial.algebraMap_eq]
  simp [lineHom, lineEvaluation, linePolynomial_C]
private theorem lineHom_slopePolynomial (ht : Transcendental (SlopeField k) (seedParameter D))
    (p : Polynomial k) :
    lineHom D ht (algebraMap (LinePoly k) (LineField k) (slopePolynomial k p)) =
      algebraMap (SlopeField k) (ParameterField D) (algebraMap (Polynomial k) (SlopeField k) p) := by
  simp [lineHom, lineEvaluation, linePolynomial_slopePolynomial]
private theorem lineHom_slope (ht : Transcendental (SlopeField k) (seedParameter D)) :
    lineHom D ht (lineParameter k 0) =
      algebraMap (SlopeField k) (ParameterField D) (genericSlope k) := by
  simp [lineHom, lineParameter, lineEvaluation, linePolynomial_slope]
private theorem lineHom_intercept (ht : Transcendental (SlopeField k) (seedParameter D)) :
    lineHom D ht (lineParameter k 1) = parameter D := by
  simp [lineHom, lineParameter, lineEvaluation, linePolynomial_intercept]
private theorem lineHom_surjective (ht : Transcendental (SlopeField k) (seedParameter D)) :
    Function.Surjective (lineHom D ht) := by
  let f : LineField k →+* CurveField D := (ParameterField D).val.toRingHom.comp (lineHom D ht)
  have hbase : Set.range (algebraMap (SlopeField k) (CurveField D)) ⊆ f.fieldRange := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective (Polynomial k) s
    rw [map_div₀]
    apply div_mem
    · exact ⟨_, congrArg (ParameterField D).val (lineHom_slopePolynomial D ht p)⟩
    · exact ⟨_, congrArg (ParameterField D).val (lineHom_slopePolynomial D ht q)⟩
  have hparameter : {seedParameter D} ⊆ (f.fieldRange : Set (CurveField D)) := by
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact ⟨_, congrArg (ParameterField D).val (lineHom_intercept D ht)⟩
  have h := IntermediateField.adjoin_le_subfield (SlopeField k) {seedParameter D} hbase hparameter
  intro x
  obtain ⟨y, hy⟩ := RingHom.mem_fieldRange.mp (h x.property)
  exact ⟨y, (ParameterField D).val.injective hy⟩
private def lineEquiv (ht : Transcendental (SlopeField k) (seedParameter D)) :
    LineField k ≃+* ParameterField D :=
  RingEquiv.ofBijective (lineHom D ht) ⟨(lineHom D ht).injective, lineHom_surjective D ht⟩
private def curveEvaluation : CurvePoly (SlopeField k) →ₐ[SlopeField k] CurveField D :=
  (IsScalarTower.toAlgHom (SlopeField k) (SlopedCurve D) (CurveField D)).comp
    (Ideal.Quotient.mkₐ (SlopeField k) (slopeIdeal D))
omit [IsDomain (SlopedCurve D)] in
private theorem curveEvaluation_parameter :
    curveEvaluation D (MvPolynomial.X (some 0) +
      MvPolynomial.C (genericSlope k) * MvPolynomial.X (some 1)) = seedParameter D := rfl
private theorem finite_rank_bound {F G M N : Type} [Field F] [Field G]
    [AddCommGroup M] [AddCommGroup N] [Module F M] [Module G N] [Module.Finite F M]
    {σ : F →+* G} (f : M →ₛₗ[σ] N) (hf : Function.Surjective f) :
    Module.Finite G N ∧ Module.finrank G N ≤ Module.finrank F M := by
  refine ⟨Module.Finite.of_surjective f hf, ?_⟩
  let b := Module.finBasis F M
  have hspan : Submodule.span G (Set.range (f ∘ b)) = ⊤ := by
    apply eq_top_iff.mpr
    intro y _
    obtain ⟨x, rfl⟩ := hf y
    rw [Set.range_comp]
    exact Submodule.image_span_subset_span f _ ⟨x, by rw [b.span_eq]; trivial, rfl⟩
  simpa using finrank_le_of_span_eq_top hspan
private theorem finite_field_of_fibre {L E A R K : Type}
    [Field L] [Field E] [CommRing A] [Algebra L A] [Module.Finite L A]
    [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] [Algebra E K]
    (e : L ≃+* E) (q : A →+* K)
    (hq : ∀ a, q (algebraMap L A a) = algebraMap E K (e a))
    (hR : Set.range (algebraMap R K) ⊆ q.range) :
    Module.Finite E K ∧ Module.finrank E K ≤ Module.finrank L A := by
  have hsmul (a : L) (x : A) : q (a • x) = e a • q x := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hq]
  let B : Subalgebra E K :=
    { toSubsemiring := q.range.toSubsemiring
      algebraMap_mem' := fun a => by
        obtain ⟨b, rfl⟩ := e.surjective a
        exact ⟨_, hq b⟩ }
  let fB : A →ₛₗ[e.toRingHom] B :=
    { toFun := fun x => ⟨q x, q.mem_range_self x⟩
      map_add' := fun x y => Subtype.ext (map_add q x y)
      map_smul' := fun a x => Subtype.ext (hsmul a x) }
  have hfB : Function.Surjective fB := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := RingHom.mem_range.mp (show y ∈ q.range from hy)
    exact ⟨x, Subtype.ext hx⟩
  let _ := Module.Finite.of_surjective fB hfB
  let H := Algebra.IsAlgebraic.toIntermediateField B
  have hsurj : Function.Surjective q := by
    intro y
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective R y
    have ha : algebraMap R K a ∈ H := hR ⟨a, rfl⟩
    have hb : algebraMap R K b ∈ H := hR ⟨b, rfl⟩
    have hd : algebraMap R K a / algebraMap R K b ∈ H := div_mem ha hb
    exact RingHom.mem_range.mp hd
  let f : A →ₛₗ[e.toRingHom] K := { q.toAddMonoidHom with map_smul' := hsmul }
  exact finite_rank_bound f hsurj
private theorem seedFibre_hom {K : Type} [Field K] [Algebra (SlopeField k) K]
    (D : Ideal (CurvePoly k)) (g : CurvePoly (SlopeField k) →ₐ[SlopeField k] K)
    (coeff : LineField k →+* K) (slopeToLine : SlopeField k →+* LineField k)
    (hcoeff : coeff.comp slopeToLine = algebraMap (SlopeField k) K)
    (hbase : coeff.comp (algebraMap k (LineField k)) =
      (algebraMap (SlopeField k) K).comp (algebraMap k (SlopeField k)))
    (hs : coeff (lineParameter k 0) = algebraMap (SlopeField k) K (genericSlope k))
    (hi : coeff (lineParameter k 1) = g (MvPolynomial.X (some 0) +
      MvPolynomial.C (genericSlope k) * MvPolynomial.X (some 1)))
    (hD : ∀ p ∈ D, g (slopeMap k p) = 0) :
    ∃ q : SeedFibre D →+* K,
      (∀ a, q (algebraMap (LineField k) (SeedFibre D) a) = coeff a) ∧
        Set.range g ⊆ q.range := by
  let φ : CurvePoly (LineField k) →+* K :=
    MvPolynomial.eval₂Hom coeff (fun i => g (MvPolynomial.X i))
  have hφ (p : CurvePoly (SlopeField k)) :
      φ (MvPolynomial.map slopeToLine p) = g p := by
    change MvPolynomial.eval₂Hom coeff _ (MvPolynomial.map slopeToLine p) = _
    rw [MvPolynomial.eval₂Hom_map_hom, hcoeff]
    exact DFunLike.congr_fun (by
      apply MvPolynomial.ringHom_ext
      · intro a
        rw [MvPolynomial.eval₂Hom_C, ← MvPolynomial.algebraMap_eq]
        exact (g.commutes a).symm
      · intro i
        rw [MvPolynomial.eval₂Hom_X']
        rfl) p
  have hsource : φ.comp (MvPolynomial.map (algebraMap k (LineField k))) =
      g.toRingHom.comp (slopeMap k) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, slopeMap, MvPolynomial.map_C]
      change MvPolynomial.eval₂Hom coeff _ (MvPolynomial.C (algebraMap k (LineField k) a)) = _
      rw [MvPolynomial.eval₂Hom_C, ← RingHom.comp_apply, hbase]
      symm
      exact g.commutes _
    · intro i
      simp [φ, slopeMap]
  have hφX (i : Option (Fin 2)) :
      φ (MvPolynomial.X i) = g (MvPolynomial.X i) :=
    MvPolynomial.eval₂Hom_X' coeff _ i
  have hφC (a : LineField k) : φ (MvPolynomial.C a) = coeff a :=
    MvPolynomial.eval₂Hom_C coeff _ a
  have hline : φ (MvPolynomial.X (some 0) + MvPolynomial.C (lineParameter k 0) *
      MvPolynomial.X (some 1) - MvPolynomial.C (lineParameter k 1)) = 0 := by
    rw [map_sub φ, map_add φ, map_mul φ, hφX, hφX, hφC, hφC]
    rw [hs, hi, sub_eq_zero]
    have hc : g (MvPolynomial.C (genericSlope k)) =
        algebraMap (SlopeField k) K (genericSlope k) := g.commutes _
    rw [map_add g, map_mul g, hc]
  have hkill : seedFibreIdeal D ≤ RingHom.ker φ := by
    apply sup_le
    · apply Ideal.map_le_iff_le_comap.mpr
      intro p hp
      change φ (MvPolynomial.map (algebraMap k (LineField k)) p) = 0
      rw [← RingHom.comp_apply, hsource, RingHom.comp_apply]
      exact hD p hp
    · apply Ideal.span_le.mpr
      intro p hp
      rw [Set.mem_singleton_iff.mp hp]
      exact hline
  let q : SeedFibre D →+* K := Ideal.Quotient.lift (seedFibreIdeal D) φ
    (fun p hp => hkill hp)
  refine ⟨q, ?_, ?_⟩
  · intro a
    change Ideal.Quotient.lift (seedFibreIdeal D) φ (fun p hp => hkill hp)
      (Ideal.Quotient.mk (seedFibreIdeal D) (MvPolynomial.C a)) = coeff a
    rw [Ideal.Quotient.lift_mk, hφC]
  · rintro _ ⟨p, rfl⟩
    refine ⟨Ideal.Quotient.mk _ (MvPolynomial.map slopeToLine p), ?_⟩
    change Ideal.Quotient.lift (seedFibreIdeal D) φ (fun p hp => hkill hp)
      (Ideal.Quotient.mk _ (MvPolynomial.map slopeToLine p)) = _
    rw [Ideal.Quotient.lift_mk, hφ]
set_option maxHeartbeats 1100000 in
private theorem finite_projection (ht : Transcendental (SlopeField k) (seedParameter D))
    [Module.Finite (LineField k) (SeedFibre D)] :
    ProjectionWithin (SlopeField k) (CurveField D) (seedParameter D)
      (Module.finrank (LineField k) (SeedFibre D)) := by
  refine Or.inr ⟨ht, ?_⟩
  let E := ParameterField D
  let e : LineField k ≃+* E := lineEquiv D ht
  let coeff : LineField k →+* E := e.toRingHom
  let slopeToLine : SlopeField k →+* LineField k :=
    e.symm.toRingHom.comp (algebraMap (SlopeField k) E)
  have hcoeff : coeff.comp slopeToLine = algebraMap (SlopeField k) E := by
    apply RingHom.ext
    intro a
    exact e.apply_symm_apply _
  let coeffK : LineField k →+* CurveField D := E.val.toRingHom.comp coeff
  have hcoeffK : coeffK.comp slopeToLine = algebraMap (SlopeField k) (CurveField D) := by
    change (E.val.toRingHom.comp coeff).comp slopeToLine = _
    rw [RingHom.comp_assoc, hcoeff]
    apply RingHom.ext
    intro a
    exact E.val.commutes a
  have hbase : coeffK.comp (algebraMap k (LineField k)) =
      (algebraMap (SlopeField k) (CurveField D)).comp (algebraMap k (SlopeField k)) := by
    apply RingHom.ext
    intro a
    change E.val (lineHom D ht (algebraMap k (LineField k) a)) = _
    rw [lineHom_C, E.val.commutes]
    rfl
  have hs : coeffK (lineParameter k 0) = algebraMap (SlopeField k) (CurveField D) (genericSlope k) := by
    change E.val (lineHom D ht (lineParameter k 0)) = _
    rw [lineHom_slope, E.val.commutes]
  have hi : coeffK (lineParameter k 1) = seedParameter D := by
    change E.val (lineHom D ht (lineParameter k 1)) = _
    rw [lineHom_intercept]
    rfl
  have hD (p : CurvePoly k) (hp : p ∈ D) : curveEvaluation D (slopeMap k p) = 0 := by
    have hp' : slopeMap k p ∈ slopeIdeal D := Ideal.mem_map_of_mem _ hp
    change algebraMap (SlopedCurve D) (CurveField D)
      (Ideal.Quotient.mk (slopeIdeal D) (slopeMap k p)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp']
    exact map_zero (algebraMap (SlopedCurve D) (CurveField D))
  obtain ⟨q, hq, hqR⟩ := seedFibre_hom D (curveEvaluation D) coeffK slopeToLine
    hcoeffK hbase hs (hi.trans (curveEvaluation_parameter D).symm) hD
  refine finite_field_of_fibre (R := SlopedCurve D) e q hq ?_
  rintro _ ⟨a, rfl⟩
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact hqR ⟨p, rfl⟩
theorem proof : K1_14_2_2_7_4_4.c2 := by
  classical
  intro k _ D _ hfinite
  by_cases h : IsAlgebraic (SlopeField k) (seedParameter D)
  · exact Or.inl h
  · let _ := hfinite
    exact finite_projection D h
end Curve
end
end K1_14_2_2_7_4_4_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_2_2_7_3
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 MvPolynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev BeforeLocalization := MvPolynomial (Fin 4) Seeds
private def beforeBase : Ambient →+* BeforeLocalization :=
  MvPolynomial.map MvPolynomial.C
private def ordinateEquation : BeforeLocalization :=
  MvPolynomial.X 2 - MvPolynomial.C (MvPolynomial.X 1)
private def beforeIdeal (Q : Ideal Ambient) : Ideal BeforeLocalization :=
  Q.map beforeBase ⊔ Ideal.span {ordinateEquation}
private abbrev denominators : Submonoid BeforeLocalization :=
  Seeds⁰.map (MvPolynomial.C (σ := Fin 4))
private def parameterEval (Q : Ideal Ambient) : Seeds →+* Polynomial (CoordinateRing Q) :=
  (Polynomial.mapRingHom ((Ideal.Quotient.mk Q).comp ordinateIncl)).comp
    ((Polynomial.mapRingHom (MvPolynomial.uniqueAlgEquiv FX (Fin 1)).toRingHom).comp
      (MvPolynomial.finSuccEquiv FX 1).toRingHom)
private theorem parameterEval_injective (Q : Ideal Ambient) :
    Function.Injective (parameterEval Q) ↔
      Function.Injective ((Ideal.Quotient.mk Q).comp ordinateIncl) := by
  let e := MvPolynomial.uniqueAlgEquiv FX (Fin 1)
  let t := MvPolynomial.finSuccEquiv FX 1
  let f := (Ideal.Quotient.mk Q).comp ordinateIncl
  change Function.Injective
    (Polynomial.map f ∘ (Polynomial.map e.toRingHom ∘ t)) ↔ Function.Injective f
  rw [← Polynomial.map_injective_iff]
  exact ⟨fun h => h.of_comp_right ((Polynomial.map_surjective _ e.surjective).comp t.surjective),
    fun h => h.comp ((Polynomial.map_injective _ e.injective).comp t.injective)⟩
private theorem parameterEval_C (Q : Ideal Ambient) (a : FX) :
    parameterEval Q (MvPolynomial.C a) =
      Polynomial.C (Ideal.Quotient.mk Q (MvPolynomial.C a)) := by
  simp [parameterEval, MvPolynomial.finSuccEquiv_apply, MvPolynomial.uniqueAlgEquiv,
    ordinateIncl]
private theorem parameterEval_X0 (Q : Ideal Ambient) :
    parameterEval Q (MvPolynomial.X 0) = Polynomial.X := by
  simp [parameterEval, MvPolynomial.finSuccEquiv_X_zero]
private theorem parameterEval_X1 (Q : Ideal Ambient) :
    parameterEval Q (MvPolynomial.X 1) =
      Polynomial.C (Ideal.Quotient.mk Q (MvPolynomial.X 2)) := by
  let e := MvPolynomial.uniqueAlgEquiv FX (Fin 1)
  let f := (Ideal.Quotient.mk Q).comp ordinateIncl
  change Polynomial.map f (Polynomial.map e.toRingHom
    ((MvPolynomial.finSuccEquiv FX 1) (MvPolynomial.X ((0 : Fin 1).succ)))) = _
  rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C, Polynomial.map_C]
  have he : e (MvPolynomial.X 0) = Polynomial.X := by
    change MvPolynomial.eval₂ Polynomial.C (fun _ : Fin 1 => Polynomial.X) (MvPolynomial.X 0) = _
    rw [MvPolynomial.eval₂_X]
  change Polynomial.C (f (e (MvPolynomial.X 0))) = _
  rw [he]
  simp [f, ordinateIncl]
private def beforeEval (Q : Ideal Ambient) : BeforeLocalization →+* Polynomial (CoordinateRing Q) :=
  MvPolynomial.eval₂Hom (S₁ := Polynomial (CoordinateRing Q)) (parameterEval Q)
    fun i => Polynomial.C (Ideal.Quotient.mk Q (MvPolynomial.X i))
private theorem beforeEval_comp (Q : Ideal Ambient) :
    (beforeEval Q).comp beforeBase = Polynomial.C.comp (Ideal.Quotient.mk Q) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, beforeEval, beforeBase, MvPolynomial.map_C,
      MvPolynomial.eval₂Hom_C, parameterEval_C]
  · intro i
    simp [beforeEval, beforeBase]
private theorem beforeIdeal_eq_ker (Q : Ideal Ambient) :
    beforeIdeal Q = RingHom.ker (beforeEval Q) := by
  let D := beforeIdeal Q
  let q := Ideal.Quotient.mk (R := BeforeLocalization) D
  have hD : D ≤ RingHom.ker (beforeEval Q) := by
    apply sup_le
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      change beforeEval Q (beforeBase a) = 0
      have he := RingHom.congr_fun (beforeEval_comp Q) a
      rw [RingHom.comp_apply, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr ha,
        map_zero] at he
      exact he
    · apply (Ideal.span_singleton_le_iff_mem _).mpr
      apply RingHom.mem_ker.mpr
      simp [ordinateEquation, beforeEval, parameterEval_X1]
  let u : CoordinateRing Q →+* BeforeLocalization ⧸ D :=
    Ideal.Quotient.lift Q (q.comp beforeBase)
      (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_sup_left (Ideal.mem_map_of_mem beforeBase ha)))
  let v : Polynomial (CoordinateRing Q) →+* BeforeLocalization ⧸ D :=
    Polynomial.eval₂RingHom u (q (MvPolynomial.C (MvPolynomial.X 0)))
  have hrel : q (MvPolynomial.X 2) = q (MvPolynomial.C (MvPolynomial.X 1)) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))
  have he : v.comp (beforeEval Q) = q := by
    apply MvPolynomial.ringHom_ext
    · have hC : (v.comp (beforeEval Q)).comp MvPolynomial.C = q.comp MvPolynomial.C := by
        apply MvPolynomial.ringHom_ext
        · intro a
          simp only [RingHom.comp_apply, beforeEval, MvPolynomial.eval₂Hom_C, parameterEval_C,
            v, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, u, Ideal.Quotient.lift_mk, beforeBase,
            MvPolynomial.map_C]
        · intro i
          simp only [RingHom.comp_apply, beforeEval, MvPolynomial.eval₂Hom_C]
          fin_cases i
          · change v (parameterEval Q (MvPolynomial.X 0)) = q (MvPolynomial.C (MvPolynomial.X 0))
            simp [parameterEval_X0, v]
          · change v (parameterEval Q (MvPolynomial.X 1)) = q (MvPolynomial.C (MvPolynomial.X 1))
            simp only [parameterEval_X1, v, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, u,
              Ideal.Quotient.lift_mk, RingHom.comp_apply, beforeBase, MvPolynomial.map_X]
            exact hrel
      exact RingHom.congr_fun hC
    · intro i
      simp only [RingHom.comp_apply, beforeEval, MvPolynomial.eval₂Hom_X', v,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, u, Ideal.Quotient.lift_mk,
        beforeBase, MvPolynomial.map_X]
  refine le_antisymm hD fun a ha => Ideal.Quotient.eq_zero_iff_mem.mp ?_
  have hv := RingHom.congr_fun he a
  rw [RingHom.comp_apply, RingHom.mem_ker.mp ha, map_zero] at hv
  exact hv.symm
private theorem localized_beforeBase :
    (algebraMap BeforeLocalization OrdinateAmbient).comp beforeBase = genericBase FX := by
  change (MvPolynomial.map (algebraMap Seeds SeedField)).comp beforeBase = genericBase FX
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, beforeBase, genericBase, MvPolynomial.map_C]
    rfl
  · intro i
    simp only [RingHom.comp_apply, beforeBase, genericBase, MvPolynomial.map_X]
private theorem localized_beforeIdeal (Q : Ideal Ambient) :
    (beforeIdeal Q).map (algebraMap BeforeLocalization OrdinateAmbient) = ordinateIdeal Q := by
  rw [beforeIdeal, Ideal.map_sup, Ideal.map_map, localized_beforeBase,
    Ideal.map_span, Set.image_singleton]
  change Q.map (genericBase FX) ⊔
    Ideal.span {MvPolynomial.map (algebraMap Seeds SeedField) ordinateEquation} =
      Q.map (genericBase FX) ⊔ Ideal.span {ySection 2}
  simp only [ordinateEquation, map_sub, MvPolynomial.map_X, MvPolynomial.map_C, ySection, generic]
theorem ordinate_localization (Q : Ideal Ambient) (hp : Q.IsPrime) :
    (Function.Injective ((Ideal.Quotient.mk Q).comp ordinateIncl) →
      (ordinateIdeal Q).IsPrime ∧ (ordinateIdeal Q).comap (genericBase FX) = Q) ∧
    (¬ Function.Injective ((Ideal.Quotient.mk Q).comp ordinateIncl) →
      ordinateIdeal Q = ⊤) := by
  let := hp
  have hprime : (beforeIdeal Q).IsPrime := by
    rw [beforeIdeal_eq_ker]
    exact RingHom.ker_isPrime _
  constructor
  · intro hdom
    have hdisj : Disjoint (denominators : Set BeforeLocalization) (beforeIdeal Q : Set BeforeLocalization) := by
      apply Set.disjoint_left.mpr
      rintro a ⟨b, hb, rfl⟩ hmem
      change MvPolynomial.C b ∈ beforeIdeal Q at hmem
      rw [beforeIdeal_eq_ker, RingHom.mem_ker] at hmem
      have hz : parameterEval Q b = parameterEval Q 0 := by
        simpa [beforeEval] using hmem
      exact (mem_nonZeroDivisors_iff_ne_zero.mp hb)
        ((parameterEval_injective Q).2 hdom hz)
    have hcontract := IsLocalization.under_map_of_isPrime_disjoint denominators
      OrdinateAmbient hprime hdisj
    rw [localized_beforeIdeal] at hcontract
    refine ⟨localized_beforeIdeal Q ▸ IsLocalization.isPrime_of_isPrime_disjoint denominators
      OrdinateAmbient _ hprime hdisj, ?_⟩
    rw [← localized_beforeBase, ← Ideal.comap_comap]
    change ((ordinateIdeal Q).under BeforeLocalization).comap beforeBase = Q
    rw [hcontract, beforeIdeal_eq_ker]
    ext a
    change beforeEval Q (beforeBase a) = 0 ↔ a ∈ Q
    rw [← RingHom.comp_apply, beforeEval_comp, RingHom.comp_apply,
      Polynomial.C_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
  · intro hdom
    have hn : ¬ Function.Injective (parameterEval Q) :=
      fun h => hdom ((parameterEval_injective Q).1 h)
    obtain ⟨a, b, he, hab⟩ := Function.not_injective_iff.mp hn
    have hne : a - b ∈ Seeds⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr (sub_ne_zero.mpr hab)
    let d : denominators := ⟨MvPolynomial.C (a - b), ⟨a - b, hne, rfl⟩⟩
    have hd : (d : BeforeLocalization) ∈ beforeIdeal Q := by
      rw [beforeIdeal_eq_ker, RingHom.mem_ker]
      simp [d, beforeEval, he]
    have hmem := Ideal.mem_map_of_mem (algebraMap BeforeLocalization OrdinateAmbient) hd
    rw [localized_beforeIdeal] at hmem
    exact (ordinateIdeal Q).eq_top_of_isUnit_mem hmem (IsLocalization.map_units OrdinateAmbient d)
end
end K1_14_2_2_7_3
end
section
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_7_3
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_7 Polynomial
open scoped Classical
private theorem totalDegree_map_le {k l : Type} [Field k] [Field l]
    (f : k →+* l) (g : MvPolynomial (Fin 2) k) :
    (MvPolynomial.map f g).totalDegree ≤ g.totalDegree := by
  unfold MvPolynomial.totalDegree
  exact Finset.sup_mono (MvPolynomial.support_map_subset f g)
theorem specializeJet_caps {P : Jet} {s : Shape} (h : RowCaps P s) :
    (specializeJet P).natDegree ≤ s.J ∧
      ∀ j, ((specializeJet P).coeff j).totalDegree ≤ s.U := by
  constructor
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    have hzero : P.coeff j = 0 := by
      apply Polynomial.ext
      intro i
      simp only [coeff_zero]
      by_contra hn
      exact (Nat.not_le_of_gt hj) (h j i hn).2.1
    simp [specializeJet, coeff_map, hzero]
  · intro j
    rw [specializeJet, coeff_map]
    change ((P.coeff j).eval₂ (MvPolynomial.map (algebraMap FX SeedField))
      (MvPolynomial.C (generic 1))).totalDegree ≤ s.U
    rw [eval₂_eq_sum, sum_def]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro i hi
    rw [← map_pow]
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, add_zero]
    exact (totalDegree_map_le _ _).trans (h j i (mem_support_iff.mp hi)).2.2
theorem specializeJet_mk (I : Ideal Ambient) (P : Jet) :
    Ideal.Quotient.mk (ordinateIdeal I) (blockEval (specializeJet P)) =
      Ideal.Quotient.mk (ordinateIdeal I) (genericBase FX (toJet P)) := by
  let q := Ideal.Quotient.mk (ordinateIdeal I)
  let f := (q.comp (genericBase FX)).comp rootIncl
  let g := q.comp (MvPolynomial.rename (Fin.castLE (by decide : 2 ≤ 4))).toRingHom
  have hy : f (MvPolynomial.X 2) = g (MvPolynomial.C (generic 1)) := by
    change q (genericBase FX
      ((MvPolynomial.rename (Fin.castLE (by decide : 3 ≤ 4))) (MvPolynomial.X 2))) =
      q ((MvPolynomial.rename (Fin.castLE (by decide : 2 ≤ 4)))
        (MvPolynomial.C (generic 1)))
    simp only [MvPolynomial.rename_X, MvPolynomial.rename_C, genericBase, MvPolynomial.map_X]
    change q (MvPolynomial.X 2) = q (MvPolynomial.C (generic 1))
    have hmem : ySection (2 : Fin 4) ∈ ordinateIdeal I :=
      Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    have hz' : q (MvPolynomial.X 2 - MvPolynomial.C (generic 1)) = 0 := hz
    exact sub_eq_zero.mp (by simpa only [map_sub] using hz')
  have hseeds : g.comp (MvPolynomial.map (algebraMap FX SeedField)) = f.comp rootSeeds := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, g, f, rootSeeds, rootIncl, genericBase,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.rename_C, MvPolynomial.map_C]
    · intro i
      simp only [RingHom.comp_apply, g, f, rootSeeds, rootIncl, genericBase,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.rename_X, MvPolynomial.map_X]
      congr 2
  have hinner : g.comp (Polynomial.eval₂RingHom
      (MvPolynomial.map (algebraMap FX SeedField)) (MvPolynomial.C (generic 1))) =
      f.comp toRoot := by
    apply RingHom.ext
    intro A
    change g (A.eval₂ (MvPolynomial.map (algebraMap FX SeedField)) (MvPolynomial.C (generic 1))) =
      f (A.eval₂ rootSeeds (MvPolynomial.X 2))
    rw [Polynomial.hom_eval₂, Polynomial.hom_eval₂, hseeds, hy]
  change q ((specializeJet P).eval₂
      (MvPolynomial.rename (Fin.castLE (by decide : 2 ≤ 4))).toRingHom (MvPolynomial.X 3)) =
    (q.comp (genericBase FX)) (P.eval₂ (rootIncl.comp toRoot) (MvPolynomial.X 3))
  rw [Polynomial.hom_eval₂, Polynomial.hom_eval₂, specializeJet, Polynomial.eval₂_map]
  have houter : (q.comp (genericBase FX)).comp (rootIncl.comp toRoot) = f.comp toRoot := rfl
  rw [houter, ← hinner]
  simp only [g, RingHom.comp_apply, genericBase, MvPolynomial.map_X]
private theorem sum_finrank_quotients_le {k R ι : Type} [Field k] [CommRing R]
    [Algebra k R] [Fintype ι] (D : Ideal R) (J : ι → Ideal R)
    [Module.Finite k (R ⧸ D)] (hle : ∀ i, D ≤ J i)
    (hpair : Pairwise fun i j => IsCoprime (J i) (J j)) :
    (∑ i, Module.finrank k (R ⧸ J i)) ≤ Module.finrank k (R ⧸ D) := by
  let f (i : ι) := Ideal.Quotient.factorₐ k (hle i)
  let (i : ι) : Module.Finite k (R ⧸ J i) :=
    Module.Finite.of_surjective (f i).toLinearMap (Ideal.Quotient.factor_surjective (hle i))
  let F := AlgHom.pi f
  have hF : Function.Surjective F := by
    intro y
    obtain ⟨x, hx⟩ := Ideal.quotientInfToPiQuotient_surj hpair y
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk D p, funext fun i => congrFun hx i⟩
  rw [← Module.finrank_pi_fintype]
  exact LinearMap.finrank_le_finrank_of_surjective (f := F.toLinearMap) hF
theorem component_mass_le {I : Ideal Ambient} {P : Jet}
    (D : Ideal OrdinateAmbient)
    (hfinite : Module.Finite SeedField (OrdinateAmbient ⧸ D))
    (hcontains : ∀ Q ∈ movingComponents I P, D ≤ ordinateIdeal Q)
    (hloc : ∀ Q : Ideal Ambient, Q.IsPrime →
      ordinateIdeal Q = ⊤ ∨
        ((ordinateIdeal Q).IsPrime ∧ (ordinateIdeal Q).comap (genericBase FX) = Q)) :
    curveYMass (movingComponents I P) ≤ Module.finrank SeedField (OrdinateAmbient ⧸ D) := by
  classical
  let S := movingComponents I P
  let J (i : S) := ordinateIdeal i.val
  have hle (i : S) : D ≤ J i := hcontains i.val i.property
  let := hfinite
  have hq (i : S) :
      J i = ⊤ ∨ ((J i).IsMaximal ∧ (J i).comap (genericBase FX) = i.val) := by
    have hp := (Ideal.mem_minimalPrimesFinset.mp (Finset.mem_filter.mp i.property).1).isPrime
    rcases hloc i.val hp with htop | ⟨hprime, hcomap⟩
    · exact Or.inl htop
    · let : (J i).IsPrime := hprime
      let : Module.Finite SeedField (OrdinateAmbient ⧸ J i) :=
        Module.Finite.of_surjective (Ideal.Quotient.factorₐ SeedField (hle i)).toLinearMap
          (Ideal.Quotient.factor_surjective (hle i))
      exact Or.inr ⟨Ideal.Quotient.maximal_of_isField (J i)
        (IsField.of_isDomain_of_finite SeedField (OrdinateAmbient ⧸ J i)), hcomap⟩
  have hpair : Pairwise fun i j : S => IsCoprime (J i) (J j) := by
    intro i j hij
    rcases hq i with htop | ⟨hmaxi, hci⟩
    · simp [Ideal.isCoprime_iff_sup_eq, htop]
    rcases hq j with htop | ⟨hmaxj, hcj⟩
    · simp [Ideal.isCoprime_iff_sup_eq, htop]
    let := hmaxi
    let := hmaxj
    apply Ideal.isCoprime_of_isMaximal
    intro heq
    apply hij
    apply Subtype.ext
    rw [← hci, ← hcj, heq]
  have h := sum_finrank_quotients_le (k := SeedField) D J hle hpair
  rw [curveYMass, ← Finset.sum_attach]
  exact h
theorem cut_le_ordinateIdeal {I Q : Ideal Ambient} {P : Jet}
    (hQ : Q ∈ cutComponents I P) :
    ordinateIdeal I ⊔ Ideal.span {blockEval (specializeJet P)} ≤ ordinateIdeal Q := by
  have hmin := Ideal.mem_minimalPrimesFinset.mp hQ
  have hle : I ⊔ Ideal.span {toJet P} ≤ Q := hmin.le
  refine sup_le (sup_le_sup (Ideal.map_mono (le_sup_left.trans hle)) le_rfl) ?_
  apply (Ideal.span_singleton_le_iff_mem _).mpr
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [specializeJet_mk]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (hle
    (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))))
end
end K1_14_2_2_7_3
end
section
namespace K1_14_2_2_7_3
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_7
def c1 : Prop :=
  ∀ (I : Ideal Ambient), I.IsPrime → ringKrullDim (CoordinateRing I) = 2 →
    Function.Injective ((Ideal.Quotient.mk I).comp ordinateIncl) →
    ringKrullDim (JetYSection I) = 1
def c2 : Prop :=
  ∀ (I : Ideal Ambient),
    Module.Finite SectionField (OverOrdinate I) →
    Module.Finite SeedField (OverJets I) →
    Module.Finite (PlaneField SeedField) (SeedFibre (ordinateIdeal I)) ∧
    Module.Finite (PlaneField SeedField) (VFibre (ordinateIdeal I)) ∧
    Module.finrank (PlaneField SeedField) (SeedFibre (ordinateIdeal I)) =
      Module.finrank SectionField (OverOrdinate I) ∧
    Module.finrank (PlaneField SeedField) (VFibre (ordinateIdeal I)) =
      Module.finrank SeedField (OverJets I)
def c3 : Prop :=
  ∀ (k : Type) [Field k] (H : Ideal (MvPolynomial (Fin 4) k)) (U J : ℕ)
    (G : Polynomial (MvPolynomial (Fin 2) k)),
    H.IsPrime → ringKrullDim (CoordinateRing H) = 1 →
    Module.Finite (PlaneField k) (SeedFibre H) →
    Module.Finite (PlaneField k) (VFibre H) →
    G.natDegree ≤ J → (∀ j, (G.coeff j).totalDegree ≤ U) → blockEval G ∉ H →
    Module.Finite k (CoordinateRing (H ⊔ Ideal.span {blockEval G})) ∧
    Module.finrank k (CoordinateRing (H ⊔ Ideal.span {blockEval G})) ≤
      U * Module.finrank (PlaneField k) (SeedFibre H) +
      J * Module.finrank (PlaneField k) (VFibre H)
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) :
    K1_14_2_2_7.c3 := by
  classical
  intro s I P _ hI hcaps hP
  obtain ⟨hprime, hcomap⟩ := (ordinate_localization I hI.prime).1 hI.ordinate_dominant
  have hdim := h1 I hI.prime hI.dimension hI.ordinate_dominant
  obtain ⟨hseed, hv, hseedrank, hvrank⟩ := h2 I hI.ordinate_finite hI.jet_finite
  obtain ⟨hdeg, hcoeff⟩ := specializeJet_caps hcaps
  have hproper : blockEval (specializeJet P) ∉ ordinateIdeal I := by
    intro h
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr h
    rw [specializeJet_mk] at hz
    have hmem : toJet P ∈ (ordinateIdeal I).comap (genericBase FX) :=
      show genericBase FX (toJet P) ∈ ordinateIdeal I from Ideal.Quotient.eq_zero_iff_mem.mp hz
    exact hP (hcomap ▸ hmem)
  obtain ⟨hfinite, hlength⟩ :=
    h3 SeedField (ordinateIdeal I) s.U s.J (specializeJet P) hprime hdim
      hseed hv hdeg hcoeff hproper
  have hmass := component_mass_le (I := I) (P := P) _ hfinite
    (fun _ hQ => cut_le_ordinateIdeal (Finset.mem_filter.mp hQ).1)
    (fun Q hp => by
      by_cases hdom : Function.Injective ((Ideal.Quotient.mk Q).comp ordinateIncl)
      · exact Or.inr ((ordinate_localization Q hp).1 hdom)
      · exact Or.inl ((ordinate_localization Q hp).2 hdom))
  apply hmass.trans
  simpa [hseedrank, hvrank, dot, weight, sectionDegree, Fin.sum_univ_four] using hlength
end
end K1_14_2_2_7_3
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace K1_14_2_2_7_1
noncomputable section
open K1_14 K1_14_2 K1_14_2_2_7 Polynomial
open scoped Polynomial
private theorem trdeg_le_one {A : Type} [CommRing A] [IsDomain A] [Algebra FX A]
    [Algebra.FiniteType FX A] (hdim : ringKrullDim A = 1) :
    Algebra.trdeg FX A ≤ 1 := by
  obtain ⟨d, f, hf, hfint⟩ := exists_finite_inj_algHom_of_fg FX A
  let B := MvPolynomial (Fin d) FX
  let : Algebra B A := f.toRingHom.toAlgebra
  let : IsScalarTower FX B A := IsScalarTower.of_algHom f
  let : Module.Finite B A := hfint
  let : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  let : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hf
  have hdB : ringKrullDim B = (d : WithBot ℕ∞) := by
    simp [B, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field]
  obtain ⟨l, hlen⟩ := Order.le_krullDim_iff.mp hdB.ge
  have := l.head.isPrime
  have hle : (⊥ : Ideal A).under B ≤ l.head.asIdeal := by
    change Ideal.comap (algebraMap B A) ⊥ ≤ l.head.asIdeal
    rw [← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective B A)]
    exact bot_le
  obtain ⟨P, _, hP, hPhead⟩ := Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal
    (⊥ : Ideal A) hle
  let : P.IsPrime := hP
  let : P.LiesOver l.head.asIdeal := ⟨hPhead.symm⟩
  obtain ⟨L, hL, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  have hle : (d : WithBot ℕ∞) ≤ ringKrullDim A :=
    Order.le_krullDim_iff.mpr ⟨L, hL.trans hlen⟩
  rw [hdim] at hle
  have hd : d ≤ 1 := by exact_mod_cast hle
  have ht := trdeg_add_eq FX B (A := A)
  rw [trdeg_eq_zero (R := B) (A := A), add_zero] at ht
  rw [← ht]
  change Algebra.trdeg FX (MvPolynomial (Fin d) FX) ≤ 1
  rw [MvPolynomial.trdeg_of_isDomain]
  simpa using (Nat.cast_le.mpr hd : (d : Cardinal.{0}) ≤ (1 : ℕ))
private def parameters {A : Type} [CommRing A] [Algebra FX A] (a b : A) :
    Seeds →ₐ[FX] A[X] :=
  ⟨MvPolynomial.eval₂Hom (C.comp (algebraMap FX A)) ![Polynomial.X, C a + Polynomial.X * C b],
    fun c => by
      change MvPolynomial.eval₂Hom (C.comp (algebraMap FX A)) _ (MvPolynomial.C c) =
        C (algebraMap FX A c)
      rw [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]⟩
@[simp] private theorem parameters_C {A : Type} [CommRing A] [Algebra FX A]
    (a b : A) (c : FX) : parameters a b (MvPolynomial.C c) = C (algebraMap FX A c) :=
  (parameters a b).commutes c
@[simp] private theorem parameters_X_zero {A : Type} [CommRing A] [Algebra FX A]
    (a b : A) : parameters a b (MvPolynomial.X 0) = Polynomial.X := by
  simp [parameters]
@[simp] private theorem parameters_X_one {A : Type} [CommRing A] [Algebra FX A]
    (a b : A) : parameters a b (MvPolynomial.X 1) = C a + Polynomial.X * C b := by
  simp [parameters]
private theorem infinitely_many_slopes {A : Type} [CommRing A] [Algebra FX A] {a b : A}
    (hm : ¬ (IsAlgebraic FX a ∧ IsAlgebraic FX b)) :
    Set.Infinite {c : FX | Transcendental FX (a + algebraMap FX A c * b)} := by
  classical
  let : Infinite FX := Infinite.of_injective _ (IsFractionRing.injective L[X] FX)
  let z (c : FX) := a + algebraMap FX A c * b
  change Set.Infinite {c : FX | ¬ IsAlgebraic FX (z c)}
  by_cases h : ∃ c, IsAlgebraic FX (z c)
  · obtain ⟨c, hc⟩ := h
    apply (Set.finite_singleton c).infinite_compl.mono
    intro d hd hda
    have hdc : d - c ≠ 0 := sub_ne_zero.mpr (by simpa using hd)
    have he : z d - z c = algebraMap FX A (d - c) * b := by
      dsimp [z]
      rw [map_sub]
      ring
    have hmul : IsAlgebraic FX (algebraMap FX A (d - c) * b) := he ▸ hda.sub hc
    have hb : IsAlgebraic FX b := by
      have hh := (isAlgebraic_algebraMap (A := A) (d - c)⁻¹).mul hmul
      rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hdc, map_one, one_mul] at hh
    have ha : IsAlgebraic FX a := by
      have hh := hc.sub ((isAlgebraic_algebraMap (A := A) c).mul hb)
      simpa [z] using hh
    exact hm ⟨ha, hb⟩
  · apply Set.infinite_univ.mono
    intro c _ hc
    exact h ⟨c, hc⟩
private theorem parameters_injective {A : Type} [CommRing A] [Algebra FX A] {a b : A}
    (hm : ¬ (IsAlgebraic FX a ∧ IsAlgebraic FX b)) :
    Function.Injective (parameters a b) := by
  classical
  apply (injective_iff_map_eq_zero (parameters a b)).mpr
  intro p hp
  let e := MvPolynomial.finSuccEquiv FX 1
  let S := MvPolynomial (Fin 1) FX
  let z (c : FX) := a + algebraMap FX A c * b
  have hinf := (infinitely_many_slopes hm).image
    (MvPolynomial.C_injective (σ := Fin 1) (R := FX)).injOn
  have hz : e p = 0 := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hinf.mono
    rintro _ ⟨c, hc, rfl⟩
    change Polynomial.eval (MvPolynomial.C c) (e p) = Polynomial.eval (MvPolynomial.C c) 0
    rw [Polynomial.eval_zero]
    let m : S →+* A := MvPolynomial.eval₂Hom (algebraMap FX A) (fun _ => z c)
    have hm_eq : m = (Polynomial.aeval (z c)).toRingHom.comp
        (MvPolynomial.uniqueAlgEquiv FX (Fin 1)).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [m, MvPolynomial.uniqueAlgEquiv_apply, RingHom.comp_apply]
      · intro k
        simp [m, MvPolynomial.uniqueAlgEquiv_apply, RingHom.comp_apply]
    have hminj : Function.Injective m := by
      rw [hm_eq]
      exact (transcendental_iff_injective.mp hc).comp
        (MvPolynomial.uniqueAlgEquiv FX (Fin 1)).injective
    have hcomp : (Polynomial.evalRingHom (algebraMap FX A c)).comp (parameters a b).toRingHom =
        m.comp ((Polynomial.evalRingHom (MvPolynomial.C c)).comp e.toRingHom) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        change Polynomial.eval (algebraMap FX A c) (parameters a b (MvPolynomial.C r)) =
          m (Polynomial.eval (MvPolynomial.C c) (e (MvPolynomial.C r)))
        simp only [parameters_C, e, MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C,
          RingHom.comp_apply, Polynomial.eval_C]
        have hr : Polynomial.eval (MvPolynomial.C c : S) (C (MvPolynomial.C r)) =
          MvPolynomial.C r := by apply Polynomial.eval_C
        exact (MvPolynomial.eval₂Hom_C (algebraMap FX A) (fun _ : Fin 1 => z c) r).symm.trans
          (congrArg m hr.symm)
      · intro k
        change Polynomial.eval (algebraMap FX A c) (parameters a b (MvPolynomial.X k)) =
          m (Polynomial.eval (MvPolynomial.C c) (e (MvPolynomial.X k)))
        have hk : k = 0 ∨ k = 1 := by fin_cases k <;> decide
        rcases hk with rfl | rfl
        · rw [parameters_X_zero, Polynomial.eval_X,
            show e (MvPolynomial.X 0) = Polynomial.X from MvPolynomial.finSuccEquiv_X_zero,
            Polynomial.eval_X]
          exact (MvPolynomial.eval₂Hom_C _ _ _).symm
        · rw [parameters_X_one, show e (MvPolynomial.X 1) = C (MvPolynomial.X 0) from
            MvPolynomial.finSuccEquiv_X_succ (j := (0 : Fin 1))]
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
          have hx : Polynomial.eval (MvPolynomial.C c : S) (C (MvPolynomial.X (0 : Fin 1))) =
            MvPolynomial.X (0 : Fin 1) := by apply Polynomial.eval_C
          calc
            _ = m (MvPolynomial.X (0 : Fin 1)) :=
              (MvPolynomial.eval₂Hom_X' (algebraMap FX A) (fun _ : Fin 1 => z c) _).symm
            _ = _ := congrArg m hx.symm
    apply (injective_iff_map_eq_zero m).mp hminj
    have h := RingHom.congr_fun hcomp p
    change Polynomial.eval (algebraMap FX A c) (parameters a b p) =
      m (Polynomial.eval (MvPolynomial.C c) (e p)) at h
    exact h.symm.trans (by rw [hp, Polynomial.eval_zero])
  exact e.injective (hz.trans (map_zero e).symm)
private theorem parameters_algebraic {A : Type} [CommRing A] [IsDomain A] [Algebra FX A]
    [Algebra.FiniteType FX A] (hdim : ringKrullDim A = 1) (a b : A) :
    letI : Algebra Seeds A[X] := (parameters a b).toRingHom.toAlgebra
    Algebra.IsAlgebraic Seeds A[X] := by
  let f := parameters a b
  let : Algebra Seeds A[X] := f.toRingHom.toAlgebra
  change Algebra.IsAlgebraic Seeds A[X]
  by_cases hf : Function.Injective f
  · let : FaithfulSMul Seeds A[X] := (faithfulSMul_iff_algebraMap_injective Seeds A[X]).mpr hf
    let : IsScalarTower FX Seeds A[X] := IsScalarTower.of_algHom f
    have ht := trdeg_add_eq FX Seeds (A := A[X])
    have hA := trdeg_add_eq FX A (A := A[X])
    have he : Algebra.trdeg FX Seeds = 2 := by
      simp [MvPolynomial.trdeg_of_isDomain]
    rw [he] at ht
    rw [Polynomial.trdeg_of_isDomain] at hA
    have hsmall : Algebra.trdeg FX A[X] ≤ 2 := by
      rw [← hA]
      calc
        _ ≤ (1 : Cardinal.{0}) + 1 := add_le_add (trdeg_le_one hdim) le_rfl
        _ = 2 := one_add_one_eq_two
    have hfin : (2 : Cardinal.{0}) + Algebra.trdeg Seeds A[X] ≤ 2 :=
      ht.le.trans hsmall
    rw [← trdeg_eq_zero_iff]
    by_contra h
    have hpos : (1 : Cardinal) ≤ Algebra.trdeg Seeds A[X] := Cardinal.one_le_iff_ne_zero.mpr h
    have hbad : (2 : Cardinal.{0}) + 1 ≤ 2 := (add_le_add le_rfl hpos).trans hfin
    have hn : (3 : ℕ) ≤ 2 := by exact_mod_cast hbad
    omega
  · exact Algebra.isAlgebraic_of_not_injective hf
private abbrev Over := MvPolynomial (Fin 4) SeedField
private abbrev extend : Ambient →+* Over := MvPolynomial.map (algebraMap FX SeedField)
private abbrev sectionIdeal (Q : Ideal Ambient) (u v : Ambient) : Ideal Over :=
  Q.map extend ⊔ Ideal.span {extend u + MvPolynomial.C (generic 0) * extend v -
    MvPolynomial.C (generic 1)}
private abbrev Fibre (Q : Ideal Ambient) (u v : Ambient) := Over ⧸ sectionIdeal Q u v
private def fromBase (Q : Ideal Ambient) (u v : Ambient) : CoordinateRing Q →+* Fibre Q u v :=
  Ideal.quotientMap (sectionIdeal Q u v) extend (Ideal.map_le_iff_le_comap.mp le_sup_left)
private def fromSlope (Q : Ideal Ambient) (u v : Ambient) :
    (CoordinateRing Q)[X] →+* Fibre Q u v :=
  Polynomial.eval₂RingHom (fromBase Q u v) (algebraMap SeedField (Fibre Q u v) (generic 0))
private theorem section_relation (Q : Ideal Ambient) (u v : Ambient) :
    fromBase Q u v (Ideal.Quotient.mk Q u) +
      algebraMap SeedField (Fibre Q u v) (generic 0) * fromBase Q u v (Ideal.Quotient.mk Q v) =
        algebraMap SeedField (Fibre Q u v) (generic 1) := by
  apply sub_eq_zero.mp
  have h : Ideal.Quotient.mk (sectionIdeal Q u v)
      (extend u + MvPolynomial.C (generic 0) * extend v - MvPolynomial.C (generic 1)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show Ideal.span {_} ≤ sectionIdeal Q u v from le_sup_right)
        (Ideal.mem_span_singleton_self _))
  simpa only [map_sub, map_add, map_mul, ← MvPolynomial.algebraMap_eq,
    Ideal.Quotient.mk_algebraMap, fromBase, Ideal.quotientMap_mk] using h
private theorem parameters_commute (Q : Ideal Ambient) (u v : Ambient) :
    (fromSlope Q u v).comp
      (parameters (Ideal.Quotient.mk Q u) (Ideal.Quotient.mk Q v)).toRingHom =
      (algebraMap SeedField (Fibre Q u v)).comp (algebraMap Seeds SeedField) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [fromSlope, fromBase, RingHom.comp_apply, MvPolynomial.algebraMap_eq]
    rfl
  · intro i
    fin_cases i
    · simp [fromSlope, RingHom.comp_apply, generic]
    · change fromSlope Q u v
          (parameters (Ideal.Quotient.mk Q u) (Ideal.Quotient.mk Q v) (MvPolynomial.X 1)) =
        algebraMap SeedField (Fibre Q u v) (generic 1)
      simp only [parameters_X_one, map_add, map_mul, fromSlope, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X, Polynomial.eval₂_C]
      exact section_relation Q u v
private theorem fibre_finite (Q : Ideal Ambient) [Q.IsPrime] (u v : Ambient)
    (hdim : ringKrullDim (CoordinateRing Q) = 1) :
    Module.Finite SeedField (Fibre Q u v) := by
  let f := parameters (Ideal.Quotient.mk Q u) (Ideal.Quotient.mk Q v)
  let : Algebra Seeds (CoordinateRing Q)[X] := f.toRingHom.toAlgebra
  have hAlg : Algebra.IsAlgebraic Seeds (CoordinateRing Q)[X] :=
    parameters_algebraic (A := CoordinateRing Q) hdim (Ideal.Quotient.mk Q u)
      (Ideal.Quotient.mk Q v)
  let J := sectionIdeal Q u v
  let q := Ideal.Quotient.mk J
  have hgen (i : Fin 4) : IsIntegral SeedField (q (MvPolynomial.X i)) := by
    let x := C (Ideal.Quotient.mk Q (MvPolynomial.X i))
    obtain ⟨p, hp, hz⟩ := hAlg.isAlgebraic x
    refine IsAlgebraic.isIntegral
      ⟨p.map (algebraMap Seeds SeedField),
        (Polynomial.map_ne_zero_iff (IsFractionRing.injective Seeds SeedField)).mpr hp, ?_⟩
    have h := congrArg (fromSlope Q u v) hz
    have hx : fromSlope Q u v x = q (MvPolynomial.X i) := by
      change fromSlope Q u v x = Ideal.Quotient.mk (sectionIdeal Q u v) (MvPolynomial.X i)
      simp only [x, fromSlope, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, fromBase,
        Ideal.quotientMap_mk, MvPolynomial.map_X]
    have hcomm := parameters_commute Q u v
    change (fromSlope Q u v).comp (algebraMap Seeds (CoordinateRing Q)[X]) = _ at hcomm
    rwa [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂, hcomm, hx,
      ← Polynomial.eval₂_map, ← Polynomial.aeval_def] at h
  refine (Algebra.finite_iff_isIntegral_and_finiteType (R := SeedField)
    (A := Fibre Q u v)).mpr ⟨⟨?_⟩, inferInstance⟩
  intro r
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective (I := J) r
  change IsIntegral SeedField (q p)
  induction p using MvPolynomial.induction_on with
  | C c =>
    simpa only [q, ← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap] using
      (isIntegral_algebraMap (A := Fibre Q u v) (x := c))
  | add p p' hp hp' =>
    rw [map_add]
    exact IsIntegral.add (R := SeedField) (A := Fibre Q u v) hp hp'
  | mul_X p i hp =>
    rw [map_mul]
    exact IsIntegral.mul (R := SeedField) (A := Fibre Q u v) hp (hgen i)
private theorem fibre_nontrivial (Q : Ideal Ambient) [Q.IsPrime] (u v : Ambient)
    (hinj : Function.Injective (parameters (Ideal.Quotient.mk Q u) (Ideal.Quotient.mk Q v))) :
    Nontrivial (Fibre Q u v) := by
  let A := CoordinateRing Q
  let : CommRing A := Ideal.Quotient.commRing Q
  let : IsDomain A := Ideal.Quotient.isDomain Q
  let F := FractionRing A[X]
  let m : A[X] →+* F := algebraMap _ _
  let f := parameters (Ideal.Quotient.mk Q u) (Ideal.Quotient.mk Q v)
  let g : SeedField →+* F := IsFractionRing.lift (g := m.comp f.toRingHom)
    ((IsFractionRing.injective A[X] F).comp hinj)
  have hg (d : Seeds) : g (algebraMap Seeds SeedField d) = m (f d) :=
    IsFractionRing.lift_algebraMap _ d
  let e : Over →+* F :=
    MvPolynomial.eval₂Hom g (fun i => m (C (Ideal.Quotient.mk Q (MvPolynomial.X i))))
  have he : e.comp extend = (m.comp C).comp (Ideal.Quotient.mk Q) := by
    apply MvPolynomial.ringHom_ext
    · intro d
      have hd : algebraMap FX SeedField d = algebraMap Seeds SeedField (MvPolynomial.C d) := rfl
      simp only [e, RingHom.comp_apply, MvPolynomial.map_C, MvPolynomial.eval₂Hom_C, hd, hg]
      exact congrArg m (f.commutes d)
    · intro i
      simp only [e, RingHom.comp_apply, MvPolynomial.map_X, MvPolynomial.eval₂Hom_X']
      rfl
  have hker : sectionIdeal Q u v ≤ RingHom.ker e := by
    refine sup_le (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
    · intro r hr
      change (e.comp extend) r = 0
      rw [he]
      change m (C (Ideal.Quotient.mk Q r)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero, map_zero]
    · intro r hr
      obtain rfl := Set.mem_singleton_iff.mp hr
      apply RingHom.mem_ker.mpr
      have hu := RingHom.congr_fun he u
      have hv := RingHom.congr_fun he v
      change e (extend u) = m (C (Ideal.Quotient.mk Q u)) at hu
      change e (extend v) = m (C (Ideal.Quotient.mk Q v)) at hv
      have hC (i : Fin 2) : e (MvPolynomial.C (generic i)) = m (f (MvPolynomial.X i)) :=
        (MvPolynomial.eval₂Hom_C g _ _).trans (hg _)
      rw [map_sub, map_add, map_mul, hu, hv, hC 0, hC 1]
      change m (C (Ideal.Quotient.mk Q u)) + m (f (MvPolynomial.X 0)) *
        m (C (Ideal.Quotient.mk Q v)) - m (f (MvPolynomial.X 1)) = 0
      simp only [f, parameters_X_zero, parameters_X_one, map_add, map_mul]
      exact sub_self _
  let φ : Fibre Q u v →+* F := Ideal.Quotient.lift _ e hker
  exact nontrivial_of_ne (1 : Fibre Q u v) 0 (fun h => one_ne_zero (by
    simpa only [map_one, map_zero] using congrArg φ h))
theorem proof : K1_14_2_2_7.c1 := by
  intro Q hQ hdim hMove
  let : Q.IsPrime := hQ
  have hm : ¬ (IsAlgebraic FX (Ideal.Quotient.mk Q (MvPolynomial.X 0)) ∧
      IsAlgebraic FX (Ideal.Quotient.mk Q (MvPolynomial.X 1))) := by
    intro h
    apply hMove
    intro i
    fin_cases i
    · exact h.1
    · exact h.2
  let u : Ambient := MvPolynomial.X 0
  let v : Ambient := MvPolynomial.X 1
  have hseed : sectionIdeal Q u v = Q.map extend ⊔ Ideal.span {seedLine 0 1} := by
    simp [sectionIdeal, u, v, seedLine]
  have hy : sectionIdeal Q (MvPolynomial.X 2) 0 = Q.map extend ⊔ Ideal.span {ySection 2} := by
    simp [sectionIdeal, ySection]
  have hSeed : Module.Finite SeedField (JetSeedSection Q) := by
    change Module.Finite SeedField (Over ⧸ (Q.map extend ⊔ Ideal.span {seedLine 0 1}))
    rw [← hseed]
    exact fibre_finite Q u v hdim
  let : Module.Finite SeedField (JetSeedSection Q) := hSeed
  let : Nontrivial (JetSeedSection Q) := by
    change Nontrivial (Over ⧸ (Q.map extend ⊔ Ideal.span {seedLine 0 1}))
    rw [← hseed]
    exact fibre_nontrivial Q u v (parameters_injective hm)
  refine ⟨hSeed, Module.finrank_pos, ?_⟩
  change Module.Finite SeedField (Over ⧸ (Q.map extend ⊔ Ideal.span {ySection 2}))
  rw [← hy]
  exact fibre_finite Q (MvPolynomial.X 2) 0 hdim
end
end K1_14_2_2_7_1
end
section
set_option autoImplicit false
namespace K1_14_2_2_7_4_4_7
noncomputable section
open K1_14_2_2_7_4_4
open IsDedekindDomain
variable {F K : Type} [Field F] [Field K] [Algebra F K]
def centered (B : Type) [CommRing B] [Algebra B K] (w : Place F K) : Prop :=
  ∀ b : B, w.val (algebraMap B K b) ≤ 1
def chartPlace {B : Type} [CommRing B] [IsDedekindDomain B]
    [Algebra F B] [Algebra B K] [IsScalarTower F B K] [IsFractionRing B K]
    (p : HeightOneSpectrum B) : Place F K where
  val := p.valuation K
  surj := p.valuation_surjective K
  trivial c hc := by
    rw [IsScalarTower.algebraMap_apply F B K, p.valuation_eq_one_iff_notMem]
    exact fun hm => p.isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ hm ((isUnit_iff_ne_zero.mpr hc).map (algebraMap F B)))
abbrev InfinityRing (F : Type) [Field F] :=
  (@RatFunc.inftyValuation F _ (Classical.decEq _)).valuationSubring
instance infinityAlgebra (F : Type) [Field F] : Algebra F (InfinityRing F) :=
  ((algebraMap F (RatFunc F)).codRestrict (InfinityRing F).toSubring fun c => by
    classical
    change RatFunc.inftyValuation F (algebraMap F (RatFunc F) c) ≤ 1
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · rw [RatFunc.algebraMap_eq_C, RatFunc.inftyValuation.C F hc]).toAlgebra
instance infinityTower (F : Type) [Field F] : IsScalarTower F (InfinityRing F) (RatFunc F) :=
  IsScalarTower.of_algebraMap_eq' rfl
end
end K1_14_2_2_7_4_4_7
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_7_4_4_3
noncomputable section
open K1_14_2 K1_14_2_2_7_4 K1_14_2_2_7_4_4
open scoped TensorProduct
private theorem degree_of_generating_image {E F K B : Type}
    [Field E] [Field F] [Field K] [CommRing B] [Algebra E B] [Algebra F K]
    [Module.Finite E B] (embed : E →+* F) (f : B →+* K)
    (hcomm : ∀ a, f (algebraMap E B a) = algebraMap F K (embed a))
    (hgen : ∀ S : IntermediateField F K, (∀ b, f b ∈ S) → ∀ x : K, x ∈ S) :
    Module.Finite F K ∧ Module.finrank F K ≤ Module.finrank E B := by
  let : Algebra E F := embed.toAlgebra
  let : Algebra E K := ((algebraMap F K).comp embed).toAlgebra
  let : IsScalarTower E F K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let fAlg : B →ₐ[E] K := { f with commutes' := hcomm }
  let q : F ⊗[E] B →ₐ[F] K := AlgHom.liftEquiv E F B K fAlg
  let : Module.Finite F q.range :=
    Module.Finite.of_surjective q.rangeRestrict.toLinearMap q.rangeRestrict_surjective
  let S : IntermediateField F K := q.range.toIntermediateField fun x hx =>
    q.range.inv_mem_of_algebraic
      (Subalgebra.isAlgebraic_iff_isAlgebraic_val.mp (IsAlgebraic.of_finite F (⟨x, hx⟩ : q.range)))
  have hmem (b : B) : f b ∈ S := by
    change f b ∈ q.range
    exact q.mem_range.mpr ⟨1 ⊗ₜ[E] b, by simp [q, fAlg]⟩
  have hq : Function.Surjective q := fun x => q.mem_range.mp (hgen S hmem x)
  refine ⟨Module.Finite.of_surjective q.toLinearMap hq, ?_⟩
  calc
    Module.finrank F K ≤ Module.finrank F (F ⊗[E] B) :=
      LinearMap.finrank_le_finrank_of_surjective hq
    _ = Module.finrank E B := Module.finrank_baseChange
variable {k : Type} [Field k] (D : Ideal (CurvePoly k)) [IsDomain (SlopedCurve D)]
private abbrev ParameterField :=
  IntermediateField.adjoin (SlopeField k) ({fieldCoord D none} : Set (CurveField D))
set_option maxHeartbeats 600000 in
private theorem all_mem_of_coordinates (S : IntermediateField (ParameterField D) (CurveField D))
    (hcoord : ∀ i, fieldCoord D i ∈ S) (x : CurveField D) : x ∈ S := by
  let g : CurvePoly (SlopeField k) →+* CurveField D :=
    (algebraMap (SlopedCurve D) (CurveField D)).comp (Ideal.Quotient.mk (slopeIdeal D))
  have hX (i : Option (Fin 2)) : g (MvPolynomial.X i) = fieldCoord D i := by
    simp [g, fieldCoord, fieldEval, slopeMap]
  have hC (a : SlopeField k) : g (MvPolynomial.C a) ∈ S := by
    change algebraMap (SlopedCurve D) (CurveField D) (algebraMap (SlopeField k) (SlopedCurve D) a) ∈ S
    rw [← IsScalarTower.algebraMap_apply (SlopeField k) (SlopedCurve D) (CurveField D)]
    have hm := S.algebraMap_mem (algebraMap (SlopeField k) (ParameterField D) a)
    exact ((ParameterField D).val.commutes a) ▸ hm
  have hpoly (p : CurvePoly (SlopeField k)) : g p ∈ S := by
    induction p using MvPolynomial.induction_on with
    | C a => exact hC a
    | add p q hp hq =>
      rw [g.map_add p q]
      exact S.add_mem hp hq
    | mul_X p i hp =>
      rw [g.map_mul p (MvPolynomial.X i), hX i]
      exact S.mul_mem hp (hcoord i)
  have ha (a : SlopedCurve D) : algebraMap (SlopedCurve D) (CurveField D) a ∈ S := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective (I := slopeIdeal D) a
    exact hpoly p
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (SlopedCurve D) x
  exact S.div_mem (ha a) (ha b)
set_option maxHeartbeats 600000 in
theorem proof : K1_14_2_2_7_4_4.c3 := by
  intro k _ D _ hfinite
  let := hfinite
  by_cases hv : IsAlgebraic (SlopeField k) (fieldCoord D none)
  · exact Or.inl hv
  refine Or.inr ⟨hv, ?_⟩
  let F := SlopeField k
  let K := CurveField D
  let L := ParameterField D
  let v : L := ⟨fieldCoord D none, IntermediateField.subset_adjoin F _ (Set.mem_singleton _)⟩
  let pEval : Polynomial k →+* L :=
    Polynomial.eval₂RingHom ((algebraMap F L).comp (algebraMap k F)) v
  have hbase : (algebraMap L K).comp (algebraMap F L) = algebraMap F K :=
    RingHom.ext (ParameterField D).val.commutes
  have hp (p : Polynomial k) :
      algebraMap L K (pEval p) =
        Polynomial.aeval (fieldCoord D none) (Polynomial.map (algebraMap k F) p) := by
    change algebraMap L K (p.eval₂ ((algebraMap F L).comp (algebraMap k F)) v) = _
    rw [Polynomial.hom_eval₂, Polynomial.aeval_def, Polynomial.eval₂_map]
    rw [← RingHom.comp_assoc, hbase]
    rfl
  have hpInj : Function.Injective pEval := by
    intro p q h
    apply Polynomial.map_injective (algebraMap k F) (algebraMap k F).injective
    exact (transcendental_iff_injective.mp hv)
      ((hp p).symm.trans ((congrArg (algebraMap L K) h).trans (hp q)))
  let embed : VField k →+* L := IsFractionRing.lift hpInj
  let ev : MvPolynomial (Fin 2) (VField k) →+* K :=
    MvPolynomial.eval₂Hom ((algebraMap L K).comp embed) (fun i => fieldCoord D (some i))
  have hev : ev.comp (vFibreMap k) = fieldEval D := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change ev (vFibreMap k (MvPolynomial.C a)) =
        algebraMap (SlopedCurve D) K (Ideal.Quotient.mk (slopeIdeal D)
          (MvPolynomial.map (algebraMap k F) (MvPolynomial.C a)))
      rw [MvPolynomial.map_C]
      rw [show vFibreMap k (MvPolynomial.C a) = MvPolynomial.C (algebraMap k (VField k) a) from
        MvPolynomial.eval₂Hom_C _ _ _]
      rw [show ev (MvPolynomial.C (algebraMap k (VField k) a)) =
        algebraMap L K (embed (algebraMap k (VField k) a)) from MvPolynomial.eval₂Hom_C _ _ _]
      change algebraMap L K (embed (algebraMap k (VField k) a)) =
        algebraMap (SlopedCurve D) K (algebraMap F (SlopedCurve D) (algebraMap k F a))
      have heval : embed (algebraMap k (VField k) a) = pEval (Polynomial.C a) := by
        rw [IsScalarTower.algebraMap_apply k (Polynomial k) (VField k) a]
        exact IsFractionRing.lift_algebraMap hpInj _
      rw [heval, hp, Polynomial.map_C, Polynomial.aeval_C]
      exact IsScalarTower.algebraMap_apply F (SlopedCurve D) K (algebraMap k F a)
    · intro i
      change ev (vFibreMap k (MvPolynomial.X i)) = fieldCoord D i
      rw [show vFibreMap k (MvPolynomial.X i) = i.elim
        (MvPolynomial.C (algebraMap (Polynomial k) (VField k) Polynomial.X)) MvPolynomial.X from
          MvPolynomial.eval₂Hom_X' _ _ i]
      cases i with
      | none =>
        change ev (MvPolynomial.C (algebraMap (Polynomial k) (VField k) Polynomial.X)) =
          fieldCoord D none
        simp only [ev, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, embed,
          IsFractionRing.lift_algebraMap, hp, Polynomial.map_X, Polynomial.aeval_X]
      | some i => exact MvPolynomial.eval₂Hom_X' _ _ i
  let J := D.map (vFibreMap k)
  let f : VFibre D →+* K := Ideal.Quotient.lift J ev (by
    have hkill : J ≤ RingHom.ker ev := by
      rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker, hev]
      intro p hp
      change algebraMap (SlopedCurve D) K (Ideal.Quotient.mk (slopeIdeal D) (slopeMap k p)) = 0
      have hz : Ideal.Quotient.mk (slopeIdeal D) (slopeMap k p) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem (slopeMap k) hp)
      rw [hz, map_zero]
    exact fun p hp => hkill hp)
  have hfC (a : VField k) : f (algebraMap (VField k) (VFibre D) a) = algebraMap L K (embed a) := by
    change ev (MvPolynomial.C a) = _
    exact MvPolynomial.eval₂Hom_C _ _ _
  refine degree_of_generating_image embed f hfC fun S hS => all_mem_of_coordinates D S ?_
  intro i
  cases i with
  | none => exact S.algebraMap_mem v
  | some i =>
    have h := hS (Ideal.Quotient.mk J (MvPolynomial.X i))
    change ev (MvPolynomial.X i) ∈ S at h
    simpa only [ev, MvPolynomial.eval₂Hom_X'] using h
end
end K1_14_2_2_7_4_4_3
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_7_4_4_7
noncomputable section
open K1_14_2_2_7_4_4
open IsDedekindDomain
open scoped WithZero nonZeroDivisors
private theorem surjective_valuation_eq {K : Type} [Field K] {v w : Valuation K ℤᵐ⁰}
    (h : v.IsEquiv w) (hv : Function.Surjective v) (hw : Function.Surjective w) : v = w := by
  obtain ⟨x, hx⟩ := hv (WithZero.exp 1)
  have vxPow (n : ℤ) : v (x ^ n) = WithZero.exp n := by
    rw [map_zpow₀, hx, ← WithZero.exp_zsmul, zsmul_eq_mul, mul_one, Int.cast_id]
  have hxPos : 1 < w x := by
    have hpos : v 1 < v x := by simp [hx]
    simpa only [map_one] using h.lt_iff_lt.mp hpos
  have hlogPos : 0 < WithZero.log (w x) :=
    (WithZero.lt_log_iff_exp_lt ((zero_lt_one.trans hxPos).ne')).mpr (by simpa using hxPos)
  obtain ⟨b, hb⟩ := hw (WithZero.exp 1)
  have hb' : v b ≠ 0 := h.eq_zero.ne.mpr (by simp [hb])
  have hbPow : v (x ^ WithZero.log (v b)) = v b := by
    rw [vxPow, WithZero.exp_log hb']
  have hmul : WithZero.log (v b) * WithZero.log (w x) = 1 := by
    have heq := congrArg WithZero.log (h.eq_iff.mp hbPow)
    simpa only [map_zpow₀, WithZero.log_zpow, zsmul_eq_mul, Int.cast_id, id_eq, hb, WithZero.log_exp] using heq
  have hlog : WithZero.log (w x) = 1 := by
    have hi : IsUnit (WithZero.log (w x)) := IsUnit.of_mul_eq_one _ (by simpa [mul_comm] using hmul)
    rcases Int.isUnit_iff.mp hi with he | he <;> omega
  have hwx : w x = WithZero.exp 1 := by
    rw [← hlog, WithZero.exp_log ((zero_lt_one.trans hxPos).ne')]
  apply Valuation.ext
  intro a
  by_cases ha : a = 0
  · simp [ha]
  have hxa : v (x ^ WithZero.log (v a)) = v a := by
    rw [vxPow, WithZero.exp_log ((map_ne_zero v).mpr ha)]
  have hwa := h.eq_iff.mp hxa
  rw [map_zpow₀, hwx, ← WithZero.exp_zsmul, zsmul_eq_mul, mul_one,
    Int.cast_id, WithZero.exp_log ((map_ne_zero v).mpr ha)] at hwa
  exact hwa
private theorem place_eq_of_val_eq {F K : Type} [Field F] [Field K] [Algebra F K]
    {w w' : Place F K} (h : w.val = w'.val) : w = w' := by
  cases w
  cases w'
  cases h
  rfl
theorem chartPlace_enumerates (F B K : Type) [Field F] [CommRing B] [IsDedekindDomain B]
    [Field K] [Algebra F B] [Algebra F K] [Algebra B K] [IsScalarTower F B K] [IsFractionRing B K] :
    Function.Injective (chartPlace (F := F) (K := K) : HeightOneSpectrum B → Place F K) ∧
      ∀ w : Place F K, centered B w → ∃ p : HeightOneSpectrum B, chartPlace p = w := by
  refine ⟨fun _ _ h => HeightOneSpectrum.valuation_injective K (congrArg Place.val h), ?_⟩
  intro w hw
  let O := w.val.valuationSubring
  let f : B →+* O := (algebraMap B K).codRestrict O.toSubring fun b =>
    (Valuation.mem_valuationSubring_iff _ _).mpr (hw b)
  let P := (IsLocalRing.maximalIdeal O).comap f
  have hP (b : B) : b ∈ P ↔ w.val (algebraMap B K b) < 1 :=
    Valuation.mem_maximalIdeal_iff K w.val (a := f b)
  have hP0 : P ≠ ⊥ := by
    intro hp
    have hval (b : B) (hb : b ≠ 0) : w.val (algebraMap B K b) = 1 := by
      refine le_antisymm (hw b) (le_of_not_gt fun hlt => hb ?_)
      have hmem := (hP b).mpr hlt
      simpa only [hp, Ideal.mem_bot] using hmem
    obtain ⟨x, hx⟩ := w.surj (WithZero.exp (-1))
    obtain ⟨n, d, hd, he⟩ := IsFractionRing.div_surjective B x
    have hn : n ≠ 0 := by
      intro hz
      rw [hz, map_zero, zero_div] at he
      rw [← he, map_zero] at hx
      exact WithZero.exp_ne_zero hx.symm
    rw [← he, map_div₀, hval n hn, hval d (mem_nonZeroDivisors_iff_ne_zero.mp hd)] at hx
    simpa using hx.symm
  let p : HeightOneSpectrum B :=
    ⟨P, Ideal.IsPrime.comap f (K := IsLocalRing.maximalIdeal O), hP0⟩
  have hle : (p.valuation K).valuationSubring ≤ O := by
    intro x hx
    obtain ⟨n, d, hnd⟩ := p.exists_primeCompl_mul_eq_of_integer x
      ((Valuation.mem_valuationSubring_iff _ _).mp hx)
    have hd1 : w.val (algebraMap B K d) = 1 :=
      le_antisymm (hw d) (le_of_not_gt fun hlt => d.2 ((hP d).mpr hlt))
    have he := congrArg w.val hnd
    simp only [map_mul, hd1, mul_one] at he
    apply (Valuation.mem_valuationSubring_iff w.val x).mpr
    rw [he]
    exact hw n
  have htop : O ≠ ⊤ := by
    intro h
    apply ((Valuation.valuationSubring_eq_top_iff w.val).mp h)
    obtain ⟨x, hx⟩ := w.surj (WithZero.exp 1)
    exact ⟨x, by simp [hx], by simp [hx]⟩
  have heq : (p.valuation K).valuationSubring = O := by
    rw [← p.valuationSubringAtPrime_eq_valuationSubring]
    exact ValuationSubring.eq_of_le_of_ne_top _ (by
      rwa [p.valuationSubringAtPrime_eq_valuationSubring]) htop
  have hequiv : (p.valuation K).IsEquiv w.val := (Valuation.isEquiv_iff_valuationSubring ..).mpr heq
  exact ⟨p, place_eq_of_val_eq (surjective_valuation_eq hequiv (p.valuation_surjective K) w.surj)⟩
end
end K1_14_2_2_7_4_4_7
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_7_4_4_7
noncomputable section
open K1_14_2_2_7_4_4
open IsDedekindDomain
open scoped Polynomial RatFunc WithZero nonZeroDivisors
def c1 : Prop :=
  ∀ (F B K : Type) [Field F] [CommRing B] [IsDedekindDomain B] [Field K]
    [Algebra F B] [Algebra F K] [Algebra B K] [IsScalarTower F B K] [IsFractionRing B K]
    (a : B), a ≠ 0 → Module.Finite F (B ⧸ Ideal.span {a}) →
    ∃ U : Finset (HeightOneSpectrum B),
      (∀ p : HeightOneSpectrum B, p ∈ U ↔ a ∈ p.asIdeal) ∧
      Module.finrank F (B ⧸ Ideal.span {a}) =
        ∑ p ∈ U, residueDegree (chartPlace p : Place F K) *
          zeroOrder (chartPlace p : Place F K) (algebraMap B K a)
def c2 : Prop :=
  ∀ (F : Type) [Field F] (a : InfinityRing F), a ≠ 0 →
    Module.Finite F (InfinityRing F ⧸ Ideal.span {a}) ∧
      (Module.finrank F (InfinityRing F ⧸ Ideal.span {a}) : ℤ) =
        -(algebraMap (InfinityRing F) (RatFunc F) a).intDegree
private theorem degree_one {R : Type} [CommRing R] [IsDomain R] (d : R → ℤ)
    (hd : ∀ x y : R, x ≠ 0 → y ≠ 0 → d (x * y) = d x + d y) : d 1 = 0 := by
  have h := hd 1 1 one_ne_zero one_ne_zero
  rw [one_mul] at h
  omega
private theorem degree_prod {R ι : Type} [CommRing R] [IsDomain R] (d : R → ℤ)
    (hd : ∀ x y : R, x ≠ 0 → y ≠ 0 → d (x * y) = d x + d y)
    (s : Finset ι) (f : ι → R) (hf : ∀ i ∈ s, f i ≠ 0) :
    d (∏ i ∈ s, f i) = ∑ i ∈ s, d (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [degree_one d hd]
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, f j ≠ 0 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      hd _ _ (hf i (Finset.mem_insert_self i s)) (Finset.prod_ne_zero_iff.mpr hs), ih hs]
private theorem quotient_norm {F R B : Type} [Field F]
    [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Algebra F R]
    [CommRing B] [IsDomain B] [Algebra R B] [Algebra F B] [IsScalarTower F R B]
    [Module.Free R B] [Module.Finite R B] (d : R → ℤ)
    (hd : ∀ x y : R, x ≠ 0 → y ≠ 0 → d (x * y) = d x + d y)
    (hbase : ∀ a : R, a ≠ 0 → Module.Finite F (R ⧸ Ideal.span {a}) ∧
      (Module.finrank F (R ⧸ Ideal.span {a}) : ℤ) = d a)
    (a : B) (ha : a ≠ 0) :
    Module.Finite F (B ⧸ Ideal.span {a}) ∧
      (Module.finrank F (B ⧸ Ideal.span {a}) : ℤ) = d (Algebra.norm R a) := by
  classical
  let b := Module.Free.chooseBasis R B
  let I : Ideal B := Ideal.span {a}
  have hI : I ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr ha
  let s := I.smithCoeffs b hI
  have hs (i : Module.Free.ChooseBasisIndex R B) : s i ≠ 0 := I.smithCoeffs_ne_zero b hI i
  let (i : Module.Free.ChooseBasisIndex R B) : Module.Finite F (R ⧸ Ideal.span {s i}) :=
    (hbase _ (hs i)).1
  have hfin : Module.Finite F (B ⧸ I) :=
    Module.Finite.equiv ((I.quotientEquivPiSpan b hI).restrictScalars F).symm
  refine ⟨hfin, ?_⟩
  have hsum : Module.finrank F (B ⧸ I) = ∑ i, Module.finrank F (R ⧸ Ideal.span {s i}) :=
    Ideal.finrank_quotient_eq_sum F b (hI := hI)
  rw [hsum, Nat.cast_sum]
  simp_rw [(hbase _ (hs _)).2]
  rw [← degree_prod d hd Finset.univ s (fun i _ => hs i)]
  obtain ⟨u, hu⟩ := associated_norm_prod_smith b ha
  have hu0 : (u : R) ≠ 0 := Units.ne_zero u
  have huTop : Ideal.span ({(u : R)} : Set R) = ⊤ := Ideal.span_singleton_eq_top.mpr u.isUnit
  have huRank : Module.finrank F (R ⧸ Ideal.span ({(u : R)} : Set R)) = 0 := by
    rw [huTop]
    exact Module.finrank_zero_of_subsingleton
  have huDeg : d (u : R) = 0 := by simpa [huRank] using (hbase (u : R) hu0).2.symm
  rw [← hu, hd _ _ (Algebra.norm_ne_zero_iff.mpr ha) hu0, huDeg, add_zero]
section Chart
variable {F K : Type} [Field F] [Field K] [Algebra F K]
private def signedWeight (w : Place F K) (g : K) : ℤ :=
  (residueDegree w : ℤ) * WithZero.log (w.val g)
private theorem signedWeight_div (w : Place F K) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    signedWeight w (x / y) = signedWeight w x - signedWeight w y := by
  simp only [signedWeight, map_div₀, WithZero.log_div ((map_ne_zero w.val).mpr hx)
    ((map_ne_zero w.val).mpr hy), mul_sub]
private theorem degree_diff (U : Finset (Place F K)) (g : K) :
    ∑ w ∈ U, signedWeight w g = (poleDegree U g : ℤ) - (zeroDegree U g : ℤ) := by
  simp only [poleDegree, zeroDegree, Nat.cast_sum, ← Finset.sum_sub_distrib,
    Nat.cast_mul, signedWeight, ← mul_sub]
  refine Finset.sum_congr rfl fun w _ => congrArg ((residueDegree w : ℤ) * ·) ?_
  unfold poleOrder zeroOrder
  omega
private theorem integral_chart (h1 : c1) {B : Type} [CommRing B]
    [IsDedekindDomain B] [Algebra F B] [Algebra B K] [IsScalarTower F B K] [IsFractionRing B K]
    (a : B) (ha : a ≠ 0) (hfin : Module.Finite F (B ⧸ Ideal.span {a})) :
    ∃ U : Finset (Place F K),
      (∀ w ∈ U, centered B w) ∧
      (∀ w, centered B w → w.val (algebraMap B K a) ≠ 1 → w ∈ U) ∧
      (∑ w ∈ U, signedWeight w (algebraMap B K a)) =
        -(Module.finrank F (B ⧸ Ideal.span {a}) : ℤ) := by
  obtain ⟨I, hI, hsum⟩ := h1 F B K a ha hfin
  let e : HeightOneSpectrum B ↪ Place F K := ⟨chartPlace, (chartPlace_enumerates F B K).1⟩
  refine ⟨I.map e, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp hw
    intro b
    exact p.valuation_le_one (K := K) b
  · intro w hw hne
    obtain ⟨p, rfl⟩ := (chartPlace_enumerates F B K).2 w hw
    refine Finset.mem_map.mpr ⟨p, (hI p).mpr ?_, rfl⟩
    by_contra hn
    exact hne ((p.valuation_eq_one_iff_notMem (K := K)).mpr hn)
  · have hpole : poleDegree (I.map e) (algebraMap B K a) = 0 := by
      refine Finset.sum_eq_zero fun w hw => ?_
      obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp hw
      have hle := p.valuation_le_one (K := K) a
      have hne := (map_ne_zero (p.valuation K)).mpr
        ((map_ne_zero_iff _ (IsFractionRing.injective B K)).mpr ha)
      have hle' : WithZero.log (p.valuation K (algebraMap B K a)) ≤ 0 :=
        (WithZero.log_le_iff_le_exp hne).mpr (by simpa using hle)
      have hn : poleOrder (e p) (algebraMap B K a) = 0 := Int.toNat_of_nonpos hle'
      simp [hn]
    rw [degree_diff, hpole, Nat.cast_zero, zero_sub]
    congr 1
    unfold zeroDegree
    rw [Finset.sum_map]
    exact_mod_cast hsum.symm
private theorem integralClosure_centered_iff {R : Type} [CommRing R] [Algebra R K]
    (w : Place F K) :
    centered (integralClosure R K) w ↔ ∀ r : R, w.val (algebraMap R K r) ≤ 1 := by
  constructor
  · intro h r
    simpa only [← IsScalarTower.algebraMap_apply R (integralClosure R K) K] using
      h (algebraMap R (integralClosure R K) r)
  · intro h a
    let O := w.val.valuationSubring
    let : Algebra R O := ((algebraMap R K).codRestrict O.toSubring fun r => by
      exact (Valuation.mem_valuationSubring_iff _ _).mpr (h r)).toAlgebra
    let : IsScalarTower R O K := IsScalarTower.of_algebraMap_eq' rfl
    exact (Valuation.valuationSubring.integers w.val).isIntegral_iff_v_le_one.mp
      ((a.2 : IsIntegral R (a : K)).tower_top (A := O))
private theorem chart_degree (h1 : c1) {R L : Type}
    [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Algebra F R]
    [Field L] [Algebra R L] [IsFractionRing R L] [Algebra L K] [Algebra R K]
    [IsScalarTower R L K] [IsScalarTower F R K] [Module.Finite L K] [Algebra.IsSeparable L K]
    (d : L → ℤ) (hd : ∀ x y : L, x ≠ 0 → y ≠ 0 → d (x * y) = d x + d y)
    (hbase : ∀ a : R, a ≠ 0 → Module.Finite F (R ⧸ Ideal.span {a}) ∧
      (Module.finrank F (R ⧸ Ideal.span {a}) : ℤ) = d (algebraMap R L a))
    (g : K) (hg : g ≠ 0) :
    ∃ U : Finset (Place F K),
      (∀ w ∈ U, ∀ r : R, w.val (algebraMap R K r) ≤ 1) ∧
      (∀ w, (∀ r : R, w.val (algebraMap R K r) ≤ 1) → w.val g ≠ 1 → w ∈ U) ∧
      (∑ w ∈ U, signedWeight w g) = -d (Algebra.norm L g) := by
  classical
  let B := integralClosure R K
  let : Algebra F B := ((algebraMap R B).comp (algebraMap F R)).toAlgebra
  let : IsScalarTower F R B := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower F B K := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap F K x = algebraMap B K (algebraMap R B (algebraMap F R x))
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  let : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain R L K B
  let : Module.Finite R B := IsIntegralClosure.finite R L K B
  let : Module.IsTorsionFree R K := .trans_faithfulSMul R L K
  let : Module.Free R B := IsIntegralClosure.module_free R L K B
  let : IsFractionRing B K := IsIntegralClosure.isFractionRing_of_finite_extension R L K B
  let : IsLocalization (Algebra.algebraMapSubmonoid B R⁰) K :=
    IsIntegralClosure.isLocalization R L K B
  have hArg {a : B} (ha : a ≠ 0) :
      ∃ U : Finset (Place F K), (∀ w ∈ U, centered B w) ∧
        (∀ w, centered B w → w.val (algebraMap B K a) ≠ 1 → w ∈ U) ∧
        (∑ w ∈ U, signedWeight w (algebraMap B K a)) =
          -d (Algebra.norm L (algebraMap B K a)) := by
    have ⟨hf, hn⟩ := quotient_norm (fun r : R => d (algebraMap R L r))
      (fun x y hx hy => by
        rw [map_mul]
        exact hd _ _ ((map_ne_zero_iff _ (IsFractionRing.injective R L)).mpr hx)
          ((map_ne_zero_iff _ (IsFractionRing.injective R L)).mpr hy)) hbase a ha
    obtain ⟨U, hU, hsupport, hweight⟩ := integral_chart (F := F) (K := K) h1 a ha hf
    exact ⟨U, hU, hsupport, by
      rw [hweight, hn, Algebra.norm_localization R R⁰ (Rₘ := L) (Sₘ := K)]⟩
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective B g
  have ha : a ≠ 0 := by
    intro hz
    apply hg
    rw [← hab, hz, map_zero, zero_div]
  have hb' : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  obtain ⟨U, hU, hsU, hwU⟩ := hArg ha
  obtain ⟨V, hV, hsV, hwV⟩ := hArg hb'
  have mem_center (w : Place F K) (hw : w ∈ U ∪ V) : centered B w :=
    (Finset.mem_union.mp hw).elim (hU w) (hV w)
  have hx : algebraMap B K a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective B K)).mpr ha
  have hy : algebraMap B K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  refine ⟨U ∪ V, fun w hw => (integralClosure_centered_iff w).mp (mem_center w hw), ?_, ?_⟩
  · intro w hw hne
    have hw' : centered B w := (integralClosure_centered_iff w).mpr hw
    by_contra hout
    rw [← hab, map_div₀,
      not_not.mp (mt (hsU w hw') (fun h => hout (Finset.mem_union_left _ h))),
      not_not.mp (mt (hsV w hw') (fun h => hout (Finset.mem_union_right _ h))), div_one] at hne
    exact hne rfl
  · have enlarge {W : Finset (Place F K)} (hW : W ⊆ U ∪ V) (z : K)
        (hs : ∀ w, centered B w → w.val z ≠ 1 → w ∈ W) :
        (∑ w ∈ W, signedWeight w z) = ∑ w ∈ U ∪ V, signedWeight w z :=
      Finset.sum_subset hW fun w hw hn => by
        have hval : w.val z = 1 := not_not.mp (mt (hs w (mem_center w hw)) hn)
        simp [signedWeight, hval]
    have hdDiv (x y : L) (hx' : x ≠ 0) (hy' : y ≠ 0) : d (x / y) = d x - d y := by
      have h := hd (x / y) y (div_ne_zero hx' hy') hy'
      rw [div_mul_cancel₀ _ hy'] at h
      omega
    have hnorm : Algebra.norm L (algebraMap B K a / algebraMap B K b) =
        Algebra.norm L (algebraMap B K a) / Algebra.norm L (algebraMap B K b) := by
      simp only [div_eq_mul_inv, map_mul, Algebra.norm_inv]
    rw [← hab, hnorm, hdDiv _ _ (Algebra.norm_ne_zero_iff.mpr hx)
      (Algebra.norm_ne_zero_iff.mpr hy)]
    simp_rw [signedWeight_div _ hx hy, Finset.sum_sub_distrib]
    rw [← enlarge Finset.subset_union_left _ hsU, ← enlarge Finset.subset_union_right _ hsV,
      hwU, hwV]
    omega
end Chart
private theorem polynomial_colength {F : Type} [Field F] (a : F[X]) (ha : a ≠ 0) :
    Module.Finite F (F[X] ⧸ Ideal.span {a}) ∧
    (Module.finrank F (F[X] ⧸ Ideal.span {a}) : ℤ) = (algebraMap F[X] (RatFunc F) a).intDegree := by
  exact ⟨(AdjoinRoot.powerBasis ha).finite, by
    rw [RatFunc.intDegree_polynomial]
    exact_mod_cast (AdjoinRoot.powerBasis ha).finrank⟩
theorem infinity_dvr (F : Type) [Field F] : IsDiscreteValuationRing (InfinityRing F) := by
  classical
  let : IsCyclic (ℤᵐ⁰)ˣ :=
    isCyclic_of_surjective WithZero.unitsWithZeroEquiv.symm
      WithZero.unitsWithZeroEquiv.symm.surjective
  change IsDiscreteValuationRing (RatFunc.inftyValuation F).valuationSubring
  infer_instance
section RationalLine
variable {F K : Type} [Field F] [Field K] [Algebra F K]
local notation "Lrat" => RatFunc F
local notation "Aline" => Polynomial F
local notation "Oinf" => InfinityRing F
set_option maxHeartbeats 1500000 in
private theorem rational_balance (h1 : c1) (h2 : c2)
    [Algebra Lrat K] [IsScalarTower F Lrat K] [Module.Finite Lrat K] [Algebra.IsSeparable Lrat K]
    (g : K) (hg : g ≠ 0) (S : Finset (Place F K)) :
    ∃ T : Finset (Place F K), zeroDegree S g ≤ poleDegree T g := by
  classical
  let baseAlgebra : Algebra Oinf Lrat := inferInstance
  let : Algebra Oinf Lrat := baseAlgebra
  let : SMul Oinf Lrat := baseAlgebra.toSMul
  let : IsScalarTower F Oinf Lrat := infinityTower F
  let : IsDiscreteValuationRing Oinf := infinity_dvr F
  let : Algebra Aline K := ((algebraMap Lrat K).comp (algebraMap Aline Lrat)).toAlgebra
  let : IsScalarTower Aline Lrat K := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower F Aline K := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap F K x = algebraMap Lrat K (algebraMap Aline Lrat (algebraMap F Aline x))
    rw [← IsScalarTower.algebraMap_apply F Aline Lrat, ← IsScalarTower.algebraMap_apply F Lrat K]
  let : Algebra Oinf K := ((algebraMap Lrat K).comp (algebraMap Oinf Lrat)).toAlgebra
  let : IsScalarTower Oinf Lrat K := IsScalarTower.of_algebraMap_eq' (R := Oinf) (S := Lrat) (A := K) rfl
  let : IsScalarTower F Oinf K := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap F K x = algebraMap Lrat K (algebraMap Oinf Lrat (algebraMap F Oinf x))
    rw [← IsScalarTower.algebraMap_apply F Oinf Lrat, ← IsScalarTower.algebraMap_apply F Lrat K]
  obtain ⟨U, hU, hsU, hwU⟩ :=
    chart_degree h1 (R := Aline) (L := Lrat) RatFunc.intDegree
      (fun _ _ hx hy => RatFunc.intDegree_mul hx hy) polynomial_colength g hg
  obtain ⟨V, hV, hsV, hwV⟩ :=
    chart_degree h1 (R := Oinf) (L := Lrat) (fun x => -x.intDegree)
      (fun _ _ hx hy => by rw [RatFunc.intDegree_mul hx hy, neg_add]) (h2 F) g hg
  let restrict (w : Place F K) : Valuation Lrat ℤᵐ⁰ := w.val.comap (algebraMap Lrat K)
  let (w : Place F K) : (restrict w).IsTrivialOn F := ⟨fun c hc => by
    change w.val (algebraMap Lrat K (algebraMap F Lrat c)) = 1
    rw [← IsScalarTower.algebraMap_apply F Lrat K]
    exact w.trivial c hc⟩
  have hnontrivial (w : Place F K) : (restrict w).IsNontrivial := by
    by_contra h
    let : w.val.IsTrivialOn Lrat := ⟨fun a ha => by
      change restrict w a = 1
      by_contra hv
      exact h ⟨a, (map_ne_zero (restrict w)).mpr ha, hv⟩⟩
    obtain ⟨b, hb⟩ := w.surj (WithZero.exp 1)
    have hb0 : b ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hb
      exact WithZero.exp_ne_zero hb.symm
    have hb1 : w.val b ≠ 1 := by
      rw [hb, ← WithZero.exp_zero, ne_eq, WithZero.exp_inj]
      decide
    exact (w.val.transcendental_of_ne_one Lrat b hb0 hb1)
      (Algebra.IsAlgebraic.isAlgebraic b)
  have hdisj : Disjoint U V := by
    refine Finset.disjoint_left.mpr fun w hu hv => ?_
    have hleO : (RatFunc.inftyValuation F).valuationSubring ≤ (restrict w).valuationSubring := by
      intro a ha
      exact (Valuation.mem_valuationSubring_iff (restrict w) a).mpr (hV w hv ⟨a, ha⟩)
    have hEq := ValuationSubring.eq_of_le_of_ne_top _ hleO
      (fun h => ((Valuation.valuationSubring_eq_top_iff (restrict w)).mp h) (hnontrivial w))
    have hle := hU w hu Polynomial.X
    change restrict w (RatFunc.X : Lrat) ≤ 1 at hle
    have hm : RatFunc.X ∈ (restrict w).valuationSubring :=
      (Valuation.mem_valuationSubring_iff _ _).mpr hle
    rw [← hEq] at hm
    have hh := (Valuation.mem_valuationSubring_iff _ _).mp hm
    rw [RatFunc.inftyValuation.X, ← WithZero.exp_zero, WithZero.exp_le_exp] at hh
    omega
  have hcover (w : Place F K) (hw : w.val g ≠ 1) : w ∈ U ∪ V := by
    rcases le_or_gt (restrict w RatFunc.X) 1 with hle | hlt
    · refine Finset.mem_union_left _ (hsU w ?_ hw)
      intro a
      exact Polynomial.valuation_le_one_of_valuation_X_le_one F hle a
    · refine Finset.mem_union_right _ (hsV w ?_ hw)
      intro a
      have h := RatFunc.valuation_isEquiv_inftyValuation_of_one_lt_valuation_X hlt
      exact h.le_one_iff_le_one.mpr a.2
  have hsum : (∑ w ∈ U ∪ V, signedWeight w g) = 0 := by
    rw [Finset.sum_union hdisj, hwU, hwV]
    omega
  rw [degree_diff] at hsum
  have hpart : zeroDegree S g ≤ zeroDegree (U ∪ V) g := by
    unfold zeroDegree
    calc
      _ = ∑ w ∈ S ∩ (U ∪ V), residueDegree w * zeroOrder w g := by
        symm
        apply Finset.sum_subset Finset.inter_subset_left
        intro w hw hn
        have hval : w.val g = 1 := by
          by_contra hv
          exact hn (Finset.mem_inter.mpr ⟨hw, hcover w hv⟩)
        simp [zeroOrder, hval]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun _ _ _ => Nat.zero_le _)
  exact ⟨U ∪ V, hpart.trans (by omega)⟩
end RationalLine
theorem of_children (h1 : c1) (h2 : c2) : K1_14_2_2_7_4_4.c7 := by
  intro F K _ _ _ hsep g hg S
  obtain ⟨t, ht, htFin, htSep⟩ := hsep
  let E := IntermediateField.adjoin F {t}
  let L := RatFunc F
  let e : L ≃ₐ[F] E := RatFunc.algEquivOfTranscendental t ht
  let f : L →ₐ[F] K := E.val.comp e.toAlgHom
  let : Algebra L K := f.toRingHom.toAlgebra
  let : IsScalarTower F L K := IsScalarTower.of_algHom f
  have hmaps : (algebraMap L K).comp e.symm.toRingHom = (RingEquiv.refl K).toRingHom.comp
      (algebraMap E K) := by
    ext x
    change (e (e.symm x) : K) = (x : K)
    rw [e.apply_symm_apply]
  let : Module.Finite E K := htFin
  let : Algebra.IsSeparable E K := htSep
  let : Module.Finite L K := Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl K) hmaps
  let : Algebra.IsSeparable L K :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl K) hmaps
  exact rational_balance h1 h2 g hg S
end
end K1_14_2_2_7_4_4_7
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace K1_14_2_2_7_4_1
noncomputable section
open K1_14 K1_14_2 K1_14_2_2_7_4
open scoped Polynomial
private abbrev WithSlope (I : Ideal Ambient) := (CoordinateRing I)[X]
local instance (I : Ideal Ambient) : CommRing (WithSlope I) :=
  @Polynomial.commRing (CoordinateRing I) (Ideal.Quotient.commRing I)
private def parameterMap (I : Ideal Ambient) : Seeds →+* WithSlope I :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap FX (CoordinateRing I)))
    ![Polynomial.X, Polynomial.C (ambientCoord I 2) +
      Polynomial.X * Polynomial.C (ambientCoord I 3)]
private theorem parameter_slope (I : Ideal Ambient) :
    parameterMap I (MvPolynomial.X 0) = Polynomial.X :=
  MvPolynomial.eval₂Hom_X' _ _ _
private theorem parameter_intercept (I : Ideal Ambient) :
    parameterMap I (MvPolynomial.X 1) = Polynomial.C (ambientCoord I 2) +
      Polynomial.X * Polynomial.C (ambientCoord I 3) :=
  MvPolynomial.eval₂Hom_X' _ _ _
private theorem parameter_injective (I : Ideal Ambient)
    (hvar : ¬ IsAlgebraic FX (ambientCoord I 2) ∨ ¬ IsAlgebraic FX (ambientCoord I 3)) :
    Function.Injective (parameterMap I) := by
  let : Infinite FX := Infinite.of_injective _ (IsFractionRing.injective L[X] FX)
  exact parameter_injective_of_varying (k := FX) (A := CoordinateRing I)
    (ambientCoord I 2) (ambientCoord I 3) hvar
private def toSlice (I : Ideal Ambient) : CoordinateRing I →+* JetSlice I :=
  Ideal.quotientMap (jetSliceIdeal I) jetSliceMap (Ideal.le_comap_map)
private def slopeToSlice (I : Ideal Ambient) : WithSlope I →+* JetSlice I :=
  Polynomial.eval₂RingHom (toSlice I) (algebraMap SeedField (JetSlice I) (generic 0))
private theorem sliceLine (I : Ideal Ambient) :
    toSlice I (ambientCoord I 2) + algebraMap SeedField (JetSlice I) (generic 0) *
      toSlice I (ambientCoord I 3) = algebraMap SeedField (JetSlice I) (generic 1) := by
  let m := Ideal.Quotient.mk (jetSliceIdeal I)
  change m (jetSliceMap (MvPolynomial.X 2)) + m (MvPolynomial.C (generic 0)) *
    m (jetSliceMap (MvPolynomial.X 3)) = m (MvPolynomial.C (generic 1))
  rw [← map_mul, ← map_add]
  congr 1
  simp [jetSliceMap]
private theorem parameter_commutes (I : Ideal Ambient) :
    (slopeToSlice I).comp (parameterMap I) =
      (algebraMap SeedField (JetSlice I)).comp (algebraMap Seeds SeedField) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [parameterMap, slopeToSlice, RingHom.comp_apply, toSlice, jetSliceMap]
    rfl
  · intro k
    fin_cases k
    · change slopeToSlice I (parameterMap I (MvPolynomial.X 0)) =
        algebraMap SeedField (JetSlice I) (generic 0)
      rw [parameter_slope, slopeToSlice, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    · change slopeToSlice I (parameterMap I (MvPolynomial.X 1)) =
        algebraMap SeedField (JetSlice I) (generic 1)
      rw [parameter_intercept]
      simp only [map_add, map_mul, slopeToSlice, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C, Polynomial.eval₂_X]
      exact sliceLine I
private abbrev SlopeField (I : Ideal Ambient) := FractionRing (WithSlope I)
private def coefficientToFrac (I : Ideal Ambient) [I.IsPrime]
    (hinj : Function.Injective (parameterMap I)) : SeedField →+* SlopeField I :=
  IsFractionRing.lift (K := SeedField)
    (g := (algebraMap (WithSlope I) (SlopeField I)).comp (parameterMap I))
    ((IsFractionRing.injective (WithSlope I) (SlopeField I)).comp hinj)
private theorem coefficientToFrac_base (I : Ideal Ambient) [I.IsPrime]
    (hinj : Function.Injective (parameterMap I)) (r : Seeds) :
    coefficientToFrac I hinj (algebraMap Seeds SeedField r) =
      algebraMap (WithSlope I) (SlopeField I) (parameterMap I r) :=
  IsFractionRing.lift_algebraMap _ r
private def remainingCoord (i : Option (Fin 2)) : Fin 4 :=
  i.elim 3 (Fin.castAdd 2)
private def polyToFrac (I : Ideal Ambient) [I.IsPrime] (hinj : Function.Injective (parameterMap I)) :
    CurvePoly SeedField →+* SlopeField I :=
  MvPolynomial.eval₂Hom (coefficientToFrac I hinj) (fun i =>
    algebraMap (WithSlope I) (SlopeField I) (Polynomial.C (ambientCoord I (remainingCoord i))))
private theorem map_elimination {A B : Type} [CommRing A] [CommRing B]
    (f : A →+* B) (y v t : A) : f (y + t * v) - f t * f v = f y := by
  rw [← f.map_mul, ← f.map_sub, add_sub_cancel_right]
private theorem originalToFrac (I : Ideal Ambient) [I.IsPrime]
    (hinj : Function.Injective (parameterMap I)) :
    (polyToFrac I hinj).comp jetSliceMap =
      ((algebraMap (WithSlope I) (SlopeField I)).comp Polynomial.C).comp (Ideal.Quotient.mk I) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, jetSliceMap, polyToFrac, MvPolynomial.eval₂Hom_C]
    change coefficientToFrac I hinj (algebraMap Seeds SeedField (MvPolynomial.C a)) = _
    rw [← MvPolynomial.algebraMap_eq FX (Fin 4), Ideal.Quotient.mk_algebraMap]
    simpa only [parameterMap, MvPolynomial.eval₂Hom_C, RingHom.comp_apply] using
      coefficientToFrac_base I hinj (MvPolynomial.C a)
  · intro i
    let f := polyToFrac I hinj
    let m := algebraMap (WithSlope I) (SlopeField I)
    have hX (j : Option (Fin 2)) :
        f (MvPolynomial.X j) = m (Polynomial.C (ambientCoord I (remainingCoord j))) :=
      MvPolynomial.eval₂Hom_X' _ _ _
    have hC (j : Fin 2) : f (MvPolynomial.C (generic j)) = m (parameterMap I (MvPolynomial.X j)) :=
      (MvPolynomial.eval₂Hom_C _ _ _).trans (coefficientToFrac_base I hinj _)
    change f (jetSliceMap (MvPolynomial.X i)) = m (Polynomial.C (ambientCoord I i))
    rw [jetSliceMap, MvPolynomial.eval₂Hom_X']
    fin_cases i
    · exact hX (some 0)
    · exact hX (some 1)
    · change f (MvPolynomial.C (generic 1) -
          MvPolynomial.C (generic 0) * MvPolynomial.X none) = _
      rw [f.map_sub, f.map_mul, hC 0, hC 1, hX none, parameter_slope, parameter_intercept]
      exact map_elimination (A := WithSlope I) (B := SlopeField I) m
        (Polynomial.C (ambientCoord I 2)) (Polynomial.C (ambientCoord I 3)) Polynomial.X
    · exact hX none
private def sliceToFrac (I : Ideal Ambient) [I.IsPrime] (hinj : Function.Injective (parameterMap I)) :
    JetSlice I →+* SlopeField I :=
  Ideal.Quotient.lift (jetSliceIdeal I) (polyToFrac I hinj) <| by
    change I.map jetSliceMap ≤ RingHom.ker (polyToFrac I hinj)
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change ((polyToFrac I hinj).comp jetSliceMap) a = 0
    rw [originalToFrac]
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
private theorem sliceToFrac_slope (I : Ideal Ambient) [I.IsPrime]
    (hinj : Function.Injective (parameterMap I)) :
    (sliceToFrac I hinj).comp (slopeToSlice I) = algebraMap (WithSlope I) (SlopeField I) := by
  apply Polynomial.ringHom_ext
  · intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    simpa [sliceToFrac, slopeToSlice, toSlice, RingHom.comp_apply] using
      RingHom.congr_fun (originalToFrac I hinj) a
  · simp only [RingHom.comp_apply, slopeToSlice, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    change sliceToFrac I hinj (Ideal.Quotient.mk (jetSliceIdeal I)
        (MvPolynomial.C (generic 0))) = _
    rw [sliceToFrac, Ideal.Quotient.lift_mk, polyToFrac, MvPolynomial.eval₂Hom_C, generic,
      coefficientToFrac_base, parameter_slope]
private theorem slope_injective (I : Ideal Ambient) [I.IsPrime]
    (hinj : Function.Injective (parameterMap I)) : Function.Injective (slopeToSlice I) := by
  have hf : Function.Injective ((sliceToFrac I hinj).comp (slopeToSlice I)) := by
    rw [sliceToFrac_slope]
    exact IsFractionRing.injective _ _
  exact Function.Injective.of_comp hf
private theorem clear_denominator (I : Ideal Ambient) (x : JetSlice I) :
    ∃ (q : WithSlope I) (r : Seeds), r ≠ 0 ∧
      x * algebraMap SeedField (JetSlice I) (algebraMap Seeds SeedField r) = slopeToSlice I q := by
  let : Algebra (MvPolynomial (Option (Fin 2)) Seeds) (CurvePoly SeedField) :=
    MvPolynomial.algebraMvPolynomial
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨⟨g, m⟩, hgm⟩ := IsLocalization.surj
    (M := (nonZeroDivisors Seeds).map (MvPolynomial.C (σ := Option (Fin 2)))) f
  obtain ⟨r, hr, hrm⟩ := m.property
  let lift : MvPolynomial (Option (Fin 2)) Seeds →+* WithSlope I := MvPolynomial.eval₂Hom (parameterMap I)
    (fun i => Polynomial.C (ambientCoord I (remainingCoord i)))
  have hcomp : (slopeToSlice I).comp lift = (Ideal.Quotient.mk (jetSliceIdeal I)).comp
      (MvPolynomial.map (algebraMap Seeds SeedField)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, lift, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C]
      rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
      exact RingHom.congr_fun (parameter_commutes I) a
    · intro i
      cases i with
      | none => simp [lift, slopeToSlice, toSlice, ambientCoord, jetSliceMap, RingHom.comp_apply, remainingCoord]
      | some i =>
        fin_cases i <;>
          simp [lift, slopeToSlice, toSlice, ambientCoord, jetSliceMap, RingHom.comp_apply, remainingCoord]
  refine ⟨lift g, r, mem_nonZeroDivisors_iff_ne_zero.mp hr, ?_⟩
  have hgm' : f * MvPolynomial.C (algebraMap Seeds SeedField r) =
      MvPolynomial.map (algebraMap Seeds SeedField) g := by
    simpa only [MvPolynomial.algebraMap_def, ← hrm, MvPolynomial.map_C] using hgm
  calc
    _ = Ideal.Quotient.mk (jetSliceIdeal I) (f * MvPolynomial.C (algebraMap Seeds SeedField r)) :=
      (map_mul _ _ _).symm
    _ = _ := (congrArg (Ideal.Quotient.mk (jetSliceIdeal I)) hgm').trans
      (RingHom.congr_fun hcomp g).symm
private theorem slice_contraction (I : Ideal Ambient) [I.IsPrime]
    (hinj : Function.Injective (parameterMap I)) : (jetSliceIdeal I).comap jetSliceMap = I := by
  refine le_antisymm ?_ Ideal.le_comap_map
  intro a ha
  have hz : toSlice I (Ideal.Quotient.mk I a) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr ha
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply Polynomial.C_injective
  apply slope_injective I hinj
  simpa only [slopeToSlice, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, map_zero] using hz
private theorem slice_isLocalization (I : Ideal Ambient) [I.IsPrime]
    (hinj : Function.Injective (parameterMap I)) :
    let : Algebra (WithSlope I) (JetSlice I) := (slopeToSlice I).toAlgebra
    IsLocalization ((nonZeroDivisors Seeds).map (parameterMap I)) (JetSlice I) := by
  let : Algebra (WithSlope I) (JetSlice I) := (slopeToSlice I).toAlgebra
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · rintro ⟨_, r, hr, rfl⟩
    change IsUnit ((slopeToSlice I).comp (parameterMap I) r)
    rw [parameter_commutes]
    apply IsUnit.map (algebraMap SeedField (JetSlice I))
    apply isUnit_iff_ne_zero.mpr
    simpa only [map_zero] using
      (IsFractionRing.injective Seeds SeedField).ne (mem_nonZeroDivisors_iff_ne_zero.mp hr)
  · intro x
    obtain ⟨q, r, hr, hx⟩ := clear_denominator I x
    refine ⟨⟨q, ⟨parameterMap I r, ⟨r, mem_nonZeroDivisors_iff_ne_zero.mpr hr, rfl⟩⟩⟩, ?_⟩
    change x * ((slopeToSlice I).comp (parameterMap I)) r = slopeToSlice I q
    rwa [parameter_commutes]
  · intro x y h
    exact ⟨1, by rw [slope_injective I hinj h]⟩
private def slopeAlgHom (I : Ideal Ambient) : WithSlope I →ₐ[FX] JetSlice I :=
  ⟨slopeToSlice I, fun a => by
    change slopeToSlice I (Polynomial.C (algebraMap FX (CoordinateRing I) a)) = _
    have h := RingHom.congr_fun (parameter_commutes I) (MvPolynomial.C a)
    simp only [RingHom.comp_apply, parameterMap, MvPolynomial.eval₂Hom_C] at h
    exact h⟩
private theorem slice_dimension (I : Ideal Ambient) [I.IsPrime] [IsDomain (JetSlice I)]
    (d : ℕ) (hdim : ringKrullDim (CoordinateRing I) = ((d + 1 : ℕ) : WithBot ℕ∞))
    (hinj : Function.Injective (parameterMap I)) :
    ringKrullDim (JetSlice I) = (d : WithBot ℕ∞) := by
  let : Algebra (WithSlope I) (JetSlice I) := (slopeToSlice I).toAlgebra
  have := slice_isLocalization I hinj
  have hAlg : Algebra.IsAlgebraic (WithSlope I) (JetSlice I) :=
    IsLocalization.isAlgebraic _ ((nonZeroDivisors Seeds).map (parameterMap I))
  exact affine_slice_dimension (k := FX) (E := SeedField) (A := CoordinateRing I)
    (B := JetSlice I) (slopeAlgHom I) (slope_injective I hinj) hAlg (parameter_field_trdeg FX) d hdim
theorem proof : K1_14_2_2_7_4.c1 := by
  intro I d hprime hdim hvar
  let : I.IsPrime := hprime
  have hinj := parameter_injective I hvar
  let : Algebra (WithSlope I) (JetSlice I) := (slopeToSlice I).toAlgebra
  have := slice_isLocalization I hinj
  have hM : (nonZeroDivisors Seeds).map (parameterMap I) ≤ nonZeroDivisors (WithSlope I) := by
    rintro _ ⟨r, hr, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr
      (fun h => (mem_nonZeroDivisors_iff_ne_zero.mp hr) (hinj (h.trans (map_zero _).symm)))
  have : IsDomain (JetSlice I) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  exact ⟨(Ideal.Quotient.isDomain_iff_prime _).mp inferInstance,
    slice_dimension I d hdim hinj, slice_contraction I hinj⟩
end
end K1_14_2_2_7_4_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace K1_14_2_2_7_4_2
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_7_4 MvPolynomial
open scoped nonZeroDivisors
private abbrev FlatParameters (k : Type) [Field k] := MvPolynomial (Fin 4) k
private abbrev JetParameters (k : Type) [Field k] := MvPolynomial (Fin 2) k
private abbrev NestedParameters (k : Type) [Field k] := MvPolynomial (Fin 2) (JetParameters k)
private abbrev SeedParameters (k : Type) [Field k] := MvPolynomial (Fin 2) (LineField k)
attribute [local instance] MvPolynomial.algebraMvPolynomial
local instance iteratedFraction (k : Type) [Field k] :
    IsFractionRing (NestedParameters k) (LineField (LineField k)) := by
  let M : Submonoid (NestedParameters k) := (nonZeroDivisors (JetParameters k)).map C
  have : IsLocalization M (SeedParameters k) :=
    MvPolynomial.isLocalization (nonZeroDivisors (JetParameters k)) (LineField k)
  have hcomap : (nonZeroDivisors (SeedParameters k)).comap
      (algebraMap (NestedParameters k) (SeedParameters k)) = nonZeroDivisors (NestedParameters k) := by
    have hinj : Function.Injective (algebraMap (NestedParameters k) (SeedParameters k)) :=
      MvPolynomial.map_injective _ (IsFractionRing.injective (JetParameters k) (LineField k))
    ext z
    simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero, map_ne_zero_iff _ hinj]
  change IsLocalization (nonZeroDivisors (NestedParameters k)) (LineField (LineField k))
  rw [← hcomap]
  exact IsLocalization.localization_localization_isLocalization_of_has_all_units M
    (nonZeroDivisors (SeedParameters k)) (LineField (LineField k)) (fun _ hu => hu.mem_nonZeroDivisors)
private def parameterIndex : Fin 4 ≃ Fin 2 ⊕ Fin 2 where
  toFun := ![Sum.inl 0, Sum.inr 0, Sum.inl 1, Sum.inr 1]
  invFun := Sum.elim ![0, 2] ![1, 3]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    rintro (i | i) <;> fin_cases i <;> rfl
private def polynomialEquiv (k : Type) [Field k] : FlatParameters k ≃+* NestedParameters k :=
  ((renameEquiv k parameterIndex).trans (sumAlgEquiv k (Fin 2) (Fin 2))).toRingEquiv
private def iteratedEquiv (k : Type) [Field k] :
    FractionRing (FlatParameters k) ≃+* LineField (LineField k) :=
  IsFractionRing.ringEquivOfRingEquiv (polynomialEquiv k)
private theorem iteratedEquiv_base (k : Type) [Field k] (x : FlatParameters k) :
    iteratedEquiv k (algebraMap (FlatParameters k) (FractionRing (FlatParameters k)) x) =
      algebraMap (SeedParameters k) (LineField (LineField k))
        (algebraMap (NestedParameters k) (SeedParameters k) (polynomialEquiv k x)) := by
  rw [← IsScalarTower.algebraMap_apply]
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap (polynomialEquiv k) x
private abbrev IteratedField := LineField SeedField
private abbrev coefficientEquiv := iteratedEquiv FX
private theorem coefficientEquiv_C (a : FX) :
    coefficientEquiv (algebraMap FX SectionField a) =
      algebraMap SeedField IteratedField (algebraMap FX SeedField a) := by
  change coefficientEquiv (algebraMap (FlatParameters FX) SectionField (C a)) = _
  rw [iteratedEquiv_base]
  change algebraMap (SeedParameters FX) IteratedField
    (algebraMap (NestedParameters FX) (SeedParameters FX) (sumAlgEquiv FX _ _ (rename parameterIndex (C a)))) = _
  rw [rename_C, sumAlgEquiv_C_inl, MvPolynomial.algebraMap_def, map_C]
  rfl
private theorem coefficientEquiv_seed (i : Fin 2) :
    coefficientEquiv (sliceParameter (![0, 2] i)) = lineParameter SeedField i := by
  have hi : parameterIndex (![0, 2] i) = Sum.inl i := by fin_cases i <;> rfl
  unfold sliceParameter lineParameter
  rw [iteratedEquiv_base]
  change algebraMap (SeedParameters FX) IteratedField (algebraMap (NestedParameters FX) (SeedParameters FX)
    (sumAlgEquiv FX _ _ (rename parameterIndex (MvPolynomial.X (![0, 2] i))))) = _
  rw [rename_X, hi, sumAlgEquiv_X_inl, MvPolynomial.algebraMap_def, map_X]
private theorem coefficientEquiv_jet (i : Fin 2) :
    coefficientEquiv (sliceParameter (![1, 3] i)) =
      algebraMap SeedField IteratedField (generic i) := by
  have hi : parameterIndex (![1, 3] i) = Sum.inr i := by fin_cases i <;> rfl
  unfold sliceParameter generic
  rw [iteratedEquiv_base]
  change algebraMap (SeedParameters FX) IteratedField (algebraMap (NestedParameters FX) (SeedParameters FX)
    (sumAlgEquiv FX _ _ (rename parameterIndex (MvPolynomial.X (![1, 3] i))))) = _
  rw [rename_X, hi, sumAlgEquiv_X_inr, MvPolynomial.algebraMap_def, map_C]
  rfl
private def extendCoefficients : CurvePoly SeedField →+* CurvePoly IteratedField :=
  MvPolynomial.map (algebraMap SeedField IteratedField)
private def substituteJet : SectionAmbient →+* CurvePoly IteratedField :=
  eval₂Hom (C.comp coefficientEquiv.toRingHom)
    ![MvPolynomial.X (some 0), MvPolynomial.X (some 1),
      C (coefficientEquiv (sliceParameter 3)) - C (coefficientEquiv (sliceParameter 1)) * MvPolynomial.X none,
      MvPolynomial.X none]
private theorem substituteJet_surjective : Function.Surjective substituteJet := by
  let includeFree : CurvePoly IteratedField →+* SectionAmbient :=
    eval₂Hom (C.comp coefficientEquiv.symm.toRingHom)
      (fun i => i.elim (MvPolynomial.X 3) (fun j => MvPolynomial.X (![0, 1] j)))
  have h : substituteJet.comp includeFree = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [includeFree, substituteJet]
    · rintro (_ | i)
      · simp [includeFree, substituteJet]
      · fin_cases i <;> simp [includeFree, substituteJet]
  intro p
  exact ⟨includeFree p, DFunLike.congr_fun h p⟩
private theorem substituteJet_comp :
    substituteJet.comp sectionBase = extendCoefficients.comp jetSliceMap := by
  have h1 := coefficientEquiv_jet 0
  have h3 := coefficientEquiv_jet 1
  change coefficientEquiv (sliceParameter 1) = _ at h1
  change coefficientEquiv (sliceParameter 3) = _ at h3
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [substituteJet, sectionBase, extendCoefficients, jetSliceMap, coefficientEquiv_C]
  · intro i
    fin_cases i <;> simp [substituteJet, sectionBase, extendCoefficients, jetSliceMap, h1, h3]
private theorem substituteJet_ideal (I : Ideal Ambient) :
    (I.map sectionBase ⊔ Ideal.span {sectionSeedLine, sectionJetLine}).map substituteJet =
      seedFibreIdeal (jetSliceIdeal I) := by
  have h0 := coefficientEquiv_seed 0
  have h2 := coefficientEquiv_seed 1
  change coefficientEquiv (sliceParameter 0) = _ at h0
  change coefficientEquiv (sliceParameter 2) = _ at h2
  have hseed : substituteJet sectionSeedLine =
      MvPolynomial.X (some 0) + C (lineParameter SeedField 0) * MvPolynomial.X (some 1) - C (lineParameter SeedField 1) := by
    simp [sectionSeedLine, substituteJet, h0, h2]
  have hjet : substituteJet sectionJetLine = 0 := by
    simp [sectionJetLine, substituteJet]
  simp [seedFibreIdeal, jetSliceIdeal, ← show extendCoefficients =
    MvPolynomial.map (algebraMap SeedField IteratedField) from rfl,
    Ideal.span_insert, Ideal.map_sup, Ideal.map_span, Set.image_singleton,
    Ideal.map_map, substituteJet_comp, hseed, hjet]
private theorem finite_rank_of_surjective {F G M N : Type} [Field F] [Field G]
    [AddCommGroup M] [AddCommGroup N] [Module F M] [Module G N] [Module.Finite F M]
    {σ : F →+* G} (l : M →ₛₗ[σ] N) (hl : Function.Surjective l) :
    Module.Finite G N ∧ Module.finrank G N ≤ Module.finrank F M := by
  refine ⟨Module.Finite.of_surjective l hl, ?_⟩
  let b := Module.finBasis F M
  have hspan : Submodule.span G (Set.range (l ∘ b)) = ⊤ := by
    apply eq_top_iff.mpr
    intro y _
    obtain ⟨x, rfl⟩ := hl y
    rw [Set.range_comp]
    exact Submodule.image_span_subset_span l _ ⟨x, by rw [b.span_eq]; trivial, rfl⟩
  simpa using finrank_le_of_span_eq_top hspan
theorem proof : K1_14_2_2_7_4.c2 := by
  intro I hfinite
  let _ := hfinite
  let J := I.map sectionBase ⊔ Ideal.span {sectionSeedLine, sectionJetLine}
  let J' := seedFibreIdeal (jetSliceIdeal I)
  have h : J ≤ J'.comap substituteJet :=
    Ideal.map_le_iff_le_comap.mp (substituteJet_ideal I).le
  let q : OverMixed I →+* SeedFibre (jetSliceIdeal I) := Ideal.quotientMap J' substituteJet h
  let l : OverMixed I →ₛₗ[coefficientEquiv.toRingHom] SeedFibre (jetSliceIdeal I) :=
    { q.toAddMonoidHom with
      map_smul' := by
        intro a x
        change q (a • x) = coefficientEquiv a • q x
        rw [Algebra.smul_def a x, Algebra.smul_def (coefficientEquiv a) (q x), map_mul]
        congr 1
        change Ideal.quotientMap J' substituteJet h (Ideal.Quotient.mk J (C a)) =
          Ideal.Quotient.mk J' (C (coefficientEquiv a))
        rw [Ideal.quotientMap_mk]
        simp [substituteJet] }
  have hl : Function.Surjective l := Ideal.quotientMap_surjective (H := h) substituteJet_surjective
  exact finite_rank_of_surjective l hl
end
end K1_14_2_2_7_4_2
end
section
set_option autoImplicit false
namespace K1_14_2_2_7_4_4_1
noncomputable section
open K1_14_2 K1_14_2_2_7_4 K1_14_2_2_7_4_4
open Polynomial
open scoped TensorProduct nonZeroDivisors
variable {k A : Type} [Field k] [CommRing A] [Algebra k A]
abbrev polynomialFractionMap (A : Type) [CommRing A] : A[X] →+* FractionRing (A[X]) :=
  algebraMap _ _
private theorem tensor_embedding [IsDomain A] :
    ∃ g : (A ⊗[k] SlopeField k) →+* FractionRing (A[X]),
      Function.Injective g ∧
      (∀ a : A, g (a ⊗ₜ[k] 1) = polynomialFractionMap A (C a)) ∧
      (∀ p : k[X], g (1 ⊗ₜ[k] algebraMap k[X] (SlopeField k) p) =
        polynomialFractionMap A (p.map (algebraMap k A))) := by
  let P := k[X]
  let M := nonZeroDivisors P
  let R := A ⊗[k] P
  let ι : P →ₐ[k] R := Algebra.TensorProduct.includeRight
  let S := Localization (M.map ι)
  let e : A[X] ≃ₐ[A] R := polyEquivTensor' k A
  let E := IsLocalization.tensorProductEquivOfMapIncludeRight k A M (SlopeField k) S
  let j := (polynomialFractionMap A).comp e.symm.toRingHom
  have hj : Function.Injective j := (IsFractionRing.injective _ _).comp e.symm.injective
  have he (a : A) (p : P) : j (a ⊗ₜ[k] p) =
      polynomialFractionMap A (C a * p.map (algebraMap k A)) := by
    change polynomialFractionMap A ((polyEquivTensor k A).symm (a ⊗ₜ[k] p)) = _
    rw [polyEquivTensor_symm_apply_tmul_eq_smul, Algebra.smul_def]
    rfl
  have hu : ∀ p : M.map ι, IsUnit (j p) := by
    rintro ⟨_, p, hp, rfl⟩
    change IsUnit (j (1 ⊗ₜ[k] p))
    rw [he, map_one, one_mul]
    apply isUnit_iff_ne_zero.mpr
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      ((Polynomial.map_ne_zero_iff (algebraMap k A).injective).mpr (nonZeroDivisors.ne_zero hp))
  let g : S →+* FractionRing (A[X]) := IsLocalization.lift hu
  have hg (r : R) : g (algebraMap R S r) = j r := IsLocalization.lift_eq _ _
  have hg_inj : Function.Injective g :=
    (IsLocalization.lift_injective_iff (S := S) (hg := hu)).mpr
      (fun x y => ⟨fun h => by rw [← hg, ← hg]; exact congrArg g h,
        fun h => congrArg (algebraMap R S) (hj h)⟩)
  refine ⟨g.comp E.toRingHom, hg_inj.comp E.injective, ?_, ?_⟩
  · intro a
    change g (E (a ⊗ₜ[k] (1 : SlopeField k))) = _
    rw [← map_one (algebraMap P (SlopeField k)),
      IsLocalization.tensorProductEquivOfMapIncludeRight_tmul, hg, he,
      Polynomial.map_one, mul_one]
  · intro p
    change g (E ((1 : A) ⊗ₜ[k] algebraMap P (SlopeField k) p)) = _
    rw [IsLocalization.tensorProductEquivOfMapIncludeRight_tmul, hg, he, map_one, one_mul]
theorem slope_embedding (D : Ideal (CurvePoly k)) [D.IsPrime] :
    let A := CoordinateRing D
    let L := FractionRing (A[X])
    ∃ g : SlopedCurve D →+* L,
      Function.Injective g ∧
      (∀ f : CurvePoly k, g (extendElement D f) =
        polynomialFractionMap A (C (Ideal.Quotient.mk D f))) ∧
      (∀ p : k[X], g (algebraMap (SlopeField k) (SlopedCurve D)
          (algebraMap k[X] (SlopeField k) p)) =
        polynomialFractionMap A (p.map (algebraMap k A))) := by
  dsimp only
  let A := CoordinateRing D
  let e : (A ⊗[k] SlopeField k) ≃+* SlopedCurve D :=
    (Algebra.TensorProduct.comm k A (SlopeField k)).toRingEquiv.trans
      (slopeBaseChange D).toRingEquiv
  obtain ⟨g, hg, ha, hp⟩ := tensor_embedding (k := k) (A := A)
  refine ⟨g.comp e.symm.toRingHom, ?_, ?_, ?_⟩
  · change Function.Injective (fun x => g (e.symm x))
    exact hg.comp e.symm.injective
  · intro f
    have he : e (Ideal.Quotient.mk D f ⊗ₜ[k] (1 : SlopeField k)) = extendElement D f := by
      change slopeBaseChange D (Algebra.TensorProduct.comm k A (SlopeField k)
        (Ideal.Quotient.mk D f ⊗ₜ[k] (1 : SlopeField k))) = _
      rw [Algebra.TensorProduct.comm_tmul]
      exact slopeBaseChange_mk D f
    rw [← he]
    change g (e.symm (e _)) = _
    rw [RingEquiv.symm_apply_apply]
    exact ha _
  · intro p
    have he : e (1 ⊗ₜ[k] algebraMap k[X] (SlopeField k) p) =
      algebraMap (SlopeField k) (SlopedCurve D) (algebraMap k[X] (SlopeField k) p) := by
      change slopeBaseChange D (Algebra.TensorProduct.comm k A (SlopeField k)
        (1 ⊗ₜ[k] algebraMap k[X] (SlopeField k) p)) = _
      rw [Algebra.TensorProduct.comm_tmul]
      exact (slopeBaseChange D).commutes _
    rw [← he]
    change g (e.symm (e _)) = _
    rw [RingEquiv.symm_apply_apply]
    exact hp _
end
end K1_14_2_2_7_4_4_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_7_4_3
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_7_4 MvPolynomial
open scoped TensorProduct
private abbrev Parameters (k : Type) [Field k] := MvPolynomial (Fin 2) k
private abbrev ParameterField (k : Type) [Field k] := FractionRing (Parameters k)
private def jetPolynomial (k : Type) [Field k] : Parameters k →+* Polynomial (Parameters k) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    ![Polynomial.C (MvPolynomial.X 1) - Polynomial.C (MvPolynomial.X 0) * Polynomial.X,
      Polynomial.X]
private theorem jetPolynomial_injective (k : Type) [Field k] :
    Function.Injective (jetPolynomial k) := by
  let s : Parameters k →+* Parameters k := MvPolynomial.eval₂Hom MvPolynomial.C ![0, MvPolynomial.X 0]
  let r : Polynomial (Parameters k) →+* Parameters k := Polynomial.eval₂RingHom s (MvPolynomial.X 1)
  have hr : r.comp (jetPolynomial k) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [r, s, jetPolynomial, RingHom.comp_apply]
    · intro i
      fin_cases i <;> simp [r, s, jetPolynomial]
  exact Function.LeftInverse.injective (g := r) (fun p => RingHom.congr_fun hr p)
private def jetPolynomialToField (k : Type) [Field k] :
    Parameters k →+* VField (ParameterField k) :=
  (algebraMap (Polynomial (ParameterField k)) (VField (ParameterField k))).comp
    ((Polynomial.mapRingHom (algebraMap (Parameters k) (ParameterField k))).comp (jetPolynomial k))
private theorem jetPolynomialToField_injective (k : Type) [Field k] :
    Function.Injective (jetPolynomialToField k) := by
  change Function.Injective
    (algebraMap (Polynomial (ParameterField k)) (VField (ParameterField k)) ∘
      Polynomial.map (algebraMap (Parameters k) (ParameterField k)) ∘ jetPolynomial k)
  exact (IsFractionRing.injective _ _).comp
    ((Polynomial.map_injective _ (IsFractionRing.injective _ _)).comp (jetPolynomial_injective k))
private def jetCoefficients (k : Type) [Field k] :
    ParameterField k →+* VField (ParameterField k) :=
  IsFractionRing.lift (jetPolynomialToField_injective k)
private theorem jetCoefficients_algebraMap (k : Type) [Field k] (q : Parameters k) :
    jetCoefficients k (algebraMap (Parameters k) (ParameterField k) q) =
      jetPolynomialToField k q :=
  IsFractionRing.lift_algebraMap _ q
private theorem jetCoefficients_const (k : Type) [Field k] (a : k) :
    jetCoefficients k (algebraMap k (ParameterField k) a) =
      algebraMap (ParameterField k) (VField (ParameterField k)) (algebraMap k (ParameterField k) a) := by
  change jetCoefficients k (algebraMap (Parameters k) (ParameterField k) (MvPolynomial.C a)) = _
  rw [jetCoefficients_algebraMap]
  simp only [jetPolynomialToField, RingHom.comp_apply, jetPolynomial, MvPolynomial.eval₂Hom_C,
    Polynomial.coe_mapRingHom, Polynomial.map_C]
  exact (IsScalarTower.algebraMap_apply (ParameterField k) (Polynomial (ParameterField k))
    (VField (ParameterField k)) (algebraMap k (ParameterField k) a)).symm
private theorem coeffCast (k : Type) [Field k] (a : ParameterField k) :
    algebraMap (Polynomial (ParameterField k)) (VField (ParameterField k)) (Polynomial.C a) =
      algebraMap (ParameterField k) (VField (ParameterField k)) a :=
  (IsScalarTower.algebraMap_apply (ParameterField k) (Polynomial (ParameterField k))
    (VField (ParameterField k)) a).symm
private theorem jetPolynomial_x0 (k : Type) [Field k] :
    jetPolynomial k (MvPolynomial.X 0) =
      Polynomial.C (MvPolynomial.X 1) - Polynomial.C (MvPolynomial.X 0) * Polynomial.X := by
  simp [jetPolynomial]
private theorem jetCoefficients_v (k : Type) [Field k] :
    jetCoefficients k (algebraMap (Parameters k) (ParameterField k) (MvPolynomial.X 1)) =
      algebraMap (Polynomial (ParameterField k)) (VField (ParameterField k)) Polynomial.X := by
  rw [jetCoefficients_algebraMap]
  simp [jetPolynomialToField, jetPolynomial]
private theorem map_affine {R S F A : Type} [CommRing R] [CommRing S] [CommRing F] [CommRing A]
    (m : R →+* S) (j : Polynomial S →+* F) (i : S →+* F) (c : F →+* A)
    (hi : ∀ x, j (Polynomial.C x) = i x) (t b : R) :
    c (i (m b)) - c (i (m t)) * c (j Polynomial.X) =
      c (j (Polynomial.map m (Polynomial.C b - Polynomial.C t * Polynomial.X))) := by
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    map_sub, map_mul, hi]
private theorem sliceMaps :
    (vFibreMap SeedField).comp jetSliceMap =
      (MvPolynomial.map (jetCoefficients FX)).comp mapGenericJets := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [RingHom.comp_apply, vFibreMap, jetSliceMap, mapGenericJets, jetCoefficients_const]
  · intro i
    fin_cases i <;>
      simp [RingHom.comp_apply, vFibreMap, jetSliceMap, mapGenericJets, generic, jetCoefficients_v]
    simp only [jetCoefficients_algebraMap, jetPolynomialToField, RingHom.comp_apply,
      Polynomial.coe_mapRingHom, jetPolynomial_x0]
    exact map_affine (algebraMap Seeds SeedField)
      (algebraMap (Polynomial SeedField) (VField SeedField))
      (algebraMap SeedField (VField SeedField)) MvPolynomial.C (coeffCast FX)
      (MvPolynomial.X 0) (MvPolynomial.X 1)
private theorem sliceIdeal (I : Ideal Ambient) :
    (jetSliceIdeal I).map (vFibreMap SeedField) =
      (I.map mapGenericJets).map (MvPolynomial.map (jetCoefficients FX)) := by
  rw [jetSliceIdeal, Ideal.map_map, Ideal.map_map, sliceMaps]
private def extendQuotient {k E σ : Type} [Field k] [Field E] [Algebra k E]
    (J : Ideal (MvPolynomial σ k)) :
    E ⊗[k] CoordinateRing J ≃ₐ[E]
      CoordinateRing (J.map (MvPolynomial.map (algebraMap k E))) := by
  let e : E ⊗[k] MvPolynomial σ k ≃ₐ[E] MvPolynomial σ E :=
    MvPolynomial.algebraTensorAlgEquiv k E
  have he : (e : E ⊗[k] MvPolynomial σ k →+* MvPolynomial σ E).comp
      (Algebra.TensorProduct.includeRight (R := k) (A := E) (B := MvPolynomial σ k) :
        MvPolynomial σ k →+* E ⊗[k] MvPolynomial σ k) =
      MvPolynomial.map (algebraMap k E) := by
    apply RingHom.ext
    intro p
    change e (1 ⊗ₜ[k] p) = _
    simp [e]
  refine (Algebra.TensorProduct.tensorQuotientEquiv (R := k) E (MvPolynomial σ k) E J).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  rw [← he, ← Ideal.map_map]
  rfl
private theorem extendedRank {k E σ : Type} [Field k] [Field E] [Algebra k E]
    (J : Ideal (MvPolynomial σ k)) [Module.Finite k (CoordinateRing J)] :
    Module.Finite E (CoordinateRing (J.map (MvPolynomial.map (algebraMap k E)))) ∧
    Module.finrank E (CoordinateRing (J.map (MvPolynomial.map (algebraMap k E)))) =
      Module.finrank k (CoordinateRing J) := by
  let e := (extendQuotient (E := E) J).toLinearEquiv
  exact ⟨Module.Finite.of_surjective e.toLinearMap e.surjective,
    e.finrank_eq.symm.trans Module.finrank_baseChange⟩
theorem proof : K1_14_2_2_7_4.c3 := by
  intro I hI
  let : Algebra SeedField (VField SeedField) := (jetCoefficients FX).toAlgebra
  obtain ⟨hfinite, hrank⟩ := extendedRank (E := VField SeedField) (I.map mapGenericJets)
  change Module.Finite (VField SeedField) (CoordinateRing ((jetSliceIdeal I).map (vFibreMap SeedField))) ∧
    Module.finrank (VField SeedField) (CoordinateRing ((jetSliceIdeal I).map (vFibreMap SeedField))) ≤
      Module.finrank SeedField (OverJets I)
  rw [sliceIdeal]
  exact ⟨hfinite, hrank.le⟩
end
end K1_14_2_2_7_4_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace K1_14_2_2_7_3_2
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_7_3 MvPolynomial
open scoped nonZeroDivisors TensorProduct
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev TwoStageField := PlaneField SeedField
private abbrev TwoStageAmbient := MvPolynomial (Fin 4) TwoStageField
private abbrev ParameterRing := MvPolynomial (Fin 4) FX
private abbrev Nested := MvPolynomial (Fin 2) Seeds
private abbrev Localized := MvPolynomial (Fin 2) SeedField
private def indices : Fin 4 ≃ Fin 2 ⊕ Fin 2 :=
  (Equiv.swap 1 2).trans (finSumFinEquiv (m := 2) (n := 2)).symm
private def nest (k : Type) [Field k] :
    MvPolynomial (Fin 4) k ≃+* MvPolynomial (Fin 2) (MvPolynomial (Fin 2) k) :=
  ((renameEquiv k indices).trans (sumAlgEquiv k (Fin 2) (Fin 2))).toRingEquiv
private theorem coefficients_exists (k : Type) [Field k] :
    ∃ e : RingEquiv (FractionRing (MvPolynomial (Fin 4) k)) (PlaneField (PlaneField k)),
      ∀ p : MvPolynomial (Fin 4) k,
        e (algebraMap (MvPolynomial (Fin 4) k) (FractionRing (MvPolynomial (Fin 4) k)) p) =
          algebraMap (MvPolynomial (Fin 2) (PlaneField k)) (PlaneField (PlaneField k))
            (algebraMap (MvPolynomial (Fin 2) (MvPolynomial (Fin 2) k))
              (MvPolynomial (Fin 2) (PlaneField k)) (nest k p)) := by
  let P := MvPolynomial (Fin 2) k
  let H := FractionRing P
  let B := MvPolynomial (Fin 4) k
  let N := MvPolynomial (Fin 2) P
  let S := MvPolynomial (Fin 2) H
  let F := FractionRing B
  let T := FractionRing S
  let D : Submonoid N := P⁰.map MvPolynomial.C
  have : IsLocalization D S := MvPolynomial.isLocalization P⁰ H
  have hinj : Function.Injective (algebraMap N S) :=
    MvPolynomial.map_injective _ (IsFractionRing.injective P H)
  have hcomap : S⁰.comap (algebraMap N S) = N⁰ := by
    ext x
    simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero, map_ne_zero_iff _ hinj]
  have : IsFractionRing N T := by
    change IsLocalization N⁰ T
    rw [← hcomap]
    exact IsLocalization.localization_localization_isLocalization_of_has_all_units D
      S⁰ T (fun _ hu => hu.mem_nonZeroDivisors)
  let s : B ≃+* N := nest k
  let e : F ≃+* T := IsFractionRing.ringEquivOfRingEquiv s
  refine ⟨e, fun p => ?_⟩
  change e (algebraMap B F p) = algebraMap S T (algebraMap N S (s p))
  rw [← IsScalarTower.algebraMap_apply N S T]
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap s p
private def coefficients : RingEquiv SectionField TwoStageField :=
  (coefficients_exists FX).choose
private theorem coefficients_on_polynomial (p : ParameterRing) :
    coefficients (algebraMap ParameterRing SectionField p) =
      algebraMap Localized TwoStageField (algebraMap Nested Localized (nest FX p)) :=
  (coefficients_exists FX).choose_spec p
private theorem coefficients_on_ground (x : FX) :
    coefficients (algebraMap FX SectionField x) =
      algebraMap SeedField TwoStageField (algebraMap FX SeedField x) := by
  change coefficients (algebraMap ParameterRing SectionField (C x)) = _
  rw [coefficients_on_polynomial]
  change algebraMap Localized TwoStageField
    (algebraMap Nested Localized (sumAlgEquiv _ _ _ (renameEquiv FX indices (C x)))) = _
  rw [renameEquiv_apply, rename_C, sumAlgEquiv_C_inl, MvPolynomial.algebraMap_def, map_C]
  rfl
private theorem coefficients_outer {i : Fin 4} {j : Fin 2} (h : indices i = Sum.inl j) :
    coefficients (sliceParameter i) = planeScalar SeedField j := by
  rw [sliceParameter, coefficients_on_polynomial]
  change algebraMap Localized TwoStageField
    (algebraMap Nested Localized (sumAlgEquiv _ _ _ (renameEquiv FX indices (MvPolynomial.X i)))) = _
  rw [renameEquiv_apply, rename_X, h, sumAlgEquiv_X_inl,
    MvPolynomial.algebraMap_def, map_X]
  rfl
private theorem coefficients_inner {i : Fin 4} {j : Fin 2} (h : indices i = Sum.inr j) :
    coefficients (sliceParameter i) = algebraMap SeedField TwoStageField (generic j) := by
  rw [sliceParameter, coefficients_on_polynomial]
  change algebraMap Localized TwoStageField
    (algebraMap Nested Localized (sumAlgEquiv _ _ _ (renameEquiv FX indices (MvPolynomial.X i)))) = _
  rw [renameEquiv_apply, rename_X, h, sumAlgEquiv_X_inr,
    MvPolynomial.algebraMap_def, map_C]
  rfl
private def ambientEquiv : SectionAmbient ≃+* TwoStageAmbient :=
  MvPolynomial.mapEquiv (Fin 4) coefficients
private theorem ambientEquiv_base :
    ambientEquiv.toRingHom.comp sectionBase = (genericBase SeedField).comp (genericBase FX) := by
  apply MvPolynomial.ringHom_ext
  · intro x
    simp only [RingHom.comp_apply, sectionBase, genericBase, map_C]
    change ambientEquiv (C (algebraMap FX SectionField x)) =
      C (algebraMap SeedField TwoStageField (algebraMap FX SeedField x))
    rw [ambientEquiv, mapEquiv_apply, map_C]
    exact congrArg C (coefficients_on_ground x)
  · intro i
    simp [ambientEquiv, sectionBase, genericBase]
private theorem ordinateEquation_image :
    ambientEquiv (MvPolynomial.X 2 - C (sliceParameter 3)) = genericBase SeedField (ySection 2) := by
  have hy := coefficients_inner (i := 3) (j := 1) rfl
  simp [ambientEquiv, mapEquiv_apply, genericBase, ySection, hy]
private theorem seedEquation_image :
    ambientEquiv sectionSeedLine =
      MvPolynomial.X 0 + C (planeScalar SeedField 0) * MvPolynomial.X 1 - C (planeScalar SeedField 1) := by
  have hs := coefficients_outer (i := 0) (j := 0) rfl
  have ht := coefficients_outer (i := 2) (j := 1) rfl
  simp [ambientEquiv, mapEquiv_apply, sectionSeedLine, hs, ht]
private theorem derivativeEquation_image :
    ambientEquiv (MvPolynomial.X 3 - C (sliceParameter 2)) = MvPolynomial.X 3 - C (planeScalar SeedField 1) := by
  have hv := coefficients_outer (i := 2) (j := 1) rfl
  simp [ambientEquiv, mapEquiv_apply, hv]
private def flatIdeal (I : Ideal Ambient) (cut : SectionAmbient) : Ideal SectionAmbient :=
  I.map sectionBase ⊔ Ideal.span {cut, MvPolynomial.X 2 - C (sliceParameter 3)}
private theorem flatIdeal_image (I : Ideal Ambient) (cut : SectionAmbient) :
    (flatIdeal I cut).map ambientEquiv.toRingHom =
      (ordinateIdeal I).map (genericBase SeedField) ⊔ Ideal.span {ambientEquiv cut} := by
  simp only [flatIdeal, ordinateIdeal, Ideal.span_insert, Ideal.map_sup, Ideal.map_span,
    Set.image_singleton, Ideal.map_map, ambientEquiv_base]
  rw [show ambientEquiv.toRingHom (MvPolynomial.X 2 - C (sliceParameter 3)) =
    genericBase SeedField (ySection 2) from ordinateEquation_image]
  let J := I.map ((genericBase SeedField).comp (genericBase FX))
  let A := Ideal.span {ambientEquiv cut}
  let B := Ideal.span {genericBase SeedField (ySection 2)}
  change J ⊔ (A ⊔ B) = (J ⊔ B) ⊔ A
  rw [sup_assoc, sup_comm B A]
private theorem transport {J : Ideal SectionAmbient} {J' : Ideal TwoStageAmbient}
    (hJ : J' = J.map ambientEquiv.toRingHom)
    (hfinite : Module.Finite SectionField (CoordinateRing J)) :
    Module.Finite TwoStageField (CoordinateRing J') ∧
      Module.finrank TwoStageField (CoordinateRing J') =
        Module.finrank SectionField (CoordinateRing J) := by
  let e := Ideal.quotientEquiv J J' ambientEquiv hJ
  have hcomm :
      (algebraMap TwoStageField (CoordinateRing J')).comp coefficients.toRingHom =
        e.toRingHom.comp (algebraMap SectionField (CoordinateRing J)) := by
    apply RingHom.ext
    intro x
    change Ideal.Quotient.mk J' (C (coefficients x)) =
      Ideal.Quotient.mk J' (ambientEquiv (C x))
    rw [ambientEquiv, mapEquiv_apply, map_C]
    rfl
  let f : CoordinateRing J →ₛₗ[coefficients.toRingHom] CoordinateRing J' :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := fun c x => by
        have hc := RingHom.congr_fun hcomm c
        simp only [RingHom.comp_apply] at hc
        calc
          e (c • x) = e (algebraMap SectionField (CoordinateRing J) c * x) :=
            congrArg e (Algebra.smul_def c x)
          _ = e (algebraMap SectionField (CoordinateRing J) c) * e x := e.map_mul _ _
          _ = algebraMap TwoStageField (CoordinateRing J') (coefficients.toRingHom c) * e x :=
            congrArg (fun y => y * e x) hc.symm
          _ = coefficients.toRingHom c • e x := (Algebra.smul_def _ _).symm }
  let _ := hfinite
  exact ⟨Module.Finite.of_surjective f e.surjective,
    (Algebra.finrank_eq_of_equiv_equiv coefficients e hcomm).symm⟩
private theorem seed_length (I : Ideal Ambient)
    (hfinite : Module.Finite SectionField (OverOrdinate I)) :
    Module.Finite TwoStageField (SeedFibre (ordinateIdeal I)) ∧
      Module.finrank TwoStageField (SeedFibre (ordinateIdeal I)) =
        Module.finrank SectionField (OverOrdinate I) := by
  apply transport (J := flatIdeal I sectionSeedLine) _ hfinite
  rw [flatIdeal_image, seedEquation_image]
private def jetIndices : Fin 2 → Fin 4 :=
  Equiv.swap 2 3 ∘ Fin.natAdd 2
private def jetCoefficients : SeedField →+* SectionField :=
  IsFractionRing.map (K := SeedField) (L := SectionField)
    (j := (rename (R := FX) jetIndices).toRingHom)
    (rename_injective _ ((Equiv.swap 2 3).injective.comp (Fin.natAdd_injective 2 2)))
private theorem jetCoefficients_X (i : Fin 2) :
    jetCoefficients (generic i) = sliceParameter (jetIndices i) := by
  unfold jetCoefficients generic sliceParameter IsFractionRing.map
  rw [IsLocalization.map_eq]
  simp
private theorem jetCoefficients_ground (x : FX) :
    jetCoefficients (algebraMap FX SeedField x) = algebraMap FX SectionField x := by
  change jetCoefficients (algebraMap Seeds SeedField (C x)) =
    algebraMap ParameterRing SectionField (C x)
  unfold jetCoefficients IsFractionRing.map
  rw [IsLocalization.map_eq]
  simp
private def jetEval : SectionAmbient →ₐ[SectionField] MvPolynomial (Fin 2) SectionField :=
  aeval ![MvPolynomial.X 0, MvPolynomial.X 1, C (sliceParameter 3), C (sliceParameter 2)]
private def seedIncl : MvPolynomial (Fin 2) SectionField →ₐ[SectionField] SectionAmbient :=
  rename (Fin.castAdd 2)
private theorem jetEval_surjective : Function.Surjective jetEval := by
  have he : jetEval.comp seedIncl = AlgHom.id _ _ := by
    apply algHom_ext
    intro i
    fin_cases i <;> simp [jetEval, seedIncl]
  intro p
  exact ⟨seedIncl p, DFunLike.congr_fun he p⟩
private def jetCut : SectionAmbient := MvPolynomial.X 3 - C (sliceParameter 2)
private theorem jetEval_ker :
    RingHom.ker jetEval.toRingHom = Ideal.span {jetCut, MvPolynomial.X 2 - C (sliceParameter 3)} := by
  let J : Ideal SectionAmbient := Ideal.span {jetCut, MvPolynomial.X 2 - C (sliceParameter 3)}
  let q := Ideal.Quotient.mkₐ SectionField J
  have hy : q (MvPolynomial.X 2) = q (C (sliceParameter 3)) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hv : q (MvPolynomial.X 3) = q (C (sliceParameter 2)) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp [jetCut]))
  have he : (q.comp seedIncl).comp jetEval = q := by
    apply algHom_ext
    intro i
    fin_cases i <;> simp [jetEval, seedIncl, algHom_C, hy, hv]
  apply le_antisymm
  · intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q p = 0
    rw [← DFunLike.congr_fun he p]
    change q (seedIncl (jetEval p)) = 0
    rw [show jetEval p = 0 from hp, map_zero, map_zero]
  · apply Ideal.span_le.mpr
    intro p hp
    change p ∈ ({jetCut, MvPolynomial.X 2 - C (sliceParameter 3)} : Set SectionAmbient) at hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl <;> simp [RingHom.mem_ker, jetCut, jetEval, algebraMap_eq]
private theorem jetEval_base :
    jetEval.toRingHom.comp sectionBase = (MvPolynomial.map jetCoefficients).comp mapGenericJets := by
  apply MvPolynomial.ringHom_ext
  · intro x
    simp [jetEval, sectionBase, mapGenericJets, algebraMap_eq, jetCoefficients_ground]
  · intro i
    have h₀ : jetIndices 0 = 3 := rfl
    have h₁ : jetIndices 1 = 2 := rfl
    fin_cases i <;> simp [jetEval, sectionBase, mapGenericJets, jetCoefficients_X, h₀, h₁]
section BaseChange
variable {k L σ : Type*} [Field k] [Field L] [Algebra k L]
private def extendedQuotient (I : Ideal (MvPolynomial σ k)) :
    L ⊗[k] (MvPolynomial σ k ⧸ I) ≃ₐ[L]
      MvPolynomial σ L ⧸ I.map (MvPolynomial.map (algebraMap k L)) := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := σ) k L
  refine (Algebra.TensorProduct.tensorQuotientEquiv L (MvPolynomial σ k) L I).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  change I.map (MvPolynomial.map (algebraMap k L)) =
    (I.map (Algebra.TensorProduct.includeRight (A := L)).toRingHom).map
      e.toRingEquiv.toRingHom
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro p
  change MvPolynomial.map (algebraMap k L) p = e (1 ⊗ₜ[k] p)
  simp [e]
end BaseChange
private theorem flat_jet_length (I : Ideal Ambient)
    (hfinite : Module.Finite SeedField (OverJets I)) :
    Module.Finite SectionField (CoordinateRing (flatIdeal I jetCut)) ∧
      Module.finrank SectionField (CoordinateRing (flatIdeal I jetCut)) =
        Module.finrank SeedField (OverJets I) := by
  let : Algebra SeedField SectionField := jetCoefficients.toAlgebra
  let J : Ideal (MvPolynomial (Fin 2) SectionField) :=
    (I.map mapGenericJets).map (MvPolynomial.map jetCoefficients)
  let f := (Ideal.Quotient.mkₐ SectionField J).comp jetEval
  have hmap : (I.map sectionBase).map jetEval.toRingHom = J := by
    dsimp only [J]
    rw [Ideal.map_map, Ideal.map_map, jetEval_base]
  have hker : RingHom.ker f.toRingHom = flatIdeal I jetCut := by
    change Ideal.comap jetEval.toRingHom (RingHom.ker (Ideal.Quotient.mk J)) = _
    have hsurj : Function.Surjective jetEval.toRingHom := jetEval_surjective
    rw [Ideal.mk_ker, ← hmap, Ideal.comap_map_of_surjective _ hsurj,
      ← RingHom.ker_eq_comap_bot, jetEval_ker]
    rfl
  let e : CoordinateRing (flatIdeal I jetCut) ≃ₐ[SectionField] CoordinateRing J :=
    (Ideal.quotientEquivAlgOfEq SectionField hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := f)
        (Ideal.Quotient.mk_surjective.comp jetEval_surjective))
  let t : SectionField ⊗[SeedField] OverJets I ≃ₐ[SectionField] CoordinateRing J :=
    extendedQuotient (I.map mapGenericJets)
  let u := (t.trans e.symm).toLinearEquiv
  let _ := hfinite
  refine ⟨Module.Finite.of_surjective u.toLinearMap u.surjective, ?_⟩
  rw [← u.finrank_eq, Module.finrank_baseChange]
private theorem derivative_length (I : Ideal Ambient)
    (hfinite : Module.Finite SeedField (OverJets I)) :
    Module.Finite TwoStageField (VFibre (ordinateIdeal I)) ∧
      Module.finrank TwoStageField (VFibre (ordinateIdeal I)) =
        Module.finrank SeedField (OverJets I) := by
  obtain ⟨hf, hr⟩ := flat_jet_length I hfinite
  have hm : (ordinateIdeal I).map (genericBase SeedField) ⊔
      Ideal.span {MvPolynomial.X 3 - C (planeScalar SeedField 1)} =
      (flatIdeal I jetCut).map ambientEquiv.toRingHom := by
    rw [flatIdeal_image, jetCut, derivativeEquation_image]
  obtain ⟨h, r⟩ := transport hm hf
  exact ⟨h, r.trans hr⟩
theorem proof : K1_14_2_2_7_3.c2 := by
  intro I ho hj
  obtain ⟨hs, rs⟩ := seed_length I ho
  obtain ⟨hv, rv⟩ := derivative_length I hj
  exact ⟨hs, hv, rs, rv⟩
end
end K1_14_2_2_7_3_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_7_4_4_6
noncomputable section
open K1_14_2_2_7_4_4 IsDedekindDomain IsLocalRing WithZero
open UniqueFactorizationMonoid
open scoped Classical WithZero
variable {F B K : Type} [Field F] [CommRing B] [IsDedekindDomain B] [Field K]
  [Algebra F B] [Algebra F K] [Algebra B K] [IsScalarTower F B K] [IsFractionRing B K]
private def adicPlace (p : HeightOneSpectrum B) : Place F K :=
  ⟨p.valuation K, p.valuation_surjective K, (Valuation.IsTrivialOn.of_le_one
    (p.valuation K) fun c => by
      rw [IsScalarTower.algebraMap_apply F B K]
      exact p.valuation_le_one (algebraMap F B c)).eq_one⟩
private theorem adicPlace_injective : Function.Injective (adicPlace (F := F) (K := K) (B := B)) :=
  fun _ _ h => HeightOneSpectrum.valuation_injective K (congrArg Place.val h)
private theorem adicPlace_order (p : HeightOneSpectrum B) {b : B} (hb : b ≠ 0) :
    zeroOrder (adicPlace (F := F) (K := K) p) (algebraMap B K b) =
      multiplicity p.asIdeal (Ideal.span {b}) := by
  change (-log (p.valuation K (algebraMap B K b))).toNat = _
  simp only [p.valuation_of_algebraMap, p.intValuation_eq_exp_neg_multiplicity hb,
    log_exp, neg_neg, Int.toNat_natCast]
private theorem prime_power_weight [Algebra.FiniteType F B] (p : HeightOneSpectrum B) (n : ℕ) :
    Module.finrank F (B ⧸ p.asIdeal ^ n) =
      n * residueDegree (adicPlace (F := F) (K := K) p) := by
  let w := adicPlace (F := F) (K := K) p
  let V := w.val.valuationSubring
  let : Algebra B V := ((algebraMap B K).codRestrict V.toSubring
    (p.valuation_le_one (K := K))).toAlgebra
  let : IsScalarTower F B V := IsScalarTower.of_algebraMap_eq fun c => by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply F B K c
  let e : p.valuationSubringAtPrime K ≃ₐ[B] V :=
    { RingEquiv.subringCongr (congrArg ValuationSubring.toSubring
        (p.valuationSubringAtPrime_eq_valuationSubring (K := K))) with
      commutes' := fun _ => Subtype.ext rfl }
  let : IsLocalization p.asIdeal.primeCompl V :=
    IsLocalization.isLocalization_of_algEquiv p.asIdeal.primeCompl e
  let : IsDiscreteValuationRing V :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B p.ne_bot V
  let : p.asIdeal.IsMaximal := p.isMaximal
  let q (j : ℕ) := (IsLocalization.AtPrime.equivQuotMaximalIdealPow p.asIdeal V j).restrictScalars F
  let qres : (B ⧸ p.asIdeal) ≃ₐ[F] ResidueField V :=
    (Ideal.quotientEquivAlgOfEq F (pow_one p.asIdeal).symm).trans
      ((q 1).trans (Ideal.quotientEquivAlgOfEq F (pow_one (maximalIdeal V))))
  let : Module.Finite F (B ⧸ p.asIdeal) := finite_quotient p.asIdeal p.ne_bot
  let : Module.Finite F (ResidueField V) := Module.Finite.equiv qres.toLinearEquiv
  let : Module.Finite F (B ⧸ p.asIdeal ^ n) := finite_quotient _ (pow_ne_zero _ p.ne_bot)
  let : Module.Finite F (V ⧸ maximalIdeal V ^ n) := Module.Finite.equiv (q n).toLinearEquiv
  have hres : Module.length (ResidueField F) (ResidueField V) =
      Module.finrank F (ResidueField V) := by
    rw [← Module.length_eq_of_surjective (R := ResidueField F)
      (residue_surjective (R := F)), Module.length_eq_finrank]
  have hlen := IsLocalRing.length_restrictScalars F V (V ⧸ maximalIdeal V ^ n)
  rw [Module.length_eq_finrank, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, hres] at hlen
  change Module.finrank F (B ⧸ p.asIdeal ^ n) = n * Module.finrank F (ResidueField V)
  rw [(q n).toLinearEquiv.finrank_eq]
  exact_mod_cast hlen
private abbrev CutFactors (I : Ideal B) := (factors I).toFinset
private def factorPrime {I : Ideal B} (p : CutFactors I) : HeightOneSpectrum B :=
  HeightOneSpectrum.ofPrime (prime_of_factor p.val (Multiset.mem_toFinset.mp p.property))
theorem normalized_cut [Algebra.FiniteType F B] (b : B) (hb : b ≠ 0) :
    ∃ S : Finset (Place F K),
      Module.finrank F (B ⧸ Ideal.span {b}) = zeroDegree S (algebraMap B K b) := by
  let I := Ideal.span {b}
  have hI : I ≠ ⊥ := by simpa only [I, ne_eq, Ideal.span_singleton_eq_bot] using hb
  let n (p : CutFactors I) := (factors I).count p.val
  let e := IsDedekindDomain.quotientEquivPiFactors hI
  let eF : (B ⧸ I) ≃ₐ[F] ∀ p : CutFactors I, B ⧸ p.val ^ n p :=
    { e with
      commutes' := fun c => by
        funext p
        change e (Ideal.Quotient.mk _ (algebraMap F B c)) p =
          Ideal.Quotient.mk _ (algebraMap F B c)
        rw [IsDedekindDomain.quotientEquivPiFactors_mk] }
  let w : CutFactors I ↪ Place F K :=
    ⟨fun p => adicPlace (factorPrime p), fun _ _ h =>
      Subtype.ext (congrArg HeightOneSpectrum.asIdeal (adicPlace_injective h))⟩
  refine ⟨Finset.univ.map w, ?_⟩
  have (p : CutFactors I) : Module.Finite F (B ⧸ p.val ^ n p) :=
    finite_quotient _ (pow_ne_zero _ (factorPrime p).ne_bot)
  rw [eF.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype, zeroDegree, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro p _
  have hn : zeroOrder (w p) (algebraMap B K b) = n p := by
    rw [show w p = adicPlace (factorPrime p) from rfl, adicPlace_order _ hb]
    change multiplicity (factorPrime p).asIdeal I = (factors I).count (factorPrime p).asIdeal
    rw [factors_eq_normalizedFactors, HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hI]
  rw [hn, mul_comm]
  exact prime_power_weight (F := F) (K := K) (factorPrime p) (n p)
end
end K1_14_2_2_7_4_4_6
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_2_2_7_3_1
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_7_3
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem lift_chain
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] [FaithfulSMul R S] (l : LTSeries (PrimeSpectrum R)) :
    ∃ L : LTSeries (PrimeSpectrum S),
      L.length = l.length ∧ L.last.asIdeal.under R = l.last.asIdeal := by
  induction l using RelSeries.inductionOn' with
  | singleton p =>
    have := p.isPrime
    have hle : (⊥ : Ideal S).under R ≤ p.asIdeal := by
      change Ideal.comap (algebraMap R S) ⊥ ≤ p.asIdeal
      rw [← RingHom.ker_eq_comap_bot,
        (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective R S)]
      exact bot_le
    obtain ⟨P, _, hP, hPp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
      p.asIdeal (⊥ : Ideal S) hle
    exact ⟨RelSeries.singleton _ ⟨P, hP⟩, rfl, hPp⟩
  | snoc l p hp ih =>
    obtain ⟨L, hlen, hlast⟩ := ih
    have := p.isPrime
    have hlt : l.last < p := hp
    obtain ⟨P, hLP, hP, hPp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
      p.asIdeal L.last.asIdeal (hlast.trans_le hlt.le)
    have hnext : L.last < (⟨P, hP⟩ : PrimeSpectrum S) := by
      refine lt_of_le_of_ne hLP fun heq => hlt.ne (PrimeSpectrum.ext_iff.mpr ?_)
      exact hlast.symm.trans ((congrArg (fun x : PrimeSpectrum S => x.asIdeal.under R) heq).trans hPp)
    exact ⟨L.snoc ⟨P, hP⟩ hnext, by simp [RelSeries.snoc, hlen], by simpa using hPp⟩
private theorem affine_dimension (k A : Type) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ∃ d : ℕ, ringKrullDim A = (d : WithBot ℕ∞) ∧ Algebra.trdeg k A = (d : Cardinal) := by
  obtain ⟨d, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg k A
  let R := MvPolynomial (Fin d) k
  let : Algebra R A := g.toRingHom.toAlgebra
  let : Module.Finite R A := hgfin
  let : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A
  let : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hginj
  let : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq fun a => (g.commutes a).symm
  have hdim : ringKrullDim R = (d : WithBot ℕ∞) := by
    simp [R, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
  refine ⟨d, ?_, ?_⟩
  · rw [← hdim]
    apply le_antisymm
    · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R A))
      intro a b hab
      exact Ideal.IsIntegral.under_lt_under (R := R) (show a.asIdeal < b.asIdeal from hab)
    · rw [hdim]
      obtain ⟨l, hlen⟩ := Order.le_krullDim_iff.mp hdim.ge
      obtain ⟨L, hL, _⟩ := lift_chain (S := A) l
      exact Order.le_krullDim_iff.mpr ⟨L, hL.trans hlen⟩
  · let : Algebra.IsAlgebraic R A := Algebra.IsAlgebraic.of_finite R A
    simpa [R, trdeg_eq_zero (R := R) (A := A), Cardinal.mk_fin] using
      (trdeg_add_eq (A := A) k R).symm
private abbrev BeforeLocalization := MvPolynomial (Fin 4) Seeds
private abbrev denominators : Submonoid BeforeLocalization :=
  Seeds⁰.map (MvPolynomial.C (σ := Fin 4))
private def beforeBase : Ambient →+* BeforeLocalization :=
  MvPolynomial.map MvPolynomial.C
private def beforeOrdinate : BeforeLocalization :=
  MvPolynomial.X 2 - MvPolynomial.C (MvPolynomial.X 1)
private def parameterEval (I : Ideal Ambient) : Seeds →+* Polynomial (CoordinateRing I) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp ((Ideal.Quotient.mk I).comp MvPolynomial.C))
    ![Polynomial.X, Polynomial.C (Ideal.Quotient.mk I (MvPolynomial.X 2))]
private def beforeEval (I : Ideal Ambient) : BeforeLocalization →+* Polynomial (CoordinateRing I) :=
  MvPolynomial.eval₂Hom (parameterEval I)
    (fun i => Polynomial.C (Ideal.Quotient.mk I (MvPolynomial.X i)))
private theorem beforeEval_comp (I : Ideal Ambient) :
    (beforeEval I).comp beforeBase = Polynomial.C.comp (Ideal.Quotient.mk I) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [beforeEval, beforeBase, parameterEval]
  · intro i
    simp [beforeEval, beforeBase]
private theorem beforeEval_surjective (I : Ideal Ambient) : Function.Surjective (beforeEval I) := by
  let u := Polynomial.eval₂RingHom beforeBase
    (MvPolynomial.C (MvPolynomial.X 0) : BeforeLocalization)
  have he : (beforeEval I).comp u = Polynomial.mapRingHom (Ideal.Quotient.mk I) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, u, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        Polynomial.coe_mapRingHom, Polynomial.map_C]
      exact RingHom.congr_fun (beforeEval_comp I) a
    · simp [u, beforeEval, parameterEval]
  have hs : Function.Surjective ((beforeEval I).comp u) := by
    rw [he]
    exact Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
  exact Function.Surjective.of_comp (f := beforeEval I) (g := u) hs
private theorem localized_beforeBase :
    (algebraMap BeforeLocalization OrdinateAmbient).comp beforeBase = genericBase FX := by
  change (MvPolynomial.map (algebraMap Seeds SeedField)).comp beforeBase = genericBase FX
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, beforeBase, genericBase, MvPolynomial.map_C]
    rfl
  · intro i
    simp only [RingHom.comp_apply, beforeBase, genericBase, MvPolynomial.map_X]
private theorem localized_beforeOrdinate :
    algebraMap BeforeLocalization OrdinateAmbient beforeOrdinate = ySection 2 := by
  change MvPolynomial.map (algebraMap Seeds SeedField) beforeOrdinate = ySection 2
  simp only [beforeOrdinate, map_sub, MvPolynomial.map_X, MvPolynomial.map_C, ySection, generic]
private abbrev SectionRing (I : Ideal Ambient) := CoordinateRing (ordinateIdeal I)
private def quotientBase (I : Ideal Ambient) : CoordinateRing I →+* SectionRing I :=
  Ideal.Quotient.lift I ((Ideal.Quotient.mk (ordinateIdeal I)).comp (genericBase FX))
    (fun _ ha => Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_sup_left (Ideal.mem_map_of_mem (genericBase FX) ha)))
private def polyToSection (I : Ideal Ambient) : Polynomial (CoordinateRing I) →+* SectionRing I :=
  Polynomial.eval₂RingHom (quotientBase I)
    (Ideal.Quotient.mk (ordinateIdeal I) (MvPolynomial.C (generic 0)))
private theorem polyToSection_C (I : Ideal Ambient) (a : Ambient) :
    polyToSection I (Polynomial.C (Ideal.Quotient.mk I a)) =
      Ideal.Quotient.mk (ordinateIdeal I) (genericBase FX a) := by
  simp only [polyToSection, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, quotientBase,
    Ideal.Quotient.lift_mk]
  rfl
private theorem ordinate_relation (I : Ideal Ambient) :
    Ideal.Quotient.mk (ordinateIdeal I) (MvPolynomial.X 2) =
      Ideal.Quotient.mk (ordinateIdeal I) (MvPolynomial.C (generic 1)) := by
  apply sub_eq_zero.mp
  rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton (ySection 2)))
private theorem evaluation_square (I : Ideal Ambient) :
    (Ideal.Quotient.mk (ordinateIdeal I)).comp (algebraMap BeforeLocalization OrdinateAmbient) =
      (polyToSection I).comp (beforeEval I) := by
  let q := Ideal.Quotient.mk (ordinateIdeal I)
  let f : BeforeLocalization →+* OrdinateAmbient := MvPolynomial.map (algebraMap Seeds SeedField)
  change q.comp f = (polyToSection I).comp (beforeEval I)
  apply MvPolynomial.ringHom_ext
  · have hc : (q.comp f).comp MvPolynomial.C =
        ((polyToSection I).comp (beforeEval I)).comp MvPolynomial.C := by
      apply MvPolynomial.ringHom_ext
      · intro a
        change q (f (MvPolynomial.C (MvPolynomial.C a))) =
          polyToSection I (beforeEval I (MvPolynomial.C (MvPolynomial.C a)))
        simp only [f, MvPolynomial.map_C, beforeEval, parameterEval, MvPolynomial.eval₂Hom_C,
          RingHom.comp_apply, polyToSection_C, genericBase]
        rfl
      · intro i
        change q (f (MvPolynomial.C (MvPolynomial.X i))) =
          polyToSection I (beforeEval I (MvPolynomial.C (MvPolynomial.X i)))
        simp only [f, MvPolynomial.map_C, beforeEval, MvPolynomial.eval₂Hom_C, parameterEval,
          MvPolynomial.eval₂Hom_X']
        fin_cases i
        · change q (MvPolynomial.C (generic 0)) = polyToSection I Polynomial.X
          simp only [polyToSection, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, q]
        · change q (MvPolynomial.C (generic 1)) =
            polyToSection I (Polynomial.C (Ideal.Quotient.mk I (MvPolynomial.X 2)))
          rw [polyToSection_C, genericBase, MvPolynomial.map_X]
          exact (ordinate_relation I).symm
    exact RingHom.congr_fun hc
  · intro i
    change q (f (MvPolynomial.X i)) = polyToSection I (beforeEval I (MvPolynomial.X i))
    simp only [f, MvPolynomial.map_X, beforeEval, MvPolynomial.eval₂Hom_X', polyToSection_C,
      genericBase, q]
private abbrev sectionAlgebra (I : Ideal Ambient) :
    Algebra (Polynomial (CoordinateRing I)) (SectionRing I) :=
  (polyToSection I).toAlgebra
private theorem localization_of_section (I : Ideal Ambient) :
    letI : Algebra (Polynomial (CoordinateRing I)) (SectionRing I) := sectionAlgebra I
    IsLocalization (denominators.map (beforeEval I)) (SectionRing I) := by
  let : Algebra (Polynomial (CoordinateRing I)) (SectionRing I) := sectionAlgebra I
  apply IsLocalization.of_surjective (S' := SectionRing I) denominators OrdinateAmbient (beforeEval I)
    (beforeEval_surjective I) (Ideal.Quotient.mk (ordinateIdeal I)) Ideal.Quotient.mk_surjective
    (evaluation_square I)
  rw [Ideal.mk_ker, ordinateIdeal]
  apply sup_le
  · rw [← localized_beforeBase, ← Ideal.map_map]
    apply Ideal.map_mono
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change beforeEval I (beforeBase a) = 0
    rw [show beforeEval I (beforeBase a) = Polynomial.C (Ideal.Quotient.mk I a)
        from RingHom.congr_fun (beforeEval_comp I) a,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  · rw [← localized_beforeOrdinate, Ideal.span_singleton_le_iff_mem]
    apply Ideal.mem_map_of_mem
    change beforeEval I beforeOrdinate = 0
    simp [beforeEval, beforeOrdinate, parameterEval]
private theorem section_algebraMap (I : Ideal Ambient) (a : FX) :
    algebraMap FX (SectionRing I) a =
      polyToSection I (algebraMap FX (Polynomial (CoordinateRing I)) a) := by
  change Ideal.Quotient.mk (ordinateIdeal I) (MvPolynomial.C (algebraMap FX SeedField a)) =
    polyToSection I (Polynomial.C (Ideal.Quotient.mk I (MvPolynomial.C a)))
  rw [polyToSection_C, genericBase, MvPolynomial.map_C]
private theorem trdeg_of_localization (k R S : Type) [Field k] [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [Algebra k R] [Algebra k S] [hAlg : Algebra R S]
    [FaithfulSMul k R] (M : Submonoid R) [hLoc : IsLocalization M S]
    (hcomp : ∀ x : k, algebraMap k S x = algebraMap R S (algebraMap k R x)) :
    Algebra.trdeg k S = Algebra.trdeg k R := by
  let : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq hcomp
  have hM : M ≤ R⁰ := by
    intro a ha
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro h
    have hunit := IsLocalization.map_units S (⟨a, ha⟩ : M)
    change IsUnit (algebraMap R S a) at hunit
    rw [h, map_zero] at hunit
    exact not_isUnit_zero hunit
  let : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr
    (IsLocalization.injective S hM)
  let : Algebra.IsAlgebraic R S := IsLocalization.isAlgebraic S M
  simpa only [trdeg_eq_zero (R := R) (A := S), add_zero] using
    (trdeg_add_eq (A := S) k R).symm
private theorem trdeg_polynomial (k R : Type) [Field k] [CommRing R] [IsDomain R]
    [Algebra k R] [FaithfulSMul k R] :
    Algebra.trdeg k (Polynomial R) = Algebra.trdeg k R + 1 := by
  let : FaithfulSMul R (Polynomial R) := (faithfulSMul_iff_algebraMap_injective R (Polynomial R)).mpr
    Polynomial.C_injective
  simpa only [Polynomial.trdeg_of_isDomain] using (trdeg_add_eq (A := Polynomial R) k R).symm
private theorem trdeg_section_over_constants (I : Ideal Ambient) (hp : I.IsPrime)
    (hdom : Function.Injective ((Ideal.Quotient.mk I).comp ordinateIncl)) :
    Algebra.trdeg FX (SectionRing I) = Algebra.trdeg FX (CoordinateRing I) + 1 := by
  let := hp
  let : (ordinateIdeal I).IsPrime := ((ordinate_localization I hp).1 hdom).1
  let : FaithfulSMul FX (Polynomial (CoordinateRing I)) :=
    (faithfulSMul_iff_algebraMap_injective FX (Polynomial (CoordinateRing I))).mpr
      (algebraMap FX (Polynomial (CoordinateRing I))).injective
  let : FaithfulSMul FX (CoordinateRing I) :=
    (faithfulSMul_iff_algebraMap_injective FX (CoordinateRing I)).mpr
      (algebraMap FX (CoordinateRing I)).injective
  have hloc := trdeg_of_localization FX (Polynomial (CoordinateRing I)) (SectionRing I)
    (hAlg := sectionAlgebra I) (denominators.map (beforeEval I))
    (hLoc := localization_of_section I) (section_algebraMap I)
  exact hloc.trans (trdeg_polynomial FX (CoordinateRing I))
private theorem trdeg_seedField : Algebra.trdeg FX SeedField = 2 := by
  let : Algebra.IsAlgebraic Seeds SeedField := IsLocalization.isAlgebraic SeedField Seeds⁰
  simpa [Seeds, trdeg_eq_zero (R := Seeds) (A := SeedField), Cardinal.mk_fin] using
    (trdeg_add_eq (A := SeedField) FX Seeds).symm
theorem proof : K1_14_2_2_7_3.c1 := by
  intro I hp hdim hdom
  change ringKrullDim (SectionRing I) = 1
  let := hp
  let : (ordinateIdeal I).IsPrime := ((ordinate_localization I hp).1 hdom).1
  obtain ⟨d, hd, ht⟩ := affine_dimension FX (CoordinateRing I)
  have hd' : d = 2 := by
    rw [hdim] at hd
    exact_mod_cast hd.symm
  have htotal : Algebra.trdeg FX (SectionRing I) = 3 := by
    rw [trdeg_section_over_constants I hp hdom, ht, hd']
    norm_num
  let : FaithfulSMul SeedField (SectionRing I) :=
    (faithfulSMul_iff_algebraMap_injective SeedField (SectionRing I)).mpr
      (algebraMap SeedField (SectionRing I)).injective
  have htower := trdeg_add_eq (A := SectionRing I) FX SeedField
  rw [trdeg_seedField, htotal] at htower
  have hrel : Algebra.trdeg SeedField (SectionRing I) = 1 := by
    apply Cardinal.eq_of_add_eq_add_left (a := 2)
    · exact htower.trans (by norm_num)
    · simp
  obtain ⟨e, he, hte⟩ := affine_dimension SeedField (SectionRing I)
  have he' : e = 1 := by
    rw [hrel] at hte
    exact_mod_cast hte.symm
  simpa [he'] using he
end
end K1_14_2_2_7_3_1
end
section
set_option autoImplicit false
namespace K1_14_2_2_7_4_4_1
noncomputable section
open K1_14_2 K1_14_2_2_7_4 K1_14_2_2_7_4_4 Polynomial
open scoped nonZeroDivisors
attribute [local instance] Polynomial.algebra
variable {k A : Type} [Field k] [CommRing A] [Algebra k A]
private theorem algebraic_of_image {S : Type} [CommRing S] [Algebra (SlopeField k) S]
    (f : S →+* FractionRing (A[X]))
    (hf : ∀ p : k[X], f (algebraMap (SlopeField k) S (algebraMap k[X] (SlopeField k) p)) =
      algebraMap A[X] (FractionRing (A[X])) (algebraMap k[X] A[X] p))
    {z : S} {p : A[X]} (hp : f z = algebraMap A[X] (FractionRing (A[X])) p)
    (hz : IsAlgebraic (SlopeField k) z) : IsAlgebraic k[X] p := by
  obtain ⟨q, hq, hz⟩ := hz
  let j := algebraMap A[X] (FractionRing (A[X]))
  let g := f.comp (algebraMap (SlopeField k) S)
  have he : eval₂ g (f z) q = 0 := by
    rw [← Polynomial.hom_eval₂, ← aeval_def, hz, map_zero]
  have hcomp : g.comp (algebraMap k[X] (SlopeField k)) = j.comp (algebraMap k[X] A[X]) :=
    RingHom.ext hf
  refine ⟨IsLocalization.integerNormalization (k[X]⁰) q,
    mt IsFractionRing.integerNormalization_eq_zero_iff.mp hq, ?_⟩
  have hh := IsLocalization.integerNormalization_eval₂_eq_zero (k[X]⁰) g q he
  rw [hcomp, hp, ← Polynomial.hom_eval₂, ← aeval_def] at hh
  exact (IsFractionRing.injective A[X] (FractionRing (A[X]))) (hh.trans (map_zero j).symm)
variable [IsDomain A]
private theorem integral_leadingCoeff {p : A[X]} (hp : IsAlgebraic k[X] p) :
    IsIntegral k p.leadingCoeff := by
  obtain ⟨r, hr, hi⟩ := hp.exists_integral_multiple
  have hlead := hi.coeff (r • p : A[X]).natDegree
  change IsIntegral k (r • p : A[X]).leadingCoeff at hlead
  rw [Algebra.smul_def, leadingCoeff_mul, Polynomial.algebraMap_def, coe_mapRingHom,
    leadingCoeff_map_of_injective (algebraMap k A).injective] at hlead
  have hinv := (isIntegral_algebraMap (R := k) (A := A) (x := r.leadingCoeff⁻¹)).mul hlead
  rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hr), map_one,
    one_mul] at hinv
  exact hinv
private theorem integral_seeds {x y : A}
    (h : IsAlgebraic k[X] (C x + (Polynomial.X : A[X]) * C y)) : IsIntegral k x ∧ IsIntegral k y := by
  have hy : IsIntegral k y := by
    by_cases hy : y = 0
    · simp [hy, isIntegral_zero]
    · have hl := integral_leadingCoeff h
      rwa [add_comm, mul_comm (Polynomial.X : A[X]), leadingCoeff_linear hy] at hl
  have hterm : IsIntegral k[X] ((Polynomial.X : A[X]) * C y) := by
    apply Polynomial.isIntegral_iff_isIntegral_coeff.mpr
    intro n
    rw [mul_comm, C_mul_X_eq_monomial, coeff_monomial]
    split_ifs
    · exact hy
    · exact isIntegral_zero
  have hx : IsAlgebraic k[X] (C x : A[X]) := by
    simpa only [add_sub_cancel_right] using h.sub hterm.isAlgebraic
  exact ⟨by simpa only [leadingCoeff_C] using integral_leadingCoeff hx, hy⟩
private abbrev coord (D : Ideal (CurvePoly k)) (i : Option (Fin 2)) : CoordinateRing D :=
  Ideal.Quotient.mk D (MvPolynomial.X i)
private theorem not_all_integral (D : Ideal (CurvePoly k)) [D.IsPrime]
    (hdim : ringKrullDim (CoordinateRing D) = 1) :
    ¬ ∀ i, IsIntegral k (coord D i) := by
  intro h
  let : Algebra.IsIntegral k (CoordinateRing D) := by
    constructor
    intro a
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    induction p using MvPolynomial.induction_on with
    | C c => exact isIntegral_algebraMap (x := c)
    | add p q hp hq => simpa only [map_add] using hp.add hq
    | mul_X p i hp => simpa only [map_mul] using hp.mul (h i)
  have hfield : IsField (CoordinateRing D) := isField_of_isIntegral_of_isField' (Field.toIsField k)
  exact zero_ne_one ((ringKrullDim_eq_zero_of_isField hfield).symm.trans hdim)
private theorem seedParameter_eq (D : Ideal (CurvePoly k)) [IsDomain (SlopedCurve D)] :
    seedParameter D =
      fieldCoord D (some 0) + algebraMap (SlopeField k) (CurveField D) (genericSlope k) *
        fieldCoord D (some 1) := by
  simp only [seedParameter, fieldCoord, fieldEval, slopeMap, RingHom.comp_apply,
    MvPolynomial.map_X, RingHom.map_add, RingHom.map_mul]
  rw [IsScalarTower.algebraMap_apply (SlopeField k) (SlopedCurve D) (CurveField D)]
  rfl
set_option maxHeartbeats 800000 in
theorem proof : K1_14_2_2_7_4_4.c1 := by
  classical
  intro k _ D hD hdim
  let : D.IsPrime := hD
  let A := CoordinateRing D
  let L := FractionRing (A[X])
  obtain ⟨g, hg, hcoords, hscalar⟩ := slope_embedding D
  let h : IsDomain (SlopedCurve D) := Function.Injective.isDomain g hg
  refine ⟨h, ?_⟩
  by_cases hs : IsAlgebraic (SlopeField k) (seedParameter D)
  · right
    intro hv
    let f : CurveField D →+* L := IsFractionRing.lift hg
    have hmap (a : SlopedCurve D) : f (algebraMap (SlopedCurve D) (CurveField D) a) = g a :=
      IsFractionRing.lift_algebraMap hg a
    have hscalar' (p : k[X]) : f (algebraMap (SlopeField k) (CurveField D)
          (algebraMap k[X] (SlopeField k) p)) =
        polynomialFractionMap A (p.map (algebraMap k A)) := by
      rw [IsScalarTower.algebraMap_apply (SlopeField k) (SlopedCurve D) (CurveField D), hmap]
      exact hscalar p
    have hcoord (i : Option (Fin 2)) :
        f (fieldCoord D i) = polynomialFractionMap A (C (coord D i)) := by
      change f (algebraMap (SlopedCurve D) (CurveField D)
        (extendElement D (MvPolynomial.X i))) = _
      rw [hmap, hcoords]
    have hp : f (seedParameter D) =
        polynomialFractionMap A (C (coord D (some 0)) +
          (Polynomial.X : A[X]) * C (coord D (some 1))) := by
      rw [seedParameter_eq D, f.map_add, f.map_mul, hcoord, hcoord, genericSlope, hscalar']
      simp only [Polynomial.map_X, RingHom.map_add, RingHom.map_mul]
    have hxy := integral_seeds (algebraic_of_image (k := k) (A := A) f hscalar' hp hs)
    have hV := integral_leadingCoeff (algebraic_of_image (k := k) (A := A) f hscalar' (hcoord none) hv)
    simp only [leadingCoeff_C] at hV
    apply not_all_integral D hdim
    intro i
    rcases i with _ | i
    · exact hV
    · fin_cases i
      · exact hxy.1
      · exact hxy.2
  · exact Or.inl hs
end
end K1_14_2_2_7_4_4_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 16
namespace K1_14_2_2_7_2_5
noncomputable section
open K1_14 K1_14_2 K1_14_2_2_7_2
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
abbrev PreAmbient := MvPolynomial (Fin 4) Seeds
def preBase : Ambient →+* PreAmbient := MvPolynomial.map MvPolynomial.C
def preParameter (i : Fin 2) : PreAmbient := MvPolynomial.C (MvPolynomial.X i)
def preLine : PreAmbient :=
  MvPolynomial.X 0 + preParameter 0 * MvPolynomial.X 1 - preParameter 1
abbrev preIdeal (Q : Ideal Ambient) : Ideal PreAmbient :=
  Q.map preBase ⊔ Ideal.span {preLine}
abbrev denominators : Submonoid PreAmbient :=
  (nonZeroDivisors Seeds).map MvPolynomial.C
private def quotientConstant (Q : Ideal Ambient) : Ambient →+* Polynomial (Ambient ⧸ Q) :=
  Polynomial.C.comp (Ideal.Quotient.mk Q)
def parameterEval (Q : Ideal Ambient) : Seeds →+* Polynomial (Ambient ⧸ Q) :=
  MvPolynomial.eval₂Hom ((quotientConstant Q).comp MvPolynomial.C)
    ![Polynomial.X, quotientConstant Q (MvPolynomial.X 0) +
      Polynomial.X * quotientConstant Q (MvPolynomial.X 1)]
def preEval (Q : Ideal Ambient) : PreAmbient →+* Polynomial (Ambient ⧸ Q) :=
  MvPolynomial.eval₂Hom (parameterEval Q) (fun i => quotientConstant Q (MvPolynomial.X i))
private theorem preEval_preBase (Q : Ideal Ambient) :
    (preEval Q).comp preBase = quotientConstant Q := by
  apply MvPolynomial.ringHom_ext <;> intro r <;>
    simp [preEval, preBase, parameterEval]
private theorem preIdeal_le_ker (Q : Ideal Ambient) : preIdeal Q ≤ RingHom.ker (preEval Q) := by
  apply sup_le
  · rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker, preEval_preBase]
    intro r hr
    simp [RingHom.mem_ker, quotientConstant, Ideal.Quotient.eq_zero_iff_mem.mpr hr]
  · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
    simp [preLine, preParameter, preEval, parameterEval]
private def quotientToPreSlice (Q : Ideal Ambient) : (Ambient ⧸ Q) →+* (PreAmbient ⧸ preIdeal Q) :=
  Ideal.Quotient.lift Q ((Ideal.Quotient.mk (preIdeal Q)).comp preBase) fun _ hr =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.mem_map_of_mem preBase hr))
private def preEvalInverse (Q : Ideal Ambient) :
    Polynomial (Ambient ⧸ Q) →+* (PreAmbient ⧸ preIdeal Q) :=
  Polynomial.eval₂RingHom (quotientToPreSlice Q) (Ideal.Quotient.mk (preIdeal Q) (preParameter 0))
private theorem preEvalInverse_constant (Q : Ideal Ambient) :
    (preEvalInverse Q).comp (quotientConstant Q) = (Ideal.Quotient.mk (preIdeal Q)).comp preBase := by
  apply RingHom.ext
  intro r
  simp [preEvalInverse, quotientConstant, quotientToPreSlice]
private theorem preEvalInverse_parameter (Q : Ideal Ambient) :
    (preEvalInverse Q).comp (parameterEval Q) =
      (Ideal.Quotient.mk (preIdeal Q)).comp MvPolynomial.C := by
  let m := Ideal.Quotient.mk (preIdeal Q)
  have hline : m (MvPolynomial.X 0) + m (preParameter 0) * m (MvPolynomial.X 1) =
      m (preParameter 1) := by
    have h : m preLine = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_sup_right (Ideal.mem_span_singleton_self preLine))
    simpa [preLine, map_sub, map_add, map_mul, sub_eq_zero] using h
  have hconst (r : Ambient) : preEvalInverse Q (quotientConstant Q r) = m (preBase r) :=
    DFunLike.congr_fun (preEvalInverse_constant Q) r
  apply MvPolynomial.ringHom_ext
  · intro r
    simpa only [RingHom.comp_apply, parameterEval, MvPolynomial.eval₂Hom_C, preBase,
      MvPolynomial.map_C] using hconst (MvPolynomial.C r)
  · intro i
    fin_cases i
    · simp [parameterEval, preEvalInverse, preParameter]
    · change preEvalInverse Q (parameterEval Q (MvPolynomial.X 1)) = m (preParameter 1)
      rw [parameterEval, MvPolynomial.eval₂Hom_X']
      change preEvalInverse Q (quotientConstant Q (MvPolynomial.X 0) +
        Polynomial.X * quotientConstant Q (MvPolynomial.X 1)) = m (preParameter 1)
      rw [map_add, map_mul, hconst, hconst]
      simpa [preEvalInverse, preBase, m] using hline
private theorem preEvalInverse_comp (Q : Ideal Ambient) :
    (preEvalInverse Q).comp (preEval Q) = Ideal.Quotient.mk (preIdeal Q) := by
  rw [preEval, MvPolynomial.comp_eval₂Hom, preEvalInverse_parameter]
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    have h := DFunLike.congr_fun (preEvalInverse_constant Q) (MvPolynomial.X i)
    simpa [preBase] using h
theorem preIdeal_eq_ker (Q : Ideal Ambient) : preIdeal Q = RingHom.ker (preEval Q) := by
  apply le_antisymm (preIdeal_le_ker Q)
  intro r hr
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have h := DFunLike.congr_fun (preEvalInverse_comp Q) r
  simpa only [RingHom.comp_apply, RingHom.mem_ker.mp hr, map_zero] using h.symm
theorem preEval_surjective (Q : Ideal Ambient) : Function.Surjective (preEval Q) := by
  let lift := Polynomial.eval₂RingHom preBase (preParameter 0)
  have h : (preEval Q).comp lift = Polynomial.mapRingHom (Ideal.Quotient.mk Q) := by
    apply Polynomial.ringHom_ext
    · intro r
      simpa only [RingHom.comp_apply, lift, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        Polynomial.coe_mapRingHom, Polynomial.map_C, quotientConstant] using
        RingHom.congr_fun (preEval_preBase Q) r
    · simp [lift, preParameter, preEval, parameterEval]
  apply Function.Surjective.of_comp (f := preEval Q) (g := lift)
  change Function.Surjective ((preEval Q).comp lift)
  rw [h]
  exact Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
private theorem preBase_comp : (algebraMap PreAmbient SeedAmbient).comp preBase = seedBase := by
  rw [seedBase, IsScalarTower.algebraMap_eq FX Seeds SeedField, MvPolynomial.algebraMap_def]
  exact RingHom.ext (MvPolynomial.map_map MvPolynomial.C _)
theorem preIdeal_map (Q : Ideal Ambient) :
    (preIdeal Q).map (algebraMap PreAmbient SeedAmbient) = seedIdeal Q := by
  have hline : algebraMap PreAmbient SeedAmbient preLine = seedLine 0 1 := by
    simp [preLine, preParameter, seedLine, generic]
  simp only [preIdeal, Ideal.map_sup, Ideal.map_map, preBase_comp, Ideal.map_span,
    Set.image_singleton, hline]
def seedSliceMap (Q : Ideal Ambient) : Polynomial (Ambient ⧸ Q) →+* JetSeedSection Q :=
  (Ideal.quotientMap (seedIdeal Q) (algebraMap PreAmbient SeedAmbient)
    (Ideal.map_le_iff_le_comap.mp (preIdeal_map Q).le)).comp (preEvalInverse Q)
private theorem seedSliceMap_comp (Q : Ideal Ambient) :
    (seedSliceMap Q).comp (preEval Q) =
      (Ideal.Quotient.mk (seedIdeal Q)).comp (algebraMap PreAmbient SeedAmbient) := by
  rw [seedSliceMap, RingHom.comp_assoc, preEvalInverse_comp]
  rfl
theorem seedSliceMap_constant (Q : Ideal Ambient) (r : Ambient) :
    seedSliceMap Q (Polynomial.C (Ideal.Quotient.mk Q r)) = seedRestrict Q r := by
  have h := RingHom.congr_fun (seedSliceMap_comp Q) (preBase r)
  change seedSliceMap Q (preEval Q (preBase r)) =
    Ideal.Quotient.mk (seedIdeal Q) (algebraMap PreAmbient SeedAmbient (preBase r)) at h
  have he := RingHom.congr_fun (preEval_preBase Q) r
  change preEval Q (preBase r) = Polynomial.C (Ideal.Quotient.mk Q r) at he
  rw [he, ← RingHom.comp_apply (algebraMap PreAmbient SeedAmbient) preBase, preBase_comp] at h
  exact h
theorem seedSlice_isLocalization (Q : Ideal Ambient) :
    letI := (seedSliceMap Q).toAlgebra
    IsLocalization (denominators.map (preEval Q)) (JetSeedSection Q) := by
  let : Algebra (Polynomial (Ambient ⧸ Q)) (JetSeedSection Q) := (seedSliceMap Q).toAlgebra
  let : IsLocalization denominators SeedAmbient :=
    MvPolynomial.isLocalization (nonZeroDivisors Seeds) SeedField
  refine IsLocalization.of_surjective denominators SeedAmbient (preEval Q)
    (preEval_surjective Q) (Ideal.Quotient.mk (seedIdeal Q)) Ideal.Quotient.mk_surjective
    (seedSliceMap_comp Q).symm ?_
  rw [Ideal.mk_ker, ← preIdeal_eq_ker, preIdeal_map]
private theorem preIdeal_comap (Q : Ideal Ambient) : (preIdeal Q).comap preBase = Q := by
  ext r
  rw [Ideal.mem_comap, preIdeal_eq_ker, RingHom.mem_ker]
  have h := DFunLike.congr_fun (preEval_preBase Q) r
  change preEval Q (preBase r) = quotientConstant Q r at h
  rw [h]
  simp [quotientConstant, Ideal.Quotient.eq_zero_iff_mem]
theorem proof : K1_14_2_2_7_2.c5 := by
  intro Q hQ hproper
  let : Q.IsPrime := hQ
  let : IsLocalization denominators SeedAmbient :=
    MvPolynomial.isLocalization (nonZeroDivisors Seeds) SeedField
  have hprime : (preIdeal Q).IsPrime := by
    rw [preIdeal_eq_ker]
    exact RingHom.ker_isPrime (preEval Q)
  have hdisjoint := (IsLocalization.map_algebraMap_ne_top_iff_disjoint
    denominators SeedAmbient (preIdeal Q)).mp ((preIdeal_map Q).trans_ne hproper)
  have hcontract := IsLocalization.under_map_of_isPrime_disjoint
    denominators SeedAmbient hprime hdisjoint
  constructor
  · rw [← preIdeal_map Q]
    exact IsLocalization.isPrime_of_isPrime_disjoint denominators SeedAmbient _ hprime hdisjoint
  · rw [← preIdeal_map Q, ← preBase_comp, ← Ideal.comap_comap]
    exact (congrArg (Ideal.comap preBase) hcontract).trans (preIdeal_comap Q)
end
end K1_14_2_2_7_2_5
end
section
set_option autoImplicit false
namespace K1_14_2_2_7_4_4_7_2
noncomputable section
open K1_14_2_2_7_4_4_7
open IsLocalRing WithZero
open scoped Polynomial
variable {F : Type} [Field F]
local notation "Oinf" => InfinityRing F
local notation "vInf" => @RatFunc.inftyValuation F _ (Classical.decEq _)
private theorem valuation_degree {x : RatFunc F} (hx : x ≠ 0) :
    vInf x = exp x.intDegree := by
  exact @RatFunc.inftyValuation_of_nonzero F _ (Classical.decEq _) x hx
private theorem mem_maximal_ideal (a : Oinf) :
    a ∈ maximalIdeal Oinf ↔ vInf (algebraMap Oinf (RatFunc F) a) < 1 :=
  Valuation.mem_maximalIdeal_iff (RatFunc F) vInf
private def parameter : Oinf :=
  ⟨1 / RatFunc.X, by
    change vInf (1 / RatFunc.X) ≤ 1
    rw [RatFunc.inftyValuation.X_inv, WithZero.exp_le_one_iff]
    omega⟩
private theorem valuation_parameter_pow (n : ℕ) :
    vInf (algebraMap Oinf (RatFunc F) ((parameter : Oinf) ^ n)) = exp (-(n : ℤ)) := by
  rw [map_pow, map_pow]
  change vInf (1 / RatFunc.X) ^ n = _
  rw [RatFunc.inftyValuation.X_inv, ← WithZero.exp_nsmul]
  congr 1
  simp
private theorem maximal_ideal :
    maximalIdeal Oinf = Ideal.span ({parameter} : Set Oinf) := by
  have ht : vInf (algebraMap Oinf (RatFunc F) (parameter : Oinf)) = exp (-1) := by
    simpa only [pow_one, Nat.cast_one] using valuation_parameter_pow (F := F) 1
  ext a
  rw [mem_maximal_ideal, Ideal.mem_span_singleton,
    (Valuation.valuationSubring.integers vInf).dvd_iff_le, ht]
  by_cases ha : algebraMap Oinf (RatFunc F) a = 0
  · simp [ha]
  · rw [valuation_degree ha, WithZero.exp_lt_one_iff, WithZero.exp_le_exp]
    omega
private theorem principal_ideal_order (a : Oinf) (ha : a ≠ 0) :
    ∃ n : ℕ, (n : ℤ) = -(algebraMap Oinf (RatFunc F) a).intDegree ∧
      Ideal.span ({a} : Set Oinf) = maximalIdeal Oinf ^ n := by
  let x := algebraMap Oinf (RatFunc F) a
  have hv := Valuation.valuationSubring.integers vInf
  have hx : x ≠ 0 := (map_ne_zero_iff _ hv.hom_inj).mpr ha
  have hval : vInf x = exp x.intDegree := valuation_degree hx
  have hle : vInf x ≤ 1 := a.property
  rw [hval, WithZero.exp_le_one_iff] at hle
  let n := (-x.intDegree).toNat
  have hn : (n : ℤ) = -x.intDegree := Int.toNat_of_nonneg (neg_nonneg.mpr hle)
  refine ⟨n, hn, ?_⟩
  rw [maximal_ideal, Ideal.span_singleton_pow, le_antisymm_iff,
    Ideal.span_singleton_le_span_singleton, Ideal.span_singleton_le_span_singleton]
  rw [hv.dvd_iff_le, hv.dvd_iff_le,
    valuation_parameter_pow, hn, neg_neg]
  change (vInf x ≤ exp x.intDegree) ∧ (exp x.intDegree ≤ vInf x)
  simp [hval]
private theorem valuation_sub_constant {x : RatFunc F} (hx : x ≠ 0)
    (hd : x.intDegree = 0) :
    vInf (x - RatFunc.C x.num.leadingCoeff) < 1 := by
  let c := x.num.leadingCoeff
  let p := x.num - Polynomial.C c * x.denom
  let m := algebraMap F[X] (RatFunc F)
  have hcn : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr (RatFunc.num_ne_zero hx)
  have hq : m x.denom ≠ 0 := by
    exact (map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).mpr x.denom_ne_zero
  have hsub : x - RatFunc.C c = m p / m x.denom := by
    change x - RatFunc.C c = m (x.num - Polynomial.C c * x.denom) / m x.denom
    rw [map_sub, map_mul]
    change x - RatFunc.C c = (m x.num - m (Polynomial.C c) * m x.denom) / m x.denom
    simp only [m, RatFunc.algebraMap_C]
    rw [← div_sub_div_same, mul_div_cancel_right₀ _ hq, RatFunc.num_div_denom]
  change vInf (x - RatFunc.C c) < 1
  rw [hsub]
  by_cases hp : p = 0
  · simp [hp]
  have hnp : m p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).mpr hp
  have hdegrees : x.num.natDegree = x.denom.natDegree := by
    unfold RatFunc.intDegree at hd
    omega
  have hscaled : Polynomial.C c * x.denom ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr hcn) x.denom_ne_zero
  have hdegEq : x.num.degree = (Polynomial.C c * x.denom).degree := by
    rw [Polynomial.degree_eq_natDegree (RatFunc.num_ne_zero hx),
      Polynomial.degree_eq_natDegree hscaled, Polynomial.natDegree_C_mul hcn, hdegrees]
  have hdeg : p.degree < x.num.degree :=
    Polynomial.degree_sub_lt_left hdegEq (RatFunc.num_ne_zero hx)
      ((RatFunc.monic_denom x).leadingCoeff_C_mul c).symm
  have hlt : p.natDegree < x.denom.natDegree :=
    hdegrees ▸ Polynomial.natDegree_lt_natDegree hp hdeg
  rw [valuation_degree (div_ne_zero hnp hq), WithZero.exp_lt_one_iff,
    RatFunc.intDegree_div hnp hq]
  change (algebraMap F[X] (RatFunc F) p).intDegree -
    (algebraMap F[X] (RatFunc F) x.denom).intDegree < 0
  rw [RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial]
  omega
private theorem residue_surjective_constants :
    Function.Surjective (algebraMap F (ResidueField Oinf)) := by
  intro z
  obtain ⟨a, rfl⟩ := residue_surjective (R := Oinf) z
  change ∃ c : F, residue Oinf (algebraMap F Oinf c) = residue Oinf a
  have hle : vInf (algebraMap Oinf (RatFunc F) a) ≤ 1 := a.property
  rcases hle.lt_or_eq with hlt | heq
  · refine ⟨0, ?_⟩
    rw [map_zero, map_zero, eq_comm, residue_eq_zero_iff, mem_maximal_ideal]
    exact hlt
  · let x := algebraMap Oinf (RatFunc F) a
    have hx : x ≠ 0 := by
      intro h
      have hv : vInf x = 1 := heq
      simp [h] at hv
    have hd : x.intDegree = 0 := by
      have h : exp x.intDegree = 1 := (valuation_degree hx).symm.trans heq
      exact WithZero.exp_injective (h.trans (WithZero.exp_zero (M := ℤ)).symm)
    refine ⟨x.num.leadingCoeff, ?_⟩
    apply Eq.symm
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximal_ideal]
    rw [map_sub, ← IsScalarTower.algebraMap_apply F Oinf (RatFunc F), RatFunc.algebraMap_eq_C]
    exact valuation_sub_constant hx hd
private theorem colength (a : Oinf) (ha : a ≠ 0) :
    Module.Finite F (Oinf ⧸ Ideal.span {a}) ∧
      (Module.finrank F (Oinf ⧸ Ideal.span {a}) : ℤ) =
        -(algebraMap Oinf (RatFunc F) a).intDegree := by
  let _ := infinity_dvr F
  let _ : IsLocalHom (algebraMap F Oinf) := ⟨fun c hc => isUnit_iff_ne_zero.mpr
    (fun h => hc.ne_zero (by rw [h, map_zero]))⟩
  have hsurj : Function.Surjective (algebraMap (ResidueField F) (ResidueField Oinf)) := by
    intro z
    obtain ⟨c, rfl⟩ := residue_surjective_constants z
    exact ⟨residue F c, ResidueField.algebraMap_residue c⟩
  have hres : Module.length (ResidueField F) (ResidueField Oinf) = 1 :=
    (Module.length_eq_of_surjective (M := ResidueField Oinf) hsurj).trans (Module.length_eq_one _ _)
  obtain ⟨n, hn, hI⟩ := principal_ideal_order a ha
  let Q := Oinf ⧸ Ideal.span ({a} : Set Oinf)
  have hO : Module.length Oinf Q = n := by
    change Module.length Oinf (Oinf ⧸ Ideal.span ({a} : Set Oinf)) = n
    rw [hI, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
  have hF : Module.length F Q = n := by
    rw [length_restrictScalars F Oinf Q, hO, hres, mul_one]
  have hfinlen : IsFiniteLength F Q := Module.length_ne_top_iff.mp (by rw [hF]; simp)
  let _ : IsNoetherian F Q := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfinlen).1
  have hrank := congrArg ENat.toNat ((Module.length_eq_finrank F Q).symm.trans hF)
  refine ⟨inferInstance, ?_⟩
  change (Module.finrank F Q : ℤ) = _
  have hrank' : Module.finrank F Q = n := by simpa only [ENat.toNat_natCast] using hrank
  exact (congrArg (fun k : ℕ => (k : ℤ)) hrank').trans hn
theorem proof : K1_14_2_2_7_4_4_7.c2 :=
  fun _ _ a ha => colength a ha
end
end K1_14_2_2_7_4_4_7_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_7_4_4_7_1
noncomputable section
open K1_14_2_2_7_4_4 K1_14_2_2_7_4_4_7
open IsDedekindDomain IsLocalRing UniqueFactorizationMonoid
open scoped Classical
variable {F B K : Type} [Field F] [CommRing B] [IsDedekindDomain B] [Field K]
  [Algebra F B] [Algebra F K] [Algebra B K] [IsScalarTower F B K] [IsFractionRing B K]
private theorem chart_order (p : HeightOneSpectrum B) {a : B} (ha : a ≠ 0) :
    zeroOrder (chartPlace p : Place F K) (algebraMap B K a) =
      multiplicity p.asIdeal (Ideal.span {a}) := by
  change (-WithZero.log (p.valuation K (algebraMap B K a))).toNat = _
  simp only [p.valuation_of_algebraMap, p.intValuation_eq_exp_neg_multiplicity ha,
    WithZero.log_exp, neg_neg, Int.toNat_natCast]
private theorem prime_power_finrank (p : HeightOneSpectrum B) (n : ℕ) :
    Module.finrank F (B ⧸ p.asIdeal ^ n) =
      residueDegree (chartPlace p : Place F K) * n := by
  let w : Place F K := chartPlace p
  let V := w.val.valuationSubring
  let : Algebra B V := ((algebraMap B K).codRestrict V.toSubring
    (p.valuation_le_one (K := K))).toAlgebra
  let : IsScalarTower F B V := IsScalarTower.of_algebraMap_eq fun c => by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply F B K c
  let e : p.valuationSubringAtPrime K ≃ₐ[B] V :=
    { RingEquiv.subringCongr (congrArg ValuationSubring.toSubring
        (p.valuationSubringAtPrime_eq_valuationSubring (K := K))) with
      commutes' := fun _ => Subtype.ext rfl }
  let : IsLocalization p.asIdeal.primeCompl V :=
    IsLocalization.isLocalization_of_algEquiv p.asIdeal.primeCompl e
  let : IsDiscreteValuationRing V :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B p.ne_bot V
  let q := (IsLocalization.AtPrime.equivQuotMaximalIdealPow p.asIdeal V n).restrictScalars F
  have hres : (Module.length (ResidueField F) (ResidueField V)).toNat =
      Module.finrank F (ResidueField V) := by
    rw [← Module.length_eq_of_surjective (R := ResidueField F)
      (residue_surjective (R := F)), Module.length_eq_rank, Cardinal.toNat_toENat]
    rfl
  have hlen := IsLocalRing.length_restrictScalars F V (V ⧸ maximalIdeal V ^ n)
  rw [IsDiscreteValuationRing.length_quotient_pow_maximalIdeal] at hlen
  have hd := congrArg ENat.toNat hlen
  simp only [ENat.toNat_mul, ENat.toNat_natCast] at hd
  rw [hres, Module.length_eq_rank, Cardinal.toNat_toENat] at hd
  change Module.finrank F (B ⧸ p.asIdeal ^ n) = Module.finrank F (ResidueField V) * n
  rw [q.toLinearEquiv.finrank_eq, mul_comm]
  exact hd
private abbrev CutFactors (I : Ideal B) := (factors I).toFinset
private def factorPrime {I : Ideal B} (p : CutFactors I) : HeightOneSpectrum B :=
  HeightOneSpectrum.ofPrime (prime_of_factor p.val (Multiset.mem_toFinset.mp p.property))
theorem proof : K1_14_2_2_7_4_4_7.c1 := by
  classical
  intro F B K _ _ _ _ _ _ _ _ _ a ha hfin
  let I : Ideal B := Ideal.span {a}
  have hI : I ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr ha
  let n (p : CutFactors I) := (factors I).count p.val
  let e := IsDedekindDomain.quotientEquivPiFactors hI
  let eF : (B ⧸ I) ≃ₐ[F] ∀ p : CutFactors I, B ⧸ p.val ^ n p :=
    { e with
      commutes' := fun c => by
        funext p
        change e (Ideal.Quotient.mk _ (algebraMap F B c)) p =
          Ideal.Quotient.mk _ (algebraMap F B c)
        rw [IsDedekindDomain.quotientEquivPiFactors_mk] }
  let primes : CutFactors I ↪ HeightOneSpectrum B :=
    ⟨factorPrime, fun _ _ h => Subtype.ext (congrArg HeightOneSpectrum.asIdeal h)⟩
  have support (p : HeightOneSpectrum B) : p.asIdeal ∈ (factors I).toFinset ↔ a ∈ p.asIdeal := by
    rw [Multiset.mem_toFinset, factors_eq_normalizedFactors, Ideal.mem_normalizedFactors_iff hI]
    exact (and_iff_right p.isPrime).trans (Ideal.span_singleton_le_iff_mem p.asIdeal)
  refine ⟨Finset.univ.map primes, ?_, ?_⟩
  · intro p
    constructor
    · intro hp
      obtain ⟨q, _, rfl⟩ := Finset.mem_map.mp hp
      exact (support (primes q)).mp q.property
    · intro hp
      let q : CutFactors I := ⟨p.asIdeal, (support p).mpr hp⟩
      exact Finset.mem_map.mpr ⟨q, Finset.mem_univ q, HeightOneSpectrum.ext rfl⟩
  · let : Module.Finite F (B ⧸ I) := hfin
    let : Module.Finite F (∀ p : CutFactors I, B ⧸ p.val ^ n p) :=
      Module.Finite.equiv eF.toLinearEquiv
    have (p : CutFactors I) : Module.Finite F (B ⧸ p.val ^ n p) := by
      let proj : (∀ q : CutFactors I, B ⧸ q.val ^ n q) →ₗ[F] B ⧸ p.val ^ n p :=
        LinearMap.proj p
      exact Module.Finite.of_surjective proj (LinearMap.proj_surjective p)
    change Module.finrank F (B ⧸ I) = _
    rw [eF.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro p _
    have hn : zeroOrder (chartPlace (primes p) : Place F K) (algebraMap B K a) = n p := by
      rw [chart_order _ ha]
      change multiplicity (primes p).asIdeal I = (factors I).count (primes p).asIdeal
      rw [factors_eq_normalizedFactors, HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hI]
    rw [hn]
    exact prime_power_finrank (F := F) (K := K) (primes p) (n p)
end
end K1_14_2_2_7_4_4_7_1
end
section
set_option autoImplicit false
namespace K1_14_2_2_7_2_4
open K1_14_2_2_7_2 Polynomial
open scoped BigOperators IntermediateField.algebraAdjoinAdjoin nonZeroDivisors
noncomputable section
variable {k A : Type} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
private theorem trdeg_le_one [Algebra.FiniteType k A] (hdim : ringKrullDim A = 1) :
    Algebra.trdeg k (FractionRing A) ≤ 1 := by
  obtain ⟨n, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg k A
  let P := MvPolynomial (Fin n) k
  let F := FractionRing A
  let : Algebra P A := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral P A := ⟨hint⟩
  have hnP : (n : WithBot ℕ∞) ≤ ringKrullDim P := by
    simpa only [P, ringKrullDim_eq_zero_of_field, zero_add, Nat.card_fin] using
      (ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial (R := k) (Fin n))
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp hnP
  have hker : RingHom.ker (algebraMap P A) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp hg
  obtain ⟨J, hJ, hover⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
    (S := A) l.head.asIdeal (by rw [hker]; exact bot_le)
  let : J.IsPrime := hJ
  let : J.LiesOver l.head.asIdeal := ⟨hover.symm⟩
  obtain ⟨L, hL, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l J
  have hlen : (n : WithBot ℕ∞) ≤ 1 := by
    rw [← hl, ← hL, ← hdim]
    exact Order.LTSeries.length_le_krullDim L
  have hn : n ≤ 1 := by exact_mod_cast hlen
  have : IsScalarTower k P F := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply P A F, IsScalarTower.algebraMap_apply k A F]
    exact congrArg (algebraMap A F) (g.commutes c).symm
  have : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hg
  have : Algebra.IsAlgebraic A F := IsLocalization.isAlgebraic F A⁰
  have : Algebra.IsAlgebraic P F := Algebra.IsAlgebraic.trans P A F
  have hb := (IsTranscendenceBasis.mvPolynomial (Fin n) k).algebraMap_comp (A := F)
  have htr : Algebra.trdeg k F = (n : Cardinal) := by
    simpa using hb.cardinalMk_eq_trdeg.symm
  rw [htr]
  exact_mod_cast hn
private theorem finite_over_cutter [Algebra.FiniteType k A] (hdim : ringKrullDim A = 1)
    {x : FractionRing A} (hx : Transcendental k x) :
    Module.Finite (IntermediateField.adjoin k ({x} : Set (FractionRing A))) (FractionRing A) := by
  let F := FractionRing A
  let E := IntermediateField.adjoin k ({x} : Set F)
  have hx_ind : AlgebraicIndependent k (fun _ : Unit => x) :=
    (algebraicIndependent_singleton_iff ()).2 hx
  have hx_basis := hx_ind.isTranscendenceBasis_of_trdeg_le_of_finite
    (by simpa using trdeg_le_one (k := k) hdim)
  have hx_range : Set.range (fun _ : Unit => x) = {x} := Set.range_const
  have : Algebra.IsAlgebraic E F := Eq.mp
    (congrArg (fun s => Algebra.IsAlgebraic (IntermediateField.adjoin k s) F) hx_range)
    hx_basis.isAlgebraic_field
  have : Algebra.EssFiniteType A F :=
    Algebra.EssFiniteType.of_isLocalization F A⁰
  have : Algebra.EssFiniteType k F := Algebra.EssFiniteType.comp k A F
  have : Algebra.EssFiniteType E F := Algebra.EssFiniteType.of_comp k E F
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic
private theorem polynomial_relation {f : A} {ι : Type} {v : ι → A} (hf : f ≠ 0)
    (hv : LinearIndependent k (fun i => Ideal.Quotient.mk (Ideal.span {f}) (v i)))
    (s : Finset ι) (p : ι → Polynomial k)
    (h : ∑ i ∈ s, aeval f (p i) * v i = 0) :
    ∀ i ∈ s, p i = 0 := by
  classical
  intro i hi
  by_contra hpi
  have hex : ∃ d : ℕ, ∃ j ∈ s, (p j).coeff d ≠ 0 :=
    ⟨(p i).natTrailingDegree, i, hi, coeff_natTrailingDegree_ne_zero.mpr hpi⟩
  let m := Nat.find hex
  obtain ⟨j, hj, hcoeff⟩ := Nat.find_spec hex
  have hd : ∀ l ∈ s, (Polynomial.X : Polynomial k) ^ m ∣ p l := by
    intro l hl
    apply X_pow_dvd_iff.mpr
    intro d hd
    by_contra hne
    exact Nat.find_min hex hd ⟨l, hl, hne⟩
  choose! q hq using hd
  have hmul : f ^ m * (∑ l ∈ s, aeval f (q l) * v l) = 0 := by
    rw [← h, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    simp [hq l hl, mul_assoc]
  have hqsum := (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero _ hf)
  let π := Ideal.Quotient.mkₐ k (Ideal.span ({f} : Set A))
  have hπf : π f = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)
  have hred := congrArg π hqsum
  simp only [map_sum, map_mul, map_zero, ← aeval_algHom_apply, hπf,
    ← coeff_zero_eq_aeval_zero', ← Algebra.smul_def] at hred
  have hzero : (q j).coeff 0 = 0 := (linearIndependent_iff'.mp hv) s _ hred j hj
  apply hcoeff
  change (p j).coeff m = 0
  rw [hq j hj, coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self, hzero]
set_option backward.isDefEq.respectTransparency false in
private theorem independent_lifts {f : A} {ι : Type} {v : ι → A} (hf : f ≠ 0)
    (hv : LinearIndependent k (fun i => Ideal.Quotient.mk (Ideal.span {f}) (v i))) :
    LinearIndependent (IntermediateField.adjoin k {algebraMap A (FractionRing A) f})
      (fun i => algebraMap A (FractionRing A) (v i)) := by
  let F := FractionRing A
  let x : F := algebraMap A F f
  let B := Algebra.adjoin k ({x} : Set F)
  let E := IntermediateField.adjoin k ({x} : Set F)
  apply (LinearIndependent.iff_fractionRing B E).mp
  rw [linearIndependent_iff']
  intro s c hc i hi
  have hcoef (j : ι) : ∃ p : Polynomial k, aeval x p = (c j : F) :=
    Algebra.adjoin_eq_exists_aeval k x (c j)
  choose p hp using hcoef
  let embed := IsScalarTower.toAlgHom k A F
  have h : ∑ j ∈ s, aeval f (p j) * v j = 0 := by
    apply (IsFractionRing.injective A F)
    change embed (∑ j ∈ s, aeval f (p j) * v j) = embed 0
    simp only [map_sum, map_mul, map_zero, ← aeval_algHom_apply]
    change (∑ j ∈ s, aeval x (p j) * algebraMap A F (v j)) = 0
    simp only [Algebra.smul_def] at hc
    change (∑ j ∈ s, (c j : F) * algebraMap A F (v j)) = 0 at hc
    simpa only [hp] using hc
  apply Subtype.ext
  change (c i : F) = 0
  rw [← hp i, polynomial_relation hf hv s p h i hi, map_zero]
theorem proof : K1_14_2_2_7_2.c4 := by
  classical
  intro k A _ _ _ _ _ hdim f hf
  let F := FractionRing A
  let x : F := algebraMap A F f
  let Q := PrincipalCut f
  by_cases hx : Transcendental k x
  · let E := IntermediateField.adjoin k ({x} : Set F)
    have : Module.Finite E F := finite_over_cutter hdim hx
    let b := Module.Basis.ofVectorSpace k Q
    choose v hv using fun i => Ideal.Quotient.mk_surjective (b i)
    have hli : LinearIndependent k (fun i => Ideal.Quotient.mk (Ideal.span {f}) (v i)) := by
      simpa only [hv] using b.linearIndependent
    have hLift : LinearIndependent E (fun i => algebraMap A F (v i)) := independent_lifts hf hli
    let : Finite (Module.Basis.ofVectorSpaceIndex k Q) := hLift.finite
    let : Fintype (Module.Basis.ofVectorSpaceIndex k Q) := Fintype.ofFinite _
    change Module.finrank k Q ≤ functionDegree k F x
    rw [Module.finrank_eq_card_basis b, functionDegree, ite_eq_left hx]
    exact hLift.fintype_card_le_finrank
  · have hfa : IsAlgebraic k f := (isAlgebraic_algebraMap_iff (R := k)
      (IsFractionRing.injective A F)).mp (not_not.mp hx)
    have hu : IsUnit f := IsArtinianRing.isUnit_of_isIntegral_of_nonZeroDivisor
      hfa.isIntegral (mem_nonZeroDivisors_of_ne_zero hf)
    have : Subsingleton Q :=
      Ideal.Quotient.subsingleton_iff.mpr (Ideal.span_singleton_eq_top.mpr hu)
    change Module.finrank k Q ≤ coordinateDegree k A f
    rw [Module.finrank_zero_of_subsingleton]
    exact Nat.zero_le _
end
end K1_14_2_2_7_2_4
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace K1_14_2_2_7_2_2_2
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 MvPolynomial
open scoped Polynomial RatFunc nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial Polynomial.algebra
private abbrev SeedPolynomials := MvPolynomial Unit Seeds
private abbrev LocalizedPolynomials := MvPolynomial Unit SeedField
private abbrev OrdinateField := RatFunc SeedField
private abbrev Parameters := MvPolynomial (Fin 4) FX
private def parameterIndex : Unit ⊕ Fin 2 → Fin 4 :=
  Sum.elim (fun _ => 3) ![0, 2]
private theorem parameterIndex_injective : Function.Injective parameterIndex := by decide
private def parameterPolynomials : SeedPolynomials →+* Parameters :=
  (rename parameterIndex).toRingHom.comp (sumRingEquiv FX Unit (Fin 2)).symm.toRingHom
private theorem parameterPolynomials_injective : Function.Injective parameterPolynomials :=
  (rename_injective _ parameterIndex_injective).comp (sumRingEquiv FX Unit (Fin 2)).symm.injective
private local instance localizedToOrdinate : Algebra LocalizedPolynomials OrdinateField :=
  Algebra.compHom _ (uniqueAlgEquiv SeedField Unit).toRingEquiv.toRingHom
private local instance localizedFraction : IsFractionRing LocalizedPolynomials OrdinateField :=
  IsFractionRing.of_ringEquiv_left (uniqueAlgEquiv SeedField Unit).toRingEquiv fun _ => rfl
private abbrev denominators : Submonoid SeedPolynomials := Seeds⁰.map MvPolynomial.C
private local instance : IsLocalization denominators LocalizedPolynomials :=
  MvPolynomial.isLocalization Seeds⁰ SeedField
private def parameterToSection : SeedPolynomials →+* SectionField :=
  (algebraMap Parameters SectionField).comp parameterPolynomials
private theorem parameterToSection_injective : Function.Injective parameterToSection := by
  change Function.Injective (fun p => algebraMap Parameters SectionField (parameterPolynomials p))
  exact (IsFractionRing.injective Parameters SectionField).comp parameterPolynomials_injective
private theorem parameterUnits (y : denominators) : IsUnit (parameterToSection y) := by
  obtain ⟨c, hc, he⟩ := y.property
  refine isUnit_iff_ne_zero.mpr fun hz => ?_
  have hzero : (y : SeedPolynomials) = 0 :=
    parameterToSection_injective (hz.trans (map_zero parameterToSection).symm)
  exact (map_ne_zero_iff MvPolynomial.C (C_injective Unit Seeds)).mpr
    (mem_nonZeroDivisors_iff_ne_zero.mp hc) (he.trans hzero)
private def localizedToSection : LocalizedPolynomials →+* SectionField :=
  IsLocalization.lift (M := denominators) (g := parameterToSection) parameterUnits
private theorem localizedToSection_injective : Function.Injective localizedToSection := by
  apply (IsLocalization.lift_injective_iff (S := LocalizedPolynomials) parameterUnits).mpr
  intro p q
  have hi : Function.Injective (algebraMap SeedPolynomials LocalizedPolynomials) :=
    MvPolynomial.map_injective _ (IsFractionRing.injective Seeds SeedField)
  rw [hi.eq_iff, parameterToSection_injective.eq_iff]
private abbrev intoOrdinate (p : SeedPolynomials) : OrdinateField :=
  algebraMap LocalizedPolynomials OrdinateField (algebraMap SeedPolynomials LocalizedPolynomials p)
private theorem seedPolynomials_C (p : Seeds) :
    intoOrdinate (C p) = RatFunc.C (algebraMap Seeds SeedField p) := by
  change algebraMap (Polynomial SeedField) OrdinateField
    (uniqueAlgEquiv SeedField Unit (MvPolynomial.map (algebraMap Seeds SeedField) (C p))) = _
  simp [uniqueAlgEquiv_apply, RatFunc.algebraMap_C]
private theorem seedPolynomials_X : intoOrdinate (MvPolynomial.X ()) = RatFunc.X := by
  change algebraMap (Polynomial SeedField) OrdinateField
    (uniqueAlgEquiv SeedField Unit (MvPolynomial.map (algebraMap Seeds SeedField) (MvPolynomial.X ()))) = _
  simp [uniqueAlgEquiv_apply, RatFunc.algebraMap_X]
def ordinateCoefficients : OrdinateField →+* SectionField :=
  IsFractionRing.lift (K := OrdinateField)
    (g := localizedToSection) localizedToSection_injective
private theorem ordinateCoefficients_polynomial (p : SeedPolynomials) :
    ordinateCoefficients (intoOrdinate p) = algebraMap Parameters SectionField (parameterPolynomials p) := by
  change IsFractionRing.lift localizedToSection_injective
    (algebraMap LocalizedPolynomials OrdinateField (algebraMap SeedPolynomials LocalizedPolynomials p)) =
      parameterToSection p
  rw [IsFractionRing.lift_algebraMap]
  exact IsLocalization.lift_eq parameterUnits p
def seedCoefficients : SeedField →+* SectionField :=
  ordinateCoefficients.comp RatFunc.C
theorem seedCoefficients_ground (c : FX) :
    seedCoefficients (algebraMap FX SeedField c) = algebraMap FX SectionField c := by
  change ordinateCoefficients (RatFunc.C (algebraMap Seeds SeedField (C c))) =
    algebraMap Parameters SectionField (C c)
  rw [← seedPolynomials_C, ordinateCoefficients_polynomial]
  simp [parameterPolynomials]
theorem seedCoefficients_generic (i : Fin 2) :
    seedCoefficients (generic i) = sliceParameter (![0, 2] i) := by
  change ordinateCoefficients (RatFunc.C (algebraMap Seeds SeedField (MvPolynomial.X i))) = _
  rw [← seedPolynomials_C, ordinateCoefficients_polynomial]
  simp [parameterPolynomials, parameterIndex, sliceParameter]
theorem ordinateCoefficients_X : ordinateCoefficients RatFunc.X = sliceParameter 3 := by
  rw [← seedPolynomials_X, ordinateCoefficients_polynomial]
  simp [parameterPolynomials, parameterIndex, sliceParameter]
end
end K1_14_2_2_7_2_2_2
end
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace K1_14_2_2_7_2_2_2
noncomputable section
open scoped Polynomial TensorProduct
open Algebra.TensorProduct
variable {k F σ : Type} [Field k] [Field F] [Algebra k F]
abbrev cutIdeal (J : Ideal (MvPolynomial σ k)) (j : σ) (u : F) :
    Ideal (MvPolynomial σ F) :=
  J.map (MvPolynomial.map (algebraMap k F)) ⊔ Ideal.span {MvPolynomial.X j - MvPolynomial.C u}
def fibreEquiv {P A : Type} [CommRing P] [CommRing A] [Algebra k P]
    [Algebra k A] [Algebra P A] [Algebra P F] [IsScalarTower k P A] [IsScalarTower k P F]
    (J : Ideal (MvPolynomial σ k)) (e : (MvPolynomial σ k ⧸ J) ≃ₐ[k] A)
    (j : σ) (t : P) (u : F)
    (hext : ∀ {B : Type} [CommRing B] [Algebra k B] {f g : P →ₐ[k] B}, f t = g t → f = g)
    (hq : algebraMap P A t = e (Ideal.Quotient.mk J (MvPolynomial.X j)))
    (hu : algebraMap P F t = u) :
    F ⊗[P] A ≃ₐ[F] (MvPolynomial σ F ⧸ cutIdeal J j u) := by
  let q : MvPolynomial σ k →ₐ[k] A := e.toAlgHom.comp (Ideal.Quotient.mkₐ k J)
  let T := F ⊗[P] A
  let S := MvPolynomial σ F ⧸ cutIdeal J j u
  let : IsScalarTower k F T := inferInstance
  let : IsScalarTower k F S := inferInstance
  letI algebraPS : Algebra P S := Algebra.compHom S (algebraMap P F)
  let : SMul P S := algebraPS.toSMul
  let : IsScalarTower P F S := IsScalarTower.of_algebraMap_eq' (R := P) (S := F) (A := S) rfl
  let : IsScalarTower k P T := IsScalarTower.to₁₂₄ k P F T
  let right : A →ₐ[P] T := includeRight
  let rightk : A →ₐ[k] T := right.restrictScalars k
  let m : MvPolynomial σ F →ₐ[F] S := Ideal.Quotient.mkₐ F _
  let ext : MvPolynomial σ k →ₐ[k] MvPolynomial σ F :=
    MvPolynomial.mapAlgHom (Algebra.ofId k F)
  let eval : MvPolynomial σ F →ₐ[F] T :=
    MvPolynomial.aeval fun i => right (q (MvPolynomial.X i))
  have heval : (eval.restrictScalars k).comp ext = rightk.comp q := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [eval, ext, rightk]
  have hxt : right (q (MvPolynomial.X j)) = algebraMap F T u := by
    change right (e (Ideal.Quotient.mk J (MvPolynomial.X j))) = _
    rw [← hq, right.commutes, IsScalarTower.algebraMap_apply P F T, hu]
  have hkill : cutIdeal J j u ≤ RingHom.ker eval.toRingHom := by
    apply sup_le
    · rw [Ideal.map_le_iff_le_comap]
      intro p hp
      change eval (ext p) = 0
      have h := AlgHom.congr_fun heval p
      change eval (ext p) = right (q p) at h
      have hp₀ : Ideal.Quotient.mk J p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
      rw [h, show q p = e (Ideal.Quotient.mk J p) from rfl, hp₀, map_zero, map_zero]
    · rw [Ideal.span_le]
      intro p hp
      rcases Set.mem_singleton_iff.mp hp with rfl
      change eval (MvPolynomial.X j - MvPolynomial.C u) = 0
      rw [map_sub, sub_eq_zero, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
      exact hxt
  let forward : S →ₐ[F] T := Ideal.Quotient.liftₐ _ eval fun p hp => hkill hp
  let qext : MvPolynomial σ k →ₐ[k] S := (m.restrictScalars k).comp ext
  let fromQuotient := Ideal.Quotient.liftₐ J qext fun p hp => by
    have hle : J.map (MvPolynomial.map (algebraMap k F)) ≤ cutIdeal J j u := le_sup_left
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.mem_map_of_mem _ hp))
  let fromA : A →ₐ[k] S := fromQuotient.comp e.symm.toAlgHom
  have hfromA (p : MvPolynomial σ k) : fromA (q p) = qext p := by
    change fromQuotient (e.symm (e (Ideal.Quotient.mk J p))) = qext p
    rw [e.symm_apply_apply]
    rfl
  have hxs : fromA (q (MvPolynomial.X j)) = algebraMap F S u := by
    rw [hfromA]
    change m (ext (MvPolynomial.X j)) = m (MvPolynomial.C u)
    rw [show ext (MvPolynomial.X j) = MvPolynomial.X j by simp [ext],
      ← sub_eq_zero, ← map_sub]
    have hle : Ideal.span {MvPolynomial.X j - MvPolynomial.C u} ≤ cutIdeal J j u := le_sup_right
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (by simp)))
  let fromAP : A →ₐ[P] S :=
    { fromA.toRingHom with
      commutes' := by
        have h : fromA.comp (IsScalarTower.toAlgHom k P A) =
            (IsScalarTower.toAlgHom k F S).comp (IsScalarTower.toAlgHom k P F) := by
          apply hext
          change fromA (algebraMap P A t) = algebraMap F S (algebraMap P F t)
          rw [hq, hu]
          exact hxs
        exact AlgHom.congr_fun h }
  let backward : T →ₐ[F] S := AlgHom.liftEquiv P F A S fromAP
  have hbackward (a : A) : backward (right a) = fromA a := by
    change backward (1 ⊗ₜ[P] a) = fromA a
    exact (AlgHom.liftEquiv_tmul (R := P) fromAP (1 : F) a).trans (one_smul F _)
  have hforward (p : MvPolynomial σ k) : forward (qext p) = right (q p) :=
    AlgHom.congr_fun heval p
  have hST : (forward.comp backward : T →ₐ[F] T) = AlgHom.id F T := by
    apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    have hqsurj : Function.Surjective q := e.surjective.comp Ideal.Quotient.mk_surjective
    rintro a
    obtain ⟨p, rfl⟩ := hqsurj a
    change forward (backward (right (q p))) = right (q p)
    rw [hbackward, hfromA]
    exact hforward p
  have hTS : (backward.comp forward : S →ₐ[F] S) = AlgHom.id F S := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    change backward (forward (m (MvPolynomial.X i))) = m (MvPolynomial.X i)
    rw [show m (MvPolynomial.X i) = qext (MvPolynomial.X i) by simp [qext, ext],
      hforward, hbackward, hfromA]
  exact (AlgEquiv.ofAlgHom forward backward hST hTS).symm
end
end K1_14_2_2_7_2_2_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_7_4_4_6
theorem proof : K1_14_2_2_7_4_4.c6 := by
  intro F A _ _ _ _ _ hfinite hdedekind a ha
  let K := FractionRing A
  let B := integralClosure A K
  let : Module.Finite A B := hfinite
  let : IsDedekindDomain B := hdedekind
  let : Algebra.FiniteType F B := Algebra.FiniteType.trans ‹Algebra.FiniteType F A› inferInstance
  let : IsFractionRing B K := integralClosure.isFractionRing_of_finite_extension K K
  obtain ⟨hf, heq⟩ := compare_normalization (F := F) a ha
  have hb : algebraMap A B a ≠ 0 := by
    intro h
    have hK : algebraMap A K a = 0 := congrArg Subtype.val h
    exact ha (IsFractionRing.injective A K (hK.trans (map_zero _).symm))
  obtain ⟨S, hS⟩ := normalized_cut (F := F) (K := K) (algebraMap A B a) hb
  rw [← IsScalarTower.algebraMap_apply A B K] at hS
  exact ⟨hf, S, (heq.trans hS).le⟩
end K1_14_2_2_7_4_4_6
end
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace K1_14_2_2_7_2_2_2
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_7_2 K1_14_2_2_7_2_2
open scoped Polynomial TensorProduct
attribute [local instance] Polynomial.algebra
private theorem flatIdeal (I : Ideal Ambient) :
    let : Algebra SeedField SectionField := seedCoefficients.toAlgebra
    cutIdeal (seedIdeal I) 2 (sliceParameter 3) =
      I.map sectionBase ⊔
        Ideal.span {sectionSeedLine, MvPolynomial.X 2 - MvPolynomial.C (sliceParameter 3)} := by
  let : Algebra SeedField SectionField := seedCoefficients.toAlgebra
  change (seedIdeal I).map (MvPolynomial.map seedCoefficients) ⊔ _ = _
  have hbase : (MvPolynomial.map seedCoefficients).comp seedBase = sectionBase := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [seedBase, sectionBase, seedCoefficients_ground]
    · intro j
      simp [seedBase, sectionBase]
  have hline : MvPolynomial.map seedCoefficients (seedLine (n := 4) 0 1) = sectionSeedLine := by
    have h₀ : seedCoefficients (generic 0) = sliceParameter 0 := seedCoefficients_generic 0
    have h₁ : seedCoefficients (generic 1) = sliceParameter 2 := seedCoefficients_generic 1
    simp [seedLine, sectionSeedLine, h₀, h₁]
  rw [seedIdeal, Ideal.map_sup, Ideal.map_map, hbase, Ideal.map_span, Set.image_singleton,
    hline, sup_assoc, ← Ideal.span_insert]
private theorem fibreFinrank {k F A σ : Type} [Field k] [Field F] [CommRing A]
    [Algebra k A] [Algebra k F] [Algebra (RatFunc k) F]
    (J : Ideal (MvPolynomial σ k)) (q : (MvPolynomial σ k ⧸ J) ≃ₐ[k] A) (j : σ) (u : F)
    (hC : ∀ c : k, algebraMap k F c = algebraMap (RatFunc k) F (RatFunc.C c))
    (hX : algebraMap (RatFunc k) F RatFunc.X = u) :
    Module.finrank (RatFunc (RatFunc k))
        (RationalBaseChange (RatFunc k) (GenericFibre k A (q (Ideal.Quotient.mk J (MvPolynomial.X j))))) =
      Module.finrank F (MvPolynomial σ F ⧸ cutIdeal J j u) := by
  let P := Polynomial k
  let U := RatFunc k
  let x := q (Ideal.Quotient.mk J (MvPolynomial.X j))
  let : Algebra P A := (Polynomial.aeval x : P →ₐ[k] A).toRingHom.toAlgebra
  let : Algebra P F := Algebra.compHom F (algebraMap P U)
  let : SMul P A := (inferInstance : Algebra P A).toSMul
  let : SMul P F := (inferInstance : Algebra P F).toSMul
  let : IsScalarTower P U F :=
    IsScalarTower.of_algebraMap_eq' (R := P) (S := U) (A := F) rfl
  let : IsScalarTower k P A := IsScalarTower.of_algebraMap_eq (R := k) (S := P) (A := A)
    fun c => (Polynomial.aeval_C x c).symm
  let : IsScalarTower k P F := IsScalarTower.of_algebraMap_eq (R := k) (S := P) (A := F) <| by
    intro c
    change algebraMap k F c = algebraMap U F (algebraMap P U (Polynomial.C c))
    rw [RatFunc.algebraMap_C, hC]
  have hparam : algebraMap P F Polynomial.X = u := by
    change algebraMap U F (algebraMap P U Polynomial.X) = u
    rw [RatFunc.algebraMap_X, hX]
  let G := GenericFibre k A x
  let e : F ⊗[U] G ≃ₐ[F] F ⊗[P] A :=
    Algebra.TensorProduct.cancelBaseChange P U F F A
  let f : F ⊗[P] A ≃ₐ[F] (MvPolynomial σ F ⧸ cutIdeal J j u) :=
    fibreEquiv J q j (Polynomial.X : P) u
      (fun h => Polynomial.algHom_ext h) (Polynomial.aeval_X x) hparam
  change Module.finrank (RatFunc U) (RationalBaseChange U G) =
    Module.finrank F (MvPolynomial σ F ⧸ cutIdeal J j u)
  calc
    _ = Module.finrank U G := Module.finrank_baseChange
    _ = Module.finrank F (F ⊗[U] G) := Module.finrank_baseChange.symm
    _ = Module.finrank F (MvPolynomial σ F ⧸ cutIdeal J j u) :=
      (e.trans f).toLinearEquiv.finrank_eq
theorem proof : K1_14_2_2_7_2_2.c2 := by
  intro I
  let : Algebra SeedField SectionField := seedCoefficients.toAlgebra
  let : Algebra (RatFunc SeedField) SectionField := ordinateCoefficients.toAlgebra
  have h := fibreFinrank (F := SectionField) (seedIdeal I) (AlgEquiv.refl (R := SeedField) (A₁ := JetSeedSection I))
    2 (sliceParameter 3) (fun _ => rfl) ordinateCoefficients_X
  exact h.trans (Ideal.quotientEquivAlgOfEq SectionField (flatIdeal I)).toLinearEquiv.finrank_eq
end
end K1_14_2_2_7_2_2_2
end
section
namespace K1_14_2_2_3
noncomputable section
open K1_14 K1_14_2
def seedPresentation : Ambient ≃+* MvPolynomial (Fin 2) Seeds :=
  ((MvPolynomial.renameEquiv FX (finSumFinEquiv (m := 2) (n := 2)).symm).trans
    (MvPolynomial.sumAlgEquiv FX (Fin 2) (Fin 2))).toRingEquiv
def jetInclude : Seeds →+* Ambient :=
  (MvPolynomial.rename (Fin.natAdd 2 : Fin 2 → Fin 4)).toRingHom
def specializeJets {A : Type*} [CommRing A] (a : Seeds →+* A) :
    Ambient →+* MvPolynomial (Fin 2) A :=
  (MvPolynomial.map a).comp seedPresentation.toRingHom
abbrev JetImageRing (I : Ideal Ambient) := CoordinateRing (I.comap jetInclude)
abbrev JetImageField (I : Ideal Ambient) := FractionRing (JetImageRing I)
def jetImageMap (I : Ideal Ambient) : Seeds →+* JetImageField I :=
  (algebraMap (JetImageRing I) (JetImageField I)).comp
    (Ideal.Quotient.mk (I.comap jetInclude))
def imageFibreMap (I : Ideal Ambient) :
    Ambient →+* MvPolynomial (Fin 2) (JetImageField I) :=
  specializeJets (jetImageMap I)
def partialWord {A : Type*} [CommRing A] (f : MvPolynomial (Fin 2) A) :
    List (Fin 2) → MvPolynomial (Fin 2) A
  | [] => f
  | i :: t => MvPolynomial.pderiv i (partialWord f t)
def fibreContact {A : Type*} [CommRing A] (J : Ideal (MvPolynomial (Fin 2) A))
    (f : MvPolynomial (Fin 2) A) (r : ℕ) : Prop :=
  ∀ t : List (Fin 2), t.length ≤ r → partialWord f t ∈ J
end
end K1_14_2_2_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace K1_14_2_2_3
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 Polynomial
open MvPolynomial (pderiv)
@[simp] theorem seedPresentation_C (c : FX) :
    seedPresentation (MvPolynomial.C c) = MvPolynomial.C (MvPolynomial.C c) := by
  simp [seedPresentation]
@[simp] theorem seedPresentation_seed (i : Fin 2) :
    seedPresentation (MvPolynomial.X (Fin.castAdd 2 i)) = MvPolynomial.X i := by
  change MvPolynomial.sumAlgEquiv FX (Fin 2) (Fin 2)
    (MvPolynomial.renameEquiv FX (finSumFinEquiv (m := 2) (n := 2)).symm
      (MvPolynomial.X (Fin.castAdd 2 i))) = _
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
    finSumFinEquiv_symm_apply_castAdd, MvPolynomial.sumAlgEquiv_X_inl]
@[simp] theorem seedPresentation_jet (i : Fin 2) :
    seedPresentation (MvPolynomial.X (Fin.natAdd 2 i)) = MvPolynomial.C (MvPolynomial.X i) := by
  change MvPolynomial.sumAlgEquiv FX (Fin 2) (Fin 2)
    (MvPolynomial.renameEquiv FX (finSumFinEquiv (m := 2) (n := 2)).symm
      (MvPolynomial.X (Fin.natAdd 2 i))) = _
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X,
    finSumFinEquiv_symm_apply_natAdd, MvPolynomial.sumAlgEquiv_X_inr]
@[simp] theorem specialize_C {A : Type*} [CommRing A] (a : Seeds →+* A) (c : FX) :
    specializeJets a (MvPolynomial.C c) = MvPolynomial.C (a (MvPolynomial.C c)) := by
  simp [specializeJets]
@[simp] theorem specialize_seed_var {A : Type*} [CommRing A] (a : Seeds →+* A) (i : Fin 2) :
    specializeJets a (MvPolynomial.X (Fin.castAdd 2 i)) = MvPolynomial.X i := by
  change MvPolynomial.map a (seedPresentation (MvPolynomial.X (Fin.castAdd 2 i))) = _
  rw [seedPresentation_seed, MvPolynomial.map_X]
@[simp] theorem specialize_jet_var {A : Type*} [CommRing A] (a : Seeds →+* A) (i : Fin 2) :
    specializeJets a (MvPolynomial.X (Fin.natAdd 2 i)) = MvPolynomial.C (a (MvPolynomial.X i)) := by
  change MvPolynomial.map a (seedPresentation (MvPolynomial.X (Fin.natAdd 2 i))) = _
  rw [seedPresentation_jet, MvPolynomial.map_C]
theorem mapGenericJets_eq : mapGenericJets = specializeJets (algebraMap Seeds SeedField) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [specialize_C, mapGenericJets, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    exact congrArg MvPolynomial.C (IsScalarTower.algebraMap_apply FX Seeds SeedField c)
  · intro i
    obtain ⟨i | i, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective i
    · rw [finSumFinEquiv_apply_left, specialize_seed_var]
      fin_cases i <;> simp [mapGenericJets]
    · rw [finSumFinEquiv_apply_right, specialize_jet_var]
      fin_cases i <;> simp [mapGenericJets, generic]
private theorem seed_coeff_zero (i : Fin 2) (c : Seeds) :
    (translateSeed i c).coeff 0 = c := by
  have h : (constantCoeff : Polynomial Seeds →+* Seeds).comp (translateSeed i) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [translateSeed]
    · intro j
      by_cases hji : j = i <;> simp [translateSeed, hji]
  exact DFunLike.congr_fun h c
private theorem seed_coeff_one (i : Fin 2) (c : Seeds) :
    (translateSeed i c).coeff 1 = pderiv i c := by
  classical
  induction c using MvPolynomial.induction_on with
  | C a => simp [translateSeed]
  | add a b ha hb => simp [map_add, ha, hb]
  | mul_X a j ha =>
    have hx : translateSeed i (MvPolynomial.X j) =
        C (MvPolynomial.X j : Seeds) + if j = i then Polynomial.X else 0 := by
      simp [translateSeed]
    rw [map_mul, hx, MvPolynomial.pderiv_mul]
    by_cases hji : j = i
    · subst j
      have hcoef : (translateSeed i a * Polynomial.X).coeff 1 = (translateSeed i a).coeff 0 :=
        coeff_mul_X (translateSeed i a) 0
      rw [ite_eq_left rfl, mul_add, coeff_add, coeff_mul_C, hcoef,
        ha, seed_coeff_zero, MvPolynomial.pderiv_X_self, mul_one]
    · rw [ite_eq_right hji, add_zero, coeff_mul_C, ha, MvPolynomial.pderiv_X_of_ne hji,
        mul_zero, add_zero]
private theorem specialize_seed {A : Type*} [CommRing A] (a : Seeds →+* A) :
    (specializeJets a).comp (rootIncl.comp rootSeeds) =
      MvPolynomial.map (a.comp MvPolynomial.C) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [rootIncl, rootSeeds, specializeJets]
  · intro i
    have hidx : Fin.castLE (by decide : 3 ≤ 4) (Fin.castLE (by decide : 2 ≤ 3) i) =
        Fin.castAdd 2 i := rfl
    simp only [RingHom.comp_apply, rootIncl, rootSeeds, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, MvPolynomial.rename_X, MvPolynomial.map_X]
    rw [hidx, specialize_seed_var]
private theorem pderiv_eval_at_const {A R : Type*} [CommSemiring A] [Semiring R]
    (i : Fin 2) (g : R →+* MvPolynomial (Fin 2) A) (x : A) (f : R[X]) :
    pderiv i (f.eval₂ g (MvPolynomial.C x)) =
      f.sum (fun j c => pderiv i (g c) * (MvPolynomial.C x) ^ j) := by
  simp [eval₂_eq_sum, Polynomial.sum, map_sum, mul_comm]
theorem specialize_seedHasse_one {A : Type*} [CommRing A] (a : Seeds →+* A)
    (i : Fin 2) (P : Jet) :
    specializeJets a (toJet (seedHasse i 1 P)) =
      pderiv i (specializeJets a (toJet P)) := by
  let t := specializeJets a
  let e : Seeds →+* MvPolynomial (Fin 2) A := MvPolynomial.map (a.comp MvPolynomial.C)
  let y : A := a (MvPolynomial.X 0)
  let v : A := a (MvPolynomial.X 1)
  let b : Equation →+* MvPolynomial (Fin 2) A := eval₂RingHom e (MvPolynomial.C y)
  have hroot : t.comp (rootIncl.comp toRoot) = b := by
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, toRoot, b, coe_eval₂RingHom, eval₂_C]
      exact RingHom.congr_fun (specialize_seed a) c
    · simp only [RingHom.comp_apply, toRoot, b, coe_eval₂RingHom, eval₂_X, rootIncl,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, MvPolynomial.rename_X]
      rw [show Fin.castLE (by decide : 3 ≤ 4) (2 : Fin 3) = Fin.natAdd 2 (0 : Fin 2) from rfl]
      exact specialize_jet_var a 0
  have hjetHom : t.comp toJet = eval₂RingHom b (MvPolynomial.C v) := by
    apply Polynomial.ringHom_ext
    · intro Q
      simpa only [RingHom.comp_apply, toJet, coe_eval₂RingHom, eval₂_C] using
        RingHom.congr_fun hroot Q
    · simp only [RingHom.comp_apply, toJet, coe_eval₂RingHom, eval₂_X]
      rw [show (3 : Fin 4) = Fin.natAdd 2 (1 : Fin 2) from rfl]
      exact specialize_jet_var a 1
  have hjet (Q : Jet) : t (toJet Q) =
      Q.eval₂ b (MvPolynomial.C v) :=
    RingHom.congr_fun hjetHom Q
  have hInner (Q : Equation) :
      (Q.sum fun k c => monomial k ((translateSeed i c).coeff 1)).eval₂
        e (MvPolynomial.C y) = pderiv i (Q.eval₂ e (MvPolynomial.C y)) := by
    refine Eq.trans ?_ (pderiv_eval_at_const i e y Q).symm
    rw [eval₂_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [eval₂_monomial, seed_coeff_one, e, MvPolynomial.pderiv_map]
  calc
    t (toJet (seedHasse i 1 P)) = (seedHasse i 1 P).eval₂
        b (MvPolynomial.C v) := hjet _
    _ = P.sum (fun j Q => pderiv i (b Q) * (MvPolynomial.C v)^j) := by
      rw [seedHasse, eval₂_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [eval₂_monomial, b, coe_eval₂RingHom, hInner]
    _ = pderiv i (P.eval₂ b (MvPolynomial.C v)) := by
      simp [eval₂_eq_sum, Polynomial.sum, map_sum, mul_comm]
    _ = pderiv i (t (toJet P)) := congrArg (pderiv i) (hjet P).symm
private def shiftedWord (P : Jet) : List (Fin 2) → Jet
  | [] => P
  | i :: t => seedHasse i 1 (shiftedWord P t)
private theorem shift_word {h : ℕ} {rows : Banks} {s : Shape}
    (hshift : K1_14_3.SeedShift h rows s) {W : ℕ} {P : Jet} (hP : P ∈ rows s W)
    (t : List (Fin 2)) :
    shiftedWord P t ∈ rows s (W + 2*h*t.length) := by
  induction t with
  | nil => simpa [shiftedWord] using hP
  | cons i t ih =>
    have hs := hshift _ _ ih i 1
    simpa [shiftedWord, Nat.mul_succ, Nat.add_assoc] using hs
private theorem specialize_shiftedWord {A : Type*} [CommRing A] (a : Seeds →+* A)
    (P : Jet) (t : List (Fin 2)) :
    specializeJets a (toJet (shiftedWord P t)) =
      partialWord (specializeJets a (toJet P)) t := by
  induction t with
  | nil => rfl
  | cons i t ih => simp only [shiftedWord, partialWord, specialize_seedHasse_one, ih]
theorem contact_of_shift {A : Type*} [CommRing A] (a : Seeds →+* A)
    {h : ℕ} {rows : Banks} {s : Shape} {I : Ideal Ambient}
    (hn : ∀ W W', W ≤ W' → rows s W ≤ rows s W')
    (hshift : K1_14_3.SeedShift h rows s) (hv : bankVanishes rows s I)
    {W r : ℕ} {P : Jet} (hcut : W + 2*h*r ≤ fullCutoff s) (hP : P ∈ rows s W) :
    fibreContact (I.map (specializeJets a)) (specializeJets a (toJet P)) r := by
  intro t ht
  rw [← specialize_shiftedWord]
  apply Ideal.mem_map_of_mem
  exact hv _ (hn _ _ ((Nat.add_le_add_left (Nat.mul_le_mul_left _ ht) _).trans hcut)
    (shift_word hshift hP t))
end
end K1_14_2_2_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace K1_14_2_2_3
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 Polynomial
open scoped nonZeroDivisors
private theorem presentation_jetInclude :
    seedPresentation.toRingHom.comp jetInclude = MvPolynomial.C := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [jetInclude]
  · intro i
    change seedPresentation ((MvPolynomial.rename (Fin.natAdd 2)) (MvPolynomial.X i)) = _
    rw [MvPolynomial.rename_X]
    exact seedPresentation_jet i
private theorem specialize_jetInclude {A : Type*} [CommRing A] (q : Seeds →+* A) (s : Seeds) :
    specializeJets q (jetInclude s) = MvPolynomial.C (q s) := by
  have h := RingHom.congr_fun presentation_jetInclude s
  change seedPresentation (jetInclude s) = MvPolynomial.C s at h
  simp [specializeJets, h]
private def odeCoeff : ODE →+* Seeds :=
  eval₂RingHom (eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)) (MvPolynomial.X 1)
private theorem odeCoeff_surjective : Function.Surjective odeCoeff := by
  let e : Seeds →+* ODE :=
    MvPolynomial.eval₂Hom (C.comp C) ![C (Polynomial.X : Polynomial FX), Polynomial.X]
  have he : odeCoeff.comp e = RingHom.id Seeds := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [e, odeCoeff]
    · intro i
      fin_cases i <;> simp [e, odeCoeff]
  intro s
  exact ⟨e s, RingHom.congr_fun he s⟩
private theorem jetPlaneIncl_eq : jetPlaneIncl = jetInclude.comp odeCoeff := by
  apply Polynomial.ringHom_ext
  · intro f
    have h : jetPlaneIncl.comp C = (jetInclude.comp odeCoeff).comp C := by
      apply Polynomial.ringHom_ext
      · intro c
        simp [jetPlaneIncl, fixedIncl, K1_14_3.fixedEmbedding, toJet, toRoot,
          rootIncl, rootSeeds, jetInclude, odeCoeff]
      · simp [jetPlaneIncl, fixedIncl, K1_14_3.fixedEmbedding, toJet, toRoot,
          rootIncl, jetInclude, odeCoeff, AlgHom.toRingHom_eq_coe]
    exact RingHom.congr_fun h f
  · simp [jetPlaneIncl, fixedIncl, K1_14_3.fixedEmbedding, toJet, jetInclude, odeCoeff]
theorem imageIdeal_eq (I : Ideal Ambient) :
    (I.comap jetPlaneIncl).map jetPlaneIncl = (I.comap jetInclude).map jetInclude := by
  rw [jetPlaneIncl_eq, ← Ideal.comap_comap, ← Ideal.map_map,
    Ideal.map_comap_of_surjective _ odeCoeff_surjective]
private theorem specialize_ker {A : Type*} [CommRing A] (q : Seeds →+* A) :
    RingHom.ker (specializeJets q) = (RingHom.ker q).map jetInclude := by
  rw [specializeJets, ← RingHom.comap_ker, MvPolynomial.ker_map, ← presentation_jetInclude,
    ← Ideal.map_map,
    Ideal.comap_map_of_bijective seedPresentation.toRingHom seedPresentation.bijective]
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem clear_denominators {A : Type*} [CommRing A] [Nontrivial A]
    (q : Seeds →+* A) (hq : Function.Surjective q) (J : Ideal Ambient) (f : Ambient)
    (hf : specializeJets ((algebraMap A (FractionRing A)).comp q) f ∈
      J.map (specializeJets ((algebraMap A (FractionRing A)).comp q))) :
    ∃ s : Seeds, q s ≠ 0 ∧ jetInclude s * f ∈ J ⊔ (RingHom.ker q).map jetInclude := by
  let e := specializeJets q
  let a := algebraMap (MvPolynomial (Fin 2) A) (MvPolynomial (Fin 2) (FractionRing A))
  have he : Function.Surjective e :=
    (MvPolynomial.map_surjective _ hq).comp seedPresentation.surjective
  have hcomp : specializeJets ((algebraMap A (FractionRing A)).comp q) = a.comp e := by
    apply RingHom.ext
    intro f
    change MvPolynomial.map ((algebraMap A (FractionRing A)).comp q) (seedPresentation f) = _
    rw [← MvPolynomial.map_map]
    rfl
  rw [hcomp, ← Ideal.map_map] at hf
  change a (e f) ∈ (J.map e).map a at hf
  obtain ⟨_, ⟨d, hd, rfl⟩, hmem⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff
      ((nonZeroDivisors A).map (MvPolynomial.C (σ := Fin 2))) _ (J.map e) (e f)).mp hf
  obtain ⟨s, hs⟩ := hq d
  rw [← hs, ← specialize_jetInclude, ← map_mul] at hmem
  rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ he,
    ← RingHom.ker_eq_comap_bot, specialize_ker] at hmem
  exact ⟨s, hs.symm ▸ nonZeroDivisors.ne_zero hd, hmem⟩
theorem clear_dual {I : Ideal Ambient} (hd : dual I) {m : ℕ} {P : Jet}
    (hf : mapGenericJets (toJet P) ∈ (I.map mapGenericJets) ^ m) :
    orderOn I P m := by
  have hproper : I.map mapGenericJets ≠ ⊤ := by
    intro ht
    have hsub : Subsingleton (OverJets I) := by
      change Subsingleton (CoordinateRing (I.map mapGenericJets))
      rw [ht]
      infer_instance
    exact (Nat.ne_of_gt hd) Module.finrank_zero_of_subsingleton
  rw [← Ideal.map_pow, mapGenericJets_eq] at hf
  have h := clear_denominators (RingHom.id Seeds) Function.surjective_id (I ^ m) (toJet P)
    (by simpa only [RingHom.comp_id] using hf)
  obtain ⟨s, hs, hmem⟩ := h
  have hnot : jetInclude s ∉ I := by
    intro hin
    apply hproper
    have hm := Ideal.mem_map_of_mem mapGenericJets hin
    rw [mapGenericJets_eq, specialize_jetInclude] at hm
    rw [mapGenericJets_eq]
    apply Ideal.eq_top_of_isUnit_mem _ hm
    have hz : algebraMap Seeds SeedField s ≠ 0 := by
      intro he
      apply hs
      exact (IsFractionRing.injective Seeds SeedField)
        (he.trans ((algebraMap Seeds SeedField).map_zero).symm)
    exact (isUnit_iff_ne_zero.mpr hz).map MvPolynomial.C
  refine ⟨jetInclude s, hnot, ?_⟩
  simpa [hd, RingHom.ker_eq_comap_bot] using hmem
theorem clear_rank_one {I : Ideal Ambient} (hp : I.IsPrime) (hd : ¬ dual I) {m : ℕ} {P : Jet}
    (hf : imageFibreMap I (toJet P) ∈ (I.map (imageFibreMap I)) ^ m) :
    orderOn I P m := by
  classical
  let _ : I.IsPrime := hp
  have hj : (I.comap jetInclude).IsPrime := Ideal.IsPrime.comap jetInclude
  let _ : Nontrivial (JetImageRing I) := Ideal.Quotient.nontrivial_iff.mpr hj.ne_top
  let q : Seeds →+* JetImageRing I := Ideal.Quotient.mk (I.comap jetInclude)
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hclear := clear_denominators (A := JetImageRing I) q hq (I ^ m) (toJet P)
  have hspec : specializeJets ((algebraMap (JetImageRing I) (JetImageField I)).comp q) =
      imageFibreMap I := rfl
  rw [hspec, Ideal.map_pow] at hclear
  obtain ⟨s, hs, hmem⟩ := hclear hf
  have hnot : jetInclude s ∉ I := fun hin =>
    hs (Ideal.Quotient.eq_zero_iff_mem.mpr hin)
  refine ⟨jetInclude s, hnot, ?_⟩
  change jetInclude s * toJet P ∈ I ^ m ⊔
    (if dual I then ⊥ else (I.comap jetPlaneIncl).map jetPlaneIncl)
  rw [ite_eq_right hd, imageIdeal_eq]
  change jetInclude s * toJet P ∈ I ^ m ⊔
    (RingHom.ker (Ideal.Quotient.mk (I.comap jetInclude))).map jetInclude at hmem
  rwa [Ideal.mk_ker] at hmem
end
end K1_14_2_2_3
end
section
namespace K1_14_2_2_3
noncomputable section
open K1 MvPolynomial
private theorem natCast_ne_zero {A : Type*} [Field A] [CharP A p] {n : ℕ}
    (hpos : 0 < n) (hn : n < p) : (n : A) ≠ 0 := by
  intro hz
  exact (not_le_of_gt hn) (Nat.le_of_dvd hpos ((CharP.cast_eq_zero_iff _ _ _).mp hz))
private theorem exists_separant {A : Type*} [Field A] [CharP A p]
    {g : MvPolynomial (Fin 2) A} (hg : Prime g) (hdeg : g.totalDegree < p) :
    ∃ i : Fin 2, ¬ g ∣ pderiv i g := by
  have hv : g.vars.Nonempty := by
    by_contra! he
    have heq := vars_eq_empty_iff_eq_C.mp he
    have hn : g.coeff 0 ≠ 0 := by
      intro hz
      exact hg.ne_zero (by rw [heq, hz, map_zero])
    exact hg.not_isUnit (heq ▸ (isUnit_iff_ne_zero.mpr hn).map C)
  obtain ⟨i, hi⟩ := hv
  have hpos := Nat.pos_of_ne_zero (mem_vars_iff_degreeOf_ne_zero.mp hi)
  have hc : (g.degreeOf i : A) ≠ 0 :=
    natCast_ne_zero hpos ((degreeOf_le_totalDegree g i).trans_lt hdeg)
  have hn := pderiv_ne_zero_of_natCast_ne_zero i g hc
  have hb := degreeOf_pderiv_le_sub_one i g
  refine ⟨i, ?_⟩
  rintro ⟨f, h⟩
  have hf : f ≠ 0 := by
    intro hf
    exact hn (by rw [h, hf, mul_zero])
  rw [h, degreeOf_mul_eq hg.ne_zero hf] at hb
  omega
private theorem iter_not_dvd {A : Type*} [Field A] [CharP A p] (i : Fin 2)
    {g : MvPolynomial (Fin 2) A} (hg : Prime g) (hsep : ¬ g ∣ pderiv i g)
    (a : ℕ) (ha : a < p) {f : MvPolynomial (Fin 2) A} (hf : ¬ g ∣ f) :
    ¬ g ∣ (pderiv (R := A) i)^[a] (g ^ a * f) := by
  induction a generalizing f with
  | zero => simpa using hf
  | succ a ih =>
    let v := ((a + 1 : ℕ) : MvPolynomial (Fin 2) A) * (pderiv i g * f) + g * pderiv i f
    have hstep : pderiv i (g ^ (a + 1) * f) = g ^ a * v := by
      rw [pderiv_mul, pderiv_pow, Nat.add_sub_cancel, pow_succ g a]
      dsimp only [v]
      ring
    have hu : IsUnit ((a + 1 : ℕ) : MvPolynomial (Fin 2) A) := by
      rw [← map_natCast (C : A →+* MvPolynomial (Fin 2) A)]
      exact (isUnit_iff_ne_zero.mpr (natCast_ne_zero (Nat.succ_pos a) ha)).map C
    have hv : ¬ g ∣ v := by
      intro hd
      have hd' := (dvd_add_left (dvd_mul_right g (pderiv i f))).mp hd
      exact (hg.dvd_or_dvd (hu.dvd_mul_left.mp hd')).elim hsep hf
    rw [Function.iterate_succ_apply, hstep]
    exact ih (Nat.lt_of_succ_lt ha) hv
private theorem partialWord_replicate {A : Type*} [Field A] (f : MvPolynomial (Fin 2) A)
    (i : Fin 2) (a : ℕ) :
    partialWord f (List.replicate a i) = (pderiv (R := A) i)^[a] f := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [List.replicate_succ, partialWord, ih, Function.iterate_succ_apply']
theorem divisor_contact {A : Type*} [Field A] [CharP A p] {g f : MvPolynomial (Fin 2) A}
    (hg : Prime g) (hdeg : g.totalDegree < p) {r : ℕ} (hr : r < p)
    (hf : fibreContact (Ideal.span {g}) f r) :
    f ∈ Ideal.span ({g} : Set (MvPolynomial (Fin 2) A)) ^ (r+1) := by
  classical
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  by_contra hpow
  obtain ⟨i, hi⟩ := exists_separant hg hdeg
  have hex : ∃ n : ℕ, ¬ g ^ n ∣ f := ⟨r+1, hpow⟩
  have hpos : 0 < Nat.find hex := by
    by_contra! hn
    have hz : Nat.find hex = 0 := by omega
    exact Nat.find_spec hex (by simp [hz])
  let a := Nat.find hex - 1
  have ha : a+1 = Nat.find hex := Nat.sub_add_cancel hpos
  have har : a ≤ r := by
    have hle := Nat.find_min' hex hpow
    omega
  obtain ⟨u, he⟩ : g ^ a ∣ f :=
    not_not.mp (Nat.find_min hex (by omega : a < Nat.find hex))
  have hu : ¬ g ∣ u := by
    rintro ⟨z, rfl⟩
    apply Nat.find_spec hex
    rw [← ha, he, pow_succ, ← mul_assoc]
    exact dvd_mul_right _ _
  have hd := hf (List.replicate a i) (by simpa using har)
  rw [partialWord_replicate, he, Ideal.mem_span_singleton] at hd
  exact iter_not_dvd i hg hi a (har.trans_lt hr) hu hd
end
end K1_14_2_2_3
end
section
namespace K1_14_2_2_3
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2
def c1 : Prop :=
  ∀ I : Ideal Ambient, I.IsPrime →
    Module.Finite SeedField (OverJets I) → dual I →
    Module.finrank SeedField (OverJets I) < p →
    ∀ (f : FibreRing) (r : ℕ), r < p →
      fibreContact (I.map mapGenericJets) f r →
      f ∈ (I.map mapGenericJets) ^ (r+1)
def c2 : Prop :=
  ∀ I : Ideal Ambient, Active I → ¬ dual I →
    ∃ g : MvPolynomial (Fin 2) (JetImageField I),
      Prime g ∧ g.totalDegree < p ∧ I.map (imageFibreMap I) = Ideal.span {g}
theorem of_children (h1 : c1) (h2 : c2) : K1_14_2_2.c3 := by
  classical
  intro h rows s I _ hactive hn hshift hv W r P hr hcut hP
  by_cases hd : dual I
  · have hc := contact_of_shift (algebraMap Seeds SeedField) hn hshift hv hcut hP
    rw [← mapGenericJets_eq] at hc
    exact clear_dual hd (h1 I hactive.prime hactive.jet_finite hd hactive.jet_lt _ r hr hc)
  · obtain ⟨g, hg, hdeg, he⟩ := h2 I hactive hd
    let _ : I.IsPrime := hactive.prime
    let _ : (I.comap jetInclude).IsPrime := Ideal.IsPrime.comap jetInclude
    let _ : CharP FX p := charP_of_injective_ringHom seedEmbedding.injective p
    let _ : CharP (JetImageField I) p :=
      charP_of_injective_ringHom ((jetImageMap I).comp MvPolynomial.C).injective p
    apply clear_rank_one hactive.prime hd
    have hc : fibreContact (I.map (imageFibreMap I)) (imageFibreMap I (toJet P)) r :=
      contact_of_shift (jetImageMap I) hn hshift hv hcut hP
    rw [he] at hc ⊢
    exact divisor_contact hg hdeg hr hc
end
end K1_14_2_2_3
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace K1_14_2_2_3_2
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_3
open scoped Polynomial nonZeroDivisors
private theorem presentation_jetInclude :
    seedPresentation.toRingHom.comp jetInclude = MvPolynomial.C := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [jetInclude]
  · intro i
    change seedPresentation ((MvPolynomial.rename (Fin.natAdd 2)) (MvPolynomial.X i)) = _
    rw [MvPolynomial.rename_X]
    exact seedPresentation_jet i
private theorem specialize_jetInclude {A : Type*} [CommRing A]
    (q : Seeds →+* A) (s : Seeds) :
    specializeJets q (jetInclude s) = MvPolynomial.C (q s) := by
  have h := RingHom.congr_fun presentation_jetInclude s
  change seedPresentation (jetInclude s) = MvPolynomial.C s at h
  simp [specializeJets, h]
private theorem specialize_ker {A : Type*} [CommRing A] (q : Seeds →+* A) :
    RingHom.ker (specializeJets q) = (RingHom.ker q).map jetInclude := by
  rw [specializeJets, ← RingHom.comap_ker, MvPolynomial.ker_map, ← presentation_jetInclude,
    ← Ideal.map_map,
    Ideal.comap_map_of_bijective seedPresentation.toRingHom seedPresentation.bijective]
private theorem jetInclude_injective : Function.Injective jetInclude := by
  intro a b h
  apply MvPolynomial.C_injective (Fin 2) Seeds
  exact (RingHom.congr_fun presentation_jetInclude a).symm.trans
    ((congrArg seedPresentation.toRingHom h).trans (RingHom.congr_fun presentation_jetInclude b))
def ordinateInImage (I : Ideal Ambient) : FX[X] →ₐ[FX] JetImageRing I :=
  Polynomial.aeval (Ideal.Quotient.mk (I.comap jetInclude) (MvPolynomial.X 0))
theorem ordinateInImage_injective {I : Ideal Ambient} (hI : Active I) :
    Function.Injective (ordinateInImage I) := by
  let u : FX[X] →+* Seeds :=
    Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)
  have h : jetInclude.comp u = ordinateIncl := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [jetInclude, u, ordinateIncl]
    · simp [jetInclude, u, ordinateIncl]
  have hn : (ordinateInImage I).toRingHom = (Ideal.Quotient.mk _).comp u := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [ordinateInImage, u]
      rfl
    · simp [ordinateInImage, u]
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  rw [RingHom.ker_eq_bot_iff_eq_zero]
  intro a ha
  change (ordinateInImage I).toRingHom a = 0 at ha
  rw [hn, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem] at ha
  have hz : ((Ideal.Quotient.mk I).comp ordinateIncl) a = 0 := by
    rw [← h]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  exact hI.ordinate_dominant (hz.trans (map_zero _).symm)
private theorem image_dimension_pos {I : Ideal Ambient} (hI : Active I)
    [I.IsPrime] : 1 ≤ ringKrullDim (JetImageRing I) := by
  let B := JetImageRing I
  let : (I.comap jetInclude).IsPrime := Ideal.comap_isPrime jetInclude I
  have hfield : ¬ IsField B := by
    intro h
    let : Field B := h.toField
    let : Module.Finite FX B := finite_of_finite_type_of_isJacobsonRing FX B
    exact Polynomial.not_finite (Module.Finite.of_injective
      (ordinateInImage I).toLinearMap (ordinateInImage_injective hI))
  obtain ⟨P, hP, _⟩ := (⊥ : Ideal B).exists_le_maximal bot_ne_top
  let : P.IsPrime := hP.isPrime
  have hne : (⊥ : Ideal B) ≠ P := fun h =>
    hfield (Ring.isField_iff_maximal_bot.mpr (h.symm ▸ hP))
  have hlt : (⊥ : Ideal B) < P := bot_lt_iff_ne_bot.mpr hne.symm
  have hlo : 1 ≤ P.height := by
    simpa [Ideal.height_bot] using Ideal.height_add_one_le_of_lt_of_isPrime hlt
  exact (WithBot.coe_le_coe.mpr hlo).trans (Ideal.height_le_ringKrullDim_of_isPrime (I := P))
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem imageIdeal_ne_bot {I : Ideal Ambient} (hI : Active I) (hd : ¬ dual I)
    [I.IsPrime] : I.comap jetInclude ≠ ⊥ := by
  intro hbot
  let Q := I.map seedPresentation.toRingHom
  have hbase : Q.comap MvPolynomial.C = I.comap jetInclude := by
    rw [← presentation_jetInclude, ← Ideal.comap_comap,
      Ideal.comap_map_of_bijective seedPresentation.toRingHom seedPresentation.bijective]
  let S := (nonZeroDivisors Seeds).map (MvPolynomial.C (σ := Fin 2))
  have hdisj : Disjoint (S : Set (MvPolynomial (Fin 2) Seeds))
      (Q : Set (MvPolynomial (Fin 2) Seeds)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨d, hd, rfl⟩ hm
    have he : d ∈ Q.comap MvPolynomial.C := hm
    rw [hbase, hbot] at he
    exact nonZeroDivisors.ne_zero hd (Ideal.mem_bot.mp he)
  have hproper := (IsLocalization.map_algebraMap_ne_top_iff_disjoint
    (S := MvPolynomial (Fin 2) SeedField) _ Q).mpr hdisj
  have he : Q.map (algebraMap (MvPolynomial (Fin 2) Seeds)
      (MvPolynomial (Fin 2) SeedField)) = I.map mapGenericJets := by
    rw [mapGenericJets_eq, specializeJets, ← Ideal.map_map]
    rfl
  rw [he] at hproper
  let : Nontrivial (OverJets I) := Ideal.Quotient.nontrivial_iff.mpr hproper
  let : Module.Finite SeedField (OverJets I) := hI.jet_finite
  exact hd Module.finrank_pos
private theorem parent_height_le {I : Ideal Ambient} (hI : Active I) [I.IsPrime] :
    I.height ≤ 2 := by
  let x : PrimeSpectrum Ambient := ⟨I, inferInstance⟩
  have hc : Order.coheight x = 2 := by
    have h := hI.dimension
    rw [ringKrullDim_quotient] at h
    change Order.krullDim (Set.Ici x) = 2 at h
    rw [← Order.coheight_eq_krullDim_Ici] at h
    exact WithBot.coe_injective h
  have hd : ringKrullDim Ambient = 4 := by
    simp [ringKrullDim_eq_zero_of_field]
  have hh : (↑(Order.height x + Order.coheight x) : WithBot ℕ∞) ≤ ringKrullDim Ambient := by
    rw [ringKrullDim, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
    exact WithBot.coe_le_coe.mpr (le_iSup (fun y : PrimeSpectrum Ambient =>
      Order.height y + Order.coheight y) x)
  rw [hc, ← x.height_eq_orderHeight, hd] at hh
  have hh' : I.height + 2 ≤ (2 : ℕ∞) + 2 := WithBot.coe_le_coe.mp hh
  exact (ENat.add_le_add_iff_right (by simp : (2 : ℕ∞) ≠ ⊤)).mp hh'
theorem primeGenerator {I : Ideal Ambient} (hI : Active I) (hd : ¬ dual I) :
    ∃ g : MvPolynomial (Fin 2) (JetImageField I),
      Prime g ∧ I.map (imageFibreMap I) = Ideal.span {g} := by
  let : I.IsPrime := hI.prime
  let P := I.comap jetInclude
  let : P.IsPrime := Ideal.comap_isPrime jetInclude I
  let B := JetImageRing I
  let D := MvPolynomial (Fin 2) B
  let E := MvPolynomial (Fin 2) (JetImageField I)
  let q : Seeds →+* B := Ideal.Quotient.mk P
  let e : Ambient →+* D := specializeJets q
  let a : D →+* E := algebraMap D E
  let Q := I.map e
  let J := I.map (imageFibreMap I)
  let S := (nonZeroDivisors B).map (MvPolynomial.C (σ := Fin 2))
  have he : Function.Surjective e :=
    (MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective).comp seedPresentation.surjective
  have hk : RingHom.ker e = P.map jetInclude := by
    rw [specialize_ker, Ideal.mk_ker]
  have hkle : RingHom.ker e ≤ I := by
    rw [hk]
    exact Ideal.map_comap_le
  have hQcomap : Q.comap e = I := by
    rw [Ideal.comap_map_of_surjective _ he, ← RingHom.ker_eq_comap_bot, sup_of_le_left hkle]
  have hQa : J = Q.map a := by
    change J = (I.map e).map a
    rw [Ideal.map_map]
    change I.map (specializeJets ((algebraMap B (JetImageField I)).comp q)) = I.map (a.comp e)
    congr 1
    apply RingHom.ext
    intro f
    change MvPolynomial.map ((algebraMap B (JetImageField I)).comp q) (seedPresentation f) =
      MvPolynomial.map (algebraMap B (JetImageField I)) (MvPolynomial.map q (seedPresentation f))
    rw [MvPolynomial.map_map]
  have hQ : Q.IsPrime := Ideal.map_isPrime_of_surjective he hkle
  have hS : Disjoint (S : Set D) (Q : Set D) := by
    rw [Set.disjoint_left]
    rintro _ ⟨d, hd, rfl⟩ hm
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective (I := P) d
    have hm' : jetInclude s ∈ Q.comap e := by
      change specializeJets q (jetInclude s) ∈ Q
      rwa [specialize_jetInclude]
    rw [hQcomap] at hm'
    exact nonZeroDivisors.ne_zero hd (Ideal.Quotient.eq_zero_iff_mem.mpr hm')
  have hJ : J.IsPrime := by
    rw [hQa]
    exact IsLocalization.isPrime_of_isPrime_disjoint S E Q hQ hS
  have hJa : J.comap a = Q := by
    rw [hQa]
    exact IsLocalization.under_map_of_isPrime_disjoint S E hQ hS
  have ha : Function.Injective a :=
    MvPolynomial.map_injective _ (IsFractionRing.injective B (JetImageField I))
  have hJn : J ≠ ⊥ := by
    intro hz
    have hQ0 : Q = ⊥ := by
      rw [← hJa, hz, Ideal.comap_bot_of_injective _ ha]
    have hIker : RingHom.ker e = I := by
      rw [RingHom.ker_eq_comap_bot, ← hQ0, hQcomap]
    let eq : CoordinateRing I ≃+* D :=
      (Ideal.quotEquivOfEq hIker.symm).trans (e.quotientKerEquivOfSurjective he)
    have hdim := ringKrullDim_eq_of_ringEquiv (R := CoordinateRing I) (S := D) eq
    rw [hI.dimension] at hdim
    have hpoly := ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial (R := B) (Fin 2)
    rw [Nat.card_fin, ← hdim] at hpoly
    have hlo : (1 : WithBot ℕ∞) + 2 ≤ 2 :=
      (add_le_add (image_dimension_pos hI) (le_refl (2 : WithBot ℕ∞))).trans hpoly
    exact (by decide : ¬ (1 : WithBot ℕ∞) + 2 ≤ 2) hlo
  have hk0 : (⊥ : Ideal Ambient) < RingHom.ker e := by
    obtain ⟨d, hdP, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (imageIdeal_ne_bot hI hd)
    apply bot_lt_iff_ne_bot.mpr
    intro h
    have hm := Ideal.mem_map_of_mem jetInclude hdP
    rw [← hk, h, Ideal.mem_bot] at hm
    exact hd0 (jetInclude_injective (hm.trans (map_zero _).symm))
  let : UniqueFactorizationMonoid (JetImageField I) := PrincipalIdealRing.to_uniqueFactorizationMonoid
  let : UniqueFactorizationMonoid E := MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  obtain ⟨g, hgJ, hg⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot hJ hJn
  refine ⟨g, hg, le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).mpr hgJ)⟩
  by_contra hn
  let G : Ideal E := Ideal.span {g}
  let K := (G.comap a).comap e
  have hG : G.IsPrime := (Ideal.span_singleton_prime hg.ne_zero).mpr hg
  have hK : K.IsPrime := Ideal.comap_isPrime e _
  have hlt : G < J := lt_of_le_of_ne ((Ideal.span_singleton_le_iff_mem _).mpr hgJ)
    (fun h => hn h.ge)
  have hmap : StrictMono (Ideal.comap a) := by
    intro U W h
    have hinv (T : Ideal E) : (T.comap a).map a = T := IsLocalization.map_under S E T
    exact lt_of_le_of_ne (Ideal.comap_mono h.le) fun hm =>
      h.ne ((hinv U).symm.trans ((congrArg (Ideal.map a) hm).trans (hinv W)))
  have he' : StrictMono (Ideal.comap e) := by
    intro U W h
    exact lt_of_le_of_ne (Ideal.comap_mono h.le)
      (fun hm => h.ne (Ideal.comap_injective_of_surjective e he hm))
  have hKI : K < I := by
    rw [← hQcomap, ← hJa]
    exact he' (hmap hlt)
  have hbotG : (⊥ : Ideal E) < G :=
    bot_lt_iff_ne_bot.mpr (Ideal.span_singleton_eq_bot.not.mpr hg.ne_zero)
  have hkK : RingHom.ker e < K := by
    rw [RingHom.ker_eq_comap_bot]
    have h := hmap hbotG
    change (⊥ : Ideal E).comap a < G.comap a at h
    rw [Ideal.comap_bot_of_injective _ ha] at h
    exact he' h
  have : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hk0
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hkK
  have h3 := Ideal.height_add_one_le_of_lt_of_isPrime hKI
  have hlo : (3 : ℕ∞) ≤ I.height := calc
    (3 : ℕ∞) = (⊥ : Ideal Ambient).height + 1 + 1 + 1 := by
      rw [Ideal.height_bot]
      decide
    _ ≤ (RingHom.ker e).height + 1 + 1 := add_le_add (add_le_add h1 le_rfl) le_rfl
    _ ≤ K.height + 1 := add_le_add h2 le_rfl
    _ ≤ I.height := h3
  exact (by decide : ¬ (3 : ℕ∞) ≤ 2) (hlo.trans (parent_height_le hI))
end
end K1_14_2_2_3_2
end
section
namespace K1_14_2_2_3_1
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_3 MvPolynomial
open scoped nonZeroDivisors
private theorem natCast_ne_zero {A : Type*} [Field A] [CharP A p] {n : ℕ}
    (hpos : 0 < n) (hlt : n < p) : (n : A) ≠ 0 := by
  intro h
  exact (not_le_of_gt hlt) (Nat.le_of_dvd hpos ((CharP.cast_eq_zero_iff _ _ _).mp h))
private theorem separable_of_small_rank {A E : Type*} [Field A] [Field E] [CharP A p]
    [Algebra A E] [Module.Finite A E] (hsize : Module.finrank A E < p) :
    Algebra.IsSeparable A E := by
  constructor
  intro x
  have hx : IsIntegral A x := Algebra.IsIntegral.isIntegral x
  let f := minpoly A x
  have hpos : 0 < f.natDegree := minpoly.natDegree_pos hx
  have hlt : f.natDegree < p := (minpoly.natDegree_le x).trans_lt hsize
  change f.Separable
  apply (Polynomial.separable_iff_derivative_ne_zero (minpoly.irreducible hx)).2
  intro hzero
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  have hcoeff := congrArg (fun q : Polynomial A => q.coeff n) hzero
  change f.derivative.coeff n = (0 : Polynomial A).coeff n at hcoeff
  have hmonic : f.coeff f.natDegree = 1 := (minpoly.monic hx).leadingCoeff
  rw [hn] at hmonic
  rw [Polynomial.coeff_derivative, Polynomial.coeff_zero, ← Nat.cast_succ,
    ← hn, hmonic, one_mul] at hcoeff
  exact natCast_ne_zero hpos hlt hcoeff
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem jet_fibre_prime {I : Ideal Ambient} (hI : I.IsPrime) (hd : dual I) :
    (I.map mapGenericJets).IsPrime := by
  let R := MvPolynomial (Fin 2) Seeds
  let S : Submonoid R := (nonZeroDivisors Seeds).map MvPolynomial.C
  let J := I.map seedPresentation.toRingHom
  have hJ : J.IsPrime := by
    change (I.map (seedPresentation : Ambient →+* R)).IsPrime
    rw [Ideal.map_comap_of_equiv seedPresentation]
    exact hI.comap _
  have hm : I.map mapGenericJets = J.map (algebraMap R FibreRing) := by
    rw [Ideal.map_map, mapGenericJets_eq]
    rfl
  have hproper : I.map mapGenericJets ≠ ⊤ := by
    intro ht
    let : Subsingleton (OverJets I) := Ideal.Quotient.subsingleton_iff.mpr ht
    exact (Nat.ne_of_gt hd) (Module.finrank_eq_zero_of_subsingleton SeedField (OverJets I))
  have hdisj : Disjoint (S : Set R) (J : Set R) :=
    (IsLocalization.map_algebraMap_ne_top_iff_disjoint S FibreRing J).mp (hm ▸ hproper)
  rw [hm]
  exact IsLocalization.isPrime_of_isPrime_disjoint S FibreRing J hJ hdisj
private def translate {A : Type*} [CommRing A] (a : Fin 2 → A) :
    MvPolynomial (Fin 2) A →+* MvPolynomial (Fin 2) A :=
  eval₂Hom C (fun i => MvPolynomial.X i + C (a i))
private theorem translate_partial {A : Type*} [CommRing A] (a : Fin 2 → A)
    (f : MvPolynomial (Fin 2) A) (i : Fin 2) :
    translate a (pderiv i f) = pderiv i (translate a f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C c => simp [translate]
  | add f g hf hg => simp [hf, hg]
  | mul_X f j hf =>
    rw [pderiv_mul, map_add, map_mul, map_mul, hf, map_mul, pderiv_mul]
    by_cases hj : j = i
    · subst j
      simp [translate]
    · simp [translate, pderiv_X_of_ne hj]
private theorem translate_word {A E : Type*} [CommRing A] [CommRing E]
    (c : A →+* E) (a : Fin 2 → E) (f : MvPolynomial (Fin 2) A) (t : List (Fin 2)) :
    partialWord (translate a (map c f)) t = translate a (map c (partialWord f t)) := by
  induction t with
  | nil => rfl
  | cons i t ih => rw [partialWord, partialWord, ih, ← translate_partial, pderiv_map]
private theorem partial_append {A : Type*} [CommRing A] (f : MvPolynomial (Fin 2) A)
    (i : Fin 2) (t : List (Fin 2)) :
    partialWord f (t ++ [i]) = partialWord (pderiv i f) t := by
  induction t with
  | nil => rfl
  | cons j t ih => simp only [List.cons_append, partialWord, ih]
private theorem origin_order {E : Type*} [CommRing E]
    (hunit : ∀ n : ℕ, 0 < n → n < p → IsUnit (n : E)) (r : ℕ)
    (hr : r < p) (f : MvPolynomial (Fin 2) E)
    (hf : ∀ t : List (Fin 2), t.length ≤ r → (partialWord f t).coeff 0 = 0) :
    f ∈ idealOfVars (Fin 2) E ^ (r + 1) := by
  classical
  induction r generalizing f with
  | zero =>
    apply (mem_pow_idealOfVars_iff' _ _).mpr
    intro m hm
    have hz : m = 0 := (Finsupp.degree_eq_zero_iff m).mp (by omega)
    subst m
    exact hf [] (by simp)
  | succ r ih =>
    apply (mem_pow_idealOfVars_iff' _ _).mpr
    intro m hm
    by_cases hz : m = 0
    · subst m
      exact hf [] (by simp)
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hz
    change m i ≠ 0 at hi
    have hs : Finsupp.single i 1 ≤ m := Finsupp.single_le_iff.mpr (Nat.pos_of_ne_zero hi)
    obtain ⟨k, hk⟩ := le_iff_exists_add'.mp hs
    have hdeg : m.degree = k.degree + 1 := by rw [hk, map_add, Finsupp.degree_single]
    have hsmall : k.degree < r + 1 := by omega
    have hmem := ih (Nat.lt_of_succ_lt hr) (pderiv i f) (fun t ht => by
      rw [← partial_append]
      apply hf
      simpa using Nat.succ_le_succ ht)
    have hc := (mem_pow_idealOfVars_iff' _ _).mp hmem k hsmall
    rw [coeff_pderiv, ← hk] at hc
    have hcast : IsUnit ((k i : E) + 1) := by
      rw [← Nat.cast_succ]
      apply hunit _ (Nat.succ_pos _)
      have hle := Finsupp.le_degree i k
      omega
    exact hcast.mul_left_eq_zero.mp hc
set_option maxHeartbeats 500000 in
private theorem contact_of_formallySmooth {A : Type*} [Field A] [CharP A p]
    (J : Ideal (MvPolynomial (Fin 2) A))
    [Algebra.FormallySmooth A (MvPolynomial (Fin 2) A ⧸ J)]
    (f : MvPolynomial (Fin 2) A) (r : ℕ) (hr : r < p) (hf : fibreContact J f r) :
    f ∈ J ^ (r + 1) := by
  let R := MvPolynomial (Fin 2) A
  let E := R ⧸ J
  let B := R ⧸ J ^ (r + 1)
  let q : R →ₐ[A] E := Ideal.Quotient.mkₐ A J
  let b : R →ₐ[A] B := Ideal.Quotient.mkₐ A (J ^ (r + 1))
  have hle : J ^ (r + 1) ≤ J := Ideal.pow_le_self (Nat.succ_ne_zero r)
  let g : B →ₐ[A] E := Ideal.Quotient.factorₐ A hle
  have hker : RingHom.ker g = J.map b := by
    change RingHom.ker (Ideal.Quotient.factor hle) = J.map (Ideal.Quotient.mk _)
    calc
      _ = (RingHom.ker (Ideal.Quotient.mk J)).map (Ideal.Quotient.mk (J ^ (r + 1))) :=
        Ideal.ker_quotient_lift (Ideal.Quotient.mk J) _
      _ = _ := by rw [Ideal.mk_ker]
  have hnil : (RingHom.ker g) ^ (r + 1) = ⊥ := by
    rw [hker, ← Ideal.map_pow]
    exact Ideal.map_quotient_self (J ^ (r + 1))
  have hn : IsNilpotent (RingHom.ker g) := ⟨r + 1, hnil⟩
  have hg : Function.Surjective g := Ideal.Quotient.factor_surjective hle
  let s := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id A E) g hg hn
  have hs (x : E) : g (s x) = x :=
    Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id A E) g hg hn x
  let a (i : Fin 2) := q (MvPolynomial.X i)
  let F := translate a (map (algebraMap A E) f)
  have he : (constantCoeff.comp ((translate a).comp (map (algebraMap A E)))) = q.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [translate, q, E, R, ← MvPolynomial.algebraMap_eq]
    · intro i
      simp [translate, a]
  have hunit (n : ℕ) (hpos : 0 < n) (hlt : n < p) : IsUnit (n : E) := by
    rw [← map_natCast (algebraMap A E)]
    exact (isUnit_iff_ne_zero.mpr (natCast_ne_zero hpos hlt : (n : A) ≠ 0)).map (algebraMap A E)
  have hF : F ∈ idealOfVars (Fin 2) E ^ (r + 1) := by
    refine origin_order hunit r hr F ?_
    intro t ht
    change constantCoeff (partialWord F t) = 0
    rw [show F = translate a (map (algebraMap A E) f) from rfl, translate_word]
    change (constantCoeff.comp ((translate a).comp (map (algebraMap A E)))) (partialWord f t) = 0
    rw [he]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hf t ht)
  let w (i : Fin 2) := b (MvPolynomial.X i) - s (a i)
  let ev : MvPolynomial (Fin 2) E →+* B := eval₂Hom s.toRingHom w
  have hw : (idealOfVars (Fin 2) E).map ev ≤ RingHom.ker g := by
    rw [Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change g (ev (MvPolynomial.X i)) = 0
    rw [show ev (MvPolynomial.X i) = w i by simp [ev]]
    change g (b (MvPolynomial.X i) - s (a i)) = 0
    rw [map_sub, hs]
    exact sub_self (a i)
  have hzero : ev F = 0 := by
    have hm := Ideal.mem_map_of_mem ev hF
    rw [Ideal.map_pow] at hm
    have hm' : ev F ∈ (RingHom.ker g) ^ (r + 1) := (pow_left_mono (r + 1) hw) hm
    rw [hnil] at hm'
    exact Ideal.mem_bot.mp hm'
  have hcomp : (ev.comp (translate a)).comp (map (algebraMap A E)) = b.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, map_C, translate, ev, eval₂Hom_C]
      change s (algebraMap A E c) = b (C c)
      rw [s.commutes, ← MvPolynomial.algebraMap_eq, b.commutes]
    · intro i
      simp [translate, ev, w]
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change b f = 0
  exact (RingHom.congr_fun hcomp f).symm.trans hzero
theorem proof : K1_14_2_2_3.c1 := by
  intro I hI hfinite hd hsize f r hr hf
  let J := I.map mapGenericJets
  let : J.IsPrime := jet_fibre_prime hI hd
  let : Module.Finite SeedField (FibreRing ⧸ J) := hfinite
  let : Field (FibreRing ⧸ J) := fieldOfFiniteDimensional SeedField _
  let : CharP SeedField p := charP_of_injective_ringHom
    ((algebraMap FX SeedField).comp seedEmbedding).injective p
  let : Algebra.IsSeparable SeedField (FibreRing ⧸ J) := separable_of_small_rank hsize
  let : Algebra.FormallyEtale SeedField (FibreRing ⧸ J) :=
    Algebra.FormallyEtale.of_isSeparable SeedField (FibreRing ⧸ J)
  exact contact_of_formallySmooth J f r hr hf
end
end K1_14_2_2_3_1
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_2_2_5
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 Polynomial
def ordinatePolynomial (G : ODE) : SectionField[X] :=
  G.map (eval₂RingHom (algebraMap FX SectionField) (sliceParameter 3))
def mixedPolynomial (G : ODE) : SectionField[X] :=
  G.eval₂
    (eval₂RingHom (Polynomial.C.comp (algebraMap FX SectionField))
      (Polynomial.C (sliceParameter 3) - Polynomial.C (sliceParameter 1) *
        (Polynomial.X : SectionField[X])))
    (Polynomial.X : SectionField[X])
abbrev JetImage (I : Ideal Ambient) :=
  CoordinateRing (R := ODE) (I.comap jetPlaneIncl)
def seedLineLift (I : Ideal Ambient) :
    MvPolynomial (Fin 3) (JetImage I) →+* MvPolynomial (Fin 2) (CoordinateRing I) :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C.comp (Ideal.quotientMap I jetPlaneIncl le_rfl))
    ![MvPolynomial.X 0, MvPolynomial.X 1,
      MvPolynomial.C (Ideal.Quotient.mk I (MvPolynomial.X 0)) +
        MvPolynomial.X 0 * MvPolynomial.C (Ideal.Quotient.mk I (MvPolynomial.X 1))]
end
end K1_14_2_2_5
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
namespace K1_14_2_2_5
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 Polynomial
open scoped BigOperators
theorem parameter_eval_injective (i : Fin 4) :
    Function.Injective (eval₂RingHom (algebraMap FX SectionField) (sliceParameter i)) := by
  let e : FX[X] →+* MvPolynomial (Fin 4) FX := eval₂RingHom MvPolynomial.C (MvPolynomial.X i)
  let r : MvPolynomial (Fin 4) FX →+* FX[X] := MvPolynomial.eval₂Hom Polynomial.C fun _ => (Polynomial.X : FX[X])
  have hr : r.comp e = RingHom.id _ := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [r, e]
    · simp [r, e]
  have hh : eval₂RingHom (algebraMap FX SectionField) (sliceParameter i) =
      (algebraMap (MvPolynomial (Fin 4) FX) SectionField).comp e := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, e, coe_eval₂RingHom, eval₂_C]
      exact IsScalarTower.algebraMap_apply FX (MvPolynomial (Fin 4) FX) SectionField a
    · simp [e, sliceParameter]
  have he : Function.Injective e :=
    (show Function.LeftInverse r e from fun p => RingHom.congr_fun hr p).injective
  rw [hh]
  exact (IsFractionRing.injective (MvPolynomial (Fin 4) FX) SectionField).comp he
theorem ordinatePolynomial_natDegree (G : ODE) :
    (ordinatePolynomial G).natDegree = G.natDegree :=
  natDegree_map_eq_of_injective (parameter_eval_injective 3) _
theorem mixedPolynomial_monomial_le {G : ODE} (hG : G ≠ 0) {j i : ℕ}
    (hij : (G.coeff j).coeff i ≠ 0) : i + j ≤ (mixedPolynomial G).natDegree := by
  classical
  let k := algebraMap FX SectionField
  let a := sliceParameter 1
  let b := sliceParameter 3
  let z : SectionField[X] := C b - C a * (Polynomial.X : SectionField[X])
  let e : FX[X] →+* SectionField[X] := eval₂RingHom (C.comp k) z
  have ha : a ≠ 0 := by
    have h := (parameter_eval_injective 1).ne (X_ne_zero (R := FX))
    simpa [a] using h
  have hz : z.natDegree = 1 := by
    change (C b - C a * (Polynomial.X : SectionField[X])).natDegree = 1
    rw [sub_eq_add_neg, add_comm, ← neg_mul, ← map_neg]
    exact natDegree_linear (neg_ne_zero.mpr ha)
  have hz' : z.leadingCoeff = -a := by
    rw [leadingCoeff, hz]
    simp [z, coeff_mul_X]
  have he (p : FX[X]) : e p = (p.map k).comp z := by
    change p.eval₂ (C.comp k) z = _
    rw [Polynomial.comp, eval₂_map]
  have hd (p : FX[X]) : (e p).natDegree = p.natDegree := by
    rw [he, natDegree_comp, hz, mul_one, natDegree_map_eq_of_injective k.injective]
  have hcoeff (p : FX[X]) (n : ℕ) (hpn : p.natDegree ≤ n) :
      (e p).coeff n = k (p.coeff n * (-1) ^ n) * a ^ n := by
    by_cases hp : p.natDegree = n
    · subst n
      calc
        (e p).coeff p.natDegree = (e p).leadingCoeff := by rw [leadingCoeff, hd]
        _ = k (p.coeff p.natDegree) * (-a) ^ p.natDegree := by
          rw [he, leadingCoeff_comp (by simp [hz]), hz', leadingCoeff_map,
            natDegree_map_eq_of_injective k.injective, coeff_natDegree]
        _ = k (p.coeff p.natDegree * (-1) ^ p.natDegree) * a ^ p.natDegree := by
          rw [map_mul, map_pow, map_neg, map_one, mul_assoc, ← mul_pow, neg_one_mul]
    · have hp' : p.natDegree < n := lt_of_le_of_ne hpn hp
      rw [coeff_eq_zero_of_natDegree_lt (by rwa [hd]), coeff_eq_zero_of_natDegree_lt hp']
      simp
  let D := G.support.sup (fun v => (G.coeff v).natDegree + v)
  have hD (v : ℕ) (hv : v ∈ G.support) : (G.coeff v).natDegree + v ≤ D :=
    Finset.le_sup (f := fun v => (G.coeff v).natDegree + v) hv
  obtain ⟨v₀, hv₀, hD₀⟩ := G.support.exists_mem_eq_sup (support_nonempty.mpr hG)
    (fun v => (G.coeff v).natDegree + v)
  change D = (G.coeff v₀).natDegree + v₀ at hD₀
  set top : FX[X] := ∑ v ∈ G.support,
    monomial (D-v) ((G.coeff v).coeff (D-v) * (-1) ^ (D-v)) with htopDef
  have htop : top ≠ 0 := by
    have htop' : top.coeff (D - v₀) ≠ 0 := by
      rw [htopDef, finsetSum_coeff, Finset.sum_eq_single_of_mem v₀ hv₀]
      · rw [coeff_monomial_same, show D - v₀ = (G.coeff v₀).natDegree by omega,
          coeff_natDegree]
        exact mul_ne_zero (leadingCoeff_ne_zero.mpr (mem_support_iff.mp hv₀))
          (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      · intro v hv hne
        have := hD v hv
        exact coeff_monomial_of_ne _ (by omega)
    intro h
    exact htop' (by simp [h])
  let t := eval₂RingHom k a
  have ht : t top ≠ 0 := by
    have h : t top ≠ t 0 := (parameter_eval_injective 1).ne htop
    simpa only [map_zero] using h
  have hcoeffD : (mixedPolynomial G).coeff D = t top := by
    change (G.eval₂ e (Polynomial.X : SectionField[X])).coeff D = t top
    rw [eval₂_eq_sum, Polynomial.sum, finsetSum_coeff, htopDef, map_sum]
    apply Finset.sum_congr rfl
    intro v hv
    have hb := hD v hv
    rw [coeff_mul_X_pow', ite_eq_left (show v ≤ D by omega), hcoeff _ _ (by omega)]
    simp [t, eval₂_monomial]
  have hDle : D ≤ (mixedPolynomial G).natDegree :=
    le_natDegree_of_ne_zero (hcoeffD.trans_ne ht)
  have hj : j ∈ G.support := by
    apply mem_support_iff.mpr
    intro h
    exact hij (by simp [h])
  exact ((Nat.add_le_add_right (le_natDegree_of_ne_zero hij) j).trans (hD _ hj)).trans hDle
end
end K1_14_2_2_5
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_2_2_5
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 Polynomial
open scoped nonZeroDivisors
private def jetCoords : Seeds →+* Ambient :=
  (MvPolynomial.rename (fun i : Fin 2 => (Fin.castLE (by decide : 2 ≤ 4) i) + 2)).toRingHom
private def toODE : Seeds →+* ODE :=
  MvPolynomial.eval₂Hom
    ((Polynomial.C : FX[X] →+* ODE).comp (Polynomial.C : FX →+* FX[X]))
    ![(Polynomial.C : FX[X] →+* ODE) (Polynomial.X : FX[X]), (Polynomial.X : ODE)]
private theorem jetPlane_C (f : FX[X]) :
    jetPlaneIncl (C f) = ordinateIncl f := by
  have h : (rootIncl.comp toRoot).comp (Polynomial.mapRingHom MvPolynomial.C) =
      ordinateIncl := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [ordinateIncl, rootIncl, toRoot, rootSeeds]
    · simp [ordinateIncl, rootIncl, toRoot]
  simpa [jetPlaneIncl, toJet, fixedIncl, K1_14_3.fixedEmbedding] using
    RingHom.congr_fun h f
private theorem jetPlane_X : jetPlaneIncl (Polynomial.X : ODE) = MvPolynomial.X 3 := by
  change ((Polynomial.X : ODE).map (Polynomial.mapRingHom MvPolynomial.C)).eval₂
    (rootIncl.comp toRoot) (MvPolynomial.X 3) = _
  rw [Polynomial.map_X, Polynomial.eval₂_X]
private theorem jetCoords_eq : jetCoords = jetPlaneIncl.comp toODE := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [jetCoords, toODE, jetPlane_C, ordinateIncl]
  · intro i
    fin_cases i <;> simp [jetCoords, toODE, jetPlane_C, jetPlane_X, ordinateIncl]
private theorem jetCoords_injective : Function.Injective jetCoords :=
  MvPolynomial.rename_injective _ (by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | contradiction)
private abbrev ParentField (I : Ideal Ambient) := FractionRing (Ambient ⧸ I)
private def parentMap (I : Ideal Ambient) : Ambient →+* ParentField I := by
  let q : Ambient →+* (Ambient ⧸ I) := Ideal.Quotient.mk I
  let f : (Ambient ⧸ I) →+* ParentField I := algebraMap _ _
  exact f.comp q
private theorem comap_ne_bot {I : Ideal Ambient} (hI : Active I) (hn : ¬ dual I) :
    I.comap jetPlaneIncl ≠ ⊥ := by
  intro hz
  have : I.IsPrime := hI.prime
  let q := parentMap I
  have hq : Function.Injective ((Ideal.Quotient.mk I).comp jetCoords) := by
    have hjet : Function.Injective ((Ideal.Quotient.mk I).comp jetPlaneIncl) := by
      apply (RingHom.injective_iff_ker_eq_bot _).2
      simpa [← RingHom.comap_ker, Ideal.mk_ker] using hz
    rw [jetCoords_eq, ← RingHom.comp_assoc]
    refine hjet.comp ?_
    intro x y hxy
    apply jetCoords_injective
    rw [jetCoords_eq]
    exact congrArg jetPlaneIncl hxy
  have hj : Function.Injective (q.comp jetCoords) :=
    (IsFractionRing.injective (Ambient ⧸ I) (ParentField I)).comp hq
  let t : SeedField →+* ParentField I := IsFractionRing.lift hj
  let e : FibreRing →+* ParentField I :=
    MvPolynomial.eval₂Hom t ![q (MvPolynomial.X 0), q (MvPolynomial.X 1)]
  have hC (a : FX) : t (algebraMap FX SeedField a) = q (MvPolynomial.C a) := by
    rw [IsScalarTower.algebraMap_apply FX Seeds SeedField]
    simp [t, jetCoords]
  have hX (i : Fin 2) : t (generic i) = q (MvPolynomial.X
      (Fin.castLE (by decide : 2 ≤ 4) i + 2)) := by
    simp [t, generic, jetCoords]
  have he : e.comp mapGenericJets = q := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simpa [e, mapGenericJets] using hC c
    · intro i
      fin_cases i <;> simp [e, mapGenericJets, hX]
  have : Module.Finite SeedField (OverJets I) := hI.jet_finite
  have hzero : Module.finrank SeedField (OverJets I) = 0 := Nat.eq_zero_of_not_pos hn
  have : Subsingleton (OverJets I) :=
    (Module.finrank_eq_zero_iff_of_free SeedField (OverJets I)).mp hzero
  have htop : (1 : FibreRing) ∈ I.map mapGenericJets :=
    Ideal.Quotient.eq_zero_iff_mem.mp (Subsingleton.elim _ _)
  have hle : I.map mapGenericJets ≤ RingHom.ker e := by
    rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker, he]
    intro x hx
    change q x = 0
    simp [q, parentMap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  have hbad : e 1 = 0 := RingHom.mem_ker.mp (hle htop)
  rw [map_one] at hbad
  exact (one_ne_zero : (1 : ParentField I) ≠ 0) hbad
attribute [local instance] Polynomial.algebra in
theorem jet_image_principal {I : Ideal Ambient} (hI : Active I) (hn : ¬ dual I) :
    ∃ G : ODE, G ≠ 0 ∧ I.comap jetPlaneIncl = Ideal.span {G} := by
  let P := I.comap jetPlaneIncl
  have : I.IsPrime := hI.prime
  have : P.IsPrime := Ideal.comap_isPrime jetPlaneIncl I
  let F := FractionRing (FX[X])
  let M : Submonoid ODE := (nonZeroDivisors (FX[X])).map (Polynomial.C : FX[X] →+* ODE)
  have := Polynomial.isLocalization (nonZeroDivisors (FX[X])) F
  have hdisj : Disjoint (M : Set ODE) (P : Set ODE) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ h
    change jetPlaneIncl (C a) ∈ I at h
    rw [jetPlane_C] at h
    have hq : ((Ideal.Quotient.mk I).comp ordinateIncl) a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr h
    exact (mem_nonZeroDivisors_iff_ne_zero.mp ha)
      (hI.ordinate_dominant (hq.trans (map_zero _).symm))
  let Q := P.map (algebraMap ODE F[X])
  have : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M F[X] P inferInstance hdisj
  have hle₀ := Ideal.height_le_ringKrullDim_of_isPrime (I := Q)
  have hdim : ringKrullDim F[X] = 1 := by simp [ringKrullDim_eq_zero_of_field]
  rw [hdim] at hle₀
  have hle : P.height ≤ 1 := by
    rw [← IsLocalization.height_map_of_disjoint (S := F[X]) M P hdisj]
    exact WithBot.coe_le_coe.mp hle₀
  have hp : P ≠ ⊥ := comap_ne_bot hI hn
  have hone : 1 ≤ P.height := by
    simpa using Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hp)
  obtain ⟨G, hG⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one
    (le_antisymm hle hone)).principal
  refine ⟨G, ?_, hG⟩
  intro hzero
  exact hp (by simpa [hzero] using hG)
end
end K1_14_2_2_5
end
section
namespace K1_14_2_2_5
noncomputable section
open K1_14_2 K1_14_2_2 Polynomial
open scoped BigOperators
private theorem caps_one : ODECaps (1 : ODE) 0 0 := by
  refine ⟨one_ne_zero, by simp, ?_⟩
  intro j i h
  by_cases hj : j = 0
  · subst j
    by_cases hi : i = 0
    · simp [hi]
    · simp [coeff_one, hi] at h
  · simp [coeff_one, hj] at h
private theorem caps_mul {F G : ODE} {B J B' J' : ℕ}
    (hF : ODECaps F B J) (hG : ODECaps G B' J') :
    ODECaps (F * G) (B + B') (J + J') := by
  classical
  refine ⟨mul_ne_zero hF.1 hG.1, natDegree_mul_le_of_le hF.2.1 hG.2.1, ?_⟩
  intro j i h
  by_contra! hdeg
  apply h
  rw [coeff_mul, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro v hv
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro y hy
  have hv' := Finset.HasAntidiagonal.mem_antidiagonal.mp hv
  have hy' := Finset.HasAntidiagonal.mem_antidiagonal.mp hy
  by_cases h1 : (F.coeff v.1).coeff y.1 = 0
  · rw [h1, zero_mul]
  by_cases h2 : (G.coeff v.2).coeff y.2 = 0
  · rw [h2, mul_zero]
  have hF' := hF.2.2 _ _ h1
  have hG' := hG.2.2 _ _ h2
  omega
theorem product_caps {α : Type*} (S : Finset α) (g : α → ODE) (b j : α → ℕ)
    (h : ∀ i ∈ S, ODECaps (g i) (b i) (j i)) :
    ODECaps (∏ i ∈ S, g i) (∑ i ∈ S, b i) (∑ i ∈ S, j i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using caps_one
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    exact caps_mul (h _ (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
theorem product_fixedOn {α : Type*} {S : Finset α} {a : α} (ha : a ∈ S)
    (g : α → ODE) {I : Ideal Ambient} (h : fixedOn (g a) I) :
    fixedOn (∏ i ∈ S, g i) I := by
  obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem g ha
  change jetPlaneIncl (∏ i ∈ S, g i) ∈ I
  rw [hq, map_mul, mul_comm]
  exact I.mul_mem_left _ h
end
end K1_14_2_2_5
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_2_2_5
noncomputable section
open K1_14_2 K1_14_2_2 Polynomial
open scoped BigOperators
def c1 : Prop :=
  ∀ (I : Ideal Ambient) (G : ODE), Active I → G ≠ 0 →
    I.comap jetPlaneIncl = Ideal.span {G} →
    Function.Injective (seedLineLift I)
def c2 : Prop :=
  ∀ (I : Ideal Ambient) (G : ODE),
    I.comap jetPlaneIncl = Ideal.span {G} → Function.Injective (seedLineLift I) →
    (∃ f : (SectionField[X] ⧸ Ideal.span {ordinatePolynomial G}) →ₗ[SectionField]
      OverOrdinate I, Function.Injective f) ∧
    (∃ f : (SectionField[X] ⧸ Ideal.span {mixedPolynomial G}) →ₗ[SectionField]
      OverMixed I, Function.Injective f)
private theorem parent_caps (h1 : c1) (h2 : c2) {I : Ideal Ambient}
    (hI : Active I) (hn : ¬ dual I) :
    ∃ G : ODE, ODECaps G (sectionDegree I 2) (sectionDegree I 1) ∧ fixedOn G I := by
  obtain ⟨G, hG, hi⟩ := jet_image_principal hI hn
  obtain ⟨⟨f, hf⟩, ⟨g, hg⟩⟩ := h2 I G hi (h1 I G hI hG hi)
  have := hI.ordinate_finite
  have := hI.mixed_finite
  have ho := LinearMap.finrank_le_finrank_of_injective (f := f) hf
  have hm := LinearMap.finrank_le_finrank_of_injective (f := g) hg
  rw [finrank_quotient_span_eq_natDegree, ordinatePolynomial_natDegree] at ho
  rw [finrank_quotient_span_eq_natDegree] at hm
  refine ⟨G, ⟨hG, ho, fun j i h => (mixedPolynomial_monomial_le hG h).trans hm⟩, ?_⟩
  change G ∈ I.comap jetPlaneIncl
  rw [hi]
  exact Ideal.subset_span rfl
theorem of_children (h1 : c1) (h2 : c2) : K1_14_2_2.c5 := by
  classical
  intro S hS hord hmix
  have hchoose (I : Ideal Ambient) :
      ∃ G : ODE, I ∈ S → ODECaps G (sectionDegree I 2) (sectionDegree I 1) ∧ fixedOn G I := by
    by_cases hI : I ∈ S
    · obtain ⟨G, hg⟩ := parent_caps h1 h2 (hS I hI).1 (hS I hI).2
      exact ⟨G, fun _ => hg⟩
    · exact ⟨1, fun h => (hI h).elim⟩
  choose G hG using hchoose
  have hprod : ODECaps (∏ I ∈ S, G I) (mass S 2) (mass S 1) :=
    product_caps S G (fun I => sectionDegree I 2) (fun I => sectionDegree I 1)
      (fun I hI => (hG I hI).1)
  refine ⟨∏ I ∈ S, G I, ⟨hprod.1, hprod.2.1.trans hord, ?_⟩,
    fun I hI => product_fixedOn hI G (hG I hI).2⟩
  intro j i h
  exact (hprod.2.2 j i h).trans hmix
end
end K1_14_2_2_5
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000
namespace K1_14_2_2_5_1
noncomputable section
open K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_5 Polynomial
private abbrev seedIncl : Seeds →+* Ambient := rootIncl.comp rootSeeds
private theorem seed_dominant {I : Ideal Ambient} (hI : Active I) :
    Function.Injective ((Ideal.Quotient.mk I).comp seedIncl) := by
  let q := (Ideal.Quotient.mk (I.map mapGenericSeed)).comp mapGenericSeed
  let e : SeedField →+* OverSeeds I := algebraMap SeedField (OverSeeds I)
  have he : q.comp seedIncl = e.comp (algebraMap Seeds SeedField) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply]
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply FX Seeds SeedField]
      simp [q, rootIncl, rootSeeds, mapGenericSeed]
      rfl
    · intro i
      fin_cases i <;> simp [q, seedIncl, rootIncl, rootSeeds, mapGenericSeed, e, generic] <;> rfl
  let : Nontrivial (OverSeeds I) := Module.nontrivial_of_finrank_pos hI.seed_size.1
  apply (injective_iff_map_eq_zero ((Ideal.Quotient.mk I).comp seedIncl)).2
  intro f hf
  have hmem : seedIncl f ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hf
  have hz : q (seedIncl f) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem mapGenericSeed hmem)
  have hzero : (e.comp (algebraMap Seeds SeedField)) f = 0 := by
    rw [← he]
    exact hz
  have hinj : Function.Injective (e.comp (algebraMap Seeds SeedField)) :=
    e.injective.comp (IsFractionRing.injective Seeds SeedField)
  exact hinj (hzero.trans (map_zero (e.comp (algebraMap Seeds SeedField))).symm)
private theorem jetPlane_C (f : FX[X]) :
    jetPlaneIncl (C f) = ordinateIncl f := by
  have h : (rootIncl.comp toRoot).comp (Polynomial.mapRingHom MvPolynomial.C) =
      ordinateIncl := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [ordinateIncl, rootIncl, toRoot, rootSeeds]
    · simp [ordinateIncl, rootIncl, toRoot]
  simpa [jetPlaneIncl, toJet, fixedIncl, K1_14_3.fixedEmbedding] using
    RingHom.congr_fun h f
private instance jetImagePrime (I : Ideal Ambient) [I.IsPrime] :
    (I.comap jetPlaneIncl).IsPrime :=
  (inferInstance : I.IsPrime).comap jetPlaneIncl
private abbrev JetField (I : Ideal Ambient) := FractionRing (JetImage I)
private abbrev ParentField (I : Ideal Ambient) := FractionRing (CoordinateRing I)
private def jetMap (I : Ideal Ambient) : ODE →+* JetField I :=
  (algebraMap (JetImage I) (JetField I)).comp (Ideal.Quotient.mk _)
private def parentMap (I : Ideal Ambient) : Ambient →+* ParentField I :=
  (algebraMap (CoordinateRing I) (ParentField I)).comp (Ideal.Quotient.mk I)
private def jetToParent (I : Ideal Ambient) [I.IsPrime] : JetField I →+* ParentField I :=
  IsFractionRing.lift (K := JetField I)
    (g := (algebraMap (CoordinateRing I) (ParentField I)).comp
      (Ideal.quotientMap I jetPlaneIncl le_rfl))
    ((IsFractionRing.injective (CoordinateRing I) (ParentField I)).comp
      Ideal.quotientMap_injective)
private theorem jetToParent_jetMap (I : Ideal Ambient) [I.IsPrime] (f : ODE) :
    jetToParent I (jetMap I f) = parentMap I (jetPlaneIncl f) := by
  simp [jetToParent, jetMap, parentMap, Ideal.quotientMap_mk]
private theorem ordinate_injective {I : Ideal Ambient} [I.IsPrime] (hI : Active I) :
    Function.Injective ((jetMap I).comp (C : FX[X] →+* ODE)) := by
  intro f g h
  apply hI.ordinate_dominant
  have h' := congrArg (jetToParent I) h
  simp only [RingHom.comp_apply, jetToParent_jetMap, jetPlane_C, parentMap] at h'
  exact IsFractionRing.injective (CoordinateRing I) (ParentField I) h'
private theorem jet_trdeg {I : Ideal Ambient} [I.IsPrime] (hI : Active I)
    {G : ODE} (hG : G ≠ 0) (hGI : G ∈ I.comap jetPlaneIncl) :
    Algebra.trdeg FX (JetField I) = 1 := by
  let : FaithfulSMul (FX[X]) (JetField I) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (ordinate_injective hI)
  let v := jetMap I (Polynomial.X : ODE)
  have hπ : (aeval v : ODE →ₐ[FX[X]] JetField I).toRingHom = jetMap I := by
    apply Polynomial.ringHom_ext
    · intro a
      change aeval v (C a) = _
      rw [aeval_C]
      rfl
    · change aeval v (Polynomial.X : ODE) = jetMap I (Polynomial.X : ODE)
      exact aeval_X v
  have hv : IsAlgebraic (FX[X]) v := by
    refine ⟨G, hG, ?_⟩
    change (aeval v : ODE →ₐ[FX[X]] JetField I).toRingHom G = 0
    rw [hπ]
    change algebraMap (JetImage I) (JetField I) (Ideal.Quotient.mk _ G) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hGI, map_zero]
  have hpoly (f : ODE) : IsAlgebraic (FX[X]) (jetMap I f) := by
    rw [← hπ]
    exact (Algebra.isAlgebraic_adjoin_singleton_iff.mpr hv) _
      (Polynomial.aeval_mem_adjoin_singleton _ _)
  let : Algebra.IsAlgebraic (FX[X]) (JetField I) := by
    constructor
    intro z
    obtain ⟨f, g, -, rfl⟩ := IsFractionRing.div_surjective (JetImage I) z
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective g
    rw [div_eq_mul_inv]
    exact (hpoly f).mul (hpoly g).inv
  rw [← trdeg_add_eq FX (FX[X]),
    Polynomial.trdeg_of_isDomain, trdeg_eq_zero (R := FX[X]), add_zero]
private theorem jetBase_toParent (I : Ideal Ambient) [I.IsPrime] (a : FX) :
    jetToParent I (algebraMap FX (JetField I) a) = parentMap I (MvPolynomial.C a) := by
  change jetToParent I (jetMap I (C (C a))) = _
  rw [jetToParent_jetMap, jetPlane_C]
  simp [ordinateIncl]
private theorem not_both_algebraic {k M E : Type} [Field k] [Field M] [Field E]
    [Algebra k M] [Algebra M E] (hM : Algebra.trdeg k M = 1) (x y : E)
    (hseed : Function.Injective
      (MvPolynomial.eval₂Hom ((algebraMap M E).comp (algebraMap k M)) (![x, y] : Fin 2 → E))) :
    ¬ (IsAlgebraic M x ∧ IsAlgebraic M y) := by
  intro h
  let F := algebraicClosure M E
  let : Algebra k F := ((algebraMap M F).comp (algebraMap k M)).toAlgebra
  let : IsScalarTower k M F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let t : Fin 2 → F :=
    ![⟨x, mem_algebraicClosure_iff.mpr h.1⟩, ⟨y, mem_algebraicClosure_iff.mpr h.2⟩]
  let f : MvPolynomial (Fin 2) k →ₐ[k] F := MvPolynomial.aeval t
  have he : F.subtype.comp f.toRingHom =
      MvPolynomial.eval₂Hom ((algebraMap M E).comp (algebraMap k M)) ![x, y] := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change F.subtype (MvPolynomial.aeval t (MvPolynomial.C a)) = _
      rw [MvPolynomial.aeval_C, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
      rfl
    · intro i
      change F.subtype (MvPolynomial.aeval t (MvPolynomial.X i)) = _
      rw [MvPolynomial.aeval_X, MvPolynomial.eval₂Hom_X']
      fin_cases i <;> rfl
  have hinj : Function.Injective f := by
    intro p q hpq
    apply hseed
    rw [← he]
    exact congrArg F.subtype hpq
  have htr := trdeg_le_of_injective f hinj
  rw [← trdeg_add_eq k M (A := F), hM, trdeg_eq_zero (R := M), add_zero,
    MvPolynomial.trdeg_of_isDomain] at htr
  have hbad : (2 : Cardinal.{0}) ≤ 1 := by
    simpa only [Cardinal.lift_id, Cardinal.mk_fin, Nat.cast_ofNat] using htr
  have hn : (2 : ℕ) ≤ 1 := by exact_mod_cast hbad
  omega
theorem proof : K1_14_2_2_5.c1 := by
  intro I G hI hG he
  let : I.IsPrime := hI.prime
  let : Algebra (JetField I) (ParentField I) := (jetToParent I).toAlgebra
  let : Infinite (JetField I) := Infinite.of_injective _ (ordinate_injective hI)
  have hGI : G ∈ I.comap jetPlaneIncl := by
    rw [he]
    exact Ideal.subset_span rfl
  let x := parentMap I (MvPolynomial.X 0)
  let y := parentMap I (MvPolynomial.X 1)
  let m : JetImage I →+* JetField I := algebraMap _ _
  let n : CoordinateRing I →+* ParentField I := algebraMap _ _
  have hcomp : (MvPolynomial.map n).comp (seedLineLift I) =
      (genericLine (M := JetField I) x y).comp (MvPolynomial.map m) := by
    apply MvPolynomial.ringHom_ext
    · intro b
      simp [seedLineLift, genericLine, m, n, jetToParent, RingHom.algebraMap_toAlgebra]
    · intro i
      fin_cases i <;> simp [seedLineLift, genericLine, x, y, n, parentMap]
  have hseed : MvPolynomial.eval₂Hom
      ((algebraMap (JetField I) (ParentField I)).comp (algebraMap FX (JetField I)))
        (![x, y] : Fin 2 → ParentField I) = (parentMap I).comp seedIncl := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
      change jetToParent I (algebraMap FX (JetField I) a) =
        parentMap I (seedIncl (MvPolynomial.C a))
      rw [jetBase_toParent]
      simp [seedIncl, rootIncl, rootSeeds]
    · intro i
      fin_cases i <;> simp [x, y, seedIncl, rootIncl, rootSeeds]
  have hseed_inj : Function.Injective (MvPolynomial.eval₂Hom
      ((algebraMap (JetField I) (ParentField I)).comp (algebraMap FX (JetField I)))
        (![x, y] : Fin 2 → ParentField I)) := by
    rw [hseed]
    exact (IsFractionRing.injective (CoordinateRing I) (ParentField I)).comp (seed_dominant hI)
  have ht : ¬ (IsAlgebraic (JetField I) x ∧ IsAlgebraic (JetField I) y) :=
    not_both_algebraic (k := FX) (M := JetField I) (E := ParentField I)
      (jet_trdeg hI hG hGI) x y hseed_inj
  have hinj : Function.Injective ((MvPolynomial.map n).comp (seedLineLift I)) := by
    rw [hcomp]
    exact (genericLine_injective (M := JetField I) (E := ParentField I) x y ht).comp
      (MvPolynomial.map_injective m (IsFractionRing.injective (JetImage I) (JetField I)))
  intro p q hpq
  apply hinj
  exact congrArg (MvPolynomial.map n) hpq
end
end K1_14_2_2_5_1
end
section
set_option autoImplicit false
namespace K1_14_2_2_4_5
noncomputable section
open K1_14 K1_14_2 K1_14_2_2
abbrev Plane (F : Type) [Field F] := MvPolynomial (Fin 2) F
abbrev PlaneSection {F : Type} [Field F] (φ : Ambient →+* Plane F) (I : Ideal Ambient) :=
  Plane F ⧸ I.map φ
abbrev RowIdeal (P Q : Jet) : Ideal Ambient := Ideal.span {toJet P, toJet Q}
abbrev PlaneIntersection {F : Type} [Field F] (f g : Plane F) :=
  Plane F ⧸ Ideal.span {f, g}
def lineValues (mixed : Bool) : Fin 4 → Plane SectionField :=
  ![MvPolynomial.C (sliceParameter 2) - MvPolynomial.C (sliceParameter 0) * MvPolynomial.X 0,
    MvPolynomial.X 0,
    if mixed then
      MvPolynomial.C (sliceParameter 3) - MvPolynomial.C (sliceParameter 1) * MvPolynomial.X 1
    else MvPolynomial.C (sliceParameter 3),
    MvPolynomial.X 1]
def lineMap (mixed : Bool) : Ambient →+* Plane SectionField :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp (algebraMap FX SectionField)) (lineValues mixed)
structure SectionChart (F : Type) [Field F] (φ : Ambient →+* Plane F) (k : Fin 4) : Prop where
  flat : letI := φ.toAlgebra; Module.Flat Ambient (Plane F)
  finite_rank : ∀ I : Ideal Ambient, Active I →
    Module.Finite F (PlaneSection φ I) ∧
      Module.finrank F (PlaneSection φ I) = sectionDegree I k
  prime_over : ∀ I : Ideal Ambient, I.IsPrime → I.map φ ≠ ⊤ →
    (I.map φ).IsPrime ∧ (I.map φ).comap φ = I
  relPrime : ∀ a b : Ambient, IsRelPrime a b → IsRelPrime (φ a) (φ b)
end
end K1_14_2_2_4_5
end
section
set_option backward.isDefEq.respectTransparency false
namespace K1_14_2_2_4_3
open K1_14 K1_14_2 K1_14_2_2 Polynomial
noncomputable def ordinaryIncl : Equation →+* Ambient := toJet.comp C
@[simp] theorem ordinaryIncl_apply (f : Equation) :
    ordinaryIncl f = toJet (C f) := rfl
abbrev ParentLocal (I : Ideal Ambient) [I.IsPrime] := Localization.AtPrime I
noncomputable abbrev parentLocalMap (I : Ideal Ambient) [I.IsPrime] :
    Ambient →+* ParentLocal I := algebraMap Ambient (ParentLocal I)
noncomputable def jetImageIdeal (I : Ideal Ambient) : Ideal Ambient :=
  (I.comap jetPlaneIncl).map jetPlaneIncl
noncomputable abbrev JetQuotient (I : Ideal Ambient) [I.IsPrime] :=
  let R := ParentLocal I
  letI : CommRing R := inferInstanceAs (CommRing (Localization.AtPrime I))
  let J : Ideal R := (jetImageIdeal I).map (parentLocalMap I)
  R ⧸ (J : Submodule R R)
noncomputable abbrev jetQuotientMap (I : Ideal Ambient) [I.IsPrime] :
    ParentLocal I →+* JetQuotient I := Ideal.Quotient.mk _
end K1_14_2_2_4_3
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
namespace K1_14_3_2_4
noncomputable section
open K1_14 K1_14_3 Polynomial
def sliceIdeal (s : Slice) (I : Ideal Jet) : Ideal SectionJet :=
  I.map sectionMap ⊔ Ideal.span (sectionEquations s)
abbrev PairSection (P Q : Jet) (s : Slice) :=
  SectionJet ⧸ sliceIdeal s (Ideal.span {P, Q})
abbrev Plane := MvPolynomial (Fin 2) SectionField
def parameter (i : Fin 4) : SectionField :=
  algebraMap (MvPolynomial (Fin 4) FX) SectionField (MvPolynomial.X i)
abbrev seedVar (i : Fin 2) : SectionJet := C (C (MvPolynomial.X i))
abbrev ordinateVar : SectionJet := C (Polynomial.X (R := SectionSeeds))
abbrev derivativeVar : SectionJet := Polynomial.X
def seedValues (s : Slice) : Fin 2 → Plane :=
  match s with
  | .seed => ![MvPolynomial.C (parameter 2), MvPolynomial.C (parameter 3)]
  | .ordinate | .mixed =>
      ![MvPolynomial.C (parameter 2) - MvPolynomial.C (parameter 0) * MvPolynomial.X 0,
        MvPolynomial.X 0]
  | .jets => MvPolynomial.X
def ordinateValue (s : Slice) : Plane :=
  match s with
  | .seed => MvPolynomial.X 0
  | .ordinate => MvPolynomial.C (parameter 3)
  | .mixed => MvPolynomial.C (parameter 3) - MvPolynomial.C (parameter 1) * MvPolynomial.X 1
  | .jets => MvPolynomial.C (parameter 2)
def derivativeValue (s : Slice) : Plane :=
  match s with
  | .seed | .ordinate | .mixed => MvPolynomial.X 1
  | .jets => MvPolynomial.C (parameter 3)
def sectionEval (s : Slice) : SectionJet →ₐ[SectionField] Plane where
  toRingHom := eval₂RingHom
    (eval₂RingHom (MvPolynomial.eval₂Hom MvPolynomial.C (seedValues s)) (ordinateValue s))
    (derivativeValue s)
  commutes' k := by
    change eval₂RingHom
      (eval₂RingHom (MvPolynomial.eval₂Hom MvPolynomial.C (seedValues s)) (ordinateValue s))
      (derivativeValue s) (C (C (MvPolynomial.C k))) = MvPolynomial.C k
    simp
def sectionRow (s : Slice) (P : Jet) : Plane :=
  sectionEval s (sectionMap P)
abbrev PlaneSection (F G : Plane) := Plane ⧸ Ideal.span {F, G}
def univariate : SectionField[X] →ₐ[SectionField] Plane :=
  Polynomial.aeval (MvPolynomial.X 0)
def BidegreeLE (F : Plane) (u b : ℕ) : Prop :=
  F.degreeOf 0 ≤ u ∧ F.degreeOf 1 ≤ b
end
end K1_14_3_2_4
end
