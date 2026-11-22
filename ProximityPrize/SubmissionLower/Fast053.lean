import ProximityPrize.SubmissionLower.Fast050
import ProximityPrize.SubmissionLower.SoloK1_13_1_1ArithmeticLogic
set_option autoImplicit true
section
namespace K1_14_3_7
noncomputable section
open K1_14 K1_14_3 Polynomial
open scoped Polynomial
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 8
private abbrev toSeed : Seeds →+* SeedField := algebraMap _ _
abbrev toClosure : SeedField →+* SeedClosure := algebraMap _ _
theorem toSeed_injective : Function.Injective toSeed :=
  IsFractionRing.injective Seeds SeedField
private theorem seedGeneric_injective : Function.Injective seedGeneric :=
  toClosure.injective.comp toSeed_injective
theorem pair_pow_le {S : Type*} [CommRing S] (I J : Ideal S) (n j : ℕ) :
    (I ⊔ J) ^ (n+j) ≤ I ^ n ⊔ J ^ (j+1) := by
  rw [← Ideal.add_eq_sup, add_pow, Ideal.sum_eq_sup]
  apply Finset.sup_le
  intro i hi
  by_cases hn : n ≤ i
  · exact Ideal.mul_le_left.trans
      (Ideal.mul_le_left.trans ((Ideal.pow_le_pow_right hn).trans le_sup_left))
  · refine Ideal.mul_le_left.trans
      (Ideal.mul_le_right.trans ((Ideal.pow_le_pow_right ?_).trans le_sup_right))
    omega
theorem leading_dvd_of_contact {S : Type*} [CommRing S]
    (a b : S) (G : Polynomial S) (k : ℕ)
    (h : G ∈ (Ideal.span ({C a, Polynomial.X - C b} : Set S[X])) ^ k) :
    a ^ (k - G.natDegree) ∣ G.leadingCoeff := by
  let j := G.natDegree
  change a ^ (k-j) ∣ G.coeff j
  by_cases hj : k ≤ j
  · simp [Nat.sub_eq_zero_of_le hj]
  let B : S[X] := Polynomial.X - C b
  have hpair : Ideal.span ({C a, B} : Set S[X]) =
      Ideal.span {C a} ⊔ Ideal.span {B} := by
    rw [← Ideal.span_union, Set.singleton_union]
  change G ∈ Ideal.span ({C a, B} : Set S[X]) ^ k at h
  rw [hpair] at h
  have hle := pair_pow_le (Ideal.span ({C a} : Set S[X])) (Ideal.span {B}) (k-j) j
  rw [Nat.sub_add_cancel (by omega : j ≤ k)] at hle
  have hsum : G ∈ Ideal.span ({C (a ^ (k-j))} : Set S[X]) ⊔
      Ideal.span {B ^ (j+1)} := by
    simpa only [Ideal.span_singleton_pow, ← C_pow] using hle h
  obtain ⟨r, hr, s, hs, hrs⟩ := Submodule.mem_sup.mp hsum
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton.mp hr
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hs
  let I : Ideal S := Ideal.span {a ^ (k-j)}
  let π := Ideal.Quotient.mk I
  let φ := Polynomial.mapRingHom π
  have hπ : π (a ^ (k-j)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  let B' : (S ⧸ I)[X] := Polynomial.X - C (π b)
  have hφC : φ (C (a ^ (k-j))) = 0 := by
    change (C (a ^ (k-j))).map π = 0
    rw [Polynomial.map_C, hπ, C_0]
  have hφB : φ B = B' := by
    change B.map π = B'
    simp only [B, B', Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have hmap : φ G = B' ^ (j+1) * φ d := by
    rw [← hrs, he, hd, map_add, map_mul, hφC, zero_mul, zero_add, map_mul, map_pow, hφB]
  have hzero : φ G = 0 := by
    by_contra hn
    have : Nontrivial (S ⧸ I) := by
      rcases subsingleton_or_nontrivial (S ⧸ I) with hsub | hnon
      · have := hsub
        exact False.elim (hn (Subsingleton.elim _ _))
      · exact hnon
    have hm : B'.Monic := monic_X_sub_C _
    have hdeg : (B' ^ (j+1)).natDegree = j+1 := by
      rw [hm.natDegree_pow, show B'.natDegree = 1 from natDegree_X_sub_C _, mul_one]
    have hlt : (φ G).natDegree < (B' ^ (j+1)).natDegree := by
      rw [hdeg]
      exact Nat.lt_succ_of_le (natDegree_map_le (p := G) (f := π))
    exact (hm.pow _).not_dvd_of_natDegree_lt hn hlt ⟨φ d, hmap⟩
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change π (G.coeff j) = 0
  rw [← coeff_map, show G.map π = 0 from hzero, coeff_zero]
theorem fibre_leading_dvd {q : Surface} {y v : SeedClosure}
    (hq : OnSeedFibre q y v) {P : Jet} {k : ℕ} (h : OrderAt q P k) :
    (Polynomial.X - C y) ^ (k - P.natDegree) ∣ P.leadingCoeff.map seedGeneric := by
  have hi : Function.Injective (Polynomial.mapRingHom seedGeneric) :=
    Polynomial.map_injective _ seedGeneric_injective
  have hc := leading_dvd_of_contact (Polynomial.X - C y) (C v) (fibreRow P) k (h y v hq)
  unfold fibreRow at hc
  rw [natDegree_map_eq_of_injective hi, leadingCoeff_map_of_injective hi] at hc
  exact hc
theorem minpoly_pow_dvd {y : SeedClosure} (hy : IsSeparable SeedField y)
    {n : ℕ} {g : SeedField[X]} (h : (Polynomial.X - C y) ^ n ∣ g.map toClosure) :
    minpoly SeedField y ^ n ∣ g := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
    by_cases hg : g = 0
    · simp [hg]
    have hgmap : g.map toClosure ≠ 0 :=
      (Polynomial.map_ne_zero_iff toClosure.injective).mpr hg
    have hlin : Polynomial.X - C y ∣ g.map toClosure :=
      (dvd_pow_self _ (by omega : n+1 ≠ 0)).trans h
    have hroot : (g.map toClosure).IsRoot y := dvd_iff_isRoot.mp hlin
    have hmin : minpoly SeedField y ∣ g := by
      apply minpoly.dvd
      simpa only [IsRoot.def, eval_map, aeval_def] using hroot
    obtain ⟨g', rfl⟩ := hmin
    have hsep : ((minpoly SeedField y).map toClosure).Separable :=
      Polynomial.Separable.map hy
    have hle := rootMultiplicity_le_one_of_separable hsep y
    rw [Polynomial.map_mul] at hgmap h
    have hmul := (le_rootMultiplicity_iff (a := y) hgmap).mpr h
    rw [rootMultiplicity_mul hgmap] at hmul
    have hg'map : g'.map toClosure ≠ 0 := right_ne_zero_of_mul hgmap
    have hrest : (Polynomial.X - C y) ^ n ∣ g'.map toClosure :=
      (le_rootMultiplicity_iff (a := y) hg'map).mp (by omega)
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih hrest)
@[instance_reducible] private def seedGCD : NormalizedGCDMonoid Seeds := by
  let : UniqueFactorizationMonoid Seeds := MvPolynomial.uniqueFactorizationMonoid (σ := Fin 2)
  let := UniqueFactorizationMonoid.strongNormalizationMonoid (α := Seeds)
  exact UniqueFactorizationMonoid.toNormalizedGCDMonoid Seeds
theorem primitive_model (g : SeedField[X]) (hg : g ≠ 0) :
    ∃ f : Equation, f.IsPrimitive ∧ Associated (f.map toSeed) g := by
  classical
  let := seedGCD
  let D : Equation := IsLocalization.integerNormalization (nonZeroDivisors Seeds) g
  obtain ⟨a, ha, hD⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors Seeds) g
  have hD0 : D ≠ 0 :=
    (IsFractionRing.integerNormalization_eq_zero_iff (A := Seeds) (p := g)).not.mpr hg
  have hcontent : IsUnit (C (toSeed D.content)) := by
    apply isUnit_C.mpr
    exact ((map_ne_zero_iff toSeed toSeed_injective).mpr (content_eq_zero_iff.not.mpr hD0)).isUnit
  have ha' : IsUnit (C (toSeed a)) :=
    isUnit_C.mpr ((map_ne_zero_iff toSeed toSeed_injective).mpr (nonZeroDivisors.ne_zero ha)).isUnit
  have hscale : C (toSeed D.content) * D.primPart.map toSeed = C (toSeed a) * g := by
    calc
      _ = D.map toSeed := by
        rw [← Polynomial.map_C, ← Polynomial.map_mul, ← D.eq_C_content_mul_primPart]
      _ = _ := by
        simpa only [Algebra.smul_def, Polynomial.algebraMap_apply] using hD
  refine ⟨D.primPart, D.isPrimitive_primPart, ?_⟩
  have hunit : Associated (C (toSeed a) * g) g := associated_unit_mul_left _ _ ha'
  rw [← hscale] at hunit
  exact (associated_unit_mul_right _ _ hcontent).trans hunit
theorem eval_at_fibre_C (f : Equation) (y v : SeedClosure) :
    seedFibreEval y v (C f) = aeval y (f.map toSeed) := by
  change (eval₂RingHom (eval₂RingHom seedGeneric y) v) (C f) = _
  rw [coe_eval₂RingHom, eval₂_C, coe_eval₂RingHom, aeval_def, eval₂_map]
  rfl
theorem proof : K1_14_3.c7 := by
  classical
  intro qs hqs hparents
  choose y v hpoint hy _hv using fun q : ↥qs => (hparents q q.property).seed_side
  let m (q : ↥qs) := minpoly SeedField (y q)
  let factors : Finset (SeedField[X]) := qs.attach.image m
  have hmem (q : ↥qs) : m q ∈ factors :=
    Finset.mem_image.mpr ⟨q, Finset.mem_attach _ _, rfl⟩
  have hpre {u : SeedField[X]} (hu : u ∈ factors) : ∃ q : ↥qs, m q = u := by
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hu
    exact ⟨q, hq⟩
  have hmonic (u : SeedField[X]) (hu : u ∈ factors) : u.Monic := by
    obtain ⟨q, rfl⟩ := hpre hu
    exact minpoly.monic (hy q).isIntegral
  have hirr (u : SeedField[X]) (hu : u ∈ factors) : Irreducible u := by
    obtain ⟨q, rfl⟩ := hpre hu
    exact minpoly.irreducible (hy q).isIntegral
  have hpair (u : SeedField[X]) (hu : u ∈ factors) (w : SeedField[X]) (hw : w ∈ factors)
      (hne : u ≠ w) : IsCoprime u w := by
    apply (hirr u hu).coprime_iff_not_dvd.mpr
    intro hd
    exact hne (eq_of_monic_of_associated (hmonic u hu) (hmonic w hw)
      (associated_of_dvd_dvd hd ((hirr u hu).dvd_symm (hirr w hw) hd)))
  let g : SeedField[X] := ∏ u ∈ factors, u
  have hg : g ≠ 0 := (monic_prod_of_monic _ _ hmonic).ne_zero
  have hsep : g.Separable := by
    apply separable_prod' hpair
    intro u hu
    obtain ⟨q, rfl⟩ := hpre hu
    exact hy q
  have hm_dvd (q : ↥qs) : m q ∣ g := Finset.dvd_prod_of_mem id (hmem q)
  obtain ⟨f, hprim, hassoc⟩ := primitive_model g hg
  have hfmap : f.map toSeed ≠ 0 :=
    (Polynomial.map_ne_zero_iff toSeed_injective).mpr hprim.ne_zero
  refine ⟨f, ⟨?_, hprim, hsep.of_dvd hassoc.dvd, ?_, ?_⟩⟩
  · obtain ⟨q, hq⟩ := hqs
    have hdeg := natDegree_le_of_dvd ((hm_dvd ⟨q, hq⟩).trans hassoc.dvd') hfmap
    rw [natDegree_map_eq_of_injective toSeed_injective] at hdeg
    exact (hirr _ (hmem ⟨q, hq⟩)).natDegree_pos.trans_le hdeg
  · intro q hq
    let q' : ↥qs := ⟨q, hq⟩
    rw [← hpoint q', RingHom.mem_ker, eval_at_fibre_C]
    exact minpoly.dvd_iff.mp ((hm_dvd q').trans hassoc.dvd')
  · intro P k _ horder
    let n := k - P.natDegree
    have hdiv : g ^ n ∣ P.leadingCoeff.map toSeed := by
      rw [show g ^ n = ∏ u ∈ factors, u ^ n from (Finset.prod_pow factors n id).symm]
      apply Finset.prod_dvd_of_coprime
      · intro u hu w hw hne
        exact (hpair u hu w hw hne).pow
      · intro u hu
        obtain ⟨q, rfl⟩ := hpre hu
        have hc := fibre_leading_dvd (hpoint q) (horder q q.property)
        rw [show seedGeneric = toClosure.comp toSeed from rfl, ← Polynomial.map_map] at hc
        exact minpoly_pow_dvd (hy q) hc
    let := seedGCD
    have hpow (e : ℕ) : (f ^ e).IsPrimitive := by
      induction e with
      | zero => simpa only [pow_zero] using (isPrimitive_one : (1 : Equation).IsPrimitive)
      | succ e ih => rw [pow_succ]; exact ih.mul hprim
    apply (hpow n).dvd_of_fraction_map_dvd_fraction_map (K := SeedField)
    rw [Polynomial.map_pow]
    exact hassoc.pow_pow.dvd.trans hdiv
end
end K1_14_3_7
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
namespace K1_14_3R_3
noncomputable section
open K1_14 K1_14_3 Polynomial MvPolynomial
open private dim_eq_Hilbert from ProximityPrize.SubmissionLower.Pack_K1_13_6_1_4Geometry
private abbrev Coordinates := Option (Option (Fin 2))
private abbrev Ambient := MvPolynomial Coordinates FX
private def toJet : Ambient ≃+* Jet :=
  (optionEquivLeft FX (Option (Fin 2))).toRingEquiv.trans
    (Polynomial.mapEquiv (optionEquivLeft FX (Fin 2)).toRingEquiv)
theorem degree_of_height_two {k σ : Type*} [Field k] [Finite σ]
    (A : Ideal (MvPolynomial σ k)) [A.IsPrime] (hA : A.height = 2) :
    (affineHilbertPolynomial A).natDegree + 2 = Nat.card σ := by
  have hA₀ : A ≠ ⊥ := Ideal.height_eq_zero_iff_eq_bot.not.mp (by simp [hA])
  obtain ⟨f, hf, hpf⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot (I := A) inferInstance hA₀
  let D := Ideal.span ({f} : Set (MvPolynomial σ k))
  let : D.IsPrime := (Ideal.span_singleton_prime hpf.ne_zero).mpr hpf
  have hDmin : D ∈ (Ideal.span ({f} : Set (MvPolynomial σ k))).minimalPrimes := by
    change D ∈ D.minimalPrimes
    rw [Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton D
  have hDh : D.height = 1 :=
    (Ideal.height_span_singleton_le_one hpf.not_isUnit).antisymm
      (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr
        (fun h => hpf.ne_zero (Ideal.span_singleton_eq_bot.mp h))))
  have hDA : D < A := lt_of_le_of_ne ((Ideal.span_singleton_le_iff_mem A).mpr hf) (by
    intro he
    rw [he, hA] at hDh
    exact (by decide : (2 : ℕ∞) ≠ 1) hDh)
  obtain ⟨g, hg, hgD⟩ := SetLike.exists_of_lt hDA
  have hAmin : A ∈ (D ⊔ Ideal.span {g}).minimalPrimes := by
    refine ⟨⟨inferInstance, sup_le hDA.le ((Ideal.span_singleton_le_iff_mem A).mpr hg)⟩, ?_⟩
    intro B hB hBA
    let : B.IsPrime := hB.1
    by_contra hne
    have hDB : D < B := lt_of_le_of_ne (le_sup_left.trans hB.2) (by
      intro he
      exact hgD (he ▸ hB.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))))
    have hBh : 2 ≤ B.height := by
      simpa only [hDh, show (1 : ℕ∞) + 1 = 2 by decide] using
        Ideal.height_add_one_le_of_lt_of_isPrime hDB
    have hAh := (add_le_add_left hBh 1).trans
      (Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_not_ge hBA hne))
    rw [hA] at hAh
    exact (by decide : ¬ (2 : ℕ∞) + 1 ≤ 2) hAh
  have hdegD :=
    natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton
      hpf.ne_zero hDmin
  have hdegA := principalCut_natDegree_affineHilbertPolynomial_add_one hgD hAmin
  omega
theorem cutCurve {q : Surface} {P : Jet} (hq : q.asIdeal.height = 2) (hP : P ∉ q.asIdeal)
    {R : Ideal Jet} (hR : R ∈ (cutIdeal q P).minimalPrimes) : IsCutCurve R := by
  let e := toJet
  let A := q.asIdeal.comap e
  let B := R.comap e
  let : A.IsPrime := Ideal.IsPrime.comap e
  let : R.IsPrime := hR.isPrime
  let : B.IsPrime := Ideal.IsPrime.comap e
  have hA : A.height = 2 := (e.height_comap _).trans hq
  have hP' : e.symm P ∉ A := by
    intro h
    change e (e.symm P) ∈ q.asIdeal at h
    rw [e.apply_symm_apply] at h
    exact hP h
  have hcomap (I : Ideal Jet) : I.comap e = I.map e.symm := by
    simpa only [RingEquiv.symm_symm] using Ideal.comap_symm (I := I) e.symm
  have hEq : (cutIdeal q P).comap e = A ⊔ Ideal.span {e.symm P} := by
    rw [hcomap, cutIdeal, Ideal.map_sup, Ideal.map_span, Set.image_singleton, ← hcomap]
  have hB : B ∈ (A ⊔ Ideal.span {e.symm P}).minimalPrimes := by
    rw [← hEq]
    exact Ideal.minimalPrimes_comap_of_surjective (f := (e : Ambient →+* Jet)) e.surjective hR
  have hdeg := principalCut_natDegree_affineHilbertPolynomial_add_one hP' hB
  have hdA := degree_of_height_two A hA
  have hcard : Nat.card Coordinates = 4 := by
    simp [Coordinates, Nat.card_eq_fintype_card]
  have hdB : (affineHilbertPolynomial B).natDegree = 1 := by
    change (affineHilbertPolynomial A).natDegree + 2 = Nat.card Coordinates at hdA
    omega
  let lift : (Ambient ⧸ B) ≃+* (Jet ⧸ R) :=
    Ideal.quotientEquiv B R e (Ideal.map_comap_eq_self_of_equiv e R).symm
  exact ⟨hR.isPrime, lift.ringKrullDim.symm.trans (by simp [dim_eq_Hilbert B, hdB])⟩
end
end K1_14_3R_3
end
section
namespace K1_13_6_3
noncomputable section
open K1_13 K1_13_6 Polynomial
open scoped BigOperators
abbrev CoeffRing := MvPolynomial (Fin taylorLength) Geom
abbrev FreshCoeffRing := MvPolynomial (Fin taylorLength) GeoField
abbrev CoeffIdeal := Ideal CoeffRing
abbrev JetIdeal := Ideal GeoJets
abbrev dimension {k σ : Type*} [Field k] [Finite σ] (P : Ideal (MvPolynomial σ k)) :=
  (MvPolynomial.affineHilbertPolynomial P).natDegree
def geomConstants : Geom →+* GeoField := genericCoeffs.comp Polynomial.C
def genericArgument : GeoField := genericCoeffs Polynomial.X
def coeffPoint (S : Geom[X]) (i : Fin taylorLength) : Geom := S.coeff i
def jetLinear {k : Type*} [Field k] (a : k) (i : ℕ) :
    MvPolynomial (Fin taylorLength) k :=
  ∑ j : Fin taylorLength,
    MvPolynomial.C ((j.val.choose i : k) * a ^ (j.val - i)) * MvPolynomial.X j
def extendIdeal (A : CoeffIdeal) : Ideal FreshCoeffRing :=
  A.map (MvPolynomial.map geomConstants)
def freshJetMap : GeoJets →+* FreshCoeffRing :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => jetLinear genericArgument i.val)
def freshImage (A : CoeffIdeal) : JetIdeal :=
  (extendIdeal A).comap freshJetMap
def FreshRegular (f : Row 4) (A : CoeffIdeal) : Prop :=
  ∃ r : ℕ, toGeneric ((separant^[r]) f) ∈ freshImage A ∧
    toGeneric (separant ((separant^[r]) f)) ∉ freshImage A
def FreshBirational (A : CoeffIdeal) : Prop :=
  ∀ h : FreshCoeffRing, ∃ u v : GeoJets,
    freshJetMap v ∉ extendIdeal A ∧
    h * freshJetMap v - freshJetMap u ∈ extendIdeal A
abbrev JetField (P : JetIdeal) := FractionRing (GeoJets ⧸ P)
def onComponent (P : JetIdeal) : GeoJets →+* JetField P :=
  (algebraMap (GeoJets ⧸ P) (JetField P)).comp (Ideal.Quotient.mk P)
def componentConstants (P : JetIdeal) : Geom →+* JetField P :=
  ((onComponent P).comp MvPolynomial.C).comp geomConstants
def coefficientKernel {F : Type*} [Field F] (k : Geom →+* F) (U : F[X]) : CoeffIdeal :=
  RingHom.ker (MvPolynomial.eval₂Hom k (fun i => U.coeff i.val))
def trajectory {F : Type*} [Field F] (k : Geom →+* F) (P : Row 4) (U : F[X]) : F[X] :=
  MvPolynomial.eval₂ (Polynomial.mapRingHom k) (fun i => hasseDeriv i.val U) P
structure SimpleCut (g : Row 4) (surface P : JetIdeal) : Prop where
  proper : toGeneric (membershipTest g) ∉ surface
  minimal : (divisorIdeal surface (membershipTest g)).IsMinimalPrime P
  one : cycleLength (divisorIdeal surface (membershipTest g)) P minimal.isPrime = 1
  next : toGeneric (nextTest g) ∈ P
structure Integrated (f Q g : Row 4) (P : JetIdeal) [P.IsPrime]
    (U : (JetField P)[X]) : Prop where
  degree : U.natDegree < taylorLength
  initial : ∀ i : Fin 4,
    (hasseDeriv i.val U).eval (onComponent P (MvPolynomial.C genericArgument)) =
      onComponent P (MvPolynomial.X i)
  factor : trajectory (componentConstants P) f U = 0
  cutter : trajectory (componentConstants P) Q U = 0
  chart : trajectory (componentConstants P) g U = 0
  specializes : ∀ S : Geom[X], S.natDegree < taylorLength → P ≤ markIdeal S →
    atJet (separant g) S ≠ 0 →
    coeffPoint S ∈ MvPolynomial.zeroLocus Geom (coefficientKernel (componentConstants P) U)
structure FreshModel (f : Row 4) (A : CoeffIdeal) : Prop where
  prime : A.IsPrime
  extended_prime : (extendIdeal A).IsPrime
  regular : FreshRegular f A
  birational : FreshBirational A
def cycleWeight (J P : JetIdeal) : ℕ := by
  classical
  exact if hp : P.IsPrime then (cycleLength J P hp).toNat else 0
structure CutCycle (f Q : Row 4) : Prop where
  local_bound : ∀ surface (hz : (intersectionIdeal f Q).IsMinimalPrime surface),
    dimension surface = 2 ∧ (1 : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) surface hz.isPrime ∧
    cycleLength (intersectionIdeal f Q) surface hz.isPrime ≤ ((shape f).b * cutterBox.b : ℕ)
  weighted_degree :
    ∑ surface ∈ (intersectionIdeal f Q).minimalPrimesFinset,
      (cycleWeight (intersectionIdeal f Q) surface : ℚ) * MvPolynomial.affineDegree surface
      ≤ ((shape f).b * cutterBox.b : ℕ)
end
end K1_13_6_3
end
section
set_option autoImplicit false
namespace K1_13_6_3
noncomputable section
open K1 K1_13 K1_13_6 Polynomial MvPolynomial
open scoped BigOperators
def markPoint (s : K → K[X]) (γ : K) : Fin taylorLength → Geom :=
  coeffPoint (extend (s γ))
theorem CutInput.markPoint_inj {Γ : Finset K} {s : K → K[X]} {f Q : Row 4} {l : ℕ}
    (h : CutInput Γ s f Q l) : Set.InjOn (markPoint s) (Γ : Set K) := by
  intro α hα β hβ hEq
  apply h.distinct hα hβ
  apply Polynomial.ext
  intro n
  by_cases hn : n < taylorLength
  · have hcoeff := congrFun hEq ⟨n, hn⟩
    exact embed.injective (by simpa only [markPoint, coeffPoint, Polynomial.coeff_map] using hcoeff)
  · have hαdeg := h.degree α hα
    have hβdeg := h.degree β hβ
    have hlt : 133671 < n := by
      change ¬ n < 133672 at hn
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hαdeg.trans_lt hlt),
      Polynomial.coeff_eq_zero_of_natDegree_lt (hβdeg.trans_lt hlt)]
def valueCut (x a : K) : CoeffRing := jetLinear (embed x) 0 - MvPolynomial.C (embed a)
theorem valueCut_degree (x a : K) : (valueCut x a).totalDegree ≤ 1 := by
  unfold valueCut jetLinear
  apply (totalDegree_sub _ _).trans
  simp only [totalDegree_C, Nat.max_zero]
  exact totalDegree_finsetSum_le (fun j _ =>
    (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X, zero_add]))
theorem valueCut_eval {s : K → K[X]} {γ x a : K} (h : (s γ).natDegree < taylorLength) :
    aeval (markPoint s γ) (valueCut x a) = 0 ↔ (s γ).eval x = a := by
  have heval : aeval (markPoint s γ) (jetLinear (embed x) 0) = embed ((s γ).eval x) := by
    rw [Polynomial.eval_eq_sum_range' h, ← Fin.sum_univ_eq_sum_range, map_sum]
    simp only [jetLinear, map_sum, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Algebra.algebraMap_self_apply, Nat.choose_zero_right,
      Nat.cast_one, Nat.sub_zero, one_mul, markPoint, coeffPoint, Polynomial.coeff_map, mul_comm]
  rw [valueCut, map_sub, heval, MvPolynomial.aeval_C, Algebra.algebraMap_self_apply, sub_eq_zero, embed.injective.eq_iff]
def degreeAllowance (A : CoeffIdeal) : ℕ := ⌊affineDegree A⌋₊
theorem degreeAllowance_le (A : CoeffIdeal) : (degreeAllowance A : ℚ) ≤ affineDegree A :=
  Nat.floor_le (affineDegree_nonneg A)
private theorem degree_at_point {A : CoeffIdeal} (hp : A.IsPrime)
    {x : Fin taylorLength → Geom} (hx : x ∈ zeroLocus Geom A) : 1 ≤ affineDegree A := by
  classical
  generalize hd : dimension A = d
  induction d using Nat.strong_induction_on generalizing A with
  | h d ih =>
    by_cases hd0 : d = 0
    · obtain ⟨hf, hdeg⟩ := finite_zeroLocus_and_ncard_le_affineDegree
        (K := Geom) A (hd.trans hd0)
      have hcard : 1 ≤ (zeroLocus Geom A).ncard := by
        simpa using Set.ncard_le_ncard (Set.singleton_subset_iff.mpr hx) hf
      exact (by exact_mod_cast hcard : (1 : ℚ) ≤ _).trans hdeg
    have hcut : ∃ i, MvPolynomial.X i - MvPolynomial.C (x i) ∉ A := by
      by_contra! hall
      let φ := Ideal.Quotient.mk A
      have hmaps : φ = φ.comp (MvPolynomial.C.comp (MvPolynomial.eval x)) := by
        apply MvPolynomial.ringHom_ext
        · intro c
          simp [φ]
        · intro i
          simp only [RingHom.comp_apply, MvPolynomial.eval_X]
          exact sub_eq_zero.mp (by
            rw [← map_sub]
            exact Ideal.Quotient.eq_zero_iff_mem.mpr (hall i))
      have hsurj : Function.Surjective (algebraMap Geom (CoeffRing ⧸ A)) := by
        intro q
        obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
        refine ⟨MvPolynomial.eval x g, ?_⟩
        exact (RingHom.congr_fun hmaps g).symm
      let _ : Module.Finite Geom (CoeffRing ⧸ A) :=
        Module.Finite.of_surjective (Algebra.linearMap Geom (CoeffRing ⧸ A)) hsurj
      exact hd0 (hd.symm.trans (by simp [dimension, affineHilbertPolynomial_eq_C_finrank]))
    obtain ⟨i, hi⟩ := hcut
    let cut : CoeffRing := MvPolynomial.X i - MvPolynomial.C (x i)
    have hdeg : cut.totalDegree ≤ 1 := (totalDegree_sub _ _).trans (by simp)
    have hzero : x ∈ zeroLocus Geom (A ⊔ Ideal.span {cut}) :=
      mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hx, by simp [cut]⟩
    obtain ⟨B, hB, hxB⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus
      _ (1 : CoeffRing) _ hzero (by simp)
    have hm := (Ideal.mem_retainedMinimalPrimes.mp hB).1
    let _ := hp
    have hdim := principalCut_natDegree_affineHilbertPolynomial_add_one hi hm
    change dimension B + 1 = dimension A at hdim
    have hBdeg := ih (dimension B) (by omega) hm.isPrime hxB rfl
    have hsum := principalCut_sum_affineDegree_retainedMinimalPrimes_le
      (1 : CoeffRing) hi hdeg
    have hle := Finset.single_le_sum (f := affineDegree) (fun B _ => affineDegree_nonneg B) hB
    simpa only [Nat.cast_one, one_mul] using hBdeg.trans (hle.trans hsum)
def marksOn (Γ : Finset K) (s : K → K[X]) (A : CoeffIdeal) : Finset K := by
  classical
  exact Γ.filter fun γ => markPoint s γ ∈ zeroLocus Geom A
theorem mem_marksOn {Γ : Finset K} {s : K → K[X]} {A : CoeffIdeal} {γ : K} :
    γ ∈ marksOn Γ s A ↔ γ ∈ Γ ∧ markPoint s γ ∈ zeroLocus Geom A := by
  classical
  simp [marksOn]
theorem degreeAllowance_pos {Γ : Finset K} {s : K → K[X]} {A : CoeffIdeal}
    (hp : A.IsPrime) (h : (marksOn Γ s A).Nonempty) : 0 < degreeAllowance A := by
  obtain ⟨γ, hγ⟩ := h
  exact Nat.floor_pos.mpr (degree_at_point hp (mem_marksOn.mp hγ).2)
def piecesOf {Γ : Finset K} (T : Finset CoeffIdeal) (part : CoeffIdeal → Finset K)
    (hpart : ∀ A ∈ T, part A ⊆ Γ) : Pieces Γ :=
  ⟨T.card, fun i => part (T.equivFin.symm i),
    fun i => hpart _ (T.equivFin.symm i).property, fun i => degreeAllowance (T.equivFin.symm i)⟩
theorem mem_piecesOf {Γ : Finset K} {T : Finset CoeffIdeal} {part : CoeffIdeal → Finset K}
    {hpart : ∀ A ∈ T, part A ⊆ Γ} {γ : K} :
    γ ∈ (piecesOf T part hpart).union ↔ ∃ A ∈ T, γ ∈ part A := by
  classical
  constructor
  · intro h
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp h
    exact ⟨T.equivFin.symm i, (T.equivFin.symm i).property, hi⟩
  · rintro ⟨A, hA, hγ⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨T.equivFin ⟨A, hA⟩, Finset.mem_univ _, ?_⟩
    simpa [piecesOf] using hγ
theorem piecesOf_total {Γ : Finset K} {T : Finset CoeffIdeal} {part : CoeffIdeal → Finset K}
    {hpart : ∀ A ∈ T, part A ⊆ Γ} :
    (piecesOf T part hpart).total = ∑ A ∈ T, degreeAllowance A := by
  change ∑ i : Fin T.card, degreeAllowance (T.equivFin.symm i) = _
  calc
    _ = ∑ A : T, degreeAllowance A := Fintype.sum_equiv T.equivFin.symm _ _ (fun _ => rfl)
    _ = _ := Finset.sum_attach T degreeAllowance
theorem piecesOf_le_degree {Γ : Finset K} {T : Finset CoeffIdeal} {part : CoeffIdeal → Finset K}
    {hpart : ∀ A ∈ T, part A ⊆ Γ} :
    ((piecesOf T part hpart).total : ℚ) ≤ ∑ A ∈ T, affineDegree A := by
  rw [piecesOf_total, Nat.cast_sum]
  exact Finset.sum_le_sum fun A _ => degreeAllowance_le A
private theorem proper_cut {Γ : Finset K} {s : K → K[X]} {A : CoeffIdeal} {x a : K}
    (hdegree : ∀ γ ∈ Γ, (s γ).natDegree < taylorLength)
    (hpoints : ∀ γ ∈ Γ, markPoint s γ ∈ zeroLocus Geom A)
    (hmiss : ∃ γ ∈ Γ, (s γ).eval x ≠ a) : valueCut x a ∉ A := by
  obtain ⟨γ, hγ, hmiss⟩ := hmiss
  exact fun hmem => hmiss (valueCut_eval (hdegree γ hγ) |>.mp (hpoints γ hγ _ hmem))
private theorem mark_on_cut {s : K → K[X]} {A : CoeffIdeal} {x a γ : K}
    (hdegree : (s γ).natDegree < taylorLength) (hpoint : markPoint s γ ∈ zeroLocus Geom A)
    (hvalue : (s γ).eval x = a) :
    markPoint s γ ∈ zeroLocus Geom (A ⊔ Ideal.span {valueCut x a}) :=
  mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hpoint, (valueCut_eval hdegree).mpr hvalue⟩
theorem curveSections_of_prime {Γ : Finset K} {s : K → K[X]} {A : CoeffIdeal}
    (hp : A.IsPrime) (hdim : dimension A = 1)
    (hdegree : ∀ γ ∈ Γ, (s γ).natDegree < taylorLength)
    (hdistinct : Set.InjOn (markPoint s) (Γ : Set K))
    (hpoints : ∀ γ ∈ Γ, markPoint s γ ∈ zeroLocus Geom A) :
    CurveSections Γ s (degreeAllowance A) := by
  classical
  let _ := hp
  intro x a hmiss
  let cut := valueCut x a
  let J := A ⊔ Ideal.span {cut}
  let H := Γ.filter fun γ => (s γ).eval x = a
  have hproper := proper_cut hdegree hpoints hmiss
  have hJdim : dimension J = 0 := by
    have hd := (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
      hp hproper (valueCut_degree x a)).1
    change dimension J ≤ dimension A - 1 at hd
    omega
  have hJdeg : affineDegree J ≤ affineDegree A := by
    have h := (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
      hp hproper (valueCut_degree x a)).2
    have ha : (affineHilbertPolynomial A).natDegree = 1 := hdim
    have hj : (affineHilbertPolynomial J).natDegree = 0 := hJdim
    simpa [affineDegree, ha, hj, J, cut, Polynomial.leadingCoeff] using h
  obtain ⟨hfinite, hcard⟩ := finite_zeroLocus_and_ncard_le_affineDegree (K := Geom) J hJdim
  have hsub : (H.image (markPoint s) : Set _) ⊆ zeroLocus Geom J := by
    intro p hp
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hΓ, hv⟩ := Finset.mem_filter.mp hγ
    exact mark_on_cut (hdegree γ hΓ) (hpoints γ hΓ) hv
  have hcount := Set.ncard_le_ncard hsub hfinite
  rw [Set.ncard_coe_finset, Finset.card_image_of_injOn
    (hdistinct.mono (Finset.filter_subset _ _))] at hcount
  exact Nat.le_floor ((Nat.cast_le.mpr hcount).trans (hcard.trans hJdeg))
theorem surfaceSections_of_prime {Γ : Finset K} {s : K → K[X]} {A : CoeffIdeal}
    (hp : A.IsPrime) (hdim : dimension A = 2)
    (hdegree : ∀ γ ∈ Γ, (s γ).natDegree < taylorLength)
    (hdistinct : Set.InjOn (markPoint s) (Γ : Set K))
    (hpoints : ∀ γ ∈ Γ, markPoint s γ ∈ zeroLocus Geom A) :
    SurfaceSections Γ s (degreeAllowance A) := by
  classical
  let _ := hp
  intro x a hmiss H
  let J := A ⊔ Ideal.span {valueCut x a}
  let T := J.minimalPrimesFinset.filter (fun B => (marksOn H s B).Nonempty)
  have hproper := proper_cut hdegree hpoints hmiss
  have hsubset (B : CoeffIdeal) (_ : B ∈ T) : marksOn H s B ⊆ H :=
    fun _ h => (mem_marksOn.mp h).1
  have hprime (B : CoeffIdeal) (hB : B ∈ T) : J.IsMinimalPrime B :=
    Ideal.mem_minimalPrimesFinset.mp (Finset.mem_filter.mp hB).1
  refine ⟨piecesOf T (marksOn H s) hsubset, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨hΓ, hvalue⟩ := Finset.mem_filter.mp hγ
    have hzero : markPoint s γ ∈ zeroLocus Geom J :=
      mark_on_cut (hdegree γ hΓ) (hpoints γ hΓ) hvalue
    obtain ⟨B, hB, hxB⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus
      J (1 : CoeffRing) _ hzero (by simp)
    have hmarks : γ ∈ marksOn H s B := mem_marksOn.mpr ⟨hγ, hxB⟩
    exact mem_piecesOf.mpr ⟨B, Finset.mem_filter.mpr ⟨Ideal.mem_minimalPrimesFinset.mpr
      (Ideal.mem_retainedMinimalPrimes.mp hB).1, ⟨γ, hmarks⟩⟩, hmarks⟩
  · intro i
    let B := T.equivFin.symm i
    have hm := hprime B B.property
    have hd := principalCut_natDegree_affineHilbertPolynomial_add_one hproper hm
    change dimension (B : CoeffIdeal) + 1 = dimension A at hd
    have hdimB : dimension (B : CoeffIdeal) = 1 := by omega
    apply curveSections_of_prime hm.isPrime hdimB
    · exact fun γ hγ => hdegree γ (Finset.mem_filter.mp (mem_marksOn.mp hγ).1).1
    · exact hdistinct.mono (fun γ hγ => (Finset.mem_filter.mp (mem_marksOn.mp hγ).1).1)
    · exact fun _ hγ => (mem_marksOn.mp hγ).2
  · intro i
    let B := T.equivFin.symm i
    exact degreeAllowance_pos (hprime B B.property).isPrime
      (Finset.mem_filter.mp B.property).2
  · apply Nat.le_floor
    have hsum := principalCut_sum_affineDegree_minimalPrimes_le hproper (valueCut_degree x a)
    exact piecesOf_le_degree.trans ((Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun B _ _ => affineDegree_nonneg B)).trans
      (by simpa only [Nat.cast_one, one_mul] using hsum))
end
end K1_13_6_3
end
section
set_option autoImplicit false
namespace K1_13_6_3
noncomputable section
open K1_13 K1_13_6 MvPolynomial
open scoped BigOperators
private theorem pderiv_degree (P : Row 4) (i : Fin 4) :
    (pderiv i P).totalDegree ≤ P.totalDegree - 1 := by
  simpa only [weightedTotalDegree_one, Pi.one_apply] using
    weightedTotalDegree_pderiv_le_sub (1 : Fin 4 → ℕ) i P
private theorem pderiv_zero_of_degree_zero {P : Row 4} (h : P.totalDegree = 0) (i : Fin 4) :
    pderiv i P = 0 := by
  rw [totalDegree_eq_zero_iff_eq_C.mp h, pderiv_C]
private theorem coefficientDerivative_degree (P : Row 4) :
    (coefficientDerivative P).totalDegree ≤ P.totalDegree := by
  unfold coefficientDerivative
  exact totalDegree_finsetSum_le fun m hm =>
    (totalDegree_monomial_le _ _).trans (le_totalDegree hm)
private theorem partialFlow_degree (P : Row 4) :
    (partialFlow P).totalDegree ≤ P.totalDegree := by
  unfold partialFlow
  apply (totalDegree_add _ _).trans
  refine max_le (coefficientDerivative_degree P) (totalDegree_finsetSum_le ?_)
  intro i _
  by_cases h : P.totalDegree = 0
  · simp [pderiv_zero_of_degree_zero h]
  · refine (totalDegree_mul _ _).trans ?_
    have hc : (MvPolynomial.C (Polynomial.C ((i.val + 1 : ℕ) : Geom)) *
        MvPolynomial.X i.succ : Row 4).totalDegree ≤ 1 :=
      (totalDegree_mul _ _).trans (by rw [totalDegree_C, totalDegree_X, zero_add])
    have hd := pderiv_degree P i.castSucc
    omega
private theorem flowNumerator_degree {g P : Row 4} {d : ℕ} (hd : g.totalDegree ≤ d) :
    (flowNumerator g P).totalDegree ≤ (d - 1) + P.totalDegree := by
  unfold flowNumerator
  apply (totalDegree_sub _ _).trans
  refine max_le ?_ ?_
  · apply (totalDegree_mul _ _).trans
    exact Nat.add_le_add (by exact (pderiv_degree g 3).trans (Nat.sub_le_sub_right hd _))
      (partialFlow_degree P)
  · by_cases h : P.totalDegree = 0
    · simp [separant, pderiv_zero_of_degree_zero h]
    · apply (totalDegree_mul _ _).trans
      have hg := (partialFlow_degree g).trans hd
      have hP : (separant P).totalDegree ≤ P.totalDegree - 1 := pderiv_degree P 3
      omega
private theorem clearedStep_degree {g P : Row 4} (a : ℕ) {d : ℕ} (hd : g.totalDegree ≤ d) :
    (clearedStep g a P).totalDegree ≤ P.totalDegree + 2 * (d - 1) := by
  unfold clearedStep
  apply (totalDegree_sub _ _).trans
  have hs : (separant g).totalDegree ≤ d - 1 :=
    (pderiv_degree g 3).trans (Nat.sub_le_sub_right hd _)
  refine max_le ?_ ?_
  · apply (totalDegree_mul _ _).trans
    have hp : (flowNumerator g P).totalDegree ≤ _ := flowNumerator_degree hd
    omega
  · apply (totalDegree_mul _ _).trans
    have hc : ((a : Row 4) * flowNumerator g (separant g)).totalDegree ≤
        (flowNumerator g (separant g)).totalDegree := by
      rw [← map_natCast (MvPolynomial.C : Polynomial Geom →+* Row 4) a]
      exact (totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add])
    have hflow : (flowNumerator g (separant g)).totalDegree ≤ _ := flowNumerator_degree hd
    omega
private theorem jetNumerator_degree {g : Row 4} {d : ℕ} (hd : g.totalDegree ≤ d) (n : ℕ) :
    (jetNumerator g n).totalDegree ≤ 1 + 2 * n * (d - 1) := by
  induction n with
  | zero => simp [jetNumerator]
  | succ n ih =>
    rw [jetNumerator]
    apply (clearedStep_degree (2 * n) hd).trans
    rw [Nat.mul_succ, Nat.add_mul]
    omega
private theorem iterate_separant_degree (f : Row 4) (r : ℕ) :
    ((separant^[r]) f).totalDegree ≤ f.totalDegree := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact ((pderiv_degree _ 3).trans (Nat.sub_le _ _)).trans ih
theorem membershipTest_degree (f : Row 4) (r : ℕ) :
    (toGeneric (membershipTest ((separant^[r]) f))).totalDegree ≤
      (chart (taylorLength + 1) (shape f).chamber).b := by
  let d := (shape f).chamber.b
  have hd : ((separant^[r]) f).totalDegree ≤ d :=
    (iterate_separant_degree f r).trans (le_max_left _ _)
  have hmap (P : Row 4) : (toGeneric P).totalDegree ≤ P.totalDegree :=
    Finset.sup_mono (support_map_subset _ _)
  unfold membershipTest
  apply (hmap _).trans ((jetNumerator_degree hd taylorLength).trans ?_)
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_succ _))) _ |>.trans (le_max_left _ _)
end
end K1_13_6_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace K1_13_6_3
noncomputable section
open K1 K1_13 K1_13_6 Polynomial MvPolynomial
open scoped BigOperators
def c1 : Prop :=
  ∀ (f Q : Row 4) (surface : JetIdeal) (r : ℕ) (P : JetIdeal)
    (hz : (intersectionIdeal f Q).IsMinimalPrime surface),
    CanonicalChart f surface r →
    cycleLength (intersectionIdeal f Q) surface hz.isPrime < (K1.p : ℕ∞) →
    let g := (separant^[r]) f
    Invariant g surface → SimpleCut g surface P → Invariant g P
def c2 : Prop :=
  ∀ (f Q : Row 4) (r : ℕ) (P : JetIdeal) (hp : P.IsPrime),
    TrueWeightLE f (90 * 180265 - 1) → TrueWeightLE Q (3000 * 180265 - 1) →
    intersectionIdeal f Q ≤ P →
    let g := (separant^[r]) f
    toGeneric g ∈ P → toGeneric (separant g) ∉ P →
    toGeneric (membershipTest g) ∈ P → Invariant g P →
    ∃ U : (JetField P)[X], @Integrated f Q g P hp U
def c3 : Prop :=
  (∀ (f Q : Row 4) (surface : JetIdeal) (r : ℕ) (P : JetIdeal) (hp : P.IsPrime)
      (U : (JetField P)[X]),
    (intersectionIdeal f Q).IsMinimalPrime surface →
    (∀ T, (intersectionIdeal f Q).IsMinimalPrime T → dimension T = 2) →
    let g := (separant^[r]) f
    toGeneric (separant g) ∉ P → (P = surface ∨ SimpleCut g surface P) →
    @Integrated f Q g P hp U →
    let A := coefficientKernel (componentConstants P) U
    FreshModel f A ∧
      ((dimension A = 1 ∧ freshImage A = P ∧ SimpleCut g surface P) ∨
        (dimension A = 2 ∧ (intersectionIdeal f Q).IsMinimalPrime (freshImage A)))) ∧
  (∀ f : Row 4, Set.InjOn freshImage {A | A.IsPrime ∧ FreshRegular f A})
def c4 : Prop :=
  ∀ A : CoeffIdeal, A.IsPrime → (extendIdeal A).IsPrime → dimension A = 1 →
    FreshBirational A → affineDegree A = affineDegree (freshImage A)
def c5 : Prop :=
  ∀ A : CoeffIdeal, A.IsPrime → (extendIdeal A).IsPrime → dimension A = 2 →
    FreshBirational A →
    2 * affineDegree A ≤ 133671 * affineDegree (freshImage A)
def c6 : Prop :=
  ∀ f Q : Row 4, SmallFactor f → ¬ f ∣ Q → InBox (shape Q) ⟨4012, 1650, 550⟩ →
    CutCycle f Q
def CurveSource (f Q : Row 4) (l : ℕ) (P : JetIdeal) : Prop :=
  ∃ (surface : JetIdeal) (r : ℕ) (hz : (intersectionIdeal f Q).IsMinimalPrime surface),
    (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) surface hz.isPrime ∧
    CanonicalChart f surface r ∧ SimpleCut ((separant^[r]) f) surface P
def FamilyCase (f Q : Row 4) (l : ℕ) (A : CoeffIdeal) : Prop :=
  (dimension A = 1 ∧ CurveSource f Q l (freshImage A)) ∨
  (dimension A = 2 ∧ (intersectionIdeal f Q).IsMinimalPrime (freshImage A))
private theorem canonical_unique {f : Row 4} {surface : JetIdeal} {r t : ℕ}
    (hr : CanonicalChart f surface r) (ht : CanonicalChart f surface t) : r = t := by
  rcases lt_trichotomy r t with h | h | h
  · have hm := ht.2.1 (r + 1) (Nat.succ_le_of_lt h)
    rw [Function.iterate_succ_apply'] at hm
    exact False.elim (hr.2.2 hm)
  · exact h
  · have hm := hr.2.1 (t + 1) (Nat.succ_le_of_lt h)
    rw [Function.iterate_succ_apply'] at hm
    exact False.elim (ht.2.2 hm)
private theorem cycleWeight_ge {f Q : Row 4} (hc : CutCycle f Q) {surface : JetIdeal}
    (hz : (intersectionIdeal f Q).IsMinimalPrime surface) {l : ℕ}
    (hl : (l : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) surface hz.isPrime) :
    l ≤ cycleWeight (intersectionIdeal f Q) surface := by
  classical
  have hne : cycleLength (intersectionIdeal f Q) surface hz.isPrime ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) (hc.local_bound surface hz).2.2
  simpa only [cycleWeight, dite_eq_left hz.isPrime, ENat.toNat_natCast] using ENat.toNat_le_toNat hl hne
private theorem surface_sum {f Q : Row 4} (hc : CutCycle f Q) (T : Finset JetIdeal)
    (hT : ∀ P ∈ T, (intersectionIdeal f Q).IsMinimalPrime P) :
    ∑ P ∈ T, affineDegree P ≤ ((shape f).b * cutterBox.b : ℕ) := by
  classical
  let S := (intersectionIdeal f Q).minimalPrimesFinset
  have hsub : T ⊆ S := fun P hP => Ideal.mem_minimalPrimesFinset.mpr (hT P hP)
  calc
    _ ≤ ∑ P ∈ S, affineDegree P :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun P _ _ => affineDegree_nonneg P)
    _ ≤ ∑ P ∈ S, (cycleWeight (intersectionIdeal f Q) P : ℚ) * affineDegree P := by
      apply Finset.sum_le_sum
      intro P hP
      have hz := Ideal.mem_minimalPrimesFinset.mp hP
      have h1 := cycleWeight_ge hc hz (hc.local_bound P hz).2.1
      exact le_mul_of_one_le_left (affineDegree_nonneg P) (by exact_mod_cast h1)
    _ ≤ _ := hc.weighted_degree
theorem curve_sum {f Q : Row 4} {l : ℕ} (hc : CutCycle f Q)
    (T : Finset JetIdeal) (hT : ∀ P ∈ T, CurveSource f Q l P) :
    (l : ℚ) * (∑ P ∈ T, affineDegree P) ≤ (membershipDegree (shape f) : ℕ) := by
  classical
  let J := intersectionIdeal f Q
  let S := J.minimalPrimesFinset
  let b := (chart (taylorLength + 1) (shape f).chamber).b
  let parent : JetIdeal → JetIdeal := fun P =>
    if h : P ∈ T then Classical.choose (hT P h) else ⊥
  have hd (P : JetIdeal) (hP : P ∈ T) :
      ∃ (r : ℕ) (hz : J.IsMinimalPrime (parent P)),
        (l : ℕ∞) ≤ cycleLength J (parent P) hz.isPrime ∧
        CanonicalChart f (parent P) r ∧ SimpleCut ((separant^[r]) f) (parent P) P := by
    simpa only [parent, dite_eq_left hP] using Classical.choose_spec (hT P hP)
  have hm (P : JetIdeal) (hP : P ∈ T) : parent P ∈ S := by
    obtain ⟨_, hz, _⟩ := hd P hP
    exact Ideal.mem_minimalPrimesFinset.mpr hz
  have hfibre (surface : JetIdeal) :
      (∑ P ∈ T.filter (fun P => parent P = surface), (l : ℚ) * affineDegree P) ≤
        b * ((cycleWeight J surface : ℚ) * affineDegree surface) := by
    let V := T.filter (fun P => parent P = surface)
    by_cases hV : V.Nonempty
    · obtain ⟨P₀, hP₀⟩ := hV
      obtain ⟨hP₀T, hP₀parent⟩ := Finset.mem_filter.mp hP₀
      have hdata := hd P₀ hP₀T
      rw [hP₀parent] at hdata
      obtain ⟨r, hz, hhigh, hchart, hcut⟩ := hdata
      let _ := hz.isPrime
      let g := (separant^[r]) f
      let B := (divisorIdeal surface (membershipTest g)).minimalPrimesFinset
      have hsub : V ⊆ B := by
        intro P hP
        obtain ⟨hPT, hPparent⟩ := Finset.mem_filter.mp hP
        obtain ⟨r', hz', _, hchart', hcut'⟩ := hd P hPT
        rw [hPparent] at hchart' hcut'
        have hEq := canonical_unique hchart' hchart
        subst r'
        exact Ideal.mem_minimalPrimesFinset.mpr hcut'.minimal
      have hB : (∑ P ∈ B, affineDegree P) ≤ (b : ℚ) * affineDegree surface :=
        principalCut_sum_affineDegree_minimalPrimes_le hcut.proper (membershipTest_degree f r)
      have hl := cycleWeight_ge hc hz hhigh
      calc
        _ = (l : ℚ) * (∑ P ∈ V, affineDegree P) := (Finset.mul_sum ..).symm
        _ ≤ (l : ℚ) * ((b : ℚ) * affineDegree surface) :=
          mul_le_mul_of_nonneg_left
            ((Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun P _ _ => affineDegree_nonneg P)).trans hB) (by positivity)
        _ ≤ _ := by
          rw [mul_left_comm]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (by exact_mod_cast hl) (affineDegree_nonneg _))
            (by positivity)
    · have he := Finset.not_nonempty_iff_eq_empty.mp hV
      change (∑ P ∈ V, (l : ℚ) * affineDegree P) ≤ _
      rw [he, Finset.sum_empty]
      exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (affineDegree_nonneg _))
  calc
    _ = ∑ P ∈ T, (l : ℚ) * affineDegree P := Finset.mul_sum ..
    _ = ∑ surface ∈ S, ∑ P ∈ T.filter (fun P => parent P = surface),
          (l : ℚ) * affineDegree P :=
      (Finset.sum_fiberwise_of_maps_to hm _).symm
    _ ≤ ∑ surface ∈ S, (b : ℚ) * ((cycleWeight J surface : ℚ) * affineDegree surface) :=
      Finset.sum_le_sum (fun surface _ => hfibre surface)
    _ = (b : ℚ) * ∑ surface ∈ S, (cycleWeight J surface : ℚ) * affineDegree surface :=
      (Finset.mul_sum ..).symm
    _ ≤ (b : ℚ) * (((shape f).b * cutterBox.b : ℕ) : ℚ) :=
      mul_le_mul_of_nonneg_left hc.weighted_degree (by positivity)
    _ = _ := by simp only [membershipDegree, Nat.cast_mul, b]; ring
theorem family_of_mark (h1 : c1) (h2 : c2) (h3 : c3)
    {Γ : Finset K} {s : K → K[X]} {f Q : Row 4} {l : ℕ}
    (input : CutInput Γ s f Q l) (hc : CutCycle f Q)
    {γ : K} (hγ : γ ∈ Γ) (hmark : ContinuedMark f Q l (extend (s γ))) :
    ∃ A : CoeffIdeal, FreshModel f A ∧ FamilyCase f Q l A ∧ γ ∈ marksOn Γ s A := by
  obtain ⟨surface, r, hz, hcont⟩ := hmark
  let g := (separant^[r]) f
  have hdim (T : JetIdeal) (hT : (intersectionIdeal f Q).IsMinimalPrime T) :
      dimension T = 2 := (hc.local_bound T hT).1
  have hnum : (shape f).b * cutterBox.b < K1.p :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ input.small.2.2.1.1) (by decide)
  have hsmall : cycleLength (intersectionIdeal f Q) surface hz.base.isPrime < (K1.p : ℕ∞) :=
    (hc.local_bound surface hz.base).2.2.trans_lt (by exact_mod_cast hnum)
  have integrate (P : JetIdeal) (hp : P.IsPrime) (hle : surface ≤ P)
      (hpoint : P ≤ markIdeal (extend (s γ))) (hI : Invariant g P)
      (hE : toGeneric (membershipTest g) ∈ P)
      (hbranch : P = surface ∨ SimpleCut g surface P) :
      ∃ A : CoeffIdeal, FreshModel f A ∧ FamilyCase f Q l A ∧ γ ∈ marksOn Γ s A := by
    have hg : toGeneric g ∈ P := hle (hz.chart.2.1 r le_rfl)
    have hsep : toGeneric (separant g) ∉ P := by
      intro hm
      have h := hpoint hm
      apply hz.regular
      unfold markIdeal at h
      rw [RingHom.mem_ker] at h
      have hinj : Function.Injective genericCoeffs :=
        (algebraMap GenericField GeoField).injective.comp
          (IsFractionRing.injective Geom[X] GenericField)
      apply hinj
      rw [map_zero]
      change MvPolynomial.eval _ (MvPolynomial.map genericCoeffs (separant g)) = 0 at h
      rw [MvPolynomial.eval_map] at h
      change MvPolynomial.eval₂ genericCoeffs (⇑genericCoeffs ∘ jet (extend (s γ)))
        (separant g) = 0 at h
      rw [← MvPolynomial.eval₂_comp] at h
      exact h
    obtain ⟨U, hU⟩ := h2 f Q r P hp input.small.2.2.2 input.weight
      (hz.base.1.2.trans hle) hg hsep hE hI
    obtain ⟨hA, hcase⟩ := h3.1 f Q surface r P hp U hz.base hdim hsep hbranch hU
    refine ⟨_, hA, ?_, mem_marksOn.mpr ⟨hγ, ?_⟩⟩
    · rcases hcase with ⟨hd, heq, hsimple⟩ | hsurface
      · exact Or.inl ⟨hd, surface, r, hz.base, hz.high, hz.chart, heq.symm ▸ hsimple⟩
      · exact Or.inr hsurface
    · have hs : (extend (s γ)).natDegree < taylorLength := by
        rw [Polynomial.natDegree_map]
        exact Nat.lt_succ_of_le (input.degree γ hγ)
      exact hU.specializes _ hs hpoint hz.regular
  rcases hcont with hE | ⟨P, hm, hproper, hpoint, hone, hnext⟩
  · exact integrate surface hz.base.isPrime le_rfl hz.point hz.invariant hE (Or.inl rfl)
  · have hs : SimpleCut g surface P := ⟨hproper, hm, hone, hnext⟩
    have hI := h1 f Q surface r P hz.base hz.chart hsmall hz.invariant hs
    have hl : divisorIdeal surface (membershipTest g) ≤ P := hm.1.2
    have hE : toGeneric (membershipTest g) ∈ P :=
      hl (Ideal.mem_sup_right (Ideal.subset_span (by simp)))
    exact integrate P hm.isPrime (le_sup_left.trans hl) hpoint hI hE (Or.inr hs)
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5)
    (h6 : c6) : K1_13_6.c3 := by
  classical
  intro Γ s f Q l input
  have hc := h6 f Q input.small input.proper input.box
  let B := Γ.filter (fun γ => ContinuedMark f Q l (extend (s γ)))
  have hw (γ : B) :
      ∃ A : CoeffIdeal, FreshModel f A ∧ FamilyCase f Q l A ∧ γ.val ∈ marksOn Γ s A := by
    obtain ⟨hγ, hmark⟩ := Finset.mem_filter.mp γ.property
    exact family_of_mark h1 h2 h3 input hc hγ hmark
  let A : B → CoeffIdeal := fun γ => Classical.choose (hw γ)
  have hA (γ : B) : FreshModel f (A γ) ∧ FamilyCase f Q l (A γ) ∧ γ.val ∈ marksOn Γ s (A γ) :=
    Classical.choose_spec (hw γ)
  let T := B.attach.image A
  let Tc := T.filter (fun P => dimension P = 1)
  let Td := T.filter (fun P => dimension P = 2)
  have hT (P : CoeffIdeal) (hp : P ∈ T) :
      FreshModel f P ∧ FamilyCase f Q l P ∧ (marksOn Γ s P).Nonempty := by
    obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨(hA γ).1, (hA γ).2.1, ⟨γ.val, (hA γ).2.2⟩⟩
  have hd (P : CoeffIdeal) (hp : P ∈ T) : dimension P = 1 ∨ dimension P = 2 :=
    (hT P hp).2.1.imp And.left And.left
  have hC (P : CoeffIdeal) (hp : P ∈ Tc) : CurveSource f Q l (freshImage P) := by
    obtain ⟨ht, he⟩ := Finset.mem_filter.mp hp
    rcases (hT P ht).2.1 with h | h
    · exact h.2
    · exact False.elim (by omega)
  have hD (P : CoeffIdeal) (hp : P ∈ Td) :
      (intersectionIdeal f Q).IsMinimalPrime (freshImage P) := by
    obtain ⟨ht, he⟩ := Finset.mem_filter.mp hp
    rcases (hT P ht).2.1 with h | h
    · exact False.elim (by omega)
    · exact h.2
  have hinj : Set.InjOn freshImage (T : Set CoeffIdeal) := by
    apply (h3.2 f).mono
    intro P hp
    have hm := (hT P hp).1
    exact ⟨hm.prime, hm.regular⟩
  have hpart (P : CoeffIdeal) : marksOn Γ s P ⊆ Γ := fun _ h => (mem_marksOn.mp h).1
  let C := piecesOf Tc (marksOn Γ s) (fun P _ => hpart P)
  let D := piecesOf Td (marksOn Γ s) (fun P _ => hpart P)
  have hdegree (γ : K) (hγ : γ ∈ Γ) : (s γ).natDegree < taylorLength :=
    Nat.lt_succ_of_le (input.degree γ hγ)
  refine ⟨C, D, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    let P := Tc.equivFin.symm i
    obtain ⟨ht, he⟩ := Finset.mem_filter.mp P.property
    exact curveSections_of_prime (hT P ht).1.prime he
      (fun γ hγ => hdegree γ (hpart P hγ))
      ((CutInput.markPoint_inj input).mono (hpart P))
      (fun _ hγ => (mem_marksOn.mp hγ).2)
  · intro i
    let P := Td.equivFin.symm i
    obtain ⟨ht, he⟩ := Finset.mem_filter.mp P.property
    exact surfaceSections_of_prime (hT P ht).1.prime he
      (fun γ hγ => hdegree γ (hpart P hγ))
      ((CutInput.markPoint_inj input).mono (hpart P))
      (fun _ hγ => (mem_marksOn.mp hγ).2)
  · intro i
    let P := Tc.equivFin.symm i
    have ht := hT P (Finset.mem_filter.mp P.property).1
    exact degreeAllowance_pos ht.1.prime ht.2.2
  · intro i
    let P := Td.equivFin.symm i
    have ht := hT P (Finset.mem_filter.mp P.property).1
    exact degreeAllowance_pos ht.1.prime ht.2.2
  · intro γ hγ hm
    let γ' : B := ⟨γ, Finset.mem_filter.mpr ⟨hγ, hm⟩⟩
    have hmem : A γ' ∈ T := Finset.mem_image_of_mem A (Finset.mem_attach _ _)
    rcases hd _ hmem with h | h
    · exact Finset.mem_union_left _ (mem_piecesOf.mpr
        ⟨_, Finset.mem_filter.mpr ⟨hmem, h⟩, (hA γ').2.2⟩)
    · exact Finset.mem_union_right _ (mem_piecesOf.mpr
        ⟨_, Finset.mem_filter.mpr ⟨hmem, h⟩, (hA γ').2.2⟩)
  · have hsum := curve_sum hc (Tc.image freshImage) (by
      intro P hp
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hp
      exact hC A hA)
    have heq : (∑ P ∈ Tc, affineDegree P) = ∑ P ∈ Tc.image freshImage, affineDegree P := by
      rw [Finset.sum_image (fun P hP R hR h => hinj (Finset.mem_filter.mp hP).1
        (Finset.mem_filter.mp hR).1 h)]
      apply Finset.sum_congr rfl
      intro P hP
      obtain ⟨ht, he⟩ := Finset.mem_filter.mp hP
      have hf := (hT P ht).1
      exact h4 P hf.prime hf.extended_prime he hf.birational
    rw [← heq] at hsum
    exact_mod_cast
      (mul_le_mul_of_nonneg_left (piecesOf_le_degree (T := Tc) (part := marksOn Γ s))
        (show (0 : ℚ) ≤ l by positivity)).trans hsum
  · have hsum := surface_sum hc (Td.image freshImage) (by
      intro P hp
      obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hp
      exact hD A hA)
    have hbound : (2 : ℚ) * (D.total : ℚ) ≤ 133671 * (((shape f).b * cutterBox.b : ℕ) : ℚ) := by
      calc
        _ ≤ 2 * (∑ P ∈ Td, affineDegree P) :=
          mul_le_mul_of_nonneg_left (piecesOf_le_degree (T := Td) (part := marksOn Γ s))
            (by positivity)
        _ ≤ ∑ P ∈ Td, 133671 * affineDegree (freshImage P) := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro P hP
          obtain ⟨ht, he⟩ := Finset.mem_filter.mp hP
          have hf := (hT P ht).1
          exact h5 P hf.prime hf.extended_prime he hf.birational
        _ = 133671 * (∑ P ∈ Td.image freshImage, affineDegree P) := by
          rw [Finset.mul_sum, Finset.sum_image (fun P hP R hR h =>
            hinj (Finset.mem_filter.mp hP).1 (Finset.mem_filter.mp hR).1 h)]
        _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
    rw [Nat.mul_assoc]
    exact_mod_cast hbound
end
end K1_13_6_3
end
section
set_option autoImplicit false
namespace K1_13_6_3_5
noncomputable section
open MvPolynomial K1_13_6 K1_13_6_3
variable {k σ τ : Type*} [Field k]
def boundaryIdeal (A : Ideal (MvPolynomial σ k)) : Ideal (MvPolynomial σ k) :=
  Ideal.span {g | ∃ f ∈ A, homogeneousComponent f.totalDegree f = g}
def boundaryWeight (J P : Ideal (MvPolynomial σ k)) : ℕ := by
  classical
  exact if hp : P.IsPrime then
    letI := hp
    let L := Localization.AtPrime P
    (Module.length L (L ⧸ J.map (algebraMap (MvPolynomial σ k) L))).toNat
  else 0
def residueDegree (φ : MvPolynomial τ k →+* MvPolynomial σ k)
    (P : Ideal (MvPolynomial σ k)) : ℕ := by
  classical
  exact if hp : P.IsPrime then
    letI := hp
    letI : (P.comap φ).IsPrime := Ideal.IsPrime.comap φ
    let f : FractionRing (MvPolynomial τ k ⧸ P.comap φ) →+*
        FractionRing (MvPolynomial σ k ⧸ P) :=
      IsFractionRing.map (Ideal.quotientMap_injective (I := P) (f := φ))
    letI := f.toAlgebra
    Module.finrank (FractionRing (MvPolynomial τ k ⧸ P.comap φ))
      (FractionRing (MvPolynomial σ k ⧸ P))
  else 0
def IsLinearProjection (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k) : Prop :=
  ∀ i, (φ (MvPolynomial.X i)).IsHomogeneous 1
def IsBirationalOn (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k)
    (A : Ideal (MvPolynomial σ k)) : Prop :=
  ∀ h : MvPolynomial σ k, ∃ u v : MvPolynomial τ k, φ v ∉ A ∧ h * φ v - φ u ∈ A
def freshProjection : GeoJets →ₐ[GeoField] FreshCoeffRing :=
  MvPolynomial.aeval (fun i : Fin 4 => jetLinear genericArgument i.val)
theorem freshProjection_linear : IsLinearProjection freshProjection := by
  intro i
  rw [freshProjection, aeval_X, jetLinear]
  apply IsHomogeneous.sum
  intro j _
  exact (isHomogeneous_C _ _).mul (isHomogeneous_X _ j)
end
end K1_13_6_3_5
end
section
set_option autoImplicit false
namespace K1_13_6_3_6
noncomputable section
open K1_13_6 K1_13_6_3
open scoped BigOperators
section Quotients
variable {R : Type} [CommRing R]
def quotientMul (I : Ideal R) (g : R) :
    (R ⧸ I.colon {g}) →ₗ[R] (R ⧸ I) :=
  (I.colon {g}).liftQ (LinearMap.toSpanSingleton R (R ⧸ I) (Ideal.Quotient.mk I g))
    fun a ha => by
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      change Ideal.Quotient.mk I a * Ideal.Quotient.mk I g = 0
      rw [← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Submodule.mem_colon_singleton.mp ha)
@[simp]
theorem quotientMul_mk (I : Ideal R) (g a : R) :
    quotientMul I g (Ideal.Quotient.mk (I.colon {g}) a) = Ideal.Quotient.mk I (a * g) := by
  change quotientMul I g (Submodule.Quotient.mk a) = _
  rw [quotientMul, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply]
  exact (map_mul (Ideal.Quotient.mk I) a g).symm
theorem quotientMul_injective (I : Ideal R) (g : R) : Function.Injective (quotientMul I g) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [quotientMul_mk, Ideal.Quotient.eq_zero_iff_mem] at ha
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Submodule.mem_colon_singleton.mpr ha)
theorem quotientMul_exact (I : Ideal R) (g : R) :
    Function.Exact (quotientMul I g)
      (Submodule.factor (le_sup_left : I ≤ I ⊔ Ideal.span {g})) := by
  rw [LinearMap.exact_iff]
  ext y
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  change (Ideal.Quotient.mk (I ⊔ Ideal.span {g}) b = 0 ↔ _)
  rw [Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hb
    obtain ⟨i, hi, j, hj, hsum⟩ := Submodule.mem_sup.mp hb
    obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton.mp hj
    refine ⟨Ideal.Quotient.mk (I.colon {g}) x, ?_⟩
    rw [quotientMul_mk, Ideal.Quotient.eq, ← hsum]
    convert I.neg_mem hi using 1
    ring
  · rintro ⟨a, ha⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [quotientMul_mk, Ideal.Quotient.eq] at ha
    have hx : x * g ∈ I ⊔ Ideal.span {g} :=
      Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr ⟨x, mul_comm x g⟩)
    simpa using (I ⊔ Ideal.span {g}).sub_mem hx (Ideal.mem_sup_left ha)
private theorem colon_map_localization {S : Type} [CommRing S] [Algebra R S]
    (T : Submonoid R) [IsLocalization T S] (I : Ideal R) (g : R) :
    (I.colon {g}).map (algebraMap R S) = (I.map (algebraMap R S)).colon {algebraMap R S g} := by
  ext z
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq T z
  rw [Submodule.mem_colon_singleton, smul_eq_mul,
    mul_comm _ (algebraMap R S g), IsLocalization.mul_mk'_eq_mk'_of_mul,
    IsLocalization.mk'_mem_map_algebraMap_iff, IsLocalization.mk'_mem_map_algebraMap_iff]
  simp only [Submodule.mem_colon_singleton, smul_eq_mul, mul_assoc, mul_comm g]
end Quotients
theorem length_step (I P : JetIdeal) (hp : P.IsPrime) (g : GeoJets) :
    cycleLength I P hp =
      cycleLength (I.colon {g}) P hp + cycleLength (I ⊔ Ideal.span {g}) P hp := by
  have := hp
  let L := Localization.AtPrime P
  let r := algebraMap GeoJets L
  let J := I.map r
  let a := r g
  have h := Module.length_eq_add_of_exact (quotientMul J a)
    (Submodule.factor (le_sup_left : J ≤ J ⊔ Ideal.span {a}))
    (quotientMul_injective J a) (Submodule.factor_surjective le_sup_left)
    (quotientMul_exact J a)
  change Module.length L (L ⧸ I.map r) =
    Module.length L (L ⧸ (I.colon {g}).map r) + Module.length L (L ⧸ (I ⊔ Ideal.span {g}).map r)
  rw [colon_map_localization P.primeCompl, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  exact h
theorem length_eq_zero_of_not_le {I P : JetIdeal} (hp : P.IsPrime) (h : ¬ I ≤ P) :
    cycleLength I P hp = 0 := by
  have := hp
  let L := Localization.AtPrime P
  have htop : I.map (algebraMap GeoJets L) = ⊤ := by
    by_contra ht
    exact h (Set.disjoint_compl_left_iff_subset.mp
      ((IsLocalization.map_algebraMap_ne_top_iff_disjoint P.primeCompl L I).mp ht))
  change Module.length L (L ⧸ I.map (algebraMap GeoJets L)) = 0
  simp [htop, Module.length_eq_zero]
theorem length_self (P : JetIdeal) (hp : P.IsPrime) : cycleLength P P hp = 1 := by
  have := hp
  let L := Localization.AtPrime P
  change Module.length L (L ⧸ P.map (algebraMap GeoJets L)) = 1
  rw [Localization.AtPrime.map_eq_maximalIdeal]
  have h : IsSimpleModule L (L ⧸ IsLocalRing.maximalIdeal L) :=
    isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal L).1
  exact Module.length_eq_one _ _
theorem length_pos {I P : JetIdeal} (hp : P.IsPrime) (h : I ≤ P) :
    1 ≤ cycleLength I P hp := by
  have := hp
  let L := Localization.AtPrime P
  have htop : I.map (algebraMap GeoJets L) ≠ ⊤ :=
    ((IsLocalization.map_algebraMap_ne_top_iff_disjoint P.primeCompl L I).mpr
      (Set.disjoint_compl_left_iff_subset.mpr h))
  have := Ideal.Quotient.nontrivial_iff.mpr htop
  exact Order.one_le_iff_ne_zero.mpr (Module.length_pos (R := L)).ne'
theorem exists_prime_colon (I : JetIdeal) (hI : I ≠ ⊤) :
    ∃ g : GeoJets, g ∉ I ∧ (I.colon {g}).IsPrime := by
  let _ := Ideal.Quotient.nontrivial_iff.mpr hI
  obtain ⟨A, hA, _⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing
    GeoJets (1 : GeoJets ⧸ I) one_ne_zero
  obtain ⟨hp, x, hx⟩ := isAssociatedPrime_iff.mp hA
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
  have heq : A = I.colon {g} := by
    ext a
    rw [hx, Submodule.mem_colon_singleton, Submodule.mem_colon_singleton, Submodule.mem_bot]
    change Ideal.Quotient.mk I a * Ideal.Quotient.mk I g = 0 ↔ a * g ∈ I
    rw [← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem
  rw [heq] at hp
  refine ⟨g, fun hg => hp.ne_top ?_, hp⟩
  simpa only [Submodule.colon_eq_top_iff_subset, Set.singleton_subset_iff, SetLike.mem_coe] using hg
end
end K1_13_6_3_6
end
section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace K1_13_6_3_5
noncomputable section
open MvPolynomial K1_13_6 K1_13_6_3
attribute [local instance] MvPolynomial.gradedAlgebra
def c1 : Prop :=
  ∀ (k σ : Type) [Field k] [Finite σ] (A : Ideal (MvPolynomial σ k)),
    A.IsPrime → dimension A = 2 →
    (∀ P, (boundaryIdeal A).IsMinimalPrime P →
      dimension P = 2 ∧ P.IsHomogeneous (homogeneousSubmodule σ k)) ∧
    affineDegree A = ∑ P ∈ (boundaryIdeal A).minimalPrimesFinset,
      (boundaryWeight (boundaryIdeal A) P : ℚ) * affineDegree P
def c2 : Prop :=
  ∀ A : CoeffIdeal, A.IsPrime →
    affineHilbertPolynomial (extendIdeal A) = affineHilbertPolynomial A ∧
    ∀ P, (boundaryIdeal (extendIdeal A)).IsMinimalPrime P →
      ∃ R, (boundaryIdeal A).IsMinimalPrime R ∧ extendIdeal R = P
def c3 : Prop :=
  ∀ R : CoeffIdeal, R.IsPrime → (extendIdeal R).IsPrime →
    R.IsHomogeneous (homogeneousSubmodule (Fin K1_13.taylorLength) K1_13.Geom) →
    dimension R = 2 →
    dimension (freshImage R) = 2 ∧
    2 * affineDegree (extendIdeal R) ≤
      133671 * (residueDegree freshJetMap (extendIdeal R) : ℚ) *
        affineDegree (freshImage R)
def c4 : Prop :=
  ∀ (k σ τ : Type) [Field k] [Finite σ] [Finite τ]
    (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k), IsLinearProjection φ →
    ∀ A : Ideal (MvPolynomial σ k), A.IsPrime → dimension A = 2 → IsBirationalOn φ A →
      dimension (A.comap φ) = 2 ∧
      ∀ P, (boundaryIdeal A).IsMinimalPrime P → dimension (P.comap φ) = 2 →
        (boundaryIdeal (A.comap φ)).IsMinimalPrime (P.comap φ)
def c5 : Prop := by
  classical
  exact ∀ (k σ τ : Type) [Field k] [Finite σ] [Finite τ]
    (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k), IsLinearProjection φ →
    ∀ A : Ideal (MvPolynomial σ k), A.IsPrime → IsBirationalOn φ A →
    ∀ Q : Ideal (MvPolynomial τ k), (boundaryIdeal (A.comap φ)).IsMinimalPrime Q →
      (∑ P ∈ (boundaryIdeal A).minimalPrimesFinset.filter (fun P => P.comap φ = Q),
        boundaryWeight (boundaryIdeal A) P * residueDegree φ.toRingHom P) ≤
      boundaryWeight (boundaryIdeal (A.comap φ)) Q
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5) :
    K1_13_6_3.c5 := by
  classical
  intro A hA hAe hdim hbir
  let B := extendIdeal A
  let C := freshImage A
  let S := (boundaryIdeal B).minimalPrimesFinset
  let T := (boundaryIdeal C).minimalPrimesFinset
  let image (P : Ideal FreshCoeffRing) : JetIdeal := P.comap freshJetMap
  let weight (P : Ideal FreshCoeffRing) : ℕ := boundaryWeight (boundaryIdeal B) P
  let rank (P : Ideal FreshCoeffRing) : ℕ := residueDegree freshJetMap P
  obtain ⟨hpoly, hdescend⟩ := h2 A hA
  have hdimB : dimension B = 2 :=
    (congrArg Polynomial.natDegree hpoly).trans hdim
  have hdegree : affineDegree A = affineDegree B := by
    change affineDegree A = affineDegree (extendIdeal A)
    simp only [affineDegree, hpoly]
  have hbirB : IsBirationalOn freshProjection B := hbir
  obtain ⟨hdimC, hproject⟩ := h4 _ _ _ freshProjection freshProjection_linear B hAe hdimB hbirB
  have hC : C.IsPrime := by
    let _ : B.IsPrime := hAe
    exact Ideal.IsPrime.comap freshJetMap
  have hdimC' : dimension C = 2 := hdimC
  have hheight (P : Ideal FreshCoeffRing) (hP : P ∈ S) :
      dimension (image P) = 2 ∧
      2 * affineDegree P ≤ 133671 * (rank P : ℚ) * affineDegree (image P) := by
    have hp := Ideal.mem_minimalPrimesFinset.mp hP
    obtain ⟨R, hR, rfl⟩ := hdescend P hp
    obtain ⟨hd, hhom⟩ := (h1 _ _ A hA hdim).1 R hR
    exact h3 R hR.isPrime hp.isPrime hhom hd
  have hmaps (P : Ideal FreshCoeffRing) (hP : P ∈ S) : image P ∈ T := by
    apply Ideal.mem_minimalPrimesFinset.mpr
    exact hproject P (Ideal.mem_minimalPrimesFinset.mp hP) (hheight P hP).1
  have hfibre (Q : JetIdeal) (hQ : Q ∈ T) :
      (∑ P ∈ S.filter (fun P => image P = Q), weight P * rank P) ≤
        boundaryWeight (boundaryIdeal C) Q := by
    exact h5 _ _ _ freshProjection freshProjection_linear B hAe hbirB Q
      (Ideal.mem_minimalPrimesFinset.mp hQ)
  calc
    2 * affineDegree A = 2 * ∑ P ∈ S, (weight P : ℚ) * affineDegree P := by
      rw [hdegree, (h1 _ _ B hAe hdimB).2]
    _ ≤ ∑ P ∈ S, 133671 * ((weight P * rank P : ℕ) : ℚ) * affineDegree (image P) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro P hP
      push_cast
      calc
        2 * ((weight P : ℚ) * affineDegree P) =
            (weight P : ℚ) * (2 * affineDegree P) := by ring
        _ ≤ (weight P : ℚ) * (133671 * (rank P : ℚ) * affineDegree (image P)) :=
          mul_le_mul_of_nonneg_left (hheight P hP).2 (by positivity)
        _ = _ := by ring
    _ = ∑ Q ∈ T, ∑ P ∈ S.filter (fun P => image P = Q),
        133671 * ((weight P * rank P : ℕ) : ℚ) * affineDegree (image P) :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ Q ∈ T, 133671 * (boundaryWeight (boundaryIdeal C) Q : ℚ) * affineDegree Q := by
      apply Finset.sum_le_sum
      intro Q hQ
      calc
        _ = ∑ P ∈ S.filter (fun P => image P = Q),
            133671 * ((weight P * rank P : ℕ) : ℚ) * affineDegree Q := by
          apply Finset.sum_congr rfl
          intro P hP
          rw [(Finset.mem_filter.mp hP).2]
        _ = 133671 * ((∑ P ∈ S.filter (fun P => image P = Q), weight P * rank P : ℕ) : ℚ) *
            affineDegree Q := by
          rw [Nat.cast_sum, Finset.mul_sum, Finset.sum_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by exact_mod_cast hfibre Q hQ) (by positivity))
          (affineDegree_nonneg Q)
    _ = 133671 * affineDegree C := by
      rw [(h1 _ _ C hC hdimC').2, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => mul_assoc ..)
end
end K1_13_6_3_5
end
section
set_option autoImplicit false
namespace K1_13_6_3_4
noncomputable section
open K1_13_6_3 MvPolynomial
def boundaryIdeal {k σ : Type*} [Field k] (I : Ideal (MvPolynomial σ k)) :
    Ideal (MvPolynomial σ k) :=
  Ideal.span {q | ∃ (p : MvPolynomial σ k) (n : ℕ),
    p ∈ I ∧ p.totalDegree ≤ n ∧ q = homogeneousComponent n p}
def boundaryChart {k σ : Type*} [Field k] (I : Ideal (MvPolynomial σ k)) (i : σ) :
    Ideal (MvPolynomial σ k) :=
  boundaryIdeal I ⊔ Ideal.span {MvPolynomial.X i - 1}
def NoBoundaryZero {k σ : Type*} [Field k] (I : Ideal (MvPolynomial σ k))
    (ℓ : MvPolynomial σ k) : Prop :=
  ∀ b : σ → k, b ∈ zeroLocus k (boundaryIdeal I) → eval b ℓ = 0 → b = 0
def ValueReduction {k σ : Type*} [Field k] (I : Ideal (MvPolynomial σ k))
    (ℓ : MvPolynomial σ k) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ quotientDegreeLE I (n + 1),
    ∃ a ∈ quotientDegreeLE I n, ∃ b ∈ quotientDegreeLE I n,
      z = a + Ideal.Quotient.mk I ℓ * b
end
end K1_13_6_3_4
end
section
set_option autoImplicit false
namespace K1_13_5_4_4_2
noncomputable section
open MvPolynomial K1_13_6_3_4
open scoped MonomialOrder
variable {k σ : Type*} [Field k]
theorem component_mul_homogeneous {p q : MvPolynomial σ k} {d : ℕ}
    (hq : q.IsHomogeneous d) (n : ℕ) :
    homogeneousComponent n (p * q) =
      if d ≤ n then homogeneousComponent (n - d) p * q else 0 := by
  classical
  conv_lhs => rw [← sum_homogeneousComponent p, Finset.sum_mul, map_sum]
  simp only [homogeneousComponent_of_mem ((homogeneousComponent_isHomogeneous _ _).mul hq)]
  by_cases hd : d ≤ n
  · rw [ite_eq_left hd]
    by_cases hr : n - d ∈ Finset.range (p.totalDegree + 1)
    · rw [Finset.sum_eq_single_of_mem (n - d) hr]
      · simp [Nat.sub_add_cancel hd]
      · intro b _ hb
        rw [ite_eq_right (by omega)]
    · have hlt : p.totalDegree < n - d := by
        rw [Finset.mem_range] at hr
        omega
      rw [homogeneousComponent_eq_zero _ _ hlt, zero_mul]
      exact Finset.sum_eq_zero fun b hb => ite_eq_right (by
        have := Finset.mem_range.mp hb
        omega)
  · rw [ite_eq_right hd]
    exact Finset.sum_eq_zero fun b _ => ite_eq_right (by omega)
theorem lift_boundary_component (I : Ideal (MvPolynomial σ k)) {q : MvPolynomial σ k}
    (hq : q ∈ boundaryIdeal I) (n : ℕ) :
    ∃ p ∈ I, p.totalDegree ≤ n ∧ homogeneousComponent n p = homogeneousComponent n q := by
  revert n
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨p, d, hp, hd, rfl⟩ := hq
    intro n
    by_cases h : n = d
    · subst n
      exact ⟨p, hp, hd, (homogeneousComponent_eq_self (homogeneousComponent_isHomogeneous d p)).symm⟩
    · exact ⟨0, I.zero_mem, by simp, by
        rw [homogeneousComponent_of_mem (homogeneousComponent_isHomogeneous d p), ite_eq_right h, map_zero]⟩
  | zero => exact fun _ => ⟨0, I.zero_mem, by simp, rfl⟩
  | add q r _ _ hq hr =>
    intro n
    obtain ⟨p, hp, hn, he⟩ := hq n
    obtain ⟨s, hs, hm, hf⟩ := hr n
    exact ⟨p + s, I.add_mem hp hs, (totalDegree_add _ _).trans (max_le hn hm), by
      rw [map_add, map_add, he, hf]⟩
  | smul a q _ hq =>
    intro n
    change ∃ p ∈ I, p.totalDegree ≤ n ∧ homogeneousComponent n p = homogeneousComponent n (a * q)
    induction a using MvPolynomial.induction_on' with
    | monomial e c =>
      rw [mul_comm, component_mul_homogeneous (isHomogeneous_monomial c rfl)]
      split_ifs with h
      · obtain ⟨p, hp, hn, he⟩ := hq (n - e.degree)
        refine ⟨p * monomial e c, I.mul_mem_right _ hp,
          (totalDegree_mul _ _).trans ?_, ?_⟩
        · have hmono := (isHomogeneous_monomial c (rfl : e.degree = e.degree)).totalDegree_le
          omega
        · rw [component_mul_homogeneous (isHomogeneous_monomial c rfl), ite_eq_left h, he]
      · exact ⟨0, I.zero_mem, by simp, map_zero _⟩
    | add a b ha hb =>
      obtain ⟨p, hp, hn, he⟩ := ha
      obtain ⟨s, hs, hm, hf⟩ := hb
      exact ⟨p + s, I.add_mem hp hs, (totalDegree_add _ _).trans (max_le hn hm), by
        rw [add_mul, map_add, map_add, he, hf]⟩
theorem boundary_component_mem (I : Ideal (MvPolynomial σ k)) {q : MvPolynomial σ k}
    (hq : q ∈ boundaryIdeal I) (n : ℕ) : homogeneousComponent n q ∈ boundaryIdeal I := by
  obtain ⟨p, hp, hd, he⟩ := lift_boundary_component I hq n
  exact Ideal.subset_span ⟨p, n, hp, hd, he.symm⟩
theorem leading_component [LinearOrder σ] [WellFoundedGT σ]
    {p : MvPolynomial σ k} (hp : p ≠ 0) :
    (homogeneousComponent p.totalDegree p) ≠ 0 ∧
      MonomialOrder.degLex.degree (homogeneousComponent p.totalDegree p) =
        MonomialOrder.degLex.degree p := by
  let m := MonomialOrder.degLex (σ := σ)
  have hmem := m.degree_mem_support hp
  have htop : m.degree p ∈ (homogeneousComponent p.totalDegree p).support := by
    rw [support_homogeneousComponent, Finset.mem_filter]
    exact ⟨hmem, degree_degLexDegree⟩
  have hne : (homogeneousComponent p.totalDegree p) ≠ 0 := by
    intro h
    simp [h] at htop
  refine ⟨hne, m.toSyn.injective (le_antisymm ?_ (m.le_degree htop))⟩
  apply m.le_degree
  have h := m.degree_mem_support hne
  rw [support_homogeneousComponent, Finset.mem_filter] at h
  exact h.1
theorem hilbertPolynomial_boundary [LinearOrder σ] [WellFoundedGT σ] [Finite σ]
    (I : Ideal (MvPolynomial σ k)) :
    affineHilbertPolynomial (boundaryIdeal I) = affineHilbertPolynomial I := by
  have he : MonomialOrder.degLex.standardExponents (boundaryIdeal I) =
      MonomialOrder.degLex.standardExponents I := by
    ext e
    constructor
    · intro h p hp hp₀ hle
      obtain ⟨hq, hd⟩ := leading_component hp₀
      exact h _ (Ideal.subset_span ⟨p, p.totalDegree, hp, le_rfl, rfl⟩) hq (hd.symm ▸ hle)
    · intro h q hq hq₀ hle
      obtain ⟨p, hp, hn, htop⟩ := lift_boundary_component I hq q.totalDegree
      obtain ⟨hne, hd⟩ := leading_component hq₀
      have heq : p.totalDegree = q.totalDegree := by
        by_contra h
        rw [homogeneousComponent_eq_zero _ _ (lt_of_le_of_ne hn h)] at htop
        exact hne htop.symm
      have hp₀ : p ≠ 0 := fun h => hne (by simpa [h] using htop.symm)
      have hd' := (leading_component hp₀).2
      rw [heq, htop, hd] at hd'
      exact h p hp hp₀ (hd'.symm ▸ hle)
  obtain ⟨N, hN⟩ := exists_eval_affineHilbertPolynomial I
  symm
  apply eq_affineHilbertPolynomial_of_eval_eq (N₀ := N)
  intro n hn
  rw [affineHilbertFunction_eq_standard_count, he, ← affineHilbertFunction_eq_standard_count]
  exact hN n hn
end
end K1_13_5_4_4_2
end
section
set_option autoImplicit false
namespace K1_13_5_4_4_2
noncomputable section
open MvPolynomial K1_13_6_3_4
variable {k K σ : Type*} [Field k] [Field K] [Algebra k K]
theorem linear_cut_regular (I : Ideal (MvPolynomial σ k)) (i : σ) :
    IsLeftRegular (Ideal.Quotient.mk (boundaryIdeal I) (MvPolynomial.X i - 1)) := by
  rw [isLeftRegular_iff_right_eq_zero_of_mul]
  intro z hz
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hz
  have h (n : ℕ) : homogeneousComponent n p ∈ boundaryIdeal I := by
    induction n with
    | zero =>
      have h₀ := boundary_component_mem I hz 0
      rw [sub_mul, one_mul, map_sub, mul_comm (MvPolynomial.X i),
        component_mul_homogeneous (isHomogeneous_X k i), ite_eq_right (by omega), zero_sub] at h₀
      exact neg_mem_iff.mp h₀
    | succ n ih =>
      have hn := boundary_component_mem I hz (n + 1)
      rw [sub_mul, one_mul, map_sub, mul_comm (MvPolynomial.X i),
        component_mul_homogeneous (isHomogeneous_X k i), ite_eq_left (by omega),
        Nat.add_sub_cancel] at hn
      exact (Submodule.sub_mem_iff_right (boundaryIdeal I) (Ideal.mul_mem_right _ _ ih)).mp hn
  rw [Ideal.Quotient.eq_zero_iff_mem, ← sum_homogeneousComponent p]
  exact (boundaryIdeal I).sum_mem fun n _ => h n
theorem boundaryChart_dimension [Finite σ] [LinearOrder σ] [WellFoundedGT σ]
    (I : Ideal (MvPolynomial σ k)) (hI : (affineHilbertPolynomial I).natDegree = 1) (i : σ) :
    (affineHilbertPolynomial (boundaryChart I i)).natDegree = 0 := by
  have hdeg : (MvPolynomial.X i - 1 : MvPolynomial σ k).totalDegree ≤ 1 :=
    (totalDegree_sub _ _).trans (max_le (totalDegree_X i).le (by simp))
  have h := (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le
    (linear_cut_regular I i) hdeg).1
  rw [hilbertPolynomial_boundary I, hI] at h
  exact Nat.eq_zero_of_le_zero h
theorem drop_component {p : MvPolynomial σ k} {n : ℕ} (h : p.totalDegree ≤ n + 1) :
    (p - homogeneousComponent (n + 1) p).totalDegree ≤ n := by
  refine Finset.sup_le fun d hd => ?_
  change d.degree ≤ n
  rw [MvPolynomial.mem_support_iff, coeff_sub, coeff_homogeneousComponent] at hd
  by_contra! hnd
  have hs : n + 1 ≤ d.degree := Nat.succ_le_of_lt hnd
  rcases eq_or_lt_of_le hs with he | hlt
  · simp [← he] at hd
  · have hp := coeff_eq_zero_of_totalDegree_lt (lt_of_le_of_lt h hlt)
    simp [hp] at hd
theorem valueReduction_of_geometric [Finite σ] [IsAlgClosed K] (I : Ideal (MvPolynomial σ k))
    {l : MvPolynomial σ k} (hl : l.IsHomogeneous 1)
    (hfree : ∀ x : σ → K, x ∈ zeroLocus K (boundaryIdeal I) → aeval x l = 0 → x = 0) :
    ValueReduction I l := by
  let J := boundaryIdeal I ⊔ Ideal.span {l}
  have hrad : idealOfVars σ k ≤ J.radical := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := K)]
    intro x hx
    rw [aeval_X, hfree x (zeroLocus_anti_mono (le_sup_left : boundaryIdeal I ≤ J) hx)
      (hx l (Ideal.mem_sup_right (Ideal.mem_span_singleton_self l)))]
    rfl
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (idealOfVars_fg σ k)
  refine ⟨N, fun n hn z hz => ?_⟩
  obtain ⟨p, hp, rfl⟩ := mem_quotientDegreeLE.mp hz
  have hm : homogeneousComponent (n + 1) p ∈ J := by
    apply hN
    apply (mem_pow_idealOfVars_iff N _).2
    intro e he
    have heq : e.degree = n + 1 := by
      by_contra hne
      exact (MvPolynomial.mem_support_iff.mp he) ((homogeneousComponent_isHomogeneous (n + 1) p).coeff_eq_zero hne)
    omega
  obtain ⟨q, hq, r, hr, he⟩ := Submodule.mem_sup.mp hm
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  obtain ⟨u, hu, hdu, huc⟩ := lift_boundary_component I hq (n + 1)
  have hc : homogeneousComponent (n + 1) (p - u - l * homogeneousComponent n s) = 0 := by
    have ht := congrArg (homogeneousComponent (n + 1)) he
    rw [homogeneousComponent_eq_self (homogeneousComponent_isHomogeneous _ _),
      map_add, component_mul_homogeneous hl, ite_eq_left (by omega), Nat.add_sub_cancel] at ht
    rw [map_sub, map_sub, huc, ← ht, add_sub_cancel_left, mul_comm l,
      homogeneousComponent_eq_self ((homogeneousComponent_isHomogeneous _ _).mul hl), sub_self]
  let a := p - u - l * homogeneousComponent n s
  have ha : a.totalDegree ≤ n + 1 :=
    (totalDegree_sub _ _).trans (max_le ((totalDegree_sub _ _).trans (max_le hp hdu))
      ((totalDegree_mul _ _).trans (by
        have hs := (homogeneousComponent_isHomogeneous n s).totalDegree_le
        have hld := hl.totalDegree_le
        omega)))
  have ha' : a.totalDegree ≤ n := by simpa [a, hc] using drop_component ha
  refine ⟨Ideal.Quotient.mk I a, mk_mem_quotientDegreeLE ha',
    Ideal.Quotient.mk I (homogeneousComponent n s),
    mk_mem_quotientDegreeLE ((homogeneousComponent_isHomogeneous _ _).totalDegree_le), ?_⟩
  rw [← map_mul, ← map_add]
  dsimp only [a]
  rw [sub_add_cancel, map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hu, sub_zero]
end
end K1_13_5_4_4_2
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 MvPolynomial
open scoped Polynomial WithZero
variable (k L : Type) [Field k] [Field L] [Algebra k L]
def CurveField : Prop :=
  ∃ t : L, Transcendental k t ∧ Module.Finite (IntermediateField.adjoin k {t}) L
structure CurvePlace where
  value : Valuation L ℤᵐ⁰
  normalized : Function.Surjective value
  on_constants : ∀ c : k, c ≠ 0 → value (algebraMap k L c) = 1
variable {L} in
def poleOrder (v : Valuation L ℤᵐ⁰) (x : L) : ℕ :=
  (WithZero.log (v x)).toNat
variable {L} in
def zeroOrder (v : Valuation L ℤᵐ⁰) (x : L) : ℕ :=
  (-WithZero.log (v x)).toNat
variable {L} in
def tuplePole {σ : Type} [Fintype σ] (v : Valuation L ℤᵐ⁰) (u : σ → L) : ℕ :=
  Finset.univ.sup (fun i => poleOrder v (u i))
def tupleHeight {σ : Type} [Fintype σ] (u : σ → L) : ℕ :=
  ∑ᶠ v : CurvePlace k L, tuplePole v.value u
def PrincipalDivisors : Prop :=
  ∀ x : L,
    (fun v : CurvePlace k L => poleOrder v.value x).HasFiniteSupport ∧
    (fun v : CurvePlace k L => zeroOrder v.value x).HasFiniteSupport ∧
    (∑ᶠ v : CurvePlace k L, poleOrder v.value x) =
      (∑ᶠ v : CurvePlace k L, zeroOrder v.value x) ∧
    (Transcendental k x →
      (∑ᶠ v : CurvePlace k L, poleOrder v.value x) =
        Module.finrank (IntermediateField.adjoin k {x}) L)
variable {L} in
def coneEval {σ : Type} (u : σ → L) : MvPolynomial σ k →+* L[X] :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap k L))
    (fun i => Polynomial.C (u i) * Polynomial.X)
variable {L} in
def coneIdeal {σ : Type} (u : σ → L) : Ideal (MvPolynomial σ k) :=
  RingHom.ker (coneEval k u)
variable {L} in
def ratios {σ : Type} (u : σ → L) (i₀ : σ) (i : σ) : L := u i / u i₀
variable {L} in
def ratioField {σ : Type} (u : σ → L) (i₀ : σ) : IntermediateField k L :=
  IntermediateField.adjoin k (Set.range (ratios u i₀))
variable {L} in
def coefficientTuple {F : Type} [Field F] {N : ℕ} (j : F →+* L) (f : F[X])
    (i : Fin N) : L := j (f.coeff i.val)
variable {L} in
def jetTuple {F : Type} [Field F] {n : ℕ} (j : F →+* L) (a : L) (f : F[X])
    (i : Fin n) : L := (Polynomial.hasseDeriv i.val f).eval₂ j a
structure FreshCurve (R : CoeffIdeal) where
  Old : Type
  Fresh : Type
  [oldField : Field Old]
  [freshField : Field Fresh]
  [oldAlgebra : Algebra Geom Old]
  [freshAlgebra : Algebra GeoField Fresh]
  oldCurve : CurveField Geom Old
  freshCurve : CurveField GeoField Fresh
  includeOld : Old →+* Fresh
  constants : includeOld.comp (algebraMap Geom Old) =
    (algebraMap GeoField Fresh).comp geomConstants
  independent : Function.Injective
    (Polynomial.eval₂RingHom includeOld (algebraMap GeoField Fresh genericArgument))
  polynomial : Old[X]
  monic : polynomial.Monic
  degree_le : polynomial.natDegree ≤ 133671
  equation : extendIdeal R =
    coneIdeal GeoField (coefficientTuple (N := taylorLength) includeOld polynomial)
  generates : IntermediateField.adjoin GeoField
    (Set.range (coefficientTuple (N := taylorLength) includeOld polynomial)) = ⊤
  nonconstant : ∃ i : Fin taylorLength,
    Transcendental GeoField (coefficientTuple includeOld polynomial i)
attribute [instance] FreshCurve.oldField FreshCurve.freshField
  FreshCurve.oldAlgebra FreshCurve.freshAlgebra
variable {L} in
def FreshCurve.center {R : CoeffIdeal} (D : FreshCurve R) : D.Fresh :=
  algebraMap GeoField D.Fresh genericArgument
variable {L} in
def FreshCurve.coefficients {R : CoeffIdeal} (D : FreshCurve R) :
    Fin taylorLength → D.Fresh :=
  coefficientTuple D.includeOld D.polynomial
variable {L} in
def FreshCurve.jets {R : CoeffIdeal} (D : FreshCurve R) {n : ℕ} :
    Fin n → D.Fresh :=
  jetTuple D.includeOld D.center D.polynomial
variable {L} in
def FreshGauss {F : Type} [Field F] (j : F →+* L) (a : L)
    (v : Valuation L ℤᵐ⁰) : Prop :=
  (∀ x : F, x ≠ 0 → v (j x) = 1) ∨
  (∀ g : F[X], v (g.eval₂ j a) = g.support.sup (fun i => v (j (g.coeff i))))
structure JetFactors {F : Type} [Field F] (f : F[X]) where
  count : ℕ
  factor : Fin count → F[X]
  multiplicity : Fin count → ℕ
  monic : ∀ i, (factor i).Monic
  separable : ∀ i, (factor i).Separable
  coprime : ∀ i j, i ≠ j → IsCoprime (factor i) (factor j)
  positive : ∀ i, 0 < multiplicity i
  le_degree : ∀ i, multiplicity i ≤ f.natDegree
  first_scalar : ∀ i, (multiplicity i : F) ≠ 0
  second_scalar : ∀ i, 2 ≤ multiplicity i → ((multiplicity i).choose 2 : F) ≠ 0
  product_eq : f = ∏ i, factor i ^ multiplicity i
end
end K1_13_6_3_5_3
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_3
noncomputable section
open Polynomial UniqueFactorizationMonoid
open scoped Polynomial
theorem cast_ne_zero_of_pos_lt {F : Type} [Field F] {p n : ℕ} [CharP F p]
    (hpos : 0 < n) (hlt : n < p) : (n : F) ≠ 0 := by
  intro h
  exact (not_le_of_gt hlt) (Nat.le_of_dvd hpos ((CharP.cast_eq_zero_iff F p n).mp h))
theorem separable_of_small_degree {F : Type} [Field F] {p : ℕ} [CharP F p]
    {q : F[X]} (hirr : Irreducible q) (hdeg : q.natDegree < p) : q.Separable := by
  apply (Polynomial.separable_iff_derivative_ne_zero hirr).mpr
  have hstep : q.natDegree - 1 + 1 = q.natDegree := by have := hirr.natDegree_pos; omega
  intro hz
  have hc := congrArg (fun x : F[X] => x.coeff (q.natDegree - 1)) hz
  rw [coeff_derivative, ← Nat.cast_succ, hstep, coeff_natDegree, coeff_zero] at hc
  apply mul_ne_zero (leadingCoeff_ne_zero.mpr hirr.ne_zero)
    (cast_ne_zero_of_pos_lt hirr.natDegree_pos hdeg)
  simpa only [Nat.succ_eq_add_one, hstep] using hc
def factorsOfMonic {F : Type} [Field F] {p : ℕ} [CharP F p] {f : F[X]}
    (hf : f.Monic) (hdeg : f.natDegree < p) (htwo : 2 < p) : JetFactors f := by
  classical
  let S := (normalizedFactors f).toFinset
  let e := (Fintype.equivFin S).symm
  let q := fun i => (e i).val
  let m := fun i => (normalizedFactors f).count (q i)
  have hmem (i : Fin (Fintype.card S)) : q i ∈ normalizedFactors f :=
    Multiset.mem_toFinset.mp (e i).property
  have hdata (i : Fin (Fintype.card S)) :
      Irreducible (q i) ∧ (q i).Monic ∧ q i ∣ f :=
    (Polynomial.mem_normalizedFactors_iff hf.ne_zero).mp (hmem i)
  have hprod : (∏ i, q i ^ m i) = f := calc
    _ = ∏ x : S, x.val ^ (normalizedFactors f).count x.val :=
      Fintype.prod_equiv e _ _ (fun _ => rfl)
    _ = (normalizedFactors f).prod := by
      exact (Finset.prod_coe_sort S (fun x => x ^ (normalizedFactors f).count x)).trans
        (Finset.prod_multiset_count _).symm
    _ = f := by
      simpa only [hf.leadingCoeff, Polynomial.C_1, one_mul]
        using Polynomial.leadingCoeff_mul_prod_normalizedFactors f
  have hsum : f.natDegree = ∑ i, m i * (q i).natDegree := by
    rw [← hprod, Polynomial.natDegree_prod_of_monic Finset.univ (fun i => q i ^ m i)
      (fun i _ => (hdata i).2.1.pow _)]
    exact Finset.sum_congr rfl fun i _ => (hdata i).2.1.natDegree_pow _
  have hm_pos (i : Fin (Fintype.card S)) : 0 < m i := Multiset.count_pos.mpr (hmem i)
  have hm_le (i : Fin (Fintype.card S)) : m i ≤ f.natDegree := calc
    m i = m i * 1 := (Nat.mul_one _).symm
    _ ≤ m i * (q i).natDegree := Nat.mul_le_mul_left _ (hdata i).1.natDegree_pos
    _ ≤ f.natDegree := by
      rw [hsum]
      exact Finset.single_le_sum (f := fun j => m j * (q j).natDegree)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hm_cast (i : Fin (Fintype.card S)) : (m i : F) ≠ 0 :=
    cast_ne_zero_of_pos_lt (hm_pos i) ((hm_le i).trans_lt hdeg)
  refine ⟨_, q, m, fun i => (hdata i).2.1, ?_, ?_, hm_pos, hm_le, hm_cast, ?_, hprod.symm⟩
  · intro i
    exact separable_of_small_degree (hdata i).1
      ((natDegree_le_of_dvd (hdata i).2.2 hf.ne_zero).trans_lt hdeg)
  · intro i j hij
    apply (hdata i).1.coprime_iff_not_dvd.mpr
    intro hdiv
    have heq := eq_of_monic_of_associated (hdata i).2.1 (hdata j).2.1
      ((hdata i).1.associated_of_dvd (hdata j).1 hdiv)
    exact hij (e.injective (Subtype.ext heq))
  · intro i hi
    have : NeZero (2 : F) := ⟨by
      exact_mod_cast (cast_ne_zero_of_pos_lt (F := F) (by decide : 0 < 2) htwo)⟩
    have hm₁ : ((m i - 1 : ℕ) : F) ≠ 0 :=
      cast_ne_zero_of_pos_lt (by omega) ((Nat.sub_le _ _).trans_lt ((hm_le i).trans_lt hdeg))
    have hm₁' : (m i : F) - 1 ≠ 0 := by
      simpa only [Nat.cast_sub (by omega : 1 ≤ m i), Nat.cast_one] using hm₁
    rw [Nat.cast_choose_two]
    exact div_ne_zero (mul_ne_zero (hm_cast i) hm₁') (NeZero.ne _)
end
end K1_13_6_3_5_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1600
namespace K1_13_6_3_5_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 K1_13_6_3_5 MvPolynomial
open scoped Polynomial WithZero
attribute [local instance] MvPolynomial.gradedAlgebra
def c1 : Prop :=
  ∀ R : CoeffIdeal, R.IsPrime → (extendIdeal R).IsPrime →
    R.IsHomogeneous (homogeneousSubmodule (Fin taylorLength) Geom) →
    dimension R = 2 → Nonempty (FreshCurve R)
def c2 : Prop :=
  ∀ (k L : Type) [Field k] [IsAlgClosed k] [Field L] [Algebra k L],
    CurveField k L → PrincipalDivisors k L
def c3 : Prop :=
  ∀ (k L σ : Type) [Field k] [IsAlgClosed k] [Field L] [Algebra k L] [Fintype σ],
    CurveField k L → PrincipalDivisors k L →
    ∀ (u : σ → L) (i : σ), u i ≠ 0 →
      ((∃ j, Transcendental k (ratios u i j)) ↔ 0 < tupleHeight k L (ratios u i)) ∧
      (0 < tupleHeight k L (ratios u i) →
        dimension (coneIdeal k u) = 2 ∧
        (tupleHeight k L (ratios u i) : ℚ) =
          (Module.finrank (ratioField k u i) L : ℚ) * affineDegree (coneIdeal k u))
def c4 : Prop :=
  ∀ (k L σ τ : Type) [Field k] [Field L] [Algebra k L],
    ∀ (u : σ → L) (i : σ) (v : τ → L) (j : τ)
      (φ : MvPolynomial τ k →+* MvPolynomial σ k),
      u i ≠ 0 → v j ≠ 0 → ratioField k u i = ⊤ →
      (coneEval k u).comp φ = coneEval k v →
      residueDegree φ (coneIdeal k u) = Module.finrank (ratioField k v j) L
def c5 : Prop :=
  ∀ (R : CoeffIdeal) (D : FreshCurve R) (v : CurvePlace GeoField D.Fresh),
    FreshGauss D.includeOld D.center v.value
def c6 : Prop :=
  ∀ (F L : Type) [Field F] [Field L]
    (j : F →+* L) (a : L) (f : F[X]) (B : JetFactors f)
    (v : Valuation L ℤᵐ⁰) (N : ℕ),
    f.natDegree < N → v a = 1 →
    Function.Injective (Polynomial.eval₂RingHom j a) →
    FreshGauss j a v →
      tuplePole v (coefficientTuple (N := N) j f) =
        ∑ r, B.multiplicity r * poleOrder v ((B.factor r).eval₂ j a) ∧
      tuplePole v (ratios (jetTuple (n := 3) j a f) 0) =
        ∑ r, min (B.multiplicity r) 2 * zeroOrder v ((B.factor r).eval₂ j a)
theorem hasFiniteSupport_tuplePole {k L σ : Type}
    [Field k] [Field L] [Algebra k L] [Fintype σ]
    (h : PrincipalDivisors k L) (u : σ → L) :
    (fun v : CurvePlace k L => tuplePole v.value u).HasFiniteSupport := by
  have hf : (⋃ i : σ, Function.support (fun v : CurvePlace k L =>
      poleOrder v.value (u i))).Finite := Set.finite_iUnion fun i => (h (u i)).1
  apply hf.subset
  intro v hv
  simp only [Set.mem_iUnion, Function.mem_support] at hv ⊢
  by_contra! hz
  exact hv (Finset.sup_eq_bot_iff _ _ |>.mpr fun i _ => hz i)
private theorem tupleHeight_le_of_inclusion {k L σ τ : Type}
    [Field k] [Field L] [Algebra k L] [Fintype σ] [Fintype τ]
    (h : PrincipalDivisors k L) (u : σ → L) (w : τ → L) (e : σ → τ)
    (he : ∀ i, u i = w (e i)) :
    tupleHeight k L u ≤ tupleHeight k L w := by
  apply finsum_le_finsum (hasFiniteSupport_tuplePole h u) (hasFiniteSupport_tuplePole h w)
  intro v
  unfold tuplePole
  apply Finset.sup_le
  intro i _
  rw [he i]
  exact Finset.le_sup (s := Finset.univ) (f := fun j => poleOrder v.value (w j))
    (Finset.mem_univ (e i))
private theorem finsum_weighted {α σ : Type} [Fintype σ] (c : σ → ℕ) (f : σ → α → ℕ)
    (hf : ∀ i, (f i).HasFiniteSupport) :
    (∑ᶠ v, ∑ i, c i * f i v) = ∑ i, c i * ∑ᶠ v, f i v := by
  classical
  let s : Set α := ⋃ i, Function.support (f i)
  have hs : s.Finite := Set.finite_iUnion hf
  have hi (i : σ) : Function.support (f i) ⊆ (hs.toFinset : Set α) := by
    rw [Set.Finite.coe_toFinset]
    exact Set.subset_iUnion (fun j => Function.support (f j)) i
  have ha : Function.support (fun v => ∑ i, c i * f i v) ⊆ (hs.toFinset : Set α) := by
    intro v hv
    by_contra h
    exact hv (Finset.sum_eq_zero fun i _ => by
      have hz : f i v = 0 := by
        by_contra hn
        exact h (hi i hn)
      simp [hz])
  rw [finsum_eq_finsetSum_of_support_subset _ ha, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [finsum_eq_finsetSum_of_support_subset _ (hi i), Finset.mul_sum]
theorem jet_eval_sum {F L : Type} [Field F] [Field L]
    (j : F →+* L) (a : L) (f : F[X]) {N : ℕ} (hn : f.natDegree < N) (i : ℕ) :
    (Polynomial.hasseDeriv i f).eval₂ j a =
      ∑ x : Fin N, ((x.val.choose i : L) * a ^ (x.val - i)) * j (f.coeff x.val) := by
  rw [Polynomial.hasseDeriv_apply, f.sum_over_range' (fun _ => by simp) _ hn,
    Polynomial.eval₂_finsetSum, Fin.sum_univ_eq_sum_range (fun x =>
      ((x.choose i : L) * a ^ (x - i)) * j (f.coeff x))]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Polynomial.eval₂_monomial, map_mul, map_natCast]
  ring
theorem cone_eval_hasse {k F L : Type} [Field k] [Field F] [Field L] [Algebra k L]
    (j : F →+* L) (a : k) (f : F[X]) {N n : ℕ} (hdeg : f.natDegree < N) :
    (coneEval k (coefficientTuple (N := N) j f)).comp
      (MvPolynomial.eval₂Hom MvPolynomial.C (fun i : Fin n =>
        ∑ r : Fin N, MvPolynomial.C ((r.val.choose i.val : k) * a ^ (r.val - i.val)) *
          MvPolynomial.X r)) =
      coneEval k (jetTuple (n := n) j (algebraMap k L a) f) := by
  let u : Fin N → L := coefficientTuple j f
  let v : Fin n → L := jetTuple j (algebraMap k L a) f
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [coneEval]
  · intro i
    rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
    have he (r : Fin N) :
        (coneEval k u)
          (MvPolynomial.C ((r.val.choose i.val : k) * a ^ (r.val - i.val)) *
            MvPolynomial.X r) =
          Polynomial.C (((r.val.choose i.val : L) * (algebraMap k L a) ^ (r.val - i.val)) *
            u r) * Polynomial.X := by
      simp [coneEval, mul_assoc]
    rw [show (coneEval k v) (MvPolynomial.X i) =
      Polynomial.C (v i) * Polynomial.X from MvPolynomial.eval₂Hom_X' _ _ _]
    rw [show v i =
      ∑ r : Fin N, ((r.val.choose i.val : L) * (algebraMap k L a) ^ (r.val - i.val)) *
        u r from jet_eval_sum j _ f hdeg i.val]
    rw [map_sum, map_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun r _ => he r
private theorem cone_eval_jets {R : CoeffIdeal} (D : FreshCurve R) :
    (coneEval GeoField D.coefficients).comp freshJetMap = coneEval GeoField (D.jets (n := 4)) :=
  cone_eval_hasse D.includeOld genericArgument D.polynomial (Nat.lt_succ_iff.mpr D.degree_le)
private theorem jet_zero_nonzero {R : CoeffIdeal} (D : FreshCurve R) {n : ℕ} (i : Fin n)
    (hi : i.val = 0) : D.jets i ≠ 0 := by
  unfold FreshCurve.jets jetTuple
  rw [hi, Polynomial.hasseDeriv_zero']
  change (Polynomial.eval₂RingHom D.includeOld D.center) D.polynomial ≠ 0
  exact fun h => D.monic.ne_zero (D.independent (h.trans (map_zero _).symm))
theorem height_comparison (h5 : c5) (h6 : c6) {R : CoeffIdeal} (D : FreshCurve R)
    (hdiv : PrincipalDivisors GeoField D.Fresh) :
    2 * tupleHeight GeoField D.Fresh D.coefficients ≤
      133671 * tupleHeight GeoField D.Fresh (ratios (D.jets (n := 4)) 0) := by
  let : CharP D.Old K1.p := charP_of_injective_ringHom
    ((algebraMap Geom D.Old).comp K1_13.embed).injective K1.p
  have hdeg : D.polynomial.natDegree < taylorLength := Nat.lt_succ_iff.mpr D.degree_le
  have hchar : D.polynomial.natDegree < K1.p := by
    exact D.degree_le.trans_lt (by decide)
  let B := factorsOfMonic D.monic hchar (by decide : 2 < K1.p)
  let z := fun i => (B.factor i).eval₂ D.includeOld D.center
  let r₃ := ratios (D.jets (n := 3)) 0
  let r₄ := ratios (D.jets (n := 4)) 0
  have hc₀ : genericArgument ≠ 0 := by
    have hinj : Function.Injective genericCoeffs :=
      (algebraMap GenericField GeoField).injective.comp
        (IsFractionRing.injective Geom[X] GenericField)
    simpa only [genericArgument, map_zero] using
      hinj.ne (show (Polynomial.X : Geom[X]) ≠ 0 from Polynomial.X_ne_zero)
  have hv (v : CurvePlace GeoField D.Fresh) :=
    h6 D.Old D.Fresh D.includeOld D.center D.polynomial B v.value taylorLength
      hdeg (v.on_constants _ hc₀) D.independent (h5 R D v)
  have hcoeff : tupleHeight GeoField D.Fresh D.coefficients =
      ∑ i, B.multiplicity i * ∑ᶠ v : CurvePlace GeoField D.Fresh, poleOrder v.value (z i) := by
    have hp (v : CurvePlace GeoField D.Fresh) :
        tuplePole v.value D.coefficients = ∑ i, B.multiplicity i * poleOrder v.value (z i) :=
      (hv v).1
    unfold tupleHeight
    simp_rw [hp]
    exact finsum_weighted _ _ (fun i => (hdiv (z i)).1)
  have hjet : tupleHeight GeoField D.Fresh r₃ =
      ∑ i, min (B.multiplicity i) 2 * ∑ᶠ v : CurvePlace GeoField D.Fresh, zeroOrder v.value (z i) := by
    have hp (v : CurvePlace GeoField D.Fresh) :
        tuplePole v.value r₃ = ∑ i, min (B.multiplicity i) 2 * zeroOrder v.value (z i) :=
      (hv v).2
    unfold tupleHeight
    simp_rw [hp]
    exact finsum_weighted _ _ (fun i => (hdiv (z i)).2.1)
  have hmore : tupleHeight GeoField D.Fresh r₃ ≤ tupleHeight GeoField D.Fresh r₄ := by
    apply tupleHeight_le_of_inclusion hdiv r₃ r₄ (Fin.castLE (by decide : 3 ≤ 4))
    intro i
    rfl
  suffices hh : 2 * tupleHeight GeoField D.Fresh D.coefficients ≤
      133671 * tupleHeight GeoField D.Fresh r₃ from
    hh.trans (Nat.mul_le_mul_left _ hmore)
  rw [hcoeff, hjet, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [(hdiv (z i)).2.2.1, ← mul_assoc, ← mul_assoc]
  apply Nat.mul_le_mul_right
  have hm := (B.le_degree i).trans D.degree_le
  by_cases hi : B.multiplicity i ≤ 2
  · rw [min_eq_left hi]
    exact Nat.mul_le_mul_right _ (by decide)
  · rw [min_eq_right (by omega)]
    omega
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) (h5 : c5) (h6 : c6) :
    K1_13_6_3_5.c3 := by
  intro R hR hprime hhom hdim
  obtain ⟨D⟩ := h1 R hR hprime hhom hdim
  have hdiv := h2 GeoField D.Fresh D.freshCurve
  let u := D.coefficients
  let v := D.jets (n := 4)
  have hcone : extendIdeal R = coneIdeal GeoField u := D.equation
  let i : Fin taylorLength := ⟨D.polynomial.natDegree, Nat.lt_succ_iff.mpr D.degree_le⟩
  have hi : u i = 1 := by
    simp [u, i, FreshCurve.coefficients, coefficientTuple, Polynomial.coeff_natDegree,
      D.monic.leadingCoeff]
  have hu : ratios u i = u := by funext j; simp [ratios, hi]
  have hv₀ : v 0 ≠ 0 := jet_zero_nonzero D 0 rfl
  have hgen : ratioField GeoField u i = ⊤ := by
    rw [ratioField, hu]
    exact D.generates
  obtain ⟨hpositive, hsource⟩ :=
    h3 GeoField D.Fresh _ D.freshCurve hdiv u i (by simp [hi])
  have hpos : 0 < tupleHeight GeoField D.Fresh u := by
    rw [← hu]
    exact hpositive.mp (by rw [hu]; exact D.nonconstant)
  have hs : (tupleHeight GeoField D.Fresh u : ℚ) = affineDegree (extendIdeal R) := by
    have h := (hsource (by simpa only [hu] using hpos)).2
    rwa [hu, hgen, IntermediateField.finrank_top, Nat.cast_one, one_mul, ← hcone] at h
  have hcmp := height_comparison h5 h6 D hdiv
  have hjpos : 0 < tupleHeight GeoField D.Fresh (ratios v 0) := by
    change 2 * tupleHeight GeoField D.Fresh u ≤ 133671 * tupleHeight GeoField D.Fresh
      (ratios v 0) at hcmp
    omega
  have himage : coneIdeal GeoField v = freshImage R := by
    rw [freshImage, D.equation]
    change RingHom.ker (coneEval GeoField v) =
      (RingHom.ker (coneEval GeoField u)).comap freshJetMap
    rw [RingHom.comap_ker, cone_eval_jets D]
  have hrank := h4 GeoField D.Fresh _ _ u i v 0 freshJetMap (by simp [hi]) hv₀ hgen
    (cone_eval_jets D)
  rw [← hcone] at hrank
  obtain ⟨hdim', ht⟩ := (h3 GeoField D.Fresh _ D.freshCurve hdiv v 0 hv₀).2 hjpos
  rw [himage, ← hrank] at ht
  refine ⟨himage ▸ hdim', ?_⟩
  have hcmp' : 2 * (tupleHeight GeoField D.Fresh u : ℚ) ≤
      133671 * (tupleHeight GeoField D.Fresh (ratios v 0) : ℚ) := by exact_mod_cast hcmp
  rw [hs, ht] at hcmp'
  simpa only [mul_assoc] using hcmp'
end
end K1_13_6_3_5_3
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_3_2
open K1_13_6_3_5_3
variable (k L : Type) [Field k] [Field L] [Algebra k L]
abbrev ParameterRing (x : L) := Algebra.adjoin k ({x} : Set L)
abbrev Normalization (x : L) := integralClosure (ParameterRing k L x) L
def origin (x : L) : Ideal (ParameterRing k L x) :=
  Ideal.span {⟨x, Algebra.self_mem_adjoin_singleton k x⟩}
abbrev ZeroPlaces (x : L) :=
  {v : CurvePlace k L // zeroOrder v.value x ≠ 0}
end K1_13_6_3_5_3_2
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace K1_13_6_3_5_3_2
noncomputable section
open K1_13_6_3_5_3 IntermediateField
open scoped WithZero Polynomial algebraAdjoinAdjoin nonZeroDivisors
def c1 : Prop :=
  ∀ (k L : Type) [Field k] [IsAlgClosed k] [Field L] [Algebra k L]
    (x : L), Transcendental k x → Module.Finite (IntermediateField.adjoin k {x}) L →
      Module.Finite (ParameterRing k L x) (Normalization k L x)
def c2 : Prop :=
  ∀ (k L : Type) [Field k] [Field L] [Algebra k L] (x : L),
    Transcendental k x → IsDedekindDomain (Normalization k L x) →
    IsFractionRing (Normalization k L x) L →
    ∃ e : ZeroPlaces k L x ≃ (origin k L x).primesOver (Normalization k L x),
      ∀ v, zeroOrder v.val.value x = (e v).val.ramificationIdx (ParameterRing k L x)
variable {k L : Type} [Field k] [Field L] [Algebra k L]
theorem finite_parameter (h : CurveField k L) {x : L}
    (hx : Transcendental k x) : Module.Finite (IntermediateField.adjoin k {x}) L := by
  obtain ⟨t, ht, hfin⟩ := h
  have ht' : IsAlgebraic (IntermediateField.adjoin k {x}) t :=
    isAlgebraic_adjoin_iff.mpr (.adjoin_singleton ht hx
      (isAlgebraic_adjoin_iff.mp (Algebra.IsAlgebraic.isAlgebraic x)))
  let Kxt := restrictScalars k (IntermediateField.adjoin (IntermediateField.adjoin k {x}) {t})
  let Ktx := restrictScalars k (IntermediateField.adjoin (IntermediateField.adjoin k {t}) {x})
  let : Algebra (IntermediateField.adjoin k {x}) Kxt :=
    (IntermediateField.adjoin (IntermediateField.adjoin k {x}) {t}).algebra
  let : Module (IntermediateField.adjoin k {x}) Kxt := Algebra.toModule
  let : SMul (IntermediateField.adjoin k {x}) Kxt := Algebra.toSMul
  let : Algebra (IntermediateField.adjoin k {t}) Ktx :=
    (IntermediateField.adjoin (IntermediateField.adjoin k {t}) {x}).algebra
  let : Module (IntermediateField.adjoin k {t}) Ktx := Algebra.toModule
  let : SMul (IntermediateField.adjoin k {t}) Ktx := Algebra.toSMul
  have : Module.Finite (IntermediateField.adjoin k {x}) Kxt :=
    IntermediateField.adjoin.finiteDimensional ht'.isIntegral
  have : Module.Finite Kxt L := by
    unfold Kxt
    rw [adjoin_simple_comm]
    have : IsScalarTower (IntermediateField.adjoin k {t}) Ktx L := isScalarTower_mid' _
    exact .right (IntermediateField.adjoin k {t}) Ktx L
  have : IsScalarTower (IntermediateField.adjoin k {x}) Kxt L := isScalarTower_mid' _
  exact Module.Finite.trans Kxt L
theorem parameterRing_pid {x : L} (hx : Transcendental k x) :
    IsPrincipalIdealRing (ParameterRing k L x) :=
  IsPrincipalIdealRing.of_surjective (Polynomial.algEquivOfTranscendental k x hx).toRingHom
    (Polynomial.algEquivOfTranscendental k x hx).surjective
private def originEquiv {x : L} (hx : Transcendental k x) :
    (ParameterRing k L x ⧸ origin k L x) ≃ₐ[k] k := by
  let e := Polynomial.algEquivOfTranscendental k x hx
  refine (Ideal.quotientEquivAlg (Ideal.span {Polynomial.X}) (origin k L x) e ?_).symm.trans ?_
  · rw [Ideal.map_span, Set.image_singleton]
    unfold origin
    change Ideal.span {⟨x, Algebra.self_mem_adjoin_singleton k x⟩} = Ideal.span {e Polynomial.X}
    simp only [e, Polynomial.algEquivOfTranscendental_apply_X]
  · rw [show (Ideal.span {Polynomial.X} : Ideal k[X]) =
        Ideal.span {Polynomial.X - Polynomial.C (0 : k)} by rw [map_zero, sub_zero]]
    exact Polynomial.quotientSpanXSubCAlgEquiv (0 : k)
theorem origin_isMaximal {x : L} (hx : Transcendental k x) :
    (origin k L x).IsMaximal :=
  Ideal.Quotient.maximal_of_isField _ ((originEquiv hx).toRingEquiv.isField (Field.toIsField k))
private theorem normalization_dedekind {x : L} (hx : Transcendental k x)
    [Module.Finite (IntermediateField.adjoin k {x}) L]
    [Module.Finite (ParameterRing k L x) (Normalization k L x)] :
    IsDedekindDomain (Normalization k L x) := by
  let A := ParameterRing k L x
  let B := Normalization k L x
  let K := IntermediateField.adjoin k {x}
  have : IsPrincipalIdealRing A := parameterRing_pid hx
  have : IsNoetherianRing B :=
    isNoetherianRing_iff.mpr (isNoetherian_of_tower A (show IsNoetherian A B from inferInstance))
  exact
    { (inferInstance : IsNoetherianRing B),
      Ring.DimensionLEOne.of_isIntegral A B,
      integralClosure.isIntegrallyClosedOfFiniteExtension K with }
theorem sum_origin_indices [IsAlgClosed k] {x : L} (hx : Transcendental k x)
    [Module.Finite (IntermediateField.adjoin k {x}) L]
    [Module.Finite (ParameterRing k L x) (Normalization k L x)] :
    (∑ᶠ P : (origin k L x).primesOver (Normalization k L x),
      P.val.ramificationIdx (ParameterRing k L x)) =
      Module.finrank (IntermediateField.adjoin k {x}) L := by
  classical
  let A := ParameterRing k L x
  let B := Normalization k L x
  let K := IntermediateField.adjoin k {x}
  let p := origin k L x
  have : IsPrincipalIdealRing A := parameterRing_pid hx
  have : IsDedekindDomain B := normalization_dedekind hx
  have : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  have : p.IsMaximal := origin_isMaximal hx
  have : p.IsPrime := Ideal.IsMaximal.isPrime inferInstance
  have : Module.IsTorsionFree A L := .trans_faithfulSMul A K L
  have : Module.IsTorsionFree A B := IsIntegralClosure.isTorsionFree A L
  have : Module.Free A B := by infer_instance
  have hdeg (P : p.primesOver B) : P.val.inertiaDeg A = 1 := by
    have : P.val.IsPrime := P.property.1
    have : P.val.LiesOver p := P.property.2
    have : P.val.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P.val p
    have hp : Function.Surjective (algebraMap k (A ⧸ p)) := by
      intro y
      let e := originEquiv hx
      exact ⟨e y, by rw [← e.symm.commutes, Algebra.algebraMap_self_apply, e.symm_apply_apply]⟩
    have : Algebra.IsIntegral k (A ⧸ p) :=
      ⟨fun y => by obtain ⟨z, rfl⟩ := hp y; exact isIntegral_algebraMap⟩
    let : Field (A ⧸ p) := Ideal.Quotient.field p
    have : Algebra.IsIntegral k (B ⧸ P.val) := .trans (A ⧸ p)
    have hsurj : Function.Surjective (algebraMap (A ⧸ p) (B ⧸ P.val)) := by
      intro y
      obtain ⟨z, hz⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral
        (k := k) (K := B ⧸ P.val)).surjective y
      exact ⟨algebraMap k (A ⧸ p) z, (IsScalarTower.algebraMap_apply _ _ _ _).symm.trans hz⟩
    rw [Ideal.inertiaDeg_eq_of_isMaximal p P.val, Algebra.finrank_eq_one_iff_bijective_algebraMap]
    exact ⟨RingHom.injective _, hsurj⟩
  have hrank : Module.finrank A B = Module.finrank K L := by
    have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L :=
      IsIntegralClosure.isLocalization A K L B
    let b := Module.Basis.localizationLocalization K (nonZeroDivisors A) L (Module.Free.chooseBasis A B)
    rw [Module.finrank_eq_card_chooseBasisIndex, Module.finrank_eq_card_basis b]
  change (∑ᶠ P : p.primesOver B, P.val.ramificationIdx A) = Module.finrank K L
  rw [finsum_eq_sum_of_fintype, ← hrank, ← Ideal.sum_ramification_inertia_eq_finrank p B]
  exact Finset.sum_congr rfl fun P _ => by rw [hdeg, mul_one]
theorem zero_sum [IsAlgClosed k] (h1 : c1) (h2 : c2) (h : CurveField k L)
    {x : L} (hx : Transcendental k x) :
    (fun v : CurvePlace k L => zeroOrder v.value x).HasFiniteSupport ∧
      (∑ᶠ v : CurvePlace k L, zeroOrder v.value x) =
        Module.finrank (IntermediateField.adjoin k {x}) L := by
  classical
  have : Module.Finite (IntermediateField.adjoin k {x}) L := finite_parameter h hx
  have : Module.Finite (ParameterRing k L x) (Normalization k L x) := h1 k L x hx inferInstance
  have : IsDedekindDomain (Normalization k L x) := normalization_dedekind hx
  have : IsFractionRing (Normalization k L x) L :=
    integralClosure.isFractionRing_of_finite_extension (IntermediateField.adjoin k {x}) L
  have : (origin k L x).IsMaximal := origin_isMaximal hx
  obtain ⟨e, he⟩ := h2 k L x hx inferInstance inferInstance
  have : Fintype (ZeroPlaces k L x) := Fintype.ofEquiv _ e.symm
  let f := fun v : CurvePlace k L => zeroOrder v.value x
  have hf : Finite (Function.support f) := by
    change Finite (ZeroPlaces k L x)
    infer_instance
  refine ⟨Set.finite_coe_iff.mp hf, ?_⟩
  change finsum f = _
  calc
    finsum f = ∑ᶠ v : ZeroPlaces k L x, f v.val := by
      change finsum f = ∑ᶠ v : Function.support f, f v.val
      rw [finsum_set_coe_eq_finsum_mem (f := f), finsum_mem_support]
    _ = ∑ᶠ P : (origin k L x).primesOver (Normalization k L x),
          P.val.ramificationIdx (ParameterRing k L x) :=
      finsum_eq_of_bijective e e.bijective he
    _ = _ := sum_origin_indices hx
private theorem adjoin_inv (x : L) :
    IntermediateField.adjoin k ({x⁻¹} : Set L) = IntermediateField.adjoin k {x} := by
  apply le_antisymm <;> apply IntermediateField.adjoin_le_iff.mpr
  · exact Set.singleton_subset_iff.mpr (IntermediateField.inv_mem _ (mem_adjoin_simple_self k x))
  · apply Set.singleton_subset_iff.mpr
    change x ∈ IntermediateField.adjoin k ({x⁻¹} : Set L)
    simpa only [inv_inv] using
      (IntermediateField.adjoin k ({x⁻¹} : Set L)).inv_mem (mem_adjoin_simple_self k x⁻¹)
theorem zeroOrder_inv (v : Valuation L ℤᵐ⁰) (x : L) :
    zeroOrder v x⁻¹ = poleOrder v x := by
  simp [zeroOrder, poleOrder, map_inv₀, WithZero.log_inv]
theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_3_5_3.c2 := by
  intro k L _ _ _ _ h x
  by_cases hx : Transcendental k x
  · have hxi : Transcendental k x⁻¹ := fun hi => hx (IsAlgebraic.inv_iff.mp hi)
    obtain ⟨hz, hsz⟩ := zero_sum h1 h2 h hx
    obtain ⟨hp, hsp⟩ := zero_sum h1 h2 h hxi
    simp_rw [zeroOrder_inv] at hp hsp
    rw [adjoin_inv] at hsp
    exact ⟨hp, hz, hsp.trans hsz.symm, fun _ => hsp⟩
  · have ha : IsAlgebraic k x := not_not.mp hx
    have : Algebra.IsAlgebraic k (IntermediateField.adjoin k {x}) :=
      IntermediateField.isAlgebraic_adjoin_simple ha.isIntegral
    have : Algebra.IsIntegral k (IntermediateField.adjoin k {x}) := inferInstance
    obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral
      (k := k) (K := IntermediateField.adjoin k {x})).surjective (AdjoinSimple.gen k x)
    have hcx : algebraMap k L c = x :=
      congrArg (algebraMap (IntermediateField.adjoin k {x}) L) hc
    have hzero (v : CurvePlace k L) : v.value x = 0 ∨ v.value x = 1 := by
      rw [← hcx]
      by_cases h0 : c = 0
      · simp [h0]
      · exact Or.inr (v.on_constants c h0)
    have hp : (fun v : CurvePlace k L => poleOrder v.value x) = 0 := by
      funext v
      rcases hzero v with hv | hv <;> simp [poleOrder, hv]
    have hz : (fun v : CurvePlace k L => zeroOrder v.value x) = 0 := by
      funext v
      rcases hzero v with hv | hv <;> simp [zeroOrder, hv]
    simp [hp, hz, Function.HasFiniteSupport, hx]
end
end K1_13_6_3_5_3_2
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_1
noncomputable section
open MvPolynomial
variable {k σ : Type*} [Field k]
def closureMap (A : Ideal (MvPolynomial σ k)) :
    MvPolynomial (Option σ) k →ₐ[k] Polynomial (MvPolynomial σ k ⧸ A) :=
  aeval fun i => Polynomial.C (Ideal.Quotient.mk A (i.elim 1 MvPolynomial.X)) * Polynomial.X
def closureIdeal (A : Ideal (MvPolynomial σ k)) : Ideal (MvPolynomial (Option σ) k) :=
  RingHom.ker (closureMap A).toRingHom
def atInfinity : MvPolynomial (Option σ) k →ₐ[k] MvPolynomial σ k :=
  aeval fun i => i.elim 0 MvPolynomial.X
end
end K1_13_6_3_5_1
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_1
noncomputable section
open MvPolynomial K1_13_6_3 K1_13_6_3_5
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k]
theorem closureIdeal_prime (A : Ideal (MvPolynomial σ k)) (hA : A.IsPrime) :
    (closureIdeal A).IsPrime := by
  let _ : A.IsPrime := hA
  exact RingHom.ker_isPrime (closureMap A).toRingHom
theorem not_mem_closureIdeal (A : Ideal (MvPolynomial σ k)) (hA : A.IsPrime) :
    MvPolynomial.X none ∉ closureIdeal A := by
  let _ : A.IsPrime := hA
  change closureMap A (MvPolynomial.X none) ≠ 0
  simp [closureMap]
theorem coeff_closureMap (A : Ideal (MvPolynomial σ k))
    (f : MvPolynomial (Option σ) k) (n : ℕ) :
    (closureMap A f).coeff n =
      Ideal.Quotient.mk A ((aeval fun i : Option σ => i.elim 1 MvPolynomial.X)
        (homogeneousComponent n f)) := by
  let e : MvPolynomial (Option σ) k →ₐ[k] MvPolynomial σ k :=
    aeval fun i => i.elim 1 MvPolynomial.X
  change (closureMap A f).coeff n = Ideal.Quotient.mk A (e (homogeneousComponent n f))
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg =>
    simp [map_add, Polynomial.coeff_add, hf, hg]
  | monomial d r =>
    have hm : closureMap A (monomial d r) =
        Polynomial.C (Ideal.Quotient.mk A (e (monomial d r))) *
          Polynomial.X ^ d.degree := by
      classical
      simp only [closureMap, e, aeval_monomial, Polynomial.algebraMap_apply,
        Finsupp.prod, Finsupp.degree_apply]
      simp only [Ideal.Quotient.mk_algebraMap, map_mul, map_prod, map_pow]
      have hprod :
          (∏ i ∈ d.support,
            (Polynomial.C (Ideal.Quotient.mk A (i.elim 1 MvPolynomial.X)) * Polynomial.X) ^ d i) =
          ∏ i ∈ d.support,
            Polynomial.C (Ideal.Quotient.mk A (i.elim 1 MvPolynomial.X)) ^ d i *
              Polynomial.X ^ d i := by
        exact Finset.prod_congr rfl fun i _ =>
          mul_pow (Polynomial.C (Ideal.Quotient.mk A (i.elim 1 MvPolynomial.X)))
            (Polynomial.X : Polynomial (MvPolynomial σ k ⧸ A)) (d i)
      rw [hprod, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      ac_rfl
    rw [hm, Polynomial.coeff_C_mul_X_pow,
      homogeneousComponent_of_mem (isHomogeneous_monomial r rfl)]
    split_ifs <;> simp_all
theorem decompose_apply (f : MvPolynomial σ k) (n : ℕ) :
    (DirectSum.decompose (homogeneousSubmodule σ k) f n : MvPolynomial σ k) =
      homogeneousComponent n f := by
  simpa only [DirectSum.Decomposition.decompose'_eq] using decomposition.decompose'_apply f n
theorem closureIdeal_homogeneous (A : Ideal (MvPolynomial σ k)) :
    (closureIdeal A).IsHomogeneous (homogeneousSubmodule (Option σ) k) := by
  intro n f hf
  rw [decompose_apply]
  change closureMap A f = 0 at hf
  change closureMap A (homogeneousComponent n f) = 0
  ext m
  rw [coeff_closureMap, homogeneousComponent_of_mem (homogeneousComponent_mem n f)]
  split_ifs with hmn
  · subst m
    rw [← coeff_closureMap, hf, Polynomial.coeff_zero]
  · simp
theorem atInfinity_rename (f : MvPolynomial σ k) :
    atInfinity (rename some f) = f := by
  have h : (atInfinity (k := k) (σ := σ)).comp (rename some) = AlgHom.id k _ := by
    ext i
    simp [atInfinity]
  exact DFunLike.congr_fun h f
theorem atInfinity_surjective :
    Function.Surjective (atInfinity (k := k) (σ := σ)) :=
  fun f => ⟨rename some f, atInfinity_rename f⟩
theorem atInfinity_eq_coeff_zero (f : MvPolynomial (Option σ) k) :
    atInfinity f = (optionEquivLeft k σ f).coeff 0 := by
  let e : Polynomial (MvPolynomial σ k) →ₐ[k] MvPolynomial σ k :=
    (Polynomial.aeval 0).restrictScalars k
  have h : (atInfinity (k := k) (σ := σ)) = e.comp (optionEquivLeft k σ).toAlgHom := by
    ext i
    cases i <;> simp [e, atInfinity, optionEquivLeft_X_none, optionEquivLeft_X_some]
  rw [h]
  change Polynomial.aeval (0 : MvPolynomial σ k) (optionEquivLeft k σ f) = _
  rw [Polynomial.coe_aeval_eq_eval, Polynomial.coeff_zero_eq_eval_zero]
theorem hilbertFunction_comap_atInfinity [Finite σ] (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    affineHilbertFunction (I.comap (atInfinity (k := k) (σ := σ))) n =
      affineHilbertFunction I n := by
  let q := Ideal.quotientMapₐ I (atInfinity (k := k) (σ := σ)) le_rfl
  let g : quotientDegreeLE (I.comap (atInfinity (k := k) (σ := σ))) n →ₗ[k]
      quotientDegreeLE I n :=
    (q.toLinearMap.domRestrict _).codRestrict _ fun x => by
      obtain ⟨f, hf, hfx⟩ := mem_quotientDegreeLE.mp x.property
      change q x.val ∈ _
      rw [← hfx]
      refine mk_mem_quotientDegreeLE (p := atInfinity f) ?_
      rw [atInfinity_eq_coeff_zero]
      exact (totalDegree_coeff_optionEquivLeft_le k σ f 0).trans hf
  have he : Function.Bijective g := by
    constructor
    · intro x y hxy
      exact Subtype.ext (Ideal.quotientMap_injective (congrArg Subtype.val hxy))
    · intro y
      obtain ⟨f, hf, hfy⟩ := mem_quotientDegreeLE.mp y.property
      refine ⟨⟨Ideal.Quotient.mk _ (rename some f),
        mk_mem_quotientDegreeLE ((totalDegree_rename_le some f).trans hf)⟩,
        Subtype.ext ?_⟩
      change Ideal.Quotient.mk I (atInfinity (rename some f)) = y.val
      rw [atInfinity_rename, hfy]
  exact (LinearEquiv.ofBijective g he).finrank_eq
theorem hilbertPolynomial_comap_atInfinity [Finite σ] (I : Ideal (MvPolynomial σ k)) :
    affineHilbertPolynomial (I.comap (atInfinity (k := k) (σ := σ))) =
      affineHilbertPolynomial I := by
  symm
  obtain ⟨N, hN⟩ := exists_eval_affineHilbertPolynomial I
  exact eq_affineHilbertPolynomial_of_eval_eq (N₀ := N)
    (fun n hn => by rw [hN n hn, hilbertFunction_comap_atInfinity])
theorem boundaryIdeal_homogeneous (A : Ideal (MvPolynomial σ k)) :
    (boundaryIdeal A).IsHomogeneous (homogeneousSubmodule σ k) := by
  apply Ideal.homogeneous_span
  rintro _ ⟨f, _, rfl⟩
  exact ⟨f.totalDegree, homogeneousComponent_mem _ _⟩
theorem minimalPrime_homogeneous {I P : Ideal (MvPolynomial σ k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (hP : I.IsMinimalPrime P) :
    P.IsHomogeneous (homogeneousSubmodule σ k) := by
  let Q := (P.homogeneousCore (homogeneousSubmodule σ k)).toIdeal
  have hQP : Q ≤ P := Ideal.toIdeal_homogeneousCore_le _ _
  have hIQ : I ≤ Q :=
    (Ideal.homogeneousCore.gc (𝒜 := homogeneousSubmodule σ k) ⟨I, hI⟩ P).mp hP.le
  have he : Q = P := le_antisymm hQP (hP.2 ⟨hP.isPrime.homogeneousCore, hIQ⟩ hQP)
  exact he ▸ (P.homogeneousCore (homogeneousSubmodule σ k)).isHomogeneous
end
end K1_13_6_3_5_1
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_3_3
noncomputable section
open K1_13_6_3_5 K1_13_6_3_5_3 MvPolynomial
variable {k L σ : Type} [Field k] [Field L] [Algebra k L] [Fintype σ]
def linearValue (a : σ → k) (r : σ → L) : L :=
  ∑ j, a j • r j
def lineProjection (i : σ) (a : σ → k) :
    MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial σ k :=
  MvPolynomial.aeval ![MvPolynomial.X i, ∑ j, MvPolynomial.C (a j) * MvPolynomial.X j]
def ChartIntegral (r : σ → L) (z : L) : Prop :=
  (∀ j, IsIntegral (Algebra.adjoin k {z}) (r j)) ∧
  (∀ j, IsIntegral (Algebra.adjoin k {z⁻¹}) (r j / z))
def onCoordinateRings (P : Ideal (MvPolynomial σ k))
    (φ : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial σ k) :
    (MvPolynomial (Fin 2) k ⧸ P.comap φ.toRingHom) →ₐ[k] (MvPolynomial σ k ⧸ P) :=
  Ideal.quotientMapₐ P φ le_rfl
theorem adjoin_line_le_ratioField (u : σ → L) (i : σ) (a : σ → k) :
    IntermediateField.adjoin k {linearValue a (ratios u i)} ≤ ratioField k u i := by
  apply IntermediateField.adjoin_le_iff.2
  intro z hz
  rw [Set.mem_singleton_iff.mp hz]
  exact (ratioField k u i).sum_mem fun j _ =>
    (ratioField k u i).smul_mem (IntermediateField.mem_adjoin_of_mem k (Set.mem_range_self j))
def projectiveDegree (u : σ → L) (i : σ) (a : σ → k) : ℕ :=
  letI := (IntermediateField.inclusion (adjoin_line_le_ratioField u i a)).toAlgebra
  Module.finrank (IntermediateField.adjoin k {linearValue a (ratios u i)})
    (ratioField k u i)
end
end K1_13_6_3_5_3_3
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_3_3
noncomputable section
open K1_13_6_3_5_3
open scoped WithZero
variable {k L σ : Type} [Field k] [Field L] [Algebra k L] [Fintype σ]
theorem finite_of_transcendental (h : CurveField k L) {z : L} (hz : Transcendental k z) :
    Module.Finite (IntermediateField.adjoin k {z}) L := by
  obtain ⟨t, ht, hfin⟩ := h
  let E := IntermediateField.adjoin k {t}
  let e : RatFunc k ≃ₐ[k] E := RatFunc.algEquivOfTranscendental t ht
  let g : RatFunc k →ₐ[k] L := E.val.comp e.toAlgHom
  let : Algebra (RatFunc k) L := g.toRingHom.toAlgebra
  have : IsScalarTower k (RatFunc k) L := IsScalarTower.of_algebraMap_eq
    fun x => (g.commutes x).symm
  have : Module.Finite E L := hfin
  have : FunctionField k L :=
    ((Module.finBasis E L).mapCoeffs e.symm fun c x => by
      rw [Algebra.smul_def, Algebra.smul_def]
      change (e (e.symm c) : L) * x = (c : L) * x
      rw [e.apply_symm_apply]).finiteDimensional_of_finite
  exact FunctionField.finiteDimensional_of_adjoin_transcendental hz
theorem finiteSupport_tuplePole (h : PrincipalDivisors k L) (r : σ → L) :
    (fun v : CurvePlace k L => tuplePole v.value r).HasFiniteSupport := by
  have hf : (⋃ j : σ, Function.support (fun v : CurvePlace k L =>
      poleOrder v.value (r j))).Finite := Set.finite_iUnion fun j => (h (r j)).1
  apply hf.subset
  intro v hv
  simp only [Set.mem_iUnion, Function.mem_support] at hv ⊢
  by_contra! hz
  exact hv (Finset.sup_eq_bot_iff _ _ |>.mpr fun j _ => hz j)
theorem poleOrder_eq_zero_iff (v : Valuation L ℤᵐ⁰) (x : L) :
    poleOrder v x = 0 ↔ v x ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx, poleOrder]
  have hv := (v.ne_zero_iff).2 hx
  rw [poleOrder, Int.toNat_eq_zero]
  simpa only [WithZero.exp_zero] using (WithZero.log_le_iff_le_exp (a := 0) hv)
theorem poleOrder_mono_value (v : Valuation L ℤᵐ⁰) {x y : L} (h : v x ≤ v y) :
    poleOrder v x ≤ poleOrder v y := by
  by_cases hx : x = 0
  · simp [poleOrder, hx]
  have hvx := (v.ne_zero_iff).2 hx
  have hvy : v y ≠ 0 := ne_of_gt ((zero_lt_iff.mpr hvx).trans_le h)
  exact Int.toNat_le_toNat ((WithZero.log_le_log hvx hvy).2 h)
theorem poleOrder_constant (v : CurvePlace k L) (c : k) :
    poleOrder v.value (algebraMap k L c) = 0 := by
  apply (poleOrder_eq_zero_iff _ _).2
  by_cases hc : c = 0
  · simp [hc]
  · exact (v.on_constants c hc).le
theorem exists_constant [IsAlgClosed k] {x : L} (hx : ¬ Transcendental k x) :
    ∃ c : k, algebraMap k L c = x := by
  have halg : IsAlgebraic k x := not_not.mp hx
  have := IntermediateField.isAlgebraic_adjoin_simple halg.isIntegral
  have he := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic
    (IntermediateField.adjoin k {x})
  exact IntermediateField.mem_bot.mp (he ▸ IntermediateField.mem_adjoin_simple_self k x)
theorem transcendental_of_pole_sum_pos [IsAlgClosed k] {z : L}
    (hp : 0 < ∑ᶠ v : CurvePlace k L, poleOrder v.value z) : Transcendental k z := by
  by_contra hc
  obtain ⟨c, rfl⟩ := exists_constant hc
  simp [poleOrder_constant] at hp
theorem height_pos_iff [IsAlgClosed k] (hf : CurveField k L) (h : PrincipalDivisors k L)
    (r : σ → L) : (∃ j, Transcendental k (r j)) ↔ 0 < tupleHeight k L r := by
  constructor
  · rintro ⟨j, hj⟩
    have := finite_of_transcendental hf hj
    have hle : (∑ᶠ v : CurvePlace k L, poleOrder v.value (r j)) ≤ tupleHeight k L r :=
      finsum_le_finsum (h (r j)).1 (finiteSupport_tuplePole h r) fun v =>
        Finset.le_sup (s := Finset.univ) (f := fun l => poleOrder v.value (r l))
          (Finset.mem_univ j)
    rw [(h (r j)).2.2.2 hj] at hle
    exact (Module.finrank_pos (R := IntermediateField.adjoin k {r j}) (M := L)).trans_le hle
  · intro hp
    by_contra! hn
    have hzero (v : CurvePlace k L) : tuplePole v.value r = 0 := by
      apply (Finset.sup_eq_bot_iff _ _).2
      intro j _
      obtain ⟨c, hc⟩ := exists_constant (hn j)
      rw [← hc]
      exact poleOrder_constant v c
    simp [tupleHeight, hzero] at hp
def maxValue (v : CurvePlace k L) (r : σ → L) : ℤᵐ⁰ :=
  max 1 (Finset.univ.sup fun j => v.value (r j))
theorem value_le_max (v : CurvePlace k L) (r : σ → L) (j : σ) :
    v.value (r j) ≤ maxValue v r :=
  (Finset.le_sup (s := Finset.univ) (f := fun j => v.value (r j))
    (Finset.mem_univ j)).trans (le_max_right _ _)
theorem value_smul_le (v : CurvePlace k L) (c : k) (x : L) :
    v.value (c • x) ≤ v.value x := by
  by_cases hc : c = 0
  · simp [hc]
  rw [Algebra.smul_def, map_mul, v.on_constants c hc, one_mul]
theorem linearValue_le_max (v : CurvePlace k L) (r : σ → L) (a : σ → k) :
    v.value (linearValue a r) ≤ maxValue v r := by
  apply v.value.map_sum_le
  intro j _
  exact (value_smul_le v (a j) (r j)).trans (value_le_max v r j)
private def cancellation (v : CurvePlace k L) (r : σ → L) : Submodule k (σ → k) where
  carrier := {a | v.value (linearValue a r) < maxValue v r}
  zero_mem' := by
    change v.value (linearValue (0 : σ → k) r) < maxValue v r
    rw [show linearValue (0 : σ → k) r = 0 by simp [linearValue], map_zero]
    exact zero_lt_one.trans_le (le_max_left _ _)
  add_mem' := by
    intro a b ha hb
    change v.value (linearValue (a + b) r) < maxValue v r
    have he : linearValue (a + b) r = linearValue a r + linearValue b r := by
      simp [linearValue, Pi.add_apply, add_smul, Finset.sum_add_distrib]
    rw [he]
    exact v.value.map_add_lt ha hb
  smul_mem' := by
    intro c a ha
    change v.value (linearValue (c • a) r) < maxValue v r
    have he : linearValue (c • a) r = c • linearValue a r := by
      simp [linearValue, Pi.smul_apply, smul_smul, Finset.smul_sum, smul_eq_mul]
    rw [he]
    exact (value_smul_le v c (linearValue a r)).trans_lt ha
theorem exists_linearValue_preserving [IsAlgClosed k] (h : PrincipalDivisors k L) (r : σ → L) :
    ∃ a : σ → k, (∀ v : CurvePlace k L,
      poleOrder v.value (linearValue a r) = tuplePole v.value r) ∧
      ∀ (v : CurvePlace k L) j, v.value (r j) ≤ max 1 (v.value (linearValue a r)) := by
  classical
  let s := (finiteSupport_tuplePole h r).toFinset
  have hs (v : CurvePlace k L) : v ∈ s ↔ tuplePole v.value r ≠ 0 := by
    exact (finiteSupport_tuplePole h r).mem_toFinset
  have hmax (v : CurvePlace k L) (hv : v ∈ s) :
      ∃ j, maxValue v r = v.value (r j) := by
    have hsup : 1 < Finset.univ.sup (fun j => v.value (r j)) := by
      by_contra! hl
      apply (hs v).mp hv
      apply (Finset.sup_eq_bot_iff _ _).2
      intro j _
      exact (poleOrder_eq_zero_iff _ _).2
        ((Finset.le_sup (s := Finset.univ) (f := fun j => v.value (r j))
          (Finset.mem_univ j)).trans hl)
    have hne : (Finset.univ : Finset σ).Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty.mp he, Finset.sup_empty] at hsup
      exact (not_lt_of_ge zero_le) hsup
    obtain ⟨j, _, hj⟩ := Finset.sup_mem_of_nonempty (f := fun j => v.value (r j)) hne
    exact ⟨j, (max_eq_right hsup.le).trans hj.symm⟩
  have hproper (v : s) : cancellation v.val r ≠ ⊤ := by
    obtain ⟨j, hj⟩ := hmax v.val v.prop
    intro ht
    have hm : (Pi.single j (1 : k)) ∈ cancellation v.val r := by rw [ht]; trivial
    change v.val.value (linearValue (Pi.single j (1 : k)) r) < maxValue v.val r at hm
    simp [hj, linearValue] at hm
  have hcover : (⋃ v : s, (cancellation v.val r : Set (σ → k))) ≠ Set.univ := by
    intro he
    obtain ⟨v, hv⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ he
    exact hproper v hv
  obtain ⟨a, ha⟩ := Set.nonempty_compl.2 hcover
  simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at ha
  refine ⟨a, ?_, ?_⟩
  · intro v
    by_cases hv : v ∈ s
    · have hnot := ha ⟨v, hv⟩
      change ¬ v.value (linearValue a r) < maxValue v r at hnot
      have he := (linearValue_le_max v r a).antisymm (le_of_not_gt hnot)
      refine le_antisymm ?_ ?_
      · obtain ⟨j, hj⟩ := hmax v hv
        exact (poleOrder_mono_value _ (he.trans hj).le).trans
          (Finset.le_sup (s := Finset.univ) (f := fun j => poleOrder v.value (r j))
            (Finset.mem_univ j))
      · apply Finset.sup_le
        intro j _
        exact poleOrder_mono_value _ ((value_le_max v r j).trans he.ge)
    · have hz : tuplePole v.value r = 0 := by simpa only [hs, not_ne_iff] using hv
      have hle (j : σ) : v.value (r j) ≤ 1 :=
        (poleOrder_eq_zero_iff _ _).1 ((Finset.sup_eq_bot_iff _ _).1 hz _ (Finset.mem_univ j))
      rw [hz]
      apply (poleOrder_eq_zero_iff _ _).2
      exact v.value.map_sum_le fun j _ => (value_smul_le v (a j) (r j)).trans (hle j)
  · intro v j
    by_cases hv : v ∈ s
    · have hnot := ha ⟨v, hv⟩
      change ¬ v.value (linearValue a r) < maxValue v r at hnot
      exact (value_le_max v r j).trans ((le_of_not_gt hnot).trans (le_max_right _ _))
    · have hz : tuplePole v.value r = 0 := by simpa only [hs, not_ne_iff] using hv
      exact ((poleOrder_eq_zero_iff _ _).1
        ((Finset.sup_eq_bot_iff _ _).1 hz _ (Finset.mem_univ j))).trans (le_max_left _ _)
end
end K1_13_6_3_5_3_3
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_3_3
noncomputable section
open K1_13_6_3_5 K1_13_6_3_5_3 MvPolynomial
open scoped Polynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k L σ : Type} [Field k] [Field L] [Algebra k L] [Fintype σ]
theorem lineProjection_linear (i : σ) (a : σ → k) :
    IsLinearProjection (lineProjection i a) := by
  intro j
  rw [lineProjection, aeval_X]
  fin_cases j
  · exact isHomogeneous_X k i
  · apply IsHomogeneous.sum
    intro l _
    exact (isHomogeneous_C _ _).mul (isHomogeneous_X _ l)
omit [Fintype σ] in
theorem coneEval_monomial (u : σ → L) (d : σ →₀ ℕ) (c : k) :
    coneEval k u (monomial d c) = Polynomial.monomial d.degree (aeval u (monomial d c)) := by
  rw [coneEval, coe_eval₂Hom, eval₂_monomial, aeval_monomial]
  simp only [RingHom.comp_apply, Finsupp.prod, Finsupp.degree_apply]
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow]
  rw [← map_prod, Finset.prod_pow_eq_pow_sum, ← mul_assoc, ← map_mul]
omit [Fintype σ] in
theorem coneIdeal_homogeneous (u : σ → L) :
    (coneIdeal k u).IsHomogeneous (homogeneousSubmodule σ k) := by
  classical
  rw [Ideal.isHomogeneous_iff_forall_subset]
  intro n p hp
  change p ∈ RingHom.ker (coneEval k u) at hp
  change GradedRing.proj (homogeneousSubmodule σ k) n p ∈ RingHom.ker (coneEval k u)
  rw [GradedRing.proj_apply]
  have hproj : (DirectSum.decompose (homogeneousSubmodule σ k) p n : MvPolynomial σ k) =
      homogeneousComponent n p := decomposition.decompose'_apply p n
  rw [hproj, RingHom.mem_ker]
  have hs (f : MvPolynomial σ k) {m : ℕ} (hf : f.IsHomogeneous m) :
      coneEval k u f = Polynomial.monomial m (aeval u f) := by
    conv_lhs => rw [f.as_sum, map_sum]
    conv_rhs => rw [f.as_sum, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hd' : d.degree = m := by
      by_contra hne
      exact (mem_support_iff.mp hd) (hf.coeff_eq_zero hne)
    rw [coneEval_monomial, hd']
  have hcoeff : (coneEval k u p).coeff n = aeval u (homogeneousComponent n p) := by
    nth_rewrite 1 [← p.sum_homogeneousComponent]
    rw [map_sum, Polynomial.finsetSum_coeff]
    simp_rw [hs _ (homogeneousComponent_isHomogeneous _ _), Polynomial.coeff_monomial]
    by_cases hn : n ∈ Finset.range (p.totalDegree + 1)
    · simp [hn]
    · have hdeg : p.totalDegree < n := by
        simpa only [Finset.mem_range, not_lt, Nat.succ_le_iff] using hn
      simp [hn, homogeneousComponent_eq_zero n p hdeg]
  rw [hs _ (homogeneousComponent_isHomogeneous _ _), ← hcoeff, RingHom.mem_ker.mp hp]
  simp
theorem cone_finrank_tower (E F : IntermediateField k L) (h : E ≤ F) :
    letI := (IntermediateField.inclusion h).toAlgebra
    Module.finrank E F * Module.finrank F L = Module.finrank E L := by
  let : Algebra E F := (IntermediateField.inclusion h).toAlgebra
  have : IsScalarTower E F L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.finrank_mul_finrank E F L
theorem residueDegree_mul_finrank (u : σ → L) (i : σ) (a : σ → k) :
    projectiveDegree u i a * Module.finrank (ratioField k u i) L =
      Module.finrank (IntermediateField.adjoin k {linearValue a (ratios u i)}) L :=
  cone_finrank_tower _ _ (adjoin_line_le_ratioField u i a)
end
end K1_13_6_3_5_3_3
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_1
noncomputable section
open MvPolynomial K1_13_6_3_6
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type} [Field k]
theorem component_mul {g : MvPolynomial σ k} {b : ℕ}
    (hg : g.IsHomogeneous b) (p : MvPolynomial σ k) (i : ℕ) :
    homogeneousComponent i (p * g) =
      if b ≤ i then homogeneousComponent (i - b) p * g else 0 := by
  simpa only [decompose_apply] using
    DirectSum.coe_decompose_mul_of_right_mem (homogeneousSubmodule σ k) i (a := p) hg
private def truncate (n : ℕ) (p : MvPolynomial σ k) : MvPolynomial σ k :=
  ∑ i ∈ Finset.range (n + 1), homogeneousComponent i p
theorem totalDegree_truncate (n : ℕ) (p : MvPolynomial σ k) :
    (truncate n p).totalDegree ≤ n := by
  rw [← mem_restrictTotalDegree]
  apply Submodule.sum_mem
  intro i hi
  rw [mem_restrictTotalDegree]
  exact (homogeneousComponent_isHomogeneous i p).totalDegree_le.trans
    (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
theorem component_truncate (n : ℕ) (p : MvPolynomial σ k) (i : ℕ) :
    homogeneousComponent i (truncate n p) = if i ≤ n then homogeneousComponent i p else 0 := by
  classical
  simp only [truncate, map_sum,
    fun j => homogeneousComponent_of_mem (m := i) (homogeneousComponent_mem j p)]
  simp [Finset.sum_ite_eq]
theorem truncate_mul_mod {I : Ideal (MvPolynomial σ k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k))
    {p f g : MvPolynomial σ k} {b n : ℕ}
    (hp : p.totalDegree ≤ n) (hg : g.IsHomogeneous b) (hbn : b ≤ n)
    (hm : p - f * g ∈ I) : p - truncate (n - b) f * g ∈ I := by
  rw [mem_iff_homogeneousComponent_mem hI]
  intro i
  rw [map_sub]
  by_cases hi : i ≤ n
  · have hh := homogeneousComponent_mem_of_mem hI hm i
    rw [map_sub, component_mul hg] at hh
    rw [component_mul hg]
    by_cases hbi : b ≤ i
    · have hle : i - b ≤ n - b := Nat.sub_le_sub_right hi b
      simpa only [ite_eq_left hbi, component_truncate, ite_eq_left hle] using hh
    · simpa only [ite_eq_right hbi] using hh
  · have ht : (truncate (n - b) f * g).totalDegree ≤ n :=
      (totalDegree_mul _ _).trans (by
        have ht₀ := totalDegree_truncate (n - b) f
        have hg₀ := hg.totalDegree_le
        omega)
    rw [homogeneousComponent_eq_zero i p (by omega),
      homogeneousComponent_eq_zero i (truncate (n - b) f * g) (by omega),
      sub_zero]
    exact I.zero_mem
theorem hilbertFunction_cyclic [Finite σ] {I : Ideal (MvPolynomial σ k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) {g : MvPolynomial σ k} {b n : ℕ}
    (hg : g.IsHomogeneous b) (hbn : b ≤ n) :
    affineHilbertFunction (I ⊔ Ideal.span {g}) n +
      affineHilbertFunction (I.colon {g}) (n - b) = affineHilbertFunction I n := by
  let J : Ideal (MvPolynomial σ k) := I ⊔ Ideal.span {g}
  let A : Ideal (MvPolynomial σ k) := I.colon {g}
  let q := Ideal.Quotient.factorₐ k (show I ≤ J from le_sup_left)
  let cut : quotientDegreeLE I n →ₗ[k] quotientDegreeLE J n :=
    (q.toLinearMap.domRestrict _).codRestrict _ fun y => by
      obtain ⟨p, hp, hpy⟩ := mem_quotientDegreeLE.mp y.property
      change q y.val ∈ _
      rw [← hpy]
      exact mk_mem_quotientDegreeLE hp
  have hcut : Function.Surjective cut := by
    intro y
    obtain ⟨p, hp, hpy⟩ := mem_quotientDegreeLE.mp y.property
    exact ⟨⟨Ideal.Quotient.mk I p, mk_mem_quotientDegreeLE hp⟩, Subtype.ext hpy⟩
  let mul := (quotientMul I g).restrictScalars k
  let emb : quotientDegreeLE A (n - b) →ₗ[k] quotientDegreeLE I n :=
    (mul.domRestrict _).codRestrict _ fun y => by
      obtain ⟨p, hp, hpy⟩ := mem_quotientDegreeLE.mp y.property
      change quotientMul I g y.val ∈ _
      rw [← hpy, quotientMul_mk]
      have hd := hg.totalDegree_le
      exact mk_mem_quotientDegreeLE ((totalDegree_mul p g).trans (by omega))
  have hemb (y : quotientDegreeLE A (n - b)) : emb y ∈ LinearMap.ker cut := by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    change q (quotientMul I g y.val) = 0
    have hex := (LinearMap.exact_iff.mp (quotientMul_exact I g))
    have hm : quotientMul I g y.val ∈
        LinearMap.range (quotientMul I g) := LinearMap.mem_range_self _ _
    rw [← hex] at hm
    exact hm
  let e := emb.codRestrict (LinearMap.ker cut) hemb
  have he : Function.Bijective e := by
    constructor
    · intro x y he
      exact Subtype.ext (quotientMul_injective I g
        (congrArg (fun z => z.val.val) he))
    · intro y
      obtain ⟨p, hp, hpy⟩ := mem_quotientDegreeLE.mp y.val.property
      have hy : q y.val.val = 0 := congrArg Subtype.val y.property
      rw [← hpy] at hy
      have hm : p ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hy
      obtain ⟨a, ha, x, hx, hax⟩ := Submodule.mem_sup.mp hm
      obtain ⟨f, rfl⟩ := Ideal.mem_span_singleton.mp hx
      have hd : p - f * g ∈ I := by
        rwa [← hax, mul_comm g f, add_sub_cancel_right]
      refine ⟨⟨Ideal.Quotient.mk A (truncate (n - b) f),
        mk_mem_quotientDegreeLE (totalDegree_truncate _ _)⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      change quotientMul I g (Ideal.Quotient.mk A (truncate (n - b) f)) = y.val.val
      rw [quotientMul_mk, ← hpy, Ideal.Quotient.eq]
      simpa only [neg_sub] using I.neg_mem (truncate_mul_mod hI hp hg hbn hd)
  have hrank := cut.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hcut, finrank_top,
    ← (LinearEquiv.ofBijective e he).finrank_eq] at hrank
  exact hrank
theorem hilbertPolynomial_cyclic [Finite σ] {I : Ideal (MvPolynomial σ k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) {g : MvPolynomial σ k} {b : ℕ}
    (hg : g.IsHomogeneous b) :
    affineHilbertPolynomial (I ⊔ Ideal.span {g}) +
      Polynomial.taylor (-(b : ℚ)) (affineHilbertPolynomial (I.colon {g})) =
      affineHilbertPolynomial I := by
  obtain ⟨N₀, h₀⟩ := exists_eval_affineHilbertPolynomial (I.colon {g})
  obtain ⟨N₁, h₁⟩ := exists_eval_affineHilbertPolynomial (I ⊔ Ideal.span {g})
  apply eq_affineHilbertPolynomial_of_eval_eq (N₀ := max (N₀ + b) N₁)
  intro N h
  have hN := (le_max_left (N₀ + b) N₁).trans h
  have hb : b ≤ N := by omega
  rw [Polynomial.eval_add, Polynomial.taylor_eval,
    h₁ N ((le_max_right (N₀ + b) N₁).trans h), ← sub_eq_add_neg, ← Nat.cast_sub hb,
    h₀ (N - b) (by omega)]
  exact_mod_cast hilbertFunction_cyclic hI hg hb
theorem coeff_cyclic [Finite σ] {I : Ideal (MvPolynomial σ k)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) {g : MvPolynomial σ k} {b : ℕ}
    (hg : g.IsHomogeneous b) {d : ℕ} (hd : (affineHilbertPolynomial I).natDegree ≤ d) :
    (affineHilbertPolynomial (I ⊔ Ideal.span {g})).coeff d +
      (affineHilbertPolynomial (I.colon {g})).coeff d =
        (affineHilbertPolynomial I).coeff d := by
  have hA := (natDegree_affineHilbertPolynomial_le_of_le
    (Ideal.le_colon : I ≤ I.colon {g})).trans hd
  simpa only [Polynomial.coeff_add, Polynomial.coeff_taylor_of_natDegree_le _ hA] using
    congrArg (fun p : Polynomial ℚ => p.coeff d) (hilbertPolynomial_cyclic hI hg)
end
end K1_13_6_3_5_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace K1_13_6_3_5_3_1
noncomputable section
open MvPolynomial K1_13_6_3 K1_13_6_3_5_3
open scoped Polynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type} [Field k]
abbrev ConeRing (I : Ideal (MvPolynomial σ k)) := MvPolynomial σ k ⧸ I
abbrev ConeFrac (I : Ideal (MvPolynomial σ k)) := FractionRing (ConeRing I)
def conePoint (I : Ideal (MvPolynomial σ k)) (i : σ) : ConeFrac I :=
  algebraMap (ConeRing I) (ConeFrac I) (Ideal.Quotient.mk I (MvPolynomial.X i))
def chartField (I : Ideal (MvPolynomial σ k)) [I.IsPrime] (a : σ) :
    IntermediateField k (ConeFrac I) :=
  ratioField k (conePoint I) a
def chartPoint (I : Ideal (MvPolynomial σ k)) [I.IsPrime] (a i : σ) : chartField I a :=
  ⟨ratios (conePoint I) a i, IntermediateField.subset_adjoin _ _ (Set.mem_range_self i)⟩
theorem conePoint_ne_zero {I : Ideal (MvPolynomial σ k)} [I.IsPrime] {a : σ}
    (ha : MvPolynomial.X a ∉ I) : conePoint I a ≠ 0 :=
  fun h => ha (Ideal.Quotient.eq_zero_iff_mem.mp
    ((IsFractionRing.injective (ConeRing I) (ConeFrac I)).eq_iff.mp
      (h.trans (map_zero (algebraMap (ConeRing I) (ConeFrac I))).symm)))
@[simp] theorem chartPoint_coe (I : Ideal (MvPolynomial σ k)) [I.IsPrime] (a i : σ) :
    (chartPoint I a i : ConeFrac I) = conePoint I i / conePoint I a := rfl
theorem chartPoint_anchor {I : Ideal (MvPolynomial σ k)} [I.IsPrime] {a : σ}
    (ha : MvPolynomial.X a ∉ I) : chartPoint I a a = 1 := by
  apply Subtype.ext
  simp [conePoint_ne_zero ha]
theorem chart_generates (I : Ideal (MvPolynomial σ k)) [I.IsPrime] (a : σ) :
    IntermediateField.adjoin k (Set.range (chartPoint I a)) = ⊤ := by
  apply (chartField I a).lift_injective
  rw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
  rw [← Set.range_comp]
  rfl
theorem eval₂_scaled {A : Type} [CommRing A] (f : k →+* A)
    (u : σ → A) (z : A) {p : MvPolynomial σ k} {d : ℕ} (hp : p.IsHomogeneous d) :
    p.eval₂ f (fun i => u i * z) = p.eval₂ f u * z ^ d := by
  classical
  simp only [eval₂_eq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, mul_assoc]
  congr 2
  have hd : m.degree = d := by
    by_contra h
    exact (mem_support_iff.mp hm) (hp.coeff_eq_zero h)
  exact congrArg (fun n => z ^ n) hd
theorem coneEval_homogeneous {L : Type} [Field L] [Algebra k L]
    (u : σ → L) {p : MvPolynomial σ k} {d : ℕ} (hp : p.IsHomogeneous d) :
    coneEval k u p = Polynomial.C (p.eval₂ (algebraMap k L) u) * Polynomial.X ^ d := by
  rw [coneEval, coe_eval₂Hom, eval₂_scaled _ _ _ hp]
  congr 1
  exact (hom_eval₂ p _ (Polynomial.C : L →+* L[X]) u).symm
theorem coneEval_coeff {L : Type} [Field L] [Algebra k L]
    (u : σ → L) (p : MvPolynomial σ k) (d : ℕ) :
    (coneEval k u p).coeff d =
      (homogeneousComponent d p).eval₂ (algebraMap k L) u := by
  classical
  conv_lhs => rw [← sum_homogeneousComponent (φ := p)]
  simp only [map_sum, Polynomial.finsetSum_coeff,
    coneEval_homogeneous u (homogeneousComponent_isHomogeneous _ _),
    Polynomial.coeff_C_mul_X_pow]
  by_cases hd : d < p.totalDegree + 1
  · rw [Finset.sum_eq_single d]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp [hd]
  · rw [homogeneousComponent_eq_zero d p (by omega), eval₂_zero]
    apply Finset.sum_eq_zero
    intro j hj
    have hne : j ≠ d := by
      rw [Finset.mem_range] at hj
      omega
    simp [Ne.symm hne]
theorem is_mem_iff_chart_eval {I : Ideal (MvPolynomial σ k)} [I.IsPrime] {a : σ}
    (ha : MvPolynomial.X a ∉ I) {p : MvPolynomial σ k} {d : ℕ} (hp : p.IsHomogeneous d) :
    p ∈ I ↔ p.eval₂ (algebraMap k (chartField I a)) (chartPoint I a) = 0 := by
  let j := (chartField I a).val
  let q : MvPolynomial σ k →+* ConeFrac I :=
    (algebraMap (ConeRing I) (ConeFrac I)).comp (Ideal.Quotient.mk I)
  have hq : q = MvPolynomial.eval₂Hom (algebraMap k (ConeFrac I)) (conePoint I) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      rw [eval₂Hom_C]
      rfl
    · intro i
      rw [eval₂Hom_X']
      rfl
  have he : q p =
      j (p.eval₂ (algebraMap k (chartField I a)) (chartPoint I a)) * conePoint I a ^ d := by
    have hx (i : σ) : j.toRingHom (chartPoint I a i) * conePoint I a = conePoint I i := by
      change (conePoint I i / conePoint I a) * conePoint I a = _
      exact div_mul_cancel₀ _ (conePoint_ne_zero ha)
    have hj : j.toRingHom.comp (algebraMap k (chartField I a)) = algebraMap k (ConeFrac I) :=
      IsScalarTower.algebraMap_eq k (chartField I a) (ConeFrac I) |>.symm
    rw [hq, coe_eval₂Hom]
    change _ = j.toRingHom _ * _
    rw [hom_eval₂, hj, ← eval₂_scaled _ _ _ hp, funext hx]
  have hk : p ∈ I ↔ q p = 0 := by
    change p ∈ I ↔ algebraMap (ConeRing I) (ConeFrac I) (Ideal.Quotient.mk I p) = 0
    rw [← map_zero (algebraMap (ConeRing I) (ConeFrac I)),
      (IsFractionRing.injective (ConeRing I) (ConeFrac I)).eq_iff,
      Ideal.Quotient.eq_zero_iff_mem]
  rw [hk, he, mul_eq_zero, or_iff_left (pow_ne_zero _ (conePoint_ne_zero ha)),
    map_eq_zero_iff j j.injective]
theorem coneIdeal_chart {I : Ideal (MvPolynomial σ k)} [I.IsPrime] {a : σ}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (ha : MvPolynomial.X a ∉ I) :
    coneIdeal k (chartPoint I a) = I := by
  classical
  ext p
  change coneEval k (chartPoint I a) p = 0 ↔ p ∈ I
  rw [Polynomial.ext_iff]
  simp only [Polynomial.coeff_zero, coneEval_coeff, ← is_mem_iff_chart_eval ha
    (homogeneousComponent_isHomogeneous _ _)]
  exact (mem_iff_homogeneousComponent_mem hI p).symm
theorem homogeneous_map {E : Type} [Field E] (f : k →+* E)
    {I : Ideal (MvPolynomial σ k)} (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) :
    (I.map (MvPolynomial.map f)).IsHomogeneous (homogeneousSubmodule σ E) := by
  obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists _ _).mp hI
  rw [hS, Ideal.map_span, Set.image_image]
  apply Ideal.homogeneous_span
  rintro _ ⟨v, _, rfl⟩
  obtain ⟨d, hd⟩ : SetLike.IsHomogeneousElem (homogeneousSubmodule σ k)
      (v : MvPolynomial σ k) := v.property
  exact ⟨d, IsHomogeneous.map hd f⟩
end
end K1_13_6_3_5_3_1
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_3_3
noncomputable section
open K1_13_6_3 K1_13_6_3_5 K1_13_6_3_5_3 MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
def c1 : Prop :=
  ∀ (k L : Type) [Field k] [IsAlgClosed k] [Field L] [Algebra k L],
    CurveField k L → ∀ V : ValuationSubring L, V ≠ ⊤ →
    (∀ c : k, algebraMap k L c ∈ V) →
    ∃ w : CurvePlace k L, w.value.valuationSubring = V
def c2 : Prop :=
  ∀ (k L σ : Type) [Field k] [Field L] [Algebra k L] [Fintype σ]
    (u : σ → L) (i : σ) (a : σ → k), u i ≠ 0 →
    let z := linearValue a (ratios u i)
    Transcendental k z → ChartIntegral (k := k) (ratios u i) z →
      (coneIdeal k u).comap (lineProjection i a).toRingHom = ⊥ ∧
        (onCoordinateRings (coneIdeal k u) (lineProjection i a)).Finite
def c3 : Prop :=
  ∀ (k σ : Type) [Field k] [Fintype σ]
    (P : Ideal (MvPolynomial σ k))
    (φ : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial σ k),
    P.IsPrime → P.IsHomogeneous (homogeneousSubmodule σ k) →
    IsLinearProjection φ → P.comap φ.toRingHom = ⊥ →
    (onCoordinateRings P φ).Finite →
    affineDegree P = (residueDegree φ.toRingHom P : ℚ)
def c4 : Prop :=
  ∀ (k L σ : Type) [Field k] [Field L] [Algebra k L] [Fintype σ]
    (u : σ → L) (i : σ) (a : σ → k), u i ≠ 0 →
    Transcendental k (linearValue a (ratios u i)) →
    Module.Finite (IntermediateField.adjoin k {linearValue a (ratios u i)}) L →
    (coneIdeal k u).comap (lineProjection i a).toRingHom = ⊥ →
    residueDegree (lineProjection i a).toRingHom (coneIdeal k u) = projectiveDegree u i a
theorem integral_of_places (h : c1) {k L : Type} [Field k] [IsAlgClosed k]
    [Field L] [Algebra k L] (hL : CurveField k L) {x t : L}
    (hx : ∀ w : CurvePlace k L, w.value t ≤ 1 → w.value x ≤ 1) :
    IsIntegral (Algebra.adjoin k {t}) x := by
  let A := Algebra.adjoin k {t}
  let B := (integralClosure A L).toSubring
  by_contra hni
  obtain ⟨V, hBV, hxV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    (R := B) (show x ∉ B from hni)
  have hne : V ≠ ⊤ := by
    intro ht
    apply hxV
    rw [ht]
    trivial
  have hmem (y : L) (hy : y ∈ A) : y ∈ V :=
    hBV (show y ∈ B from isIntegral_algebraMap (x := (⟨y, hy⟩ : A)))
  obtain ⟨w, hw⟩ := h k L hL V hne fun c => hmem _ (A.algebraMap_mem c)
  have htV := hmem t (Algebra.subset_adjoin (Set.mem_singleton t))
  apply hxV
  rw [← hw] at htV ⊢
  exact hx w htV
theorem integral_on_charts (h : c1) {k L σ : Type} [Field k] [IsAlgClosed k]
    [Field L] [Algebra k L] [Fintype σ] (hL : CurveField k L) {r : σ → L} {z : L}
    (hz : z ≠ 0)
    (hbound : ∀ (w : CurvePlace k L) j, w.value (r j) ≤ max 1 (w.value z)) :
    ChartIntegral (k := k) r z := by
  constructor
  · intro j
    exact integral_of_places h hL fun w hw =>
      (hbound w j).trans (max_eq_left hw).le
  · intro j
    apply integral_of_places h hL
    intro w hw
    have hval : 1 ≤ w.value z := (w.value.one_le_val_iff hz).2 hw
    rw [map_div₀, div_le_iff₀ ((w.value.pos_iff).2 hz), one_mul]
    exact (hbound w j).trans (max_eq_right hval).le
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) :
    K1_13_6_3_5_3.c3 := by
  intro k L σ _ _ _ _ _ hL hdiv u i hi
  refine ⟨height_pos_iff hL hdiv _, ?_⟩
  intro hp
  obtain ⟨a, ha, hbound⟩ := exists_linearValue_preserving hdiv (ratios u i)
  let z := linearValue a (ratios u i)
  have hheight : (∑ᶠ v : CurvePlace k L, poleOrder v.value z) =
      tupleHeight k L (ratios u i) := finsum_congr ha
  have hz : Transcendental k z := transcendental_of_pole_sum_pos (hheight.symm ▸ hp)
  have hcharts := integral_on_charts h1 hL hz.ne_zero hbound
  obtain ⟨hker, hfin⟩ := h2 k L σ u i a hi hz hcharts
  let P := coneIdeal k u
  let φ := lineProjection i a
  have hdeg := h3 k σ P φ (RingHom.ker_isPrime _) (coneIdeal_homogeneous u)
    (lineProjection_linear i a) hker hfin
  have hr := h4 k L σ u i a hi hz (finite_of_transcendental hL hz) hker
  constructor
  · have hinj : Function.Injective (onCoordinateRings P φ) := Ideal.quotientMap_injective
    have hh := natDegree_affineHilbertPolynomial_eq_of_finite_of_injective
      (onCoordinateRings P φ) hfin hinj
    rw [hker, natDegree_affineHilbertPolynomial_bot, Nat.card_fin] at hh
    exact hh
  · rw [hdeg, hr, ← Nat.cast_mul, mul_comm (Module.finrank _ L) (projectiveDegree u i a),
      residueDegree_mul_finrank, ← (hdiv z).2.2.2 hz, hheight]
end
end K1_13_6_3_5_3_3
end
section
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace K1_13_6_3_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 Polynomial
def componentRow (P : JetIdeal) : Row 4 →+* JetField P :=
  (onComponent P).comp (MvPolynomial.map genericCoeffs)
abbrev ContractedRing (P : JetIdeal) := ↥(componentRow P).range
abbrev ContractedField (P : JetIdeal) := FractionRing (ContractedRing P)
def rowAt (P : JetIdeal) : Row 4 →+* ContractedField P :=
  (algebraMap (ContractedRing P) (ContractedField P)).comp (componentRow P).rangeRestrict
def constantsAt (P : JetIdeal) : Geom →+* ContractedField P :=
  (rowAt P).comp (MvPolynomial.C.comp Polynomial.C)
instance contractedAlgebra (P : JetIdeal) : Algebra Geom (ContractedField P) :=
  (constantsAt P).toAlgebra
def toComponent (P : JetIdeal) [P.IsPrime] : ContractedField P →+* JetField P :=
  IsFractionRing.lift (g := (componentRow P).range.subtype) Subtype.val_injective
def abscissa {F : Type} [CommRing F] (e : Row 4 →+* F) : F :=
  e (MvPolynomial.C Polynomial.X)
def jetCoordinate {F : Type} [CommRing F] (e : Row 4 →+* F) (i : Fin 4) : F :=
  e (MvPolynomial.X i)
def fromTaylor {F : Type} [CommRing F] {M : ℕ} (x : F) (jets : Fin M → F) : F[X] :=
  ∑ i : Fin M, Polynomial.C (jets i) * (Polynomial.X (R := F) - Polynomial.C x) ^ i.val
def dividedIterate {F : Type} [Field F] [Algebra Geom F]
    (D : Derivation Geom F F) (y : F) (n : ℕ) : F :=
  ((D : F → F)^[n]) y / (n.factorial : F)
def differentialTaylor {F : Type} [Field F] [Algebra Geom F]
    (D : Derivation Geom F F) (x y : F) : F[X] :=
  fromTaylor x (fun i : Fin taylorLength => dividedIterate D y i.val)
def chartTaylor {F : Type} [Field F] (e : Row 4 →+* F) (g : Row 4) : F[X] :=
  fromTaylor (abscissa e)
    (fun i : Fin taylorLength => e (jetNumerator g i.val) / e (separant g) ^ (2 * i.val) / (i.val.factorial : F))
end
end K1_13_6_3_2
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_3_3_3
noncomputable section
open MvPolynomial K1_13_6_3_5 K1_13_6_3_5_3_3
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type} [Field k]
variable (P : Ideal (MvPolynomial σ k))
variable (φ : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial σ k)
abbrev planeIdeal : Ideal (MvPolynomial (Fin 2) k) := P.comap φ.toRingHom
private def truncate {τ : Type} (n : ℕ) (p : MvPolynomial τ k) : MvPolynomial τ k :=
  ∑ i ∈ Finset.range (n + 1), homogeneousComponent i p
theorem truncate_eq {τ : Type} {p : MvPolynomial τ k} {n : ℕ}
    (hp : p.totalDegree ≤ n) : truncate n p = p := by
  symm
  calc
    p = ∑ i ∈ Finset.range (p.totalDegree + 1), homogeneousComponent i p :=
      (sum_homogeneousComponent p).symm
    _ = truncate n p := ?_
  unfold truncate
  apply Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ hp))
  intro i _ hi
  exact homogeneousComponent_eq_zero i p (by simpa using hi)
theorem truncate_degree {τ : Type} (n : ℕ) (p : MvPolynomial τ k) :
    (truncate n p).totalDegree ≤ n := by
  rw [← mem_restrictTotalDegree]
  apply Submodule.sum_mem
  intro i hi
  rw [mem_restrictTotalDegree]
  exact (homogeneousComponent_isHomogeneous i p).totalDegree_le.trans
    (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
theorem truncate_component {τ : Type} (n i : ℕ) (p : MvPolynomial τ k) :
    homogeneousComponent i (truncate n p) = if i ≤ n then homogeneousComponent i p else 0 := by
  classical
  simp only [truncate, map_sum,
    fun j => homogeneousComponent_of_mem (m := i) (homogeneousComponent_mem j p)]
  simp [Finset.sum_ite_eq]
private theorem projection_homogeneous (hφ : IsLinearProjection φ)
    {p : MvPolynomial (Fin 2) k} {i : ℕ} (hp : p.IsHomogeneous i) :
    (φ p).IsHomogeneous i := by
  rw [DFunLike.congr_fun (aeval_unique φ) p, aeval_def, algebraMap_eq]
  simpa only [one_mul] using hp.eval₂ C (φ ∘ MvPolynomial.X) (isHomogeneous_C _) hφ
theorem projection_component (hφ : IsLinearProjection φ)
    (p : MvPolynomial (Fin 2) k) (i : ℕ) :
    homogeneousComponent i (φ p) = φ (homogeneousComponent i p) := by
  classical
  conv_lhs => rw [← truncate_eq (p := p) le_rfl]
  simp only [truncate, map_sum, fun j => homogeneousComponent_of_mem (m := i)
    (projection_homogeneous φ hφ (homogeneousComponent_isHomogeneous j p))]
  by_cases hi : i ≤ p.totalDegree
  · simp [Finset.sum_ite_eq, hi]
  · rw [homogeneousComponent_eq_zero i p (by omega), map_zero]
    simp [Finset.sum_ite_eq, hi]
theorem filtered_of_generators
    (hP : P.IsHomogeneous (homogeneousSubmodule σ k)) (hφ : IsLinearProjection φ)
    {ι : Type} [Fintype ι] (b : ι → MvPolynomial σ k) (d : ι → ℕ)
    (hb : ∀ j, (b j).IsHomogeneous (d j))
    (hgen : ∀ y : MvPolynomial σ k ⧸ P,
      ∃ a : ι → MvPolynomial (Fin 2) k,
        ∑ j, Ideal.Quotient.mk P (φ (a j) * b j) = y)
    (n : ℕ) {y : MvPolynomial σ k ⧸ P} (hy : y ∈ quotientDegreeLE P n) :
    ∃ a : ι → MvPolynomial (Fin 2) k, (∀ j, (a j).totalDegree ≤ n) ∧
      ∑ j, Ideal.Quotient.mk P (φ (a j) * b j) = y := by
  obtain ⟨p, hp, rfl⟩ := mem_quotientDegreeLE.mp hy
  obtain ⟨a, ha⟩ := hgen (Ideal.Quotient.mk P p)
  rw [← map_sum, Ideal.Quotient.eq] at ha
  let a' := fun j => if d j ≤ n then truncate (n - d j) (a j) else 0
  have ha' (j : ι) : (a' j).totalDegree ≤ n := by
    by_cases hd : d j ≤ n
    · simpa only [a', ite_eq_left hd] using (truncate_degree (n - d j) (a j)).trans (Nat.sub_le ..)
    · simp [a', hd]
  refine ⟨a', ha', ?_⟩
  rw [← map_sum, Ideal.Quotient.eq, mem_iff_homogeneousComponent_mem hP]
  intro i
  rw [map_sub, map_sum]
  by_cases hi : i ≤ n
  · have he (j : ι) : homogeneousComponent i (φ (a' j) * b j) =
        homogeneousComponent i (φ (a j) * b j) := by
      rw [K1_13_6_3_5_1.component_mul (hb j), K1_13_6_3_5_1.component_mul (hb j)]
      by_cases hd : d j ≤ i
      · simp only [ite_eq_left hd, a', ite_eq_left (hd.trans hi), projection_component φ hφ,
          truncate_component, ite_eq_left (Nat.sub_le_sub_right hi _)]
      · rw [ite_eq_right hd, ite_eq_right hd]
    simpa only [map_sub, map_sum, he] using homogeneousComponent_mem_of_mem hP ha i
  · have he (j : ι) :
        homogeneousComponent i (φ (a' j) * b j) = 0 := by
      rw [K1_13_6_3_5_1.component_mul (hb j)]
      by_cases hd : d j ≤ i
      · rw [ite_eq_left hd]
        by_cases hj : d j ≤ n
        · simp only [a', ite_eq_left hj, projection_component φ hφ, truncate_component,
            ite_eq_right (by omega : ¬ i - d j ≤ n - d j), map_zero, zero_mul]
        · simp [a', hj]
      · rw [ite_eq_right hd]
    simp [he, homogeneousComponent_eq_zero i p (by omega : p.totalDegree < i)]
theorem exists_filtered_generators
    (hP : P.IsHomogeneous (homogeneousSubmodule σ k)) (hφ : IsLinearProjection φ)
    (hf : (onCoordinateRings P φ).Finite) :
    ∃ (m : ℕ) (b : Fin m → MvPolynomial σ k),
      ∀ (n : ℕ) (y : MvPolynomial σ k ⧸ P), y ∈ quotientDegreeLE P n →
        ∃ a : Fin m → MvPolynomial (Fin 2) k, (∀ j, (a j).totalDegree ≤ n) ∧
          ∑ j, Ideal.Quotient.mk P (φ (a j) * b j) = y := by
  classical
  let g := onCoordinateRings P φ
  let := g.toRingHom.toAlgebra
  have hfin : Module.Finite (MvPolynomial (Fin 2) k ⧸ planeIdeal P φ)
      (MvPolynomial σ k ⧸ P) := hf
  obtain ⟨s, hs⟩ := hfin.fg_top
  choose f hf using fun i : s => Ideal.Quotient.mk_surjective (I := P) (i : MvPolynomial σ k ⧸ P)
  obtain ⟨D, hD⟩ := Finite.exists_le (fun j => (f j).totalDegree)
  let ι := s × Fin (D + 1)
  let b : ι → MvPolynomial σ k := fun j => homogeneousComponent j.2 (f j.1)
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨_, b ∘ e, filtered_of_generators P φ hP hφ _ (fun j => (e j).2)
    (fun j => homogeneousComponent_isHomogeneous _ _) ?_⟩
  intro y
  have hy : y ∈ Submodule.span (MvPolynomial (Fin 2) k ⧸ planeIdeal P φ)
      (Set.range (fun i : s => (i : MvPolynomial σ k ⧸ P))) := by
    rw [Subtype.range_coe_subtype, Finset.setOfPred_mem, hs]
    trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hy
  choose a ha using fun j => Ideal.Quotient.mk_surjective (I := planeIdeal P φ) (c j)
  refine ⟨fun j => a (e j).1, ?_⟩
  change (∑ j, Ideal.Quotient.mk P (φ (a (e j).1) * b (e j))) = y
  rw [Equiv.sum_comp e (fun j : ι => Ideal.Quotient.mk P (φ (a j.1) * b j))]
  rw [Fintype.sum_prod_type]
  convert hc using 1
  apply Finset.sum_congr rfl
  intro j _
  have hsum : ∑ l : Fin (D + 1), homogeneousComponent l (f j) = f j := by
    rw [Fin.sum_univ_eq_sum_range (fun l : ℕ => homogeneousComponent l (f j))]
    exact truncate_eq (hD j)
  simp only [b, ← map_sum, ← Finset.mul_sum, hsum, map_mul, hf]
  rw [Algebra.smul_def, ← ha j]
  rfl
end
end K1_13_6_3_5_3_3_3
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_3_3_4
noncomputable section
open K1_13_6_3_5 K1_13_6_3_5_3 K1_13_6_3_5_3_3
open scoped Polynomial RatFunc
attribute [local instance] Polynomial.algebra
private def scale {L : Type} [Field L] (b : L) (hb : b ≠ 0) :
    L[X] ≃ₐ[L] L[X] :=
  Polynomial.algEquivOfCompEqX (Polynomial.C b⁻¹ * Polynomial.X)
    (Polynomial.C b * Polynomial.X)
    (by simp [← Polynomial.C_mul, ← mul_assoc, hb])
    (by simp [← Polynomial.C_mul, ← mul_assoc, hb])
private theorem coneEval_div {k L σ : Type} [Field k] [Field L] [Algebra k L]
    (w : σ → L) (b : L) (hb : b ≠ 0) :
    coneEval k (fun i => w i / b) = (scale b hb).toRingHom.comp (coneEval k w) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [coneEval, scale, Polynomial.algebraMap_eq]
  · intro i
    simp only [RingHom.comp_apply, coneEval, MvPolynomial.eval₂Hom_X']
    change Polynomial.C (w i / b) * Polynomial.X =
      Polynomial.aeval (Polynomial.C b⁻¹ * Polynomial.X) (Polynomial.C (w i) * Polynomial.X)
    rw [map_mul, Polynomial.aeval_C, Polynomial.algebraMap_eq, Polynomial.aeval_X, ← mul_assoc,
      ← Polynomial.C_mul, div_eq_mul_inv]
private def coneRat {k L σ : Type} [Field k] [Field L] [Algebra k L] (w : σ → L) :
    MvPolynomial σ k →+* RatFunc L :=
  (algebraMap L[X] (RatFunc L)).comp (coneEval k w)
private theorem coneRat_C {k L σ : Type} [Field k] [Field L] [Algebra k L]
    (w : σ → L) (c : k) :
    coneRat w (MvPolynomial.C c) = RatFunc.C (algebraMap k L c) := by
  simp [coneRat, coneEval]
private theorem coneRat_X {k L σ : Type} [Field k] [Field L] [Algebra k L]
    (w : σ → L) (i : σ) :
    coneRat (k := k) w (MvPolynomial.X i) = RatFunc.C (w i) * RatFunc.X := by
  simp [coneRat, coneEval]
private theorem coneRat_ker_div {k L σ : Type} [Field k] [Field L] [Algebra k L]
    (w : σ → L) (b : L) (hb : b ≠ 0) :
    RingHom.ker (coneRat (k := k) (fun i => w i / b)) = coneIdeal k w := by
  rw [coneRat, RingHom.ker_comp_of_injective _ (RatFunc.algebraMap_injective L),
    coneEval_div w b hb]
  exact RingHom.ker_comp_of_injective (coneEval k w)
    (f := (scale b hb).toRingHom) (scale b hb).injective
private def fractionEval {A K : Type} [CommRing A] [Field K]
    (P : Ideal A) [P.IsPrime] (e : A →+* K) (h : RingHom.ker e = P) :
    FractionRing (A ⧸ P) →+* K :=
  IsFractionRing.lift (RingHom.lift_injective_of_ker_le_ideal P
    (fun _ ha => RingHom.mem_ker.mp (h.symm ▸ ha)) h.le)
private theorem fractionEval_mk {A K : Type} [CommRing A] [Field K]
    (P : Ideal A) [P.IsPrime] (e : A →+* K) (h : RingHom.ker e = P) (a : A) :
    fractionEval P e h
      (algebraMap (A ⧸ P) (FractionRing (A ⧸ P)) (Ideal.Quotient.mk P a)) = e a := by
  rw [fractionEval, IsFractionRing.lift_algebraMap, Ideal.Quotient.lift_mk]
private theorem fractionEval_range_le {A K : Type} [CommRing A] [Field K]
    (P : Ideal A) [P.IsPrime] (e : A →+* K) (h : RingHom.ker e = P)
    (S : Subfield K) (he : ∀ a, e a ∈ S) :
    (fractionEval P e h).fieldRange ≤ S := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨x, y, _, rfl⟩ := IsFractionRing.div_surjective (A ⧸ P) z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [map_div₀, fractionEval_mk, fractionEval_mk]
  exact S.div_mem (he a) (he b)
private theorem ratFunc_mem {F K : Type} [Field F] [Field K]
    (g : RatFunc F →+* K) (S : Subfield K)
    (hC : ∀ a, g (RatFunc.C a) ∈ S) (hX : g RatFunc.X ∈ S) (z : RatFunc F) : g z ∈ S := by
  have hp (p : F[X]) : g (algebraMap F[X] (RatFunc F) p) ∈ S := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        rw [map_add, map_add]
        exact S.add_mem hp hq
    | monomial n a =>
        rw [RatFunc.algebraMap_monomial, map_mul, map_pow]
        exact S.mul_mem (hC a) (S.pow_mem hX n)
  induction z using RatFunc.induction_on with
  | f p q hq =>
      rw [map_div₀]
      exact S.div_mem (hp p) (hp q)
private theorem ratFunc_map_poly {F L : Type} [Field F] [Field L] [Algebra F L]
    (p : F[X]) :
    algebraMap (RatFunc F) (RatFunc L) (algebraMap F[X] (RatFunc F) p) =
      algebraMap L[X] (RatFunc L) (p.map (algebraMap F L)) := by
  rw [← IsScalarTower.algebraMap_apply F[X] (RatFunc F) (RatFunc L),
    IsScalarTower.algebraMap_apply F[X] L[X] (RatFunc L)]
  rfl
private theorem ratFunc_map_C {F L : Type} [Field F] [Field L] [Algebra F L] (c : F) :
    algebraMap (RatFunc F) (RatFunc L) (RatFunc.C c) = RatFunc.C (algebraMap F L c) := by
  simpa only [RatFunc.algebraMap_C, Polynomial.map_C] using
    ratFunc_map_poly (L := L) (Polynomial.C c)
private theorem ratFunc_map_X {F L : Type} [Field F] [Field L] [Algebra F L] :
    algebraMap (RatFunc F) (RatFunc L) RatFunc.X = RatFunc.X := by
  simpa only [RatFunc.algebraMap_X, Polynomial.map_X] using
    ratFunc_map_poly (L := L) (Polynomial.X : F[X])
theorem ratFunc_map_comp {E F L : Type} [Field E] [Field F] [Field L]
    [Algebra E F] [Algebra F L] [Algebra E L] [IsScalarTower E F L] :
    (algebraMap (RatFunc F) (RatFunc L)).comp (algebraMap (RatFunc E) (RatFunc F)) =
      algebraMap (RatFunc E) (RatFunc L) := by
  apply IsFractionRing.ringHom_ext (A := E[X])
  intro p
  rw [RingHom.comp_apply, ratFunc_map_poly, ratFunc_map_poly, ratFunc_map_poly,
    Polynomial.map_map, ← IsScalarTower.algebraMap_eq E F L]
private theorem fractionEquiv {k L σ : Type} [Field k] [Field L] [Algebra k L]
    (w : σ → L) (i : σ) (hi : w i = 1) (F : IntermediateField k L)
    (hF : IntermediateField.adjoin k (Set.range w) = F)
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime] (hP : RingHom.ker (coneRat w) = P) :
    ∃ e : FractionRing (MvPolynomial σ k ⧸ P) ≃+* RatFunc F,
      (algebraMap (RatFunc F) (RatFunc L)).comp e.toRingHom = fractionEval P (coneRat w) hP := by
  let f := fractionEval P (coneRat w) hP
  let g := algebraMap (RatFunc F) (RatFunc L)
  have he (p : MvPolynomial σ k) : coneRat w p ∈ f.fieldRange :=
    ⟨_, fractionEval_mk P (coneRat w) hP p⟩
  have hcoord (j : σ) : RatFunc.C (w j) * RatFunc.X ∈ f.fieldRange := by
    simpa only [coneRat_X] using he (MvPolynomial.X j)
  have hX : RatFunc.X ∈ f.fieldRange := by
    simpa only [hi, map_one, one_mul] using hcoord i
  have hconstants (c : F) : RatFunc.C (c : L) ∈ f.fieldRange := by
    let S : IntermediateField k L :=
      (f.fieldRange.comap RatFunc.C).toIntermediateField (fun b => by
        change RatFunc.C (algebraMap k L b) ∈ f.fieldRange
        simpa only [coneRat_C] using he (MvPolynomial.C b))
    have hle : F ≤ S := by
      rw [← hF, IntermediateField.adjoin_le_iff]
      rintro _ ⟨j, rfl⟩
      change RatFunc.C (w j) ∈ f.fieldRange
      have h := f.fieldRange.div_mem (hcoord j) hX
      rwa [mul_div_cancel_right₀ _ RatFunc.X_ne_zero] at h
    exact hle c.property
  have hg : g.fieldRange = f.fieldRange := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      refine ratFunc_mem g f.fieldRange (fun c => ?_) ?_ z
      · rw [show g (RatFunc.C c) = RatFunc.C (c : L) from ratFunc_map_C c]
        exact hconstants c
      · exact ratFunc_map_X (F := F) (L := L) ▸ hX
    · apply fractionEval_range_le
      intro p
      induction p using MvPolynomial.induction_on with
      | C b =>
          rw [coneRat_C]
          exact ⟨RatFunc.C (algebraMap k F b), ratFunc_map_C _⟩
      | add p q hp hq =>
          rw [map_add]
          exact g.fieldRange.add_mem hp hq
      | mul_X p j hp =>
          rw [map_mul, coneRat_X]
          refine g.fieldRange.mul_mem hp (g.fieldRange.mul_mem ?_ ⟨RatFunc.X, ratFunc_map_X⟩)
          have hj : w j ∈ F := hF ▸ IntermediateField.mem_adjoin_of_mem k (Set.mem_range_self j)
          exact ⟨RatFunc.C ⟨w j, hj⟩, ratFunc_map_C _⟩
  refine ⟨f.rangeRestrictFieldEquiv.trans
    ((RingEquiv.subfieldCongr hg.symm).trans g.rangeRestrictFieldEquiv.symm), ?_⟩
  ext1 x
  change g (g.rangeRestrictFieldEquiv.symm _) = f x
  exact RingHom.rangeRestrictFieldEquiv_apply_symm_apply _ _
theorem finrank_cone {E F L KU KV : Type}
    [Field E] [Field F] [Field L] [Field KU] [Field KV]
    [Algebra E F] [Algebra F L] [Algebra E L] [IsScalarTower E F L]
    (f : KV →+* KU) (eV : KV ≃+* RatFunc E) (eU : KU ≃+* RatFunc F)
    (h : ((algebraMap (RatFunc F) (RatFunc L)).comp eU.toRingHom).comp f =
      (algebraMap (RatFunc E) (RatFunc L)).comp eV.toRingHom) :
    letI := f.toAlgebra
    Module.finrank KV KU = Module.finrank E F := by
  let _ : Algebra KV KU := f.toAlgebra
  have hcomm : (algebraMap (RatFunc E) (RatFunc F)).comp eV.toRingHom =
      eU.toRingHom.comp f := by
    ext1 x
    apply (algebraMap (RatFunc F) (RatFunc L)).injective
    change ((algebraMap (RatFunc F) (RatFunc L)).comp (algebraMap (RatFunc E) (RatFunc F)))
      (eV x) = (algebraMap (RatFunc F) (RatFunc L)) (eU (f x))
    rw [ratFunc_map_comp]
    exact (RingHom.congr_fun h x).symm
  calc
    _ = Module.finrank (RatFunc E) (RatFunc F) := Algebra.finrank_eq_of_equiv_equiv eV eU hcomm
    _ = Module.finrank E[X] F[X] := IsFractionRing.finrank_eq E[X] (RatFunc E) F[X] (RatFunc F)
    _ = Module.finrank E F := congrArg Cardinal.toNat (rank_polynomial_polynomial E F)
set_option maxHeartbeats 1000000 in
theorem proof : K1_13_6_3_5_3_3.c4 := by
  classical
  intro k L σ _ _ _ _ u i a hi _hz _hfinite _hcomap
  let U := ratios u i
  let z := linearValue a U
  let V : Fin 2 → L := ![1, z]
  let E := IntermediateField.adjoin k {z}
  let F := ratioField k u i
  let φ := (lineProjection i a).toRingHom
  let P := coneIdeal k u
  let Q := P.comap φ
  let _ : P.IsPrime := RingHom.ker_isPrime (coneEval k u)
  let _ : Q.IsPrime := Ideal.IsPrime.comap φ
  have hU : U i = 1 := div_self hi
  have hV : V 0 = 1 := rfl
  have hE : IntermediateField.adjoin k (Set.range V) = E := by
    apply le_antisymm
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨j, rfl⟩
      fin_cases j
      · exact E.one_mem
      · exact IntermediateField.mem_adjoin_of_mem k (Set.mem_singleton z)
    · apply IntermediateField.adjoin_le_iff.mpr
      intro b hb
      rw [Set.mem_singleton_iff.mp hb]
      exact IntermediateField.mem_adjoin_of_mem k ⟨1, rfl⟩
  have hnorm : (coneRat (k := k) U).comp φ = coneRat V := by
    apply MvPolynomial.ringHom_ext
    · intro b
      change coneRat U (lineProjection i a (MvPolynomial.C b)) = coneRat V (MvPolynomial.C b)
      simp [coneRat_C]
    · intro j
      change coneRat U (lineProjection i a (MvPolynomial.X j)) = coneRat V (MvPolynomial.X j)
      rw [lineProjection, MvPolynomial.aeval_X]
      fin_cases j
      · change coneRat U (MvPolynomial.X i) = coneRat V (MvPolynomial.X 0)
        rw [coneRat_X, coneRat_X, hU, hV]
      · change coneRat U (∑ l, MvPolynomial.C (a l) * MvPolynomial.X l) =
          coneRat V (MvPolynomial.X 1)
        rw [coneRat_X]
        change coneRat U (∑ l, MvPolynomial.C (a l) * MvPolynomial.X l) =
          RatFunc.C (∑ l, a l • U l) * RatFunc.X
        rw [map_sum, map_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l _
        rw [map_mul, coneRat_C, coneRat_X, Algebra.smul_def, map_mul, mul_assoc]
  have hP : RingHom.ker (coneRat (k := k) U) = P := coneRat_ker_div u (u i) hi
  have hQ : RingHom.ker (coneRat (k := k) V) = Q := by
    rw [← hnorm, ← RingHom.comap_ker, hP]
  let KU := FractionRing (MvPolynomial σ k ⧸ P)
  let KV := FractionRing (MvPolynomial (Fin 2) k ⧸ Q)
  let fU : KU →+* RatFunc L := fractionEval P (coneRat U) hP
  let fV : KV →+* RatFunc L := fractionEval Q (coneRat V) hQ
  let f : KV →+* KU :=
    IsFractionRing.map (Ideal.quotientMap_injective (I := P) (f := φ))
  let _ : Algebra KV KU := f.toAlgebra
  have hsquare : fU.comp f = fV := by
    apply IsFractionRing.ringHom_ext (A := MvPolynomial (Fin 2) k ⧸ Q)
    intro b
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hf : f (algebraMap (MvPolynomial (Fin 2) k ⧸ Q) KV (Ideal.Quotient.mk Q p)) =
        algebraMap (MvPolynomial σ k ⧸ P) KU (Ideal.Quotient.mk P (φ p)) := by
      change IsLocalization.map _ (Ideal.quotientMap P φ le_rfl) _ _ = _
      rw [IsLocalization.map_eq]
      rfl
    rw [RingHom.comp_apply, hf]
    exact (fractionEval_mk P (coneRat U) hP (φ p)).trans
      ((RingHom.congr_fun hnorm p).trans (fractionEval_mk Q (coneRat V) hQ p).symm)
  obtain ⟨eU, heU⟩ := fractionEquiv U i hU F rfl P hP
  obtain ⟨eV, heV⟩ := fractionEquiv V 0 hV E hE Q hQ
  let _ : Algebra E F := (IntermediateField.inclusion (adjoin_line_le_ratioField u i a)).toAlgebra
  let _ : IsScalarTower E F L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  unfold residueDegree
  rw [dite_eq_left (show P.IsPrime from inferInstance)]
  change Module.finrank KV KU = Module.finrank E F
  apply finrank_cone (L := L) f eV eU
  rw [heU, heV]
  exact hsquare
end
end K1_13_6_3_5_3_3_4
end
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 80000
namespace K1_13_6_3_5_3_1
noncomputable section
open MvPolynomial K1_13_6_3 K1_13_6_3_5_3
open scoped Polynomial nonZeroDivisors
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type} [Field k]
private theorem trdeg_fraction (A F : Type) [CommRing A] [IsDomain A] [Field F]
    [Algebra k A] [Algebra k F] [Algebra A F] [IsScalarTower k A F] [IsFractionRing A F] :
    Algebra.trdeg k F = Algebra.trdeg k A := by
  have : Algebra.IsAlgebraic A F := IsLocalization.isAlgebraic _ A⁰
  rw [← trdeg_add_eq k A (A := F), trdeg_eq_zero (R := A) (A := F), add_zero]
theorem trdeg_of_finite {A B : Type} [CommRing A] [IsDomain A] [CommRing B]
    [IsDomain B] [Algebra k A] [Algebra k B] (g : B →ₐ[k] A) (hg : Function.Injective g)
    (hfinite : g.Finite) : Algebra.trdeg k A = Algebra.trdeg k B := by
  let algebra := g.toRingHom.toAlgebra
  let := algebra
  let : IsScalarTower k B A := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  let : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hg
  let : Module.Finite B A := hfinite
  have : Algebra.IsAlgebraic B A := Algebra.IsIntegral.isAlgebraic
  simpa only [trdeg_eq_zero (R := B) (A := A), add_zero] using
    (trdeg_add_eq k B (A := A)).symm
theorem trdeg_cone [Finite σ] (I : Ideal (MvPolynomial σ k)) [I.IsPrime] :
    Algebra.trdeg k (ConeFrac I) = (dimension I : Cardinal) := by
  obtain ⟨d, g, hg, hfinite⟩ := exists_finite_inj_algHom_of_fg k (ConeRing I)
  have hdim := natDegree_affineHilbertPolynomial_eq_card_of_finite_of_injective g hfinite hg
  rw [Nat.card_fin] at hdim
  calc
    Algebra.trdeg k (ConeFrac I) = Algebra.trdeg k (ConeRing I) := trdeg_fraction _ _
    _ = Algebra.trdeg k (MvPolynomial (Fin d) k) := trdeg_of_finite g hg hfinite
    _ = (d : Cardinal) := by simp [MvPolynomial.trdeg_of_isDomain]
    _ = (dimension I : Cardinal) := congrArg (fun n : ℕ => (n : Cardinal)) hdim.symm
theorem trdeg_cone_chart (I : Ideal (MvPolynomial σ k)) [I.IsPrime] (a : σ)
    (heq : coneIdeal k (chartPoint I a) = I) (ha : MvPolynomial.X a ∉ I) :
    Algebra.trdeg k (ConeFrac I) = Algebra.trdeg k (chartField I a) + 1 := by
  let L := chartField I a
  let F := FractionRing L[X]
  let f : MvPolynomial σ k →ₐ[k] L[X] :=
    MvPolynomial.aeval (fun i => Polynomial.C (chartPoint I a i) * Polynomial.X)
  have hf : RingHom.ker f = I := heq
  let g : ConeRing I →ₐ[k] L[X] :=
    Ideal.Quotient.liftₐ I f (fun p hp => show p ∈ RingHom.ker f from hf.symm ▸ hp)
  have hg : Function.Injective g :=
    (Ideal.injective_lift_iff _).mpr hf
  let emb : L[X] →ₐ[k] F := (Algebra.ofId L[X] F).restrictScalars k
  let u := emb.comp g
  have hu : Function.Injective u := (IsFractionRing.injective L[X] F).comp hg
  let j : ConeFrac I →ₐ[k] F := IsFractionRing.liftAlgHom hu
  have hj (i : σ) : j (conePoint I i) =
      emb (Polynomial.C (chartPoint I a i) * Polynomial.X) := by
    change IsFractionRing.lift (g := u.toRingHom) hu
      (algebraMap (ConeRing I) (ConeFrac I) (Ideal.Quotient.mk I (MvPolynomial.X i))) = _
    rw [IsFractionRing.lift_algebraMap]
    change emb (f (MvPolynomial.X i)) = _
    rw [MvPolynomial.aeval_X]
  have hx : j (conePoint I a) = emb Polynomial.X := by
    rw [hj, chartPoint_anchor ha, map_one, one_mul]
  have hz : emb Polynomial.X ≠ 0 := by
    rw [← hx]
    exact (map_eq_zero j).not.mpr (conePoint_ne_zero ha)
  let const : L →ₐ[k] F := (Algebra.ofId L F).restrictScalars k
  have hC (c : L) : const c = emb (Polynomial.C c) :=
    IsScalarTower.algebraMap_apply L L[X] F c
  have hc (i : σ) :
      const (chartPoint I a i) = j (conePoint I i / conePoint I a) := by
    rw [map_div₀, hj, hx, map_mul, mul_div_cancel_right₀ _ hz]
    exact hC _
  have hconst : ∀ x : L, const x ∈ j.fieldRange := by
    have hle : IntermediateField.adjoin k (Set.range (chartPoint I a)) ≤
        j.fieldRange.comap const := by
      apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨i, rfl⟩
      exact ⟨_, (hc i).symm⟩
    rw [chart_generates] at hle
    exact fun x => hle (show x ∈ (⊤ : IntermediateField k L) from trivial)
  have hpoly (p : L[X]) : emb p ∈ j.fieldRange := by
    refine Polynomial.induction_on' (motive := fun p : L[X] => emb p ∈ j.fieldRange) p ?_ ?_
    · intro p q hp hq
      rw [map_add]
      exact j.fieldRange.add_mem hp hq
    · intro n c
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, ← hx, ← hC]
      have hmem : j (conePoint I a) ∈ j.fieldRange := ⟨conePoint I a, rfl⟩
      exact j.fieldRange.mul_mem (hconst c) (j.fieldRange.pow_mem hmem n)
  have hsurj : Function.Surjective j := by
    intro z
    obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective L[X] z
    exact j.fieldRange.div_mem (hpoly p) (hpoly q)
  have : FaithfulSMul k L :=
    (faithfulSMul_iff_algebraMap_injective k L).mpr (algebraMap k L).injective
  calc
    Algebra.trdeg k (ConeFrac I) = Algebra.trdeg k F :=
      (AlgEquiv.ofBijective j ⟨j.injective, hsurj⟩).trdeg_eq
    _ = Algebra.trdeg k L[X] := trdeg_fraction L[X] F
    _ = Algebra.trdeg k L + 1 := by
      simpa only [Polynomial.trdeg_of_isDomain] using (trdeg_add_eq k L (A := L[X])).symm
theorem chart_curve [Finite σ] (I : Ideal (MvPolynomial σ k)) [I.IsPrime] (a : σ)
    (hhom : I.IsHomogeneous (homogeneousSubmodule σ k)) (ha : MvPolynomial.X a ∉ I)
    (hdim : dimension I = 2) :
    CurveField k (chartField I a) ∧ ∃ i, Transcendental k (chartPoint I a i) := by
  let L := chartField I a
  have hh := trdeg_cone_chart I a (coneIdeal_chart hhom ha) ha
  rw [trdeg_cone I, hdim] at hh
  change (2 : Cardinal) = Algebra.trdeg k L + 1 at hh
  have htr : Algebra.trdeg k L = 1 := by
    have hone : (1 : Cardinal) + 1 = 2 := by norm_num
    rw [← hone] at hh
    exact Cardinal.eq_of_add_eq_add_right hh.symm (by simp)
  have hex : ∃ i, Transcendental k (chartPoint I a i) := by
    by_contra! hall
    have halg := (IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic
      (F := k) (S := Set.range (chartPoint I a))).mpr (by rintro _ ⟨i, rfl⟩; exact not_not.mp (hall i))
    rw [chart_generates] at halg
    have : Algebra.IsAlgebraic k L :=
      (IntermediateField.topEquiv (F := k) (E := L)).isAlgebraic
    rw [trdeg_eq_zero (R := k) (A := L)] at htr
    exact zero_ne_one htr
  refine ⟨?_, hex⟩
  obtain ⟨i, hi⟩ := hex
  refine ⟨chartPoint I a i, hi, ?_⟩
  let K := IntermediateField.adjoin k {chartPoint I a i}
  have hai : AlgebraicIndependent k (fun _ : Fin 1 => chartPoint I a i) :=
    (algebraicIndependent_singleton_iff (0 : Fin 1)).mpr hi
  have hb := hai.isTranscendenceBasis_of_trdeg_le_of_finite (by
    change Algebra.trdeg k L ≤ Cardinal.mk (Fin 1)
    simp [htr])
  have hrange : Set.range (fun _ : Fin 1 => chartPoint I a i) = {chartPoint I a i} := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨0, h.symm⟩⟩
  have halg : Algebra.IsAlgebraic K L := by
    change Algebra.IsAlgebraic (IntermediateField.adjoin k {chartPoint I a i}) L
    rw [← hrange]
    exact hb.isAlgebraic_field
  have htop : IntermediateField.adjoin K (Set.range (chartPoint I a)) = ⊤ := by
    apply IntermediateField.restrictScalars_injective k
    rw [IntermediateField.restrictScalars_adjoin_eq_sup, chart_generates, sup_top_eq,
      IntermediateField.restrictScalars_top]
  have hf := IntermediateField.finiteDimensional_adjoin (K := K)
    (S := Set.range (chartPoint I a)) (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  rw [htop] at hf
  let e := IntermediateField.topEquiv (F := K) (E := L)
  exact Module.Finite.of_surjective e.toLinearMap e.surjective
theorem exists_anchor {n : ℕ} (I : Ideal (MvPolynomial (Fin n) k)) [I.IsPrime]
    (hd : dimension I = 2) :
    ∃ a : Fin n, MvPolynomial.X a ∉ I ∧ ∀ i : Fin n, a < i → MvPolynomial.X i ∈ I := by
  classical
  let s := Finset.univ.filter fun i : Fin n => MvPolynomial.X i ∉ I
  have hs : s.Nonempty := by
    by_contra hn
    have hz (i : Fin n) : MvPolynomial.X i ∈ I := by
      by_contra hx
      exact hn ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
    have hsurj : Function.Surjective (algebraMap k (ConeRing I)) := by
      intro x
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      refine ⟨constantCoeff p, ?_⟩
      have he : Ideal.Quotient.mk I =
          eval₂Hom (algebraMap k (ConeRing I)) (fun _ => 0) := by
        apply MvPolynomial.ringHom_ext
        · intro c
          rw [eval₂Hom_C]
          rfl
        · intro i
          rw [eval₂Hom_X', Ideal.Quotient.eq_zero_iff_mem]
          exact hz i
      rw [eval₂Hom_zero'] at he
      exact (RingHom.congr_fun he p).symm
    let : Module.Finite k (ConeRing I) :=
      Module.Finite.of_surjective (Algebra.linearMap k (ConeRing I)) hsurj
    rw [dimension, affineHilbertPolynomial_eq_C_finrank, Polynomial.natDegree_C] at hd
    omega
  refine ⟨s.max' hs, (Finset.mem_filter.mp (Finset.max'_mem s hs)).2, ?_⟩
  intro i hi
  by_contra hz
  exact (not_le_of_gt hi) (Finset.le_max' s i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩))
end
end K1_13_6_3_5_3_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace K1_13_6_3_5_3_3_3
noncomputable section
open MvPolynomial K1_13_6_3_5 K1_13_6_3_5_3_3
attribute [local instance] MvPolynomial.gradedAlgebra
theorem proof : K1_13_6_3_5_3_3.c3 := by
  classical
  intro k σ _ _ P φ hprime hP hφ hker hfin
  let Q := planeIdeal P φ
  let A := MvPolynomial (Fin 2) k ⧸ Q
  let B := MvPolynomial σ k ⧸ P
  let F := FractionRing A
  let E := FractionRing B
  let g : A →ₐ[k] B := onCoordinateRings P φ
  have : P.IsPrime := hprime
  have : Q.IsPrime := Ideal.IsPrime.comap φ.toRingHom
  have hg : Function.Injective g := Ideal.quotientMap_injective
  let : Algebra A B := g.toRingHom.toAlgebra
  have : Module.Finite A B := hfin
  let f : F →+* E := IsFractionRing.map (show Function.Injective g.toRingHom from hg)
  let : Algebra F E := f.toAlgebra
  let i : A →ₐ[k] F := IsScalarTower.toAlgHom k A F
  let j : B →ₐ[k] E := IsScalarTower.toAlgHom k B E
  have hi : Function.Injective i := IsFractionRing.injective A F
  have hj : Function.Injective j := IsFractionRing.injective B E
  have hcomm (a : A) : j (g a) = algebraMap F E (i a) := by
    change algebraMap B E (g a) = f (algebraMap A F a)
    symm
    apply IsLocalization.map_eq
  have : IsScalarTower k F E := IsScalarTower.of_algebraMap_eq fun a => by
    calc
      algebraMap k E a = j (g (algebraMap k A a)) := ((j.comp g).commutes a).symm
      _ = algebraMap F E (algebraMap k F a) := by rw [hcomm, i.commutes]
  obtain ⟨m, v₀, hv₀⟩ := exists_filtered_generators P φ hP hφ hfin
  let v : Fin m → B := fun l => Ideal.Quotient.mk P (v₀ l)
  have hv (n : ℕ) (x : B) (hx : x ∈ quotientDegreeLE P n) :
      ∃ a : Fin m → A, (∀ l, a l ∈ quotientDegreeLE Q n) ∧ ∑ l, g (a l) * v l = x := by
    obtain ⟨a, ha, he⟩ := hv₀ n x hx
    refine ⟨(Ideal.Quotient.mk Q) ∘ a, fun l => mk_mem_quotientDegreeLE (ha l), ?_⟩
    change (∑ l, Ideal.Quotient.mk P (φ (a l)) * Ideal.Quotient.mk P (v₀ l)) = x
    simpa only [map_mul] using he
  let V := Submodule.span F (Set.range (j ∘ v))
  have hV (x : B) : j x ∈ V := by
    obtain ⟨n, hn⟩ := exists_mem_quotientDegreeLE P x
    obtain ⟨a, _, rfl⟩ := hv n x hn
    rw [map_sum]
    refine Submodule.sum_mem _ fun l _ => ?_
    rw [map_mul, hcomm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self l))
  have htop : V = ⊤ := by
    refine top_unique fun x _ => ?_
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective B x
    obtain ⟨c, a, ha, he⟩ := Algebra.IsAlgebraic.exists_smul_eq_mul A p
      (nonZeroDivisors.ne_zero hq)
    have hq' : j q ≠ 0 := (map_ne_zero_iff j hj).mpr (nonZeroDivisors.ne_zero hq)
    have ha' : i a ≠ 0 := (map_ne_zero_iff i hi).mpr ha
    change j p / j q ∈ V
    have hfrac : j p / j q = j c / algebraMap F E (i a) := by
      apply (div_eq_div_iff hq' ((map_ne_zero (algebraMap F E)).2 ha')).mpr
      have h := congrArg j he
      change j (g a * p) = j (q * c) at h
      simpa only [map_mul, hcomm, mul_comm] using h
    rw [hfrac, div_eq_inv_mul, ← map_inv₀, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (hV c)
  have : Module.Finite F V := Module.Finite.span_of_finite F (Set.finite_range _)
  have : FiniteDimensional F E := Module.Finite.of_surjective V.subtype
    (fun x => ⟨⟨x, htop.symm ▸ Submodule.mem_top⟩, rfl⟩)
  let e := Module.Basis.ofSpan htop.ge
  let := FiniteDimensional.fintypeBasisIndex e
  have he (r : _) : ∃ u : B, j u = e r := by
    obtain ⟨l, hl⟩ := Module.Basis.ofSpan_subset htop.ge (Set.mem_range_self r)
    exact ⟨v l, hl⟩
  choose u hu using he
  have hg₁ (l : Fin 2) : g (Ideal.Quotient.mk Q (MvPolynomial.X l)) ∈ quotientDegreeLE P 1 :=
    mk_mem_quotientDegreeLE (hφ l).totalDegree_le
  obtain ⟨C₁, h₁⟩ := lower_bound g i j hi hcomm hg₁ e u hu
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A)
    (fun z : Fin m × _ => e.equivFun (j (v z.1)) z.2)
  have hb (l : Fin m) (r : _) : ∃ b : A, i b = i d * e.equivFun (j (v l)) r := by
    obtain ⟨b, hb⟩ := hd (l, r)
    refine ⟨b, ?_⟩
    change algebraMap A F b = algebraMap A F (d : A) * e.equivFun (j (v l)) r
    simpa only [Algebra.smul_def] using hb
  choose b hb using hb
  have hd' : i d ≠ 0 := (map_ne_zero_iff i hi).mpr (nonZeroDivisors.ne_zero d.property)
  obtain ⟨C₂, h₂⟩ := upper_bound g i j hi hj hcomm e v hv hd' b hb
  have hr : Module.finrank F E = Fintype.card _ := Module.finrank_eq_card_basis e
  rw [← hr] at h₁ h₂
  have hdeg := natDegree_affineHilbertPolynomial_eq_of_finite_of_injective g hfin hg
  have h := degree_of_bounds (Module.finrank_pos (R := F) (M := E)).ne' hdeg h₁ h₂
  have hplane : affineDegree Q = 1 := by
    rw [show Q = ⊥ from hker, affineDegree_bot]
  rw [hplane, mul_one] at h
  rw [residueDegree, dite_eq_left hprime]
  exact h
end
end K1_13_6_3_5_3_3_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace K1_13_6_3_4
noncomputable section
open Filter MvPolynomial Polynomial
open scoped BigOperators
variable {k σ τ : Type*} [Field k] [Finite σ] [Finite τ]
variable {I : Ideal (MvPolynomial σ k)} {J : Ideal (MvPolynomial τ k)}
abbrev Piece (g : (MvPolynomial τ k ⧸ J) →ₐ[k] (MvPolynomial σ k ⧸ I)) (n : ℕ) :=
  (quotientDegreeLE J n).map g.toLinearMap
theorem degreeShift [IsDomain (MvPolynomial σ k ⧸ I)]
    (g : (MvPolynomial τ k ⧸ J) →ₐ[k] (MvPolynomial σ k ⧸ I))
    (i : τ) {ℓ : MvPolynomial σ k}
    (hℓ : g (Ideal.Quotient.mk J (MvPolynomial.X i)) = Ideal.Quotient.mk I ℓ)
    (hb : ∀ x, ∃ a b, g b ≠ 0 ∧ g b * x = g a)
    (hr : ValueReduction I ℓ) :
    ∃ C : ℕ, ∀ n : ℕ, affineHilbertFunction I n ≤ affineHilbertFunction J (n + C) := by
  classical
  obtain ⟨N, hred⟩ := hr
  let B := Module.finBasis k (quotientDegreeLE I N)
  choose a b hb₀ hab using fun j ↦ hb (B j : MvPolynomial σ k ⧸ I)
  let d := ∏ j, b j
  let other := fun j ↦ ∏ r ∈ Finset.univ.erase j, b r
  have hd (j : Fin (Module.finrank k (quotientDegreeLE I N))) : d = other j * b j := by
    exact (Finset.prod_erase_mul _ b (Finset.mem_univ j)).symm
  have hd₀ : g d ≠ 0 := by
    rw [show g d = ∏ j, g (b j) by simp [d, map_prod]]
    exact Finset.prod_ne_zero_iff.mpr fun j _ ↦ hb₀ j
  choose levels hlevels using fun j ↦ exists_mem_quotientDegreeLE J (other j * a j)
  obtain ⟨C, hC⟩ := Finite.exists_le levels
  have hbase (x : MvPolynomial σ k ⧸ I) (hx : x ∈ quotientDegreeLE I N) :
      g d * x ∈ Piece g C := by
    let z : quotientDegreeLE I N := ⟨x, hx⟩
    have hz : (∑ j, (B.repr z j) • (B j : MvPolynomial σ k ⧸ I)) = x := by
      simpa only [map_sum, map_smul, Submodule.subtype_apply] using
        congrArg (quotientDegreeLE I N).subtype (B.sum_repr z)
    rw [← hz, Finset.mul_sum]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    have hmul : g d * (B j : MvPolynomial σ k ⧸ I) = g (other j * a j) := by
      rw [hd j, map_mul, mul_assoc, hab j, ← map_mul]
    rw [show g d * ((B.repr z j) • (B j : MvPolynomial σ k ⧸ I)) =
      (B.repr z j) • (g d * (B j : MvPolynomial σ k ⧸ I)) from
        Algebra.mul_smul_comm (B.repr z j) (g d) (B j : MvPolynomial σ k ⧸ I), hmul]
    apply Submodule.smul_mem
    exact Submodule.mem_map.mpr ⟨_, quotientDegreeLE_mono J (hC j) (hlevels j), rfl⟩
  have hstep (n : ℕ) (hn : N ≤ n) (ih : ∀ x ∈ quotientDegreeLE I n, g d * x ∈ Piece g (n + C)) :
      ∀ x ∈ quotientDegreeLE I (n + 1), g d * x ∈ Piece g (n + 1 + C) := by
    intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := hred n hn x hx
    obtain ⟨s, hs, he⟩ := Submodule.mem_map.mp (ih v hv)
    change g s = g d * v at he
    rw [mul_add, mul_left_comm (g d), ← hℓ]
    apply Submodule.add_mem
    · exact Submodule.map_mono (quotientDegreeLE_mono J (by omega)) (ih u hu)
    · change g _ * (g d * v) ∈ _
      rw [← he, ← map_mul]
      exact Submodule.mem_map.mpr ⟨_, by
        simpa only [Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using
          mul_mem_quotientDegreeLE (mk_X_mem_quotientDegreeLE J i) hs, rfl⟩
  have hall (n : ℕ) : ∀ x ∈ quotientDegreeLE I n, g d * x ∈ Piece g (n + C) := by
    induction n with
    | zero =>
      intro x hx
      simpa using hbase x (quotientDegreeLE_mono I (Nat.zero_le N) hx)
    | succ n ih =>
      by_cases hn : N ≤ n
      · exact hstep n hn ih
      · intro x hx
        exact Submodule.map_mono (quotientDegreeLE_mono J (Nat.le_add_left C _))
          (hbase x (quotientDegreeLE_mono I (by omega) hx))
  refine ⟨C, fun n ↦ ?_⟩
  let mult := (LinearMap.mulLeft k (g d)).comp (quotientDegreeLE I n).subtype
  let m : quotientDegreeLE I n →ₗ[k] Piece g (n + C) :=
    mult.codRestrict (Piece g (n + C)) (fun x ↦ hall n x x.property)
  have hm : Function.Injective m := by
    intro x y hxy
    apply Subtype.ext
    apply mul_left_cancel₀ hd₀
    exact congrArg Subtype.val hxy
  have hfin : Module.Finite k (Piece g (n + C)) := by
    unfold Piece
    infer_instance
  exact (LinearMap.finrank_le_finrank_of_injective hm).trans
    (Submodule.finrank_map_le _ _)
theorem degree_eq_of_valueReduction [IsDomain (MvPolynomial σ k ⧸ I)]
    (g : (MvPolynomial τ k ⧸ J) →ₐ[k] (MvPolynomial σ k ⧸ I))
    (hg : Function.Injective g) (i : τ) {ℓ : MvPolynomial σ k}
    (hℓ : g (Ideal.Quotient.mk J (MvPolynomial.X i)) = Ideal.Quotient.mk I ℓ)
    (hlin : ∀ j, g (Ideal.Quotient.mk J (MvPolynomial.X j)) ∈ quotientDegreeLE I 1)
    (hb : ∀ x, ∃ a b, g b ≠ 0 ∧ g b * x = g a)
    (hr : ValueReduction I ℓ) : affineDegree I = affineDegree J := by
  obtain ⟨C, hupper⟩ := degreeShift g i hℓ hb hr
  have hlower (n : ℕ) : affineHilbertFunction J n ≤ affineHilbertFunction I n := by
    simpa only [one_mul] using affineHilbertFunction_le_of_injective g hg hlin n
  let P := affineHilbertPolynomial I
  let Q := affineHilbertPolynomial J
  have hshift : Tendsto (fun n : ℕ ↦ n + C) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ Nat.le_add_right n C) tendsto_id
  have hbound : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) ≤ (taylor (C : ℚ) Q).eval (n : ℚ) := by
    filter_upwards [eventually_eval_affineHilbertPolynomial I,
      hshift.eventually (eventually_eval_affineHilbertPolynomial J)] with n hn hnC
    rw [taylor_eval, ← Nat.cast_add, hn, hnC]
    exact_mod_cast hupper n
  have hbound' : ∀ᶠ n : ℕ in atTop, Q.eval (n : ℚ) ≤ P.eval (n : ℚ) := by
    filter_upwards [eventually_eval_affineHilbertPolynomial I,
      eventually_eval_affineHilbertPolynomial J] with n hn hn'
    rw [hn, hn']
    exact_mod_cast hlower n
  have hle := natDegree_le_of_eventually_eval_natCast_le
    (eventually_eval_affineHilbertPolynomial_nonneg I) hbound
  have hge := natDegree_le_of_eventually_eval_natCast_le
    (eventually_eval_affineHilbertPolynomial_nonneg J) hbound'
  have hdeg : P.natDegree = Q.natDegree :=
    (hle.1.trans_eq (natDegree_taylor Q _)).antisymm hge.1
  have hlc : P.leadingCoeff = Q.leadingCoeff := by
    apply le_antisymm _ (hge.2 hdeg.symm)
    simpa only [leadingCoeff_taylor] using hle.2 (hdeg.trans (natDegree_taylor Q _).symm)
  change (P.natDegree.factorial : ℚ) * P.leadingCoeff =
    (Q.natDegree.factorial : ℚ) * Q.leadingCoeff
  rw [hdeg, hlc]
end
end K1_13_6_3_4
end
section
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option synthInstance.maxHeartbeats 80000
namespace K1_13_6_3_5_3_1
noncomputable section
open MvPolynomial
open scoped Polynomial TensorProduct nonZeroDivisors
open Algebra.TensorProduct
variable {k E σ : Type} [Field k] [Field E] [Algebra k E]
abbrev scalarExtension (I : Ideal (MvPolynomial σ k)) :=
  I.map (MvPolynomial.map (algebraMap k E))
def coneRingInclude (I : Ideal (MvPolynomial σ k)) :
    ConeRing I →+* ConeRing (scalarExtension (E := E) I) :=
  Ideal.quotientMap _ (MvPolynomial.map (algebraMap k E)) Ideal.le_comap_map
private def quotientTensor (I : Ideal (MvPolynomial σ k)) :
    E ⊗[k] ConeRing I ≃ₐ[E] ConeRing (scalarExtension (E := E) I) := by
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := σ) k E
  let ι : MvPolynomial σ k →ₐ[k] E ⊗[k] MvPolynomial σ k := includeRight
  have hcomp : e.toRingHom.comp ι.toRingHom = MvPolynomial.map (algebraMap k E) := by
    apply RingHom.ext
    intro p
    change e (1 ⊗ₜ[k] p) = _
    simp [e]
  refine (Algebra.TensorProduct.tensorQuotientEquiv (R := k) E _ E I).trans
    (Ideal.quotientEquivAlg _ _ e ?_)
  exact ((Ideal.map_map (I := I) ι.toRingHom e.toRingHom).trans
    (congrArg (fun f => I.map f) hcomp)).symm
set_option backward.isDefEq.respectTransparency false in
private theorem quotientTensor_tmul (I : Ideal (MvPolynomial σ k))
    (z : E) (p : MvPolynomial σ k) :
    quotientTensor I (z ⊗ₜ[k] Ideal.Quotient.mk I p) =
      z • Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap k E) p) := by
  simp [quotientTensor]
  exact map_smul (Ideal.Quotient.mkₐ E (scalarExtension (E := E) I)).toLinearMap z _
theorem coneRing_eval_injective (I : Ideal (MvPolynomial σ k)) {z : E}
    (hz : Transcendental k z) :
    Function.Injective (Polynomial.eval₂RingHom (coneRingInclude (E := E) I)
      (algebraMap E (ConeRing (scalarExtension (E := E) I)) z)) := by
  let A := ConeRing I
  let j : k[X] →ₐ[k] E := Polynomial.aeval z
  let b : A[X] ≃ₐ[k] A ⊗[k] k[X] := polyEquivTensor k A
  let m : A ⊗[k] k[X] →ₐ[k] A ⊗[k] E := Algebra.TensorProduct.map (AlgHom.id k A) j
  let c : A ⊗[k] E ≃ₐ[k] E ⊗[k] A := Algebra.TensorProduct.comm k A E
  let e := quotientTensor (E := E) I
  let H : A[X] →+* ConeRing (scalarExtension (E := E) I) :=
    e.toRingHom.comp (c.toRingHom.comp (m.toRingHom.comp b.toRingHom))
  have hm : Function.Injective m :=
    TensorProduct.map_injective_of_flat_flat _ _ Function.injective_id
      (transcendental_iff_injective.mp hz)
  have hH : H = Polynomial.eval₂RingHom (coneRingInclude (E := E) I)
      (algebraMap E (ConeRing (scalarExtension (E := E) I)) z) := by
    apply Polynomial.ringHom_ext
    · intro a
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
      change e (c (m (b (Polynomial.C (Ideal.Quotient.mk I p))))) = _
      have hC : c (m (b (Polynomial.C (Ideal.Quotient.mk I p)))) =
          (1 : E) ⊗ₜ[k] Ideal.Quotient.mk I p := by simp [b, c, m, j]
      rw [hC, show e _ = _ from quotientTensor_tmul (E := E) I 1 p, one_smul,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      rfl
    · change e (c (m (b Polynomial.X))) = _
      have hX : c (m (b Polynomial.X)) = z ⊗ₜ[k] Ideal.Quotient.mk I 1 := by
        simp [b, c, m, j]
      rw [hX, show e _ = _ from quotientTensor_tmul I z 1]
      simp only [map_one]
      change z • (1 : ConeRing (scalarExtension (E := E) I)) =
        (Polynomial.X : A[X]).eval₂ (coneRingInclude (E := E) I)
          (algebraMap E (ConeRing (scalarExtension (E := E) I)) z)
      rw [Polynomial.eval₂_X]
      exact (Algebra.algebraMap_eq_smul_one (A := ConeRing (scalarExtension (E := E) I)) z).symm
  rw [← hH]
  exact e.injective.comp (c.injective.comp (hm.comp b.injective))
theorem coneRingInclude_injective (I : Ideal (MvPolynomial σ k)) {z : E}
    (hz : Transcendental k z) : Function.Injective (coneRingInclude (E := E) I) := by
  rw [← Polynomial.eval₂RingHom_comp_C (coneRingInclude (E := E) I)
    (algebraMap E (ConeRing (scalarExtension (E := E) I)) z)]
  exact (coneRing_eval_injective I hz).comp Polynomial.C_injective
theorem coneFrac_eval_injective (I : Ideal (MvPolynomial σ k)) [I.IsPrime]
    [(scalarExtension (E := E) I).IsPrime] {z : E} (hz : Transcendental k z) :
    Function.Injective (Polynomial.eval₂RingHom
      (IsFractionRing.map (coneRingInclude_injective I hz) :
        ConeFrac I →+* ConeFrac (scalarExtension (E := E) I))
      (algebraMap E (ConeFrac (scalarExtension (E := E) I)) z)) := by
  let A := ConeRing I
  let : IsDomain A := (Ideal.Quotient.isDomain_iff_prime I).2 inferInstance
  let B := ConeRing (scalarExtension (E := E) I)
  let C := ConeFrac (scalarExtension (E := E) I)
  let j : ConeFrac I →+* C := IsFractionRing.map (coneRingInclude_injective I hz)
  let x := algebraMap E C z
  let f : A →+* B := coneRingInclude (E := E) I
  have hcomp : j.comp (algebraMap A (ConeFrac I)) = (algebraMap B C).comp f :=
    IsLocalization.map_comp (M := A⁰) (T := B⁰) _
  have he (p : A[X]) :
      p.eval₂ (j.comp (algebraMap A (ConeFrac I))) x =
        algebraMap B C (p.eval₂ f (algebraMap E B z)) := by
    rw [Polynomial.hom_eval₂, ← hcomp, ← IsScalarTower.algebraMap_apply E B C]
  change Function.Injective (Polynomial.eval₂RingHom j x)
  intro p q hpq
  have hp : (p - q).eval₂ j x = 0 :=
    (Polynomial.eval₂_sub (p := p) (q := q) j (x := x)).trans (sub_eq_zero.mpr hpq)
  have heval := (he (IsLocalization.integerNormalization A⁰ (p - q))).symm.trans
    (IsLocalization.integerNormalization_eval₂_eq_zero A⁰ j (p - q) hp)
  have hzero : (IsLocalization.integerNormalization A⁰ (p - q)).eval₂ f (algebraMap E B z) = 0 :=
    (IsFractionRing.injective B C) (heval.trans (map_zero (algebraMap B C)).symm)
  have hnorm : IsLocalization.integerNormalization A⁰ (p - q) = 0 := by
    apply coneRing_eval_injective I hz
    change (IsLocalization.integerNormalization A⁰ (p - q)).eval₂ f (algebraMap E B z) =
      (0 : A[X]).eval₂ f (algebraMap E B z)
    exact hzero.trans (Polynomial.eval₂_zero _ _).symm
  exact sub_eq_zero.mp ((IsFractionRing.integerNormalization_eq_zero_iff (A := A)).mp hnorm)
end
end K1_13_6_3_5_3_1
end
section
set_option autoImplicit false
namespace K1_13_6_3_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_3
open scoped BigOperators Polynomial
private def universalPolynomial : CoeffRing[X] :=
  ∑ j : Fin taylorLength, Polynomial.monomial j.val (MvPolynomial.X j)
private def universalTrajectory (R : Row 4) : CoeffRing[X] :=
  MvPolynomial.eval₂ (Polynomial.mapRingHom MvPolynomial.C)
    (fun i => Polynomial.hasseDeriv i.val universalPolynomial) R
private def coeffEval {F : Type*} [Field F] (k : Geom →+* F) (U : F[X]) :
    CoeffRing →+* F :=
  MvPolynomial.eval₂Hom k (fun j => U.coeff j.val)
theorem map_universalPolynomial {F : Type*} [Field F]
    (k : Geom →+* F) {U : F[X]} (hd : U.natDegree < taylorLength) :
    universalPolynomial.map (coeffEval k U) = U := by
  change Polynomial.mapRingHom (coeffEval k U) universalPolynomial = U
  simp only [universalPolynomial, map_sum, Polynomial.coe_mapRingHom, Polynomial.map_monomial,
    coeffEval, MvPolynomial.eval₂Hom_X']
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => Polynomial.monomial n (U.coeff n))]
  exact (U.as_sum_range' _ hd).symm
theorem map_universalTrajectory {F : Type*} [Field F]
    (k : Geom →+* F) {U : F[X]} (hd : U.natDegree < taylorLength) (R : Row 4) :
    (universalTrajectory R).map (coeffEval k U) = trajectory k R U := by
  change Polynomial.mapRingHom (coeffEval k U) (universalTrajectory R) = _
  rw [universalTrajectory, MvPolynomial.hom_eval₂, trajectory]
  congr 1
  · rw [Polynomial.mapRingHom_comp]
    congr 1
    ext a
    simp [coeffEval]
  · funext i
    rw [Polynomial.coe_mapRingHom, ← Polynomial.hasseDeriv_map, map_universalPolynomial k hd]
private def evaluateFresh : CoeffRing[X] →+* FreshCoeffRing :=
  Polynomial.eval₂RingHom (MvPolynomial.map geomConstants) (MvPolynomial.C genericArgument)
private theorem evaluateFresh_hasse (i : ℕ) :
    evaluateFresh (Polynomial.hasseDeriv i universalPolynomial) =
      jetLinear genericArgument i := by
  classical
  simp only [universalPolynomial, map_sum, jetLinear]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.hasseDeriv_monomial]
  simp only [evaluateFresh, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
    map_mul, map_natCast, MvPolynomial.map_X]
  rw [map_pow]
  ac_rfl
theorem evaluateFresh_trajectory (R : Row 4) :
    evaluateFresh (universalTrajectory R) = freshJetMap (toGeneric R) := by
  change (evaluateFresh.comp
      (MvPolynomial.eval₂Hom (Polynomial.mapRingHom MvPolynomial.C)
        (fun i : Fin 4 => Polynomial.hasseDeriv i.val universalPolynomial))) R =
    (freshJetMap.comp (MvPolynomial.map genericCoeffs)) R
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C, freshJetMap]
    change Polynomial.eval₂ (MvPolynomial.map geomConstants) (MvPolynomial.C genericArgument)
        (a.map MvPolynomial.C) = MvPolynomial.C (genericCoeffs a)
    have hm : (MvPolynomial.map geomConstants).comp (MvPolynomial.C : Geom →+* CoeffRing) =
        (MvPolynomial.C : GeoField →+* FreshCoeffRing).comp geomConstants := by
      apply RingHom.ext
      simp
    rw [Polynomial.eval₂_map, hm, ← Polynomial.hom_eval₂]
    have hx : Polynomial.eval₂RingHom geomConstants genericArgument = genericCoeffs := by
      apply Polynomial.ringHom_ext
      · intro b
        exact Polynomial.eval₂_C _ _
      · exact Polynomial.eval₂_X _ _
    change MvPolynomial.C ((Polynomial.eval₂RingHom geomConstants genericArgument) a) = _
    rw [hx]
  · intro i
    simpa only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.map_X,
      freshJetMap] using evaluateFresh_hasse i.val
theorem fresh_mem_of_trajectory_zero {F : Type*} [Field F] (k : Geom →+* F)
    {U : F[X]} (hd : U.natDegree < taylorLength) (R : Row 4)
    (hR : trajectory k R U = 0) :
    toGeneric R ∈ freshImage (coefficientKernel k U) := by
  change freshJetMap (toGeneric R) ∈ extendIdeal (coefficientKernel k U)
  rw [← evaluateFresh_trajectory]
  let T := universalTrajectory R
  have hz : T.map (coeffEval k U) = 0 := (map_universalTrajectory k hd R).trans hR
  have hc (n : ℕ) : T.coeff n ∈ coefficientKernel k U := by
    change coeffEval k U (T.coeff n) = 0
    simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using
      congrArg (fun V : F[X] => V.coeff n) hz
  change evaluateFresh T ∈ _
  rw [congrArg evaluateFresh T.as_sum_range, map_sum]
  apply Ideal.sum_mem
  intro n _
  rw [evaluateFresh, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hc n))
def oldCoeffs (P : JetIdeal) : GeoField →+* JetField P :=
  (onComponent P).comp MvPolynomial.C
def oldEval (P : JetIdeal) (U : (JetField P)[X]) : FreshCoeffRing →+* JetField P :=
  MvPolynomial.eval₂Hom (oldCoeffs P) (fun j => U.coeff j.val)
theorem oldEval_jetLinear (P : JetIdeal) [P.IsPrime] {U : (JetField P)[X]}
    (hd : U.natDegree < taylorLength) (i : ℕ) :
    oldEval P U (jetLinear genericArgument i) =
      (Polynomial.hasseDeriv i U).eval (oldCoeffs P genericArgument) := by
  have hsum : U = ∑ j : Fin taylorLength, Polynomial.monomial j.val (U.coeff j.val) := by
    rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => Polynomial.monomial n (U.coeff n))]
    exact U.as_sum_range' _ hd
  rw [congrArg (fun V => (Polynomial.hasseDeriv i V).eval (oldCoeffs P genericArgument)) hsum]
  simp only [jetLinear, map_sum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Polynomial.hasseDeriv_monomial, Polynomial.eval_monomial, map_mul, oldEval,
    MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X', map_natCast, map_pow]
  ring
theorem fresh_le_source {f Q g : Row 4} {P : JetIdeal} [P.IsPrime]
    {U : (JetField P)[X]} (h : Integrated f Q g P U) :
    freshImage (coefficientKernel (componentConstants P) U) ≤ P := by
  have hmap : (oldEval P U).comp (MvPolynomial.map geomConstants) =
      coeffEval (componentConstants P) U := by
    ext a <;> simp [oldEval, oldCoeffs, coeffEval, componentConstants]
  have hkill : extendIdeal (coefficientKernel (componentConstants P) U) ≤
      RingHom.ker (oldEval P U) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    exact (DFunLike.congr_fun hmap a).trans ha
  have hcomp : (oldEval P U).comp freshJetMap = onComponent P := by
    ext a
    · simp [oldEval, freshJetMap, oldCoeffs]
    · rw [RingHom.comp_apply, freshJetMap, MvPolynomial.eval₂Hom_X',
        oldEval_jetLinear P h.degree]
      exact h.initial a
  intro a ha
  have hz : onComponent P a = 0 :=
    (DFunLike.congr_fun hcomp a).symm.trans (hkill ha)
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply IsFractionRing.injective (GeoJets ⧸ P) (JetField P)
  exact hz.trans (map_zero _).symm
theorem trajectory_to_fresh {f Q g : Row 4} {P : JetIdeal} [P.IsPrime]
    {U : (JetField P)[X]} (h : Integrated f Q g P U)
    (hsep : toGeneric (separant g) ∉ P) :
    let A := coefficientKernel (componentConstants P) U
    intersectionIdeal f Q ≤ freshImage A ∧ freshImage A ≤ P ∧
      toGeneric g ∈ freshImage A ∧ toGeneric (separant g) ∉ freshImage A := by
  dsimp only
  have hle := fresh_le_source h
  refine ⟨?_, hle, fresh_mem_of_trajectory_zero _ h.degree _ h.chart, fun hs => hsep (hle hs)⟩
  rw [intersectionIdeal, Ideal.span_le]
  rintro _ (hs | hs)
  · exact hs ▸ fresh_mem_of_trajectory_zero _ h.degree _ h.factor
  · rcases hs with rfl
    exact fresh_mem_of_trajectory_zero _ h.degree _ h.cutter
end
end K1_13_6_3_3
end
section
set_option autoImplicit false
namespace K1_13_6_3_1
noncomputable section
open K1_13 K1_13_6
abbrev SepField := separableClosure GenericField GeoField
abbrev SepJets := MvPolynomial (Fin 4) SepField
def sepToGeo : SepJets →+* GeoJets :=
  MvPolynomial.map (algebraMap SepField GeoField)
def rowToSep : Row 4 →+* SepJets :=
  MvPolynomial.map ((algebraMap GenericField SepField).comp (algebraMap (Polynomial Geom) GenericField))
@[simp] theorem sepToGeo_rowToSep (U : Row 4) : sepToGeo (rowToSep U) = toGeneric U := by
  rw [sepToGeo, rowToSep, MvPolynomial.map_map, toGeneric, genericCoeffs,
    ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq GenericField SepField GeoField]
end
end K1_13_6_3_1
end
section
set_option autoImplicit false
namespace K1_13_6_3_1
noncomputable section
open K1_13_6 K1_13_6_3
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem flat_sepToGeo : Module.Flat SepJets GeoJets := by
  have h : Algebra.IsPushout SepField SepJets GeoField GeoJets := inferInstance
  exact Module.Flat.isBaseChange SepField SepJets GeoField GeoJets h.out
private theorem map_eq_maximal_of_length_one (J P : JetIdeal) [P.IsPrime]
    (h : cycleLength J P ‹P.IsPrime› = 1) :
    J.map (algebraMap GeoJets (Localization.AtPrime P)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
  unfold cycleLength at h
  rw [Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
    IsLocalRing.isMaximal_iff] at h
  exact h
theorem simple_saturation (g : K1_13.Row 4) (surface P : JetIdeal)
    (hdesc : (surface.comap sepToGeo).map sepToGeo = surface)
    (hsimple : SimpleCut g surface P) :
    ∀ x ∈ P.comap sepToGeo, ∃ t ∉ P.comap sepToGeo,
      t * x ∈ surface.comap sepToGeo ⊔ Ideal.span {rowToSep (membershipTest g)} := by
  have : P.IsPrime := hsimple.minimal.isPrime
  let q := P.comap sepToGeo
  have : q.IsPrime := Ideal.comap_isPrime _ _
  have : P.LiesOver q := ⟨rfl⟩
  let A := Localization.AtPrime q
  let B := Localization.AtPrime P
  let _ : Algebra A B := Localization.AtPrime.algebraOfLiesOver q P
  have : Module.Flat SepJets GeoJets := flat_sepToGeo
  have : IsLocalHom (algebraMap A B) := by
    change IsLocalHom (Localization.localRingHom q P sepToGeo rfl)
    infer_instance
  have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let J : Ideal SepJets := surface.comap sepToGeo ⊔ Ideal.span {rowToSep (membershipTest g)}
  have hJ : J.map (algebraMap SepJets GeoJets) = divisorIdeal surface (membershipTest g) := by
    change (surface.comap sepToGeo ⊔ Ideal.span {rowToSep (membershipTest g)}).map sepToGeo = _
    rw [Ideal.map_sup, hdesc, Ideal.map_span, Set.image_singleton, sepToGeo_rowToSep,
      divisorIdeal]
  have hJB : (J.map (algebraMap SepJets A)).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq SepJets A B,
      IsScalarTower.algebraMap_eq SepJets GeoJets B, ← Ideal.map_map, hJ]
    exact map_eq_maximal_of_length_one _ P hsimple.one
  intro x hx
  have hxB : algebraMap A B (algebraMap SepJets A x) ∈ IsLocalRing.maximalIdeal B := by
    rw [← IsScalarTower.algebraMap_apply SepJets A B,
      IsScalarTower.algebraMap_apply SepJets GeoJets B, ← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hx
  rw [← hJB] at hxB
  have hxA : algebraMap SepJets A x ∈ J.map (algebraMap SepJets A) := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (J.map (algebraMap SepJets A))]
    exact hxB
  exact (IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl A J x).mp hxA
end
end K1_13_6_3_1
end
section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 2000
set_option linter.style.haveILetI false
namespace K1_13_6_3_4
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 MvPolynomial
open scoped BigOperators
private theorem eval₂_scale {k K σ : Type*} [Field k] [Field K] [Fintype σ]
    (f : k →+* K) (x : σ → K) (t : K) {p : MvPolynomial σ k} {n : ℕ}
    (hp : p.IsHomogeneous n) : eval₂ f (fun i ↦ t * x i) p = t ^ n * eval₂ f x p := by
  classical
  rw [eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hdeg : d.degree = n := by
    by_contra h
    exact (mem_support_iff.mp hd) (hp.coeff_eq_zero h)
  rw [show (∏ i : σ, (t * x i) ^ d i) = t ^ n * ∏ i : σ, x i ^ d i by
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      ← Finsupp.degree_eq_sum, hdeg]]
  ring
theorem eval_scale_zero {k σ : Type*} [Field k] [Fintype σ]
    (x : σ → k) (t : k) {p : MvPolynomial σ k} {n : ℕ}
    (hp : p.IsHomogeneous n) (hx : eval x p = 0) : eval (fun i ↦ t * x i) p = 0 :=
  (eval₂_scale (RingHom.id k) x t hp).trans (mul_eq_zero_of_right _ hx)
private theorem map_boundary_generator {k K σ : Type*} [Field k] [Field K]
    (f : k →+* K) (A : Ideal (MvPolynomial σ k)) {p : MvPolynomial σ k}
    {n : ℕ} (hp : p ∈ A) (hn : p.totalDegree ≤ n) :
    MvPolynomial.map f (homogeneousComponent n p) ∈ boundaryIdeal (A.map (MvPolynomial.map f)) := by
  have he : MvPolynomial.map f (homogeneousComponent n p) =
      homogeneousComponent n (MvPolynomial.map f p) := by
    ext d
    by_cases hd : d.degree = n <;> simp only [coeff_homogeneousComponent, coeff_map, hd, ite_true, ite_false, map_zero]
  have hd : (MvPolynomial.map f p).totalDegree ≤ p.totalDegree :=
    Finset.sup_mono (support_map_subset f p)
  exact Ideal.subset_span ⟨MvPolynomial.map f p, n, Ideal.mem_map_of_mem _ hp, hd.trans hn, he⟩
private theorem linear_sum_homogeneous {k σ : Type*} [Field k] [Fintype σ] (c : σ → k) :
    (∑ j : σ, MvPolynomial.C (c j) * MvPolynomial.X j).IsHomogeneous 1 :=
  (homogeneousSubmodule σ k 1).sum_mem fun j _ ↦ isHomogeneous_C_mul_X (c j) j
theorem jetLinear_homogeneous (a : GeoField) (r : ℕ) : (jetLinear a r).IsHomogeneous 1 :=
  linear_sum_homogeneous fun j : Fin taylorLength ↦ (j.val.choose r : GeoField) * a ^ (j.val - r)
private theorem normalize_boundary (A : CoeffIdeal) {x : Fin taylorLength → GeoField}
    (hx : x ∈ zeroLocus GeoField (boundaryIdeal (extendIdeal A)))
    {i : Fin taylorLength} (hi : x i ≠ 0) :
    letI : Algebra Geom GeoField := geomConstants.toAlgebra
    (fun j ↦ (x i)⁻¹ * x j) ∈ zeroLocus GeoField (boundaryChart A i) := by
  letI : Algebra Geom GeoField := geomConstants.toAlgebra
  let b : Fin taylorLength → GeoField := fun j ↦ (x i)⁻¹ * x j
  change boundaryChart A i ≤ RingHom.ker (eval₂Hom geomConstants b)
  apply sup_le
  · apply Ideal.span_le.mpr
    rintro _ ⟨p, n, hp, hn, rfl⟩
    have he := hx (MvPolynomial.map geomConstants (homogeneousComponent n p))
      (map_boundary_generator geomConstants A hp hn)
    change (MvPolynomial.map geomConstants (homogeneousComponent n p)).eval x = 0 at he
    rw [eval_map] at he
    change eval₂ geomConstants b (homogeneousComponent n p) = 0
    rw [eval₂_scale geomConstants x ((x i)⁻¹) (homogeneousComponent_isHomogeneous ..), he,
      mul_zero]
  · apply Ideal.span_le.mpr
    rintro _ (rfl : _ = MvPolynomial.X i - 1)
    change eval₂ geomConstants b (MvPolynomial.X i - 1) = 0
    rw [eval₂_sub, eval₂_X, eval₂_one]
    exact sub_eq_zero.mpr (inv_mul_cancel₀ hi)
private theorem finite_chart_coordinates {k K σ : Type*} [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [Finite σ] (J : Ideal (MvPolynomial σ k)) (hJ : dimension J = 0)
    {x : σ → K} (hx : x ∈ zeroLocus K J) (j : σ) : ∃ c : k, algebraMap k K c = x j := by
  letI : Module.Finite k (MvPolynomial σ k ⧸ J) :=
    moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero hJ
  let e : (MvPolynomial σ k ⧸ J) →ₐ[k] K := Ideal.Quotient.liftₐ J (aeval x) hx
  have h : IsIntegral k (x j) := by
    have hJX := (Algebra.IsIntegral.isIntegral (R := k) (Ideal.Quotient.mk J (MvPolynomial.X j))).map e
    change IsIntegral k (aeval x (MvPolynomial.X j)) at hJX
    simpa only [aeval_X] using hJX
  apply h.mem_range_algHom_of_minpoly_splits (K := k) _ (Algebra.ofId k K)
  simpa only [Algebra.algebraMap_self, Polynomial.map_id] using
    IsAlgClosed.splits (minpoly k (x j))
theorem polynomial_value_ne_zero {k K σ : Type*} [Field k] [Field K] [Fintype σ]
    (f : Polynomial k →+* K) (hf : Function.Injective f) (d : σ → ℕ) (hd : Function.Injective d)
    (a : σ → k) {i : σ} (hi : a i ≠ 0) :
    (∑ j : σ, f Polynomial.X ^ d j * f (Polynomial.C (a j))) ≠ 0 := by
  classical
  let P : Polynomial k := ∑ j : σ, Polynomial.monomial (d j) (a j)
  have hcoeff : P.coeff (d i) = a i := by
    rw [show P.coeff (d i) = ∑ j : σ, (Polynomial.monomial (d j) (a j)).coeff (d i) by
      exact map_sum (Polynomial.lcoeff k (d i)) _ _]
    rw [Finset.sum_eq_single i]
    · exact Polynomial.coeff_monomial_same _ _
    · intro j _ hj
      exact Polynomial.coeff_monomial_of_ne _ (fun h ↦ hj (hd h.symm))
    · exact fun h ↦ (h (Finset.mem_univ i)).elim
  have hp : P ≠ 0 := by
    intro he
    exact hi (by rw [← hcoeff, he, Polynomial.coeff_zero])
  have he : f P = ∑ j : σ, f Polynomial.X ^ d j * f (Polynomial.C (a j)) := by
    simp only [P, map_sum, ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, mul_comm]
  rw [← he]
  exact fun h ↦ hp (hf (h.trans f.map_zero.symm))
private theorem fresh_value_ne_zero {a : Fin taylorLength → Geom} {i : Fin taylorLength}
    (hi : a i ≠ 0) : eval (geomConstants ∘ a) (jetLinear genericArgument 0) ≠ 0 := by
  have hinj : Function.Injective genericCoeffs :=
    (algebraMap GenericField GeoField).injective.comp (IsFractionRing.injective (Polynomial Geom) GenericField)
  have hne := polynomial_value_ne_zero genericCoeffs hinj Fin.val Fin.val_injective a hi
  intro h
  apply hne
  rw [← h]
  unfold jetLinear
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [map_mul, eval_C, eval_X, Nat.choose_zero_right, Nat.cast_one, one_mul,
    Nat.sub_zero, Function.comp_apply, genericArgument, geomConstants, RingHom.comp_apply]
theorem noBoundaryZero_of_charts (A : CoeffIdeal)
    (hA : ∀ i, dimension (boundaryChart A i) = 0) :
    NoBoundaryZero (extendIdeal A) (jetLinear genericArgument 0) := by
  classical
  letI : Algebra Geom GeoField := geomConstants.toAlgebra
  intro x hx hval
  funext i
  change x i = 0
  by_contra hi
  let b : Fin taylorLength → GeoField := fun j ↦ (x i)⁻¹ * x j
  have hb : b ∈ zeroLocus GeoField (boundaryChart A i) := normalize_boundary A hx hi
  choose a ha using fun j ↦ finite_chart_coordinates (boundaryChart A i) (hA i) hb j
  have he : geomConstants ∘ a = b := funext ha
  have hai : a i ≠ 0 := by
    intro ha₀
    have hz := ha i
    change geomConstants (a i) = (x i)⁻¹ * x i at hz
    rw [ha₀, map_zero, inv_mul_cancel₀ hi] at hz
    exact zero_ne_one hz
  apply fresh_value_ne_zero hai
  rw [he]
  exact eval_scale_zero x ((x i)⁻¹) (jetLinear_homogeneous genericArgument 0) hval
end
end K1_13_6_3_4
end
section
set_option autoImplicit false
namespace K1_13_6_3_3
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 MvPolynomial
open scoped Polynomial
def c1 : Prop :=
  ∀ A : CoeffIdeal, A.IsPrime →
    (extendIdeal A).IsPrime ∧ dimension (extendIdeal A) = dimension A ∧
      (extendIdeal A).comap (MvPolynomial.map geomConstants) = A
def c2 : Prop :=
  ∀ (g : Row 4) (i : Fin taylorLength), ∃ (u : GeoJets) (e : ℕ),
    ∀ A : CoeffIdeal, A.IsPrime → (extendIdeal A).IsPrime →
      toGeneric g ∈ freshImage A → toGeneric (separant g) ∉ freshImage A →
      MvPolynomial.X i * freshJetMap (toGeneric (separant g)) ^ e -
        freshJetMap u ∈ extendIdeal A
private theorem recovery_of_generators (rec : c2) (g : Row 4) (h : FreshCoeffRing) :
    ∃ (u : GeoJets) (e : ℕ), ∀ A : CoeffIdeal, A.IsPrime → (extendIdeal A).IsPrime →
      toGeneric g ∈ freshImage A → toGeneric (separant g) ∉ freshImage A →
      h * freshJetMap (toGeneric (separant g)) ^ e - freshJetMap u ∈ extendIdeal A := by
  let s := toGeneric (separant g)
  induction h using MvPolynomial.induction_on with
  | C a =>
    refine ⟨MvPolynomial.C a, 0, fun A _ _ _ _ => ?_⟩
    simp [freshJetMap]
  | add h h' ih ih' =>
    obtain ⟨u, e, hu⟩ := ih
    obtain ⟨v, d, hv⟩ := ih'
    refine ⟨u * s ^ d + v * s ^ e, e + d, fun A hp he hg hs => ?_⟩
    let q := Ideal.Quotient.mk (extendIdeal A)
    have hu' := Ideal.Quotient.eq_zero_iff_mem.mpr (hu A hp he hg hs)
    have hv' := Ideal.Quotient.eq_zero_iff_mem.mpr (hv A hp he hg hs)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (h * freshJetMap s ^ e - freshJetMap u) = 0 at hu'
    change q (h' * freshJetMap s ^ d - freshJetMap v) = 0 at hv'
    change q ((h + h') * freshJetMap s ^ (e + d) - freshJetMap
      (u * s ^ d + v * s ^ e)) = 0
    simp only [map_add, map_mul, map_sub, map_pow, pow_add] at hu' hv' ⊢
    linear_combination q (freshJetMap s) ^ d * hu' + q (freshJetMap s) ^ e * hv'
  | mul_X h i ih =>
    obtain ⟨u, e, hu⟩ := ih
    obtain ⟨v, d, hv⟩ := rec g i
    refine ⟨u * v, e + d, fun A hp he hg hs => ?_⟩
    let q := Ideal.Quotient.mk (extendIdeal A)
    have hu' := Ideal.Quotient.eq_zero_iff_mem.mpr (hu A hp he hg hs)
    have hv' := Ideal.Quotient.eq_zero_iff_mem.mpr (hv A hp he hg hs)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (h * freshJetMap s ^ e - freshJetMap u) = 0 at hu'
    change q (MvPolynomial.X i * freshJetMap s ^ d - freshJetMap v) = 0 at hv'
    change q ((h * MvPolynomial.X i) * freshJetMap s ^ (e + d) - freshJetMap
      (u * v)) = 0
    simp only [map_mul, map_sub, map_pow, pow_add, sub_eq_zero] at hu' hv' ⊢
    calc
      _ = (q h * q (freshJetMap s) ^ e) *
          (q (MvPolynomial.X i) * q (freshJetMap s) ^ d) := by ac_rfl
      _ = _ := by rw [hu', hv']
private theorem fresh_prime {A : CoeffIdeal} (hA : (extendIdeal A).IsPrime) :
    (freshImage A).IsPrime := by
  let _ := hA
  exact inferInstanceAs ((extendIdeal A).comap freshJetMap).IsPrime
private theorem fresh_birational (rec : c2) {A : CoeffIdeal} (hA : A.IsPrime)
    (hext : (extendIdeal A).IsPrime) {g : Row 4}
    (hg : toGeneric g ∈ freshImage A) (hs : toGeneric (separant g) ∉ freshImage A) :
    FreshBirational A := by
  intro h
  obtain ⟨u, e, hrel⟩ := recovery_of_generators rec g h
  refine ⟨u, toGeneric (separant g) ^ e, ?_, ?_⟩
  · intro hp
    exact hs ((fresh_prime hext).mem_of_pow_mem e hp)
  · rw [map_pow]
    exact hrel A hA hext hg hs
private def freshJetAlgHom : GeoJets →ₐ[GeoField] FreshCoeffRing :=
  MvPolynomial.aeval (fun i : Fin 4 => jetLinear genericArgument i.val)
private theorem freshJetAlgHom_toRingHom : freshJetAlgHom.toRingHom = freshJetMap := by
  ext a <;> simp [freshJetAlgHom, freshJetMap]
private theorem dim_fresh_of_recovery (rec : c2) {A : CoeffIdeal}
    (hA : A.IsPrime) (hext : (extendIdeal A).IsPrime) {g : Row 4}
    (hg : toGeneric g ∈ freshImage A) (hs : toGeneric (separant g) ∉ freshImage A) :
    dimension (freshImage A) = dimension (extendIdeal A) := by
  let I := extendIdeal A
  let J := freshImage A
  let v := toGeneric (separant g)
  have hJ : J = I.comap freshJetAlgHom := by
    change I.comap freshJetMap = I.comap freshJetAlgHom.toRingHom
    rw [freshJetAlgHom_toRingHom]
  let F := Ideal.quotientMapₐ I freshJetAlgHom hJ.le
  have hinj : Function.Injective F := Ideal.quotientMap_injective' (H := hJ.le) hJ.ge
  apply le_antisymm (natDegree_affineHilbertPolynomial_le_of_injective F hinj)
  let vI := freshJetMap v
  have hFv : F (Ideal.Quotient.mk J v) = Ideal.Quotient.mk I vI := by
    rw [Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk]
    change Ideal.Quotient.mk I (freshJetAlgHom.toRingHom v) = _
    rw [freshJetAlgHom_toRingHom]
  let L := Localization.Away (Ideal.Quotient.mk I vI)
  let _ : IsLocalization.Away (F (Ideal.Quotient.mk J v)) L := by
    rw [hFv]
    infer_instance
  let G := IsLocalization.Away.mapₐ (R := GeoField)
    (Localization.Away (Ideal.Quotient.mk J v)) L F (Ideal.Quotient.mk J v)
  have hsurj : Function.Surjective G := by
    apply (IsLocalization.Away.map_surjective_iff _ _ F.toRingHom (Ideal.Quotient.mk J v)).mpr
    intro x
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨u, e, hrel⟩ := recovery_of_generators rec g h
    have hEq := sub_eq_zero.mp (show
      Ideal.Quotient.mk I (h * vI ^ e) - Ideal.Quotient.mk I (freshJetMap u) = 0 by
      rw [← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hrel A hA hext hg hs))
    refine ⟨Ideal.Quotient.mk J u, e, ?_⟩
    change F (Ideal.Quotient.mk J u) = F (Ideal.Quotient.mk J v) ^ e * Ideal.Quotient.mk I h
    rw [hFv, Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk]
    change Ideal.Quotient.mk I (freshJetAlgHom.toRingHom u) = _
    rw [freshJetAlgHom_toRingHom, ← hEq, map_mul, map_pow, mul_comm]
  let _ : I.IsPrime := hext
  have hreg : IsLeftRegular (Ideal.Quotient.mk I vI) :=
    IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
      (mt Ideal.Quotient.eq_zero_iff_mem.mp hs)
  exact natDegree_affineHilbertPolynomial_le_of_surjective_away_away hreg G hsurj
private theorem dim_lt_of_prime_lt {P J : JetIdeal} (hP : P.IsPrime) (hJ : J.IsPrime)
    (hlt : P < J) : dimension J < dimension P := by
  classical
  obtain ⟨s, hJmem, hPmem⟩ := SetLike.exists_of_lt hlt
  have hcut : P ⊔ Ideal.span {s} ≤ J :=
    sup_le hlt.le ((Ideal.span_singleton_le_iff_mem J).mpr hJmem)
  let _ := hJ
  obtain ⟨T, hT, hle⟩ := Ideal.exists_minimalPrimes_le hcut
  let _ := hP
  have hd := principalCut_natDegree_affineHilbertPolynomial_add_one hPmem hT
  have hlt' : dimension T < dimension P := by
    change dimension T + 1 = dimension P at hd
    omega
  exact lt_of_le_of_lt (natDegree_affineHilbertPolynomial_le_of_le hle) hlt'
theorem classify {f Q g : Row 4} {surface P J : JetIdeal} (hp : P.IsPrime)
    (hJ : J.IsPrime) (hS : (intersectionIdeal f Q).IsMinimalPrime surface)
    (hCycle : ∀ T, (intersectionIdeal f Q).IsMinimalPrime T → dimension T = 2)
    (hsource : P = surface ∨ SimpleCut g surface P) (hcontain : intersectionIdeal f Q ≤ J)
    (hold : J ≤ P) {A : CoeffIdeal} (hdim : dimension J = dimension A) :
    ((dimension A = 1 ∧ J = P ∧ SimpleCut g surface P) ∨
      (dimension A = 2 ∧ (intersectionIdeal f Q).IsMinimalPrime J)) := by
  let _ := hJ
  obtain ⟨T, hT, hTJ⟩ := Ideal.exists_minimalPrimes_le hcontain
  have hdT := hCycle T hT
  have hdJ := natDegree_affineHilbertPolynomial_le_of_le hTJ
  change dimension J ≤ dimension T at hdJ
  have hdP : 1 ≤ dimension P := by
    rcases hsource with hEq | hcut
    · rw [hEq, hCycle surface hS]
      decide
    · let _ := hS.isPrime
      have hd := principalCut_natDegree_affineHilbertPolynomial_add_one hcut.proper hcut.minimal
      change dimension P + 1 = dimension surface at hd
      rw [hCycle surface hS] at hd
      omega
  have hPJ := natDegree_affineHilbertPolynomial_le_of_le hold
  change dimension P ≤ dimension J at hPJ
  by_cases hd1 : dimension J = 1
  · have hEq : J = P := by
      by_contra hne
      have := dim_lt_of_prime_lt hJ hp (lt_of_le_of_ne hold hne)
      omega
    have hcut : SimpleCut g surface P := by
      rcases hsource with hEq' | hcut
      · rw [hEq, hEq', hCycle surface hS] at hd1
        contradiction
      · exact hcut
    exact Or.inl ⟨hdim.symm.trans hd1, hEq, hcut⟩
  · have hd2 : dimension J = 2 := by omega
    have hEq : T = J := by
      by_contra hne
      have := dim_lt_of_prime_lt hT.isPrime hJ (lt_of_le_of_ne hTJ hne)
      omega
    exact Or.inr ⟨hdim.symm.trans hd2, hEq ▸ hT⟩
private theorem injective_on_regular (base : c1) (rec : c2) (f : Row 4) :
    Set.InjOn freshImage {A | A.IsPrime ∧ FreshRegular f A} := by
  intro A hA B hB himage
  obtain ⟨hAp, hAr⟩ := hA
  obtain ⟨hBp, _⟩ := hB
  obtain ⟨hAe, _, hAc⟩ := base A hAp
  obtain ⟨hBe, _, hBc⟩ := base B hBp
  obtain ⟨r, hgA, hsA⟩ := hAr
  let g := (separant^[r]) f
  have hgB : toGeneric g ∈ freshImage B := himage ▸ hgA
  have hsB : toGeneric (separant g) ∉ freshImage B := himage ▸ hsA
  have hEq : extendIdeal A = extendIdeal B := by
    ext h
    obtain ⟨u, e, hrel⟩ := recovery_of_generators rec g h
    let s := freshJetMap (toGeneric (separant g))
    have transfer (D : CoeffIdeal) (hDp : D.IsPrime) (hDe : (extendIdeal D).IsPrime)
        (hgD : toGeneric g ∈ freshImage D) (hsD : toGeneric (separant g) ∉ freshImage D) :
        h ∈ extendIdeal D ↔ u ∈ freshImage D := by
      have hdiff : h * s ^ e - freshJetMap u ∈ extendIdeal D := hrel D hDp hDe hgD hsD
      have hn : s ^ e ∉ extendIdeal D := fun hp => hsD (hDe.mem_of_pow_mem e hp)
      change _ ↔ freshJetMap u ∈ extendIdeal D
      constructor
      · intro hh
        have hm := Ideal.mul_mem_right (s ^ e) (extendIdeal D) hh
        exact ((extendIdeal D).sub_mem_iff_right hm).1 hdiff
      · intro hu
        have hm := ((extendIdeal D).sub_mem_iff_left hu).1 hdiff
        exact (hDe.mem_or_mem hm).resolve_right hn
    rw [transfer A hAp hAe hgA hsA, transfer B hBp hBe hgB hsB, himage]
  rw [← hAc, ← hBc, hEq]
theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_3.c3 := by
  refine ⟨?_, injective_on_regular h1 h2⟩
  intro f Q surface r P hp U hS hCycle
  dsimp only
  intro hsep hsource hIntegrated
  let _ := hp
  let A := coefficientKernel (componentConstants P) U
  have hA : A.IsPrime := RingHom.ker_isPrime _
  obtain ⟨hext, hdim, _⟩ := h1 A hA
  obtain ⟨hcontain, hold, hg, hs⟩ := trajectory_to_fresh hIntegrated hsep
  refine ⟨⟨hA, hext, ⟨r, hg, hs⟩, fresh_birational h2 hA hext hg hs⟩, ?_⟩
  exact classify hp (fresh_prime hext) hS hCycle hsource hcontain hold
    ((dim_fresh_of_recovery h2 hA hext hg hs).trans hdim)
end
end K1_13_6_3_3
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace K1_13_6_3_5_3_2_1
open K1_13_6_3_5_3_2 IntermediateField
open scoped algebraAdjoinAdjoin Polynomial
noncomputable section
def frobeniusRange (k A : Type) [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] (p n : ℕ) [ExpChar k p] [ExpChar A p] : Subalgebra k A :=
  { (iterateFrobenius A p n).range.toSubsemiring with
    algebraMap_mem' r := by
      obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq r (expChar_pow_pos k p n)
      exact ⟨algebraMap k A s, by rw [iterateFrobenius_def, ← map_pow, hs]⟩ }
theorem finite_over_frobeniusRange (k A : Type) [Field k] [IsAlgClosed k]
    [CommRing A] [Algebra k A] (p n : ℕ) [ExpChar k p] [ExpChar A p]
    (z : A) (hz : Algebra.adjoin k ({z} : Set A) = ⊤) :
    Module.Finite (frobeniusRange k A p n) A := by
  let S := frobeniusRange k A p n
  let T := Algebra.adjoin S ({z} : Set A)
  have hi : IsIntegral S z := by
    apply IsIntegral.of_pow (expChar_pow_pos A p n)
    let s : S := ⟨z ^ p ^ n, ⟨z, rfl⟩⟩
    exact isIntegral_algebraMap (x := s)
  have ht : T = ⊤ := by
    have hle : Algebra.adjoin k ({z} : Set A) ≤ T.restrictScalars k :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr (Algebra.self_mem_adjoin_singleton S z))
    rw [hz] at hle
    exact le_antisymm le_top fun a _ => hle (Algebra.mem_top (R := k) (x := a))
  have hfg : T.toSubmodule.FG := hi.fg_adjoin_singleton
  rw [ht, Algebra.top_toSubmodule] at hfg
  exact ⟨hfg⟩
theorem proof : K1_13_6_3_5_3_2.c1 := by
  intro k L _ _ _ _ x hx hfin
  let A := ParameterRing k L x
  let K := IntermediateField.adjoin k ({x} : Set L)
  let E := separableClosure K L
  let B := Normalization k L x
  let C := integralClosure A E
  have : Module.Finite K L := hfin
  have : IsScalarTower A E L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsPrincipalIdealRing A := parameterRing_pid hx
  have : Module.Finite A C := IsIntegralClosure.finite A K E C
  let p := ringExpChar L
  have : ExpChar L p := ringExpChar.expChar L
  have : ExpChar k p := (algebraMap k L).expChar (algebraMap k L).injective p
  have : ExpChar A p := (algebraMap A L).expChar Subtype.val_injective p
  have : ExpChar E p := (algebraMap E L).expChar (algebraMap E L).injective p
  let n := IsPurelyInseparable.exponent E L
  let S := frobeniusRange k A p n
  let z : A := ⟨x, Algebra.self_mem_adjoin_singleton k x⟩
  have hz : Algebra.adjoin k ({z} : Set A) = ⊤ := by
    rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.range_eq_top]
    intro a
    obtain ⟨f, hf⟩ := (Polynomial.algEquivOfTranscendental k x hx).surjective a
    exact ⟨f, hf⟩
  have : Module.Finite S A := finite_over_frobeniusRange k A p n z hz
  let σ : A →+* S := (iterateFrobenius A p n).rangeRestrict
  let e : A ≃+* S := RingEquiv.ofBijective σ
    ⟨fun _ _ h => iterateFrobenius_inj A p n (congrArg Subtype.val h),
      (iterateFrobenius A p n).rangeRestrict_surjective⟩
  have : RingHomInvPair (e : A →+* S) (e.symm : S →+* A) := RingHomInvPair.of_ringEquiv e
  have : RingHomInvPair (e.symm : S →+* A) (e : A →+* S) := RingHomInvPair.of_ringEquiv e.symm
  have : IsNoetherianRing S := isNoetherianRing_of_ringEquiv A e
  have : Module.Finite S C := Module.Finite.trans A C
  have : IsNoetherian S C := inferInstance
  let F : L →+* E := IsPurelyInseparable.iterateFrobenius E L p (n := n) le_rfl
  have hF (b : L) : algebraMap E L (F b) = b ^ p ^ n :=
    IsPurelyInseparable.algebraMap_iterateFrobenius E p le_rfl b
  have hmem (b : B) : F b.val ∈ integralClosure A E := by
    change IsIntegral A (F b.val)
    apply (IntermediateField.coe_isIntegral_iff (R := A)).mp
    change IsIntegral A (algebraMap E L (F b.val))
    rw [hF]
    exact (show IsIntegral A b.val from b.property).pow _
  let g : B →+* C :=
    (F.comp (integralClosure A L).val.toRingHom).codRestrict (integralClosure A E).toSubring hmem
  let f : B →ₛₗ[(e : A →+* S)] C :=
    { g with
      map_smul' a b := by
        apply Subtype.ext
        apply (algebraMap E L).injective
        change algebraMap E L (F (algebraMap A L a * b.val)) =
          algebraMap E L (algebraMap A E (a ^ p ^ n) * F b.val)
        rw [hF, mul_pow, map_mul, ← IsScalarTower.algebraMap_apply A E L, map_pow, hF] }
  apply Module.Finite.of_injective f
  intro b b' hb
  apply Subtype.ext
  apply iterateFrobenius_inj L p n
  change b.val ^ p ^ n = b'.val ^ p ^ n
  rw [← hF, ← hF]
  exact congrArg (fun c : C => algebraMap E L c.val) hb
end
end K1_13_6_3_5_3_2_1
end
section
set_option autoImplicit false
namespace K1_13_6_3_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_3
def c1 : Prop :=
  ∀ (f Q : Row 4) (surface : JetIdeal)
    (hz : (intersectionIdeal f Q).IsMinimalPrime surface),
    cycleLength (intersectionIdeal f Q) surface hz.isPrime < (K1.p : ℕ∞) →
    (surface.comap sepToGeo).map sepToGeo = surface
def c2 : Prop :=
  ∀ (g : Row 4) (surface : JetIdeal), surface.IsPrime → Invariant g surface →
    ∃ D : Derivation ℤ SepJets SepJets,
      (∀ U : Row 4, D (rowToSep U) = rowToSep (flowNumerator g U)) ∧
      (∀ u ∈ surface.comap sepToGeo, D u ∈ surface.comap sepToGeo)
private theorem step_in_sep (g : Row 4) (D : Derivation ℤ SepJets SepJets)
    (hD : ∀ U : Row 4, D (rowToSep U) = rowToSep (flowNumerator g U))
    (n : ℕ) :
    rowToSep (jetNumerator g (n+1)) =
      rowToSep (separant g) * D (rowToSep (jetNumerator g n)) -
        (↑(2*n) : SepJets) * D (rowToSep (separant g)) * rowToSep (jetNumerator g n) := by
  simp only [jetNumerator, clearedStep, map_sub, map_mul, map_natCast, ← hD]
private theorem sep_sq_dvd_jet (g : Row 4) (D : Derivation ℤ SepJets SepJets)
    (hD : ∀ U : Row 4, D (rowToSep U) = rowToSep (flowNumerator g U))
    (n : ℕ) (hn : 1 ≤ n) :
    rowToSep (separant g)^2 ∣ rowToSep (jetNumerator g n) := by
  let s := rowToSep (separant g)
  change s^2 ∣ _
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      have hz : separant (MvPolynomial.X (0 : Fin 4) : Row 4) = 0 := by
        simp [separant, MvPolynomial.pderiv_X]
      use rowToSep (partialFlow (MvPolynomial.X 0))
      rw [step_in_sep g D hD 0, jetNumerator, hD, flowNumerator, hz]
      simp [s, pow_two, mul_assoc]
    | succ n =>
      obtain ⟨w, hw⟩ := ih (Nat.succ_pos _)
      rw [step_in_sep g D hD (n+1)]
      change s^2 ∣ s * D (rowToSep (jetNumerator g (n+1))) -
        (↑(2*(n+1)) : SepJets) * D s * rowToSep (jetNumerator g (n+1))
      rw [hw]
      use s * D w + 2 * D s * w - (↑(2*(n+1)) : SepJets) * D s * w
      simp only [pow_two, D.leibniz, smul_eq_mul]
      ring
private theorem nonvanishing_of_simple_cut {R : Type*} [CommRing R]
    (T P : Ideal R) [T.IsPrime] (hle : T ≤ P) {s e : R}
    (hs : s ∉ T) (he : s^2 ∣ e)
    (hsat : ∀ x ∈ P, ∃ t ∉ P, t * x ∈ T ⊔ Ideal.span {e}) : s ∉ P := by
  intro hsp
  obtain ⟨v, hv, hvs⟩ := hsat s hsp
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hvs
  obtain ⟨w, hw⟩ := he
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hb
  have hrel : s * (v - s * (w*c)) = a := by
    rw [hc, hw] at hab
    linear_combination -hab
  have hmem : v - s * (w*c) ∈ T :=
    (‹T.IsPrime›.mem_or_mem (hrel.symm ▸ ha)).resolve_left hs
  apply hv
  have hm := P.add_mem (hle hmem) (P.mul_mem_right (w*c) hsp)
  simpa using hm
private theorem stable_of_simple_cut {R : Type*} [CommRing R]
    (T P : Ideal R) [P.IsPrime] (hle : T ≤ P)
    (D : Derivation ℤ R R) (hT : ∀ u ∈ T, D u ∈ T)
    {e : R} (he : e ∈ P) (hDe : D e ∈ P)
    (hsat : ∀ x ∈ P, ∃ t ∉ P, t * x ∈ T ⊔ Ideal.span {e}) :
    ∀ u ∈ P, D u ∈ P := by
  intro u hu
  obtain ⟨t, ht, htu⟩ := hsat u hu
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp htu
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hb
  have hDb : D b ∈ P := by
    rw [hc, D.leibniz, smul_eq_mul, smul_eq_mul]
    exact P.add_mem (P.mul_mem_right _ he) (P.mul_mem_left _ hDe)
  have hDtu : D (t*u) ∈ P := by
    rw [← hab, map_add]
    exact P.add_mem (hle (hT a ha)) hDb
  rw [D.leibniz, smul_eq_mul, smul_eq_mul] at hDtu
  exact (‹P.IsPrime›.mem_or_mem
    ((P.add_mem_iff_left (P.mul_mem_right (D t) hu)).mp hDtu)).resolve_left ht
theorem of_children (h1 : c1) (h2 : c2) : K1_13_6_3.c1 := by
  intro f Q surface r P hz hchart hlen g hI hcut
  let T := surface.comap sepToGeo
  let q := P.comap sepToGeo
  let s := rowToSep (separant g)
  let e := rowToSep (membershipTest g)
  have : T.IsPrime := hz.isPrime.comap sepToGeo
  have : q.IsPrime := hcut.minimal.isPrime.comap sepToGeo
  obtain ⟨D, hD, hstable⟩ := h2 g surface hz.isPrime hI
  have hle : T ≤ q := Ideal.comap_mono (le_sup_left.trans hcut.minimal.le)
  have he : e ∈ q := by
    change sepToGeo (rowToSep (membershipTest g)) ∈ P
    rw [sepToGeo_rowToSep]
    apply hcut.minimal.le
    exact Submodule.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hsat := simple_saturation g surface P (h1 f Q surface hz hlen) hcut
  have hs : s ∉ T := by
    change sepToGeo (rowToSep (separant g)) ∉ surface
    rw [sepToGeo_rowToSep]
    exact hchart.2.2
  have hsq : s^2 ∣ e := sep_sq_dvd_jet g D hD taylorLength (by decide)
  have hs' : s ∉ q := nonvanishing_of_simple_cut T q hle hs hsq hsat
  have hnext : rowToSep (nextTest g) ∈ q := by
    change sepToGeo (rowToSep (nextTest g)) ∈ P
    rw [sepToGeo_rowToSep]
    exact hcut.next
  change rowToSep (jetNumerator g (taylorLength+1)) ∈ q at hnext
  rw [step_in_sep g D hD taylorLength] at hnext
  change s * D e - (↑(2*taylorLength) : SepJets) * D s * e ∈ q at hnext
  have hDe : D e ∈ q :=
    (‹q.IsPrime›.mem_or_mem
      ((q.sub_mem_iff_left (q.mul_mem_left _ he)).mp hnext)).resolve_left hs'
  intro U hU
  have hU' : rowToSep U ∈ q := by
    change sepToGeo (rowToSep U) ∈ P
    rwa [sepToGeo_rowToSep]
  have hflow : D (rowToSep U) ∈ q :=
    stable_of_simple_cut T q hle D hstable he hDe hsat _ hU'
  rw [← sepToGeo_rowToSep]
  change rowToSep (flowNumerator g U) ∈ q
  exact (hD U) ▸ hflow
end
end K1_13_6_3_1
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_5
noncomputable section
open K1_13_6_3_5
variable {U V R S : Type} [CommRing U] [CommRing V] [CommRing R] [CommRing S]
structure SectionPresentation (J : Ideal U) (w : R) where
  toQuotient : R →+* U ⧸ J
  surjective : Function.Surjective toQuotient
  ker_eq : RingHom.ker toQuotient = Ideal.span {w}
def Compatible (g : U →+* V) (f : R →+* S) {J : Ideal U} {I : Ideal V} {w : R}
    (r : SectionPresentation J w) (s : SectionPresentation I (f w)) : Prop :=
  ∃ m : U ⧸ J →+* V ⧸ I,
    m.comp (Ideal.Quotient.mk J) = (Ideal.Quotient.mk I).comp g ∧
    m.comp r.toQuotient = s.toQuotient.comp f
structure ConeModel {k σ τ : Type} [Field k]
    (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k) (A : Ideal (MvPolynomial σ k)) where
  F : Type
  [field : Field F]
  [algebra : Algebra k F]
  target : Subalgebra k F
  source : Subalgebra k F
  le : target ≤ source
  targetNoetherian : IsNoetherianRing target
  sourceNoetherian : IsNoetherianRing source
  fraction : IsFractionRing target F
  w : target
  w_ne : w ≠ 0
  targetSection : SectionPresentation (boundaryIdeal (A.comap φ)) w
  sourceSection : SectionPresentation (boundaryIdeal A) (Subalgebra.inclusion le w)
  compatible : Compatible φ.toRingHom (Subalgebra.inclusion le).toRingHom
    targetSection sourceSection
abbrev LocalSection (J p : Ideal R) [p.IsPrime] :=
  Localization.AtPrime p ⧸ J.map (algebraMap R (Localization.AtPrime p))
def weight (J p : Ideal R) : ℕ := by
  classical
  exact if hp : p.IsPrime then
    letI := hp
    (Module.length (Localization.AtPrime p) (LocalSection J p)).toNat
  else 0
def degree (f : R →+* S) (p : Ideal S) : ℕ := by
  classical
  exact if hp : p.IsPrime then
    letI := hp
    letI : (p.comap f).IsPrime := Ideal.IsPrime.comap f
    let g : FractionRing (R ⧸ p.comap f) →+* FractionRing (S ⧸ p) :=
      IsFractionRing.map (Ideal.quotientMap_injective (I := p) (f := f))
    letI := g.toAlgebra
    Module.finrank (FractionRing (R ⧸ p.comap f)) (FractionRing (S ⧸ p))
  else 0
def fibrePrimes [IsNoetherianRing S] (f : R →+* S) (J : Ideal S) (q : Ideal R) :
    Finset (Ideal S) := by
  classical
  exact J.minimalPrimesFinset.filter (fun p => p.comap f = q)
def fibreWeight [IsNoetherianRing S] (f : R →+* S) (J : Ideal S) (q : Ideal R) : ℕ :=
  ∑ p ∈ fibrePrimes f J q, weight J p * degree f p
theorem fibre_prime [IsNoetherianRing S] {f : R →+* S} {J : Ideal S} {q : Ideal R}
    (p : fibrePrimes f J q) : (p : Ideal S).IsPrime :=
  (Ideal.mem_minimalPrimesFinset.mp (Finset.mem_filter.mp p.property).1).isPrime
theorem fibre_comap [IsNoetherianRing S] {f : R →+* S} {J : Ideal S} {q : Ideal R}
    (p : fibrePrimes f J q) : q = (p : Ideal S).comap f :=
  (Finset.mem_filter.mp p.property).2.symm
def branchLength [IsNoetherianRing S] (f : R →+* S) (J : Ideal S) (q : Ideal R)
    [q.IsPrime] (p : fibrePrimes f J q) : ℕ∞ :=
  letI : (p : Ideal S).IsPrime := fibre_prime p
  letI := (Localization.localRingHom q (p : Ideal S) f (fibre_comap p)).toAlgebra
  Module.length (Localization.AtPrime q) (LocalSection J (p : Ideal S))
abbrev FractionSubalgebra (L : Type) [CommRing L] := Subalgebra L (FractionRing L)
abbrev SectionQuotient (x : R) (B : Type) [CommRing B] [Algebra R B] :=
  B ⧸ Ideal.span {algebraMap R B x}
def sectionLength (x : R) (B : Type) [CommRing B] [Algebra R B] : ℕ∞ :=
  Module.length R (SectionQuotient x B)
end
end K1_13_6_3_5_5
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 2000
namespace K1_13_6_3_4
noncomputable section
open K1_13_6 K1_13_6_3 MvPolynomial
def c1 : Prop :=
  ∀ A : CoeffIdeal, affineHilbertPolynomial (extendIdeal A) = affineHilbertPolynomial A
def c2 : Prop :=
  ∀ A : CoeffIdeal, A.IsPrime → dimension A = 1 →
    ∀ i : Fin K1_13.taylorLength, dimension (boundaryChart A i) = 0
def c3 : Prop :=
  ∀ I : Ideal FreshCoeffRing,
    NoBoundaryZero I (jetLinear genericArgument 0) →
    ValueReduction I (jetLinear genericArgument 0)
def jetAlg : GeoJets →ₐ[GeoField] FreshCoeffRing :=
  aeval (fun i : Fin 4 ↦ jetLinear genericArgument i.val)
theorem jetAlg_apply (p : GeoJets) : jetAlg p = freshJetMap p := rfl
private def jetQuot (A : CoeffIdeal) :
    (GeoJets ⧸ freshImage A) →ₐ[GeoField] (FreshCoeffRing ⧸ extendIdeal A) :=
  Ideal.quotientMapₐ (extendIdeal A) jetAlg (by
    intro p hp
    exact hp)
private theorem jetQuot_mk (A : CoeffIdeal) (p : GeoJets) :
    jetQuot A (Ideal.Quotient.mk (freshImage A) p) = Ideal.Quotient.mk (extendIdeal A) (freshJetMap p) := rfl
private theorem jetQuot_X (A : CoeffIdeal) (j : Fin 4) :
    jetQuot A (Ideal.Quotient.mk (freshImage A) (MvPolynomial.X j)) =
      Ideal.Quotient.mk (extendIdeal A) (jetLinear genericArgument j.val) := by
  rw [jetQuot_mk, ← jetAlg_apply]
  exact congrArg (Ideal.Quotient.mk (extendIdeal A)) (aeval_X _ _)
private theorem jetQuot_injective (A : CoeffIdeal) : Function.Injective (jetQuot A) := by
  apply (injective_iff_map_eq_zero (jetQuot A)).mpr
  intro z hz
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [jetQuot_mk, Ideal.Quotient.eq_zero_iff_mem] at hz
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hz
theorem birational_quotient {A : CoeffIdeal} (hb : FreshBirational A)
    (x : FreshCoeffRing ⧸ extendIdeal A) :
    ∃ a b, jetQuot A b ≠ 0 ∧ jetQuot A b * x = jetQuot A a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨u, v, hv, huv⟩ := hb p
  refine ⟨Ideal.Quotient.mk _ u, Ideal.Quotient.mk _ v, ?_, ?_⟩
  · rwa [jetQuot_mk, Ne, Ideal.Quotient.eq_zero_iff_mem]
  · rw [jetQuot_mk, jetQuot_mk, mul_comm, ← map_mul, ← sub_eq_zero, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr huv
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : K1_13_6_3.c4 := by
  intro A hA hExt hdim hb
  letI := hExt
  have hred := h3 (extendIdeal A) (noBoundaryZero_of_charts A (h2 A hA hdim))
  have hlin (j : Fin 4) :
      jetQuot A (Ideal.Quotient.mk (freshImage A) (MvPolynomial.X j)) ∈
        quotientDegreeLE (extendIdeal A) 1 := by
    rw [jetQuot_X]
    exact mk_mem_quotientDegreeLE (jetLinear_homogeneous genericArgument j.val).totalDegree_le
  have hz : jetQuot A (Ideal.Quotient.mk (freshImage A) (MvPolynomial.X 0)) =
      Ideal.Quotient.mk (extendIdeal A) (jetLinear genericArgument 0) := jetQuot_X A 0
  have he := degree_eq_of_valueReduction (jetQuot A) (jetQuot_injective A) 0 hz hlin
    (birational_quotient hb) hred
  have hext : affineDegree (extendIdeal A) = affineDegree A := by
    unfold affineDegree
    rw [h1 A]
  exact hext.symm.trans he
end
end K1_13_6_3_4
end
section
set_option autoImplicit false
namespace K1_13_6_3_6
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 MvPolynomial RingTheory.Sequence
open scoped TensorProduct Pointwise
attribute [local instance] MvPolynomial.algebraMvPolynomial
theorem geometryCoeffs_injective : Function.Injective genericCoeffs :=
  (algebraMap GenericField GeoField).injective.comp
    (IsFractionRing.injective (K := GenericField) _)
theorem totalDegree_toGeneric (f : Row 4) :
    (toGeneric f).totalDegree = f.totalDegree := by
  unfold totalDegree toGeneric
  rw [support_map_of_injective _ geometryCoeffs_injective]
theorem toGeneric_ne_zero {f : Row 4} (hf : f ≠ 0) : toGeneric f ≠ 0 :=
  fun h => hf (MvPolynomial.map_injective _ geometryCoeffs_injective (h.trans (map_zero _).symm))
private theorem geometry_flat :
    Module.Flat (MvPolynomial (Fin 4) GenericField) GeoJets := by
  let R := GenericField
  let B := MvPolynomial (Fin 4) R
  let E := GeoField
  let e : B ⊗[R] E ≃ₐ[B] GeoJets :=
    { __ := ((Algebra.TensorProduct.comm R B E).trans
        ((algebraTensorAlgEquiv (σ := Fin 4) R E).restrictScalars R)).toRingEquiv
      commutes' := fun b => by
        change algebraTensorAlgEquiv R E (1 ⊗ₜ[R] b) = algebraMap B GeoJets b
        simpa only [algebraTensorAlgEquiv_tmul, one_smul] using
          congrFun (congrArg DFunLike.coe (MvPolynomial.algebraMap_def (σ := Fin 4)
            (R := GenericField) (S := GeoField)).symm) b }
  exact Module.Flat.of_linearEquiv e.symm.toLinearEquiv
private theorem weaklyRegular_pair_iff {R : Type} [CommRing R] (f Q : R) :
    IsWeaklyRegular R [f, Q] ↔
      IsLeftRegular f ∧ IsLeftRegular (Ideal.Quotient.mk (Ideal.span {f}) Q) := by
  rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff]
  have h : f • (⊤ : Submodule R R) = (Ideal.span {f} : Submodule R R) := by
    rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  exact and_congr_right' ((Submodule.quotEquivOfEq _ _ h).isSMulRegular_congr Q)
theorem physical_weaklyRegular {f Q : Row 4} (hf : SmallFactor f)
    (hQ : ¬ f ∣ Q) : IsWeaklyRegular (Row 4) [f, Q] := by
  let I : Ideal (Row 4) := Ideal.span {f}
  have hprim : I.IsPrime := (Ideal.span_singleton_prime hf.1.ne_zero).2 hf.1.prime
  rw [weaklyRegular_pair_iff]
  refine ⟨IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hf.1.ne_zero, ?_⟩
  change IsLeftRegular (Ideal.Quotient.mk I Q)
  have := hprim
  exact IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
    (mt Ideal.Quotient.eq_zero_iff_mem.mp (Ideal.mem_span_singleton.not.mpr hQ))
theorem geometric_regular {f Q : Row 4} (hf : SmallFactor f) (hQ : ¬ f ∣ Q) :
    IsLeftRegular (Ideal.Quotient.mk (Ideal.span {toGeneric f}) (toGeneric Q)) := by
  let B := MvPolynomial (Fin 4) GenericField
  let T := (nonZeroDivisors (Polynomial Geom)).map
    (MvPolynomial.C (σ := Fin 4))
  have h₁ := (physical_weaklyRegular hf hQ).of_isLocalization B T
  have := geometry_flat
  have h₂ := h₁.of_flat (S := GeoJets)
  simp only [List.map_cons, List.map_nil] at h₂
  change IsWeaklyRegular GeoJets
    [MvPolynomial.map (algebraMap GenericField GeoField)
      (MvPolynomial.map (algebraMap (Polynomial Geom) GenericField) f),
     MvPolynomial.map (algebraMap GenericField GeoField)
      (MvPolynomial.map (algebraMap (Polynomial Geom) GenericField) Q)] at h₂
  have h₃ : IsWeaklyRegular GeoJets [toGeneric f, toGeneric Q] := by
    simpa only [toGeneric, genericCoeffs, MvPolynomial.map_map] using h₂
  exact ((weaklyRegular_pair_iff ..).mp h₃).2
theorem surface_dimension {f Q : Row 4} (hf : SmallFactor f) (hQ : ¬ f ∣ Q)
    {P : JetIdeal} (hP : (intersectionIdeal f Q).IsMinimalPrime P) : dimension P = 2 := by
  let F : Ideal GeoJets := Ideal.span {toGeneric f}
  have heq : intersectionIdeal f Q = F ⊔ Ideal.span {toGeneric Q} := by
    simp only [intersectionIdeal, F, ← Ideal.span_union, Set.singleton_union]
  have hFP : F ≤ P := le_sup_left.trans (heq ▸ hP.le)
  have := hP.isPrime
  obtain ⟨A, hA, hAP⟩ := Ideal.exists_minimalPrimes_le hFP
  have hn : toGeneric Q ∉ A := by
    intro h
    obtain ⟨y, hy, hxy⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hA h
    exact hy (Ideal.Quotient.eq_zero_iff_mem.mp (geometric_regular hf hQ (by
      change Ideal.Quotient.mk F (toGeneric Q) * Ideal.Quotient.mk F y =
        Ideal.Quotient.mk F (toGeneric Q) * 0
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hxy, mul_zero])))
  have hsub : A ⊔ Ideal.span {toGeneric Q} ≤ P :=
    sup_le hAP (le_sup_right.trans (heq ▸ hP.le))
  have hmin : P ∈ (A ⊔ Ideal.span {toGeneric Q}).minimalPrimes := by
    refine ⟨⟨hP.isPrime, hsub⟩, fun B hB hBP => hP.2 ⟨hB.1, ?_⟩ hBP⟩
    rw [heq]
    exact sup_le ((hA.le.trans le_sup_left).trans hB.2) (le_sup_right.trans hB.2)
  have h₁ := natDegree_affineHilbertPolynomial_add_one_of_mem_minimalPrimes_span_singleton
    (toGeneric_ne_zero hf.1.ne_zero) hA
  have := hA.isPrime
  have h₂ := principalCut_natDegree_affineHilbertPolynomial_add_one hn hmin
  rw [Nat.card_fin] at h₁
  change (affineHilbertPolynomial P).natDegree = 2
  omega
theorem intersection_hilbert {f Q : Row 4} (hf : SmallFactor f) (hQ : ¬ f ∣ Q) :
    dimension (intersectionIdeal f Q) ≤ 2 ∧
      2 * (affineHilbertPolynomial (intersectionIdeal f Q)).coeff 2 ≤
        (shape f).b * (shape Q).b := by
  let F : Ideal GeoJets := Ideal.span {toGeneric f}
  have heq : intersectionIdeal f Q = F ⊔ Ideal.span {toGeneric Q} := by
    simp only [intersectionIdeal, F, ← Ideal.span_union, Set.singleton_union]
  have hF : F ≠ ⊤ := by
    intro ht
    have hg : IsUnit (toGeneric f) := Ideal.span_singleton_eq_top.mp ht
    have hdeg := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hg).2
    have htop : (shape f).t ≤ f.totalDegree := degreeOf_le_totalDegree _ _
    rw [totalDegree_toGeneric] at hdeg
    have := hf.2.1
    omega
  have hdeg := natDegree_affineHilbertPolynomial_span_singleton_add_one
    (toGeneric_ne_zero hf.1.ne_zero) hF
  rw [Nat.card_fin] at hdeg
  have hthree : (affineHilbertPolynomial (Ideal.span {toGeneric f})).natDegree = 3 := by omega
  have hcoeff : 6 * (affineHilbertPolynomial F).leadingCoeff = (shape f).b := by
    have hd := affineDegree_span_singleton (toGeneric_ne_zero hf.1.ne_zero)
    rw [affineDegree, hthree, totalDegree_toGeneric] at hd
    norm_num at hd
    exact hd
  have hc := principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le
    (geometric_regular hf hQ) (totalDegree_toGeneric Q).le
  rw [← heq, hthree] at hc
  norm_num at hc
  refine ⟨hc.1, ?_⟩
  change 2 * (affineHilbertPolynomial (intersectionIdeal f Q)).coeff 2 ≤
    (f.totalDegree : ℚ) * (Q.totalDegree : ℚ)
  change 6 * (affineHilbertPolynomial F).leadingCoeff = (f.totalDegree : ℚ) at hcoeff
  nlinarith only [hc.2, congrArg (fun x : ℚ => x * Q.totalDegree) hcoeff]
end
end K1_13_6_3_6
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_4
noncomputable section
open MvPolynomial K1_13_6_3 K1_13_6_3_5
variable {k σ : Type*} [Field k]
theorem component_mem_boundary {I : Ideal (MvPolynomial σ k)}
    {p : MvPolynomial σ k} {n : ℕ} (hp : p ∈ I) (hn : p.totalDegree ≤ n) :
    homogeneousComponent n p ∈ boundaryIdeal I := by
  rcases hn.eq_or_lt with rfl | hn
  · exact Ideal.subset_span ⟨p, hp, rfl⟩
  · rw [homogeneousComponent_eq_zero _ _ hn]
    exact (boundaryIdeal I).zero_mem
private abbrev equations (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Submodule k (MvPolynomial σ k) :=
  I.restrictScalars k ⊓ restrictTotalDegree σ k n
theorem equations_finite [Finite σ] (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Module.Finite k (equations I n) :=
  Module.Finite.of_injective (Submodule.inclusion inf_le_right) (Submodule.inclusion_injective _)
def leadingMap (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    equations I n →ₗ[k] MvPolynomial σ k :=
  (homogeneousComponent n).domRestrict (equations I n)
theorem range_le (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    LinearMap.range (leadingMap I n) ≤ LinearMap.range (leadingMap (boundaryIdeal I) n) := by
  rintro _ ⟨p, rfl⟩
  have hp := (Submodule.mem_inf.mp p.property).1
  have hdeg := (mem_restrictTotalDegree σ n (p : MvPolynomial σ k)).mp
    (Submodule.mem_inf.mp p.property).2
  have hh := homogeneousComponent_isHomogeneous n (p : MvPolynomial σ k)
  refine ⟨⟨homogeneousComponent n p, Submodule.mem_inf.mpr ⟨
    component_mem_boundary hp hdeg, (mem_restrictTotalDegree σ n _).mpr hh.totalDegree_le⟩⟩, ?_⟩
  exact homogeneousComponent_eq_self hh
theorem leading_zero_iff {p : MvPolynomial σ k} {n : ℕ}
    (hp : p.totalDegree ≤ n + 1) :
    homogeneousComponent (n + 1) p = 0 ↔ p.totalDegree ≤ n := by
  constructor
  · intro hz
    apply Finset.sup_le
    intro d hd
    have hle : d.degree ≤ n + 1 := (le_totalDegree hd).trans hp
    have hne : d.degree ≠ n + 1 := by
      intro he
      apply mem_support_iff.mp hd
      simpa [coeff_homogeneousComponent, he] using
        congrArg (fun q : MvPolynomial σ k ↦ q.coeff d) hz
    exact Nat.le_of_lt_succ (lt_of_le_of_ne hle hne)
  · intro h
    exact homogeneousComponent_eq_zero _ _ (Nat.lt_succ_of_le h)
theorem finrank_leading_ker_succ (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Module.finrank k (LinearMap.ker (leadingMap I (n + 1))) =
      Module.finrank k (equations I n) := by
  have hle : equations I n ≤ equations I (n + 1) := by
    rintro p ⟨hp, hd⟩
    exact ⟨hp, (mem_restrictTotalDegree σ (n + 1) p).mpr
      (((mem_restrictTotalDegree σ n p).mp hd).trans (Nat.le_succ n))⟩
  have he : LinearMap.ker (leadingMap I (n + 1)) =
      (equations I n).comap (equations I (n + 1)).subtype := by
    ext p
    have hp := (Submodule.mem_inf.mp p.property).1
    have hdeg := (mem_restrictTotalDegree σ (n + 1) (p : MvPolynomial σ k)).mp
      (Submodule.mem_inf.mp p.property).2
    rw [LinearMap.mem_ker]
    change homogeneousComponent (n + 1) (p : MvPolynomial σ k) = 0 ↔
      (p : MvPolynomial σ k) ∈ equations I n
    rw [Submodule.mem_inf, mem_restrictTotalDegree, leading_zero_iff hdeg]
    exact ⟨fun h ↦ ⟨hp, h⟩, And.right⟩
  rw [he]
  exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
theorem finrank_leading_ker_zero (I : Ideal (MvPolynomial σ k)) :
    Module.finrank k (LinearMap.ker (leadingMap I 0)) = 0 := by
  have hker : LinearMap.ker (leadingMap I 0) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro p hp
    apply Subtype.ext
    have hdeg := (mem_restrictTotalDegree σ 0 (p : MvPolynomial σ k)).mp
      (Submodule.mem_inf.mp p.property).2
    change homogeneousComponent 0 (p : MvPolynomial σ k) = 0 at hp
    rw [homogeneousComponent_zero] at hp
    exact (totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hdeg)).trans hp
  rw [hker, finrank_bot]
theorem finrank_equations_le [Finite σ] (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Module.finrank k (equations I n) ≤ Module.finrank k (equations (boundaryIdeal I) n) := by
  have (J : Ideal (MvPolynomial σ k)) (d : ℕ) := equations_finite J d
  have step (d : ℕ) :=
    Submodule.finrank_mono (range_le I d)
  induction n with
  | zero =>
    have hI := (leadingMap I 0).finrank_range_add_finrank_ker
    have hB := (leadingMap (boundaryIdeal I) 0).finrank_range_add_finrank_ker
    rw [finrank_leading_ker_zero, add_zero] at hI hB
    exact hI ▸ hB ▸ step 0
  | succ n ih =>
    have hI := (leadingMap I (n + 1)).finrank_range_add_finrank_ker
    have hB := (leadingMap (boundaryIdeal I) (n + 1)).finrank_range_add_finrank_ker
    rw [finrank_leading_ker_succ] at hI hB
    exact hI ▸ hB ▸ Nat.add_le_add (step (n + 1)) ih
theorem hilbert_add_finrank_equations [Finite σ] (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    affineHilbertFunction I n + Module.finrank k (equations I n) =
      Module.finrank k (restrictTotalDegree σ k n) := by
  let f := (Ideal.Quotient.mkₐ k I).toLinearMap.domRestrict (restrictTotalDegree σ k n)
  have hker : LinearMap.ker f = (equations I n).comap (restrictTotalDegree σ k n).subtype := by
    ext p
    rw [LinearMap.mem_ker]
    change Ideal.Quotient.mk I (p : MvPolynomial σ k) = 0 ↔
      (p : MvPolynomial σ k) ∈ equations I n
    rw [Ideal.Quotient.eq_zero_iff_mem, Submodule.mem_inf]
    exact ⟨fun hp ↦ ⟨hp, p.property⟩, And.left⟩
  have hr : LinearMap.range f = quotientDegreeLE I n := LinearMap.range_domRestrict _ _
  have h := f.finrank_range_add_finrank_ker
  rw [hr, hker, (Submodule.comapSubtypeEquivOfLe inf_le_right).finrank_eq] at h
  exact h
theorem boundary_dimension_le [Finite σ] (I : Ideal (MvPolynomial σ k)) :
    dimension (boundaryIdeal I) ≤ dimension I := by
  apply natDegree_affineHilbertPolynomial_le_of_eventually_le_mul (m := 1) (c := 1) (by decide)
  apply Filter.Eventually.of_forall
  intro n
  simp only [one_mul]
  have hI := hilbert_add_finrank_equations I n
  have hB := hilbert_add_finrank_equations (boundaryIdeal I) n
  have hle := finrank_equations_le I n
  omega
end
end K1_13_6_3_5_4
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_5
noncomputable section
theorem local_residue_rank {R S : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (p : Ideal S) [p.IsPrime] (q : Ideal R) [q.IsPrime]
    (h : q = p.comap f) :
    letI := (Localization.localRingHom q p f h).toAlgebra
    letI : IsLocalHom (algebraMap (Localization.AtPrime q) (Localization.AtPrime p)) :=
      Localization.isLocalHom_localRingHom q p f h
    Module.finrank q.ResidueField p.ResidueField = degree f p := by
  subst q
  let q := p.comap f
  let _ : q.IsPrime := Ideal.IsPrime.comap f
  let _ := (Localization.localRingHom q p f rfl).toAlgebra
  let _ : IsLocalHom (algebraMap (Localization.AtPrime q) (Localization.AtPrime p)) :=
    Localization.isLocalHom_localRingHom q p f rfl
  change Module.finrank q.ResidueField p.ResidueField = degree f p
  rw [degree, dite_eq_left (show p.IsPrime from inferInstance)]
  let fq : (R ⧸ q) →+* (S ⧸ p) := Ideal.quotientMap p f le_rfl
  let ff : FractionRing (R ⧸ q) →+* FractionRing (S ⧸ p) :=
    IsFractionRing.map (Ideal.quotientMap_injective (I := p) (f := f))
  let _ := ff.toAlgebra
  let i := FractionRing.algEquiv (R ⧸ q) q.ResidueField
  let j := FractionRing.algEquiv (S ⧸ p) p.ResidueField
  have hcomm :
      (algebraMap q.ResidueField p.ResidueField).comp i.toRingHom = j.toRingHom.comp ff := by
    apply IsFractionRing.ringHom_ext (A := R ⧸ q)
    intro a
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hi : i (algebraMap (R ⧸ q) (FractionRing (R ⧸ q)) (Ideal.Quotient.mk q r)) =
        algebraMap R q.ResidueField r :=
      i.commutes _
    have hf : ff (algebraMap (R ⧸ q) (FractionRing (R ⧸ q)) (Ideal.Quotient.mk q r)) =
        algebraMap (S ⧸ p) (FractionRing (S ⧸ p)) (Ideal.Quotient.mk p (f r)) := by
      change IsLocalization.map _ fq _ _ = _
      rw [IsLocalization.map_eq]
      rfl
    change algebraMap q.ResidueField p.ResidueField
        (i (algebraMap (R ⧸ q) (FractionRing (R ⧸ q)) (Ideal.Quotient.mk q r))) =
      j (ff (algebraMap (R ⧸ q) (FractionRing (R ⧸ q)) (Ideal.Quotient.mk q r)))
    rw [hi, hf, j.commutes]
    change Ideal.ResidueField.map q p f rfl (algebraMap R q.ResidueField r) = _
    exact Ideal.ResidueField.map_algebraMap q p f rfl r
  change Module.finrank (q.ResidueField) (p.ResidueField) =
    Module.finrank (FractionRing (R ⧸ q)) (FractionRing (S ⧸ p))
  exact (congrArg Cardinal.toNat (Algebra.rank_eq_of_equiv_equiv
    i.toRingEquiv j.toRingEquiv hcomm)).symm
theorem branchLength_toNat {R S : Type} [CommRing R] [CommRing S] [IsNoetherianRing S]
    (f : R →+* S) (J : Ideal S) (q : Ideal R) [q.IsPrime]
    (p : fibrePrimes f J q) :
    (branchLength f J q p).toNat = weight J (p : Ideal S) * degree f (p : Ideal S) := by
  classical
  let hp := fibre_prime p
  let T := Localization.AtPrime (p : Ideal S)
  let L := Localization.AtPrime q
  let e := Localization.localRingHom q (p : Ideal S) f (fibre_comap p)
  let _ : Algebra L T := e.toAlgebra
  let _ : IsLocalHom (algebraMap L T) :=
    Localization.isLocalHom_localRingHom q (p : Ideal S) f (fibre_comap p)
  change (Module.length L (LocalSection J (p : Ideal S))).toNat = _
  rw [IsLocalRing.length_restrictScalars L T, ENat.toNat_mul, weight, dite_eq_left hp,
    Module.length_eq_rank, Cardinal.toNat_toENat]
  change (Module.length T (LocalSection J (p : Ideal S))).toNat *
    Module.finrank q.ResidueField (p : Ideal S).ResidueField = _
  exact congrArg ((Module.length T (LocalSection J (p : Ideal S))).toNat * ·)
    (local_residue_rank f (p : Ideal S) q (fibre_comap p))
end
end K1_13_6_3_5_5
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace K1_13_6_3_4_3
noncomputable section
open K1_13_6_3 K1_13_6_3_4 MvPolynomial
open Finset.HasAntidiagonal
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k]
private theorem decompose_apply (a : MvPolynomial σ k) (n : ℕ) :
    (DirectSum.decompose (homogeneousSubmodule σ k) a n : MvPolynomial σ k) =
      homogeneousComponent n a :=
  decomposition.decompose'_apply a n
private theorem component_mul (a b : MvPolynomial σ k) (n : ℕ) :
    homogeneousComponent n (a * b) = ∑ ij ∈ antidiagonal n,
      homogeneousComponent ij.1 a * homogeneousComponent ij.2 b := by
  let grades := homogeneousSubmodule σ k
  calc
    homogeneousComponent n (a * b) = (DirectSum.decompose grades (a * b) n : MvPolynomial σ k) :=
      (decompose_apply (a * b) n).symm
    _ = ∑ ij ∈ antidiagonal n,
          (DirectSum.decompose grades a ij.1 : MvPolynomial σ k) *
            (DirectSum.decompose grades b ij.2 : MvPolynomial σ k) := by
      rw [DirectSum.decompose_mul, DirectSum.coe_mul_apply_eq_sum_antidiagonal]
    _ = _ := by simp only [grades, decompose_apply]
theorem component_mul_of_homogeneous {a b : MvPolynomial σ k} {i j : ℕ}
    (ha : a.IsHomogeneous i) :
    homogeneousComponent (i + j) (a * b) = a * homogeneousComponent j b := by
  simpa only [decompose_apply, Nat.add_sub_cancel_left] using
    (DirectSum.coe_decompose_mul_of_left_mem_of_le
      (𝒜 := homogeneousSubmodule σ k) (b := b) ha (Nat.le_add_right i j))
private theorem lift_boundary_component (I : Ideal (MvPolynomial σ k))
    {q : MvPolynomial σ k} (hq : q ∈ boundaryIdeal I) :
    ∀ n, ∃ r ∈ I, r.totalDegree ≤ n ∧ homogeneousComponent n r = homogeneousComponent n q := by
  unfold boundaryIdeal at hq
  induction hq using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨p, m, hp, hdeg, rfl⟩ := hq
    intro n
    by_cases h : n = m
    · subst n
      exact ⟨p, hp, hdeg, (homogeneousComponent_eq_self
        (homogeneousComponent_isHomogeneous m p)).symm⟩
    · refine ⟨0, I.zero_mem, by simp, ?_⟩
      rw [map_zero, homogeneousComponent_of_mem (homogeneousComponent_mem m p), ite_eq_right h]
  | zero => exact fun n ↦ ⟨0, I.zero_mem, by simp, rfl⟩
  | add a b _ _ ha hb =>
    intro n
    obtain ⟨r, hr, hrd, hre⟩ := ha n
    obtain ⟨s, hs, hsd, hse⟩ := hb n
    exact ⟨r + s, I.add_mem hr hs, (totalDegree_add r s).trans (max_le hrd hsd),
      by rw [map_add, map_add, hre, hse]⟩
  | smul a b _ hb =>
    classical
    intro n
    choose r hrI hrDegree hrComponent using hb
    change ∃ p ∈ I, p.totalDegree ≤ n ∧
      homogeneousComponent n p = homogeneousComponent n (a * b)
    refine ⟨∑ ij ∈ antidiagonal n, homogeneousComponent ij.1 a * r ij.2,
      I.sum_mem (fun ij _ ↦ I.mul_mem_left _ (hrI ij.2)), ?_, ?_⟩
    · rw [← mem_restrictTotalDegree]
      apply Submodule.sum_mem
      intro ij hij
      rw [mem_restrictTotalDegree, ← mem_antidiagonal.mp hij]
      exact (totalDegree_mul _ _).trans (Nat.add_le_add
        (homogeneousComponent_isHomogeneous ij.1 a).totalDegree_le (hrDegree ij.2))
    · rw [map_sum, component_mul a b n]
      refine Finset.sum_congr rfl fun ij hij ↦ ?_
      rw [← mem_antidiagonal.mp hij,
        component_mul_of_homogeneous (homogeneousComponent_isHomogeneous ij.1 a), hrComponent]
theorem coordinate_power_mem [Finite σ] [IsAlgClosed k]
    {I : Ideal (MvPolynomial σ k)} {ℓ : MvPolynomial σ k} (h : NoBoundaryZero I ℓ) (i : σ) :
    ∃ e : ℕ, MvPolynomial.X i ^ e ∈ boundaryIdeal I ⊔ Ideal.span {ℓ} := by
  let J := boundaryIdeal I ⊔ Ideal.span {ℓ}
  have hx : MvPolynomial.X i ∈ vanishingIdeal k (zeroLocus k J) := by
    intro b hb
    have hbI := zeroLocus_anti_mono (show boundaryIdeal I ≤ J from le_sup_left) hb
    have hright : Ideal.span ({ℓ} : Set (MvPolynomial σ k)) ≤ J := le_sup_right
    have hbℓ : eval b ℓ = 0 := hb ℓ (hright (Ideal.subset_span (by simp)))
    simp only [aeval_X, h b hbI hbℓ, Pi.zero_apply]
  rw [vanishingIdeal_zeroLocus_eq_radical] at hx
  exact Ideal.mem_radical_iff.mp hx
theorem homogeneous_mem_of_coordinate_powers [Fintype σ]
    {J : Ideal (MvPolynomial σ k)} (e : σ → ℕ) (he : ∀ i, MvPolynomial.X i ^ e i ∈ J)
    {n : ℕ} (hn : (∑ i, e i) < n) {q : MvPolynomial σ k} (hq : q.IsHomogeneous n) : q ∈ J := by
  classical
  rw [← q.support_sum_monomial_coeff]
  apply J.sum_mem
  intro d hd
  have hdDegree : d.degree = n := by
    by_contra h
    exact (mem_support_iff.mp hd) (hq.coeff_eq_zero h)
  obtain ⟨i, hi⟩ : ∃ i, e i ≤ d i := by
    by_contra! h
    have hsum : (∑ i, d i) ≤ ∑ i, e i := Finset.sum_le_sum fun i _ ↦ (h i).le
    rw [← Finsupp.degree_eq_sum, hdDegree] at hsum
    exact (not_le_of_gt hn) hsum
  have hsingle : Finsupp.single i (e i) ≤ d := Finsupp.single_le_iff.mpr hi
  let d' := d - Finsupp.single i (e i)
  have hd' : d' + Finsupp.single i (e i) = d := tsub_add_cancel_of_le hsingle
  have hmon := J.mul_mem_left (monomial d' (q.coeff d)) (he i)
  rwa [MvPolynomial.X_pow_eq_monomial, monomial_mul_monomial, mul_one, hd'] at hmon
private theorem degree_le_of_component_zero {p : MvPolynomial σ k} {n : ℕ}
    (hp : p.totalDegree ≤ n + 1) (hzero : homogeneousComponent (n + 1) p = 0) :
    p.totalDegree ≤ n := by
  unfold totalDegree
  refine Finset.sup_le fun d hd ↦ ?_
  have hle : d.degree ≤ n + 1 := (le_totalDegree hd).trans hp
  have hne : d.degree ≠ n + 1 := by
    intro h
    have hcoeff := congrArg (fun q : MvPolynomial σ k ↦ q.coeff d) hzero
    change (homogeneousComponent (n + 1) p).coeff d = 0 at hcoeff
    exact (mem_support_iff.mp hd) (by simpa only [coeff_homogeneousComponent, ite_eq_left h] using hcoeff)
  change d.degree ≤ n
  omega
private theorem value_reduction [Fintype σ] [IsAlgClosed k]
    {I : Ideal (MvPolynomial σ k)} {ℓ : MvPolynomial σ k}
    (hℓ : ℓ.IsHomogeneous 1) (h : NoBoundaryZero I ℓ) : ValueReduction I ℓ := by
  classical
  choose e he using coordinate_power_mem h
  refine ⟨∑ i, e i, ?_⟩
  intro n hn z hz
  obtain ⟨p, hp, rfl⟩ := mem_quotientDegreeLE.mp hz
  have htop : homogeneousComponent (n + 1) p ∈ boundaryIdeal I ⊔ Ideal.span {ℓ} :=
    homogeneous_mem_of_coordinate_powers e he (Nat.lt_succ_of_le hn)
      (homogeneousComponent_isHomogeneous (n + 1) p)
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp htop
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hv
  obtain ⟨r, hrI, hrDegree, hr⟩ := lift_boundary_component I hu (n + 1)
  have hmul (f : MvPolynomial σ k) : homogeneousComponent (n + 1) (ℓ * f) =
      ℓ * homogeneousComponent n f := by
    rw [Nat.add_comm n 1, component_mul_of_homogeneous hℓ]
  have htop_eq : homogeneousComponent (n + 1) p =
      homogeneousComponent (n + 1) r + ℓ * homogeneousComponent n b := by
    have hcomp := congrArg (homogeneousComponent (n + 1)) huv
    simpa only [map_add, ← hr, hmul,
      homogeneousComponent_eq_self (homogeneousComponent_isHomogeneous (n + 1) p)] using hcomp.symm
  let b' := homogeneousComponent n b
  have hb' : b'.IsHomogeneous n := homogeneousComponent_isHomogeneous n b
  let a := p - (r + ℓ * b')
  have hab : (r + ℓ * b').totalDegree ≤ n + 1 :=
    (totalDegree_add _ _).trans (max_le hrDegree ((totalDegree_mul _ _).trans
      ((Nat.add_le_add hℓ.totalDegree_le hb'.totalDegree_le).trans_eq (Nat.add_comm 1 n))))
  have ha : a.totalDegree ≤ n := by
    apply degree_le_of_component_zero
    · rw [← mem_restrictTotalDegree] at hp hab ⊢
      exact (restrictTotalDegree σ k (n + 1)).sub_mem hp hab
    · simp only [a, b', map_sub, map_add, hmul, homogeneousComponent_eq_self hb',
        ← htop_eq, sub_self]
  refine ⟨Ideal.Quotient.mk I a, mk_mem_quotientDegreeLE ha,
    Ideal.Quotient.mk I b', mk_mem_quotientDegreeLE hb'.totalDegree_le, ?_⟩
  have hrzero : Ideal.Quotient.mk I r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hrI
  calc
    Ideal.Quotient.mk I p = Ideal.Quotient.mk I (a + (r + ℓ * b')) :=
      congrArg (Ideal.Quotient.mk I) (sub_add_cancel p (r + ℓ * b')).symm
    _ = _ := by rw [map_add, map_add, hrzero, zero_add, map_mul]
theorem proof : K1_13_6_3_4.c3 := by
  intro I h
  exact value_reduction (jetLinear_homogeneous genericArgument 0) h
end
end K1_13_6_3_4_3
end
section
set_option autoImplicit false
namespace K1_13_6_3_3_1
noncomputable section
open MvPolynomial
open scoped TensorProduct
variable {k L σ : Type*} [Field k] [Field L] [Algebra k L]
private abbrev baseIdeal (L : Type*) [Field L] [Algebra k L]
    (I : Ideal (MvPolynomial σ k)) : Ideal (MvPolynomial σ L) :=
  I.map (MvPolynomial.map (algebraMap k L))
private def baseQuot (I : Ideal (MvPolynomial σ k)) :
    L ⊗[k] (MvPolynomial σ k ⧸ I) ≃ₐ[L] MvPolynomial σ L ⧸ baseIdeal L I := by
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
private theorem baseQuot_tmul (I : Ideal (MvPolynomial σ k)) (a : L)
    (p : MvPolynomial σ k) :
    baseQuot I (a ⊗ₜ[k] Ideal.Quotient.mk I p) =
      a • Ideal.Quotient.mk (baseIdeal L I) (MvPolynomial.map (algebraMap k L) p) := by
  unfold baseQuot
  simp only [AlgEquiv.trans_apply, Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul,
    Ideal.quotientEquivAlg_mk, MvPolynomial.algebraTensorAlgEquiv_tmul]
  exact map_smul (Ideal.Quotient.mkₐ L (baseIdeal L I)) a _
theorem baseIdeal_comap (I : Ideal (MvPolynomial σ k)) :
    (baseIdeal L I).comap (MvPolynomial.map (algebraMap k L)) = I := by
  refine le_antisymm (fun p hp => ?_) Ideal.le_comap_map
  have hz : Ideal.Quotient.mk (baseIdeal L I) (MvPolynomial.map (algebraMap k L) p) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hp
  have he : baseQuot I ((1 : L) ⊗ₜ[k] Ideal.Quotient.mk I p) = baseQuot I 0 := by
    simp [baseQuot_tmul, hz]
  have hi := Algebra.TensorProduct.includeRight_injective
    (B := MvPolynomial σ k ⧸ I) (RingHom.injective (algebraMap k L))
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply hi
  change (1 : L) ⊗ₜ[k] Ideal.Quotient.mk I p = (1 : L) ⊗ₜ[k] 0
  rw [TensorProduct.tmul_zero]
  exact (baseQuot I).injective he
section Prime
variable [Finite σ] [IsAlgClosed k]
private def pointEval (I : Ideal (MvPolynomial σ k)) (x : σ → k)
    (hx : x ∈ zeroLocus k I) : (MvPolynomial σ k ⧸ I) →ₐ[k] k :=
  Ideal.Quotient.liftₐ I (aeval x) (mem_zeroLocus_iff.mp hx)
theorem exists_point (I : Ideal (MvPolynomial σ k)) (hI : I.IsPrime)
    (u v : MvPolynomial σ k ⧸ I) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ x : σ → k, ∃ hx : x ∈ zeroLocus k I,
      pointEval I x hx u ≠ 0 ∧ pointEval I x hx v ≠ 0 := by
  classical
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective v
  have hpq : p * q ∉ I := fun h => (hI.mem_or_mem h).elim
    (fun hp => hu (Ideal.Quotient.eq_zero_iff_mem.mpr hp))
    (fun hq => hv (Ideal.Quotient.eq_zero_iff_mem.mpr hq))
  have hvan : vanishingIdeal k (zeroLocus k I) = I := by
    rw [vanishingIdeal_zeroLocus_eq_radical, hI.radical]
  have hx : ∃ x ∈ zeroLocus k I, aeval x (p * q) ≠ 0 := by
    by_contra! h
    exact hpq (hvan ▸ mem_vanishingIdeal_iff.mpr h)
  obtain ⟨x, hx, h⟩ := hx
  rw [map_mul, mul_ne_zero_iff] at h
  exact ⟨x, hx, h⟩
theorem tensor_mul_ne_zero (I : Ideal (MvPolynomial σ k)) (hI : I.IsPrime)
    {a b : L ⊗[k] (MvPolynomial σ k ⧸ I)} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b ≠ 0 := by
  classical
  let B := Module.Free.chooseBasis k L
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := MvPolynomial σ k ⧸ I) B
  have nonzero_coord (w : L ⊗[k] (MvPolynomial σ k ⧸ I)) (hw : w ≠ 0) :
      ∃ i, e w i ≠ 0 := by
    by_contra! h
    exact hw (e.injective (by simpa only [map_zero] using Finsupp.ext h))
  obtain ⟨i, hi⟩ := nonzero_coord a ha
  obtain ⟨j, hj⟩ := nonzero_coord b hb
  obtain ⟨x, hx, ha', hb'⟩ := exists_point I hI (e a i) (e b j) hi hj
  let f := pointEval I x hx
  let m := Algebra.TensorProduct.map (AlgHom.id k L) f
  let d := TensorProduct.equivFinsuppOfBasisLeft (N := k) B
  have coord (w : L ⊗[k] (MvPolynomial σ k ⧸ I)) (l : Module.Free.ChooseBasisIndex k L) :
      d (m w) l = f (e w l) := by
    induction w using TensorProduct.inductionOn with
    | tmul c u =>
      simp [d, e, m, map_smul]
    | add y z hy hz => simp [hy, hz]
  have nonzero_image (w : L ⊗[k] (MvPolynomial σ k ⧸ I))
      (l : Module.Free.ChooseBasisIndex k L) (hw : f (e w l) ≠ 0) : m w ≠ 0 := by
    intro h
    exact hw (by rw [← coord, h]; simp)
  let r := Algebra.TensorProduct.rid (R := k) (S := k) (A := L)
  intro hab
  have h := congrArg (fun w => r (m w)) hab
  have hprod : r (m a) * r (m b) = 0 := by simpa only [map_mul, map_zero] using h
  exact (mul_ne_zero (fun h => nonzero_image a i ha' (r.injective (h.trans r.map_zero.symm)))
    (fun h => nonzero_image b j hb' (r.injective (h.trans r.map_zero.symm)))) hprod
theorem baseIdeal_prime (I : Ideal (MvPolynomial σ k)) (hI : I.IsPrime) :
    (baseIdeal L I).IsPrime := by
  refine ⟨fun h => hI.ne_top ((baseIdeal_comap (L := L) I).symm.trans (by rw [h, Ideal.comap_top])),
    fun {p q} hpq => ?_⟩
  by_contra! h
  let e := (baseQuot (L := L) I).symm
  let a := e (Ideal.Quotient.mk (baseIdeal L I) p)
  let b := e (Ideal.Quotient.mk (baseIdeal L I) q)
  have ha : a ≠ 0 := fun hz =>
    h.1 (Ideal.Quotient.eq_zero_iff_mem.mp (e.injective (hz.trans e.map_zero.symm)))
  have hb : b ≠ 0 := fun hz =>
    h.2 (Ideal.Quotient.eq_zero_iff_mem.mp (e.injective (hz.trans e.map_zero.symm)))
  apply tensor_mul_ne_zero I hI ha hb
  rw [← map_mul e, ← map_mul (Ideal.Quotient.mk (baseIdeal L I)),
    Ideal.Quotient.eq_zero_iff_mem.mpr hpq, map_zero]
end Prime
section Hilbert
variable [Finite σ]
theorem baseIdeal_hilbertFunction (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    affineHilbertFunction (baseIdeal L I) n = affineHilbertFunction I n := by
  classical
  let W := quotientDegreeLE I n
  let V := quotientDegreeLE (baseIdeal L I) n
  let f : L ⊗[k] W →ₗ[L] MvPolynomial σ L ⧸ baseIdeal L I :=
    (baseQuot I).toLinearEquiv.toLinearMap.comp
      (TensorProduct.AlgebraTensorModule.lTensor L L W.subtype)
  have hcalc (a : L) (z : W) : f (a ⊗ₜ[k] z) = baseQuot I (a ⊗ₜ[k] z.val) := rfl
  have hinj : Function.Injective f := (baseQuot I).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap W.subtype Subtype.val_injective)
  have hrange : LinearMap.range f = V := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      induction z using TensorProduct.inductionOn with
      | tmul a z =>
        obtain ⟨p, hp, he⟩ := mem_quotientDegreeLE.mp z.property
        rw [hcalc, ← he, baseQuot_tmul]
        apply V.smul_mem
        apply mk_mem_quotientDegreeLE
        exact (Finset.sup_mono (support_map_subset (algebraMap k L) p)).trans hp
      | add y z hy hz => simpa only [map_add] using V.add_mem hy hz
    · intro y hy
      obtain ⟨p, hp, rfl⟩ := mem_quotientDegreeLE.mp hy
      nth_rw 1 [p.as_sum]
      rw [map_sum]
      apply Submodule.sum_mem
      intro m hm
      have hdeg := (le_totalDegree hm).trans hp
      let z : W := ⟨Ideal.Quotient.mk I (monomial m 1),
        mk_mem_quotientDegreeLE ((totalDegree_monomial_le m (1 : k)).trans hdeg)⟩
      refine ⟨p.coeff m ⊗ₜ[k] z, ?_⟩
      rw [hcalc, show z.val = Ideal.Quotient.mk I (monomial m 1) from rfl, baseQuot_tmul]
      rw [MvPolynomial.map_monomial, map_one]
      change p.coeff m • Ideal.Quotient.mkₐ L (baseIdeal L I) (monomial m 1) =
        Ideal.Quotient.mkₐ L (baseIdeal L I) (monomial m (p.coeff m))
      rw [← map_smul, smul_monomial, smul_eq_mul, mul_one]
  let e := (LinearEquiv.ofInjective f hinj).trans (LinearEquiv.ofEq _ _ hrange)
  let B := Module.Free.chooseBasis k W
  change Module.finrank L V = Module.finrank k W
  rw [Module.finrank_eq_nat_card_basis ((B.baseChange L).map e), Module.finrank_eq_nat_card_basis B]
theorem baseIdeal_hilbertPolynomial (I : Ideal (MvPolynomial σ k)) :
    affineHilbertPolynomial (baseIdeal L I) = affineHilbertPolynomial I := by
  obtain ⟨n₀, hn₀⟩ := exists_eval_affineHilbertPolynomial I
  refine (eq_affineHilbertPolynomial_of_eval_eq (N₀ := n₀) fun n hn => ?_).symm
  rw [hn₀ n hn, baseIdeal_hilbertFunction]
end Hilbert
open K1_13 K1_13_6 K1_13_6_3
theorem proof : K1_13_6_3_3.c1 := by
  intro A hA
  let : Algebra Geom GeoField := geomConstants.toAlgebra
  exact ⟨baseIdeal_prime A hA, congrArg Polynomial.natDegree (baseIdeal_hilbertPolynomial A),
    baseIdeal_comap A⟩
end
end K1_13_6_3_3_1
end
section
set_option autoImplicit false
set_option linter.style.haveILetI false
namespace K1_13_5_4_2_2_1
noncomputable section
open K1_13_5_4_2_2 K1_13_5_4_4_2 K1_13_6_3_4 MvPolynomial
variable {k σ : Type} [Field k] [Finite σ]
theorem linearForm_homogeneous (a : σ → k) : (linearForm a).IsHomogeneous 1 := by
  classical
  unfold linearForm
  exact (homogeneousSubmodule σ k 1).sum_mem fun i _ => isHomogeneous_C_mul_X (a i) i
def pairing (z : σ → k) : (σ → k) →ₗ[k] k := by
  classical
  letI := Fintype.ofFinite σ
  exact ∑ i, z i • LinearMap.proj i
theorem pairing_eval (z a : σ → k) : pairing z a = eval z (linearForm a) := by
  classical
  simp [pairing, linearForm, mul_comm]
theorem pairing_ker_ne_top (z : σ → k) {i : σ} (hi : z i ≠ 0) :
    LinearMap.ker (pairing z) ≠ ⊤ := by
  classical
  letI := Fintype.ofFinite σ
  intro h
  have hz : pairing z (Pi.single i 1) = 0 := LinearMap.mem_ker.mp (h ▸ Submodule.mem_top)
  have hs : pairing z (Pi.single i 1) = z i := by
    simp only [pairing, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  exact hi (hs.symm.trans hz)
private theorem eval_scale (x : σ → k) (c : k)
    {p : MvPolynomial σ k} {n : ℕ} (hp : p.IsHomogeneous n) :
    eval (fun i => c * x i) p = c ^ n * eval x p := by
  classical
  letI := Fintype.ofFinite σ
  change eval₂ (RingHom.id k) (fun i => c * x i) p = c ^ n * eval₂ (RingHom.id k) x p
  rw [eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = n := by
    by_contra h
    exact (mem_support_iff.mp hd) (hp.coeff_eq_zero h)
  rw [show (∏ i : σ, (c * x i) ^ d i) = c ^ n * ∏ i : σ, x i ^ d i by
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      ← Finsupp.degree_eq_sum, hdeg]]
  ring
private theorem normalize_boundary (I : Ideal (MvPolynomial σ k))
    {x : σ → k} (hx : x ∈ zeroLocus k (boundaryIdeal I)) {i : σ} (hi : x i ≠ 0) :
    (fun j => (x i)⁻¹ * x j) ∈ zeroLocus k (boundaryChart I i) := by
  let y : σ → k := fun j => (x i)⁻¹ * x j
  change boundaryChart I i ≤ RingHom.ker (eval y)
  apply sup_le
  · apply Ideal.span_le.mpr
    rintro _ ⟨p, n, hp, hn, rfl⟩
    apply RingHom.mem_ker.mpr
    change eval (fun j => (x i)⁻¹ * x j) (homogeneousComponent n p) = 0
    rw [eval_scale x (x i)⁻¹ (homogeneousComponent_isHomogeneous n p)]
    have hz : eval x (homogeneousComponent n p) = 0 :=
      hx _ (Ideal.subset_span ⟨p, n, hp, hn, rfl⟩)
    rw [hz, mul_zero]
  · apply Ideal.span_le.mpr
    rintro _ (rfl : _ = MvPolynomial.X i - 1)
    apply RingHom.mem_ker.mpr
    rw [map_sub, eval_X, map_one]
    exact sub_eq_zero.mpr (inv_mul_cancel₀ hi)
omit [Finite σ] in
theorem boundary_chart_coordinate (I : Ideal (MvPolynomial σ k)) {i : σ}
    (z : zeroLocus k (boundaryChart I i)) : z.val i = 1 := by
  have h : eval z.val (MvPolynomial.X i - 1) = 0 :=
    z.property _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  exact sub_eq_zero.mp (by simpa using h)
theorem exists_boundary_exclusions [IsAlgClosed k] (I : Ideal (MvPolynomial σ k))
    (hI : (affineHilbertPolynomial I).natDegree = 1) :
    ∃ bad : Finset (Submodule k (σ → k)), (∀ B ∈ bad, B ≠ ⊤) ∧
      ∀ a : σ → k, (∀ B ∈ bad, a ∉ B) → NoBoundaryZero I (linearForm a) := by
  classical
  letI := Fintype.ofFinite σ
  let e := Fintype.equivFin σ
  letI : LinearOrder σ := LinearOrder.lift' e e.injective
  letI : WellFoundedGT σ := Finite.to_wellFoundedGT
  let P (i : σ) := zeroLocus k (boundaryChart I i)
  letI (i : σ) : Fintype (P i) :=
    ((finite_zeroLocus_iff_natDegree_affineHilbertPolynomial_eq_zero _).mpr
      (boundaryChart_dimension I hI i)).fintype
  let obstruction (p : Σ i, P i) := LinearMap.ker (pairing p.2.val)
  refine ⟨Finset.univ.image obstruction, ?_, ?_⟩
  · intro B hB
    obtain ⟨⟨i, z⟩, _, rfl⟩ := Finset.mem_image.mp hB
    apply pairing_ker_ne_top z.val (i := i)
    rw [boundary_chart_coordinate I z]
    exact one_ne_zero
  · intro a ha x hx hz
    funext i
    change x i = 0
    by_contra hi
    let z : P i := ⟨_, normalize_boundary I hx hi⟩
    apply ha (obstruction ⟨i, z⟩) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    change pairing z.val a = 0
    rw [pairing_eval]
    change eval (fun j => (x i)⁻¹ * x j) (linearForm a) = 0
    rw [eval_scale x (x i)⁻¹ (linearForm_homogeneous a), hz, mul_zero]
end
end K1_13_5_4_2_2_1
end
section
set_option autoImplicit false
namespace K1_13_6_3_5_5
noncomputable section
open K1_13_6_3_5
def c1 : Prop :=
  ∀ (k σ τ : Type) [Field k] [Finite σ] [Finite τ]
    (φ : MvPolynomial τ k →ₐ[k] MvPolynomial σ k), IsLinearProjection φ →
    ∀ A : Ideal (MvPolynomial σ k), A.IsPrime → IsBirationalOn φ A →
      Nonempty (ConeModel φ A)
def c2 : Prop :=
  ∀ (U V R S : Type) [CommRing U] [CommRing V] [CommRing R] [CommRing S]
    [IsNoetherianRing V] [IsNoetherianRing S]
    (g : U →+* V) (f : R →+* S) (J : Ideal U) (I : Ideal V) (w : R)
    (r : SectionPresentation J w) (s : SectionPresentation I (f w)),
    Compatible g f r s →
    ∀ Q : Ideal U, J.IsMinimalPrime Q →
      ∃ q : Ideal R, (Ideal.span {w}).IsMinimalPrime q ∧
        weight J Q = weight (Ideal.span {w}) q ∧
        fibreWeight g I Q = fibreWeight f (Ideal.span {f w}) q
def c3 : Prop :=
  ∀ (L : Type) [CommRing L] [IsDomain L] [IsNoetherianRing L] [IsLocalRing L]
    [Ring.KrullDimLE 1 L] (x : L), x ≠ 0 →
    ∀ (B : FractionSubalgebra L) (s : Finset (SectionQuotient x B)),
      Module.length L (Submodule.span L (s : Set (SectionQuotient x B))) ≤ Ring.ord L x
def c4 : Prop :=
  ∀ (R S F : Type) [CommRing R] [IsDomain R] [CommRing S] [IsNoetherianRing S]
    [Field F] [Algebra R F] [IsFractionRing R F]
    (f : R →+* S) (e : S →+* F), Function.Injective e →
    e.comp f = algebraMap R F →
    ∀ (w : R) (q : Ideal R) [q.IsPrime],
      ∃ B : FractionSubalgebra (Localization.AtPrime q),
        (∑ p : fibrePrimes f (Ideal.span {f w}) q, branchLength f (Ideal.span {f w}) q p) ≤
          sectionLength (algebraMap R (Localization.AtPrime q) w) B
theorem length_le_of_finite_spans {L M : Type} [Ring L] [AddCommGroup M] [Module L M]
    (n : ℕ∞) (h : ∀ s : Finset M, Module.length L (Submodule.span L (s : Set M)) ≤ n) :
    Module.length L M ≤ n := by
  classical
  rw [← WithBot.coe_le_coe, Module.coe_length, Order.krullDim, iSup_le_iff]
  intro t
  have hstep (i : Fin t.length) : ∃ z ∈ t i.succ, z ∉ t i.castSucc :=
    Set.not_subset.mp (t.step i).not_ge
  choose z hz hnot using hstep
  let s := Finset.univ.image z
  let N := Submodule.span L (s : Set M)
  let u : LTSeries (Submodule L N) :=
    { length := t.length
      toFun := fun i => (t i).comap N.subtype
      step := fun i => by
        refine lt_of_le_of_ne (Submodule.comap_mono (t.step i).le) ?_
        intro he
        let a : N := ⟨z i, Submodule.subset_span (Finset.mem_image_of_mem z (Finset.mem_univ i))⟩
        have ha : a ∈ (t i.succ).comap N.subtype := hz i
        exact hnot i (show a ∈ (t i.castSucc).comap N.subtype from he.symm ▸ ha) }
  calc
    _ = (u.length : WithBot ℕ∞) := rfl
    _ ≤ Order.krullDim (Submodule L N) := Order.LTSeries.length_le_krullDim u
    _ = (Module.length L N : WithBot ℕ∞) := (Module.coe_length L N).symm
    _ ≤ _ := WithBot.coe_le_coe.mpr (h s)
theorem principal_fibre_bound (h3 : c3) (h4 : c4)
    {R S F : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [IsNoetherianRing S] [Field F] [Algebra R F] [IsFractionRing R F]
    (f : R →+* S) (e : S →+* F) (he : Function.Injective e)
    (hcomp : e.comp f = algebraMap R F)
    (w : R) (hw : w ≠ 0) (q : Ideal R) (hq : (Ideal.span {w}).IsMinimalPrime q) :
    fibreWeight f (Ideal.span {f w}) q ≤ weight (Ideal.span {w}) q := by
  classical
  let _ := hq.isPrime
  let L := Localization.AtPrime q
  let x := algebraMap R L w
  have hx : x ≠ 0 := by
    simpa only [x, map_zero] using (IsLocalization.injective L q.primeCompl_le_nonZeroDivisors).ne hw
  have hdim : Ring.KrullDimLE 1 L := by
    constructor
    change ringKrullDim L ≤ (1 : ℕ)
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q L]
    exact WithBot.coe_le_coe.mpr
      (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq)
  let _ := hdim
  have hfinite : Ring.ord L x ≠ ⊤ := Ring.ord_ne_top (mem_nonZeroDivisors_iff_ne_zero.mpr hx)
  obtain ⟨B, hB⟩ := h4 R S F f e he hcomp w q
  let I : Ideal S := Ideal.span {f w}
  have hsum : (∑ p : fibrePrimes f I q, branchLength f I q p) ≤ Ring.ord L x :=
    hB.trans (length_le_of_finite_spans _ (h3 L x hx B))
  have hsumFinite : (∑ p : fibrePrimes f I q, branchLength f I q p) ≠ ⊤ :=
    (lt_of_le_of_lt hsum hfinite.lt_top).ne
  have hnat := ENat.toNat_le_toNat hsum hfinite
  rw [ENat.toNat_sum (ENat.sum_ne_top.mp hsumFinite)] at hnat
  have hweight : (Ring.ord L x).toNat = weight (Ideal.span {w}) q := by
    rw [weight, dite_eq_left hq.isPrime]
    change _ = (Module.length L (L ⧸ (Ideal.span {w}).map (algebraMap R L))).toNat
    have hmap : (Ideal.span {w}).map (algebraMap R L) = Ideal.span {x} := by
      rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun J : Ideal L => (Module.length L (L ⧸ J)).toNat) hmap.symm
  rw [hweight] at hnat
  change fibreWeight f I q ≤ _
  unfold fibreWeight
  rw [← Finset.sum_coe_sort]
  simpa only [branchLength_toNat f I q] using hnat
theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) (h4 : c4) :
    K1_13_6_3_5.c5 := by
  classical
  intro k σ τ _ _ _ φ hφ A hA hbir Q hQ
  obtain ⟨M⟩ := h1 k σ τ φ hφ A hA hbir
  let _ := M.field
  let _ := M.algebra
  let _ := M.targetNoetherian
  let _ := M.sourceNoetherian
  let _ := M.fraction
  let f := (Subalgebra.inclusion M.le).toRingHom
  let e := M.source.val.toRingHom
  obtain ⟨q, hq, hweight, hsum⟩ :=
    h2 _ _ M.target M.source φ.toRingHom f _ _ M.w
      M.targetSection M.sourceSection M.compatible Q hQ
  change fibreWeight φ.toRingHom (boundaryIdeal A) Q ≤
    weight (boundaryIdeal (A.comap φ)) Q
  rw [hsum, hweight]
  exact principal_fibre_bound h3 h4 f e Subtype.val_injective rfl M.w M.w_ne q hq
end
end K1_13_6_3_5_5
end
section
namespace K1_8
noncomputable section
open Polynomial K1
structure AmplitudeDirection (U V : Bivar) where
  α : Fin 2 → K[X]
  β : Fin 2 → K[X]
  a : K[X]
  b : K[X]
  a_ne : a ≠ 0
  b_ne : b ≠ 0
  scalar_coprime : IsCoprime a b
  α_primitive : IsCoprime (α 0) (α 1)
  β_primitive : IsCoprime (β 0) (β 1)
  direction : sameDirection U V (threeU a β) (threeV b α)
end
end K1_8
end
