import ProximityPrize.SubmissionLower.Fast062
import ProximityPrize.SubmissionLower.Fast063
import ProximityPrize.SubmissionLower.Fast064
set_option Elab.async false
set_option autoImplicit true
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2500
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
namespace K1_14_2_4_1_3_3_2
noncomputable section
open K1_14 K1_14_2 K1_14_2_4_1 K1_14_2_4_1_1 K1_14_2_4_1_2 K1_14_2_4_1_3_3
open scoped Polynomial
private abbrev FibrePoly := MvPolynomial (Fin 3) SeedField
private abbrev baseChange : RootAmbient →+* FibrePoly :=
  MvPolynomial.map (algebraMap FX SeedField)
private abbrev fibreIdeal (J : Ideal RootAmbient) : Ideal FibrePoly :=
  J.map baseChange ⊔ Ideal.span {ySection 2}
private def ambientInFibre (J : Ideal RootAmbient) : RootAmbient →+* RootYSection J :=
  (Ideal.Quotient.mk (fibreIdeal J)).comp baseChange
private theorem ambientInFibre_ordinate (J : Ideal RootAmbient) :
    ambientInFibre J (MvPolynomial.X 2) = algebraMap SeedField (RootYSection J)
      (K1_14_2.generic 1) := by
  change Ideal.Quotient.mk (fibreIdeal J) (baseChange (MvPolynomial.X 2)) =
    Ideal.Quotient.mk (fibreIdeal J) (MvPolynomial.C (K1_14_2.generic 1))
  rw [MvPolynomial.map_X, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact (le_sup_right : Ideal.span {ySection 2} ≤ fibreIdeal J)
    (Ideal.mem_span_singleton_self (ySection 2))
attribute [local instance] MvPolynomial.algebraMvPolynomial in
private theorem clear_fibre_denominators (J : Ideal RootAmbient)
    (d : RootAmbient ⧸ J →+* RootYSection J)
    (hd : d.comp (Ideal.Quotient.mk J) = ambientInFibre J)
    (q : RootYSection J) :
    ∃ u : RootYSection J, IsUnit u ∧ ∃ p : (Polynomial (RootAmbient ⧸ J)),
      q * u = Polynomial.eval₂RingHom d
        (algebraMap SeedField (RootYSection J) (K1_14_2.generic 0)) p := by
  let D := RootAmbient ⧸ J
  let Q := RootYSection J
  let : CommRing D := Ideal.Quotient.commRing J
  let : CommRing (Polynomial D) := AddMonoidAlgebra.commRing
  let mkQ := Ideal.Quotient.mk (fibreIdeal J)
  let s : Seeds →+* (Polynomial D) := MvPolynomial.eval₂Hom
    (Polynomial.C.comp ((Ideal.Quotient.mk J).comp MvPolynomial.C))
    ![Polynomial.X, Polynomial.C (Ideal.Quotient.mk J (MvPolynomial.X 2))]
  let subst : MvPolynomial (Fin 3) Seeds →+* (Polynomial D) := MvPolynomial.eval₂Hom s
    (fun i => Polynomial.C (Ideal.Quotient.mk J (MvPolynomial.X i)))
  let ev : (Polynomial D) →+* Q := Polynomial.eval₂RingHom d
    (algebraMap SeedField Q (K1_14_2.generic 0))
  have hs : ev.comp s = (algebraMap SeedField Q).comp (algebraMap Seeds SeedField) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [s, RingHom.comp_apply, MvPolynomial.eval₂Hom_C, ev, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C]
      calc
        _ = ambientInFibre J (MvPolynomial.C a) := DFunLike.congr_fun hd (MvPolynomial.C a)
        _ = _ := by
          change mkQ (baseChange (MvPolynomial.C a)) =
            mkQ (MvPolynomial.C (algebraMap FX SeedField a))
          rw [MvPolynomial.map_C]
    · intro i
      simp only [s, RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      fin_cases i
      · change ev Polynomial.X = algebraMap SeedField Q (K1_14_2.generic 0)
        simp [ev]
      · change ev (Polynomial.C (Ideal.Quotient.mk J (MvPolynomial.X 2))) =
          algebraMap SeedField Q (K1_14_2.generic 1)
        simp only [ev, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
        exact (DFunLike.congr_fun hd _).trans (ambientInFibre_ordinate J)
  have hsubst : ev.comp subst = mkQ.comp (algebraMap (MvPolynomial (Fin 3) Seeds) FibrePoly) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change ev (MvPolynomial.eval₂Hom s _ (MvPolynomial.C a)) =
        mkQ (MvPolynomial.map (algebraMap Seeds SeedField) (MvPolynomial.C a))
      rw [MvPolynomial.eval₂Hom_C, MvPolynomial.map_C]
      exact DFunLike.congr_fun hs a
    · intro i
      change ev (MvPolynomial.eval₂Hom s _ (MvPolynomial.X i)) =
        mkQ (MvPolynomial.map (algebraMap Seeds SeedField) (MvPolynomial.X i))
      rw [MvPolynomial.eval₂Hom_X', MvPolynomial.map_X]
      change Polynomial.eval₂ d _ (Polynomial.C (Ideal.Quotient.mk J (MvPolynomial.X i))) =
        mkQ (MvPolynomial.X i)
      rw [Polynomial.eval₂_C]
      calc
        _ = ambientInFibre J (MvPolynomial.X i) := DFunLike.congr_fun hd _
        _ = _ := by
          change mkQ (baseChange (MvPolynomial.X i)) = mkQ (MvPolynomial.X i)
          rw [MvPolynomial.map_X]
  let M : Submonoid (MvPolynomial (Fin 3) Seeds) := (nonZeroDivisors Seeds).map MvPolynomial.C
  let : IsLocalization M FibrePoly := MvPolynomial.isLocalization (nonZeroDivisors Seeds) SeedField
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := fibreIdeal J) q
  obtain ⟨⟨p, u⟩, hp⟩ := IsLocalization.surj M a
  refine ⟨mkQ (algebraMap (MvPolynomial (Fin 3) Seeds) FibrePoly u),
    (IsLocalization.map_units FibrePoly u).map mkQ,
    subst p, ?_⟩
  change mkQ a * mkQ (algebraMap (MvPolynomial (Fin 3) Seeds) FibrePoly u) = ev (subst p)
  rw [← map_mul, hp]
  exact (DFunLike.congr_fun hsubst p).symm
private theorem fraction_mem {A F G : Type} [CommRing A] [Field F] [Field G]
    [Algebra A F] [IsFractionRing A F] (S : Subfield G) (f : F →+* G)
    (h : ∀ a : A, f (algebraMap A F a) ∈ S) (z : F) : f z ∈ S := by
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective A z
  rw [map_div₀]
  exact S.div_mem (h a) (h b)
private theorem polynomial_mem {A F : Type} [CommRing A] [Field F]
    (S : Subfield F) (f : (Polynomial A) →+* F)
    (hC : ∀ a, f (Polynomial.C a) ∈ S) (hX : f Polynomial.X ∈ S)
    (p : (Polynomial A)) : f p ∈ S := by
  refine Polynomial.induction_on p hC (fun p q hp hq => ?_) (fun n a ha => ?_)
  · rw [map_add]
    exact S.add_mem hp hq
  · rw [pow_succ, ← mul_assoc, map_mul]
    exact S.mul_mem ha hX
variable {C₀ : ConstantSeeds} [Fact (Irreducible C₀)] {J : Ideal RootAmbient} {g : ℕ}
private abbrev rootMap (R : PrimitiveRoot C₀ J g) := K1_14_2_4_1_2.generic R
private theorem rootMap_base (R : PrimitiveRoot C₀ J g) (a : FX) :
    rootMap R (MvPolynomial.C a) = rootBase R a := by
  simp only [K1_14_2_4_1_2.generic, RingHom.comp_apply, genericRootMap, MvPolynomial.eval₂Hom_C]
  rfl
private theorem rootMap_ordinate (R : PrimitiveRoot C₀ J g) :
    rootMap R (MvPolynomial.X 2) = rootOrdinate R := by
  simp only [K1_14_2_4_1_2.generic, RingHom.comp_apply, genericRootMap, MvPolynomial.eval₂Hom_X']
  rfl
private theorem rootMap_kernel (R : PrimitiveRoot C₀ J g) :
    RingHom.ker (rootMap R) = J := by
  ext p
  rw [RingHom.mem_ker]
  change AdjoinRoot.mk (rootEquation R) (genericRootMap C₀ p) = 0 ↔ p ∈ J
  have h : p ∈ J ↔ genericRootMap C₀ p ∈ Ideal.span {rootEquation R} :=
    Iff.of_eq (congrArg (fun I : Ideal RootAmbient => p ∈ I) R.contraction)
  exact (AdjoinRoot.mk_eq_zero.trans Ideal.mem_span_singleton.symm).trans h.symm
private theorem spare_mem (R : PrimitiveRoot C₀ J g)
    (S : Subfield (SpareField (RootField R)))
    (hroot : ∀ p : RootAmbient, spareConstant (RootField R) (rootMap R p) ∈ S)
    (hspare : spareVariable (RootField R) ∈ S)
    (z : SpareField (RootField R)) : z ∈ S := by
  let E := RootField R
  let F := ConstantSeedX C₀
  let : Field E := inferInstanceAs (Field (RootField R))
  let : Field F := inferInstanceAs (Field (ConstantSeedX C₀))
  let k := spareConstant E
  let kF : F →+* SpareField E := k.comp (AdjoinRoot.of (rootEquation R))
  have hC := K1_14_2_4_1_1_1.proof C₀
  let : Algebra (Seeds ⧸ seedEquation C₀) F := (seedCurveMap C₀ hC.kernel).toAlgebra
  let : IsFractionRing (Seeds ⧸ seedEquation C₀) F := hC.localized
  have hseed (a : F) : kF a ∈ S := by
    refine fraction_mem (A := Seeds ⧸ seedEquation C₀) S kF ?_ a
    intro q
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    have heq : genericRootMap C₀ (rootSeeds p) = Polynomial.C (genericSeedMap C₀ p) := by
      have h := DFunLike.congr_fun rootView_seed p
      change rootView (rootSeeds p) = Polynomial.C p at h
      rw [genericRootMap_eq, RingHom.comp_apply]
      change (rootView (rootSeeds p)).map (genericSeedMap C₀) = _
      rw [h, Polynomial.map_C]
    change spareConstant (RootField R)
      ((AdjoinRoot.mk (rootEquation R)) (Polynomial.C (genericSeedMap C₀ p))) ∈ S
    have hp := hroot (rootSeeds p)
    simpa only [K1_14_2_4_1_2.generic, RingHom.comp_apply, heq] using hp
  have hconstants (a : E) : k a ∈ S := by
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective (g := rootEquation R) a
    change (k.comp (AdjoinRoot.mk (rootEquation R))) p ∈ S
    apply polynomial_mem S
    · exact hseed
    · change k (rootOrdinate R) ∈ S
      simpa only [rootMap_ordinate] using hroot (MvPolynomial.X 2)
  change (RingHom.id (SpareField E)) z ∈ S
  refine fraction_mem (A := (Polynomial E)) S (RingHom.id _) ?_ z
  intro p
  exact polynomial_mem S (algebraMap (Polynomial E) (SpareField E)) hconstants hspare p
private theorem fibre_embedding {E : Type} [Field E] (J : Ideal RootAmbient)
    (ρ : RootAmbient →+* E) (hker : RingHom.ker ρ = J)
    (b : SeedField →+* SpareField E)
    (hb : IsOrdinateMap (ρ.comp MvPolynomial.C) (ρ (MvPolynomial.X 2)) b) :
    ∃ f : RootYSection J →+* SpareField E, Function.Injective f ∧
      f.comp (algebraMap SeedField (RootYSection J)) = b ∧
      f.comp (ambientInFibre J) = (spareConstant E).comp ρ := by
  let Q := RootYSection J
  let k := spareConstant E
  let ev : FibrePoly →+* SpareField E :=
    MvPolynomial.eval₂Hom b (fun i => k (ρ (MvPolynomial.X i)))
  have hev : ev.comp baseChange = k.comp ρ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simpa only [RingHom.comp_apply, MvPolynomial.map_C, ev, MvPolynomial.eval₂Hom_C,
        k] using hb.1 a
    · intro i
      change MvPolynomial.eval₂Hom b (fun i => k (ρ (MvPolynomial.X i)))
        (baseChange (MvPolynomial.X i)) = k (ρ (MvPolynomial.X i))
      rw [MvPolynomial.map_X, MvPolynomial.eval₂Hom_X']
  have hkill : fibreIdeal J ≤ RingHom.ker ev := by
    apply sup_le
    · rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker, hev,
        RingHom.ker_comp_of_injective _ k.injective, hker]
    · apply Ideal.span_le.mpr
      rintro p ⟨rfl⟩
      change ev (ySection 2) = 0
      simp only [ySection, map_sub, ev, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C]
      exact sub_eq_zero.mpr hb.2.1.symm
  let f : Q →+* SpareField E := Ideal.Quotient.lift (fibreIdeal J) ev
    (fun _ h => RingHom.mem_ker.mp (hkill h))
  have hfBase : f.comp (algebraMap SeedField Q) = b := by
    apply RingHom.ext
    intro a
    change ev (MvPolynomial.C a) = b a
    exact MvPolynomial.eval₂Hom_C _ _ _
  have hfAmbient : f.comp (ambientInFibre J) = k.comp ρ := hev
  let D := RootAmbient ⧸ J
  let : CommRing D := Ideal.Quotient.commRing J
  let : CommRing (Polynomial D) := AddMonoidAlgebra.commRing
  let j : D →+* E := Ideal.Quotient.lift J ρ (fun p hp =>
    RingHom.mem_ker.mp (hker.symm ▸ hp))
  have hj : Function.Injective j :=
    RingHom.lift_injective_of_ker_le_ideal J _ hker.le
  let d : D →+* Q := Ideal.Quotient.lift J (ambientInFibre J) (fun p hp =>
    Ideal.Quotient.eq_zero_iff_mem.mpr
      ((le_sup_left : J.map baseChange ≤ fibreIdeal J) (Ideal.mem_map_of_mem baseChange hp)))
  have hd : d.comp (Ideal.Quotient.mk J) = ambientInFibre J := rfl
  let t : (Polynomial D) →+* Q := Polynomial.eval₂RingHom d
    (algebraMap SeedField Q (K1_14_2.generic 0))
  have hft : f.comp t = (algebraMap (Polynomial E) (SpareField E)).comp (Polynomial.mapRingHom j) := by
    apply Polynomial.ringHom_ext'
    · apply Ideal.Quotient.ringHom_ext
      apply RingHom.ext
      intro p
      simp only [RingHom.comp_apply, t, Polynomial.coe_eval₂RingHom, Polynomial.coe_mapRingHom]
      rw [Polynomial.eval₂_C, Polynomial.map_C]
      change f (d (Ideal.Quotient.mk J p)) = k (ρ p)
      exact DFunLike.congr_fun hfAmbient p
    · change f (Polynomial.eval₂RingHom d
        (algebraMap SeedField Q (K1_14_2.generic 0)) Polynomial.X) = _
      rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X]
      exact (DFunLike.congr_fun hfBase _).trans hb.2.2
  have htinj : Function.Injective (f.comp t) := by
    rw [hft]
    exact (IsFractionRing.injective (Polynomial E) (SpareField E)).comp (Polynomial.map_injective j hj)
  have hfinj : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro q hq
    obtain ⟨u, hu, p, hp⟩ := clear_fibre_denominators J d hd q
    have hpzero : (f.comp t) p = 0 := by
      change f (t p) = 0
      rw [← show q * u = t p from hp, map_mul, hq, zero_mul]
    have hp0 : p = 0 := (injective_iff_map_eq_zero (f.comp t)).mp htinj p hpzero
    have hp' : q * u = t p := hp
    rw [hp0, map_zero] at hp'
    exact (hu.mul_left_eq_zero).mp hp'
  exact ⟨f, hfinj, hfBase, hfAmbient⟩
theorem proof : K1_14_2_4_1_3_3.c2 := by
  intro C₀ hC J g R hfinite b hb
  let Q := RootYSection J
  have hb' : IsOrdinateMap ((rootMap R).comp MvPolynomial.C) (rootMap R (MvPolynomial.X 2)) b := by
    refine ⟨fun a => ?_, ?_, hb.2.2⟩
    · simpa only [RingHom.comp_apply, rootMap_base] using hb.1 a
    · simpa only [rootMap_ordinate] using hb.2.1
  obtain ⟨f, hfinj, hfBase, hfAmbient⟩ := fibre_embedding J (rootMap R) (rootMap_kernel R) b hb'
  let : IsDomain Q := hfinj.isDomain f
  let : Module.Finite SeedField Q := hfinite
  let : Field Q := (IsField.of_isDomain_of_finite SeedField Q).toField
  have hsurj : Function.Surjective f := by
    intro z
    apply RingHom.mem_fieldRange.mp
    apply spare_mem R f.fieldRange _ _ z
    · intro p
      exact ⟨ambientInFibre J p, DFunLike.congr_fun hfAmbient p⟩
    · exact ⟨algebraMap SeedField Q (K1_14_2.generic 0),
        (DFunLike.congr_fun hfBase _).trans hb.2.2⟩
  exact ⟨RingEquiv.ofBijective f ⟨hfinj, hsurj⟩, hfBase⟩
end
end K1_14_2_4_1_3_3_2
end
section
set_option autoImplicit false
namespace K1_14_2_4_1_5_1
noncomputable section
open K1_14 K1_14_2_4_1 K1_14_2_4_1_5 K1_13_6_3_4 MvPolynomial
def slopeCoeff {n : ℕ} (i : Fin n) : SlopeField n :=
  algebraMap (ParameterGeometry n) (SlopeField n) (MvPolynomial.X i)
def slopeForm (n : ℕ) : MvPolynomial (Fin n) (SlopeField n) :=
  ∑ i, MvPolynomial.C (slopeCoeff i) * MvPolynomial.X i
private theorem eval₂_scale {k E σ : Type*} [Field k] [Field E] [Fintype σ]
    (f : k →+* E) (x : σ → E) (t : E) {p : MvPolynomial σ k} {d : ℕ}
    (hp : p.IsHomogeneous d) :
    eval₂ f (fun i => t * x i) p = t ^ d * eval₂ f x p := by
  classical
  rw [eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hd : e.degree = d := by
    by_contra h
    exact (mem_support_iff.mp he) (hp.coeff_eq_zero h)
  rw [show (∏ i : σ, (t * x i) ^ e i) = t ^ d * ∏ i : σ, x i ^ e i by
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      ← Finsupp.degree_eq_sum, hd]]
  ring
private theorem map_boundary_component {k E σ : Type*} [Field k] [Field E]
    (f : k →+* E) (I : Ideal (MvPolynomial σ k)) {p : MvPolynomial σ k} {d : ℕ}
    (hp : p ∈ I) (hd : p.totalDegree ≤ d) :
    MvPolynomial.map f (homogeneousComponent d p) ∈ boundaryIdeal (I.map (MvPolynomial.map f)) := by
  have he : MvPolynomial.map f (homogeneousComponent d p) =
      homogeneousComponent d (MvPolynomial.map f p) := by
    ext e
    by_cases h : e.degree = d <;>
      simp only [coeff_homogeneousComponent, coeff_map, h, ite_true, ite_false, map_zero]
  refine Ideal.subset_span ⟨MvPolynomial.map f p, d, Ideal.mem_map_of_mem _ hp, ?_, he⟩
  exact (Finset.sup_mono (support_map_subset f p)).trans hd
private theorem boundaryChart_dimension_le_one {k σ : Type*} [Field k] [Finite σ]
    [LinearOrder σ] [WellFoundedGT σ] (I : Ideal (MvPolynomial σ k))
    (hI : (affineHilbertPolynomial I).natDegree ≤ 1) (i : σ) :
    (affineHilbertPolynomial (boundaryChart I i)).natDegree = 0 := by
  rcases eq_or_lt_of_le hI with h | h
  · exact K1_13_5_4_4_2.boundaryChart_dimension I h i
  · apply Nat.eq_zero_of_le_zero
    have hcut : boundaryIdeal I ≤ boundaryChart I i := le_sup_left
    refine (natDegree_affineHilbertPolynomial_le_of_le hcut).trans ?_
    rw [K1_13_5_4_4_2.hilbertPolynomial_boundary]
    omega
private abbrev SlopeClosure (n : ℕ) := AlgebraicClosure (SlopeField n)
private theorem normalize_boundary {n : ℕ} (I : Ideal (ParameterGeometry n))
    {x : Fin n → SlopeClosure n}
    (hx : x ∈ zeroLocus (SlopeClosure n)
      (boundaryIdeal (I.map (MvPolynomial.map (algebraMap FX (SlopeField n))))))
    {i : Fin n} (hi : x i ≠ 0) :
    (fun j => (x i)⁻¹ * x j) ∈ zeroLocus (SlopeClosure n) (boundaryChart I i) := by
  change boundaryChart I i ≤ RingHom.ker (eval₂Hom (algebraMap FX (SlopeClosure n))
    (fun j => (x i)⁻¹ * x j))
  apply sup_le
  · apply Ideal.span_le.mpr
    rintro _ ⟨p, d, hp, hd, rfl⟩
    have he := hx _ (map_boundary_component (algebraMap FX (SlopeField n)) I hp hd)
    rw [aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq] at he
    change eval₂ (algebraMap FX (SlopeClosure n)) (fun j => (x i)⁻¹ * x j)
      (homogeneousComponent d p) = 0
    rw [eval₂_scale _ x ((x i)⁻¹) (homogeneousComponent_isHomogeneous _ _), he, mul_zero]
  · apply Ideal.span_le.mpr
    rintro _ (rfl : _ = MvPolynomial.X i - 1)
    change eval₂ (algebraMap FX (SlopeClosure n)) (fun j => (x i)⁻¹ * x j)
      (MvPolynomial.X i - 1) = 0
    rw [eval₂_sub, eval₂_X, eval₂_one, inv_mul_cancel₀ hi, sub_self]
private theorem chart_coordinate_algebraic {k E σ : Type*} [Field k] [Field E] [Algebra k E]
    [Finite σ] (J : Ideal (MvPolynomial σ k)) (hJ : (affineHilbertPolynomial J).natDegree = 0)
    {x : σ → E} (hx : x ∈ zeroLocus E J) (j : σ) : IsAlgebraic k (x j) := by
  let : Module.Finite k (MvPolynomial σ k ⧸ J) :=
    moduleFinite_of_natDegree_affineHilbertPolynomial_eq_zero hJ
  let e : (MvPolynomial σ k ⧸ J) →ₐ[k] E := Ideal.Quotient.liftₐ J (aeval x) hx
  have h := (Algebra.IsIntegral.isIntegral (R := k) (Ideal.Quotient.mk J (MvPolynomial.X j))).map e
  change IsIntegral k (aeval x (MvPolynomial.X j)) at h
  rw [aeval_X] at h
  exact h.isAlgebraic
theorem slopeValueReduction {n : ℕ} (I : Ideal (ParameterGeometry n))
    (hI : (affineHilbertPolynomial I).natDegree ≤ 1) :
    ValueReduction (I.map (MvPolynomial.map (algebraMap FX (SlopeField n)))) (slopeForm n) := by
  classical
  have hl : (slopeForm n).IsHomogeneous 1 :=
    (homogeneousSubmodule (Fin n) (SlopeField n) 1).sum_mem
      fun j _ => isHomogeneous_C_mul_X (slopeCoeff j) j
  apply K1_13_5_4_4_2.valueReduction_of_geometric (K := SlopeClosure n) _ hl
  intro x hx hz
  funext i
  change x i = 0
  by_contra hi
  let E := SlopeClosure n
  let u (j : Fin n) : E := algebraMap (SlopeField n) E (slopeCoeff j)
  have hu₀ : AlgebraicIndependent FX (@slopeCoeff n) :=
    (algebraicIndependent_X (Fin n) FX).map'
      (f := IsScalarTower.toAlgHom FX (ParameterGeometry n) (SlopeField n))
      (IsFractionRing.injective _ _)
  have hu : AlgebraicIndependent FX u :=
    hu₀.map' (f := IsScalarTower.toAlgHom FX (SlopeField n) E) (algebraMap (SlopeField n) E).injective
  let A := algebraicClosure FX E
  have hlin : LinearIndependent A u := hu.algebraicClosure.linearIndependent
  have hb := normalize_boundary I hx hi
  let b (j : Fin n) : A := ⟨(x i)⁻¹ * x j, mem_algebraicClosure_iff.mpr
    (chart_coordinate_algebraic _ (boundaryChart_dimension_le_one I hI i) hb j)⟩
  have hsum : ∑ j, u j * x j = 0 := by
    simpa only [slopeForm, map_sum, map_mul, aeval_C, aeval_X, u] using hz
  have hs : ∑ j, b j • u j = 0 := by
    change ∑ j, ((x i)⁻¹ * x j) * u j = 0
    simp_rw [mul_assoc, mul_comm (x _) (u _)]
    rw [← Finset.mul_sum, hsum, mul_zero]
  have hzero := (Fintype.linearIndependent_iff.mp hlin b hs) i
  have hbi : (x i)⁻¹ * x i = (0 : E) := congrArg Subtype.val hzero
  rw [inv_mul_cancel₀ hi] at hbi
  exact one_ne_zero hbi
end
end K1_14_2_4_1_5_1
end
section
set_option autoImplicit false
namespace K1_14_2_4_1_5_1
noncomputable section
open K1_14 K1_14_2_4_1 K1_14_2_4_1_5 K1_13_6_3_4 MvPolynomial
open scoped K1_14_2_4_1_5
private def parameterIdeal {n : ℕ} (B : Ideal (ChartBaseRing n)) : Ideal (ParameterGeometry n) :=
  B.comap (parameterInclusion n)
private theorem parameterIdeal_degree {n : ℕ} (B : Ideal (ChartBaseRing n)) :
    (affineHilbertPolynomial (parameterIdeal B)).natDegree ≤
      (affineHilbertPolynomial B).natDegree := by
  let f : ParameterGeometry n →ₐ[FX] ChartBaseRing n := MvPolynomial.rename Sum.inr
  let g : (ParameterGeometry n ⧸ parameterIdeal B) →ₐ[FX] Base B :=
    Ideal.quotientMapₐ B f le_rfl
  exact natDegree_affineHilbertPolynomial_le_of_injective g
    (Ideal.quotientMap_injective (I := B) (f := f.toRingHom))
private abbrev extendedParameterIdeal {n : ℕ} (B : Ideal (ChartBaseRing n)) :
    Ideal (MvPolynomial (Fin n) (SlopeField n)) :=
  (parameterIdeal B).map (MvPolynomial.map (algebraMap FX (SlopeField n)))
private def evalQuotient {n : ℕ} (B : Ideal (ChartBaseRing n)) :
    (MvPolynomial (Fin n) (SlopeField n) ⧸ extendedParameterIdeal B) →ₐ[SlopeField n]
      ExtendedBase B := by
  apply Ideal.Quotient.liftₐ _ (parameterEval B)
  change extendedParameterIdeal B ≤ RingHom.ker (parameterEval B).toRingHom
  apply Ideal.map_le_iff_le_comap.mpr
  intro q hq
  have hq' : parameterInclusion n q ∈ B := hq
  change parameterEval B (MvPolynomial.map (algebraMap FX (SlopeField n)) q) = 0
  rw [parameterEval_map B, Ideal.Quotient.eq_zero_iff_mem.mpr hq', map_zero]
private theorem eval_slopeForm {n : ℕ} (B : Ideal (ChartBaseRing n)) :
    evalQuotient B (Ideal.Quotient.mk (extendedParameterIdeal B) (slopeForm n)) =
      genericLinear B := by
  change parameterEval B (slopeForm n) = genericLinear B
  unfold slopeForm genericLinear
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_mul, parameterEval, aeval_C, aeval_X, slopeCoeff]
  exact (Algebra.smul_def (A := ExtendedBase B) _ _).symm
private theorem map_evalQuotient_degree {n : ℕ} (B : Ideal (ChartBaseRing n)) (d : ℕ) :
    (quotientDegreeLE (extendedParameterIdeal B) d).map (evalQuotient B).toLinearMap =
      parameterDegreeLE B d := by
  rw [quotientDegreeLE, ← Submodule.map_comp, parameterDegreeLE]
  congr 1
private theorem powerSpan_le_succ {F A : Type} [Field F] [CommRing A] [Algebra F A]
    (a : A) (W : Submodule F A) (k : ℕ) : powerSpan a W k ≤ powerSpan a W (k + 1) := by
  induction k with
  | zero => exact le_sup_left
  | succ k ih =>
    exact sup_le_sup le_rfl (Submodule.map_mono ih)
private theorem add_mul_mem_powerSpan_succ {F A : Type} [Field F] [CommRing A] [Algebra F A]
    (a : A) (W : Submodule F A) (k : ℕ) {x y : A}
    (hx : x ∈ powerSpan a W k) (hy : y ∈ powerSpan a W k) :
    x + a * y ∈ powerSpan a W (k + 1) := by
  refine Submodule.add_mem _ (powerSpan_le_succ a W k hx) ?_
  change a * y ∈ W ⊔ (powerSpan a W k).map (LinearMap.mulLeft F a)
  exact Submodule.mem_sup.mpr ⟨0, W.zero_mem, a * y, ⟨y, hy, rfl⟩, zero_add _⟩
private theorem map_valueReduction {F A σ : Type} [Field F] [CommRing A] [Algebra F A]
    {I : Ideal (MvPolynomial σ F)} {ℓ : MvPolynomial σ F}
    (φ : (MvPolynomial σ F ⧸ I) →ₐ[F] A) (h : ValueReduction I ℓ) :
    ∃ D : ℕ, ∀ k : ℕ, (quotientDegreeLE I (D + k)).map φ.toLinearMap ≤
      powerSpan (φ (Ideal.Quotient.mk I ℓ)) ((quotientDegreeLE I D).map φ.toLinearMap) k := by
  obtain ⟨D, hD⟩ := h
  refine ⟨D, ?_⟩
  intro k
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hz
    obtain ⟨x, hx, y, hy, hxy⟩ := hD (D + k) (Nat.le_add_right D k) w hw
    change φ w ∈ _
    rw [hxy, map_add, map_mul]
    exact add_mul_mem_powerSpan_succ _ _ _
      (ih (Submodule.mem_map_of_mem hx)) (ih (Submodule.mem_map_of_mem hy))
theorem proof : K1_14_2_4_1_5.c1 := by
  intro n B _ hdim
  have h := slopeValueReduction (parameterIdeal B) ((parameterIdeal_degree B).trans hdim)
  obtain ⟨D, hD⟩ := map_valueReduction (evalQuotient B) h
  refine ⟨D, fun k => ?_⟩
  simpa only [map_evalQuotient_degree, eval_slopeForm] using hD k
end
end K1_14_2_4_1_5_1
end
section
set_option autoImplicit false
namespace K1_14_2_4_2
noncomputable section
open K1 K1_14 K1_14_2_4 MvPolynomial
open K1_14_6_1 (derivativeAt)
open scoped Polynomial BigOperators
variable {n : ℕ}
private abbrev incl := algebraMap (Polynomial L) FX
theorem eval_center (S : (Polynomial K)) : (S.map seedEmbedding).eval center = atX S := by
  rw [Polynomial.eval_map]
  change S.eval₂ (incl.comp (Polynomial.C.comp (algebraMap K L))) (incl Polynomial.X) =
    incl (S.map (algebraMap K L))
  rw [← Polynomial.hom_eval₂, ← Polynomial.eval₂_map, Polynomial.eval₂_C_X]
theorem factorial_ne_zero {i : ℕ} (hi : i < p) : (i.factorial : FX) ≠ 0 := by
  let : CharP FX p := charP_of_injective_ringHom seedEmbedding.injective p
  induction i with
  | zero => simp
  | succ i ih =>
    have hc : ((i+1 : ℕ) : FX) ≠ 0 := by
      intro h
      exact (not_le_of_gt hi) (Nat.le_of_dvd (Nat.succ_pos i) ((CharP.cast_eq_zero_iff FX p _).mp h))
    simpa only [Nat.factorial_succ, Nat.cast_mul] using mul_ne_zero hc (ih (Nat.lt_of_succ_lt hi))
private def weight (x : K) (i : ℕ) : FX :=
  (i.factorial : FX)⁻¹ * (seedEmbedding x - center)^i
end
end K1_14_2_4_2
end
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace K1_13_6_1_4_1_2
noncomputable section
open MvPolynomial
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
section Family
variable {k σ τ : Type} [Field k]
local notation "P" => MvPolynomial τ k
local notation "F" => FractionRing (MvPolynomial τ k)
local notation "A" => MvPolynomial σ k
local notation "T" => MvPolynomial σ (MvPolynomial τ k)
local notation "U" => MvPolynomial σ (FractionRing (MvPolynomial τ k))
private def liftBase : A →+* T := MvPolynomial.map MvPolynomial.C
private def preCut (s : Finset τ) (p : τ → A) : T :=
  ∑ j ∈ s, C (MvPolynomial.X j) * liftBase (p j)
def fixedCut (s : Finset τ) (p : τ → A) (c : τ → k) : A :=
  ∑ j ∈ s, C (c j) * p j
def familyCut (s : Finset τ) (p : τ → A) : U :=
  algebraMap T U (preCut s p)
private def reduce (I : Ideal A) : T →+* MvPolynomial τ (A ⧸ I) :=
  (MvPolynomial.map (Ideal.Quotient.mk I)).comp (commAlgEquiv k σ τ).toRingHom
@[simp] private theorem reduce_C (I : Ideal A) (r : P) :
    reduce I (C r) = MvPolynomial.map (algebraMap k (A ⧸ I)) r := by
  change MvPolynomial.map (Ideal.Quotient.mk I) (commAlgEquiv k σ τ (C r)) = _
  rw [commAlgEquiv_C, MvPolynomial.map_map]
  rfl
@[simp] private theorem reduce_lift (I : Ideal A) (v : A) :
    reduce I (liftBase (τ := τ) v) = (C (Ideal.Quotient.mk I v) : MvPolynomial τ (A ⧸ I)) := by
  change (reduce I).comp liftBase v = (C.comp (Ideal.Quotient.mk I)) v
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [liftBase]
    rfl
  · intro i
    simp [reduce, liftBase]
private theorem ker_reduce (I : Ideal A) : RingHom.ker (reduce (τ := τ) I) = I.map liftBase := by
  let e := commAlgEquiv k σ τ
  have hcomp : e.toRingHom.comp liftBase = (C : A →+* MvPolynomial τ A) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [e, liftBase]
    · intro i
      simp [e, liftBase]
  change RingHom.ker ((MvPolynomial.map (Ideal.Quotient.mk I)).comp e.toRingHom) = _
  rw [← RingHom.comap_ker, MvPolynomial.ker_map, Ideal.mk_ker,
    ← hcomp, ← Ideal.map_map]
  exact Ideal.comap_map_of_bijective (I := I.map liftBase) e.toRingHom e.bijective
private theorem extend_lift : (algebraMap T U).comp liftBase = MvPolynomial.map (algebraMap k F) := by
  change (MvPolynomial.map (algebraMap P F)).comp liftBase = _
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [liftBase]
    rfl
  · intro i
    simp [liftBase]
private theorem extend_lift_apply (v : A) :
    algebraMap T U (liftBase v) = MvPolynomial.map (algebraMap k F) v :=
  DFunLike.congr_fun extend_lift v
private theorem extend_cutIdeal (I : Ideal A) (s : Finset τ) (p : τ → A) :
    (I.map liftBase ⊔ Ideal.span {preCut s p}).map (algebraMap T U) =
      I.map (MvPolynomial.map (algebraMap k F)) ⊔ Ideal.span {familyCut s p} := by
  rw [Ideal.map_sup, Ideal.map_map, extend_lift, Ideal.map_span, Set.image_singleton]
  rfl
theorem familyCut_eq_sum (s : Finset τ) (p : τ → A) :
    familyCut s p = ∑ j ∈ s, C (algebraMap P F (MvPolynomial.X j)) *
      MvPolynomial.map (algebraMap k F) (p j) := by
  unfold familyCut preCut
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, extend_lift_apply, MvPolynomial.algebraMap_def, MvPolynomial.map_C]
theorem familyCut_finite [Finite σ] (I : Ideal A) [I.IsPrime]
    (hdim : (affineHilbertPolynomial I).natDegree ≤ 1)
    (s : Finset τ) (p : τ → A) {j : τ} (hj : j ∈ s) (hone : p j = 1) :
    Module.Finite F (U ⧸
      (I.map (MvPolynomial.map (algebraMap k F)) ⊔ Ideal.span {familyCut s p})) := by
  classical
  let M := (nonZeroDivisors P).map (C (σ := σ))
  let I' : Ideal T := I.map liftBase
  have hprime : I'.IsPrime := by
    rw [show I' = I.map liftBase from rfl, ← ker_reduce]
    exact (RingHom.ker_isPrime (reduce I))
  have hdisj : Disjoint (M : Set T) (I' : Set T) := by
    refine Set.disjoint_left.mpr ?_
    intro x hx hi
    change x ∈ (nonZeroDivisors P).map (C (σ := σ)) at hx
    obtain ⟨r, hr, rfl⟩ := hx
    change C r ∈ I.map liftBase at hi
    rw [← ker_reduce, RingHom.mem_ker, reduce_C] at hi
    exact nonZeroDivisors.ne_zero hr
      ((MvPolynomial.map_injective _ (algebraMap k (A ⧸ I)).injective) (hi.trans (map_zero _).symm))
  have hpre : preCut s p ∉ I' := by
    change preCut s p ∉ I.map liftBase
    rw [← ker_reduce, RingHom.mem_ker]
    intro hh
    have h := congrArg (fun p : MvPolynomial τ (A ⧸ I) => p.coeff (Finsupp.single j 1)) hh
    simp only [preCut, map_sum, map_mul, reduce_C, reduce_lift, map_X, coeff_sum, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h
    rw [Finset.sum_eq_single_of_mem j hj] at h
    · simp [hone] at h
    · intro i _ hi
      rw [mul_comm (MvPolynomial.X i), coeff_C_mul, MvPolynomial.coeff_single_X]
      simp [hi]
  have hext : I'.map (algebraMap T U) = I.map (MvPolynomial.map (algebraMap k F)) := by
    rw [show I' = I.map liftBase from rfl, Ideal.map_map, extend_lift]
  have hprime' := IsLocalization.isPrime_of_isPrime_disjoint M U I' hprime hdisj
  have hproper : familyCut s p ∉ I'.map (algebraMap T U) := by
    change preCut s p ∉ (I'.map (algebraMap T U)).under T
    rwa [IsLocalization.under_map_of_isPrime_disjoint M U hprime hdisj]
  rw [hext] at hprime' hproper
  apply natDegree_affineHilbertPolynomial_eq_zero_iff.mp
  apply Nat.eq_zero_of_le_zero
  have h := (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
    hprime' hproper (le_refl (familyCut s p).totalDegree)).1
  rw [K1_13_5_5_2.hilbertPolynomial_map] at h
  exact h.trans (by omega)
private theorem shift_reduce_preCut (I : Ideal A) (s : Finset τ) (p : τ → A) (c : τ → k) :
    shift (fun j => algebraMap k (A ⧸ I) (c j)) (reduce I (preCut s p)) =
      C (Ideal.Quotient.mk I (fixedCut s p c)) +
        ∑ j ∈ s, C (Ideal.Quotient.mk I (p j)) * MvPolynomial.X j := by
  let q := Ideal.Quotient.mk I
  calc
    _ = ∑ j ∈ s, (C (q (C (c j) * p j)) + C (q (p j)) * MvPolynomial.X j) := by
      simp only [preCut, map_sum, map_mul, reduce_C, reduce_lift, map_X, shift_X, shift_C]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [add_mul]
      change MvPolynomial.X j * C (q (p j)) + C (q (C (c j))) * C (q (p j)) = _
      rw [mul_comm (MvPolynomial.X j), add_comm]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← map_sum, ← map_sum]
      rfl
theorem familyCut_independent (I : Ideal A) [I.IsPrime]
    (s : Finset τ) (p : τ → A) (c : τ → k) (hproper : fixedCut s p c ∉ I)
    {ι : Type} [Fintype ι] (v : ι → A)
    (hv : LinearIndependent k (fun i =>
      Ideal.Quotient.mk (I ⊔ Ideal.span {fixedCut s p c}) (v i))) :
    LinearIndependent F fun i =>
      Ideal.Quotient.mk
        (I.map (MvPolynomial.map (algebraMap k F)) ⊔ Ideal.span {familyCut s p})
        (MvPolynomial.map (algebraMap k F) (v i)) := by
  classical
  let M := (nonZeroDivisors P).map (C (σ := σ))
  let J : Ideal T := I.map liftBase ⊔ Ideal.span {preCut s p}
  let JF := J.map (algebraMap T U)
  let qF := Ideal.Quotient.mk JF
  rw [← extend_cutIdeal]
  apply Fintype.linearIndependent_iff.mpr
  intro b hb
  change ∑ i, b i • qF (MvPolynomial.map (algebraMap k F) (v i)) = 0 at hb
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors P) b
  choose a ha using hd
  let S : T := ∑ i, C (a i) * liftBase (v i)
  have hS : algebraMap T U S ∈ JF := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change qF (algebraMap T U S) = 0
    have hterm : ∀ i, qF (algebraMap T U (C (a i) * liftBase (v i))) =
        (d.val • b i) • qF (MvPolynomial.map (algebraMap k F) (v i)) := by
      intro i
      rw [map_mul, map_mul, extend_lift_apply, MvPolynomial.algebraMap_def,
        MvPolynomial.map_C, ha i, ← qF.map_mul, ← MvPolynomial.smul_eq_C_mul]
      exact map_smul (Ideal.Quotient.mkₐ F JF) _ _
    have hs (i : ι) : d.val • b i = algebraMap P F d.val * b i :=
      Algebra.smul_def d.val (b i)
    simp only [S, map_sum, hterm, hs, mul_smul, ← Finset.smul_sum, hb, smul_zero]
  obtain ⟨m, hm, hmul⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff M U J S).mp hS
  change m ∈ (nonZeroDivisors P).map (C (σ := σ)) at hm
  obtain ⟨r, hr, rfl⟩ := hm
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hmul
  obtain ⟨H, hH⟩ := Ideal.mem_span_singleton.mp hy
  have hx0 : reduce (τ := τ) I x = 0 := by
    change x ∈ I.map liftBase at hx
    rwa [← ker_reduce, RingHom.mem_ker] at hx
  let translate := shift (fun j : τ => algebraMap k (A ⧸ I) (c j))
  have he : translate (reduce I (C r * S)) =
      translate (reduce I (preCut s p)) * translate (reduce I H) := by
    rw [← hxy, map_add, hx0, zero_add, hH, map_mul, map_mul, mul_comm]
  have he' : ∑ i, MvPolynomial.map (algebraMap k (A ⧸ I)) (shift c (r * a i)) *
        C (Ideal.Quotient.mk I (v i)) =
      (C (Ideal.Quotient.mk I (fixedCut s p c)) +
        ∑ j ∈ s, C (Ideal.Quotient.mk I (p j)) * MvPolynomial.X j) *
        translate (reduce I H) := by
    rw [show translate (reduce I (preCut s p)) = _ from shift_reduce_preCut I s p c] at he
    refine Eq.trans ?_ he
    dsimp only [S]
    rw [Finset.mul_sum, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_assoc, ← C.map_mul]
    simp only [translate, map_mul, reduce_C, reduce_lift, shift_map, shift_C]
  let q := Ideal.Quotient.factorₐ k (le_sup_left : I ≤ I ⊔ Ideal.span {fixedCut s p c})
  have hq : q (Ideal.Quotient.mk I (fixedCut s p c)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hzero := coefficients_eq_zero q (mt Ideal.Quotient.eq_zero_iff_mem.mp hproper)
    hq hv s (fun j => Ideal.Quotient.mk I (p j)) _ _ he'
  intro i
  have hai : a i = 0 := by
    have hh : r * a i = 0 := shift_injective c (by simpa using hzero i)
    exact (mul_eq_zero.mp hh).resolve_left (nonZeroDivisors.ne_zero hr)
  have hh := ha i
  rw [hai, map_zero, Algebra.smul_def] at hh
  exact (mul_eq_zero.mp hh.symm).resolve_left
    ((map_ne_zero_iff _ (IsFractionRing.injective P F)).mpr (nonZeroDivisors.ne_zero d.property))
end Family
end
end K1_13_6_1_4_1_2
end
section
set_option autoImplicit false
namespace K1_13_6_1_4_1_2
noncomputable section
open MvPolynomial K1_13 K1_13_6 K1_13_6_1 K1_13_6_1_4 K1_13_6_1_4_1
private def exponent (a : Shape) : SectionIndex a ↪ (Fin 4 →₀ ℕ) where
  toFun m := Finsupp.equivFunOnFinite.symm fun i => (m i).val
  inj' := by
    intro x y h
    funext i
    apply Fin.ext
    exact DFunLike.congr_fun h i
private def boxTerm (k : Type) [Field k] {a : Shape} (m : SectionIndex a) :
    MvPolynomial (Fin 4) k :=
  ∏ i : Fin 4, MvPolynomial.X i ^ (m i).val
private theorem exists_fixedCut {k : Type} [Field k]
    {Q : MvPolynomial (Fin 4) k} {a : Shape} (hQ : FitsBox Q a) :
    ∃ c : SectionIndex a → k, fixedCut (boxMonomials a) (boxTerm k) c = Q := by
  classical
  refine ⟨fun m => Q.coeff (exponent a m), ?_⟩
  have hexp (m : SectionIndex a) (i : Fin 4) : exponent a m i = (m i).val := rfl
  have hsupport : Q.support ⊆ (boxMonomials a).map (exponent a) := by
    intro s hs
    have hb : (∑ i : Fin 4, s i) ≤ a.b := by
      simpa [Finsupp.sum_fintype] using (le_totalDegree hs).trans hQ.1
    have hj : (∑ i : Fin 4, i.val * s i) ≤ a.j := by
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype, nsmul_eq_mul, Nat.mul_comm] using
        (le_weightedTotalDegree Fin.val hs).trans hQ.2.1
    have ht : s 3 ≤ a.t := (monomial_le_degreeOf 3 hs).trans hQ.2.2
    let m : SectionIndex a := fun i =>
      ⟨s i, Nat.lt_succ_of_le ((Finset.single_le_sum
        (f := fun j : Fin 4 => s j) (fun j _ => Nat.zero_le (s j)) (Finset.mem_univ i)).trans hb)⟩
    refine Finset.mem_map.mpr ⟨m, ?_, Finsupp.ext fun _ => rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ m, hb, hj, ht⟩
  have hsum := Finset.sum_subset (f := fun s => monomial s (Q.coeff s)) hsupport (by
    intro s _ hs
    rw [notMem_support_iff.mp hs, map_zero])
  rw [Finset.sum_map] at hsum
  calc
    fixedCut (boxMonomials a) (boxTerm k) (fun m => Q.coeff (exponent a m)) =
        ∑ m ∈ boxMonomials a, monomial (exponent a m) (Q.coeff (exponent a m)) := by
      unfold fixedCut boxTerm
      apply Finset.sum_congr rfl
      intro m _
      rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      simp only [hexp]
    _ = Q := hsum.symm.trans Q.as_sum.symm
theorem proof : K1_13_6_1_4_1.c2 := by
  classical
  intro k _ I Q a hI hdim _ hproper hfit
  let : I.IsPrime := hI
  obtain ⟨c, hc⟩ := exists_fixedCut hfit
  let z : SectionIndex a := fun _ => 0
  have hz : z ∈ boxMonomials a := by simp [z, boxMonomials]
  have hone : boxTerm k z = 1 := by simp [boxTerm, z]
  have hgen : familyCut (boxMonomials a) (boxTerm k) = cutPolynomial k a := by
    rw [familyCut_eq_sum, cutPolynomial]
    simp [boxTerm]
  let J := I ⊔ Ideal.span {Q}
  have hdimJ : (affineHilbertPolynomial J).natDegree = 0 := by
    have h := (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le_of_isPrime
      hI hproper (le_refl Q.totalDegree)).1
    exact Nat.eq_zero_of_le_zero (h.trans (by omega))
  let : Module.Finite k (MvPolynomial (Fin 4) k ⧸ J) :=
    natDegree_affineHilbertPolynomial_eq_zero_iff.mp hdimJ
  let := familyCut_finite I hdim (boxMonomials a) (boxTerm k) hz hone
  let b := Module.finBasis k (MvPolynomial (Fin 4) k ⧸ J)
  choose v hv using fun i => Ideal.Quotient.mk_surjective (b i)
  have hlin : LinearIndependent k (fun i => Ideal.Quotient.mk J (v i)) := by
    simpa only [hv] using b.linearIndependent
  have hlin' := familyCut_independent I (boxMonomials a) (boxTerm k) c
    (hc.symm ▸ hproper) v (hc.symm ▸ hlin)
  unfold genericCutLength
  rw [← hgen]
  simpa only [Fintype.card_fin] using hlin'.fintype_card_le_finrank
end
end K1_13_6_1_4_1_2
end
section
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace K1_13_6_3_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 Polynomial
@[simp] theorem toComponent_rowAt (P : JetIdeal) [P.IsPrime] (H : Row 4) :
    toComponent P (rowAt P H) = componentRow P H := by
  unfold toComponent rowAt
  rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]
  rfl
theorem componentRow_eq_zero (P : JetIdeal) [P.IsPrime] (H : Row 4) :
    componentRow P H = 0 ↔ toGeneric H ∈ P := by
  change algebraMap (GeoJets ⧸ P) (JetField P) (Ideal.Quotient.mk P (toGeneric H)) = 0 ↔ _
  rw [map_eq_zero_iff _ (IsFractionRing.injective (GeoJets ⧸ P) (JetField P)),
    Ideal.Quotient.eq_zero_iff_mem]
theorem rowAt_eq_zero (P : JetIdeal) [P.IsPrime] (H : Row 4) :
    rowAt P H = 0 ↔ toGeneric H ∈ P := by
  rw [← map_eq_zero_iff _ (toComponent P).injective, toComponent_rowAt, componentRow_eq_zero]
@[simp] theorem toComponent_constantsAt (P : JetIdeal) [P.IsPrime] (a : Geom) :
    toComponent P (algebraMap Geom (ContractedField P) a) = componentConstants P a := by
  change toComponent P (rowAt P (MvPolynomial.C (Polynomial.C a))) = _
  rw [toComponent_rowAt]
  simp [componentRow, componentConstants, geomConstants]
@[simp] theorem toComponent_abscissa (P : JetIdeal) [P.IsPrime] :
    toComponent P (abscissa (rowAt P)) = onComponent P (MvPolynomial.C genericArgument) := by
  rw [abscissa, toComponent_rowAt]
  simp [componentRow, genericArgument]
@[simp] theorem toComponent_jetCoordinate (P : JetIdeal) [P.IsPrime] (i : Fin 4) :
    toComponent P (jetCoordinate (rowAt P) i) = onComponent P (MvPolynomial.X i) := by
  rw [jetCoordinate, toComponent_rowAt]
  simp [componentRow]
theorem factorial_ne_zero {F : Type} [Field F] (k : Geom →+* F) {n : ℕ}
    (h : n < K1.p) : (n.factorial : F) ≠ 0 := by
  rw [← map_natCast k]
  exact (map_ne_zero_iff k k.injective).mpr (K1_13_7_1.factorial_cast_ne_zero h)
theorem fromTaylor_degree {F : Type} [CommRing F] {M : ℕ} (x : F) (a : Fin M → F)
    (hM : 0 < M) : (fromTaylor x a).natDegree < M := by
  unfold fromTaylor
  refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ (n := M - 1) _ ?_) (by omega)
  intro i _
  have hterm : (C (a i) * (Polynomial.X (R := F) - Polynomial.C x) ^ i.val).natDegree ≤ i.val := by
    apply natDegree_mul_le.trans
    simp only [natDegree_C, zero_add]
    simpa only [Nat.mul_one] using natDegree_pow_le_of_le i.val (natDegree_X_sub_C_le x)
  exact hterm.trans (Nat.le_pred_of_lt i.isLt)
theorem fromTaylor_hasse {F : Type} [CommRing F] {M : ℕ} (x : F) (a : Fin M → F)
    (i : Fin M) : (hasseDeriv i.val (fromTaylor x a)).eval x = a i := by
  classical
  have h : taylor x (fromTaylor x a) = ∑ j, monomial j.val (a j) := by
    simp only [fromTaylor, map_sum, taylor_mul, taylor_pow, taylor_C, map_sub,
      taylor_X, add_sub_cancel_right, C_mul_X_pow_eq_monomial]
  rw [← taylor_coeff, h, finsetSum_coeff, Finset.sum_eq_single i]
  · simp
  · intro j _ hij
    simp [coeff_monomial, Finsupp.single_apply, show j.val ≠ i.val from fun he => hij (Fin.ext he)]
  · simp
theorem map_fromTaylor {F E : Type} [CommRing F] [CommRing E] (k : F →+* E)
    {M : ℕ} (x : F) (a : Fin M → F) :
    (fromTaylor x a).map k = fromTaylor (k x) (fun i => k (a i)) := by
  change Polynomial.mapRingHom k (fromTaylor x a) = _
  simp only [fromTaylor, map_sum, map_mul, map_pow, map_sub, Polynomial.coe_mapRingHom, map_C, map_X]
theorem map_trajectory {F E : Type} [Field F] [Field E] (k : F →+* E) (a : Geom →+* F)
    (H : Row 4) (U : (Polynomial F)) :
    (trajectory a H U).map k = trajectory (k.comp a) H (U.map k) := by
  unfold trajectory
  change Polynomial.mapRingHom k (MvPolynomial.eval₂ _ _ H) = _
  rw [MvPolynomial.hom_eval₂]
  have hm : (Polynomial.mapRingHom k).comp (Polynomial.mapRingHom a) =
      Polynomial.mapRingHom (k.comp a) := by
    apply RingHom.ext
    intro q
    exact Polynomial.map_map a k q
  simp only [hm, Polynomial.coe_mapRingHom, ← Polynomial.hasseDeriv_map]
private theorem cleared_product_rule {F : Type} [Field F] [Algebra Geom F]
    (D : Derivation Geom F F) (s v : F) (a : ℕ) :
    s * (s * D (s ^ a * v)) - (a : F) * (s * D s) * (s ^ a * v) =
      s ^ (a + 2) * D v := by
  cases a with
  | zero => simp [pow_two, mul_assoc]
  | succ a =>
    rw [D.leibniz, D.leibniz_pow, Nat.succ_sub_one, pow_add s (a + 1) 2, pow_succ' s a]
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_succ]
    ring
theorem jetNumerator_eq_iterate {F : Type} [Field F] [Algebra Geom F]
    (e : Row 4 →+* F) (g : Row 4) (D : Derivation Geom F F)
    (action : ∀ H, e (separant g) * D (e H) = e (flowNumerator g H)) (n : ℕ) :
    e (jetNumerator g n) =
      e (separant g) ^ (2 * n) * ((D : F → F)^[n]) (jetCoordinate e 0) := by
  induction n with
  | zero => simp [jetNumerator, jetCoordinate]
  | succ n ih =>
    simp only [jetNumerator, clearedStep, map_sub, map_mul, map_natCast, ← action]
    rw [ih, cleared_product_rule, Function.iterate_succ_apply',
      show 2 * (n + 1) = 2 * n + 2 by omega]
theorem separated_weight {H : Row 4} {B : ℕ} (h : TrueWeightLE H B) :
    TrueWeightLE (separant H) B := by
  intro m hm
  rw [MvPolynomial.mem_support_iff, separant, MvPolynomial.coeff_pderiv] at hm
  have hsrc := h _ (MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hm))
  have hweight (w : Fin 4 → ℕ) :
      (m + Finsupp.single (3 : Fin 4) 1).sum (fun i k => w i * k) =
        m.sum (fun i k => w i * k) + w 3 := by
    rw [Finsupp.sum_add_index' (fun i => Nat.mul_zero (w i)) (fun i b c => Nat.mul_add (w i) b c),
      Finsupp.sum_single_index (h := fun i k => w i * k) (Nat.mul_zero _), mul_one]
  rw [hweight] at hsrc
  change ((separant H).coeff m).natDegree + _ ≤ B
  rw [separant, MvPolynomial.coeff_pderiv]
  have hd := natDegree_mul_le (p := H.coeff (m + Finsupp.single 3 1))
    (q := (m 3 : (Polynomial Geom)) + 1)
  have hc : ((m 3 : (Polynomial Geom)) + 1).natDegree = 0 := by
    rw [← Nat.cast_succ, natDegree_natCast]
  rw [hc, add_zero] at hd
  omega
theorem iterate_separant_weight {H : Row 4} {B : ℕ} (h : TrueWeightLE H B) (r : ℕ) :
    TrueWeightLE ((separant^[r]) H) B := by
  induction r with
  | zero => exact h
  | succ r ih => simpa only [Function.iterate_succ_apply'] using separated_weight ih
end
end K1_13_6_3_2
end
section
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace K1_13_6_3_2
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 Polynomial
def c1 : Prop :=
  ∀ (g : Row 4) (P : JetIdeal) (_hp : P.IsPrime),
    toGeneric g ∈ P → toGeneric (separant g) ∉ P → Invariant g P →
    ∃ D : Derivation Geom (ContractedField P) (ContractedField P),
      D (abscissa (rowAt P)) = 1 ∧
      (∀ i : Fin 3, D (jetCoordinate (rowAt P) i.castSucc) =
        ((i.val + 1 : ℕ) : ContractedField P) * jetCoordinate (rowAt P) i.succ) ∧
      ∀ H : Row 4, rowAt P (separant g) * D (rowAt P H) = rowAt P (flowNumerator g H)
def c2 : Prop :=
  ∀ (F : Type) [Field F] [Algebra Geom F] (D : Derivation Geom F F) (x y : F),
    D x = 1 → ((D : F → F)^[taylorLength]) y = 0 →
    ∀ (H : Row 4) (B : ℕ), TrueWeightLE H B → B + 3 < K1.p →
      MvPolynomial.eval₂ (Polynomial.aeval x).toRingHom
        (fun i => dividedIterate D y i.val) H = 0 →
      trajectory (algebraMap Geom F) H (differentialTaylor D x y) = 0
def c3 : Prop :=
  ∀ (g : Row 4) (P : JetIdeal) (_hp : P.IsPrime),
    toGeneric g ∈ P → toGeneric (separant g) ∉ P →
    ∀ S : (Polynomial Geom), S.natDegree < taylorLength → P ≤ markIdeal S →
      atJet (separant g) S ≠ 0 →
      coeffPoint S ∈ MvPolynomial.zeroLocus Geom
        (coefficientKernel (componentConstants P) (chartTaylor (componentRow P) g))
end
end K1_13_6_3_2
end
section
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace K1_13_6_3_2_1
noncomputable section
open K1_13 K1_13_6 K1_13_6_3 K1_13_6_3_2 K1_13_6_2_2_2
open nonZeroDivisors
private def rowJet {F : Type} [CommRing F] (g : Row 4) (e : Chart g →+* F) :
    Row 4 →+* Dual F where
  toFun H := (e (incl g H), e (D g (incl g H)))
  map_zero' := by
    apply TrivSqZeroExt.ext
    · change e (incl g 0) = 0
      simp
    · change e (D g (incl g 0)) = 0
      simp
  map_one' := by
    apply TrivSqZeroExt.ext
    · change e (incl g 1) = 1
      simp
    · change e (D g (incl g 1)) = 0
      rw [map_one, show D g 1 = 0 from by simpa only [Nat.cast_one] using D_natCast g 1,
        map_zero]
  map_add' H J := by
    apply TrivSqZeroExt.ext
    · change e (incl g (H + J)) = e (incl g H) + e (incl g J)
      simp only [map_add]
    · change e (D g (incl g (H + J))) = e (D g (incl g H)) + e (D g (incl g J))
      simp only [map_add]
  map_mul' H J := by
    apply TrivSqZeroExt.ext
    · change e (incl g (H * J)) = e (incl g H) * e (incl g J)
      simp only [map_mul]
    · change e (D g (incl g (H * J))) =
        e (incl g H) * e (D g (incl g J)) + e (D g (incl g H)) * e (incl g J)
      simp only [map_mul, D_mul, map_add]
private theorem extendJet {A F : Type} [CommRing A] [Field F] [Algebra A F]
    [IsFractionRing A F] (j : A →+* Dual F)
    (hfst : ∀ a, (j a).fst = algebraMap A F a) :
    ∃ J : F →+* Dual F, (∀ a, J (algebraMap A F a) = j a) ∧ ∀ z, (J z).fst = z := by
  have hu (a : nonZeroDivisors A) : IsUnit (j a) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, hfst]
    exact IsLocalization.map_units F a
  let J : F →+* Dual F := IsLocalization.lift hu
  have hJ (a : A) : J (algebraMap A F a) = j a := IsLocalization.lift_eq hu a
  refine ⟨J, hJ, ?_⟩
  have he : (TrivSqZeroExt.fstHom F F F).toRingHom.comp J = RingHom.id F := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors A)
    apply RingHom.ext
    intro a
    change (J (algebraMap A F a)).fst = algebraMap A F a
    rw [hJ, hfst]
  exact DFunLike.congr_fun he
private def derivationOfJet {k F : Type} [CommRing k] [CommRing F] [Algebra k F]
    (J : F →+* Dual F) (hfst : ∀ z, (J z).fst = z)
    (hconst : ∀ a : k, (J (algebraMap k F a)).snd = 0) : Derivation k F F :=
  Derivation.mk'
    { toFun := fun z => (J z).snd
      map_add' := fun x y => by rw [map_add, TrivSqZeroExt.snd_add]
      map_smul' := fun a x => by
        change (J (a • x)).snd = a • (J x).snd
        rw [Algebra.smul_def, map_mul]
        change (J (algebraMap k F a)).fst * (J x).snd +
          (J (algebraMap k F a)).snd * (J x).fst = a • (J x).snd
        rw [hfst, hconst, zero_mul, add_zero, Algebra.smul_def] }
    (fun x y => by
      change (J (x * y)).snd = x * (J y).snd + y * (J x).snd
      rw [map_mul]
      change (J x).fst * (J y).snd + (J x).snd * (J y).fst = _
      rw [hfst, hfst, mul_comm (J x).snd y])
private theorem chartDerivation {A F : Type} [CommRing A] [Field F] [Algebra A F]
    [IsFractionRing A F] [Algebra Geom F] (g : Row 4)
    (f : Row 4 →+* A) (hf : Function.Surjective f) (e : Chart g →+* F)
    (he : ∀ H, e (incl g H) = algebraMap A F (f H))
    (hstable : ∀ H, algebraMap A F (f H) = 0 → e (D g (incl g H)) = 0)
    (hconst : ∀ a : Geom, algebraMap A F (f (MvPolynomial.C (Polynomial.C a))) =
      algebraMap Geom F a) :
    ∃ δ : Derivation Geom F F, ∀ H, δ (algebraMap A F (f H)) = e (D g (incl g H)) := by
  let j₀ := rowJet g e
  have hker : RingHom.ker f ≤ RingHom.ker j₀ := by
    intro H hH
    have hz : algebraMap A F (f H) = 0 := by rw [RingHom.mem_ker.mp hH, map_zero]
    apply RingHom.mem_ker.mpr
    apply TrivSqZeroExt.ext
    · exact (he H).trans hz
    · exact hstable H hz
  let j : A →+* Dual F := f.liftOfSurjective hf ⟨j₀, hker⟩
  have hj (H : Row 4) : j (f H) = j₀ H := RingHom.liftOfSurjective_comp_apply f hf _ H
  have hjfst (a : A) : (j a).fst = algebraMap A F a := by
    obtain ⟨H, rfl⟩ := hf a
    rw [hj]
    exact he H
  obtain ⟨J, hJ, hJfst⟩ := extendJet j hjfst
  have hrow (H : Row 4) : J (algebraMap A F (f H)) = j₀ H := (hJ (f H)).trans (hj H)
  have hc (a : Geom) : (J (algebraMap Geom F a)).snd = 0 := by
    rw [← hconst, hrow]
    change e (D g (constants g (Polynomial.C a))) = 0
    rw [D_incl_C, Polynomial.derivative_C]
    change e (incl g (MvPolynomial.C 0)) = 0
    simp only [map_zero]
  exact ⟨derivationOfJet J hJfst hc, fun H => congrArg TrivSqZeroExt.snd (hrow H)⟩
set_option maxHeartbeats 800000 in
theorem proof : K1_13_6_3_2.c1 := by
  intro g P hp _hg hs hi
  let _ : P.IsPrime := hp
  let F := ContractedField P
  let f : Row 4 →+* ContractedRing P := (componentRow P).rangeRestrict
  have hf : Function.Surjective f := (componentRow P).rangeRestrict_surjective
  have hs' : rowAt P (separant g) ≠ 0 := fun hz => hs ((rowAt_eq_zero P _).mp hz)
  let e : Chart g →+* F := IsLocalization.Away.lift (separant g) (g := rowAt P) hs'.isUnit
  have he (H : Row 4) : e (incl g H) = rowAt P H := IsLocalization.Away.lift_eq _ _ _
  have hflow (H : Row 4) : rowAt P (separant g) * e (D g (incl g H)) =
      rowAt P (flowNumerator g H) := by
    simpa only [map_mul, he] using DFunLike.congr_arg e (D_incl g H)
  have hstable (H : Row 4) (hz : rowAt P H = 0) : e (D g (incl g H)) = 0 := by
    have ht := (rowAt_eq_zero P (flowNumerator g H)).mpr (hi H ((rowAt_eq_zero P H).mp hz))
    exact (mul_eq_zero.mp ((hflow H).trans ht)).resolve_left hs'
  obtain ⟨δ, hδ⟩ := chartDerivation g f hf e he hstable (fun _ => rfl)
  have hδrow (H : Row 4) : δ (rowAt P H) = e (D g (incl g H)) := hδ H
  refine ⟨δ, ?_, ?_, fun H => by rw [hδrow, hflow]⟩
  · change δ (rowAt P (MvPolynomial.C Polynomial.X)) = 1
    rw [hδrow]
    change e (D g (constants g Polynomial.X)) = 1
    rw [D_incl_C, Polynomial.derivative_X]
    change e (incl g (MvPolynomial.C 1)) = 1
    simp only [map_one]
  · intro i
    change δ (rowAt P (MvPolynomial.X i.castSucc)) =
      ((i.val + 1 : ℕ) : F) * rowAt P (MvPolynomial.X i.succ)
    rw [hδrow, D_X_old, map_mul, map_natCast, he]
end
end K1_13_6_3_2_1
end
section
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace K1_13_6_3_2_2
noncomputable section
open K1_13 K1_13_6_3 K1_13_6_3_2 Polynomial
variable {F : Type} [Field F] [Algebra Geom F]
private theorem natCast_ne_zero {n : ℕ} (hn : 0 < n) (hp : n < K1.p) :
    (n : F) ≠ 0 := by
  intro h
  have hf := factorial_ne_zero (algebraMap Geom F) hp
  cases n with
  | zero => omega
  | succ n => exact hf (by rw [Nat.factorial_succ, Nat.cast_mul, h, zero_mul])
variable (D : Derivation Geom F F)
private def horizontal : Subsemiring (Polynomial F) where
  carrier := {P | ∀ n, D (P.coeff n) = P.derivative.coeff n}
  zero_mem' n := by simp
  one_mem' n := by
    rw [derivative_one, coeff_zero, coeff_one]
    split_ifs <;> simp
  add_mem' {P Q} hP hQ n := by
    simp only [coeff_add, map_add, hP n, hQ n]
  mul_mem' {P Q} hP hQ n := by
    have hMul (a b : F) : D (a * b) = a * D b + D a * b := by
      rw [D.leibniz, smul_eq_mul, smul_eq_mul, mul_comm b (D a)]
    change D ((P * Q).coeff n) = (P * Q).derivative.coeff n
    simp only [coeff_mul, map_sum, hMul, hP _, hQ _, derivative_mul, coeff_add,
      Finset.sum_add_distrib]
    abel
omit [Algebra Geom F] in
private theorem hasse_comm (i j : ℕ) (P : (Polynomial F)) :
    hasseDeriv i (hasseDeriv j P) = hasseDeriv j (hasseDeriv i P) := by
  have hi := LinearMap.congr_fun (hasseDeriv_comp (R := F) i j) P
  have hj := LinearMap.congr_fun (hasseDeriv_comp (R := F) j i) P
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hi hj
  rw [hi, hj, Nat.add_comm j i, Nat.choose_symm_add (a := i) (b := j)]
private theorem hasse_horizontal {P : (Polynomial F)} (hP : P ∈ horizontal D) (i : ℕ) :
    hasseDeriv i P ∈ horizontal D := by
  intro n
  rw [← hasseDeriv_one', hasse_comm 1 i, hasseDeriv_one', hasseDeriv_coeff,
    hasseDeriv_coeff, D.leibniz, D.map_natCast, smul_eq_mul, smul_eq_mul,
    mul_zero, add_zero, hP (n + i)]
private theorem shifted_coefficients (x : F) (hx : D x = 1) (b : (Polynomial Geom)) :
    taylor x (b.map (algebraMap Geom F)) ∈ horizontal D := by
  have hX : ((Polynomial.X : (Polynomial F)) + C x) ∈ horizontal D := by
    intro n
    simp only [coeff_add, derivative_X_add_C, coeff_X, coeff_C, coeff_one]
    split_ifs <;> simp_all
  induction b using Polynomial.induction_on' with
  | add a b ha hb =>
    simpa only [Polynomial.map_add, map_add] using (horizontal D).add_mem ha hb
  | monomial n a =>
    rw [Polynomial.map_monomial, taylor_monomial]
    refine (horizontal D).mul_mem (fun j => ?_) ((horizontal D).pow_mem hX n)
    simp only [coeff_C, derivative_C, coeff_zero]
    split_ifs <;> simp
private theorem divided_step (y : F) (n : ℕ) (hn : n + 1 < K1.p) :
    D (dividedIterate D y n) = dividedIterate D y (n + 1) * ((n : F) + 1) := by
  have hf : (n.factorial : F) ≠ 0 :=
    factorial_ne_zero (algebraMap Geom F) (Nat.lt_of_succ_lt hn)
  have hs : (n : F) + 1 ≠ 0 := by
    rw [← Nat.cast_succ]
    exact natCast_ne_zero (Nat.succ_pos _) hn
  simp only [dividedIterate]
  rw [D.leibniz_div_const _ _ (D.map_natCast _), smul_eq_mul, Function.iterate_succ_apply',
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  field_simp [hf, hs]
private def centered (L : ℕ) (x y : F) : (Polynomial F) :=
  taylor x (fromTaylor (M := L) x (fun j => dividedIterate D y j.val))
private theorem coeff_centered {L : ℕ} (hL : 0 < L) (x y : F) (n : ℕ) :
    (centered D L x y).coeff n = if n < L then dividedIterate D y n else 0 := by
  by_cases hn : n < L
  · rw [ite_eq_left hn, centered, taylor_coeff]
    exact fromTaylor_hasse x (fun j : Fin L => dividedIterate D y j.val) ⟨n, hn⟩
  · rw [ite_eq_right hn]
    apply coeff_eq_zero_of_natDegree_lt
    unfold centered
    rw [natDegree_taylor]
    exact (fromTaylor_degree _ _ hL).trans_le (Nat.le_of_not_lt hn)
private theorem centered_horizontal {L : ℕ} (hL : 0 < L) (hp : L < K1.p) (x y : F)
    (hcut : ((D : F → F)^[L]) y = 0) :
    centered D L x y ∈ horizontal D := by
  intro n
  rw [coeff_derivative, coeff_centered D hL, coeff_centered D hL]
  by_cases hnext : n + 1 < L
  · rw [ite_eq_left hnext, ite_eq_left (show n < L by omega)]
    exact divided_step D y n (hnext.trans hp)
  · rw [ite_eq_right hnext, zero_mul]
    by_cases hn : n < L
    · have he : n + 1 = L := by omega
      have hz : dividedIterate D y L = 0 := by
        rw [dividedIterate, hcut, zero_div]
      rw [ite_eq_left hn, divided_step D y n (by rwa [he]), he, hz, zero_mul]
    · rw [ite_eq_right hn, map_zero]
private theorem trajectory_horizontal (x : F) (hx : D x = 1) (H : Row 4) (U : (Polynomial F))
    (hU : taylor x U ∈ horizontal D) :
    taylor x (trajectory (algebraMap Geom F) H U) ∈ horizontal D := by
  let t := (taylorAlgHom x).toRingHom
  let g := t.comp (Polynomial.mapRingHom (algebraMap Geom F))
  let a : Fin 4 → (Polynomial F) := fun i => hasseDeriv i.val (taylor x U)
  have ha (i : Fin 4) : t (hasseDeriv i.val U) = a i :=
    (hasseDeriv_taylor U x i.val).symm
  have ht : t (trajectory (algebraMap Geom F) H U) = MvPolynomial.eval₂ g a H := by
    rw [trajectory, MvPolynomial.hom_eval₂]
    simp only [ha]
    rfl
  change t (trajectory (algebraMap Geom F) H U) ∈ horizontal D
  rw [ht]
  let g' : (Polynomial Geom) →+* horizontal D := g.codRestrict _ (shifted_coefficients D x hx)
  let a' : Fin 4 → horizontal D := fun i => ⟨a i, hasse_horizontal D hU i.val⟩
  let P : horizontal D := MvPolynomial.eval₂ g' a' H
  have hm : (P : (Polynomial F)) = MvPolynomial.eval₂ g a H :=
    MvPolynomial.hom_eval₂ H g' (horizontal D).subtype a'
  rw [← hm]
  exact P.2
private theorem trajectory_degree (H : Row 4) {B : ℕ} (hH : TrueWeightLE H B)
    {U : (Polynomial F)} (hU : U.natDegree ≤ 133671) :
    (trajectory (algebraMap Geom F) H U).natDegree ≤ B := by
  classical
  rw [trajectory, MvPolynomial.eval₂_eq]
  apply natDegree_sum_le_of_forall_le
  intro m hm
  have hprod : (∏ i ∈ m.support, hasseDeriv i.val U ^ m i).natDegree ≤
      m.sum (fun i e => (133671 - i.val) * e) := by
    unfold Finsupp.sum
    apply (natDegree_prod_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    change ((hasseDeriv i.val U) ^ m i).natDegree ≤ (133671 - i.val) * m i
    rw [Nat.mul_comm]
    exact natDegree_pow_le_of_le _ ((natDegree_hasseDeriv_le U i.val).trans
      (Nat.sub_le_sub_right hU _))
  exact (natDegree_mul_le_of_le natDegree_map_le hprod).trans (hH m hm)
private theorem trajectory_at_center (x : F) (H : Row 4) (U : (Polynomial F)) :
    (trajectory (algebraMap Geom F) H U).eval x =
      MvPolynomial.eval₂ (Polynomial.aeval x).toRingHom
        (fun i => (hasseDeriv i.val U).eval x) H := by
  change evalRingHom x (MvPolynomial.eval₂ _ _ H) = _
  have hc : (evalRingHom x).comp (Polynomial.mapRingHom (algebraMap Geom F)) =
      (Polynomial.aeval x).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      change ((C a).map (algebraMap Geom F)).eval x = Polynomial.aeval x (C a)
      rw [Polynomial.map_C, eval_C, aeval_C]
    · change ((Polynomial.X : (Polynomial Geom)).map (algebraMap Geom F)).eval x =
        Polynomial.aeval x Polynomial.X
      rw [Polynomial.map_X, eval_X, aeval_X]
  rw [MvPolynomial.hom_eval₂, hc]; rfl
private theorem horizontal_zero {P : (Polynomial F)} (hP : P ∈ horizontal D)
    (h0 : P.coeff 0 = 0) (hdeg : P.natDegree < K1.p) : P = 0 := by
  have hz : ∀ n < K1.p, P.coeff n = 0 := by
    intro n
    induction n with
    | zero => exact fun _ => h0
    | succ n ih =>
      intro hn
      have he := hP n
      rw [coeff_derivative, ih (Nat.lt_of_succ_lt hn), map_zero] at he
      have hs : (n : F) + 1 ≠ 0 := by
        rw [← Nat.cast_succ]
        exact natCast_ne_zero (Nat.succ_pos _) hn
      exact (mul_eq_zero.mp he.symm).resolve_right hs
  ext n
  rw [coeff_zero]
  by_cases hn : n < K1.p
  · exact hz n hn
  · exact coeff_eq_zero_of_natDegree_lt (hdeg.trans_le (Nat.le_of_not_lt hn))
set_option maxRecDepth 200000 in
theorem proof : K1_13_6_3_2.c2 := by
  intro F _ _ D x y hx hcut H B hH hguard hzero
  let U := differentialTaylor D x y
  change trajectory (algebraMap Geom F) H U = 0
  have hU : U.natDegree < taylorLength := fromTaylor_degree _ _ (by decide)
  have hjet (i : Fin 4) : (hasseDeriv i.val U).eval x = dividedIterate D y i.val := by
    have h := fromTaylor_hasse x (fun j => dividedIterate D y j.val)
      (i.castLE (by decide : 4 ≤ taylorLength))
    exact h
  have hroot : (trajectory (algebraMap Geom F) H U).eval x = 0 := by
    rwa [trajectory_at_center, show (fun i : Fin 4 => (hasseDeriv i.val U).eval x) =
      (fun i : Fin 4 => dividedIterate D y i.val) from funext hjet]
  have htranslate : taylor x U ∈ horizontal D :=
    centered_horizontal D (by decide : 0 < taylorLength) (by decide) x y hcut
  apply (taylor_eq_zero x _).mp
  apply horizontal_zero D (trajectory_horizontal D x hx H U htranslate)
  · rwa [taylor_coeff_zero]
  · rw [natDegree_taylor]
    exact (trajectory_degree H hH (Nat.le_of_lt_succ hU)).trans_lt
      (lt_of_le_of_lt (Nat.le_add_right B 3) hguard)
end
end K1_13_6_3_2_2
end
section
set_option autoImplicit false
namespace K1_13_6_3_2_3
noncomputable section
open Polynomial K1_13_6_3_2
variable {R k F E : Type} [CommRing R] [Field k] [Field F] [Field E]
private def liftAt (s : R) (e : R →+* F) (h : e s ≠ 0) : Localization.Away s →+* F :=
  IsLocalization.Away.lift s h.isUnit
private theorem liftAt_map (s : R) (e : R →+* F) (h : e s ≠ 0) (a : R) :
    liftAt s e h (algebraMap R (Localization.Away s) a) = e a :=
  IsLocalization.Away.lift_eq s h.isUnit a
private theorem liftAt_inverse (s : R) (e : R →+* F) (h : e s ≠ 0) :
    liftAt s e h (IsLocalization.Away.invSelf s) = (e s)⁻¹ := by
  have heq := congrArg (liftAt s e h)
    (IsLocalization.Away.mul_invSelf (S := Localization.Away s) s)
  rw [map_mul, liftAt_map, map_one] at heq
  exact ((mul_eq_one_iff_inv_eq₀ h).mp heq).symm
private theorem liftAt_zero (s : R) (e : R →+* F) (f : R →+* E)
    (he : e s ≠ 0) (hf : f s ≠ 0) (hker : ∀ a, e a = 0 → f a = 0)
    (z : Localization.Away s) (hz : liftAt s e he z = 0) : liftAt s f hf z = 0 := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj s z
  have h₁ := congrArg (liftAt s e he) ha
  have h₂ := congrArg (liftAt s f hf) ha
  simp only [map_mul, map_pow, liftAt_map, hz, zero_mul] at h₁
  simp only [map_mul, map_pow, liftAt_map, hker a h₁.symm] at h₂
  exact (mul_eq_zero.mp h₂).resolve_right (pow_ne_zero _ hf)
private def localTaylor {M : ℕ} (c : k →+* R) (s x : R) (a : Fin M → R) :
    (Polynomial (Localization.Away s)) :=
  let η := algebraMap R (Localization.Away s)
  fromTaylor (η x) (fun i : Fin M => η (a i) *
    (IsLocalization.Away.invSelf s) ^ (2 * i.val) * η (c (i.val.factorial : k)⁻¹))
def fieldTaylor {M : ℕ} (e : R →+* F) (s x : R) (a : Fin M → R) : (Polynomial F) :=
  fromTaylor (e x) (fun i : Fin M => e (a i) / e s ^ (2 * i.val) / (i.val.factorial : F))
private theorem map_localTaylor {M : ℕ} (c : k →+* R) (s x : R) (a : Fin M → R)
    (e : R →+* F) (he : e s ≠ 0) :
    (localTaylor c s x a).map (liftAt s e he) = fieldTaylor e s x a := by
  unfold localTaylor fieldTaylor
  rw [map_fromTaylor, liftAt_map]
  apply congrArg (fromTaylor (M := M) (e x))
  funext i
  have hc : e (c (i.val.factorial : k)⁻¹) = (i.val.factorial : F)⁻¹ := by
    change (e.comp c) _ = _
    rw [map_inv₀, map_natCast]
  simp only [map_mul, map_pow, liftAt_map, liftAt_inverse, hc, div_eq_mul_inv, inv_pow]
private def coeffEquation {M : ℕ} {B : Type} [CommRing B] (c : k →+* B) (U : (Polynomial B))
    (q : MvPolynomial (Fin M) k) : B :=
  q.eval₂ c (fun i => U.coeff i.val)
private theorem map_equation {M : ℕ} {B : Type} [CommRing B] (h : B →+* F)
    (c : k →+* B) (U : (Polynomial B)) (q : MvPolynomial (Fin M) k) :
    h (coeffEquation c U q) = coeffEquation (h.comp c) (U.map h) q := by
  simp only [coeffEquation, MvPolynomial.hom_eval₂, coeff_map]
private theorem specialize_equation {M : ℕ} (c : k →+* R) (s x : R) (a : Fin M → R)
    (e : R →+* F) (he : e s ≠ 0) (q : MvPolynomial (Fin M) k) :
    liftAt s e he (coeffEquation ((algebraMap R (Localization.Away s)).comp c)
      (localTaylor c s x a) q) = coeffEquation (e.comp c) (fieldTaylor e s x a) q := by
  rw [map_equation, map_localTaylor]
  have hc : (liftAt s e he).comp ((algebraMap R (Localization.Away s)).comp c) = e.comp c :=
    RingHom.ext fun b => liftAt_map s e he (c b)
  rw [hc]
theorem transport {M : ℕ} (c : k →+* R) (s x : R) (a : Fin M → R)
    (e : R →+* F) (f : R →+* E) (he : e s ≠ 0) (hf : f s ≠ 0)
    (hker : ∀ b, e b = 0 → f b = 0) (q : MvPolynomial (Fin M) k)
    (hq : q.eval₂ (e.comp c) (fun i => (fieldTaylor e s x a).coeff i.val) = 0) :
    q.eval₂ (f.comp c) (fun i => (fieldTaylor f s x a).coeff i.val) = 0 := by
  change coeffEquation (f.comp c) _ q = 0
  rw [← specialize_equation c s x a f hf q]
  apply liftAt_zero s e f he hf hker
  rw [specialize_equation]
  exact hq
end
end K1_13_6_3_2_3
end
section
set_option autoImplicit false
set_option maxRecDepth 1600
set_option maxHeartbeats 500000
namespace K1_13_6_3_2_3
noncomputable section
open Polynomial K1_13 K1_13_6 K1_13_6_3 K1_13_6_3_2
private def physicalConstants : Geom →+* Row 4 := MvPolynomial.C.comp Polynomial.C
private def markRow (S : (Polynomial Geom)) : Row 4 →+* GeoField :=
  genericCoeffs.comp (MvPolynomial.eval (jet S))
private theorem markRow_apply (S : (Polynomial Geom)) (H : Row 4) :
    markRow S H = genericCoeffs (atJet H S) := rfl
private theorem markRow_constants (S : (Polynomial Geom)) :
    (markRow S).comp physicalConstants = geomConstants := by
  apply RingHom.ext
  intro a
  simp only [markRow, physicalConstants, RingHom.comp_apply, MvPolynomial.eval_C, geomConstants]
private theorem componentRow_constants (P : JetIdeal) :
    (componentRow P).comp physicalConstants = componentConstants P := by
  apply RingHom.ext
  intro a
  simp only [componentRow, physicalConstants, componentConstants, geomConstants,
    RingHom.comp_apply, MvPolynomial.map_C]
private theorem genericCoeffs_inj : Function.Injective genericCoeffs :=
  (algebraMap GenericField GeoField).injective.comp (IsFractionRing.injective (Polynomial Geom) GenericField)
private theorem divided_actual (g : Row 4) (S : (Polynomial Geom)) (hg : atJet g S = 0)
    (hs : markRow S (separant g) ≠ 0) (i : Fin taylorLength) :
    markRow S (jetNumerator g i.val) / markRow S (separant g) ^ (2*i.val) /
      (i.val.factorial : GeoField) = genericCoeffs (hasseDeriv i.val S) := by
  have ho : derivative^[i.val] S = (i.val.factorial : (Polynomial Geom)) * hasseDeriv i.val S := by
    have h := congrFun (factorial_smul_hasseDeriv (R := Geom) (k := i.val)) S
    change i.val.factorial • hasseDeriv i.val S = derivative^[i.val] S at h
    simpa only [nsmul_eq_mul] using h.symm
  have hfact := factorial_ne_zero geomConstants (i.isLt.trans (by decide : taylorLength < K1.p))
  rw [markRow_apply S (jetNumerator g i.val), eval_jetNumerator _ _ hg, map_mul, map_pow,
    ← markRow_apply, mul_div_cancel_left₀ _ (pow_ne_zero _ hs), ho, map_mul, map_natCast,
    mul_div_cancel_left₀ _ hfact]
private theorem eval_generic_center (U : (Polynomial Geom)) :
    (U.map geomConstants).eval genericArgument = genericCoeffs U := by
  change ((evalRingHom genericArgument).comp (mapRingHom geomConstants)) U = _
  apply RingHom.congr_fun
  apply Polynomial.ringHom_ext <;> simp [geomConstants, genericArgument]
private theorem recover {B : Type} [CommRing B] {M : ℕ} (x : B) (a : Fin M → B)
    (U : (Polynomial B)) (hU : U.natDegree < M)
    (ha : ∀ i : Fin M, a i = (hasseDeriv i.val U).eval x) : fromTaylor x a = U := by
  apply taylor_injective x
  ext n
  by_cases hn : n < M
  · rw [taylor_coeff, taylor_coeff]
    exact (fromTaylor_hasse x a ⟨n, hn⟩).trans (ha ⟨n, hn⟩)
  · have hM : 0 < M := (Nat.zero_le _).trans_lt hU
    have hleft := (fromTaylor_degree x a hM).trans_le (Nat.le_of_not_lt hn)
    have hright := hU.trans_le (Nat.le_of_not_lt hn)
    rw [coeff_eq_zero_of_natDegree_lt ((natDegree_taylor _ _).trans_lt hleft),
      coeff_eq_zero_of_natDegree_lt ((natDegree_taylor _ _).trans_lt hright)]
private theorem mark_polynomial (g : Row 4) (S : (Polynomial Geom)) (hg : atJet g S = 0)
    (hs : markRow S (separant g) ≠ 0) (hd : S.natDegree < taylorLength) :
    chartTaylor (markRow S) g = S.map geomConstants := by
  have hx : abscissa (markRow S) = genericArgument := by
    simp only [abscissa, markRow, RingHom.comp_apply, MvPolynomial.eval_C, genericArgument]
  unfold chartTaylor
  rw [hx]
  apply recover _ _ _ (natDegree_map_le.trans_lt hd)
  intro i
  rw [divided_actual g S hg hs i, hasseDeriv_map, eval_generic_center]
private theorem fieldTaylor_chart {F : Type} [Field F] (e : Row 4 →+* F) (g : Row 4) :
    fieldTaylor e (separant g) (MvPolynomial.C Polynomial.X)
      (fun i : Fin taylorLength => jetNumerator g i.val) = chartTaylor e g := rfl
private def vanishes {F : Type} [Field F] (k : Geom →+* F) (U : (Polynomial F)) (q : CoeffRing) : Prop :=
  q.eval₂ k (fun i => U.coeff i.val) = 0
private theorem mem_kernel_iff {F : Type} [Field F] (k : Geom →+* F) (U : (Polynomial F))
    (q : CoeffRing) : q ∈ coefficientKernel k U ↔ vanishes k U q := Iff.rfl
private theorem mark_equation {F : Type} [Field F] (k : Geom →+* F) (S : (Polynomial Geom)) (q : CoeffRing)
    (h : vanishes k (S.map k) q) : MvPolynomial.eval (coeffPoint S) q = 0 := by
  unfold vanishes at h
  simp only [coeff_map] at h
  apply (map_eq_zero_iff _ k.injective).mp
  rw [MvPolynomial.eval₂_comp]
  exact h
private theorem transport_chart (P : JetIdeal) [P.IsPrime] (g : Row 4) (S : (Polynomial Geom))
    (hgen : componentRow P (separant g) ≠ 0) (hmark : markRow S (separant g) ≠ 0)
    (hP : P ≤ markIdeal S) (q : CoeffRing)
    (hq : vanishes (componentConstants P) (chartTaylor (componentRow P) g) q) :
    vanishes geomConstants (chartTaylor (markRow S) g) q := by
  have hker (b : Row 4) (hb : componentRow P b = 0) : markRow S b = 0 := by
    have hz := K1_13_6_1.mem_markIdeal.mp (hP ((componentRow_eq_zero P b).mp hb))
    rw [markRow_apply, hz, map_zero]
  rw [← componentRow_constants] at hq
  rw [← markRow_constants S]
  rw [← fieldTaylor_chart] at hq ⊢
  unfold vanishes at hq ⊢
  exact transport (k := Geom) (R := Row 4) (F := JetField P) (E := GeoField) (M := taylorLength)
    physicalConstants (separant g) (MvPolynomial.C Polynomial.X)
    (fun i : Fin taylorLength => jetNumerator g i.val) (componentRow P) (markRow S)
    hgen hmark hker q hq
/-- Same statement as `K1_13_6_3_2.c3`, but written out so that the `IsDomain` instance of the
quotient is elaborated in place; `c3` itself stores it as an auxiliary proof whose type uses a
different instance path, and unifying the two through the KoalaBear extension field is very
expensive on Lean 4.36. -/
theorem proof (g : Row 4) (P : JetIdeal) [hp : P.IsPrime]
    (hg : toGeneric g ∈ P) (hsep : toGeneric (separant g) ∉ P) :
    ∀ S : (Polynomial Geom), S.natDegree < taylorLength → P ≤ markIdeal S →
      atJet (separant g) S ≠ 0 →
      coeffPoint S ∈ MvPolynomial.zeroLocus Geom
        (coefficientKernel (componentConstants P) (chartTaylor (componentRow P) g)) := by
  intro S hd hP hr
  have hgen : componentRow P (separant g) ≠ 0 := fun h => hsep ((componentRow_eq_zero P _).mp h)
  have hmark : markRow S (separant g) ≠ 0 := (map_ne_zero_iff _ genericCoeffs_inj).mpr hr
  have hzero := K1_13_6_1.mem_markIdeal.mp (hP hg)
  apply MvPolynomial.mem_zeroLocus_iff.mpr
  intro q hq
  rw [mem_kernel_iff] at hq
  have h := transport_chart P g S hgen hmark hP q hq
  rw [mark_polynomial g S hzero hmark hd] at h
  exact mark_equation geomConstants S q h
end
end K1_13_6_3_2_3
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 8
namespace K1_14_3R_3_3
open K1_14 K1_14_3 MvPolynomial
open scoped nonZeroDivisors
noncomputable section
abbrev Parameters := MvPolynomial (Fin 4) FX
abbrev Raw (σ : Type) := MvPolynomial σ FX
abbrev Over (σ : Type) := MvPolynomial σ SectionField
private abbrev Free := {k : Fin 4 // k ≠ 2}
def parameter (k : Fin 4) : SectionField :=
  algebraMap Parameters SectionField (MvPolynomial.X k)
def fieldLine {σ : Type} (i j : σ) : Over σ :=
  MvPolynomial.X i + C (parameter 0) * MvPolynomial.X j - C (parameter 2)
def sliceIdeal {σ : Type} (P : Ideal (Raw σ)) (i j : σ) : Ideal (Over σ) :=
  P.map (map (algebraMap FX SectionField)) ⊔ Ideal.span {fieldLine i j}
attribute [local instance] MvPolynomial.algebraMvPolynomial
end
end K1_14_3R_3_3
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 8
namespace K1_14_3R_3_3
open K1_14 K1_14_3 K1_14_3R_3 MvPolynomial
open scoped BigOperators
noncomputable section
private abbrev Coord := Option (Option (Fin 2))
private def seedCoord (i : Fin 2) : Coord := some (some i)
end
end K1_14_3R_3_3
end
section
namespace K1_14_2_6
noncomputable section
open K1_14 K1_14_2 Polynomial
abbrev GenericClosure := AlgebraicClosure SeedField
def toGenericClosure : Seeds →+* GenericClosure :=
  (algebraMap SeedField GenericClosure).comp (algebraMap Seeds SeedField)
def genericSeedPoint (y v : GenericClosure) : Ambient →+* GenericClosure :=
  MvPolynomial.eval₂Hom (algebraMap FX GenericClosure)
    ![algebraMap SeedField GenericClosure (generic 0),
      algebraMap SeedField GenericClosure (generic 1), y, v]
def genericJetPoint (a b : GenericClosure) : Ambient →+* GenericClosure :=
  MvPolynomial.eval₂Hom (algebraMap FX GenericClosure)
    ![a, b, algebraMap SeedField GenericClosure (generic 0),
      algebraMap SeedField GenericClosure (generic 1)]
def OnSeedFibre (I : Ideal Ambient) (y v : GenericClosure) : Prop :=
  RingHom.ker (genericSeedPoint y v) = I
def SeparableJetFibre (I : Ideal Ambient) : Prop :=
  ∃ a b, RingHom.ker (genericJetPoint a b) = I ∧
    IsSeparable SeedField a ∧ IsSeparable SeedField b
def HasSeedContact (I : Ideal Ambient) (P : Jet) (m : ℕ) : Prop :=
  ∀ a b : ℕ, a + b < m →
    toJet (seedHasse 0 a (seedHasse 1 b P)) ∈ I
def fibreRow (P : Jet) : Polynomial (Polynomial GenericClosure) :=
  P.map (Polynomial.mapRingHom toGenericClosure)
def HasJetContact (P : Jet) (y v : GenericClosure) (m : ℕ) : Prop :=
  ∀ a b : ℕ, a + b < m →
    (hasseDeriv a ((hasseDeriv b (fibreRow P)).eval (C v))).eval y = 0
end
end K1_14_2_6
end
section
namespace K1_14_2_6
noncomputable section
open K1 K1_14 K1_14_2 Polynomial
def c2 : Prop :=
  ∀ (I : Ideal Ambient), SeparableJetFibre I →
    ∀ (P : Jet) (m : ℕ), m < p → HasSeedContact I P m →
    ∀ y v, OnSeedFibre I y v → HasJetContact P y v m
end
end K1_14_2_6
end
section
set_option autoImplicit false
namespace K1_14_2_6_1
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_6
attribute [local instance] MvPolynomial.algebraMvPolynomial
private abbrev Iterated := MvPolynomial (Fin 2) Seeds
private def chartEquiv (e : Fin 4 ≃ Fin 2 ⊕ Fin 2) : Ambient ≃+* Iterated :=
  ((MvPolynomial.renameEquiv FX e).trans
    (MvPolynomial.sumAlgEquiv FX (Fin 2) (Fin 2))).toRingEquiv
private abbrev seedVariables : Fin 4 ≃ Fin 2 ⊕ Fin 2 :=
  finSumFinEquiv.symm.trans (Equiv.sumComm (Fin 2) (Fin 2))
private abbrev jetVariables : Fin 4 ≃ Fin 2 ⊕ Fin 2 :=
  (finSumFinEquiv (m := 2) (n := 2)).symm
private theorem chartMap (e : Fin 4 ≃ Fin 2 ⊕ Fin 2) :
    (algebraMap Iterated FibreRing).comp (chartEquiv e).toRingHom =
      MvPolynomial.eval₂Hom (MvPolynomial.C.comp (algebraMap FX SeedField))
        (Sum.elim MvPolynomial.X (fun i => MvPolynomial.C (generic i)) ∘ e) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [chartEquiv]
    rfl
  · intro i
    rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', Function.comp_apply]
    change algebraMap Iterated FibreRing
      (MvPolynomial.sumAlgEquiv FX (Fin 2) (Fin 2)
        (MvPolynomial.renameEquiv FX e (MvPolynomial.X i))) = _
    rw [MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, MvPolynomial.algebraMap_def]
    cases e i <;> simp [generic]
theorem seedMap : mapGenericSeed =
    (algebraMap Iterated FibreRing).comp (chartEquiv seedVariables).toRingHom := by
  rw [chartMap]
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [mapGenericSeed, MvPolynomial.eval₂Hom_C]
  · intro i
    simp only [mapGenericSeed, MvPolynomial.eval₂Hom_X', Function.comp_apply]
    fin_cases i <;> rfl
theorem jetMap : mapGenericJets =
    (algebraMap Iterated FibreRing).comp (chartEquiv jetVariables).toRingHom := by
  rw [chartMap]
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [mapGenericJets, MvPolynomial.eval₂Hom_C]
  · intro i
    simp only [mapGenericJets, MvPolynomial.eval₂Hom_X', Function.comp_apply]
    fin_cases i <;> rfl
private theorem separable_of_small_rank (E : Type) [Field E] [Algebra SeedField E]
    [Module.Finite SeedField E] (hsize : Module.finrank SeedField E < p) (x : E) :
    IsSeparable SeedField x := by
  let : CharP SeedField p := charP_of_injective_ringHom
    ((algebraMap FX SeedField).comp seedEmbedding).injective p
  have hx : IsIntegral SeedField x := Algebra.IsIntegral.isIntegral x
  let f := minpoly SeedField x
  have hpos : 0 < f.natDegree := minpoly.natDegree_pos hx
  have hlt : f.natDegree < p := (minpoly.natDegree_le x).trans_lt hsize
  have hcast : (f.natDegree : SeedField) ≠ 0 := by
    intro h
    exact (not_le_of_gt hlt) (Nat.le_of_dvd hpos ((CharP.cast_eq_zero_iff SeedField p _).mp h))
  change f.Separable
  apply (Polynomial.separable_iff_derivative_ne_zero (minpoly.irreducible hx)).2
  intro hzero
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  apply hcast
  have hcoeff := congrArg (fun q : Polynomial SeedField => q.coeff n) hzero
  change f.derivative.coeff n = (0 : Polynomial SeedField).coeff n at hcoeff
  have hmonic : f.coeff f.natDegree = 1 := (minpoly.monic hx).leadingCoeff
  rw [hn] at hmonic
  rw [Polynomial.coeff_derivative, Polynomial.coeff_zero, ← Nat.cast_succ,
    ← hn, hmonic, one_mul] at hcoeff
  exact hcoeff
theorem fibreHom (g : Ambient →+* FibreRing) (e : Ambient ≃+* Iterated)
    (hg : g = (algebraMap Iterated FibreRing).comp e.toRingHom)
    (I : Ideal Ambient) (hI : I.IsPrime) [Module.Finite SeedField (FibreRing ⧸ I.map g)]
    (hpos : 0 < Module.finrank SeedField (FibreRing ⧸ I.map g))
    (hsize : Module.finrank SeedField (FibreRing ⧸ I.map g) < p) :
    ∃ f : FibreRing →ₐ[SeedField] GenericClosure,
      RingHom.ker (f.toRingHom.comp g) = I ∧ ∀ x, IsSeparable SeedField (f x) := by
  let S : Submonoid Iterated := (nonZeroDivisors Seeds).map MvPolynomial.C
  let J : Ideal FibreRing := I.map g
  let I' : Ideal Iterated := I.map e.toRingHom
  have hJ : J = I'.map (algebraMap Iterated FibreRing) := by
    rw [Ideal.map_map, ← hg]
  have hI' : I'.IsPrime := by
    change (I.map (e : Ambient →+* Iterated)).IsPrime
    rw [Ideal.map_comap_of_equiv e]
    exact hI.comap _
  have hproper : J ≠ ⊤ := by
    intro ht
    let : Subsingleton (FibreRing ⧸ J) := Ideal.Quotient.subsingleton_iff.mpr ht
    exact hpos.ne' (Module.finrank_eq_zero_of_subsingleton SeedField (FibreRing ⧸ J))
  have hd : Disjoint (S : Set Iterated) (I' : Set Iterated) :=
    (IsLocalization.map_algebraMap_ne_top_iff_disjoint S FibreRing I').mp (hJ ▸ hproper)
  have hcontract : (I'.map (algebraMap Iterated FibreRing)).comap
      (algebraMap Iterated FibreRing) = I' :=
    IsLocalization.under_map_of_isPrime_disjoint S FibreRing hI' hd
  let : J.IsPrime := hJ ▸ IsLocalization.isPrime_of_isPrime_disjoint S FibreRing I' hI' hd
  let : Field (FibreRing ⧸ J) := fieldOfFiniteDimensional SeedField _
  let : Module.IsTorsionFree SeedField (FibreRing ⧸ J) :=
    DivisionSemiring.to_moduleIsTorsionFree
  let emb : (FibreRing ⧸ J) →ₐ[SeedField] GenericClosure := IsAlgClosed.lift
  refine ⟨emb.comp (Ideal.Quotient.mkₐ SeedField J), ?_, ?_⟩
  · change RingHom.ker (emb.toRingHom.comp ((Ideal.Quotient.mk J).comp g)) = I
    rw [RingHom.ker_comp_of_injective _ emb.injective, ← RingHom.comap_ker, Ideal.mk_ker,
      hg, ← Ideal.comap_comap, hJ, hcontract]
    exact Ideal.comap_map_of_bijective _ e.bijective
  · intro x
    exact (separable_of_small_rank (FibreRing ⧸ J) hsize (Ideal.Quotient.mk J x)).map
      emb emb.injective
theorem seedPoint (f : FibreRing →ₐ[SeedField] GenericClosure) :
    genericSeedPoint (f (MvPolynomial.X 0)) (f (MvPolynomial.X 1)) =
      f.toRingHom.comp mapGenericSeed := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [genericSeedPoint, mapGenericSeed, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    change algebraMap FX GenericClosure c =
      f (algebraMap SeedField FibreRing (algebraMap FX SeedField c))
    rw [f.commutes, ← IsScalarTower.algebraMap_apply FX SeedField GenericClosure]
  · intro i
    fin_cases i <;> simp [genericSeedPoint, mapGenericSeed, ← MvPolynomial.algebraMap_eq]
theorem jetPoint (f : FibreRing →ₐ[SeedField] GenericClosure) :
    genericJetPoint (f (MvPolynomial.X 0)) (f (MvPolynomial.X 1)) =
      f.toRingHom.comp mapGenericJets := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [genericJetPoint, mapGenericJets, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    change algebraMap FX GenericClosure c =
      f (algebraMap SeedField FibreRing (algebraMap FX SeedField c))
    rw [f.commutes, ← IsScalarTower.algebraMap_apply FX SeedField GenericClosure]
  · intro i
    fin_cases i <;> simp [genericJetPoint, mapGenericJets, ← MvPolynomial.algebraMap_eq]
end
end K1_14_2_6_1
end
section
namespace K1_14_2_6_2
noncomputable section
open K1_14 K1_14_2 K1_14_2_6
open scoped BigOperators nonZeroDivisors
private abbrev Dual := TrivSqZeroExt GenericClosure GenericClosure
private def basePoint (j : Fin 2) : Seeds →+* Dual :=
  MvPolynomial.eval₂Hom
    ((TrivSqZeroExt.inlHom GenericClosure GenericClosure).comp (algebraMap FX GenericClosure))
    (fun i => ⟨algebraMap SeedField GenericClosure (generic i), if i = j then 1 else 0⟩)
private abbrev residue : Dual →+* GenericClosure :=
  (TrivSqZeroExt.fstHom GenericClosure GenericClosure GenericClosure).toRingHom
private theorem basePoint_C (j : Fin 2) (x : FX) :
    basePoint j (MvPolynomial.C x) = TrivSqZeroExt.inl (algebraMap FX GenericClosure x) :=
  MvPolynomial.eval₂Hom_C _ _ _
private theorem basePoint_X (i j : Fin 2) :
    basePoint j (MvPolynomial.X i) =
      ⟨algebraMap SeedField GenericClosure (generic i), if i = j then 1 else 0⟩ :=
  MvPolynomial.eval₂Hom_X' _ _ _
private theorem residue_basePoint (j : Fin 2) :
    residue.comp (basePoint j) = toGenericClosure := by
  apply MvPolynomial.ringHom_ext
  · intro x
    rw [RingHom.comp_apply, basePoint_C]
    change algebraMap FX GenericClosure x =
      algebraMap SeedField GenericClosure (algebraMap Seeds SeedField (algebraMap FX Seeds x))
    exact (IsScalarTower.algebraMap_apply FX Seeds GenericClosure x).trans
      (IsScalarTower.algebraMap_apply Seeds SeedField GenericClosure _)
  · intro i
    rw [RingHom.comp_apply, basePoint_X]
    rfl
private theorem basePoint_units (j : Fin 2) (s : Seeds⁰) : IsUnit (basePoint j s) := by
  apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
  apply isUnit_iff_ne_zero.mpr
  change residue (basePoint j s) ≠ 0
  rw [← RingHom.comp_apply, residue_basePoint]
  have hi : Function.Injective toGenericClosure :=
    (algebraMap SeedField GenericClosure).injective.comp (IsFractionRing.injective Seeds SeedField)
  intro hz
  exact nonZeroDivisors.ne_zero s.property (hi (hz.trans (map_zero toGenericClosure).symm))
private def baseLift (j : Fin 2) : SeedField →+* Dual :=
  IsLocalization.lift (basePoint_units j)
private theorem residue_baseLift (j : Fin 2) :
    residue.comp (baseLift j) = algebraMap SeedField GenericClosure := by
  apply IsLocalization.ringHom_ext Seeds⁰
  apply RingHom.ext
  intro s
  simp only [RingHom.comp_apply, baseLift, IsLocalization.lift_eq]
  change residue (basePoint j s) = toGenericClosure s
  exact DFunLike.congr_fun (residue_basePoint j) s
private theorem baseLift_C (j : Fin 2) (x : FX) :
    baseLift j (algebraMap FX SeedField x) =
      TrivSqZeroExt.inl (algebraMap FX GenericClosure x) := by
  rw [IsScalarTower.algebraMap_apply FX Seeds SeedField, baseLift, IsLocalization.lift_eq]
  exact basePoint_C j x
private theorem baseLift_generic (i j : Fin 2) :
    baseLift j (generic i) =
      ⟨algebraMap SeedField GenericClosure (generic i), if i = j then 1 else 0⟩ := by
  rw [show baseLift j (generic i) = basePoint j (MvPolynomial.X i) from
    IsLocalization.lift_eq (basePoint_units j) _]
  exact basePoint_X i j
private theorem liftPoint (a b : GenericClosure)
    (ha : IsSeparable SeedField a) (hb : IsSeparable SeedField b) (j : Fin 2) :
    ∃ e : Ambient →+* Dual, residue.comp e = genericJetPoint a b ∧
      (∀ x, e (MvPolynomial.C x) = TrivSqZeroExt.inl (algebraMap FX GenericClosure x)) ∧
      (e (MvPolynomial.X 2)).snd = (if j = 0 then 1 else 0) ∧
      (e (MvPolynomial.X 3)).snd = (if j = 1 then 1 else 0) ∧
      RingHom.ker (genericJetPoint a b) ≤ RingHom.ker e := by
  let E := separableClosure SeedField GenericClosure
  let a' : E := ⟨a, ha⟩
  let b' : E := ⟨b, hb⟩
  let : Algebra SeedField Dual := (baseLift j).toAlgebra
  let red : Dual →ₐ[SeedField] GenericClosure :=
    { residue with commutes' := fun x => DFunLike.congr_fun (residue_baseLift j) x }
  have hred : Function.Surjective red := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  have hnil : IsNilpotent (RingHom.ker red.toRingHom) :=
    ⟨2, TrivSqZeroExt.kerIdeal_sq GenericClosure GenericClosure⟩
  let : Algebra.FormallyEtale SeedField E := Algebra.FormallyEtale.of_isSeparable _ _
  let ext : E →ₐ[SeedField] Dual :=
    Algebra.FormallySmooth.liftOfSurjective E.val red hred hnil
  have hext (x : E) : residue (ext x) = E.val x :=
    Algebra.FormallySmooth.liftOfSurjective_apply E.val red hred hnil x
  let point : Ambient →+* E :=
    MvPolynomial.eval₂Hom (algebraMap FX E)
      ![a', b', algebraMap SeedField E (generic 0), algebraMap SeedField E (generic 1)]
  have hpoint : E.val.toRingHom.comp point = genericJetPoint a b := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp [point, genericJetPoint]
    · intro i
      fin_cases i <;> simp [point, genericJetPoint, a', b']
  refine ⟨ext.toRingHom.comp point, ?_, ?_, ?_, ?_, ?_⟩
  · apply RingHom.ext
    intro Q
    exact (hext (point Q)).trans (DFunLike.congr_fun hpoint Q)
  · intro x
    change ext (point (MvPolynomial.C x)) = _
    rw [show point (MvPolynomial.C x) = algebraMap FX E x from MvPolynomial.eval₂Hom_C ..,
      IsScalarTower.algebraMap_apply FX SeedField E, AlgHom.commutes]
    exact baseLift_C j x
  · change (ext (point (MvPolynomial.X 2))).snd = _
    rw [show point (MvPolynomial.X 2) = algebraMap SeedField E (generic 0) by simp [point],
      AlgHom.commutes]
    change (baseLift j (generic 0)).snd = _
    rw [baseLift_generic]
    simp [eq_comm]
  · change (ext (point (MvPolynomial.X 3))).snd = _
    rw [show point (MvPolynomial.X 3) = algebraMap SeedField E (generic 1) by simp [point],
      AlgHom.commutes]
    change (baseLift j (generic 1)).snd = _
    rw [baseLift_generic]
    simp [eq_comm]
  · intro Q hQ
    rw [RingHom.mem_ker] at hQ ⊢
    have hp : E.val (point Q) = 0 := (DFunLike.congr_fun hpoint Q).trans hQ
    change ext (point Q) = 0
    rw [E.val.injective (hp.trans (map_zero E.val).symm), map_zero]
private theorem chain (e : Ambient →+* Dual) (g : Ambient →+* GenericClosure)
    (hg : residue.comp e = g)
    (hc : ∀ x, e (MvPolynomial.C x) = TrivSqZeroExt.inl (algebraMap FX GenericClosure x))
    (Q : Ambient) :
    (e Q).snd = ∑ i : Fin 4, g (MvPolynomial.pderiv i Q) * (e (MvPolynomial.X i)).snd := by
  have hf (P : Ambient) : (e P).fst = g P := DFunLike.congr_fun hg P
  induction Q using MvPolynomial.induction_on with
  | C x => simp [hc]
  | add P Q hP hQ => simp [hP, hQ, add_mul, Finset.sum_add_distrib]
  | mul_X P j hP =>
      simp only [map_mul, TrivSqZeroExt.snd_mul, hf, hP, smul_eq_mul,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, MvPolynomial.pderiv_mul,
        map_add, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]
      have hs : (∑ i : Fin 4,
          g (MvPolynomial.pderiv i (MvPolynomial.X j)) * (e (MvPolynomial.X i)).snd) =
          (e (MvPolynomial.X j)).snd := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro i _ hij
          simp [MvPolynomial.pderiv_X_of_ne hij.symm]
        · simp
      rw [hs]
      rw [add_comm]
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
theorem tangentStep {I : Ideal Ambient} (hI : SeparableJetFibre I)
    {Q : Ambient} (hQ : Q ∈ I) (h0 : MvPolynomial.pderiv 0 Q ∈ I)
    (h1 : MvPolynomial.pderiv 1 Q ∈ I) :
    MvPolynomial.pderiv 2 Q ∈ I ∧ MvPolynomial.pderiv 3 Q ∈ I := by
  obtain ⟨a, b, hker, ha, hb⟩ := hI
  subst I
  let g := genericJetPoint a b
  have hzero (j : Fin 2) :
      (if j = 0 then g (MvPolynomial.pderiv 2 Q) else 0) +
        (if j = 1 then g (MvPolynomial.pderiv 3 Q) else 0) = 0 := by
    obtain ⟨e, he, hC, h2, h3, hker⟩ := liftPoint a b ha hb j
    have key := chain e g he hC Q
    rw [RingHom.mem_ker.mp (hker hQ)] at key
    rw [Fin.sum_univ_four] at key
    rw [RingHom.mem_ker.mp h0, RingHom.mem_ker.mp h1, h2, h3] at key
    fin_cases j <;> simpa using key.symm
  exact ⟨RingHom.mem_ker.mpr (by simpa using hzero 0),
    RingHom.mem_ker.mpr (by simpa using hzero 1)⟩
end
end K1_14_2_6_2
end
section
namespace K1_14_2_6_2
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_6 Polynomial
abbrev coordDeriv (i : Fin 4) : Ambient → Ambient := MvPolynomial.pderiv i
private theorem derivative_eval {R : Type*} [CommRing R]
    (f : Ambient →+* (Polynomial R)) (i : Fin 4)
    (hC : ∀ x, derivative (f (MvPolynomial.C x)) = 0)
    (hX : ∀ j, derivative (f (MvPolynomial.X j)) = f (coordDeriv i (MvPolynomial.X j))) :
    Function.Semiconj f (coordDeriv i) derivative := by
  intro Q
  induction Q using MvPolynomial.induction_on with
  | C x => simp [coordDeriv, hC]
  | add P Q hP hQ =>
    simpa only [coordDeriv, map_add, derivative_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P j hP =>
    simp only [coordDeriv, MvPolynomial.pderiv_mul, map_add, map_mul, derivative_mul, hP, hX]
def seedIndex (i : Fin 2) : Fin 4 := Fin.castLE (by decide) i
private def translation (i : Fin 4) : Ambient →+* (Polynomial Ambient) :=
  MvPolynomial.eval₂Hom (C.comp MvPolynomial.C)
    (fun j => C (MvPolynomial.X j : Ambient) + if j = i then Polynomial.X (R := Ambient) else 0)
private theorem translation_zero (i : Fin 4) (Q : Ambient) :
    (translation i Q).coeff 0 = Q := by
  have h : (evalRingHom (0 : Ambient)).comp (translation i) = RingHom.id Ambient := by
    apply MvPolynomial.ringHom_ext
    · simp [translation]
    · intro j
      by_cases hj : j = i <;> simp [translation, hj]
  rw [coeff_zero_eq_eval_zero]
  exact DFunLike.congr_fun h Q
private theorem translation_derivative (i : Fin 4) :
    Function.Semiconj (translation i) (coordDeriv i) derivative := by
  apply derivative_eval
  · simp [translation]
  · intro j
    by_cases h : j = i <;> simp [translation, coordDeriv, h]
private def seedIncl : Seeds →+* Ambient := rootIncl.comp rootSeeds
private theorem rootIncl_X (k : Fin 3) :
    rootIncl (MvPolynomial.X k) = MvPolynomial.X (Fin.castLE (by decide) k) := by
  simp [rootIncl]
private theorem toJet_sum (P : Jet) :
    toJet P = P.sum fun j g =>
      (g.sum fun k c => seedIncl c * MvPolynomial.X 2 ^ k) * MvPolynomial.X 3 ^ j := by
  simp only [toJet, toRoot, coe_eval₂RingHom, eval₂_eq_sum, RingHom.comp_apply,
    Polynomial.sum, map_sum, map_mul, map_pow, seedIncl, rootIncl_X]
  rfl
private theorem translation_seed (i : Fin 2) (c : Seeds) :
    translation (seedIndex i) (seedIncl c) = (translateSeed i c).map seedIncl := by
  have h : (translation (seedIndex i)).comp seedIncl =
      (mapRingHom seedIncl).comp (translateSeed i) := by
    apply MvPolynomial.ringHom_ext
    · simp [translation, translateSeed, seedIncl, rootIncl, rootSeeds]
    · intro j
      fin_cases i <;> fin_cases j <;>
        simp [translation, translateSeed, seedIncl, rootIncl, rootSeeds, seedIndex]
  exact DFunLike.congr_fun h c
private theorem translation_toJet (i : Fin 2) (r : ℕ) (P : Jet) :
    (translation (seedIndex i) (toJet P)).coeff r = toJet (seedHasse i r P) := by
  have hY : translation (seedIndex i) (MvPolynomial.X 2) = C (MvPolynomial.X 2) := by
    fin_cases i <;> simp [translation, seedIndex]
  have hV : translation (seedIndex i) (MvPolynomial.X 3) = C (MvPolynomial.X 3) := by
    fin_cases i <;> simp [translation, seedIndex]
  have hYpow (k : ℕ) :
      translation (seedIndex i) (MvPolynomial.X 2 ^ k) = C (MvPolynomial.X 2 ^ k) := by
    rw [map_pow, hY, ← C_pow]
  have hVpow (j : ℕ) :
      translation (seedIndex i) (MvPolynomial.X 3 ^ j) = C (MvPolynomial.X 3 ^ j) := by
    rw [map_pow, hV, ← C_pow]
  have hm (j k : ℕ) (c : Seeds) :
      toJet (monomial j (monomial k c)) = seedIncl c * MvPolynomial.X 2 ^ k *
        MvPolynomial.X 3 ^ j := by
    simp [toJet, toRoot, eval₂_monomial, seedIncl, rootIncl_X]
  conv_lhs => rw [toJet_sum]
  simp only [seedHasse, Polynomial.sum, map_sum, map_mul, hm, hYpow, hVpow,
    finsetSum_coeff, coeff_mul_C, translation_seed, coeff_map, Finset.sum_mul]
theorem seed_iter (i : Fin 2) (r : ℕ) (P : Jet) :
    (coordDeriv (seedIndex i))^[r] (toJet P) = r.factorial • toJet (seedHasse i r P) := by
  have h := (translation_derivative (seedIndex i)).iterate_right r (toJet P)
  have hc := congrArg (fun Q : (Polynomial Ambient) => Q.coeff 0) h
  simpa only [translation_zero, coeff_iterate_derivative, Nat.zero_add,
    Nat.descFactorial_self, translation_toJet] using hc
private def yFibre (v : GenericClosure) : Ambient →+* (Polynomial GenericClosure) :=
  MvPolynomial.eval₂Hom (C.comp (algebraMap FX GenericClosure))
    ![C (algebraMap SeedField GenericClosure (generic 0)),
      C (algebraMap SeedField GenericClosure (generic 1)), Polynomial.X, C v]
private def vFibre : Ambient →+* Polynomial (Polynomial GenericClosure) :=
  MvPolynomial.eval₂Hom (C.comp (C.comp (algebraMap FX GenericClosure)))
    ![C (C (algebraMap SeedField GenericClosure (generic 0))),
      C (C (algebraMap SeedField GenericClosure (generic 1))), C (Polynomial.X (R := GenericClosure)), Polynomial.X]
private theorem yFibre_derivative (v : GenericClosure) :
    Function.Semiconj (yFibre v) (coordDeriv 2) derivative := by
  apply derivative_eval
  · simp [yFibre]
  · intro j
    fin_cases j <;> simp [yFibre, coordDeriv, MvPolynomial.pderiv_X]
private theorem vFibre_derivative :
    Function.Semiconj vFibre (coordDeriv 3) derivative := by
  apply derivative_eval
  · simp [vFibre]
  · intro j
    fin_cases j <;> simp [vFibre, coordDeriv, MvPolynomial.pderiv_X]
private theorem eval_yFibre (y v : GenericClosure) :
    (evalRingHom y).comp (yFibre v) = genericSeedPoint y v := by
  apply MvPolynomial.ringHom_ext
  · simp [yFibre, genericSeedPoint]
  · intro j
    fin_cases j <;> simp [yFibre, genericSeedPoint]
private theorem eval_vFibre (v : GenericClosure) :
    (evalRingHom (C v)).comp vFibre = yFibre v := by
  apply MvPolynomial.ringHom_ext
  · simp [yFibre, vFibre]
  · intro j
    fin_cases j <;> simp [yFibre, vFibre]
private theorem vFibre_toJet (P : Jet) : vFibre (toJet P) = fibreRow P := by
  have hs : vFibre.comp seedIncl = C.comp (C.comp toGenericClosure) := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp [vFibre, seedIncl, rootIncl, rootSeeds, toGenericClosure,
        ← IsScalarTower.algebraMap_apply]
      exact IsScalarTower.algebraMap_apply FX Seeds GenericClosure x
    · intro j
      fin_cases j <;> simp [vFibre, seedIncl, rootIncl, rootSeeds, toGenericClosure, generic]
  have hy : vFibre.comp (rootIncl.comp toRoot) = C.comp (mapRingHom toGenericClosure) := by
    apply Polynomial.ringHom_ext
    · intro c
      change vFibre (rootIncl (toRoot (C c))) = _
      simpa [toRoot, seedIncl] using DFunLike.congr_fun hs c
    · simp [toRoot, vFibre, rootIncl_X]
  change vFibre (P.eval₂ (rootIncl.comp toRoot) (MvPolynomial.X 3)) = _
  rw [Polynomial.hom_eval₂, hy, show vFibre (MvPolynomial.X 3) = Polynomial.X by simp [vFibre]]
  rfl
theorem eval_jet_iter (P : Jet) (a b : ℕ) (y v : GenericClosure) :
    genericSeedPoint y v ((coordDeriv 2)^[a] ((coordDeriv 3)^[b] (toJet P))) =
      a.factorial • b.factorial •
        (hasseDeriv a ((hasseDeriv b (fibreRow P)).eval (C v))).eval y := by
  rw [← eval_yFibre, RingHom.comp_apply,
    (yFibre_derivative v).iterate_right a,
    ← eval_vFibre, RingHom.comp_apply,
    vFibre_derivative.iterate_right b, vFibre_toJet]
  rw [← factorial_smul_hasseDeriv, ← factorial_smul_hasseDeriv]
  simp only [LinearMap.coe_smul, Pi.smul_apply, map_nsmul, coe_evalRingHom]
  exact smul_comm _ _ _
end
end K1_14_2_6_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
namespace K1_14_3R_1
noncomputable section
open K1_14 K1_14_3 K1_14_2 Polynomial
local notation "SF" => K1_14_3.SeedField
def jetCoordinates : Seeds ≃+* JetPlane :=
  ((MvPolynomial.renameEquiv FX (Equiv.swap (0 : Fin 2) 1)).trans
    (MvPolynomial.finSuccEquiv FX 1)).toRingEquiv.trans
    (Polynomial.mapEquiv (MvPolynomial.uniqueAlgEquiv FX (Fin 1)).toRingEquiv)
private theorem jetCoordinates_C (x : FX) :
    jetCoordinates (MvPolynomial.C x) = C (C x) := by
  change (MvPolynomial.finSuccEquiv FX 1
    (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) (MvPolynomial.C x))).map
      (MvPolynomial.uniqueAlgEquiv FX (Fin 1)).toRingHom = _
  simp [MvPolynomial.finSuccEquiv_apply]
private theorem jetCoordinates_X0 :
    jetCoordinates (MvPolynomial.X 0) = C (Polynomial.X (R := FX)) := by
  change (MvPolynomial.finSuccEquiv FX 1
    (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) (MvPolynomial.X 0))).map
      (MvPolynomial.uniqueAlgEquiv FX (Fin 1)).toRingHom = _
  rw [MvPolynomial.rename_X, Equiv.swap_apply_left]
  rw [show (1 : Fin 2) = (0 : Fin 1).succ from rfl, MvPolynomial.finSuccEquiv_X_succ]
  simp
private theorem jetCoordinates_X1 :
    jetCoordinates (MvPolynomial.X 1) = Polynomial.X := by
  change (MvPolynomial.finSuccEquiv FX 1
    (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) (MvPolynomial.X 1))).map
      (MvPolynomial.uniqueAlgEquiv FX (Fin 1)).toRingHom = _
  rw [MvPolynomial.rename_X, Equiv.swap_apply_right, MvPolynomial.finSuccEquiv_X_zero, map_X]
def fractionCoordinates : JetField ≃+* SF :=
  IsFractionRing.ringEquivOfRingEquiv (A := JetPlane) (K := JetField)
    (B := Seeds) (L := SF) jetCoordinates.symm
private abbrev toJetField := algebraMap JetPlane JetField
private abbrev toSeedField : Seeds →+* SF := algebraMap Seeds SF
private theorem fractionCoordinates_apply (x : JetPlane) :
    fractionCoordinates (toJetField x) = toSeedField (jetCoordinates.symm x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (A := JetPlane) (K := JetField)
    (B := Seeds) (L := SF) jetCoordinates.symm x
set_option backward.isDefEq.respectTransparency true
private theorem jet_hom_ext {T : Type*} [CommSemiring T] {g h : Jet →+* T}
    (hc : ∀ x : FX, g (C (C (MvPolynomial.C x))) = h (C (C (MvPolynomial.C x))))
    (hs : ∀ i : Fin 2, g (C (C (MvPolynomial.X i))) = h (C (C (MvPolynomial.X i))))
    (hy : g (C (Polynomial.X (R := Seeds))) = h (C (Polynomial.X (R := Seeds))))
    (hv : g Polynomial.X = h Polynomial.X) : g = h := by
  apply Polynomial.ringHom_ext' _ hv
  apply Polynomial.ringHom_ext' _ hy
  exact MvPolynomial.ringHom_ext (fun x => hc x) (fun i => hs i)
@[simp] theorem toJet_C (x : FX) :
    toJet (C (C (MvPolynomial.C x))) = MvPolynomial.C x := by
  simp [toJet, toRoot, rootIncl, rootSeeds]
@[simp] theorem toJet_seed (i : Fin 2) :
    toJet (C (C (MvPolynomial.X i))) = MvPolynomial.X (Fin.castLE (by decide) i) := by
  fin_cases i <;> simp [toJet, toRoot, rootIncl, rootSeeds]
@[simp] theorem toJet_y :
    toJet (C (Polynomial.X (R := Seeds))) = MvPolynomial.X 2 := by
  simp [toJet, toRoot, rootIncl]
@[simp] theorem toJet_v :
    toJet (Polynomial.X (R := Equation)) = MvPolynomial.X 3 := by
  simp [toJet]
private theorem toJet_surjective : Function.Surjective toJet := by
  intro Q
  induction Q using MvPolynomial.induction_on with
  | C x => exact ⟨C (C (MvPolynomial.C x)), toJet_C x⟩
  | add P Q hP hQ =>
    obtain ⟨P', rfl⟩ := hP
    obtain ⟨Q', rfl⟩ := hQ
    exact ⟨P' + Q', map_add _ _ _⟩
  | mul_X P i hP =>
    obtain ⟨P', rfl⟩ := hP
    have hX : ∃ j, toJet j = MvPolynomial.X i := by
      fin_cases i
      · exact ⟨_, toJet_seed 0⟩
      · exact ⟨_, toJet_seed 1⟩
      · exact ⟨_, toJet_y⟩
      · exact ⟨_, toJet_v⟩
    obtain ⟨j, hj⟩ := hX
    exact ⟨P' * j, by rw [map_mul, hj]⟩
theorem seedGeneric_C (x : FX) :
    seedGeneric (MvPolynomial.C x) = algebraMap FX SeedClosure x := by
  change algebraMap SF SeedClosure (algebraMap Seeds SF (algebraMap FX Seeds x)) = _
  rw [← IsScalarTower.algebraMap_apply Seeds SF SeedClosure,
    ← IsScalarTower.algebraMap_apply FX Seeds SeedClosure]
theorem seed_chart (y v : SeedClosure) :
    (K1_14_2_6.genericSeedPoint y v).comp toJet = seedFibreEval y v := by
  apply jet_hom_ext
  · intro x
    simp [K1_14_2_6.genericSeedPoint, seedFibreEval, seedGeneric_C]
  · intro i
    fin_cases i <;>
      simp [K1_14_2_6.genericSeedPoint, seedFibreEval, seedGeneric, K1_14_2.generic]
  · simp [K1_14_2_6.genericSeedPoint, seedFibreEval]
  · simp [K1_14_2_6.genericSeedPoint, seedFibreEval]
theorem seed_chart_ker {q : Surface} {y v : SeedClosure} (h : OnSeedFibre q y v) :
    (RingHom.ker (K1_14_2_6.genericSeedPoint y v)).comap toJet = q.asIdeal := by
  rw [RingHom.comap_ker, seed_chart, h]
theorem generic_C (x : FX) : jetCoordinates.symm (C (C x)) = MvPolynomial.C x :=
  jetCoordinates.symm_apply_eq.mpr (jetCoordinates_C x).symm
theorem generic_Y : jetCoordinates.symm (C (Polynomial.X (R := FX))) = MvPolynomial.X 0 :=
  jetCoordinates.symm_apply_eq.mpr jetCoordinates_X0.symm
theorem generic_V : jetCoordinates.symm (Polynomial.X (R := Polynomial FX)) =
    MvPolynomial.X 1 :=
  jetCoordinates.symm_apply_eq.mpr jetCoordinates_X1.symm
theorem jet_chart {q : Surface} (h : Parent q) {y v : SeedClosure}
    (hyv : OnSeedFibre q y v) :
    K1_14_2_6.SeparableJetFibre (RingHom.ker (K1_14_2_6.genericSeedPoint y v)) := by
  obtain ⟨g, hg, hker, hsep⟩ := h.jet_side
  let : Algebra JetField SF := fractionCoordinates.toRingHom.toAlgebra
  let l : JetClosure →ₐ[JetField] SeedClosure :=
    IsAlgClosed.lift (R := JetField) (S := JetClosure) (M := SeedClosure)
  let a (i : Fin 2) := l (g (C (C (MvPolynomial.X i))))
  have hmap (x : JetPlane) :
      l (g (fixedEmbedding x)) = seedGeneric (jetCoordinates.symm x) := by
    rw [show g (fixedEmbedding x) = jetGeneric x from DFunLike.congr_fun hg x]
    change l (algebraMap JetField JetClosure (toJetField x)) = _
    rw [l.commutes, IsScalarTower.algebraMap_apply JetField SF SeedClosure]
    change algebraMap SF SeedClosure (fractionCoordinates (toJetField x)) = _
    exact congrArg (algebraMap SF SeedClosure) (fractionCoordinates_apply x)
  have hchart : (K1_14_2_6.genericJetPoint (a 0) (a 1)).comp toJet =
      l.toRingHom.comp g := by
    apply jet_hom_ext
    · intro x
      simpa [K1_14_2_6.genericJetPoint, fixedEmbedding, generic_C, seedGeneric_C] using
        (hmap (C (C x))).symm
    · intro i
      fin_cases i <;> simp [K1_14_2_6.genericJetPoint, a]
    · simpa [K1_14_2_6.genericJetPoint, fixedEmbedding, generic_Y,
        seedGeneric, K1_14_2.generic] using
        (hmap (C (Polynomial.X (R := FX)))).symm
    · simpa [K1_14_2_6.genericJetPoint, fixedEmbedding, generic_V,
        seedGeneric, K1_14_2.generic] using
        (hmap (Polynomial.X (R := Polynomial FX))).symm
  have hsep' (x : JetClosure) (hx : IsSeparable JetField x) : IsSeparable SF (l x) := by
    have hx' : (minpoly JetField x).Separable := hx
    apply (hx'.map (f := fractionCoordinates.toRingHom)).of_dvd
    apply minpoly.dvd
    rw [aeval_def, Polynomial.eval₂_map]
    change (minpoly JetField x).eval₂
      ((algebraMap SF SeedClosure).comp (algebraMap JetField SF)) (l x) = 0
    rw [← IsScalarTower.algebraMap_eq JetField SF SeedClosure, ← aeval_def,
      aeval_algHom_apply l, minpoly.aeval, map_zero]
  refine ⟨a 0, a 1, ?_, hsep' _ (hsep 0), hsep' _ (hsep 1)⟩
  have hc : (RingHom.ker (K1_14_2_6.genericJetPoint (a 0) (a 1))).comap toJet =
      (RingHom.ker (K1_14_2_6.genericSeedPoint y v)).comap toJet := by
    rw [seed_chart_ker hyv, RingHom.comap_ker, hchart, RingHom.ker_comp_of_injective _ l.injective,
      hker]
  ext Q
  obtain ⟨P, rfl⟩ := toJet_surjective Q
  exact Iff.of_eq (congrArg (fun I : Ideal Jet => P ∈ I) hc)
end
end K1_14_3R_1
end
section
namespace K1_14_2_6_2
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_6
private theorem partial_commute (i j : Fin 4) : Function.Commute (coordDeriv i) (coordDeriv j) := by
  intro Q
  by_cases hij : i = j
  · subst j
    rfl
  apply MvPolynomial.ext
  intro d
  simp only [coordDeriv, MvPolynomial.coeff_pderiv, Finsupp.add_apply, Finsupp.single_apply,
    ite_eq_right hij, ite_eq_right (Ne.symm hij), add_zero]
  rw [add_right_comm d (Finsupp.single i 1) (Finsupp.single j 1)]
  ring
private def mixed (P : Jet) (a b c d : ℕ) : Ambient :=
  (coordDeriv 2)^[c] ((coordDeriv 3)^[d] ((coordDeriv 0)^[a] ((coordDeriv 1)^[b] (toJet P))))
private theorem mixed_seed0 (P : Jet) (a b c d : ℕ) :
    coordDeriv 0 (mixed P a b c d) = mixed P (a+1) b c d := by
  unfold mixed
  rw [((partial_commute 0 2).iterate_right c).eq, ((partial_commute 0 3).iterate_right d).eq,
    Function.iterate_succ_apply']
private theorem mixed_seed1 (P : Jet) (a b c d : ℕ) :
    coordDeriv 1 (mixed P a b c d) = mixed P a (b+1) c d := by
  unfold mixed
  rw [((partial_commute 1 2).iterate_right c).eq, ((partial_commute 1 3).iterate_right d).eq,
    ((partial_commute 1 0).iterate_right a).eq, Function.iterate_succ_apply']
private theorem mixed_jet3 (P : Jet) (a b c d : ℕ) :
    coordDeriv 3 (mixed P a b c d) = mixed P a b c (d+1) := by
  unfold mixed
  rw [((partial_commute 3 2).iterate_right c).eq, Function.iterate_succ_apply']
private theorem mixed_base (P : Jet) (a b : ℕ) :
    mixed P a b 0 0 = b.factorial • a.factorial • toJet (seedHasse 0 a (seedHasse 1 b P)) := by
  have hcomm : Function.Commute (fun Q : Ambient => b.factorial • Q) (coordDeriv 0) :=
    fun Q => (map_nsmul (MvPolynomial.pderiv (R := FX) (0 : Fin 4)) b.factorial Q).symm
  have h0 (Q : Jet) :
      (coordDeriv 0)^[a] (toJet Q) = a.factorial • toJet (seedHasse 0 a Q) := seed_iter 0 a Q
  have h1 :
      (coordDeriv 1)^[b] (toJet P) = b.factorial • toJet (seedHasse 1 b P) := seed_iter 1 b P
  simp only [mixed, Function.iterate_zero_apply, h1, ← (hcomm.iterate_right a).eq, h0]
private theorem mixed_contact {I : Ideal Ambient} (hI : SeparableJetFibre I)
    {P : Jet} {m : ℕ} (hP : HasSeedContact I P m) :
    ∀ a b c d, a+b+c+d < m → mixed P a b c d ∈ I := by
  suffices ∀ k a b c d, c+d = k → a+b+c+d < m → mixed P a b c d ∈ I by
    exact fun a b c d h => this (c+d) a b c d rfl h
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    have step (a b c d : ℕ) (hk : c+d < k) (ht : a+b+c+d+1 < m) :
        coordDeriv 2 (mixed P a b c d) ∈ I ∧ coordDeriv 3 (mixed P a b c d) ∈ I := by
      apply tangentStep hI (ih (c+d) hk a b c d rfl (by omega))
      · change coordDeriv 0 (mixed P a b c d) ∈ I
        rw [mixed_seed0]
        exact ih (c+d) hk (a+1) b c d rfl (by omega)
      · change coordDeriv 1 (mixed P a b c d) ∈ I
        rw [mixed_seed1]
        exact ih (c+d) hk a (b+1) c d rfl (by omega)
    intro a b c d hk ht
    cases c with
    | succ c =>
      have h := (step a b c d (by omega) (by omega)).1
      simpa only [mixed, Function.iterate_succ_apply'] using h
    | zero =>
      cases d with
      | zero =>
        rw [mixed_base]
        exact nsmul_mem (nsmul_mem (hP a b (by omega)) _) _
      | succ d =>
        exact (mixed_jet3 P a b 0 d) ▸ (step a b 0 d (by omega) (by omega)).2
theorem proof : K1_14_2_6.c2 := by
  intro I hI P m hm hP y v hy a b hab
  have h := mixed_contact hI hP 0 0 a b (by omega)
  have hev : genericSeedPoint y v ((coordDeriv 2)^[a] ((coordDeriv 3)^[b] (toJet P))) = 0 := by
    apply RingHom.mem_ker.mp
    rw [show RingHom.ker (genericSeedPoint y v) = I from hy]
    simpa only [mixed, Function.iterate_zero_apply] using h
  rw [eval_jet_iter] at hev
  simp only [nsmul_eq_mul] at hev
  let : CharP GenericClosure p := charP_of_injective_ringHom (algebraMap K GenericClosure).injective p
  have hp := CharP.char_is_prime_of_two_le K p (by decide)
  have hfac (n : ℕ) (hn : n < p) : (n.factorial : GenericClosure) ≠ 0 := by
    intro hz
    exact (not_le_of_gt hn) (hp.dvd_factorial.mp ((CharP.cast_eq_zero_iff GenericClosure p _).mp hz))
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hev).resolve_left (hfac a (by omega)))).resolve_left
    (hfac b (by omega))
end
end K1_14_2_6_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace K1_14_2_3_2
noncomputable section
open K1_14 K1_14_2 Polynomial
open scoped BigOperators
private abbrev liftCoeffs : Seeds →+* MvPolynomial (Fin 2) SeedField :=
  MvPolynomial.map (algebraMap FX SeedField)
private def intercept : (Polynomial SeedField) :=
  Polynomial.C (generic 1) - Polynomial.C (generic 0) * Polynomial.X
private def substitute : MvPolynomial (Fin 2) SeedField →ₐ[SeedField] (Polynomial SeedField) :=
  MvPolynomial.aeval ![intercept, Polynomial.X]
private def sliced (P : Seeds) : (Polynomial SeedField) := substitute (liftCoeffs P)
private theorem slope_eval_injective :
    Function.Injective (Polynomial.eval₂RingHom (algebraMap FX SeedField) (-generic 0)) := by
  let f : (Polynomial FX) →+* Seeds := Polynomial.eval₂RingHom MvPolynomial.C (-MvPolynomial.X 0)
  let g : Seeds →+* (Polynomial FX) :=
    MvPolynomial.eval₂Hom Polynomial.C ![-Polynomial.X, 0]
  have hfg : g.comp f = RingHom.id _ := by
    apply Polynomial.ringHom_ext
    · intro r
      simp [f, g, Polynomial.coe_eval₂RingHom]
    · simp [f, g, Polynomial.coe_eval₂RingHom]
  have hf : Function.LeftInverse g f := fun x => RingHom.congr_fun hfg x
  have he : (algebraMap Seeds SeedField).comp f =
      Polynomial.eval₂RingHom (algebraMap FX SeedField) (-generic 0) := by
    apply Polynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, f, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      rw [IsScalarTower.algebraMap_apply FX Seeds SeedField]
      rfl
    · simp [f, Polynomial.coe_eval₂RingHom, generic]
  rw [← he]
  exact (IsFractionRing.injective Seeds SeedField).comp hf.injective
private theorem sum_exponents (m : Fin 2 →₀ ℕ) : m.sum (fun _ n => n) = m 0 + m 1 := by
  simp [Finsupp.sum_of_support_subset m (Finset.subset_univ m.support)]
private theorem sliced_natDegree (P : Seeds) (hP : P ≠ 0) :
    (sliced P).natDegree = P.totalDegree := by
  classical
  let d := P.totalDegree
  let term (m : Fin 2 →₀ ℕ) :=
    Polynomial.C (algebraMap FX SeedField (P.coeff m)) * intercept ^ m 0 * Polynomial.X ^ m 1
  have hsum : sliced P = ∑ m ∈ P.support, term m := by
    conv_lhs => rw [sliced, P.as_sum, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [MvPolynomial.map_monomial]
    simp only [substitute, MvPolynomial.aeval_def, MvPolynomial.eval₂_monomial,
      term, Polynomial.algebraMap_eq]
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
    simp [mul_assoc]
  have hi : intercept.natDegree ≤ 1 := by
    unfold intercept
    have hm : (Polynomial.C (generic 0) * Polynomial.X).natDegree ≤ 1 :=
      (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
    simpa using Polynomial.natDegree_sub_le_of_le (p := Polynomial.C (generic 1))
      (show (Polynomial.C (generic 1)).natDegree ≤ 1 from by simp) hm
  have hi₁ : intercept.coeff 1 = -generic 0 := by
    simp [intercept]
  have hterm (m : Fin 2 →₀ ℕ) : (term m).natDegree ≤ m 0 + m 1 := by
    apply Polynomial.natDegree_mul_le_of_le
    · exact (Polynomial.natDegree_C_mul_le _ _).trans
        (by simpa using Polynomial.natDegree_pow_le_of_le (m 0) hi)
    · simp
  have hle (m : Fin 2 →₀ ℕ) (hm : m ∈ P.support) : m 0 + m 1 ≤ d := by
    simpa only [sum_exponents] using MvPolynomial.le_totalDegree hm
  refine le_antisymm ?_ (Polynomial.le_natDegree_of_ne_zero ?_)
  · rw [hsum]
    exact Polynomial.natDegree_sum_le_of_forall_le _ _ (fun m hm => (hterm m).trans (hle m hm))
  let top := P.support.filter (fun m => m 0 + m 1 = d)
  let slopePoly : (Polynomial FX) := ∑ m ∈ top, Polynomial.C (P.coeff m) * Polynomial.X ^ m 0
  have hcoeff :
      (sliced P).coeff d = Polynomial.eval₂RingHom (algebraMap FX SeedField) (-generic 0) slopePoly := by
    dsimp only [slopePoly, top]
    rw [hsum, Polynomial.finsetSum_coeff, map_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases he : m 0 + m 1 = d
    · rw [ite_eq_left he, ← he]
      dsimp only [term]
      rw [Polynomial.coeff_mul_X_pow, Polynomial.coeff_C_mul]
      have hp := Polynomial.coeff_pow_of_natDegree_le (m := m 0) hi
      rw [mul_one] at hp
      rw [hp, hi₁]
      simp [Polynomial.coe_eval₂RingHom]
    · rw [ite_eq_right he, Polynomial.coeff_eq_zero_of_natDegree_lt
        ((hterm m).trans_lt (lt_of_le_of_ne (hle m hm) he))]
  obtain ⟨e, he, hed⟩ := Finset.exists_mem_eq_sup P.support
    (MvPolynomial.support_nonempty.mpr hP) (fun m => m.sum (fun _ n => n))
  have ht : e ∈ top := Finset.mem_filter.mpr ⟨he, by
    change e 0 + e 1 = P.support.sup (fun m => m.sum (fun _ n => n))
    rw [← sum_exponents, hed]⟩
  have hslope : slopePoly ≠ 0 := by
    have hc : slopePoly.coeff (e 0) = P.coeff e := by
      dsimp only [slopePoly]
      rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single_of_mem e ht]
      · simp
      · intro m hm hme
        have hi0 : e 0 ≠ m 0 := by
          intro he0
          have he1 : e 1 = m 1 := by
            have h₁ := (Finset.mem_filter.mp ht).2
            have h₂ := (Finset.mem_filter.mp hm).2
            omega
          apply hme
          ext i
          fin_cases i
          · exact he0.symm
          · exact he1.symm
        simp [hi0]
    exact fun hz => MvPolynomial.mem_support_iff.mp he (by rw [← hc, hz, Polynomial.coeff_zero])
  rw [hcoeff]
  exact fun hz => hslope (slope_eval_injective (hz.trans (map_zero _).symm))
/-- Substitution on the generic seed line, viewed as a polynomial in its free coordinate. -/
def genericSeedLineMap : Seeds →+* SeedField[X] := substitute.toRingHom.comp liftCoeffs

theorem genericSeedLine_degree (P : Seeds) (nz : P ≠ 0) :
    (genericSeedLineMap P).natDegree=P.totalDegree := sliced_natDegree P nz

@[simp] theorem genericSeedLine_C (x:FX) : genericSeedLineMap (MvPolynomial.C x)=C (algebraMap FX SeedField x) := by
  simp [genericSeedLineMap,substitute,liftCoeffs]

@[simp] theorem genericSeedLine_X0 : genericSeedLineMap (MvPolynomial.X 0)=C (generic 1)-C (generic 0)*Polynomial.X := by
  simp [genericSeedLineMap,substitute,liftCoeffs,intercept]

@[simp] theorem genericSeedLine_X1 : genericSeedLineMap (MvPolynomial.X 1)=Polynomial.X := by
  simp [genericSeedLineMap,substitute,liftCoeffs]

private def planeEquiv (P : Seeds) :
    PlaneSeedSection (Ideal.span {P}) ≃ₐ[SeedField] ((Polynomial SeedField) ⧸ Ideal.span {sliced P}) := by
  let J : Ideal (MvPolynomial (Fin 2) SeedField) :=
    (Ideal.span {P}).map liftCoeffs ⊔ Ideal.span {seedLine 0 1}
  let A := MvPolynomial (Fin 2) SeedField ⧸ J
  let B := (Polynomial SeedField) ⧸ Ideal.span {sliced P}
  let j := Ideal.Quotient.mkₐ SeedField J
  let k := Ideal.Quotient.mkₐ SeedField (Ideal.span {sliced P})
  have h0 : substitute (MvPolynomial.X 0) = intercept := by simp [substitute]
  have h1 : substitute (MvPolynomial.X 1) = Polynomial.X := by simp [substitute]
  have hline : substitute (seedLine 0 1) = 0 := by
    simp only [seedLine, map_sub, map_add, map_mul, MvPolynomial.algHom_C,
      h0, h1, Polynomial.algebraMap_eq, intercept, sub_add_cancel, sub_self]
  have hmap : J = Ideal.span {liftCoeffs P} ⊔ Ideal.span {seedLine 0 1} := by
    change (Ideal.span {P}).map liftCoeffs ⊔ _ = _
    rw [Ideal.map_span, Set.image_singleton]
  have hjP : j (liftCoeffs P) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [hmap]
    exact Ideal.mem_sup_left (Ideal.subset_span (Set.mem_singleton _))
  have hjLine : j (seedLine 0 1) = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))
  let f : A →ₐ[SeedField] B := Ideal.Quotient.liftₐ J (k.comp substitute) (by
    intro x hx
    have h : J ≤ RingHom.ker (k.comp substitute).toRingHom := by
      rw [hmap]
      refine sup_le (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
      · rintro x (rfl : x = liftCoeffs P)
        exact RingHom.mem_ker.mpr (Ideal.Quotient.mk_singleton_self _)
      · rintro x (rfl : x = seedLine 0 1)
        apply RingHom.mem_ker.mpr
        change k (substitute _) = 0
        rw [hline, map_zero]
    exact h hx)
  let p : (Polynomial SeedField) →ₐ[SeedField] A := Polynomial.aeval (j (MvPolynomial.X 1))
  have hp : p.comp substitute = j := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · change p (substitute (MvPolynomial.X 0)) = j (MvPolynomial.X 0)
      rw [h0]
      simp only [p, intercept, map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      simp only [seedLine, map_sub, map_add, map_mul, MvPolynomial.algHom_C] at hjLine
      rw [sub_eq_zero] at hjLine
      exact sub_eq_of_eq_add hjLine.symm
    · change p (substitute (MvPolynomial.X 1)) = j (MvPolynomial.X 1)
      rw [h1]
      exact Polynomial.aeval_X _
  let g : B →ₐ[SeedField] A := Ideal.Quotient.liftₐ _ p (by
    intro x hx
    have h : Ideal.span {sliced P} ≤ RingHom.ker p.toRingHom := by
      apply Ideal.span_le.mpr
      rintro x (rfl : x = sliced P)
      exact RingHom.mem_ker.mpr ((DFunLike.congr_fun hp (liftCoeffs P)).trans hjP)
    exact h hx)
  apply AlgEquiv.ofAlgHom f g
  · apply AlgHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h : (f.comp g).comp k = k := by
      apply Polynomial.algHom_ext
      simp only [AlgHom.comp_apply]
      have hg : g (k Polynomial.X) = j (MvPolynomial.X 1) := by
        change p Polynomial.X = j (MvPolynomial.X 1)
        exact Polynomial.aeval_X _
      rw [hg]
      change k (substitute (MvPolynomial.X 1)) = _
      rw [h1]
    exact DFunLike.congr_fun h x
  · apply AlgHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact DFunLike.congr_fun hp x
theorem plane_degree (P : Seeds) (hP : P ≠ 0) :
    Module.finrank SeedField (PlaneSeedSection (Ideal.span {P})) = P.totalDegree := by
  calc
    _ = Module.finrank SeedField ((Polynomial SeedField) ⧸ Ideal.span {sliced P}) :=
      (planeEquiv P).toLinearEquiv.finrank_eq
    _ = _ := finrank_quotient_span_eq_natDegree.trans (sliced_natDegree P hP)
end
end K1_14_2_3_2
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000
namespace K1_14_3_2_4
noncomputable section
open MvPolynomial Polynomial
variable {k : Type*} [Field k]
local notation "Biv" => MvPolynomial (Fin 2) k
end
end K1_14_3_2_4
end
section
namespace K1_13_2_3_2
open K1_13_2 K1_13_2_3 Finset
open scoped BigOperators
private theorem baseline_le_counts (i : BlockIndex) :
    baseline i ≤ (oldCount (initialFlag i)).toNat ∧
    baseline i ≤ (targetCount (initialFlag i)).toNat := by
  have hk : kernelLower (initialFlag i) = oldCount (initialFlag i) - targetCount (initialFlag i) := by
    simp [kernelLower, initialFlag]
  unfold baseline blockBound
  dsimp
  split
  · exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  · let lower := max 0 (max (kernelLower (initialFlag i))
        (kernelLower (residualFlag (initialFlag i) (fun _ => 0))))
    have hzero : 0 ≤ lower := le_max_left _ _
    have hker : kernelLower (initialFlag i) ≤ lower :=
      (le_max_left _ _).trans (le_max_right _ _)
    refine ⟨Int.toNat_le_toNat ((min_le_right _ _).trans ?_),
      Int.toNat_le_toNat ((min_le_right _ _).trans ?_)⟩
    · change oldCount (initialFlag i) - lower ≤ oldCount (initialFlag i)
      omega
    · change oldCount (initialFlag i) - lower ≤ targetCount (initialFlag i)
      omega
private theorem initialFlag_at (s : Fin 4013) (j : Fin 4650) (t u : ℕ)
    (ht : t ≤ 1350) (hst : s.val + t = 3000) (hju : j.val + u + 1 = 1650 + t) :
    initialFlag (s,j) = ⟨1650, (u : ℤ) - t + 1,1650,550, (u : ℤ) + 1⟩ := by
  simp [initialFlag, offset, min_eq_right (show (1650 : ℤ) ≤ s.val by omega)]
  omega
private def removed (t : ℕ) : ℕ := (t + 1649) / 4 + 1
private def targetHead (t u : ℕ) : ℤ :=
  let d := 1650 - removed t
  cumulative 1650 (u : ℤ) - cumulative (d : ℤ) ((u : ℤ) - (3 * removed t : ℕ)) +
    cumulative (d : ℤ) ((u : ℤ) - t)
private def piece (t k u : ℕ) : ℤ :=
  (if u < k then targetHead t u else cumulative 1650 1650) - cumulative 1650 ((u : ℤ) - t)
private theorem old_at (t u : ℕ) (hu : u < 1650 + t) :
    oldCount ⟨1650, (u : ℤ) - t + 1,1650,550, (u : ℤ) + 1⟩ =
      cumulative 1650 1650 - cumulative 1650 ((u : ℤ) - t) := by
  simp only [oldCount, cappedCount, Int.reduceLT, ite_false, Int.reduceAdd, Int.reduceMul]
  rw [show (u : ℤ) - t + 1 - 1 = (u : ℤ) - t by omega,
    min_eq_right (show (u : ℤ) - t ≤ 1650 by omega)]
  have hz (x : ℤ) (hx : x < 0) : cumulative (1650 - 550 - 1) x = 0 := by
    simp [cumulative, hx]
  rw [hz _ (by omega), hz _ (by omega), sub_zero, sub_zero]
private theorem target_at (t u : ℕ) (ht : t ≤ 1350) :
    targetCount ⟨1650, (u : ℤ) - t + 1,1650,550, (u : ℤ) + 1⟩ =
      targetHead t u - cumulative 1650 ((u : ℤ) - t) := by
  have hb : (u : ℤ) + 1 - 1 - ((u : ℤ) - t + 1) + 1650 = (t : ℤ) + 1649 := by omega
  have hr : min (1650 : ℤ) (((t : ℤ) + 1649) / 4) + 1 = (removed t : ℤ) := by
    unfold removed
    omega
  have hd : (1650 : ℤ) - (removed t : ℤ) = ((1650 - removed t : ℕ) : ℤ) := by
    unfold removed
    omega
  simp only [targetCount, hb, not_lt.mpr (show (0 : ℤ) ≤ t + 1649 by omega), ite_false, hr, hd,
    targetHead, Nat.cast_mul]
  rw [show (u : ℤ) + 1 - 1 = (u : ℤ) by omega, show (u : ℤ) - t + 1 - 1 = (u : ℤ) - t by omega]
  ring_nf
private theorem piece_nonneg (t k u : ℕ) (ht : t ≤ 1350) (hu : u < 1650 + t) :
    0 ≤ piece t k u := by
  unfold piece
  split
  · dsimp only [targetHead]
    have h1 := cumulative_mono 1650 (show (u : ℤ) - t ≤ u by omega)
    have h2 := cumulative_mono (1650 - removed t)
      (show (u : ℤ) - (3 * removed t : ℕ) ≤ (u : ℤ) - t by unfold removed; omega)
    change cumulative 1650 ((u : ℤ) - t) ≤ cumulative 1650 (u : ℤ) at h1
    omega
  · exact sub_nonneg.mpr (cumulative_mono 1650 (show (u : ℤ) - t ≤ 1650 by omega))
private theorem baseline_le_piece (s : Fin 4013) (j : Fin 4650) (t k u : ℕ)
    (ht : t ≤ 1350) (hst : s.val + t = 3000) (hju : j.val + u + 1 = 1650 + t) :
    baseline (s,j) ≤ (piece t k u).toNat := by
  have h := baseline_le_counts (s,j)
  rw [initialFlag_at s j t u ht hst hju, old_at t u (by omega), target_at t u ht] at h
  unfold piece
  split
  · exact h.2
  · exact h.1
private theorem baseline_zero (s : Fin 4013) (j : Fin 4650) (t : ℕ)
    (hst : s.val + t = 3000) (hj : 1650 + t ≤ j.val) : baseline (s,j) = 0 := by
  have ho : (3000 : ℤ) - (s.val : ℤ) - ((j.val : ℤ) - 1650) ≤ 0 := by omega
  simp [baseline, blockBound, initialFlag, offset, ho]
private theorem sum_cutoff {α : Type*} [AddCommMonoid α] (f : ℕ → α) {m n : ℕ} (h : m ≤ n) :
    (∑ j ∈ range n, if j < m then f j else 0) = ∑ j ∈ range m, f j := by
  calc
    _ = ∑ j ∈ range m, if j < m then f j else 0 := by
      symm
      apply sum_subset (range_mono h)
      intro j _ hj
      rw [mem_range] at hj
      rw [ite_eq_right hj]
    _ = _ := sum_congr rfl fun j hj => ite_eq_left (mem_range.mp hj)
private theorem grade_le (s : Fin 4013) (t k : ℕ) (ht : t ≤ 1350) (hst : s.val + t = 3000) :
    (∑ j : Fin 4650, baseline (s,j)) ≤ ∑ u ∈ range (1650 + t), (piece t k u).toNat := by
  calc
    _ ≤ ∑ j : Fin 4650, if j.val < 1650 + t then (piece t k (1650 + t - 1 - j.val)).toNat else 0 := by
      apply sum_le_sum
      intro j _
      by_cases hj : j.val < 1650 + t
      · rw [ite_eq_left hj]
        exact baseline_le_piece s j t k _ ht hst (by omega)
      · simp [hj, baseline_zero s j t hst (by omega : 1650 + t ≤ j.val)]
    _ = ∑ j ∈ range (1650 + t), (piece t k (1650 + t - 1 - j)).toNat := by
      rw [Fin.sum_univ_eq_sum_range
        (fun j : ℕ => if j < 1650 + t then (piece t k (1650 + t - 1 - j)).toNat else 0)]
      exact sum_cutoff _ (by omega)
    _ = _ := sum_range_reflect (fun u => (piece t k u).toNat) (1650 + t)
private theorem sum_switch (f : ℕ → ℤ) (b : ℤ) {k n : ℕ} (h : k ≤ n) :
    (∑ u ∈ range n, if u < k then f u else b) = (∑ u ∈ range k, f u) + (↑(n - k) : ℤ) * b := by
  conv_lhs => rw [← Nat.add_sub_of_le h, sum_range_add]
  rw [sum_congr rfl (f := fun u => if u < k then f u else b) (g := f)
    (fun u hu => ite_eq_left (mem_range.mp hu))]
  rw [sum_congr rfl (f := fun u => if k + u < k then f (k + u) else b) (g := fun _ => b)
    (fun u _ => ite_eq_right (by omega))]
  simp
private def closedGrade (t k : ℕ) : ℤ :=
  let d := 1650 - removed t
  cumulativePrefix 1650 k + 24 * ((1650 + t - k : ℕ) : ℤ) * cumulative 1650 1650 -
    cumulativePrefix 1650 1650 + cumulativePrefix d (k - t) - cumulativePrefix d (k - 3 * removed t)
private theorem sum_piece_scaled (t k : ℕ) (ht : t ≤ 1350) (hk : k ≤ 1650) :
    24 * (∑ u ∈ range (1650 + t), piece t k u) = closedGrade t k := by
  have hd : 900 ≤ 1650 - removed t := by unfold removed; omega
  unfold piece closedGrade
  rw [sum_sub_distrib, sum_switch _ _ (by omega : k ≤ 1650 + t)]
  simp only [targetHead, sum_sub_distrib, sum_add_distrib, mul_sub, mul_add, sum_shift_cumulative]
  have hshift := sum_shift_cumulative 1650 (1650 + t) t
  have hcut := prefix_eq 1650 k (by omega)
  have hfull := prefix_eq 1650 1650 (by decide)
  norm_num only [Nat.cast_ofNat] at hshift hcut hfull
  rw [hshift, show 1650 + t - t = 1650 by omega, hcut, hfull,
    prefix_eq _ (k - 3 * removed t) (by omega),
    prefix_eq _ (k - t) (by omega)]
  ring_nf
private theorem grade_scaled_le (s : Fin 4013) (t k : ℕ) (ht : t ≤ 1350)
    (hst : s.val + t = 3000) (hk : k ≤ 1650) :
    24 * ((∑ j : Fin 4650, baseline (s,j) : ℕ) : ℤ) ≤ closedGrade t k := by
  have h : ((∑ j : Fin 4650, baseline (s,j) : ℕ) : ℤ) ≤
      ((∑ u ∈ range (1650 + t), (piece t k u).toNat : ℕ) : ℤ) := by
    exact_mod_cast grade_le s t k ht hst
  conv at h => rhs; rw [Nat.cast_sum]
  have hn (u : ℕ) (hu : u ∈ range (1650 + t)) : ((piece t k u).toNat : ℤ) = piece t k u :=
    Int.toNat_of_nonneg (piece_nonneg t k u ht (mem_range.mp hu))
  rw [sum_congr rfl hn] at h
  rw [← sum_piece_scaled t k ht hk]
  exact mul_le_mul_of_nonneg_left h (by decide)
private def findCut (t : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    let mid := (lo + hi) / 2
    if targetHead t mid < cumulative 1650 1650 then findCut t fuel (mid + 1) hi
    else findCut t fuel lo mid
private def cutoff (t : ℕ) : ℕ := min 1650 (findCut t 11 0 1650)
private def gradeEstimate (t : ℕ) : ℤ := closedGrade t (cutoff t)
private theorem sum_window (f : ℕ → ℤ) {lo w n : ℕ} (h : lo + w ≤ n) :
    (∑ j ∈ range n, if lo ≤ j ∧ j < lo + w then f j else 0) = ∑ j ∈ range w, f (lo + j) := by
  have he (j : ℕ) : (if lo ≤ j ∧ j < lo + w then f j else 0) =
      (if j < lo + w then if lo ≤ j then f j else 0 else 0) := by
    by_cases h₁ : lo ≤ j <;> by_cases h₂ : j < lo + w <;> simp [h₁, h₂]
  simp_rw [he]
  rw [sum_cutoff _ h, sum_range_add]
  have hz : (∑ j ∈ range lo, if lo ≤ j then f j else 0) = 0 :=
    sum_eq_zero fun j hj => ite_eq_right (by have := mem_range.mp hj; omega)
  rw [hz, zero_add]
  exact sum_congr rfl fun j _ => ite_eq_left (by omega)
private def evaluate (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => evaluate f n + f n
private theorem evaluate_eq (f : ℕ → ℤ) (n : ℕ) : evaluate f n = ∑ j ∈ range n, f j := by
  induction n with
  | zero => simp [evaluate]
  | succ n ih => rw [evaluate, sum_range_succ, ih]
private theorem k1232_evaluate_append (f : ℕ → ℤ) (a b : ℕ) :
    evaluate f (a + b) = evaluate f a + evaluate (fun j => f (a + j)) b := by
  simpa only [evaluate_eq] using sum_range_add f a b
private theorem k1232_join_evaluations {f : ℕ → ℤ} {a b n : ℕ} {x y z : ℤ}
    (ha : evaluate f a = x) (hb : evaluate (fun j => f (a + j)) b = y)
    (hn : a + b = n) (hz : x + y = z) : evaluate f n = z := by
  rw [← hn, ← hz]
  exact (k1232_evaluate_append f a b).trans (congrArg₂ (fun x y : ℤ => x + y) ha hb)
open K1_13_2_3_2 (twice_den denPolynomial denPrefix denPrefixPolynomial)
private def twiceDenNat (n : ℕ) : ℕ :=
  let q := n / 6
  let r := n % 6
  2 + r * (r + 1) + q * (11 + r * (7 + r) + q * (21 + 6 * r + 12 * q))
private def denPrefixNat (n : ℕ) : ℕ :=
  let q := n / 6
  let r := n % 6
  r * (20 + 4 * r * r) +
    q * (60 + r * (92 + r * (36 + 4 * r)) +
      q * (276 + r * (216 + 36 * r) + q * (432 + 144 * r + 216 * q)))
private theorem twiceDenNat_eq (n : ℕ) :
    2 * denominator n = (twiceDenNat n : ℤ) := by
  rw [twice_den _ (by omega)]
  unfold twiceDenNat denPolynomial
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Int.natCast_ediv, Int.natCast_mod]
  ring
private theorem denPrefixNat_eq (n : ℕ) : denPrefix n = (denPrefixNat n : ℤ) := by
  unfold denPrefix denPrefixPolynomial denPrefixNat
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Int.natCast_ediv, Int.natCast_mod]
  ring
private theorem cumulative_of_le_degree (d n : ℕ) (h : n ≤ d) :
    cumulative d n = denominator n := by
  have hz (x : ℤ) (hx : x < 0) : denominator x = 0 := by simp [denominator, hx]
  have hd : ¬(d : ℤ) < 0 := by omega
  have hn : ¬(n : ℤ) < 0 := by omega
  simp (disch := omega) [cumulative, hd, hn, hz]
private theorem prefix_of_le_degree (d n : ℕ) (h : n ≤ d) :
    cumulativePrefix d n = (denPrefixNat n : ℤ) := by
  have hz : denPrefix 0 = 0 := by decide
  simp (disch := omega) only [cumulativePrefix, Nat.sub_eq_zero_of_le, Nat.cast_zero, hz,
    sub_zero, add_zero, denPrefixNat_eq]
private theorem full_cumulative_value : cumulative 1650 1650 = 125576826 := by decide
private def headBelow (t u : ℕ) : ℤ :=
  cumulative 1650 u + cumulative (1650 - removed t : ℕ) ((u : ℤ) - t)
private theorem headBelow_eq (t u : ℕ) (hu : u < 3 * removed t) :
    targetHead t u = headBelow t u := by
  have hz (d x : ℤ) (hx : x < 0) : cumulative d x = 0 := by simp [cumulative, hx]
  simp (disch := omega) only [targetHead, headBelow, hz, sub_zero]
private theorem headBelow_mono (t : ℕ) : Monotone (headBelow t) := by
  intro x y h
  unfold headBelow
  exact add_le_add (cumulative_mono 1650 (by exact_mod_cast h))
    (cumulative_mono (1650 - removed t) (by omega))
private theorem headBelow_value (t u : ℕ) (ht : t ≤ u) (hu : u ≤ 1650)
    (hd : u - t ≤ 1650 - removed t) :
    2 * headBelow t u = ((twiceDenNat u + twiceDenNat (u - t) : ℕ) : ℤ) := by
  have hfull : cumulative 1650 (u : ℤ) = denominator u := by
    simpa only [Nat.cast_ofNat] using cumulative_of_le_degree _ _ hu
  unfold headBelow
  rw [show (u : ℤ) - t = ((u - t : ℕ) : ℤ) by omega, hfull,
    cumulative_of_le_degree _ _ hd, mul_add, twiceDenNat_eq, twiceDenNat_eq, Nat.cast_add]
private def cutPath (k limit : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, lo, _ => lo == k
  | fuel + 1, lo, hi =>
    let mid := (lo + hi) / 2
    decide (mid < limit) &&
      (if mid < k then cutPath k limit fuel (mid + 1) hi else cutPath k limit fuel lo mid)
private theorem cutPath_sound (t k limit : ℕ)
    (hc : ∀ u < limit, (targetHead t u < cumulative 1650 1650 ↔ u < k))
    (fuel lo hi : ℕ) (h : cutPath k limit fuel lo hi = true) :
    findCut t fuel lo hi = k := by
  induction fuel generalizing lo hi with
  | zero => simpa [findCut, cutPath] using h
  | succ fuel ih =>
    have hp := Bool.and_eq_true_iff.mp h
    have hm : (lo + hi) / 2 < limit := of_decide_eq_true hp.1
    simp only [findCut, hc _ hm]
    by_cases hmid : (lo + hi) / 2 < k
    · rw [ite_eq_left hmid]
      exact ih _ _ (by simpa only [ite_eq_left hmid] using hp.2)
    · rw [ite_eq_right hmid]
      exact ih _ _ (by simpa only [ite_eq_right hmid] using hp.2)
private abbrev cutWitness (t k : ℕ) : Prop :=
  t < k ∧ k ≤ 1650 ∧ k < 3 * removed t ∧ k - t ≤ 1650 - removed t ∧
    twiceDenNat (k - 1) + twiceDenNat (k - 1 - t) < 251153652 ∧
    251153652 ≤ twiceDenNat k + twiceDenNat (k - t) ∧
    cutPath k (3 * removed t) 11 0 1650 = true
private theorem cutoff_of_witness (t k : ℕ) (h : cutWitness t k) : cutoff t = k := by
  obtain ⟨ht, hk, _, hd, hlo, hhi, hp⟩ := h
  have hmin := headBelow_value t (k - 1) (by omega) (by omega) (by omega)
  have hmax := headBelow_value t k (by omega) hk hd
  have h₁ : headBelow t (k - 1) < 125576826 := by omega
  have h₂ : 125576826 ≤ headBelow t k := by omega
  have cmp (u : ℕ) (hu : u < 3 * removed t) :
      targetHead t u < cumulative 1650 1650 ↔ u < k := by
    rw [headBelow_eq _ _ hu, full_cumulative_value]
    constructor
    · intro hc
      by_contra! hle
      exact (not_lt_of_ge ((headBelow_mono t hle).trans' h₂)) hc
    · intro huk
      exact (headBelow_mono t (show u ≤ k - 1 by omega)).trans_lt h₁
  unfold cutoff
  rw [cutPath_sound t k _ cmp 11 0 1650 hp, min_eq_right hk]
private def gradeCredit (t k : ℕ) : ℕ :=
  denPrefixNat k + 3013843824 * (1650 + t - k) + denPrefixNat (k - t)
private theorem gradeCredit_eq (t k : ℕ) (h : cutWitness t k) :
    gradeEstimate t = (gradeCredit t k : ℤ) - (denPrefixNat 1650 : ℤ) := by
  rw [gradeEstimate, cutoff_of_witness t k h]
  obtain ⟨_, hk, hr, hd, _⟩ := h
  dsimp only [closedGrade, gradeCredit]
  rw [show k - 3 * removed t = 0 by omega, prefix_of_le_degree _ _ hk,
    prefix_of_le_degree 1650 1650 le_rfl, prefix_of_le_degree _ _ hd,
    prefix_of_le_degree _ 0 (Nat.zero_le _), full_cumulative_value]
  have hz : denPrefixNat 0 = 0 := by decide
  rw [hz]
  push_cast
  ring
private def validCuts (start : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | n + 1, digits =>
    decide (cutWitness (1350 - (start + n)) (digits % 2048)) && validCuts start n (digits / 2048)
private def creditSum (start : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, digits =>
    creditSum start n (digits / 2048) + gradeCredit (1350 - (start + n)) (digits % 2048)
private theorem creditSum_eq (start n digits : ℕ) (h : validCuts start n digits = true) :
    evaluate (fun j => gradeEstimate (1350 - (start + j))) n =
      (creditSum start n digits : ℤ) - (n : ℤ) * (denPrefixNat 1650 : ℤ) := by
  induction n generalizing digits with
  | zero => simp [evaluate, creditSum]
  | succ n ih =>
    have hs := Bool.and_eq_true_iff.mp h
    rw [evaluate, ih _ hs.2, gradeCredit_eq _ _ (of_decide_eq_true hs.1)]
    simp only [creditSum, Nat.cast_add, Nat.cast_succ]
    ring
private theorem block_of_cuts (start n digits : ℕ) (z : ℤ)
    (hcuts : validCuts start n digits = true)
    (hsum : (creditSum start n digits : ℤ) - (n : ℤ) * (denPrefixNat 1650 : ℤ) = z) :
    evaluate (fun j => gradeEstimate (1350 - (start + j))) n = z :=
  (creditSum_eq _ _ _ hcuts).trans hsum
section
set_option maxRecDepth 50000
set_option maxHeartbeats 0
private theorem k1232_evaluate_000 :
    evaluate (fun j => gradeEstimate (1350 - (0 + j))) 20 = 80832455229384 :=
  block_of_cuts 0 20
    0xcdf9bf37e6fcdf9bf37e6fcdf9bf37e6fcdf9bf37e6fcdf9bf37e6f 80832455229384
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_020 :
    evaluate (fun j => gradeEstimate (1350 - (20 + j))) 20 = 79635592691832 :=
  block_of_cuts 20 20
    0xcdf9bb3766ecdd9bb3766ecdd9bb3766ecdd9bb3766ecdd9bb3766e 79635592691832
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_040 :
    evaluate (fun j => gradeEstimate (1350 - (40 + j))) 20 = 78440393723472 :=
  block_of_cuts 40 20
    0xcdd9bb3766ecdd9bb3766dcdb9b736e6dcdb9b736e6dcdb9b736e6d 78440393723472
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_060 :
    evaluate (fun j => gradeEstimate (1350 - (60 + j))) 20 = 77247047512416 :=
  block_of_cuts 60 20
    0xcdb9b736e6dcdb9b736e6dcdb9b33666ccd99b33666ccd99b33666c 77247047512416
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_080 :
    evaluate (fun j => gradeEstimate (1350 - (80 + j))) 20 = 76055754794496 :=
  block_of_cuts 80 20
    0xcd99b33666ccd99b33666ccd99af35e6bcd79af35e6bcd79af35e6b 76055754794496
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_100 :
    evaluate (fun j => gradeEstimate (1350 - (100 + j))) 20 = 74866722453312 :=
  block_of_cuts 100 20
    0xcd79af35e6bcd79af35e6bcd59ab3566acd59ab3566acd59ab3566a 74866722453312
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_120 :
    evaluate (fun j => gradeEstimate (1350 - (120 + j))) 20 = 73680164934216 :=
  block_of_cuts 120 20
    0xcd59ab3566acd59a734e69cd39a734e69cd39a734e69cd39a734e69 73680164934216
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_140 :
    evaluate (fun j => gradeEstimate (1350 - (140 + j))) 20 = 72496300970568 :=
  block_of_cuts 140 20
    0xcd39a334668cd19a334668cd19a334668cd19a334668ccf99f33e67 72496300970568
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_160 :
    evaluate (fun j => gradeEstimate (1350 - (160 + j))) 20 = 71315354680920 :=
  block_of_cuts 160 20
    0xccf99f33e67ccf99f33e67ccf99f33666ccd99b33666ccd99b33666 71315354680920
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_180 :
    evaluate (fun j => gradeEstimate (1350 - (180 + j))) 20 = 70137564602976 :=
  block_of_cuts 180 20
    0xccd99b33665ccb99732e65ccb99732e65ccb99732e65cc999332664 70137564602976
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_200 :
    evaluate (fun j => gradeEstimate (1350 - (200 + j))) 20 = 68963160075144 :=
  block_of_cuts 200 20
    0xcc999332664cc999332664cc798f31e63cc798f31e63cc798f31e63 68963160075144
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_220 :
    evaluate (fun j => gradeEstimate (1350 - (220 + j))) 20 = 67792386793464 :=
  block_of_cuts 220 20
    0xcc598b31662cc598b31662cc598b31661cc398730e61cc398730e61 67792386793464
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_240 :
    evaluate (fun j => gradeEstimate (1350 - (240 + j))) 20 = 66625491000888 :=
  block_of_cuts 240 20
    0xcc398730660cc198330660cc198330660cbf97f2fe5fcbf97f2fe5f 66625491000888
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_260 :
    evaluate (fun j => gradeEstimate (1350 - (260 + j))) 20 = 65462720303784 :=
  block_of_cuts 260 20
    0xcbf97f2f65ecbd97b2f65ecbd97b2f65ecbb9772ee5dcbb9772ee5d 65462720303784
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_280 :
    evaluate (fun j => gradeEstimate (1350 - (280 + j))) 20 = 64304328567000 :=
  block_of_cuts 280 20
    0xcbb9772e65ccb99732e65ccb99732e65bcb796f2de5bcb796f2de5b 64304328567000
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_300 :
    evaluate (fun j => gradeEstimate (1350 - (300 + j))) 20 = 63150570148488 :=
  block_of_cuts 300 20
    0xcb596b2d65acb596b2d65acb59672ce59cb39672ce59cb39632c658 63150570148488
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_320 :
    evaluate (fun j => gradeEstimate (1350 - (320 + j))) 20 = 62001702709200 :=
  block_of_cuts 320 20
    0xcb19632c658cb19632be57caf95f2be57caf95f2b656cad95b2b656 62001702709200
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_340 :
    evaluate (fun j => gradeEstimate (1350 - (340 + j))) 20 = 60857989332096 :=
  block_of_cuts 340 20
    0xcad95b2ae55cab9572ae55cab9572a654ca99532a654ca995329e53 60857989332096
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_360 :
    evaluate (fun j => gradeEstimate (1350 - (360 + j))) 20 = 59719686384336 :=
  block_of_cuts 360 20
    0xca794f29e53ca794b29652ca594b29652ca594728e51ca394728e51 59719686384336
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_380 :
    evaluate (fun j => gradeEstimate (1350 - (380 + j))) 20 = 58587059139312 :=
  block_of_cuts 380 20
    0xca194328650ca19432864fc9f93f27e4fc9f93f2764ec9d93b2764e 58587059139312
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_400 :
    evaluate (fun j => gradeEstimate (1350 - (400 + j))) 20 = 57460370517984 :=
  block_of_cuts 400 20
    0xc9d93726e4dc9b93726e4dc999332664cc999332664bc9792f25e4b 57460370517984
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_420 :
    evaluate (fun j => gradeEstimate (1350 - (420 + j))) 20 = 56339882531856 :=
  block_of_cuts 420 20
    0xc9792b2564ac9592b2564ac9392724e49c9392724648c9192324648 56339882531856
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_440 :
    evaluate (fun j => gradeEstimate (1350 - (440 + j))) 20 = 55225858815408 :=
  block_of_cuts 440 20
    0xc8f91f23e47c8f91f23e46c8d91b23646c8d91722e45c8b91722e44 55225858815408
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_460 :
    evaluate (fun j => gradeEstimate (1350 - (460 + j))) 20 = 54118560065088 :=
  block_of_cuts 460 20
    0xc8991322644c8990f21e43c8790f21e42c8590b21642c8590720e41 54118560065088
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_480 :
    evaluate (fun j => gradeEstimate (1350 - (480 + j))) 20 = 53018250987240 :=
  block_of_cuts 480 20
    0xc8390720640c8190320640c7f8ff1fe3fc7f8ff1f63ec7d8fb1f63d 53018250987240
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_500 :
    evaluate (fun j => gradeEstimate (1350 - (500 + j))) 20 = 51925188079944 :=
  block_of_cuts 500 20
    0xc7b8f71ee3dc7b8f31e63cc798f31de3bc778ef1de3bc758eb1d63a 51925188079944
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_520 :
    evaluate (fun j => gradeEstimate (1350 - (520 + j))) 20 = 50839633362096 :=
  block_of_cuts 520 20
    0xc758e71ce39c738e71ce38c718e31c638c6f8df1be37c6f8db1b636 50839633362096
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_540 :
    evaluate (fun j => gradeEstimate (1350 - (540 + j))) 20 = 49761840927024 :=
  block_of_cuts 540 20
    0xc6d8db1ae35c6b8d71ae34c698d31a634c678cf19e33c678cb19632 49761840927024
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_560 :
    evaluate (fun j => gradeEstimate (1350 - (560 + j))) 20 = 48692065869432 :=
  block_of_cuts 560 20
    0xc658cb18e31c638c718e30c618c318630c5f8bf17e2fc5f8bb1762e 48692065869432
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_580 :
    evaluate (fun j => gradeEstimate (1350 - (580 + j))) 20 = 47630560454832 :=
  block_of_cuts 580 20
    0xc5d8bb16e2dc5b8b71662cc598b31662bc578af15e2bc558ab1562a 47630560454832
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_600 :
    evaluate (fun j => gradeEstimate (1350 - (600 + j))) 20 = 46577573150784 :=
  block_of_cuts 600 20
    0xc538a714e29c538a314628c518a313e27c4f89f13626c4d89b13625 46577573150784
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_620 :
    evaluate (fun j => gradeEstimate (1350 - (620 + j))) 20 = 45533347926264 :=
  block_of_cuts 620 20
    0xc4b89712e24c4989312624c4788f11e23c4588b11622c4388710e21 45533347926264
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_640 :
    evaluate (fun j => gradeEstimate (1350 - (640 + j))) 20 = 44498129823840 :=
  block_of_cuts 640 20
    0xc4388310620c4187f0fe1fc3f87b0f61ec3d87b0ee1dc3b8770e61c 44498129823840
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_660 :
    evaluate (fun j => gradeEstimate (1350 - (660 + j))) 20 = 43472154839544 :=
  block_of_cuts 660 20
    0xc398730de1bc3786f0d61ac3586b0ce19c338670c618c318630be17 43472154839544
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_680 :
    evaluate (fun j => gradeEstimate (1350 - (680 + j))) 20 = 42455658222000 :=
  block_of_cuts 680 20
    0xc2f85f0be16c2d85b0b615c2b8570ae14c298530a613c2784f09e12 42455658222000
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_700 :
    evaluate (fun j => gradeEstimate (1350 - (700 + j))) 20 = 41448869045472 :=
  block_of_cuts 700 20
    0xc2584b09611c2384708610c2184307e0fc1f83f0760ec1d83b06e0d 41448869045472
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_720 :
    evaluate (fun j => gradeEstimate (1350 - (720 + j))) 20 = 40452013687080 :=
  block_of_cuts 720 20
    0xc1b8370660cc1983305e0bc1782f0560ac1582704e09c1382304608 40452013687080
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_740 :
    evaluate (fun j => gradeEstimate (1350 - (740 + j))) 20 = 39465313582800 :=
  block_of_cuts 740 20
    0xc1181f03e07c0d81b03606c0b81702e05c0981302604c0780f01e02 39465313582800
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_760 :
    evaluate (fun j => gradeEstimate (1350 - (760 + j))) 20 = 38488981885344 :=
  block_of_cuts 760 20
    0xc0580b01601c0380700600c01802ffdffbff7feff5febfd7f6fedfd 38488981885344
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_780 :
    evaluate (fun j => gradeEstimate (1350 - (780 + j))) 20 = 37523232286272 :=
  block_of_cuts 780 20
    0xbfb7f2fe5fcbf77eefddfbbf57eafd5f9bf37e6fcdf8bf17e2fbdf7 37523232286272
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_800 :
    evaluate (fun j => gradeEstimate (1350 - (800 + j))) 20 = 36568268216736 :=
  block_of_cuts 800 20
    0xbef7defb5f6bed7d6fadf5be97d2fa5f4be77cef9df2be57caf95f1 36568268216736
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_820 :
    evaluate (fun j => gradeEstimate (1350 - (820 + j))) 20 = 35624289073704 :=
  block_of_cuts 820 20
    0xbe37c6f85f0be17bef7defbdf7baf75eebdb7b6f6decbd97b2f5deb 35624289073704
    (by decide +kernel) (by decide +kernel)
private theorem k1232_evaluate_840 :
    evaluate (fun j => gradeEstimate (1350 - (840 + j))) 20 = 34691489395248 :=
  block_of_cuts 840 20
    0xbd77aef55eabd57a6f4de9bd17a2f45e7bcf79ef3de6bcd79af2de5 34691489395248
    (by decide +kernel) (by decide +kernel)
end
private theorem evaluate_check : evaluate (fun j => gradeEstimate (1350 - j)) 860 = 0x8aeca5ce48950 := by
  have h000 : evaluate (fun j => gradeEstimate (1350 - j)) 0 = 0 := rfl
  have h020 : evaluate (fun j => gradeEstimate (1350 - j)) 20 = 80832455229384 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h000 k1232_evaluate_000 rfl rfl
  have h040 : evaluate (fun j => gradeEstimate (1350 - j)) 40 = 0x91f1e0fe8040 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h020 k1232_evaluate_020 rfl rfl
  have h060 : evaluate (fun j => gradeEstimate (1350 - j)) 60 = 0xd94934cc4e90 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h040 k1232_evaluate_040 rfl rfl
  have h080 : evaluate (fun j => gradeEstimate (1350 - j)) 80 = 316155489157104 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h060 k1232_evaluate_060 rfl rfl
  have h100 : evaluate (fun j => gradeEstimate (1350 - j)) 100 = 392211243951600 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h080 k1232_evaluate_080 rfl rfl
  have h120 : evaluate (fun j => gradeEstimate (1350 - j)) 120 = 467077966404912 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h100 k1232_evaluate_100 rfl rfl
  have h140 : evaluate (fun j => gradeEstimate (1350 - j)) 140 = 540758131339128 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h120 k1232_evaluate_120 rfl rfl
  have h160 : evaluate (fun j => gradeEstimate (1350 - j)) 160 = 613254432309696 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h140 k1232_evaluate_140 rfl rfl
  have h180 : evaluate (fun j => gradeEstimate (1350 - j)) 180 = 684569786990616 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h160 k1232_evaluate_160 rfl rfl
  have h200 : evaluate (fun j => gradeEstimate (1350 - j)) 200 = 754707351593592 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h180 k1232_evaluate_180 rfl rfl
  have h220 : evaluate (fun j => gradeEstimate (1350 - j)) 220 = 823670511668736 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h200 k1232_evaluate_200 rfl rfl
  have h240 : evaluate (fun j => gradeEstimate (1350 - j)) 240 = 891462898462200 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h220 k1232_evaluate_220 rfl rfl
  have h260 : evaluate (fun j => gradeEstimate (1350 - j)) 260 = 958088389463088 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h240 k1232_evaluate_240 rfl rfl
  have h280 : evaluate (fun j => gradeEstimate (1350 - j)) 280 = 0x3a2ea104e9ed8 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h260 k1232_evaluate_260 rfl rfl
  have h300 : evaluate (fun j => gradeEstimate (1350 - j)) 300 = 0x3dd6614f807b0 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h280 k1232_evaluate_280 rfl rfl
  have h320 : evaluate (fun j => gradeEstimate (1350 - j)) 320 = 0x416d578451a38 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h300 k1232_evaluate_300 rfl rfl
  have h340 : evaluate (fun j => gradeEstimate (1350 - j)) 340 = 0x44f395dbc4208 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h320 k1232_evaluate_320 rfl rfl
  have h360 : evaluate (fun j => gradeEstimate (1350 - j)) 360 = 0x48692f8923e88 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h340 k1232_evaluate_340 rfl rfl
  have h380 : evaluate (fun j => gradeEstimate (1350 - j)) 380 = 0x4bce38b43a958 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h360 k1232_evaluate_360 rfl rfl
  have h400 : evaluate (fun j => gradeEstimate (1350 - j)) 400 = 0x4f22c681cdc48 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h380 k1232_evaluate_380 rfl rfl
  have h420 : evaluate (fun j => gradeEstimate (1350 - j)) 420 = 0x5266ef1160c28 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h400 k1232_evaluate_400 rfl rfl
  have h440 : evaluate (fun j => gradeEstimate (1350 - j)) 440 = 0x559ac97c56838 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h420 k1232_evaluate_420 rfl rfl
  have h460 : evaluate (fun j => gradeEstimate (1350 - j)) 460 = 0x58be6dd77dde8 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h440 k1232_evaluate_440 rfl rfl
  have h480 : evaluate (fun j => gradeEstimate (1350 - j)) 480 = 0x5bd1f53044428 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h460 k1232_evaluate_460 rfl rfl
  have h500 : evaluate (fun j => gradeEstimate (1350 - j)) 500 = 0x5ed5799088b10 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h480 k1232_evaluate_480 rfl rfl
  have h520 : evaluate (fun j => gradeEstimate (1350 - j)) 520 = 0x61c915f6c7c58 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h500 k1232_evaluate_500 rfl rfl
  have h540 : evaluate (fun j => gradeEstimate (1350 - j)) 540 = 0x64ace65b5f908 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h520 k1232_evaluate_520 rfl rfl
  have h560 : evaluate (fun j => gradeEstimate (1350 - j)) 560 = 0x678107a900a38 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h540 k1232_evaluate_540 rfl rfl
  have h580 : evaluate (fun j => gradeEstimate (1350 - j)) 580 = 0x6a4597bda28b0 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h560 k1232_evaluate_560 rfl rfl
  have h600 : evaluate (fun j => gradeEstimate (1350 - j)) 600 = 0x6cfab567d1160 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h580 k1232_evaluate_580 rfl rfl
  have h620 : evaluate (fun j => gradeEstimate (1350 - j)) 620 = 0x6fa080630d1a0 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h600 k1232_evaluate_600 rfl rfl
  have h640 : evaluate (fun j => gradeEstimate (1350 - j)) 640 = 0x7237195382298 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h620 k1232_evaluate_620 rfl rfl
  have h660 : evaluate (fun j => gradeEstimate (1350 - j)) 660 = 0x74bea1c70caf8 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h640 k1232_evaluate_640 rfl rfl
  have h680 : evaluate (fun j => gradeEstimate (1350 - j)) 680 = 0x77373c2c994f0 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h660 k1232_evaluate_660 rfl rfl
  have h700 : evaluate (fun j => gradeEstimate (1350 - j)) 700 = 0x79a10bd36e6a0 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h680 k1232_evaluate_680 rfl rfl
  have h720 : evaluate (fun j => gradeEstimate (1350 - j)) 720 = 0x7bfc34e548b80 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h700 k1232_evaluate_700 rfl rfl
  have h740 : evaluate (fun j => gradeEstimate (1350 - j)) 740 = 0x7e48dc63c8ca8 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h720 k1232_evaluate_720 rfl rfl
  have h760 : evaluate (fun j => gradeEstimate (1350 - j)) 760 = 0x80872823bcb78 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h740 k1232_evaluate_740 rfl rfl
  have h780 : evaluate (fun j => gradeEstimate (1350 - j)) 780 = 0x82b73ec539d18 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h760 k1232_evaluate_760 rfl rfl
  have h800 : evaluate (fun j => gradeEstimate (1350 - j)) 800 = 0x84d947b420358 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h780 k1232_evaluate_780 rfl rfl
  have h820 : evaluate (fun j => gradeEstimate (1350 - j)) 820 = 0x86ed6b1e51cf8 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h800 k1232_evaluate_800 rfl rfl
  have h840 : evaluate (fun j => gradeEstimate (1350 - j)) 840 = 0x88f3d1efd9720 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h820 k1232_evaluate_820 rfl rfl
  have h860 : evaluate (fun j => gradeEstimate (1350 - j)) 860 = 0x8aeca5ce48950 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h840 k1232_evaluate_840 rfl rfl
  exact h860
private theorem scaled_bound : 24 * (baselineSum 1650 2510 : ℤ) ≤ 0x8aeca5ce48950 := by
  unfold baselineSum baselineSumOn
  rw [← univ_product_univ, sum_product, Nat.cast_sum, mul_sum]
  calc
    _ ≤ ∑ s : Fin 4013, if 1650 ≤ s.val ∧ s.val < 2510 then gradeEstimate (3000 - s.val) else 0 := by
      apply sum_le_sum
      intro s _
      by_cases hs : 1650 ≤ s.val ∧ s.val < 2510
      · simpa only [ite_eq_left hs, gradeEstimate] using
          grade_scaled_le s (3000 - s.val) (cutoff (3000 - s.val))
            (by omega) (by omega) (min_le_left _ _)
      · simp [hs]
    _ = ∑ j ∈ range 860, gradeEstimate (1350 - j) := by
      rw [Fin.sum_univ_eq_sum_range
        (fun s : ℕ => if 1650 ≤ s ∧ s < 2510 then gradeEstimate (3000 - s) else 0)]
      rw [show 2510 = 1650 + 860 by decide, sum_window _ (by decide : 1650 + 860 ≤ 4013)]
      exact sum_congr rfl fun j _ => congrArg gradeEstimate (by omega)
    _ = _ := (evaluate_eq _ _).symm.trans evaluate_check
theorem proof : K1_13_2_3.c2 := by
  unfold K1_13_2_3.c2
  have h := scaled_bound
  omega
end K1_13_2_3_2
end
section
namespace K1_10
noncomputable section
open K1 Polynomial
def planeNodes (d : ℕ) (u : Words) (deleted : Finset I) (U V : Fin 2 → (Polynomial K))
    (O : Fin 2 → Fin 2 → (Polynomial K)) : Prop :=
  ∀ i ∉ deleted, ∀ j l, (U l).eval (node i) * u j i + (V j).eval (node i) * (u l i)^d =
    (O j l).eval (node i)
structure Plane (u : Words) (deleted : Finset I) (h : ℕ) (U V : Fin 2 → (Polynomial K)) where
  output : Fin 2 → Fin 2 → (Polynomial K)
  U_ne : ∃ l, U l ≠ 0
  V_ne : ∃ j, V j ≠ 0
  height_eq : max (amplitudeDegree (U 0) (U 1)) (amplitudeDegree (V 0) (V 1)) = h
  primitive : ∀ f : (Polynomial K), (∀ l, f ∣ U l) → (∀ j, f ∣ V j) → IsUnit f
  output_degree : ∀ j l, (output j l).degree < (131072 + h : ℕ)
  nodes : planeNodes p u deleted U V output
structure Adjugate (u : Words) (deleted : Finset I) (h : ℕ) where
  denom : (Polynomial K)
  nonzero : denom ≠ 0
  denom_degree : denom.natDegree ≤ 2 * h
  numer : Fin 2 → (Polynomial K)
  numer_degree : ∀ j, (numer j).degree < (131072 + 2 * h : ℕ)
  nodes : ∀ i ∉ deleted, ∀ j, denom.eval (node i) * u j i = (numer j).eval (node i)
abbrev SeedPoly := MvPolynomial (Fin 2) K
structure ScalarSource where
  poly : MvPolynomial (Fin 2) SeedPoly
  nonzero : poly ≠ 0
  y_degree : poly.degreeOf 1 ≤ 5
  s_degree : ∀ e ∈ poly.support, (poly.coeff e).degreeOf 0 ≤ 26
  t_degree : ∀ e ∈ poly.support, (poly.coeff e).degreeOf 1 ≤ 21
  total : ∀ e ∈ poly.support, e 1 + (poly.coeff e).totalDegree ≤ 37
def ScalarSource.atLabel (A : ScalarSource) (γ : K) : MvPolynomial (Fin 2) K :=
  A.poly.map (MvPolynomial.eval ![γ, γ ^ p])
def sourceDim (d b s t : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (b + 1), ∑ j ∈ Finset.range (b + 1 - i),
    (d + 1 - 131071 * (i+j)) * (s+1-i) * (t+1-j)
def jetDim (m s t : ℕ) : ℕ :=
  ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range (m-i), (m-i-j) * (s+1-i) * (t+1-j)
end
end K1_10
end
section
set_option autoImplicit false
namespace K1_10_1
noncomputable section
open K1 K1_11 MvPolynomial
def relationBounds (h : ℕ) : Fin 4 → ℕ := ![131071 + h, 1, 1, 1]
def liftOrdinary : Polynomial K →+* MvPolynomial (Fin 4) K :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)
def pencil (A : Fin 2 → Polynomial K) (z : MvPolynomial (Fin 4) K) :
    MvPolynomial (Fin 4) K :=
  liftOrdinary (A 0) + z * liftOrdinary (A 1)
def denominator (V : Fin 2 → Polynomial K) : MvPolynomial (Fin 4) K :=
  pencil V (MvPolynomial.X 2)
def numerator (U : Fin 2 → Polynomial K) (O : Fin 2 → Fin 2 → Polynomial K) :
    MvPolynomial (Fin 4) K :=
  pencil (fun j => O j 0) (MvPolynomial.X 2) + MvPolynomial.X 3 * pencil (fun j => O j 1) (MvPolynomial.X 2) -
    pencil U (MvPolynomial.X 3) * MvPolynomial.X 1
def planeRelation (U V : Fin 2 → Polynomial K) (O : Fin 2 → Fin 2 → Polynomial K) :
    MvPolynomial (Fin 5) K :=
  polynomialView.symm (Polynomial.C (denominator V) * Polynomial.X - Polynomial.C (numerator U O))
theorem planeRelation_view (U V : Fin 2 → Polynomial K) (O : Fin 2 → Fin 2 → Polynomial K) :
    polynomialView (planeRelation U V O) =
      Polynomial.C (denominator V) * Polynomial.X - Polynomial.C (numerator U O) :=
  polynomialView.apply_symm_apply _
def shiftAt (u : Words) (i : I) : MvPolynomial (Fin 5) K →ₐ[K] MvPolynomial (Fin 5) K :=
  contactShift (node i) (u 0 i) (u 1 i) (u 0 i ^ p) (u 1 i ^ p)
end
end K1_10_1
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace K1_10_1
noncomputable section
open MvPolynomial K1_11
variable {F : Type*} [Field F] {N : ℕ} {L : MvPolynomial (Fin 5) F}
structure Contacts (N : ℕ) (L : MvPolynomial (Fin 5) F) where
  x : Fin N → F
  first : Fin N → F
  firstSlope : Fin N → F
  second : Fin N → F
  secondSlope : Fin N → F
  order_one : ∀ i, (contactLift contactWeight
    (contactShift (x i) (first i) (firstSlope i) (second i) (secondSlope i) L)).natTrailingDegree = 1
def Contacts.shifted (C : Contacts N L) (i : Fin N) :=
  contactShift (C.x i) (C.first i) (C.firstSlope i) (C.second i) (C.secondSlope i)
variable (C : Contacts N L) {h : ℕ}
    (hdeg : ∀ j, L.weightedTotalDegree (sourceWeights 131071 j) = relationBounds h j)
end
end K1_10_1
end
section
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
namespace K1_10
noncomputable section
open K1 Polynomial FrobeniusLocator
attribute [local instance 2500] K1.Frac._proof_1 K1.ordinary._proof_1
local notation "KS" => @CommSemiring.toSemiring K
  (@Semifield.toCommSemiring K (@Field.toSemifield K
    (@CompPoly.Extension.Ext.instField KoalaBear.Field KoalaBear.instFieldField KoalaBear.ext6Params
      K1.Frac._proof_1 KoalaBear.instFactEqNatCardFieldQExt6Params
      KoalaBear.instFactIrreduciblePolynomialFieldPolyExt6Params)))
end
end K1_10
end
section
set_option autoImplicit false
namespace K1_10_2
noncomputable section
open K1 MvPolynomial
open scoped Polynomial
abbrev Marks (u : Words) (Γ : Finset K) := ∀ γ ∈ Γ, BadMark u γ
abbrev Row := MvPolynomial (Fin 3) (Polynomial K)
abbrev GenericRow := MvPolynomial (Fin 3) Frac
def trajectory (γ : K) (P : (Polynomial K)) : Fin 3 → (Polynomial K) :=
  ![P, Polynomial.C γ, Polynomial.C (γ ^ p)]
def atTrajectory (g : Row) (γ : K) (P : (Polynomial K)) : (Polynomial K) :=
  MvPolynomial.eval (trajectory γ P) g
def derivativeOrder (g : Row) (j : Fin 5) : Row :=
  (MvPolynomial.pderiv (R := (Polynomial K)) (0 : Fin 3))^[j.val] g
def RegularRoot (g : Row) (γ : K) (P : (Polynomial K)) : Prop :=
  atTrajectory g γ P = 0 ∧ atTrajectory (MvPolynomial.pderiv 0 g) γ P ≠ 0
def toGeneric (g : Row) : GenericRow :=
  MvPolynomial.map (algebraMap (Polynomial K) Frac) g
def point (γ : K) (P : (Polynomial K)) : Fin 3 → Frac :=
  (algebraMap (Polynomial K) Frac) ∘ trajectory γ P
def cutDegree : ℕ := (2 * 131071 - 1) * (37 - 1) + 1
structure TaylorCuts {u : Words} {Γ : Finset K} (F : Marks u Γ) where
  equation : I → GenericRow
  degree : ∀ i, (equation i).totalDegree ≤ cutDegree
  agrees : ∀ γ (hγ : γ ∈ Γ) i,
    MvPolynomial.eval (point γ (F γ hγ).decoder) (equation i) = 0 ↔
      (F γ hγ).decoder.eval (node i) = u 0 i + γ * u 1 i
end
end K1_10_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace K1_10_2
noncomputable section
open MvPolynomial
open scoped BigOperators
private theorem ncard_inter_filter {A : Type*} (S : Finset A) (locus : Set A) [DecidablePred (· ∈ locus)] :
    ((S : Set A) ∩ locus).ncard = (S.filter (· ∈ locus)).card := by
  rw [← Set.ncard_coe_finset, Finset.coe_filter]
  rfl
private theorem one_le_degree_of_point {F σ : Type*} [Field F] [Finite σ]
    (J : Ideal (MvPolynomial σ F)) [J.IsPrime] (x : σ → F) (hx : x ∈ zeroLocus F J) :
    1 ≤ affineDegree J := by
  classical
  generalize hd : (affineHilbertPolynomial J).natDegree = d
  induction d using Nat.strong_induction_on generalizing J with
  | ind d ih =>
    by_cases h0 : d = 0
    · have hfin := finite_zeroLocus_and_ncard_le_affineDegree (K := F) J (hd.trans h0)
      have hxone : 1 ≤ (zeroLocus F J).ncard := by
        simpa using Set.ncard_le_ncard (Set.singleton_subset_iff.mpr hx) hfin.1
      exact (by exact_mod_cast hxone : (1 : ℚ) ≤ _).trans hfin.2
    have hproper : ∃ i, MvPolynomial.X i - C (x i) ∉ J := by
      by_contra hn
      push Not at hn
      let φ := Ideal.Quotient.mk J
      have hmaps : φ = φ.comp (C.comp (MvPolynomial.eval x)) := by
        apply MvPolynomial.ringHom_ext
        · intro c
          simp [φ]
        · intro i
          simp only [RingHom.comp_apply, eval_X]
          exact sub_eq_zero.mp (by rw [← map_sub]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (hn i))
      have hsurj : Function.Surjective (algebraMap F (MvPolynomial σ F ⧸ J)) := by
        intro q
        obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
        refine ⟨MvPolynomial.eval x g, ?_⟩
        exact (RingHom.congr_fun hmaps g).symm
      have : Module.Finite F (MvPolynomial σ F ⧸ J) :=
        Module.Finite.of_surjective (Algebra.linearMap F (MvPolynomial σ F ⧸ J)) hsurj
      exact h0 (by rw [← hd, affineHilbertPolynomial_eq_C_finrank, Polynomial.natDegree_C])
    obtain ⟨i, hi⟩ := hproper
    let f := MvPolynomial.X i - C (x i)
    have hxf : aeval x f = 0 := by simp [f]
    have hfdeg : f.totalDegree ≤ 1 := by
      exact (totalDegree_sub _ _).trans (by simp)
    have hxp : x ∈ zeroLocus F (J ⊔ Ideal.span {f}) :=
      mem_zeroLocus_sup_span_singleton_iff.mpr ⟨hx, hxf⟩
    obtain ⟨Q, hQ, hxQ⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus
      (J ⊔ Ideal.span {f}) (1 : MvPolynomial σ F) x hxp (by simp)
    have hQmin := (Ideal.mem_retainedMinimalPrimes.mp hQ).1
    have : Q.IsPrime := hQmin.isPrime
    have hd' := principalCut_natDegree_affineHilbertPolynomial_add_one hi hQmin
    have hone := ih _ (by omega) Q hxQ rfl
    have hsum := principalCut_sum_affineDegree_retainedMinimalPrimes_le
      (1 : MvPolynomial σ F) hi hfdeg
    have hQsum := Finset.single_le_sum (f := affineDegree)
      (fun A _ => affineDegree_nonneg A) hQ
    simpa only [Nat.cast_one, one_mul] using hone.trans (hQsum.trans hsum)
private theorem prime_count_with_terminal {F σ ι : Type*} [Field F] [Finite σ] [Fintype ι]
    (s : MvPolynomial σ F) (cuts : ι → MvPolynomial σ F) {A L M : ℕ}
    (hLA : L ≤ A) (hdeg : ∀ i, (cuts i).totalDegree ≤ M) {R : ℚ} (hR : 1 ≤ R)
    (hratio : ∀ m < L, (((Fintype.card ι - m) * M : ℕ) : ℚ) ≤ R * ((A - m : ℕ) : ℚ))
    (S : Finset (σ → F)) (hreg : ∀ x ∈ S, aeval x s ≠ 0)
    (hA : ∀ x ∈ S, A ≤ {i | aeval x (cuts i) = 0}.ncard)
    (hterminal : ∀ J : Ideal (MvPolynomial σ F), L ≤ {i | cuts i ∈ J}.ncard →
      (((S : Set (σ → F)) ∩ zeroLocus F J).ncard : ℚ) ≤ R)
    (P : Ideal (MvPolynomial σ F)) [P.IsPrime] (W : Finset (σ → F)) (hW : W ⊆ S)
    (hzero : ∀ x ∈ W, x ∈ zeroLocus F P) :
    (W.card : ℚ) ≤ affineDegree P * R ^ (affineHilbertPolynomial P).natDegree := by
  classical
  generalize hd : (affineHilbertPolynomial P).natDegree = d
  induction d using Nat.strong_induction_on generalizing P W with
  | ind d ih =>
    rcases W.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
    · simpa using mul_nonneg (affineDegree_nonneg P) (pow_nonneg (zero_le_one.trans hR) d)
    rcases d with _ | e
    · have hfin := finite_zeroLocus_and_ncard_le_affineDegree (K := F) P hd
      have hcard := Set.ncard_le_ncard
        (fun x (hx : x ∈ (W : Set (σ → F))) => hzero x hx) hfin.1
      rw [Set.ncard_coe_finset] at hcard
      simpa using (by exact_mod_cast hcard : (W.card : ℚ) ≤ _).trans hfin.2
    let keep : Finset ι := Finset.univ.filter fun i => cuts i ∈ P
    have hkeep : keep.card = {i | cuts i ∈ P}.ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext i
      simp [keep]
    by_cases hpers : L ≤ keep.card
    · have hc : W.card ≤ ((S : Set (σ → F)) ∩ zeroLocus F P).ncard := by
        rw [← Set.ncard_coe_finset]
        exact Set.ncard_le_ncard (fun x hx => ⟨hW hx, hzero x hx⟩)
      have hdegP := one_le_degree_of_point P x₀ (hzero x₀ hx₀)
      calc
        (W.card : ℚ) ≤ (((S : Set (σ → F)) ∩ zeroLocus F P).ncard : ℚ) := by exact_mod_cast hc
        _ ≤ R := hterminal P (hkeep ▸ hpers)
        _ ≤ affineDegree P * R ^ (e+1) := by
          calc
            R = 1 * R ^ (1 : ℕ) := by ring
            _ ≤ affineDegree P * R ^ (e+1) :=
              mul_le_mul hdegP (pow_le_pow_right₀ hR (by omega)) (by positivity) (by linarith)
    let rel : (σ → F) → ι → Prop := fun x i => aeval x (cuts i) = 0
    let c : ℚ := ((A - keep.card : ℕ) : ℚ)
    have hc : 0 < c := by
      change (0 : ℚ) < ((A - keep.card : ℕ) : ℚ)
      exact_mod_cast (by omega : 0 < A - keep.card)
    have hlowNat : W.card * (A - keep.card) ≤ ∑ i ∈ keepᶜ, (W.bipartiteBelow rel i).card := by
      refine Finset.card_mul_sub_card_le_sum_compl_card_bipartiteBelow rel keep fun x hx => ?_
      rw [← Set.ncard_coe_finset, Finset.coe_bipartiteAbove]
      simpa [rel] using hA x (hW hx)
    have hlow : (W.card : ℚ) * c ≤ ∑ i ∈ keepᶜ, ((W.bipartiteBelow rel i).card : ℚ) := by
      change (W.card : ℚ) * ((A - keep.card : ℕ) : ℚ) ≤ _
      exact_mod_cast hlowNat
    have hcut : ∀ i ∈ keepᶜ, ((W.bipartiteBelow rel i).card : ℚ) ≤ M * affineDegree P * R^e := by
      intro i hi
      have hiP : cuts i ∉ P := by simpa [keep] using hi
      rw [← Set.ncard_coe_finset, Finset.coe_bipartiteBelow]
      refine ncard_inter_cut_le_of_retained_le s hiP (hdeg i) W
        (fun x hx => ⟨hzero x hx, hreg x (hW hx)⟩) (by positivity) fun Q hQ => ?_
      have hQmin := (Ideal.mem_retainedMinimalPrimes.mp hQ).1
      have : Q.IsPrime := hQmin.isPrime
      have hQdim : (affineHilbertPolynomial Q).natDegree = e := by
        have := principalCut_natDegree_affineHilbertPolynomial_add_one hiP hQmin
        omega
      rw [ncard_inter_filter]
      exact ih e (by omega) Q _ (fun _ hx => hW (Finset.mem_filter.mp hx).1)
        (fun _ hx => (Finset.mem_filter.mp hx).2) hQdim
    have hupp : ∑ i ∈ keepᶜ, ((W.bipartiteBelow rel i).card : ℚ) ≤
        ((Fintype.card ι - keep.card : ℕ) : ℚ) * (M * affineDegree P * R^e) := by
      refine (Finset.sum_le_card_nsmul _ _ _ hcut).trans_eq ?_
      rw [nsmul_eq_mul, Finset.card_compl]
    refine le_of_mul_le_mul_right (hlow.trans (hupp.trans ?_)) hc
    calc
      ((Fintype.card ι - keep.card : ℕ) : ℚ) * (M * affineDegree P * R^e) =
          (((Fintype.card ι - keep.card) * M : ℕ) : ℚ) * (affineDegree P * R^e) := by
        rw [Nat.cast_mul]
        ring
      _ ≤ (R * c) * (affineDegree P * R^e) :=
        mul_le_mul_of_nonneg_right (hratio keep.card (by omega))
          (mul_nonneg (affineDegree_nonneg P) (pow_nonneg (zero_le_one.trans hR) e))
      _ = (affineDegree P * R^(e+1)) * c := by rw [pow_succ]; ring
theorem surface_count_with_terminal {F ι : Type*} [Field F] [Fintype ι]
    (g s : MvPolynomial (Fin 3) F) (hg : g ≠ 0) (cuts : ι → MvPolynomial (Fin 3) F)
    {A L M E : ℕ} (hLA : L ≤ A) (hgdeg : g.totalDegree ≤ E) (hdeg : ∀ i, (cuts i).totalDegree ≤ M)
    {R : ℚ} (hR : 1 ≤ R)
    (hratio : ∀ m < L, (((Fintype.card ι - m) * M : ℕ) : ℚ) ≤ R * ((A - m : ℕ) : ℚ))
    (S : Finset (Fin 3 → F)) (hS : ∀ x ∈ S, aeval x g = 0 ∧ aeval x s ≠ 0)
    (hA : ∀ x ∈ S, A ≤ {i | aeval x (cuts i) = 0}.ncard)
    (hterminal : ∀ J : Ideal (MvPolynomial (Fin 3) F), L ≤ {i | cuts i ∈ J}.ncard →
      (((S : Set (Fin 3 → F)) ∩ zeroLocus F J).ncard : ℚ) ≤ R) :
    (S.card : ℚ) ≤ E * R^2 := by
  classical
  let family := (Ideal.span {g}).retainedMinimalPrimes s
  have hmem (Q) (hQ : Q ∈ family) : g ∈ Q :=
    (Ideal.mem_retainedMinimalPrimes.mp hQ).1.le (Ideal.mem_span_singleton_self g)
  have hdim : ∀ Q ∈ family, (affineHilbertPolynomial Q).natDegree ≤ 2 := by
    intro Q hQ
    simpa [Nat.card_eq_fintype_card] using natDegree_affineHilbertPolynomial_le_of_mem hg (hmem Q hQ)
  have hsum : ∑ Q ∈ family, affineDegree Q ≤ (E : ℚ) := by
    have : (⊥ : Ideal (MvPolynomial (Fin 3) F)).IsPrime := Ideal.isPrime_bot
    have hnot : g ∉ (⊥ : Ideal (MvPolynomial (Fin 3) F)) := by simpa using hg
    simpa only [family, bot_sup_eq, affineDegree_bot, mul_one] using
      principalCut_sum_affineDegree_retainedMinimalPrimes_le s hnot hgdeg
  refine card_le_mul_pow_of_forall_mem_zeroLocus family hdim hsum hR S (fun x hx => ?_) ?_
  · have hxg : x ∈ zeroLocus F (Ideal.span {g}) := mem_zeroLocus_iff_le_ker_aeval.mpr
      ((Ideal.span_singleton_le_iff_mem _).mpr (RingHom.mem_ker.mpr (hS x hx).1))
    exact exists_retainedMinimalPrime_of_mem_zeroLocus _ s x hxg (hS x hx).2
  · intro Q hQ
    have : Q.IsPrime := (Ideal.mem_retainedMinimalPrimes.mp hQ).1.isPrime
    rw [ncard_inter_filter]
    exact prime_count_with_terminal s cuts hLA hdeg hR hratio S
      (fun x hx => (hS x hx).2) hA hterminal Q _
      (fun _ hx => (Finset.mem_filter.mp hx).1) (fun _ hx => (Finset.mem_filter.mp hx).2)
end
end K1_10_2
end
section
set_option autoImplicit false
namespace K1_10_2_2
noncomputable section
open K1 K1_10_2 MvPolynomial
open scoped Polynomial BigOperators
def dx (f : Row) : Row :=
  ∑ m ∈ f.support, monomial m (f.coeff m).derivative
abbrev dy (f : Row) : Row := MvPolynomial.pderiv 0 f
def flow (g f : Row) : Row :=
  dy g * dx f - dx g * dy f
def numerator (g : Row) : ℕ → Row
  | 0 => -dx g
  | n+1 => dy g * flow g (numerator g n) -
    MvPolynomial.C ((2*n+1 : ℕ) : (Polynomial K)) * flow g (dy g) * numerator g n
@[simp] private theorem coeff_dx (f : Row) (m : Fin 3 →₀ ℕ) :
    (dx f).coeff m = (f.coeff m).derivative := by
  classical
  rw [dx, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm, map_zero]
private theorem dx_C (c : (Polynomial K)) :
    dx (MvPolynomial.C c) = MvPolynomial.C c.derivative := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [coeff_dx]
  by_cases hm : 0 = m <;> simp [MvPolynomial.coeff_C, hm]
private theorem dx_add (f q : Row) : dx (f + q) = dx f + dx q := by
  ext m
  simp
private theorem dx_mul_X (f : Row) (j : Fin 3) :
    dx (f * MvPolynomial.X j) = dx f * MvPolynomial.X j := by
  classical
  ext m
  rw [coeff_dx, MvPolynomial.coeff_mul_X', MvPolynomial.coeff_mul_X']
  split_ifs <;> simp
private theorem trajectory_chain (γ : K) (P : (Polynomial K)) (f : Row) :
    (atTrajectory f γ P).derivative = atTrajectory (dx f) γ P +
      P.derivative * atTrajectory (dy f) γ P := by
  have hconstant (j : Fin 3) (hj : j ≠ 0) : (trajectory γ P j).derivative = 0 := by
    fin_cases j
    · exact (hj rfl).elim
    · exact Polynomial.derivative_C
    · exact Polynomial.derivative_C
  unfold atTrajectory
  induction f using MvPolynomial.induction_on with
  | C c => simp [dx_C]
  | add f q hf hq =>
    simp only [map_add, dx_add, hf, hq, dy, mul_add]
    ring
  | mul_X f j ih =>
    rw [map_mul, MvPolynomial.eval_X, Polynomial.derivative_mul, ih, dx_mul_X,
      map_mul, MvPolynomial.eval_X]
    simp only [dy, MvPolynomial.pderiv_mul, map_add, map_mul, MvPolynomial.eval_X]
    by_cases hj : j = 0
    · subst j
      rw [show (trajectory γ P 0).derivative = P.derivative from rfl,
        MvPolynomial.pderiv_X_self, map_one]
      ring
    · rw [hconstant j hj, MvPolynomial.pderiv_X_of_ne hj, map_zero]
      ring
private theorem eval_flow (g f : Row) (γ : K) (P : (Polynomial K)) (hg : atTrajectory g γ P = 0) :
    atTrajectory (flow g f) γ P = atTrajectory (dy g) γ P * (atTrajectory f γ P).derivative := by
  have hz : atTrajectory (dx g) γ P + P.derivative * atTrajectory (dy g) γ P = 0 := by
    rw [← trajectory_chain, hg, map_zero]
  rw [trajectory_chain]
  simp only [flow, atTrajectory, map_sub, map_mul]
  unfold atTrajectory at hz
  linear_combination -MvPolynomial.eval (trajectory γ P) (dy f) * hz
private theorem cleared_product_rule (a : ℕ) (U V : (Polynomial K)) :
    U * (U * (U^a * V).derivative) - (a : (Polynomial K)) * (U * U.derivative) * (U^a * V) =
      U^(a+2) * V.derivative := by
  cases a with
  | zero => simp [pow_two, mul_assoc]
  | succ a =>
    rw [Polynomial.derivative_mul, Polynomial.derivative_pow, Nat.succ_sub_one,
      pow_add U (a+1) 2, pow_succ' U a]
    simp only [Polynomial.C_eq_natCast]
    push_cast
    ring
theorem eval_numerator (g : Row) (γ : K) (P : (Polynomial K))
    (hg : atTrajectory g γ P = 0) (n : ℕ) :
    atTrajectory (numerator g n) γ P =
      atTrajectory (dy g) γ P ^ (2*n+1) * ((Polynomial.derivative (R := K))^[n+1]) P := by
  induction n with
  | zero =>
    have hz := trajectory_chain γ P g
    rw [hg, map_zero] at hz
    change MvPolynomial.eval (trajectory γ P) (-dx g) = _
    rw [map_neg]
    change -atTrajectory (dx g) γ P = _
    simp only [Nat.zero_add, Nat.mul_zero, pow_one, Function.iterate_one]
    linear_combination hz
  | succ n ih =>
    change MvPolynomial.eval (trajectory γ P) (_ - _) = _
    rw [map_sub, map_mul, map_mul, map_mul, MvPolynomial.eval_C]
    change atTrajectory (dy g) γ P * atTrajectory (flow g (numerator g n)) γ P -
      ((2*n+1 : ℕ) : (Polynomial K)) * atTrajectory (flow g (dy g)) γ P *
        atTrajectory (numerator g n) γ P = _
    rw [eval_flow _ _ _ _ hg, eval_flow _ _ _ _ hg, ih, cleared_product_rule,
      show 2*(n+1)+1 = 2*n+1+2 by omega]
    congr 1
    exact (Function.iterate_succ_apply' _ _ _).symm
theorem dx_degree (f : Row) : (dx f).totalDegree ≤ f.totalDegree := by
  classical
  apply totalDegree_le_of_support_subset
  intro m hm
  contrapose! hm
  rw [MvPolynomial.notMem_support_iff] at hm ⊢
  rw [coeff_dx, hm, map_zero]
theorem dy_degree (f : Row) : (dy f).totalDegree ≤ f.totalDegree - 1 := by
  simpa only [weightedTotalDegree_one, Pi.one_apply] using
    weightedTotalDegree_pderiv_le_sub (1 : Fin 3 → ℕ) (0 : Fin 3) f
end
end K1_10_2_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
namespace K1_10_2
noncomputable section
open K1 K1_10 MvPolynomial
open scoped Polynomial
private theorem pderiv_degree (g : Row) :
    (MvPolynomial.pderiv (0 : Fin 3) g).totalDegree ≤ g.totalDegree := by
  simpa only [weightedTotalDegree_one] using
    weightedTotalDegree_pderiv_le (1 : Fin 3 → ℕ) (0 : Fin 3) g
theorem derivativeOrder_degree (g : Row) (j : Fin 5) :
    (derivativeOrder g j).totalDegree ≤ g.totalDegree := by
  have h (n : ℕ) :
      (((MvPolynomial.pderiv (R := (Polynomial K)) (0 : Fin 3))^[n]) g).totalDegree ≤
        g.totalDegree := by
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (pderiv_degree _).trans ih
  exact h j.val
theorem eval_toGeneric (g : Row) (γ : K) (P : (Polynomial K)) :
    MvPolynomial.eval (point γ P) (toGeneric g) = algebraMap (Polynomial K) Frac (atTrajectory g γ P) := by
  rw [toGeneric, MvPolynomial.eval_map]
  exact (MvPolynomial.eval₂_comp (algebraMap (Polynomial K) Frac) (trajectory γ P) g).symm
end
end K1_10_2
end
section
set_option autoImplicit false
namespace K1_10_2_2
noncomputable section
open K1 K1_10_2 MvPolynomial
open scoped Polynomial BigOperators
private def width : ℕ := 131071
def clearPower : ℕ := 2 * width - 1
private abbrev fracMap : (Polynomial K) →+* Frac := algebraMap (Polynomial K) Frac
private abbrev embed : K →+* Frac := fracMap.comp Polynomial.C
private abbrev centre : Frac := fracMap Polynomial.X
private theorem eval_at_centre (P : (Polynomial K)) : (P.map embed).eval centre = fracMap P := by
  rw [Polynomial.eval_map]
  simpa only [Polynomial.eval₂_C_X] using
    (Polynomial.hom_eval₂ P Polynomial.C fracMap Polynomial.X).symm
private theorem factorial_ne_zero_of_lt {n : ℕ} (hn : n < p) : (n.factorial : Frac) ≠ 0 := by
  let : CharP Frac p := charP_of_injective_ringHom embed.injective p
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : ((n + 1 : ℕ) : Frac) ≠ 0 := by
      intro hz
      have hd := (CharP.cast_eq_zero_iff Frac p (n+1)).mp hz
      exact (not_le_of_gt hn) (Nat.le_of_dvd (Nat.succ_pos n) hd)
    simpa only [Nat.factorial_succ, Nat.cast_mul] using
      mul_ne_zero hc (ih (Nat.lt_of_succ_lt hn))
private abbrev derivativeAt (P : (Polynomial K)) (n : ℕ) : Frac :=
  fracMap (((Polynomial.derivative (R := K))^[n]) P)
private def taylorScalar (x : K) (n : ℕ) : Frac :=
  (n.factorial : Frac)⁻¹ * (embed x - centre)^n
private theorem taylor_term (P : (Polynomial K)) (x : K) (n : ℕ) (hn : n < p) :
    (Polynomial.taylor centre (P.map embed)).coeff n * (embed x - centre)^n =
      derivativeAt P n * taylorScalar x n := by
  rw [Polynomial.taylor_coeff, Polynomial.hasseDeriv_map, eval_at_centre]
  have h := congrFun (Polynomial.factorial_smul_hasseDeriv (R := K) n) P
  have hfactor : derivativeAt P n = (n.factorial : Frac) * fracMap (Polynomial.hasseDeriv n P) := by
    unfold derivativeAt
    rw [← h]
    simp only [LinearMap.smul_apply]
    rw [nsmul_eq_mul, map_mul, map_natCast]
  rw [hfactor, taylorScalar]
  symm
  calc
    _ = (fracMap (Polynomial.hasseDeriv n P) * (embed x - centre)^n) *
        ((n.factorial : Frac) * (n.factorial : Frac)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ (factorial_ne_zero_of_lt hn), mul_one]
private theorem eval_taylor (P : (Polynomial K)) (hP : P.degree < 131072) (x : K) :
    embed (P.eval x) = fracMap P +
      ∑ n ∈ Finset.range width, derivativeAt P (n+1) * taylorScalar x (n+1) := by
  have hd : (Polynomial.taylor centre (P.map embed)).natDegree < width+1 := by
    rw [Polynomial.natDegree_taylor]
    apply Polynomial.natDegree_map_le.trans_lt
    by_cases hzero : P = 0
    · rw [hzero, Polynomial.natDegree_zero]
      exact Nat.zero_lt_succ width
    · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mpr hP
  calc
    _ = (Polynomial.taylor centre (P.map embed)).eval (embed x - centre) := by
      rw [Polynomial.taylor_eval_sub, Polynomial.eval_map_apply]
    _ = _ := by
      rw [Polynomial.eval_eq_sum_range' hd, Finset.sum_range_succ']
      simp only [Polynomial.taylor_coeff_zero, eval_at_centre, pow_zero, mul_one]
      rw [add_comm]
      refine congrArg (fun s : Frac => fracMap P + s) (Finset.sum_congr rfl ?_)
      intro n hn
      apply taylor_term
      have hn' := Finset.mem_range.mp hn
      change n < 131071 at hn'
      change n+1 < 2130706433
      omega
abbrev separant (g : Row) : GenericRow := toGeneric (dy g)
def taylorNumerator (g : Row) (x : K) : GenericRow :=
  separant g ^ clearPower * MvPolynomial.X 0 +
    ∑ n ∈ Finset.range width,
      separant g ^ (clearPower - (2*n+1)) * toGeneric (numerator g n) *
        MvPolynomial.C (taylorScalar x (n+1))
def received (u : Words) (i : I) : GenericRow :=
  MvPolynomial.C (embed (u 0 i)) + MvPolynomial.X 1 * MvPolynomial.C (embed (u 1 i))
def nodeCut (u : Words) (g : Row) (i : I) : GenericRow :=
  taylorNumerator g (node i) - separant g ^ clearPower * received u i
theorem toGeneric_degree (f : Row) : (toGeneric f).totalDegree ≤ f.totalDegree := by
  rw [totalDegree_eq, totalDegree_eq]
  exact Finset.sup_mono (MvPolynomial.support_map_subset fracMap f)
theorem order_le_clearPower {n : ℕ} (hn : n ∈ Finset.range width) :
    2*n+1 ≤ clearPower := by
  have hn' := Finset.mem_range.mp hn
  unfold width at hn'
  unfold clearPower width
  omega
theorem received_degree (u : Words) (i : I) : (received u i).totalDegree ≤ 1 := by
  unfold received
  apply (totalDegree_add _ _).trans
  rw [totalDegree_C, Nat.zero_max]
  exact (totalDegree_mul _ _).trans (by rw [totalDegree_X, totalDegree_C])
private theorem eval_toGeneric (f : Row) (γ : K) (P : (Polynomial K)) :
    MvPolynomial.eval (point γ P) (toGeneric f) = fracMap (atTrajectory f γ P) := by
  rw [toGeneric, MvPolynomial.eval_map]
  exact (MvPolynomial.eval₂_comp fracMap (trajectory γ P) f).symm
private theorem eval_taylorNumerator (g : Row) (γ : K) (P : (Polynomial K))
    (hg : atTrajectory g γ P = 0) (hP : P.degree < 131072) (x : K) :
    MvPolynomial.eval (point γ P) (taylorNumerator g x) =
      fracMap (atTrajectory (dy g) γ P) ^ clearPower * embed (P.eval x) := by
  let a := fracMap (atTrajectory (dy g) γ P)
  simp only [taylorNumerator, map_add, map_mul, map_pow, map_sum, MvPolynomial.eval_X,
    MvPolynomial.eval_C, eval_toGeneric]
  change a ^ clearPower * fracMap P + (∑ n ∈ Finset.range width,
    a ^ (clearPower - (2*n+1)) * fracMap (atTrajectory (numerator g n) γ P) *
      taylorScalar x (n+1)) = a ^ clearPower * embed (P.eval x)
  rw [eval_taylor P hP, mul_add, Finset.mul_sum]
  refine congrArg (fun s : Frac => a ^ clearPower * fracMap P + s) (Finset.sum_congr rfl ?_)
  intro n hn
  rw [eval_numerator g γ P hg, map_mul, map_pow]
  change a ^ (clearPower - (2*n+1)) * (a ^ (2*n+1) * derivativeAt P (n+1)) *
    taylorScalar x (n+1) = a ^ clearPower * (derivativeAt P (n+1) * taylorScalar x (n+1))
  rw [← mul_assoc (a ^ (clearPower - (2*n+1))), mul_assoc _ (derivativeAt P (n+1)),
    ← pow_add, Nat.sub_add_cancel (order_le_clearPower hn)]
theorem eval_nodeCut (u : Words) (g : Row) (γ : K) (P : (Polynomial K))
    (hg : RegularRoot g γ P) (hP : P.degree < 131072) (i : I) :
    MvPolynomial.eval (point γ P) (nodeCut u g i) = 0 ↔
      P.eval (node i) = u 0 i + γ * u 1 i := by
  have hsep : fracMap (atTrajectory (dy g) γ P) ≠ 0 :=
    (map_ne_zero_iff fracMap (IsFractionRing.injective (Polynomial K) Frac)).mpr hg.2
  have hreceived : MvPolynomial.eval (point γ P) (received u i) =
      embed (u 0 i + γ * u 1 i) := by
    simp only [received, map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      show point γ P 1 = embed γ from rfl]
  rw [nodeCut, map_sub, map_mul, map_pow, eval_taylorNumerator g γ P hg.1 hP,
    eval_toGeneric, hreceived, ← mul_sub, mul_eq_zero, or_iff_right (pow_ne_zero _ hsep),
    sub_eq_zero]
  exact embed.injective.eq_iff
end
end K1_10_2_2
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1200000
namespace K1_10_2_1
noncomputable section
open K1 K1_10 K1_10_2 MvPolynomial
open scoped Polynomial
section Regroup
variable {L : Type*} [CommRing L]
def seedRow : MvPolynomial (Fin 2) L →+* MvPolynomial (Fin 3) (Polynomial L) :=
  (rename (Fin.succ : Fin 2 → Fin 3)).toRingHom.comp (MvPolynomial.map Polynomial.C)
def regroup : MvPolynomial (Fin 2) (MvPolynomial (Fin 2) L) →+*
    MvPolynomial (Fin 3) (Polynomial L) :=
  eval₂Hom seedRow ![C Polynomial.X, MvPolynomial.X 0]
theorem seedRow_degree (a : MvPolynomial (Fin 2) L) :
    (seedRow a).totalDegree ≤ a.totalDegree := by
  change (rename Fin.succ (MvPolynomial.map Polynomial.C a)).totalDegree ≤ a.totalDegree
  exact (totalDegree_rename_le _ _).trans (Finset.sup_mono (support_map_subset _ _))
end Regroup
section Specialize
variable {R : Type*} [CommRing R]
def specialize (s t : R) : MvPolynomial (Fin 3) R →+* (Polynomial R) :=
  eval₂Hom Polynomial.C ![Polynomial.X, Polynomial.C s, Polynomial.C t]
theorem eval_specialize (g : MvPolynomial (Fin 3) R) (s t P : R) :
    (specialize s t g).eval P = MvPolynomial.eval ![P, s, t] g := by
  have h : (Polynomial.evalRingHom P).comp (specialize s t) =
      MvPolynomial.eval ![P, s, t] := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [specialize]
    · intro i
      fin_cases i <;> simp [specialize]
  exact RingHom.congr_fun h g
theorem specialize_pderiv (g : MvPolynomial (Fin 3) R) (s t : R) :
    specialize s t (pderiv 0 g) = Polynomial.derivative (specialize s t g) := by
  classical
  induction g using MvPolynomial.induction_on with
  | C a => simp [specialize, Polynomial.derivative_C]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f i hf =>
    have hx : specialize s t (pderiv 0 (MvPolynomial.X i)) =
        Polynomial.derivative (specialize s t (MvPolynomial.X i)) := by
      fin_cases i <;> simp [specialize, Polynomial.derivative_C, Polynomial.derivative_X]
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hf, hx,
      Polynomial.derivative_mul]
    ac_rfl
theorem specialize_iterate (s t : R) (g : MvPolynomial (Fin 3) R) (j : ℕ) :
    specialize s t ((pderiv (R := R) (0 : Fin 3))^[j] g) =
      Polynomial.derivative^[j] (specialize s t g) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply', specialize_pderiv, ih]
end Specialize
section DecoderView
variable {L : Type*} [CommRing L]
def decoderView : MvPolynomial (Fin 2) L →+* (Polynomial (Polynomial L)) :=
  (Polynomial.mapRingHom (uniqueAlgEquiv L (Fin 1)).toRingHom).comp
    ((finSuccEquiv L 1).toRingHom.comp (rename (Fin.rev : Fin 2 → Fin 2)).toRingHom)
private theorem decoderView_eq :
    (decoderView (L := L)) = eval₂Hom (Polynomial.C.comp Polynomial.C)
      ![Polynomial.C Polynomial.X, Polynomial.X] := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [decoderView, finSuccEquiv_apply, uniqueAlgEquiv_apply]
  · intro i
    fin_cases i <;> rw [eval₂Hom_X']
    · have hx : finSuccEquiv L 1 (rename Fin.rev (MvPolynomial.X (0 : Fin 2))) =
          Polynomial.C (MvPolynomial.X (0 : Fin 1)) := by
        rw [rename_X, show Fin.rev (0 : Fin 2) = Fin.succ (0 : Fin 1) by rfl,
          finSuccEquiv_X_succ]
      change (finSuccEquiv L 1 (rename Fin.rev (MvPolynomial.X (0 : Fin 2)))).map
        (uniqueAlgEquiv L (Fin 1)).toRingHom = Polynomial.C Polynomial.X
      rw [hx]
      simp [uniqueAlgEquiv_apply]
    · have hx : finSuccEquiv L 1 (rename Fin.rev (MvPolynomial.X (1 : Fin 2))) =
          Polynomial.X := by
        rw [rename_X, show Fin.rev (1 : Fin 2) = 0 by rfl, finSuccEquiv_X_zero]
      change (finSuccEquiv L 1 (rename Fin.rev (MvPolynomial.X (1 : Fin 2)))).map
        (uniqueAlgEquiv L (Fin 1)).toRingHom = Polynomial.X
      rw [hx, Polynomial.map_X]
theorem decoderView_injective : Function.Injective (decoderView (L := L)) :=
  (Polynomial.map_injective _ (uniqueAlgEquiv L (Fin 1)).injective).comp
    ((finSuccEquiv L 1).injective.comp (rename_injective _ Fin.rev_injective))
theorem decoderView_degree (v : MvPolynomial (Fin 2) L) :
    (decoderView v).natDegree ≤ v.degreeOf 1 := by
  change ((finSuccEquiv L 1 (rename Fin.rev v)).map _).natDegree ≤ v.degreeOf 1
  apply Polynomial.natDegree_map_le.trans
  rw [natDegree_finSuccEquiv, ← show Fin.rev (1 : Fin 2) = 0 by rfl]
  exact (degreeOf_rename_of_injective Fin.rev_injective 1).le
theorem specialize_regroup (v : MvPolynomial (Fin 2) (MvPolynomial (Fin 2) L))
    (s t : L) :
    specialize (Polynomial.C s) (Polynomial.C t) (regroup v) =
      decoderView (v.map (MvPolynomial.eval ![s, t])) := by
  let seeds : MvPolynomial (Fin 2) L →+* L := MvPolynomial.eval ![s, t]
  have hseed : (specialize (Polynomial.C s) (Polynomial.C t)).comp seedRow =
      (Polynomial.C.comp Polynomial.C).comp seeds := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [specialize, seedRow, seeds]
    · intro i
      fin_cases i <;> simp [specialize, seedRow, seeds]
  have h : (specialize (Polynomial.C s) (Polynomial.C t)).comp regroup =
      decoderView.comp (MvPolynomial.map seeds) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simpa [regroup, decoderView_eq, RingHom.comp_apply] using RingHom.congr_fun hseed a
    · intro i
      fin_cases i <;> simp [regroup, specialize, decoderView_eq]
  exact RingHom.congr_fun h v
theorem eval_decoderView (v : MvPolynomial (Fin 2) L) (P : (Polynomial L)) :
    (decoderView v).eval P = MvPolynomial.aeval ![Polynomial.X, P] v := by
  have h : (Polynomial.evalRingHom P).comp decoderView =
      (MvPolynomial.aeval ![Polynomial.X, P]).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [decoderView_eq]
    · intro i
      fin_cases i <;> simp [decoderView_eq]
  exact RingHom.congr_fun h v
end DecoderView
open Polynomial in
theorem exists_simple_derivative {R : Type*} [CommRing R] [IsDomain R]
    (q B : ℕ) [CharP R q] (f : (Polynomial R)) (hf : f ≠ 0) (hdegree : f.natDegree ≤ B)
    (hsmall : B < q) (y : R) (hroot : f.IsRoot y) :
    ∃ j < B, (Polynomial.derivative^[j] f).IsRoot y ∧
      ¬ (Polynomial.derivative (Polynomial.derivative^[j] f)).IsRoot y := by
  let μ := f.rootMultiplicity y
  have hμpos : 0 < μ := (rootMultiplicity_pos hf).mpr hroot
  have hμle : μ ≤ B := by
    have hd := natDegree_le_of_dvd (f.pow_rootMultiplicity_dvd y) hf
    have hle : μ ≤ f.natDegree := by simpa [μ, natDegree_pow] using hd
    exact hle.trans hdegree
  have hnzd : ∀ m ≤ μ, m ≠ 0 → (m : R) ∈ nonZeroDivisors R := by
    intro m hm hmn
    apply mem_nonZeroDivisors_of_ne_zero
    intro hz
    have hd : q ∣ m := (CharP.cast_eq_zero_iff R q m).mp hz
    have hq : q ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hmn) hd
    omega
  have hnext : ¬ (derivative^[μ] f).IsRoot y := by
    intro hnext
    have hall : ∀ m ≤ μ, (derivative^[m] f).IsRoot y := by
      intro m hm
      rcases lt_or_eq_of_le hm with hh | rfl
      · exact isRoot_iterate_derivative_of_lt_rootMultiplicity hh
      · exact hnext
    exact (Nat.lt_irrefl μ)
      (lt_rootMultiplicity_of_isRoot_iterate_derivative_of_mem_nonZeroDivisors' hf hall hnzd)
  refine ⟨μ - 1, by omega, isRoot_iterate_derivative_of_lt_rootMultiplicity (by omega), ?_⟩
  have he : derivative (derivative^[μ - 1] f) = derivative^[μ] f := by
    simpa only [Nat.succ_eq_add_one, Nat.sub_add_cancel hμpos] using
      (Function.iterate_succ_apply' derivative (μ - 1) f).symm
  rwa [he]
end
end K1_10_2_1
end
section
namespace K1_14_4
noncomputable section
open K1_14 Polynomial MvPolynomial
private abbrev Flat := MvPolynomial (Option (Fin 2)) FX
def flatten : Equation ≃ₐ[FX] Flat := (optionEquivLeft FX (Fin 2)).symm
def seedView : Equation ≃ₐ[FX] MvPolynomial (Fin 2) (Polynomial FX) :=
  flatten.trans (optionEquivRight FX (Fin 2))
def seedDegree (f : Equation) : ℕ := (seedView f).totalDegree
theorem seedView_coeff (f : Equation) (i : ℕ) (d : Fin 2 →₀ ℕ) :
    ((seedView f).coeff d).coeff i = (f.coeff i).coeff d := by
  change ((optionEquivRight FX (Fin 2) (flatten f)).coeff d).coeff i = _
  rw [optionEquivRight_coeff_coeff, ← optionEquivLeft_coeff_coeff]
  simp [flatten]
theorem seedDegree_le_iff (f : Equation) (u : ℕ) :
    seedDegree f ≤ u ↔ SeedBound f u := by
  unfold seedDegree SeedBound
  simp only [MvPolynomial.totalDegree, Finset.sup_le_iff]
  constructor
  · intro h i d hd
    apply h d
    rw [MvPolynomial.mem_support_iff] at hd ⊢
    intro hz
    apply hd
    rw [← seedView_coeff, hz, Polynomial.coeff_zero]
  · intro h d hd
    obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr (MvPolynomial.mem_support_iff.mp hd)
    apply h i d
    rwa [MvPolynomial.mem_support_iff, ← seedView_coeff, ← Polynomial.mem_support_iff]
theorem seedDegree_mul {f g : Equation} (hf : f ≠ 0) (hg : g ≠ 0) :
    seedDegree (f * g) = seedDegree f + seedDegree g := by
  unfold seedDegree
  rw [map_mul, totalDegree_mul_of_isDomain (by simpa using hf) (by simpa using hg)]
theorem seedDegree_pow {f : Equation} (hf : f ≠ 0) (n : ℕ) :
    seedDegree (f ^ n) = n * seedDegree f := by
  induction n with
  | zero => simp [seedDegree]
  | succ n ih => rw [pow_succ, seedDegree_mul (pow_ne_zero _ hf) hf, ih, Nat.succ_mul]
end
end K1_14_4
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 850000
namespace K1_14_2_2R
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_4 Polynomial
open scoped Classical
private def unflatten : Ambient →+* Jet :=
  MvPolynomial.eval₂Hom (C.comp (C.comp MvPolynomial.C))
    ![C (C (MvPolynomial.X 0)), C (C (MvPolynomial.X 1)),
      C (Polynomial.X (R := Seeds)), Polynomial.X (R := Equation)]
private theorem to_from : toJet.comp unflatten = RingHom.id Ambient := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [unflatten, toJet, toRoot, rootIncl, rootSeeds]
  · intro i
    fin_cases i <;> simp [unflatten, toJet, toRoot, rootIncl, rootSeeds]
private theorem from_to : unflatten.comp toJet = RingHom.id Jet := by
  apply Polynomial.ringHom_ext
  · intro f
    suffices h : (unflatten.comp toJet).comp C = (RingHom.id Jet).comp C from
      DFunLike.congr_fun h f
    apply Polynomial.ringHom_ext
    · intro a
      suffices h : ((unflatten.comp toJet).comp C).comp C =
          ((RingHom.id Jet).comp C).comp C from DFunLike.congr_fun h a
      apply MvPolynomial.ringHom_ext
      · intro c
        simp [unflatten, toJet, toRoot, rootIncl, rootSeeds]
      · intro i
        fin_cases i <;> simp [unflatten, toJet, toRoot, rootIncl, rootSeeds]
    · simp [unflatten, toJet, toRoot, rootIncl, rootSeeds]
  · simp [unflatten, toJet]
theorem toJet_relPrime_of_properPair {P Q : Jet} (h : K1_14_3_2.ProperPair P Q) :
    IsRelPrime (toJet P) (toJet Q) := by
  have hrel : IsRelPrime P Q := WfDvdMonoid.isRelPrime_of_no_irreducible_factors
    (fun hp => h.left_ne hp.1) (fun d hi hd => h.no_common d hi hd)
  intro d hdP hdQ
  have un (a : Jet) : unflatten (toJet a) = a := DFunLike.congr_fun from_to a
  have hd : IsUnit (unflatten d) :=
    hrel (by simpa only [un] using map_dvd unflatten hdP)
         (by simpa only [un] using map_dvd unflatten hdQ)
  have hD : toJet (unflatten d) = d := DFunLike.congr_fun to_from d
  rw [← hD]
  exact hd.map toJet
private theorem seed_le (f : Equation) (i : ℕ) :
    (f.coeff i).totalDegree ≤ seedDegree f := by
  by_cases h : i ∈ f.support
  · exact Finset.le_sup (f := fun j => (f.coeff j).totalDegree) h
  · simp [Polynomial.notMem_support_iff.mp h]
private theorem as_seed_degree (f : Equation) : seedDegree f = K1_14_4.seedDegree f := by
  apply le_antisymm
  · exact Finset.sup_le fun i _ => (K1_14_4.seedDegree_le_iff f _).mp le_rfl i
  · exact (K1_14_4.seedDegree_le_iff f _).mpr (seed_le f)
private def graphShape (f : Equation) (j : ℕ) : Shape := ⟨1, f.natDegree, j, seedDegree f⟩
private theorem factor_caps (f : Equation) (j : ℕ) : RowCaps (C f) (graphShape f j) := by
  intro v y hy
  cases v with
  | zero =>
    rw [coeff_C_zero] at hy ⊢
    exact ⟨by simpa [graphShape] using le_natDegree_of_ne_zero hy, Nat.zero_le _, seed_le _ _⟩
  | succ v => simp [coeff_C_succ] at hy
private theorem order_one {I : Ideal Ambient} {P : Jet} (hi : I.IsPrime) (h : toJet P ∈ I) :
    orderOn I P 1 := by
  refine ⟨1, hi.one_notMem, ?_⟩
  rw [one_mul, pow_one]
  exact Ideal.mem_sup_left h
private theorem graph_mass (lengths : K1_14_2_2_4.c4) (sections : K1_14_2_2_4.c5)
    {P Q : Jet} {f : Equation} (hf : Irreducible f) (hpos : 0 < f.natDegree)
    (hsmall : f.natDegree < p) (hP : C f ∣ P) (hQ : C f ∣ Q)
    (S : Finset (Ideal Ambient))
    (hS : ∀ I ∈ S, Active I ∧ chainCompatible P Q I ∧ toJet (C f) ∈ I) (k : Fin 4) :
    mass S k ≤ highCap (seedDegree f) f.natDegree k := by
  obtain ⟨g, a, ha, hp, _⟩ := K1_14_3R.ordinary_graph f hf hpos hsmall
  have hc : RowCaps (K1_14_3R.chainCutter g) (graphShape f 1) :=
    K1_14_3R.chainCutter_caps_of_dvd hp.left_ne (factor_caps f 1) le_rfl (dvd_refl _) ha
  have h := sections (C f) (K1_14_3R.chainCutter g) (graphShape f 0) (graphShape f 1)
    S k 1 hp.left_ne hp.right_ne (toJet_relPrime_of_properPair hp) (Nat.zero_le _) hpos (factor_caps f 0) hc
    (by decide) (by
      intro I hI
      obtain ⟨active, comp, hon⟩ := hS I hI
      have hc' := comp f hf hpos hP hQ hon g a ha
      refine ⟨active, fun _ => ?_⟩
      simpa using lengths _ _ I active 1 (by decide)
        (order_one active.prime hon) (order_one active.prime hc'))
  fin_cases k <;> simpa [graphShape, pairCap, highCap, two_mul, Nat.add_mul] using h
private theorem high_add (x z y w : ℕ) (k : Fin 4) :
    highCap x z k + highCap y w k ≤ highCap (x+y) (z+w) k := by
  fin_cases k <;> simp [highCap] <;> nlinarith
private theorem high_mul (r x z : ℕ) (k : Fin 4) :
    highScale r k * highCap x z k = highCap (r*x) (r*z) k := by
  fin_cases k <;> simp [highCap, highScale] <;> ring
private theorem cancel_power {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]
    {e f T : R} {r : ℕ} (h : IsRelPrime e f) (hd : e^r ∣ f^r * T) : e^r ∣ T :=
  h.pow.dvd_of_dvd_mul_left hd
private theorem residual_power {e f T : Equation} {r : ℕ} (h : IsRelPrime e f)
    (hd : e^r ∣ f^r * T) : e^r ∣ T := by
  let : UniqueFactorizationMonoid FX := PrincipalIdealRing.to_uniqueFactorizationMonoid
  let : UniqueFactorizationMonoid Seeds := MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  let : UniqueFactorizationMonoid Equation := Polynomial.uniqueFactorizationMonoid
  exact cancel_power h hd
theorem high_graph_mass (lengths : K1_14_2_2_4.c4) (sections : K1_14_2_2_4.c5)
    (H : Equation) (P Q : Jet) (S : Finset (Ideal Ambient)) (r : ℕ)
    (hH : H ≠ 0) (hp : H.natDegree < p) (hr : 0 < r)
    (hP : C H ∣ P) (hQ : C H ∣ Q)
    (hS : ∀ I ∈ S, Active I ∧ chainCompatible P Q I ∧ HighOn H r I) (k : Fin 4) :
    highScale r k * mass S k ≤ highCap (seedDegree H) H.natDegree k := by
  classical
  by_cases hs : S.Nonempty
  · obtain ⟨I, hI⟩ := hs
    obtain ⟨f, hf, hpos, hpow, _⟩ := (hS I hI).2.2
    obtain ⟨T, hfac⟩ := hpow
    have hT : T ≠ 0 := by
      intro hz
      exact hH (by simp [hfac, hz])
    have hdeg : H.natDegree = r * f.natDegree + T.natDegree := by
      rw [hfac, natDegree_mul (pow_ne_zero _ hf.ne_zero) hT, natDegree_pow]
    have hseed : seedDegree H = r * seedDegree f + seedDegree T := by
      simp only [as_seed_degree, hfac, K1_14_4.seedDegree_mul (pow_ne_zero _ hf.ne_zero) hT,
        K1_14_4.seedDegree_pow hf.ne_zero]
    have hfd : f ∣ H := (dvd_pow_self f hr.ne').trans ⟨T, hfac⟩
    have hTd : T ∣ H := ⟨f ^ r, hfac.trans (mul_comm _ _)⟩
    let on (J : Ideal Ambient) := toJet (C f) ∈ J
    have hg := graph_mass lengths sections hf hpos ((natDegree_le_of_dvd hfd hH).trans_lt hp)
      ((_root_.map_dvd (C : Equation →+* Jet) hfd).trans hP) ((_root_.map_dvd (C : Equation →+* Jet) hfd).trans hQ) (S.filter on)
      (fun J hJ => by
        obtain ⟨hm, ho⟩ := Finset.mem_filter.mp hJ
        exact ⟨(hS J hm).1, (hS J hm).2.1, ho⟩) k
    have ht := high_graph_mass lengths sections T P Q (S.filter fun J => ¬ on J) r hT
      ((natDegree_le_of_dvd hTd hH).trans_lt hp) hr
      ((_root_.map_dvd (C : Equation →+* Jet) hTd).trans hP) ((_root_.map_dvd (C : Equation →+* Jet) hTd).trans hQ) (by
        intro J hJ
        obtain ⟨hm, ho⟩ := Finset.mem_filter.mp hJ
        obtain ⟨active, comp, e, he, hy, hd, hmem⟩ := hS J hm
        have hcop : IsRelPrime e f := he.isRelPrime_iff_not_dvd.mpr (by
          rintro ⟨b, hb⟩
          apply ho
          change toJet (C f) ∈ J
          rw [hb, map_mul, map_mul]
          exact J.mul_mem_right _ hmem)
        refine ⟨active, comp, e, he, hy, residual_power hcop ?_, hmem⟩
        simpa only [← hfac] using hd) k
    have hadd : mass (S.filter on) k + mass (S.filter fun J => ¬ on J) k = mass S k :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    rw [← hadd, Nat.mul_add, hseed, hdeg]
    exact (Nat.add_le_add (Nat.mul_le_mul_left _ hg) ht).trans
      (by rw [high_mul]; exact high_add _ _ _ _ _)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs, mass]
termination_by H.natDegree
decreasing_by
  have hpos' := Nat.mul_pos hr hpos
  omega
end
end K1_14_2_2R
end
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 8
namespace K1_14_2_2_4_3
noncomputable section
open K1 K1_14 K1_14_2 K1_14_2_2 K1_14_2_2_4 Polynomial
open scoped nonZeroDivisors
private theorem seedDegree_eq (f : Equation) : seedDegree f = K1_14_4.seedDegree f := by
  apply le_antisymm
  · refine Finset.sup_le fun j _ => ?_
    exact ((K1_14_4.seedDegree_le_iff _ _).mp le_rfl) j
  · apply (K1_14_4.seedDegree_le_iff _ _).mpr
    intro j
    by_cases hj : f.coeff j = 0
    · simp [hj]
    · exact Finset.le_sup (f := fun j => (f.coeff j).totalDegree) (mem_support_iff.mpr hj)
private theorem seedDegree_le_of_dvd {f H : Equation} (hH : H ≠ 0) (h : f ∣ H) :
    seedDegree f ≤ seedDegree H := by
  obtain ⟨g, rfl⟩ := h
  rw [seedDegree_eq, seedDegree_eq,
    K1_14_4.seedDegree_mul (left_ne_zero_of_mul hH) (right_ne_zero_of_mul hH)]
  exact Nat.le_add_right _ _
private theorem seed_constant_image (a : Seeds) :
    mapGenericSeed (ordinaryIncl (C a)) = MvPolynomial.C (algebraMap Seeds SeedField a) := by
  have he : mapGenericSeed.comp (rootIncl.comp rootSeeds) =
      MvPolynomial.C.comp (algebraMap Seeds SeedField) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, rootIncl, rootSeeds, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, MvPolynomial.rename_C, mapGenericSeed, MvPolynomial.eval₂Hom_C]
      rw [IsScalarTower.algebraMap_apply FX Seeds SeedField, MvPolynomial.algebraMap_eq]
    · intro i
      fin_cases i <;> simp [rootIncl, rootSeeds, mapGenericSeed, generic]
  simpa [toJet, toRoot] using RingHom.congr_fun he a
private theorem seed_constant_not_mem {I : Ideal Ambient} (hI : Active I) {a : Seeds}
    (ha : a ≠ 0) : ordinaryIncl (C a) ∉ I := by
  intro h
  have hunit : IsUnit (mapGenericSeed (ordinaryIncl (C a))) := by
    rw [seed_constant_image]
    exact (isUnit_iff_ne_zero.mpr (fun hz => ha ((IsFractionRing.injective _ _)
      (hz.trans (map_zero (algebraMap Seeds SeedField)).symm)))).map
      MvPolynomial.C
  have htop : I.map mapGenericSeed = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ h) hunit
  let : Subsingleton (OverSeeds I) := Ideal.Quotient.subsingleton_iff.mpr htop
  exact hI.seed_size.1.ne' (Module.finrank_eq_zero_of_subsingleton SeedField (OverSeeds I))
attribute [local instance] Polynomial.algebra in
theorem ordinary_contraction {I : Ideal Ambient} (hI : Active I)
    (hP : I.comap ordinaryIncl ≠ ⊥) :
    ∃ f : Equation, Irreducible f ∧ 0 < f.natDegree ∧
      I.comap ordinaryIncl = Ideal.span {f} := by
  let P : Ideal Equation := I.comap ordinaryIncl
  have : I.IsPrime := hI.prime
  have : P.IsPrime := Ideal.comap_isPrime ordinaryIncl I
  let S : Submonoid Equation := (nonZeroDivisors Seeds).map (C : Seeds →+* Equation)
  have := Polynomial.isLocalization (nonZeroDivisors Seeds) SeedField
  have hdisj : Disjoint (S : Set Equation) (P : Set Equation) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ h
    exact seed_constant_not_mem hI (mem_nonZeroDivisors_iff_ne_zero.mp ha) h
  let Q := P.map (algebraMap Equation (Polynomial SeedField))
  have : Q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint S (Polynomial SeedField) P inferInstance hdisj
  have hle := Ideal.height_le_ringKrullDim_of_isPrime (I := Q)
  have hdim : ringKrullDim (Polynomial SeedField) = 1 := by simp [ringKrullDim_eq_zero_of_field]
  rw [hdim] at hle
  have hheight : Ideal.height (R := (Polynomial SeedField)) Q = Ideal.height (R := Equation) P :=
    IsLocalization.height_map_of_disjoint (R := Equation) (S := (Polynomial SeedField)) S P hdisj
  have hle' : Ideal.height (R := Equation) P ≤ 1 :=
    hheight ▸ WithBot.coe_le_coe.mp hle
  have hge : 1 ≤ Ideal.height (R := Equation) P := by
    have hlt : (⊥ : Ideal Equation) < P := bot_lt_iff_ne_bot.mpr hP
    simpa using Ideal.height_add_one_le_of_lt_of_isPrime hlt
  obtain ⟨f, hf⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one (p := P)
    (le_antisymm hle' hge)).principal
  change P = Ideal.span {f} at hf
  have hf0 : f ≠ 0 := by
    intro h
    exact hP (by simpa [h] using hf)
  have hprime : (Ideal.span ({f} : Set Equation)).IsPrime := by
    rw [← hf]
    infer_instance
  have hmem : ordinaryIncl f ∈ I := by
    change f ∈ P
    rw [hf]
    exact Ideal.mem_span_singleton_self f
  have hdeg : 0 < f.natDegree := by
    by_contra! h
    have hfC := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero h)
    exact seed_constant_not_mem hI (fun hz => hf0 (hfC.trans (by rw [hz, map_zero])))
      (hfC ▸ hmem)
  exact ⟨f, ((Ideal.span_singleton_prime hf0).mp hprime).irreducible, hdeg, hf⟩
theorem ordinary_factorization {I : Ideal Ambient} (hI : Active I) {H : Equation} (hH : H ≠ 0)
    {r : ℕ} (hhigh : ¬ HighOn H r I) (hmem : ordinaryIncl H ∈ I) :
    ∃ (f g : Equation) (e : ℕ), H = f ^ e * g ∧ e < r ∧
      Irreducible f ∧ 0 < f.natDegree ∧ f.natDegree ≤ H.natDegree ∧
      seedDegree f ≤ seedDegree H ∧ I.comap ordinaryIncl = Ideal.span {f} ∧
      ordinaryIncl g ∉ I := by
  have hP : I.comap ordinaryIncl ≠ ⊥ := by
    intro hp
    change H ∈ I.comap ordinaryIncl at hmem
    exact hH (Ideal.mem_bot.mp (hp ▸ hmem))
  obtain ⟨f, hf, hpos, hcontract⟩ := ordinary_contraction hI hP
  have hfI : ordinaryIncl f ∈ I := by
    change f ∈ I.comap ordinaryIncl
    rw [hcontract]
    exact Ideal.mem_span_singleton_self f
  have hnot : ¬ f ^ r ∣ H := fun h => hhigh ⟨f, hf, hpos, h, hfI⟩
  have hdvd : f ∣ H := by
    change H ∈ I.comap ordinaryIncl at hmem
    rwa [hcontract, Ideal.mem_span_singleton] at hmem
  classical
  let ex : ∃ n : ℕ, ¬ f ^ n ∣ H := ⟨r, hnot⟩
  have hminpos : 0 < Nat.find ex := by
    by_contra! h
    have hn := Nat.find_spec ex
    rw [Nat.eq_zero_of_le_zero h, pow_zero] at hn
    exact hn (one_dvd _)
  obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero hminpos.ne'
  have her : e < r := by
    have hh := Nat.find_min' ex hnot
    omega
  have hediv : f ^ e ∣ H := by
    by_contra hn
    exact Nat.find_min ex (show e < Nat.find ex by omega) hn
  obtain ⟨g, hg⟩ := hediv
  refine ⟨f, g, e, hg, her, hf, hpos, natDegree_le_of_dvd hdvd hH,
    seedDegree_le_of_dvd hH hdvd, hcontract, ?_⟩
  intro hgI
  change g ∈ I.comap ordinaryIncl at hgI
  rw [hcontract, Ideal.mem_span_singleton] at hgI
  obtain ⟨v, hv⟩ := hgI
  apply Nat.find_spec ex
  use v
  rw [he, pow_succ, hg, hv, mul_assoc]
end
end K1_14_2_2_4_3
end
section
namespace K1_14_4
noncomputable section
open K1_14 Polynomial Finset
section Filtration
variable {F A : Type*} [Field F] [CommRing A] [Algebra F A]
private def filtered (V : Submodule F (Polynomial A)) (n : ℕ) : Submodule F (Polynomial A) :=
  V ⊓ (degreeLT A n).restrictScalars F
theorem mem_filtered {V : Submodule F (Polynomial A)} {P : (Polynomial A)} {n : ℕ} :
    P ∈ filtered V n ↔ P ∈ V ∧ P.degree < n :=
  and_congr_right fun _ => mem_degreeLT
def gradeMap (V : Submodule F (Polynomial A)) (j : ℕ) :
    filtered V (j + 1) →ₗ[F] A :=
  ((lcoeff A j).restrictScalars F).comp (filtered V (j + 1)).subtype
private theorem gradeMap_ker_rank (V : Submodule F (Polynomial A)) (j : ℕ) :
    Module.rank F (gradeMap V j).ker = Module.rank F (filtered V j) := by
  have heq : (gradeMap V j).ker.map (filtered V (j + 1)).subtype = filtered V j := by
    apply Submodule.ext
    intro P
    constructor
    · rintro ⟨⟨Q, hQ⟩, hker, rfl⟩
      obtain ⟨hV, hd⟩ := mem_filtered.mp hQ
      refine mem_filtered.mpr ⟨hV, (degree_lt_iff_coeff_zero _ _).2 ?_⟩
      intro i hi
      by_cases hij : i = j
      · subst i
        exact hker
      · exact (degree_lt_iff_coeff_zero _ _).1 hd i (by omega)
    · intro hP
      obtain ⟨hV, hd⟩ := mem_filtered.mp hP
      have hP' : P ∈ filtered V (j + 1) :=
        mem_filtered.mpr ⟨hV, hd.trans (by norm_cast; omega)⟩
      exact ⟨⟨P, hP'⟩, coeff_eq_zero_of_degree_lt hd, rfl⟩
  rw [← heq, rank_map_eq (filtered V (j + 1)).injective_subtype]
private theorem filtered_rank_le (V : Submodule F (Polynomial A)) (g : ℕ → ℕ)
    (h : ∀ j, Module.rank F (gradeMap V j).range ≤ (↑(g j) : Cardinal)) (n : ℕ) :
    Module.rank F (filtered V n) ≤ (↑(∑ j ∈ range n, g j) : Cardinal) := by
  induction n with
  | zero =>
    have hzero : filtered V 0 = ⊥ := by
      apply bot_unique
      intro P hp
      rw [Submodule.mem_bot]
      by_contra hn
      have h := (natDegree_lt_iff_degree_lt hn).2 (mem_filtered.mp hp).2
      omega
    rw [hzero]
    simp
  | succ n ih =>
    rw [← (gradeMap V n).rank_range_add_rank_ker, gradeMap_ker_rank, sum_range_succ,
      Nat.cast_add, add_comm]
    exact add_le_add ih (h n)
theorem finrank_le_grades (V : Submodule F (Polynomial A)) (g : ℕ → ℕ) (n : ℕ)
    (h : ∀ j, Module.rank F (gradeMap V j).range ≤ (↑(g j) : Cardinal))
    (hdeg : ∀ P ∈ V, P.degree < n) :
    Module.finrank F V ≤ ∑ j ∈ range n, g j := by
  have heq : filtered V n = V :=
    inf_eq_left.mpr fun P hp => mem_degreeLT.mpr (hdeg P hp)
  have hr := filtered_rank_le V g h n
  rw [heq] at hr
  exact Module.finrank_le_of_rank_le hr
end Filtration
end
end K1_14_4
end
section
set_option autoImplicit false
namespace K1_13_7_6_2
noncomputable section
open K1_13_7
def minPrimes (J : Ideal Lower) : Finset (PrimeSpectrum Lower) :=
  ((J.finite_minimalPrimes_of_isNoetherianRing).preimage
    (f := PrimeSpectrum.asIdeal) (by
      intro p _ q _ hpq
      exact PrimeSpectrum.ext_iff.mpr hpq)).toFinset
@[simp] theorem mem_minPrimes (J : Ideal Lower) (p : PrimeSpectrum Lower) :
    p ∈ minPrimes J ↔ p.asIdeal ∈ J.minimalPrimes :=
  Set.Finite.mem_toFinset _
def precedingPrimes (J : Ideal Lower) (q : PrimeSpectrum Lower) :
    Finset (PrimeSpectrum Lower) := by
  classical
  exact (minPrimes J).filter (fun p => p.asIdeal ≤ q.asIdeal)
theorem mem_precedingPrimes (J : Ideal Lower) (q p : PrimeSpectrum Lower) :
    p ∈ precedingPrimes J q ↔ p.asIdeal ∈ J.minimalPrimes ∧ p.asIdeal ≤ q.asIdeal := by
  classical
  rw [precedingPrimes, Finset.mem_filter, mem_minPrimes]
def RegularCut (q : PrimeSpectrum Lower) (J : Ideal Lower) (t : Lower) : Prop :=
  let A := Localization.AtPrime q.asIdeal
  IsSMulRegular (A ⧸ J.map (algebraMap Lower A)) (algebraMap Lower A t)
end
end K1_13_7_6_2
end
