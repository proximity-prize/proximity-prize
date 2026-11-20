import ProximityPrize.SubmissionLower.Fast005
import ProximityPrize.SubmissionLower.Fast006
import ProximityPrize.SubmissionLower.Fast003
import ProximityPrize.SubmissionLower.Fast007
import ProximityPrize.SubmissionLower.Fast009
import ProximityPrize.SubmissionLower.Fast011
import ProximityPrize.SubmissionLower.Fast014
import ProximityPrize.SubmissionLower.Pack_K1Defs
import ProximityPrize.SubmissionLower.Fast050
import ProximityPrize.SubmissionLower.Fast054
import ProximityPrize.SubmissionLower.Fast017
import ProximityPrize.SubmissionLower.Fast051
import ProximityPrize.SubmissionLower.Fast022
import ProximityPrize.SubmissionLower.Numeric2Aux
import ProximityPrize.SubmissionLower.Fast018
import ProximityPrize.SubmissionLower.Fast019
import ProximityPrize.SubmissionLower.Fast020
import ProximityPrize.SubmissionLower.Fast063
import ProximityPrize.SubmissionLower.Fast023
import ProximityPrize.SubmissionLower.Fast029
import ProximityPrize.SubmissionLower.Fast032
import ProximityPrize.SubmissionLower.Pack_K1_14_2_2_4Split
import ProximityPrize.SubmissionLower.Fast062
import ProximityPrize.SubmissionLower.Fast052
import ProximityPrize.SubmissionLower.Fast053
import ProximityPrize.SubmissionLower.Fast057
import ProximityPrize.SubmissionLower.Fast035
import ProximityPrize.SubmissionLower.Fast042
import ProximityPrize.SubmissionLower.Fast058
import ProximityPrize.SubmissionLower.Fast055
import ProximityPrize.SubmissionLower.Fast056
import ProximityPrize.SubmissionLower.Fast064
set_option Elab.async false

section PackSource_K1_14_2_4_1_3_3_2Proof
set_option autoImplicit true
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
/-- After multiplying by a unit from the scalar field, every element of the
fibre is a polynomial in the spare parameter over the original root ring. -/
private theorem clear_fibre_denominators (J : Ideal RootAmbient)
    (d : RootAmbient ⧸ J →+* RootYSection J)
    (hd : d.comp (Ideal.Quotient.mk J) = ambientInFibre J)
    (q : RootYSection J) :
    ∃ u : RootYSection J, IsUnit u ∧ ∃ p : (RootAmbient ⧸ J)[X],
      q * u = Polynomial.eval₂RingHom d
        (algebraMap SeedField (RootYSection J) (K1_14_2.generic 0)) p := by
  let D := RootAmbient ⧸ J
  let Q := RootYSection J
  let : CommRing D := Ideal.Quotient.commRing J
  let : CommRing D[X] := Polynomial.commRing
  let mkQ := Ideal.Quotient.mk (fibreIdeal J)
  let s : Seeds →+* D[X] := MvPolynomial.eval₂Hom
    (Polynomial.C.comp ((Ideal.Quotient.mk J).comp MvPolynomial.C))
    ![Polynomial.X, Polynomial.C (Ideal.Quotient.mk J (MvPolynomial.X 2))]
  let subst : MvPolynomial (Fin 3) Seeds →+* D[X] := MvPolynomial.eval₂Hom s
    (fun i => Polynomial.C (Ideal.Quotient.mk J (MvPolynomial.X i)))
  let ev : D[X] →+* Q := Polynomial.eval₂RingHom d
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
    (S : Subfield F) (f : A[X] →+* F)
    (hC : ∀ a, f (Polynomial.C a) ∈ S) (hX : f Polynomial.X ∈ S)
    (p : A[X]) : f p ∈ S := by
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

/-- A subfield containing the original root coordinates and the spare
indeterminate contains the whole rational function field in that indeterminate. -/
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
  refine fraction_mem (A := E[X]) S (RingHom.id _) ?_ z
  intro p
  exact polynomial_mem S (algebraMap E[X] (SpareField E)) hconstants hspare p

/-- Evaluating the ambient coordinates gives an embedding of the fibre once the
prescribed scalar map has matched the ordinate and the spare indeterminate. -/
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
  let : CommRing D[X] := Polynomial.commRing
  let j : D →+* E := Ideal.Quotient.lift J ρ (fun p hp =>
    RingHom.mem_ker.mp (hker.symm ▸ hp))
  have hj : Function.Injective j :=
    RingHom.lift_injective_of_ker_le_ideal J _ hker.le
  let d : D →+* Q := Ideal.Quotient.lift J (ambientInFibre J) (fun p hp =>
    Ideal.Quotient.eq_zero_iff_mem.mpr
      ((le_sup_left : J.map baseChange ≤ fibreIdeal J) (Ideal.mem_map_of_mem baseChange hp)))
  have hd : d.comp (Ideal.Quotient.mk J) = ambientInFibre J := rfl
  let t : D[X] →+* Q := Polynomial.eval₂RingHom d
    (algebraMap SeedField Q (K1_14_2.generic 0))
  have hft : f.comp t = (algebraMap E[X] (SpareField E)).comp (Polynomial.mapRingHom j) := by
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
    exact (IsFractionRing.injective E[X] (SpareField E)).comp (Polynomial.map_injective j hj)
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

/-- The generic ordinate section is the root function field with the spare
parameter adjoined, with the prescribed embedding of the slice scalars. -/
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
end PackSource_K1_14_2_4_1_3_3_2Proof

section PackSource_K1_14_2_4_1_5_1Boundary
set_option autoImplicit true
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

/-- A normalized boundary direction has algebraic coordinates over the old field.
The independent coefficients remain linearly independent over that algebraic closure. -/
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
end PackSource_K1_14_2_4_1_5_1Boundary

section PackSource_K1_14_2_4_1_5_1Proof
set_option autoImplicit true
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
end PackSource_K1_14_2_4_1_5_1Proof

section PackSource_K1_14_2_4_2Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_14_2_4_2

noncomputable section

open K1 K1_14 K1_14_2_4 MvPolynomial
open K1_14_6_1 (derivativeAt)
open scoped Polynomial BigOperators

variable {n : ℕ}

private abbrev incl := algebraMap L[X] FX

private theorem eval_center (S : K[X]) : (S.map seedEmbedding).eval center = atX S := by
  rw [Polynomial.eval_map]
  change S.eval₂ (incl.comp (Polynomial.C.comp (algebraMap K L))) (incl Polynomial.X) =
    incl (S.map (algebraMap K L))
  rw [← Polynomial.hom_eval₂, ← Polynomial.eval₂_map, Polynomial.eval₂_C_X]

private theorem factorial_ne_zero {i : ℕ} (hi : i < p) : (i.factorial : FX) ≠ 0 := by
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

private theorem taylor_term (S : K[X]) (x : K) (i : ℕ) (hi : i < p) :
    (Polynomial.taylor center (S.map seedEmbedding)).coeff i * (seedEmbedding x - center)^i =
      derivativeAt S i * weight x i := by
  rw [Polynomial.taylor_coeff, Polynomial.hasseDeriv_map, eval_center]
  have h := congrFun (Polynomial.factorial_smul_hasseDeriv (R := K) i) S
  have hfactor : derivativeAt S i = (i.factorial : FX) * atX (Polynomial.hasseDeriv i S) := by
    dsimp only [derivativeAt]
    rw [← h, LinearMap.smul_apply]
    simp only [nsmul_eq_mul, atX, liftPoly, Polynomial.map_mul,
      Polynomial.map_natCast, map_mul, map_natCast]
  rw [hfactor, weight]
  symm
  calc
    _ = (atX (Polynomial.hasseDeriv i S) * (seedEmbedding x - center)^i) *
        ((i.factorial : FX) * (i.factorial : FX)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ (factorial_ne_zero hi), mul_one]

private theorem eval_taylor {d : ℕ} (hdp : d < p) (S : K[X]) (hS : S.natDegree ≤ d) (x : K) :
    seedEmbedding (S.eval x) = atX S +
      ∑ i ∈ Finset.range d, derivativeAt S (i+1) * weight x (i+1) := by
  have hd : (Polynomial.taylor center (S.map seedEmbedding)).natDegree < d+1 := by
    rw [Polynomial.natDegree_taylor]
    exact (Polynomial.natDegree_map_le.trans hS).trans_lt (Nat.lt_succ_self _)
  calc
    _ = (Polynomial.taylor center (S.map seedEmbedding)).eval (seedEmbedding x - center) := by
      rw [Polynomial.taylor_eval_sub, Polynomial.eval_map_apply]
    _ = _ := by
      rw [Polynomial.eval_eq_sum_range' hd, Finset.sum_range_succ']
      simp only [Polynomial.taylor_coeff_zero, eval_center, pow_zero, mul_one]
      rw [add_comm]
      refine congrArg (fun v : FX => atX S + v) (Finset.sum_congr rfl ?_)
      intro i hi
      exact taylor_term S x _ ((Nat.succ_le_of_lt (Finset.mem_range.mp hi)).trans_lt hdp)

private theorem padding {d i : ℕ} (hi : i ∈ Finset.range d) :
    taylorPower d - (2*i+1) + (2*i+1) = taylorPower d := by
  have hid := Finset.mem_range.mp hi
  unfold taylorPower
  omega

private def valueNumerator (d : ℕ) (f : SourceRing n) (x : K) : SourceRing n :=
  separant f ^ taylorPower d * ordinate +
    ∑ i ∈ Finset.range d, weight x (i+1) •
      (separant f ^ (taylorPower d - (2*i+1)) * cleared f i)

private theorem valueNumerator_bound {d g : ℕ} {f : SourceRing n}
    (hg : 0 < g) (hf : f ∈ box n g 1) (x : K) :
    valueNumerator d f x ∈ box n (ordinateBound d g) (taylorPower d) := by
  have ha := separant_bound hf
  unfold valueNumerator
  apply (box _ _ _).add_mem
  · simpa only [ordinateBound, Nat.add_comm, Nat.add_zero, Nat.mul_one] using
      mul_mem_restrictBidegree (box_pow ha (taylorPower d)) (ordinate_mem (n := n))
  · apply sum_mem
    intro i hi
    apply (box _ _ _).smul_mem
    have hpad := padding hi
    have h := mul_mem_restrictBidegree
      (box_pow ha (taylorPower d - (2*i+1))) (cleared_bound hg hf i)
    have hy : (taylorPower d - (2*i+1))*(g-1) + (1+(2*i+1)*(g-1)) = ordinateBound d g := by
      calc
        _ = 1+(taylorPower d - (2*i+1)+(2*i+1))*(g-1) := by ring
        _ = _ := by rw [hpad, ordinateBound]
    rwa [hy, ← Nat.add_mul, hpad, Nat.mul_one] at h

private theorem eval_valueNumerator {d : ℕ} (hdp : d < p) (f : SourceRing n)
    (t : Fin n → L) (S : K[X]) (hS : S.natDegree ≤ d) (hf : markEval t S f = 0) (x : K) :
    markEval t S (valueNumerator d f x) =
      markEval t S (separant f ^ taylorPower d) * seedEmbedding (S.eval x) := by
  let a := markEval t S (separant f)
  have h : markEval t S ordinate = atX S := eval_X _
  simp only [valueNumerator, map_add, map_mul, map_pow, map_sum]
  rw [h, eval_taylor hdp S hS, mul_add, Finset.mul_sum]
  refine congrArg (_ + ·) (Finset.sum_congr rfl ?_)
  intro i hi
  rw [MvPolynomial.smul_eq_C_mul, map_mul, eval_C, map_mul, map_pow, eval_cleared _ _ _ hf]
  have hp : a ^ (taylorPower d - (2*i+1)) * a ^ (2*i+1) = a ^ taylorPower d := by
    rw [← pow_add, padding hi]
  change weight x (i+1) * (a ^ (taylorPower d - (2*i+1)) *
    (a ^ (2*i+1) * derivativeAt S (i+1))) = a ^ taylorPower d * _
  calc
    _ = (a ^ (taylorPower d - (2*i+1)) * a ^ (2*i+1)) *
        (derivativeAt S (i+1) * weight x (i+1)) := by ring
    _ = _ := by rw [hp]

theorem proof : K1_14_2_4.c2 := by
  intro n d g _hd hdp hg f hdegree
  have hf := flatten_bound hdegree
  refine ⟨⟨separant (flatten f) ^ taylorPower d, valueNumerator d (flatten f),
    ?_, valueNumerator_bound hg hf⟩, ?_⟩
  · have h := box_pow (separant_bound hf) (taylorPower d)
    rw [Nat.mul_one] at h
    exact mem_restrictBidegree_mono h (Nat.le_add_left _ _) le_rfl
  · intro t S hS hroot hsep
    constructor
    · change markEval t S (separant (flatten f) ^ taylorPower d) ≠ 0
      rw [map_pow, eval_separant]
      exact pow_ne_zero _ (by
        simpa only [map_zero] using (IsFractionRing.injective L[X] FX).ne hsep)
    · intro x
      apply eval_valueNumerator hdp _ t S hS _ x
      rw [eval_flatten, hroot, map_zero]

end
end K1_14_2_4_2
end PackSource_K1_14_2_4_2Proof

section PackSource_K1_13_6_1_4_1_2Family
set_option autoImplicit true
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

/-- The fixed section of a polynomial family with the specified coefficients. -/
def fixedCut (s : Finset τ) (p : τ → A) (c : τ → k) : A :=
  ∑ j ∈ s, C (c j) * p j

/-- The generic section of a polynomial family over the coefficient fraction field. -/
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

/-- The independent coefficient of a unit term makes the generic cut proper. -/
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

/-- Independent fixed-section classes stay independent in a proper generic family. -/
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
end PackSource_K1_13_6_1_4_1_2Family

section PackSource_K1_13_6_1_4_1_2Proof
set_option autoImplicit true
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

/-- The support caps put every term of the fixed cut in the independent system. -/
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
end PackSource_K1_13_6_1_4_1_2Proof

section PackSource_K1_2PruningWitness
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace K1_2.Pruning
open FrobeniusLocator
open Polynomial Finset CoreDefinitions Code LinearCode
noncomputable section
variable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
local instance decidablePruningWitness (P : Prop) : Decidable P := Classical.propDecidable P

/-- Mathematical MCA on an arbitrary puncture of the original index set. -/
def BadOn (x : ι → F) (u v : ι → F) (k A : ℕ) (D : Finset ι) (γ : F) : Prop :=
  ∃ S : Finset ι, S ⊆ D ∧ A ≤ S.card ∧
    ExtendsOn x (fun i => u i + γ*v i) k S ∧
    ¬ (ExtendsOn x u k S ∧ ExtendsOn x v k S)

/-- The punctured Johnson theorem required here, on subsets of this domain.
No characteristic or geometric theorem is asserted by this definition. -/
def PuncturedCap (x : ι → F) (k A s0 K : ℕ) : Prop :=
  ∀ (D : Finset ι), D.card ≤ A+s0 → ∀ (u v : ι → F) (Γ : Finset F),
    (∀ γ ∈ Γ, BadOn x u v k A D γ) → Γ.card ≤ K

theorem projected_of_extendsOn (x : ι ↪ F) (u : ι → F) (k : ℕ) [NeZero k]
    (S : Finset ι) (h : ExtendsOn x u k S) :
    projectedWord u S ∈ projectedCodeSubmod (ReedSolomon.code x k) S := by
  obtain ⟨P, hP, hval⟩ := h
  rw [mem_projectedCodeSubmod_iff]
  refine ⟨fun i => P.eval (x i), ?_, ?_⟩
  · apply ReedSolomon.mem_code_iff_eval_of_ne_zero.mpr
    refine ⟨P, ?_, fun i => rfl⟩
    by_cases hP0 : P = 0
    · simpa only [hP0, natDegree_zero] using Nat.pos_of_ne_zero (NeZero.ne k)
    · exact (natDegree_lt_iff_degree_lt hP0).mpr hP
  · funext i
    exact (hval i.val i.property).symm

/-- Keep nonjointness when converting native-style MCA to an exact-A support.
The interpolation/trimming theorem is the probe's existing checked theorem. -/
theorem isMCA_exact_witness [Fintype F] (x : ι ↪ F) (u : Fin 2 → ι → F)
    (k A : ℕ) [NeZero k] (hkA : k < A) (δ : ℝ)
    (hthreshold : ∀ T : Finset ι,
      (Fintype.card ι : ℝ) * (1 - δ) ≤ T.card → A ≤ T.card)
    (γ : F) (hmca : IsMCA (AffineLineGenerator F) (ReedSolomon.code x k) γ u δ) :
    ∃ S : Finset ι, S.card = A ∧
      ExtendsOn x (fun i => u 0 i + γ*u 1 i) k S ∧
      ¬ (ExtendsOn x (u 0) k S ∧ ExtendsOn x (u 1) k S) := by
  obtain ⟨T, hT, hcomb, j, hj⟩ := hmca
  rw [LinearCode.mem_projectedCodeSubmod_iff] at hcomb
  obtain ⟨c, hc, hproj⟩ := hcomb
  obtain ⟨P, hP, heval⟩ := ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hc
  have hPdeg : P.degree < k := Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast hP)
  have hfold : ∀ i ∈ T, P.eval (x i) = u 0 i + γ * u 1 i := by
    intro i hi
    have h := congrFun hproj ⟨i, hi⟩
    simpa [AffineLineGenerator, Fin.sum_univ_two, projectedWord, heval i,
      smul_eq_mul, mul_comm] using h.symm
  have hbad : ¬ (ExtendsOn x (u 0) k T ∧ ExtendsOn x (u 1) k T) := by
    intro h
    apply hj
    fin_cases j
    · exact projected_of_extendsOn x (u 0) k T h.1
    · exact projected_of_extendsOn x (u 1) k T h.2
  obtain ⟨S, _, hSA, hPdeg, hfoldS, hbadS⟩ := exact_A_bad_witness
    x x.injective (u 0) (u 1) γ k A hkA T (hthreshold T hT) P hPdeg hfold hbad
  exact ⟨S, hSA, ⟨P, hPdeg, hfoldS⟩, hbadS⟩

/-- A selected exact support at every slope under consideration. -/
structure WitnessFamily (x : ι → F) (u v : ι → F) (k A : ℕ) (Γ : Finset F) where
  support : F → Finset ι
  card_support : ∀ γ ∈ Γ, (support γ).card = A
  decodes : ∀ γ ∈ Γ, ExtendsOn x (fun i => u i + γ*v i) k (support γ)
  nonjoint : ∀ γ ∈ Γ, ¬ (ExtendsOn x u k (support γ) ∧ ExtendsOn x v k (support γ))

theorem witnessFamily_of_MCA [Fintype F] (x : ι ↪ F) (u : Fin 2 → ι → F)
    (k A : ℕ) [NeZero k] (hkA : k < A) (δ : ℝ)
    (hthreshold : ∀ T : Finset ι,
      (Fintype.card ι : ℝ) * (1 - δ) ≤ T.card → A ≤ T.card)
    (Γ : Finset F)
    (hΓ : ∀ γ ∈ Γ, IsMCA (AffineLineGenerator F) (ReedSolomon.code x k) γ u δ) :
    Nonempty (WitnessFamily x (u 0) (u 1) k A Γ) := by
  have hex : ∀ γ : {γ // γ ∈ Γ}, ∃ S : Finset ι, S.card = A ∧
      ExtendsOn x (fun i => u 0 i + γ.val*u 1 i) k S ∧
      ¬ (ExtendsOn x (u 0) k S ∧ ExtendsOn x (u 1) k S) :=
    fun γ => isMCA_exact_witness x u k A hkA δ hthreshold γ.val (hΓ γ.val γ.property)
  choose S hS hdec hnon using hex
  let support : F → Finset ι := fun γ => if h : γ ∈ Γ then S ⟨γ,h⟩ else ∅
  refine ⟨⟨support, ?_, ?_, ?_⟩⟩
  · intro γ hγ
    simpa only [support, dif_pos hγ] using hS ⟨γ,hγ⟩
  · intro γ hγ
    simpa only [support, dif_pos hγ] using hdec ⟨γ,hγ⟩
  · intro γ hγ
    simpa only [support, dif_pos hγ] using hnon ⟨γ,hγ⟩

namespace WitnessFamily
variable {x : ι → F} {u v : ι → F} {k A : ℕ} {Γ : Finset F}

def roots (W : WitnessFamily x u v k A Γ) (γ : F) : Finset ι :=
  Finset.univ \ W.support γ

def slopes (W : WitnessFamily x u v k A Γ) (Q : Finset ι) : Finset F :=
  Γ.filter fun γ => Q ⊆ W.roots γ

theorem mem_slopes (W : WitnessFamily x u v k A Γ) (Q : Finset ι) (γ : F) :
    γ ∈ W.slopes Q ↔ γ ∈ Γ ∧ Q ⊆ W.roots γ := Finset.mem_filter

@[simp] theorem slopes_empty (W : WitnessFamily x u v k A Γ) : W.slopes ∅ = Γ := by
  simp [slopes]

theorem roots_card (W : WitnessFamily x u v k A Γ) (γ : F) (hγ : γ ∈ Γ) :
    (W.roots γ).card = Fintype.card ι - A := by
  simp [roots, card_sdiff_of_subset (subset_univ _), W.card_support γ hγ]

theorem child_slopes (W : WitnessFamily x u v k A Γ) (Q : Finset ι) (a : ι) :
    (W.slopes Q).filter (fun γ => a ∈ W.roots γ) ⊆ W.slopes (insert a Q) := by
  intro γ hγ
  obtain ⟨hγ, ha⟩ := Finset.mem_filter.mp hγ
  obtain ⟨hΓ, hQ⟩ := (W.mem_slopes Q γ).mp hγ
  exact (W.mem_slopes (insert a Q) γ).mpr ⟨hΓ, insert_subset_iff.mpr ⟨ha, hQ⟩⟩

/-- Normal generic common roots force the same witness onto the puncture. -/
theorem badOn_puncture (W : WitnessFamily x u v k A Γ)
    (H : Finset ι) (γ : F) (hγ : γ ∈ Γ) (hH : H ⊆ W.roots γ) :
    BadOn x u v k A (Finset.univ \ H) γ := by
  refine ⟨W.support γ, ?_, (W.card_support γ hγ).ge, W.decodes γ hγ, W.nonjoint γ hγ⟩
  intro a ha
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ?_⟩
  intro haH
  exact (Finset.mem_sdiff.mp (hH haH)).2 ha

end WitnessFamily

/-- The precise remaining generic-rank facts for every set of appended rows.
The leaf fields are polynomial certificates, not assumed slope counts.
All appended rows are constant, so one original degree budget is retained. -/
structure RankFacts {x : ι → F} {u v : ι → F} {k A : ℕ} {Γ : Finset F}
    (W : WitnessFamily x u v k A Γ) (s0 δ : ℕ) where
  nullity : Finset ι → ℕ
  common : Finset ι → Finset ι
  common_card : ∀ Q, 0 < nullity Q → (common Q).card ≤ Fintype.card ι - A
  child_nullity : ∀ Q a, a ∉ common Q → nullity (insert a Q) + 1 = nullity Q
  zero_minor : ∀ Q, nullity Q = 0 → ∃ Δ : F[X], Δ ≠ 0 ∧ Δ.natDegree ≤ δ ∧
    ∀ γ ∈ W.slopes Q, Δ.eval γ = 0
  core_minor : ∀ Q, 0 < nullity Q → Fintype.card ι - A - (common Q).card ≤ s0 →
    ∃ Δ : F[X], Δ ≠ 0 ∧ Δ.natDegree ≤ δ ∧
      ∀ γ ∈ W.slopes Q, Δ.eval γ ≠ 0 → common Q ⊆ W.roots γ

theorem polynomial_exception_cap (Γ : Finset F) (Δ : F[X]) (hΔ : Δ ≠ 0) :
    (Γ.filter fun γ => Δ.eval γ = 0).card ≤ Δ.natDegree := by
  apply (Finset.card_le_card (t := Δ.roots.toFinset) ?_).trans
    ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _))
  intro γ hγ
  exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hΔ).mpr (Finset.mem_filter.mp hγ).2)

/-- Build the counted system from explicit minor/specialization facts and the
sole Johnson-core cap hypothesis. No other positive-nullity count is assumed. -/
def system_of_rankFacts {x : ι → F} {u v : ι → F} {k A s0 δ K : ℕ} {Γ : Finset F}
    (W : WitnessFamily x u v k A Γ) (R : RankFacts W s0 δ)
    (hA : A ≤ Fintype.card ι) (hcore : PuncturedCap x k A s0 K) :
    PruningSystem (Finset ι) F ι (Fintype.card ι - A) s0 δ K where
  domain := Finset.univ
  nullity := R.nullity
  slopes := W.slopes
  roots := fun _ => W.roots
  common := R.common
  child := fun Q a => insert a Q
  roots_subset := by intros; exact Finset.subset_univ _
  roots_card := fun Q γ hγ => W.roots_card γ ((W.mem_slopes Q γ).mp hγ).1
  common_subset := by intros; exact Finset.subset_univ _
  common_card := R.common_card
  zero_cap := by
    intro Q hQ
    obtain ⟨Δ, hΔ, hdeg, hzero⟩ := R.zero_minor Q hQ
    have heq : (W.slopes Q).filter (fun γ => Δ.eval γ = 0) = W.slopes Q :=
      Finset.filter_true_of_mem hzero
    rw [← heq]
    exact (polynomial_exception_cap _ Δ hΔ).trans hdeg
  core_cap := by
    intro Q hQ hsmall
    obtain ⟨Δ, hΔ, hdeg, hnormal⟩ := R.core_minor Q hQ hsmall
    have hpuncture : (Finset.univ \ R.common Q).card ≤ A+s0 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
      have := R.common_card Q hQ
      omega
    have hrest := hcore (Finset.univ \ R.common Q) hpuncture u v
      ((W.slopes Q).filter fun γ => Δ.eval γ ≠ 0) (by
        intro γ hγ
        obtain ⟨hγ, hne⟩ := Finset.mem_filter.mp hγ
        exact W.badOn_puncture (R.common Q) γ ((W.mem_slopes Q γ).mp hγ).1 (hnormal γ hγ hne))
    have hexc := (polynomial_exception_cap (W.slopes Q) Δ hΔ).trans hdeg
    have hsplit := Finset.card_filter_add_card_filter_not (s := W.slopes Q) (fun γ => Δ.eval γ = 0)
    change _ + ((W.slopes Q).filter fun γ => Δ.eval γ ≠ 0).card = _ at hsplit
    omega
  child_nullity := by
    intro Q a ha
    exact R.child_nullity Q a (Finset.mem_sdiff.mp ha).2
  child_slopes := fun Q a _ => W.child_slopes Q a


/-- Generic witness-family endpoint, before specializing any large native
finite index type. Keeping its dimensions symbolic avoids expansion of
the native Fintype enumeration during elaboration. -/
theorem witness_pruning_count {x : ι → F} {u v : ι → F} {k A s0 δ K : ℕ} {Γ : Finset F}
    (W : WitnessFamily x u v k A Γ) (R : RankFacts W s0 δ)
    (hA : A ≤ Fintype.card ι) (hcore : PuncturedCap x k A s0 K) :
    (Γ.card : ℚ) ≤ bound δ K (1 + (A : ℚ) / ((s0 : ℚ) + 1)) (R.nullity ∅) := by
  let P := system_of_rankFacts W R hA hcore
  have h := pruning_system_count P (by
    change Fintype.card ι - A ≤ (Finset.univ : Finset ι).card
    rw [Finset.card_univ]
    exact Nat.sub_le _ _) ∅
  change ((W.slopes ∅).card : ℚ) ≤ bound δ K
    (1 + ((Finset.univ : Finset ι).card - (Fintype.card ι - A) : ℕ) /
      ((s0 : ℚ) + 1)) (R.nullity ∅) at h
  simpa only [W.slopes_empty, Finset.card_univ, Nat.sub_sub_self hA] using h


theorem finite_event_count {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P]
    (B : ℕ) (hcap : ∀ Γ : Finset α, (∀ γ ∈ Γ, P γ) → Γ.card ≤ B) :
    (Finset.univ.filter P).card ≤ B := by
  apply hcap
  intro γ hγ
  exact (Finset.mem_filter.mp hγ).2
end
end K1_2.Pruning
end PackSource_K1_2PruningWitness

section PackSource_K1_2PruningMatrix
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace K1_2.Pruning.MatrixModel
open FrobeniusLocator
open Polynomial Finset Matrix
open scoped BigOperators
noncomputable section
local instance decidablePruningMatrix (P : Prop) : Decidable P := Classical.propDecidable P

variable {F K ι row : Type} [Field F] [Field K] [Fintype ι] [DecidableEq ι]
variable [Fintype row] [DecidableEq row]

/-- Fixed row type, with zero rows at nodes whose evaluation constraint has
not yet been appended. This avoids changing types along the pruning tree. -/
def augmented (M : Matrix row (Fin (t+1)) F[X]) (x : ι → F) (Q : Finset ι) :
    Matrix (row ⊕ ι) (Fin (t+1)) F[X] :=
  Sum.elim M (fun a j => if a ∈ Q then C (x a ^ j.val) else 0)

def nodeRow (φ : F[X] →+* K) (x : ι → F) (t : ℕ) (a : ι) : Fin (t+1) → K :=
  fun j => φ (C (x a ^ j.val))

def kernel (φ : F[X] →+* K) (M : Matrix row (Fin (t+1)) F[X])
    (x : ι → F) (Q : Finset ι) : Submodule K (Fin (t+1) → K) :=
  LinearMap.ker ((augmented M x Q).map φ).mulVecLin

def common (φ : F[X] →+* K) (M : Matrix row (Fin (t+1)) F[X])
    (x : ι → F) (Q : Finset ι) : Finset ι :=
  Finset.univ.filter fun a => ∀ v, v ∈ kernel φ M x Q →
    AppendConstants.functional (nodeRow φ x t a) v = 0

theorem mem_kernel (φ : F[X] →+* K) (M : Matrix row (Fin (t+1)) F[X])
    (x : ι → F) (Q : Finset ι) (v : Fin (t+1) → K) :
    v ∈ kernel φ M x Q ↔ (M.map φ).mulVec v = 0 ∧
      ∀ a ∈ Q, AppendConstants.functional (nodeRow φ x t a) v = 0 := by
  constructor
  · intro h
    refine ⟨funext (fun i => congrFun h (Sum.inl i)), ?_⟩
    intro a ha
    have h' := congrFun h (Sum.inr a)
    simpa only [augmented, Matrix.mulVec, dotProduct, Matrix.map_apply,
      Sum.elim_inr, if_pos ha, nodeRow, AppendConstants.functional,
      LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, Matrix.mulVecLin_apply] using h'
  · rintro ⟨hM, hQ⟩
    funext i
    cases i with
    | inl i => exact congrFun hM i
    | inr a =>
      by_cases ha : a ∈ Q
      · simpa only [augmented, Matrix.mulVec, dotProduct, Matrix.map_apply,
          Sum.elim_inr, if_pos ha, nodeRow, AppendConstants.functional,
          LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, Matrix.mulVecLin_apply] using hQ a ha
      · simp [augmented, Matrix.mulVec, dotProduct, ha]

theorem kernel_insert (φ : F[X] →+* K) (M : Matrix row (Fin (t+1)) F[X])
    (x : ι → F) (Q : Finset ι) (a : ι) :
    kernel φ M x (insert a Q) =
      LinearMap.ker (AppendConstants.appendOne ((augmented M x Q).map φ)
        (nodeRow φ x t a)).mulVecLin := by
  ext v
  change (v ∈ kernel φ M x (insert a Q)) ↔
    (AppendConstants.appendOne ((augmented M x Q).map φ) (nodeRow φ x t a)).mulVec v = 0
  rw [mem_kernel, AppendConstants.appendOne_kernel]
  change _ ↔ (v ∈ kernel φ M x Q) ∧ _
  rw [mem_kernel]
  simp only [Finset.forall_mem_insert]
  tauto

theorem nullity_drop (φ : F[X] →+* K) (M : Matrix row (Fin (t+1)) F[X])
    (x : ι → F) (Q : Finset ι) (a : ι) (ha : a ∉ common φ M x Q) :
    Module.finrank K (kernel φ M x (insert a Q)) + 1 =
      Module.finrank K (kernel φ M x Q) := by
  rw [kernel_insert]
  apply AppendConstants.nullity_drop_one
  by_contra h
  push Not at h
  apply ha
  simp only [common, Finset.mem_filter, Finset.mem_univ, true_and]
  exact h

def vectorPolynomial {E : Type*} [Field E] (v : Fin (t+1) → E) : E[X] :=
  ∑ j, monomial j.val (v j)

theorem vectorPolynomial_coeff {E : Type*} [Field E] (v : Fin (t+1) → E)
    (j : Fin (t+1)) : (vectorPolynomial v).coeff j.val = v j := by
  simp [vectorPolynomial, Polynomial.coeff_monomial, ← Fin.ext_iff]

theorem vectorPolynomial_ne_zero {E : Type*} [Field E] (v : Fin (t+1) → E)
    (hv : v ≠ 0) : vectorPolynomial v ≠ 0 := by
  intro hzero
  apply hv
  funext j
  have h := congrArg (fun P : E[X] => P.coeff j.val) hzero
  simpa only [vectorPolynomial_coeff, coeff_zero, Pi.zero_apply] using h

theorem vectorPolynomial_degree {E : Type*} [Field E] (v : Fin (t+1) → E) :
    (vectorPolynomial v).natDegree ≤ t := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_of_lt_succ j.isLt)

theorem common_card_le (φ : F[X] →+* K) (hφ : Function.Injective φ)
    (M : Matrix row (Fin (t+1)) F[X]) (x : ι → F) (hx : Function.Injective x)
    (Q : Finset ι) (hpos : 0 < Module.finrank K (kernel φ M x Q)) :
    (common φ M x Q).card ≤ t := by
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hv' : v.val ≠ 0 := fun h => hv (Subtype.ext h)
  let y : ι → K := fun a => φ (C (x a))
  have hy : Function.Injective y := hφ.comp (Polynomial.C_injective.comp hx)
  have hroot : ∀ a ∈ common φ M x Q, (vectorPolynomial v.val).eval (y a) = 0 := by
    intro a ha
    have hh := (Finset.mem_filter.mp ha).2 v.val v.property
    simpa only [vectorPolynomial, eval_finset_sum, eval_monomial,
      AppendConstants.functional, nodeRow, map_pow, map_C, y,
      LinearMap.coe_mk, AddHom.coe_mk, mul_comm] using hh
  have hcard : (common φ M x Q).card ≤ (vectorPolynomial v.val).natDegree := by
    rw [← Finset.card_image_of_injective _ hy]
    apply Polynomial.card_le_degree_of_subset_roots
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    exact (Polynomial.mem_roots (vectorPolynomial_ne_zero v.val hv')).mpr (hroot a ha)
  exact hcard.trans (vectorPolynomial_degree v.val)

/-- A nonzero minor cannot select one row twice. -/
theorem rows_injective_of_minor {R col : Type*} [CommRing R] [Nontrivial R]
    {r : ℕ} (M : Matrix row col R) (rows : Fin r → row) (cols : Fin r → col)
    (hne : (M.submatrix rows cols).det ≠ 0) : Function.Injective rows := by
  intro i j hij
  by_contra hneij
  apply hne
  apply Matrix.det_zero_of_row_eq hneij
  funext c
  change M (rows i) (cols c) = M (rows j) (cols c)
  rw [hij]

theorem minor_degree_ledger (M : Matrix row (Fin (t+1)) F[X]) (x : ι → F)
    (Q : Finset ι) (d : row → ℕ) (hdeg : ∀ i j, (M i j).natDegree ≤ d i)
    {r : ℕ} (rows : Fin r → row ⊕ ι) (cols : Fin r → Fin (t+1))
    (hne : ((augmented M x Q).submatrix rows cols).det ≠ 0) :
    ((augmented M x Q).submatrix rows cols).det.natDegree ≤ ∑ i, d i := by
  let e : row ⊕ ι → ℕ := Sum.elim d (fun _ => 0)
  have he : ∀ i j, (augmented M x Q i j).natDegree ≤ e i := by
    intro i j
    cases i with
    | inl i => exact hdeg i j
    | inr a => by_cases ha : a ∈ Q <;> simp [augmented, e, ha]
  have hdet := FrobeniusLocator.natDegree_det_le_row_sum
    ((augmented M x Q).submatrix rows cols) (fun q => e (rows q))
      (fun i j => he (rows i) (cols j))
  apply hdet.trans
  have hinj := rows_injective_of_minor (augmented M x Q) rows cols hne
  calc
    ∑ q, e (rows q) = ∑ i ∈ Finset.univ.image rows, e i :=
      (Finset.sum_image (fun i _ j _ hij => hinj hij)).symm
    _ ≤ ∑ i, e i := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = ∑ i, d i := by simp [e, Fintype.sum_sum_type]


theorem locator_root_iff (x : ι → F) (hx : Function.Injective x)
    (S : Finset ι) (a : ι) : (locator x S).eval (x a) = 0 ↔ a ∈ S := by
  constructor
  · intro h
    simp only [locator, eval_prod, eval_sub, eval_X, eval_C,
      Finset.prod_eq_zero_iff, sub_eq_zero] at h
    obtain ⟨b, hb, heq⟩ := h
    exact hx heq ▸ hb
  · exact locator_eval_zero x S a

theorem augmented_locator {x u v : ι → F} {k A : ℕ} {Γ : Finset F}
    (W : WitnessFamily x u v k A Γ)
    (M : Matrix row (Fin (Fintype.card ι - A + 1)) F[X])
    (hM : ∀ γ ∈ Γ, (M.map (evalRingHom γ)).mulVec
      (fun j => (locator x (W.roots γ)).coeff j.val) = 0)
    (Q : Finset ι) (γ : F) (hγ : γ ∈ W.slopes Q) :
    ((augmented M x Q).map (evalRingHom γ)).mulVec
      (fun j => (locator x (W.roots γ)).coeff j.val) = 0 := by
  obtain ⟨hΓ, hQ⟩ := (W.mem_slopes Q γ).mp hγ
  apply (mem_kernel (evalRingHom γ) M x Q _).mpr
  refine ⟨hM γ hΓ, ?_⟩
  intro a ha
  have hz := locator_eval_zero x (W.roots γ) a (hQ ha)
  have he := sum_coeff_eval (locator x (W.roots γ)) (Fintype.card ι-A)
    (by rw [locator_natDegree, W.roots_card γ hΓ]) (x a)
  simpa only [AppendConstants.functional, nodeRow, coe_evalRingHom,
    eval_C, LinearMap.coe_mk, AddHom.coe_mk, mul_comm] using he.trans hz

/-- All induction rank/specialization facts follow from a polynomial row
ledger and the original locator-annihilation fact. In particular they are
not independent assumptions about the individual slopes. -/
def rankFacts_of_matrix (φ : F[X] →+* K) (hφ : Function.Injective φ)
    {x u v : ι → F} {k A s0 δ : ℕ} {Γ : Finset F}
    (hx : Function.Injective x) (W : WitnessFamily x u v k A Γ)
    (M : Matrix row (Fin (Fintype.card ι - A + 1)) F[X])
    (d : row → ℕ) (hdeg : ∀ i j, (M i j).natDegree ≤ d i)
    (hδ : ∑ i, d i ≤ δ)
    (hM : ∀ γ ∈ Γ, (M.map (evalRingHom γ)).mulVec
      (fun j => (locator x (W.roots γ)).coeff j.val) = 0) : RankFacts W s0 δ where
  nullity Q := Module.finrank K (kernel φ M x Q)
  common := common φ M x
  common_card Q hQ := common_card_le φ hφ M x hx Q hQ
  child_nullity Q a ha := nullity_drop φ M x Q a ha
  zero_minor := by
    intro Q hQ
    let N := augmented M x Q
    obtain ⟨rows, hrows⟩ := GenericRank.exists_rows_det_ne_zero (N.map φ) (by
      intro v hv
      have hv' : v ∈ kernel φ M x Q := hv
      rw [Submodule.finrank_eq_zero.mp hQ] at hv'
      exact hv')
    let Δ := (N.submatrix rows id).det
    have hmap : φ Δ = ((N.map φ).submatrix rows id).det := by
      have hh := φ.map_det (N.submatrix rows id)
      rw [RingHom.mapMatrix_apply] at hh
      have heq : (N.submatrix rows id).map φ = (N.map φ).submatrix rows id := by
        ext i j
        rfl
      rw [heq] at hh
      exact hh
    have hΔ : Δ ≠ 0 := by
      intro hzero
      apply hrows
      rw [← hmap, hzero, map_zero]
    refine ⟨Δ, hΔ, (minor_degree_ledger M x Q d hdeg rows id hΔ).trans hδ, ?_⟩
    intro γ hγ
    have hv := augmented_locator W M hM Q γ hγ
    have hsub : (((N.map (evalRingHom γ)).submatrix rows id).mulVec
        (fun j => (locator x (W.roots γ)).coeff j.val)) = 0 := by
      funext i
      exact congrFun hv (rows i)
    have hc : (locator x (W.roots γ)).coeff (Fintype.card ι - A) = 1 := by
      have heq := (locator_natDegree x (W.roots γ)).trans
        (W.roots_card γ ((W.mem_slopes Q γ).mp hγ).1)
      rw [← heq]
      exact (locator_monic x (W.roots γ)).coeff_natDegree
    have hz := Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hsub
      (i := ⟨Fintype.card ι - A, Nat.lt_succ_self _⟩)
      (by simpa only [hc] using (one_mem (nonZeroDivisors F)))
    have heval := (evalRingHom γ).map_det (N.submatrix rows id)
    rw [RingHom.mapMatrix_apply] at heval
    exact heval.trans hz
  core_minor := by
    intro Q _ _
    let N := augmented M x Q
    obtain ⟨B⟩ := NormalFiber.exists_rowBasis φ N ((N.map φ).rank) rfl
    refine ⟨(NormalFiber.pivot B).det, B.minor_ne,
      (minor_degree_ledger M x Q d hdeg B.rows B.cols B.minor_ne).trans hδ, ?_⟩
    intro γ hγ hnormal a ha
    have hv := augmented_locator W M hM Q γ hγ
    have hfun : ∀ v, (N.map φ).mulVec v = 0 →
        ∑ c, φ (C (x a ^ c.val)) * v c = 0 := by
      intro v hv
      exact (Finset.mem_filter.mp ha).2 v hv
    have hz := GenericCofactor.common_functional_specializes B hφ
      (fun c => C (x a ^ c.val)) hfun γ hnormal _ hv
    apply (locator_root_iff x hx (W.roots γ) a).mp
    rw [← sum_coeff_eval (locator x (W.roots γ)) (Fintype.card ι-A)
      (by rw [locator_natDegree, W.roots_card γ ((W.mem_slopes Q γ).mp hγ).1])]
    simpa only [eval_C, mul_comm] using hz


theorem kernel_empty (φ : F[X] →+* K) (M : Matrix row (Fin (t+1)) F[X])
    (x : ι → F) : kernel φ M x ∅ = LinearMap.ker (M.map φ).mulVecLin := by
  ext v
  rw [mem_kernel]
  simp

/-- A generic row-basis certificate with its row-degree ledger is enough;
all descendants, rank drops and terminal normal-fiber implications are
proved above using the shared z01 layer. -/
theorem witness_count_of_rowBasis (φ : F[X] →+* K) (hφ : Function.Injective φ)
    {x u v : ι → F} {k A s0 δ coreK : ℕ} {Γ : Finset F}
    (hx : Function.Injective x) (hA : A ≤ Fintype.card ι)
    (W : WitnessFamily x u v k A Γ)
    (M : Matrix row (Fin (Fintype.card ι - A + 1)) F[X])
    {ρ : ℕ} (B : NormalFiber.RowBasis φ M ρ)
    (d : row → ℕ) (hdeg : ∀ i j, (M i j).natDegree ≤ d i)
    (hδ : ∑ i, d (B.rows i) ≤ δ)
    (hM : ∀ γ ∈ Γ, (M.map (evalRingHom γ)).mulVec
      (fun j => (locator x (W.roots γ)).coeff j.val) = 0)
    (hcore : PuncturedCap x k A s0 coreK) :
    (Γ.card : ℚ) ≤ bound δ coreK (1 + (A : ℚ) / ((s0 : ℚ)+1))
      (Fintype.card ι - A + 1 - (M.map φ).rank) := by
  let N := M.submatrix B.rows id
  have hN : ∀ γ ∈ Γ, (N.map (evalRingHom γ)).mulVec
      (fun j => (locator x (W.roots γ)).coeff j.val) = 0 := by
    intro γ hγ
    funext i
    exact congrFun (hM γ hγ) (B.rows i)
  let R := rankFacts_of_matrix φ hφ hx W N (fun i => d (B.rows i))
    (fun i j => hdeg (B.rows i) j) hδ hN (s0 := s0)
  have hcount := witness_pruning_count W R hA hcore
  have hk : LinearMap.ker (N.map φ).mulVecLin = LinearMap.ker (M.map φ).mulVecLin := by
    ext v
    exact (GenericCofactor.generic_kernel_eq_selected B v).symm
  have hdim : R.nullity ∅ = Fintype.card ι - A + 1 - (M.map φ).rank := by
    change Module.finrank K (kernel φ N x ∅) = _
    rw [kernel_empty, hk]
    have h := LinearMap.finrank_range_add_finrank_ker (M.map φ).mulVecLin
    change (M.map φ).rank + _ = _ at h
    rw [Module.finrank_fin_fun] at h
    omega
  rwa [hdim] at hcount

end
end K1_2.Pruning.MatrixModel
end PackSource_K1_2PruningMatrix

section PackSource_K1_2PruningFrobenius
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace K1_2.Pruning
open FrobeniusLocator
open Polynomial Finset Matrix
open scoped BigOperators
noncomputable section
local instance decidablePruningFrobenius (P : Prop) : Decidable P := Classical.propDecidable P
variable {F K ι : Type} [Field F] [Field K] [Fintype ι] [DecidableEq ι]

/-- The pruning theorem for the actual Frobenius-stacked locator matrix.
All generic-rank, row-budget, append and specialization facts are proved;
the punctured MCA cap is the only external counting hypothesis. -/
theorem stacked_pruning_count (p : ℕ) [ExpChar F p]
    (φ : F[X] →+* K) (hφ : Function.Injective φ)
    (x : ι → F) (hx : Function.Injective x) (hfixed : ∀ i, x i ^ p = x i)
    (u v : ι → F) (k A L s0 coreK : ℕ) (hA : A ≤ Fintype.card ι)
    (hsize : k + L + (Fintype.card ι - A) ≤ Fintype.card ι)
    (hfirst : ((hankel x u v L (Fintype.card ι - A)).map φ).rank = L)
    (hcore : PuncturedCap x k A s0 coreK)
    (Γ : Finset F) (W : WitnessFamily x u v k A Γ) :
    (Γ.card : ℚ) ≤
      bound (L + p * (((stacked p x u v L (Fintype.card ι - A)).map φ).rank - L))
        coreK (1 + (A : ℚ) / ((s0 : ℚ) + 1))
        (Fintype.card ι - A + 1 - ((stacked p x u v L (Fintype.card ι - A)).map φ).rank) := by
  let M := stacked p x u v L (Fintype.card ι - A)
  have hordinary : ((M.map φ).submatrix (NormalFiber.ordinaryRows L) id) =
      (hankel x u v L (Fintype.card ι - A)).map φ := by
    ext i j
    simp [M, Matrix.submatrix_apply, Matrix.map_apply, NormalFiber.ordinaryRows, stacked]
  have hfirstRows := NormalFiber.first_rows_independent_of_rank φ L M
    (by rw [hordinary]; exact hfirst)
  have hdeg : ∀ i j, (M i j).natDegree ≤ if i.1 = 0 then 1 else p :=
    stacked_entry_natDegree p x u v L (Fintype.card ι - A)
  obtain ⟨B, hledger, _⟩ := NormalFiber.exists_stacked_basis φ L ((M.map φ).rank) p M rfl hfirstRows hdeg
  apply MatrixModel.witness_count_of_rowBasis φ hφ hx hA W M B
    (fun i => if i.1 = 0 then 1 else p) hdeg hledger.le ?_ hcore
  intro γ hγ
  obtain ⟨P, hP, hagree⟩ := W.decodes γ hγ
  apply locator_annihilates_stacked p x hx hfixed u v γ k L (Fintype.card ι - A)
    hsize P hP (W.roots γ) (W.roots_card γ hγ).le
  intro a ha
  have haS : a ∈ W.support γ := by
    simpa only [WitnessFamily.roots, Finset.mem_sdiff, Finset.mem_univ, true_and,
      not_not] using ha
  exact (hagree a haS).symm


/-- Same theorem with an explicit domain cardinality, for native adapters
whose Fintype enumeration must not be reduced by elaboration. -/
theorem stacked_pruning_count_of_card (p : ℕ) [ExpChar F p]
    (φ : F[X] →+* K) (hφ : Function.Injective φ)
    (x : ι → F) (hx : Function.Injective x) (hfixed : ∀ i, x i ^ p = x i)
    (u v : ι → F) (n k A L s0 coreK : ℕ) (hn : Fintype.card ι = n) (hA : A ≤ n)
    (hsize : k + L + (n - A) ≤ n)
    (hfirst : ((hankel x u v L (n - A)).map φ).rank = L)
    (hcore : PuncturedCap x k A s0 coreK)
    (Γ : Finset F) (W : WitnessFamily x u v k A Γ) :
    (Γ.card : ℚ) ≤ bound (L + p * (((stacked p x u v L (n - A)).map φ).rank - L))
      coreK (1 + (A : ℚ) / ((s0 : ℚ)+1))
      (n - A + 1 - ((stacked p x u v L (n - A)).map φ).rank) := by
  subst n
  exact stacked_pruning_count p φ hφ x hx hfixed u v k A L s0 coreK hA hsize hfirst hcore Γ W

end
end K1_2.Pruning
end PackSource_K1_2PruningFrobenius

section PackSource_K1_13_6_3_2Aux1
set_option autoImplicit true
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
    simp [coeff_monomial, show j.val ≠ i.val from fun he => hij (Fin.ext he)]
  · simp

theorem map_fromTaylor {F E : Type} [CommRing F] [CommRing E] (k : F →+* E)
    {M : ℕ} (x : F) (a : Fin M → F) :
    (fromTaylor x a).map k = fromTaylor (k x) (fun i => k (a i)) := by
  change Polynomial.mapRingHom k (fromTaylor x a) = _
  simp only [fromTaylor, map_sum, map_mul, map_pow, map_sub, Polynomial.coe_mapRingHom, map_C, map_X]

theorem map_trajectory {F E : Type} [Field F] [Field E] (k : F →+* E) (a : Geom →+* F)
    (H : Row 4) (U : F[X]) :
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

/-- The explicit numerators compute the ordinary tangent iterates over the
contracted chart as well as over genuine polynomial marks. -/
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
    (q := (m 3 : Geom[X]) + 1)
  have hc : ((m 3 : Geom[X]) + 1).natDegree = 0 := by
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
end PackSource_K1_13_6_3_2Aux1

section PackSource_K1_13_6_3_2Split
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace K1_13_6_3_2

noncomputable section

open K1_13 K1_13_6 K1_13_6_3 Polynomial

/-- The regular tangent derivation on the fraction field of the contraction. -/
def c1 : Prop :=
  ∀ (g : Row 4) (P : JetIdeal) (_hp : P.IsPrime),
    toGeneric g ∈ P → toGeneric (separant g) ∉ P → Invariant g P →
    ∃ D : Derivation Geom (ContractedField P) (ContractedField P),
      D (abscissa (rowAt P)) = 1 ∧
      (∀ i : Fin 3, D (jetCoordinate (rowAt P) i.castSucc) =
        ((i.val + 1 : ℕ) : ContractedField P) * jetCoordinate (rowAt P) i.succ) ∧
      ∀ H : Row 4, rowAt P (separant g) * D (rowAt P H) = rowAt P (flowNumerator g H)

/-- The truncated differential exponential continues a single
physical row under its strict true-weight guard. -/
def c2 : Prop :=
  ∀ (F : Type) [Field F] [Algebra Geom F] (D : Derivation Geom F F) (x y : F),
    D x = 1 → ((D : F → F)^[taylorLength]) y = 0 →
    ∀ (H : Row 4) (B : ℕ), TrueWeightLE H B → B + 3 < K1.p →
      MvPolynomial.eval₂ (Polynomial.aeval x).toRingHom
        (fun i => dividedIterate D y i.val) H = 0 →
      trajectory (algebraMap Geom F) H (differentialTaylor D x y) = 0

/-- The explicit chart Taylor coefficients specialize on every regular mark. -/
def c3 : Prop :=
  ∀ (g : Row 4) (P : JetIdeal) (_hp : P.IsPrime),
    toGeneric g ∈ P → toGeneric (separant g) ∉ P →
    ∀ S : Geom[X], S.natDegree < taylorLength → P ≤ markIdeal S →
      atJet (separant g) S ≠ 0 →
      coeffPoint S ∈ MvPolynomial.zeroLocus Geom
        (coefficientKernel (componentConstants P) (chartTaylor (componentRow P) g))

private theorem rowAt_eval (P : JetIdeal) (H : Row 4) :
    MvPolynomial.eval₂ (Polynomial.aeval (abscissa (rowAt P))).toRingHom
      (jetCoordinate (rowAt P)) H = rowAt P H := by
  change MvPolynomial.eval₂Hom _ _ H = rowAt P H
  have hc : (Polynomial.aeval (abscissa (rowAt P))).toRingHom =
      (rowAt P).comp MvPolynomial.C := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C, RingHom.comp_apply]
      rfl
    · simp [abscissa]
  rw [hc]
  have h : MvPolynomial.eval₂Hom ((rowAt P).comp MvPolynomial.C)
      (jetCoordinate (rowAt P)) = rowAt P := by
    apply MvPolynomial.ringHom_ext <;> simp [jetCoordinate]
  rw [h]

private theorem initial_dividedIterate {F : Type} [Field F] [Algebra Geom F]
    (e : Row 4 →+* F) (D : Derivation Geom F F)
    (shift : ∀ i : Fin 3, D (jetCoordinate e i.castSucc) =
      ((i.val + 1 : ℕ) : F) * jetCoordinate e i.succ) (i : Fin 4) :
    dividedIterate D (jetCoordinate e 0) i.val = jetCoordinate e i := by
  have raw (j : Fin 4) : ((D : F → F)^[j.val]) (jetCoordinate e 0) =
      (j.val.factorial : F) * jetCoordinate e j := by
    induction j using Fin.induction with
    | zero => simp
    | succ j ih =>
      rw [Fin.val_succ, Function.iterate_succ_apply', ← Fin.val_castSucc j, ih]
      simp only [D.leibniz, D.map_natCast, smul_eq_mul, mul_zero, add_zero, shift,
        Fin.val_castSucc, Nat.factorial_succ, Nat.cast_mul]
      ring
  have hfact := factorial_ne_zero (algebraMap Geom F)
    (i.isLt.trans (by decide : 4 < K1.p))
  rw [dividedIterate, raw i, mul_div_cancel_left₀ _ hfact]

private theorem chartTaylor_toComponent (P : JetIdeal) [P.IsPrime] (g : Row 4) :
    (chartTaylor (rowAt P) g).map (toComponent P) = chartTaylor (componentRow P) g := by
  unfold chartTaylor abscissa
  rw [map_fromTaylor]
  simp only [map_div₀, map_pow, map_natCast, toComponent_rowAt]

theorem of_children (h1 : c1) (h2 : c2) (h3 : c3) : K1_13_6_3.c2 := by
  intro f Q r P hp hf hQ hcut
  dsimp only
  intro hg hsep hmember hinv
  let g := (separant^[r]) f
  let e := rowAt P
  let x := abscissa e
  let y := jetCoordinate e 0
  let k := toComponent P
  obtain ⟨D, hx, hshift, haction⟩ := h1 g P hp hg hsep hinv
  have hs : e (separant g) ≠ 0 := fun hz => hsep ((rowAt_eq_zero P _).mp hz)
  have hM : ((D : ContractedField P → ContractedField P)^[taylorLength]) y = 0 := by
    have hz := (rowAt_eq_zero P (membershipTest g)).mpr hmember
    change e (jetNumerator g taylorLength) = 0 at hz
    rw [jetNumerator_eq_iterate e g D haction] at hz
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hs)
  have hcanon : chartTaylor e g = differentialTaylor D x y := by
    unfold chartTaylor differentialTaylor
    apply congrArg (fromTaylor (M := taylorLength) x)
    funext i
    unfold dividedIterate
    rw [jetNumerator_eq_iterate e g D haction, mul_div_cancel_left₀ _ (pow_ne_zero _ hs)]
  have hmap : (differentialTaylor D x y).map k = chartTaylor (componentRow P) g := by
    rw [← hcanon]
    exact chartTaylor_toComponent P g
  have hinitial (i : Fin 4) : dividedIterate D y i.val = jetCoordinate e i :=
    initial_dividedIterate e D hshift i
  have hconstants : k.comp (algebraMap Geom (ContractedField P)) = componentConstants P := by
    ext a
    exact toComponent_constantsAt P a
  have hcontinue (H : Row 4) (B : ℕ) (hW : TrueWeightLE H B) (hguard : B + 3 < K1.p)
      (hH : toGeneric H ∈ P) :
      trajectory (componentConstants P) H (chartTaylor (componentRow P) g) = 0 := by
    have hzero : MvPolynomial.eval₂ (Polynomial.aeval x).toRingHom
        (fun i => dividedIterate D y i.val) H = 0 := by
      simp only [hinitial]
      exact (rowAt_eval P H).trans ((rowAt_eq_zero P H).mpr hH)
    have hh := congrArg (fun U : (ContractedField P)[X] => U.map k)
      (h2 (ContractedField P) D x y hx hM H B hW hguard hzero)
    rw [map_trajectory, hconstants, hmap, Polynomial.map_zero] at hh
    exact hh
  have hfP : toGeneric f ∈ P :=
    hcut (Ideal.subset_span (by simp : toGeneric f ∈ ({toGeneric f, toGeneric Q} : Set GeoJets)))
  have hQP : toGeneric Q ∈ P :=
    hcut (Ideal.subset_span (by simp : toGeneric Q ∈ ({toGeneric f, toGeneric Q} : Set GeoJets)))
  refine ⟨chartTaylor (componentRow P) g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fromTaylor_degree _ _ (by decide : 0 < taylorLength)
  · intro i
    rw [← hmap]
    change (hasseDeriv i.val ((differentialTaylor D x y).map k)).eval
      (onComponent P (MvPolynomial.C genericArgument)) = _
    rw [Polynomial.hasseDeriv_map, ← toComponent_abscissa P]
    change ((hasseDeriv i.val (differentialTaylor D x y)).map k).eval (k x) = _
    rw [Polynomial.eval_map_apply]
    have hT := fromTaylor_hasse x (fun j => dividedIterate D y j.val)
      (i.castLE (by decide : 4 ≤ taylorLength))
    change (hasseDeriv i.val (differentialTaylor D x y)).eval x = dividedIterate D y i.val at hT
    rw [hT, hinitial]
    exact toComponent_jetCoordinate P i
  · exact hcontinue f _ hf (by decide) hfP
  · exact hcontinue Q _ hQ (by decide) hQP
  · exact hcontinue g _ (iterate_separant_weight hf r) (by decide) hg
  · exact h3 g P hp hg hsep

end
end K1_13_6_3_2
end PackSource_K1_13_6_3_2Split

section PackSource_K1_13_6_3_2_1Proof
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace K1_13_6_3_2_1

noncomputable section

open K1_13 K1_13_6 K1_13_6_3 K1_13_6_3_2 K1_13_6_2_2_2
open nonZeroDivisors

/-- Use the chart flow for the second coordinate of a row map into dual numbers. -/
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

/-- A dual-number map over the fraction inclusion extends across every denominator. -/
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

/-- The second coordinate is a derivation when the first is the identity and
the second coordinate vanishes on the constants. -/
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

/-- Descend the regular chart flow across a stable kernel and then extend it
to the fraction field of the resulting row image. -/
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
end PackSource_K1_13_6_3_2_1Proof

section PackSource_K1_13_6_3_2_2Proof
set_option autoImplicit true
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

/-- In the translated variable, the coefficient derivation acts as differentiation. -/
private def horizontal : Subsemiring F[X] where
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
private theorem hasse_comm (i j : ℕ) (P : F[X]) :
    hasseDeriv i (hasseDeriv j P) = hasseDeriv j (hasseDeriv i P) := by
  have hi := LinearMap.congr_fun (hasseDeriv_comp (R := F) i j) P
  have hj := LinearMap.congr_fun (hasseDeriv_comp (R := F) j i) P
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hi hj
  rw [hi, hj, Nat.add_comm j i, Nat.choose_symm_add (a := i) (b := j)]

private theorem hasse_horizontal {P : F[X]} (hP : P ∈ horizontal D) (i : ℕ) :
    hasseDeriv i P ∈ horizontal D := by
  intro n
  rw [← hasseDeriv_one', hasse_comm 1 i, hasseDeriv_one', hasseDeriv_coeff,
    hasseDeriv_coeff, D.leibniz, D.map_natCast, smul_eq_mul, smul_eq_mul,
    mul_zero, add_zero, hP (n + i)]

private theorem shifted_coefficients (x : F) (hx : D x = 1) (b : Geom[X]) :
    taylor x (b.map (algebraMap Geom F)) ∈ horizontal D := by
  have hX : ((Polynomial.X : F[X]) + C x) ∈ horizontal D := by
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

private def centered (L : ℕ) (x y : F) : F[X] :=
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

private theorem trajectory_horizontal (x : F) (hx : D x = 1) (H : Row 4) (U : F[X])
    (hU : taylor x U ∈ horizontal D) :
    taylor x (trajectory (algebraMap Geom F) H U) ∈ horizontal D := by
  let t := (taylorAlgHom x).toRingHom
  let g := t.comp (Polynomial.mapRingHom (algebraMap Geom F))
  let a : Fin 4 → F[X] := fun i => hasseDeriv i.val (taylor x U)
  have ha (i : Fin 4) : t (hasseDeriv i.val U) = a i :=
    (hasseDeriv_taylor U x i.val).symm
  have ht : t (trajectory (algebraMap Geom F) H U) = MvPolynomial.eval₂ g a H := by
    rw [trajectory, MvPolynomial.hom_eval₂]
    simp only [ha]
    rfl
  change t (trajectory (algebraMap Geom F) H U) ∈ horizontal D
  rw [ht]
  let g' : Geom[X] →+* horizontal D := g.codRestrict _ (shifted_coefficients D x hx)
  let a' : Fin 4 → horizontal D := fun i => ⟨a i, hasse_horizontal D hU i.val⟩
  let P : horizontal D := MvPolynomial.eval₂ g' a' H
  have hm : (P : F[X]) = MvPolynomial.eval₂ g a H :=
    MvPolynomial.hom_eval₂ H g' (horizontal D).subtype a'
  rw [← hm]
  exact P.2

private theorem trajectory_degree (H : Row 4) {B : ℕ} (hH : TrueWeightLE H B)
    {U : F[X]} (hU : U.natDegree ≤ 133671) :
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

private theorem trajectory_at_center (x : F) (H : Row 4) (U : F[X]) :
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
    · change ((Polynomial.X : Geom[X]).map (algebraMap Geom F)).eval x =
        Polynomial.aeval x Polynomial.X
      rw [Polynomial.map_X, eval_X, aeval_X]
  rw [MvPolynomial.hom_eval₂, hc]; rfl

private theorem horizontal_zero {P : F[X]} (hP : P ∈ horizontal D)
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
end PackSource_K1_13_6_3_2_2Proof

section PackSource_K1_13_6_3_2_3Transport
set_option autoImplicit true
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

/-- A common denominator lets any specialization that survives at s inherit
equations from the first field. -/
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
    (Localization.Away s)[X] :=
  let η := algebraMap R (Localization.Away s)
  fromTaylor (η x) (fun i : Fin M => η (a i) *
    (IsLocalization.Away.invSelf s) ^ (2 * i.val) * η (c (i.val.factorial : k)⁻¹))

def fieldTaylor {M : ℕ} (e : R →+* F) (s x : R) (a : Fin M → R) : F[X] :=
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

private def coeffEquation {M : ℕ} {B : Type} [CommRing B] (c : k →+* B) (U : B[X])
    (q : MvPolynomial (Fin M) k) : B :=
  q.eval₂ c (fun i => U.coeff i.val)

private theorem map_equation {M : ℕ} {B : Type} [CommRing B] (h : B →+* F)
    (c : k →+* B) (U : B[X]) (q : MvPolynomial (Fin M) k) :
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
end PackSource_K1_13_6_3_2_3Transport

section PackSource_K1_13_6_3_2_3Proof
set_option autoImplicit true
set_option autoImplicit false
set_option maxRecDepth 1600
set_option maxHeartbeats 500000

namespace K1_13_6_3_2_3

noncomputable section

open Polynomial K1_13 K1_13_6 K1_13_6_3 K1_13_6_3_2

private def physicalConstants : Geom →+* Row 4 := MvPolynomial.C.comp Polynomial.C

private def markRow (S : Geom[X]) : Row 4 →+* GeoField :=
  genericCoeffs.comp (MvPolynomial.eval (jet S))

private theorem markRow_apply (S : Geom[X]) (H : Row 4) :
    markRow S H = genericCoeffs (atJet H S) := rfl

private theorem markRow_constants (S : Geom[X]) :
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
  (algebraMap GenericField GeoField).injective.comp (IsFractionRing.injective Geom[X] GenericField)

private theorem divided_actual (g : Row 4) (S : Geom[X]) (hg : atJet g S = 0)
    (hs : markRow S (separant g) ≠ 0) (i : Fin taylorLength) :
    markRow S (jetNumerator g i.val) / markRow S (separant g) ^ (2*i.val) /
      (i.val.factorial : GeoField) = genericCoeffs (hasseDeriv i.val S) := by
  have ho : derivative^[i.val] S = (i.val.factorial : Geom[X]) * hasseDeriv i.val S := by
    have h := congrFun (factorial_smul_hasseDeriv (R := Geom) (k := i.val)) S
    change i.val.factorial • hasseDeriv i.val S = derivative^[i.val] S at h
    simpa only [nsmul_eq_mul] using h.symm
  have hfact := factorial_ne_zero geomConstants (i.isLt.trans (by decide : taylorLength < K1.p))
  rw [markRow_apply S (jetNumerator g i.val), eval_jetNumerator _ _ hg, map_mul, map_pow,
    ← markRow_apply, mul_div_cancel_left₀ _ (pow_ne_zero _ hs), ho, map_mul, map_natCast,
    mul_div_cancel_left₀ _ hfact]

private theorem eval_generic_center (U : Geom[X]) :
    (U.map geomConstants).eval genericArgument = genericCoeffs U := by
  change ((evalRingHom genericArgument).comp (mapRingHom geomConstants)) U = _
  apply RingHom.congr_fun
  apply Polynomial.ringHom_ext <;> simp [geomConstants, genericArgument]

private theorem recover {B : Type} [CommRing B] {M : ℕ} (x : B) (a : Fin M → B)
    (U : B[X]) (hU : U.natDegree < M)
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

private theorem mark_polynomial (g : Row 4) (S : Geom[X]) (hg : atJet g S = 0)
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

private def vanishes {F : Type} [Field F] (k : Geom →+* F) (U : F[X]) (q : CoeffRing) : Prop :=
  q.eval₂ k (fun i => U.coeff i.val) = 0

private theorem mem_kernel_iff {F : Type} [Field F] (k : Geom →+* F) (U : F[X])
    (q : CoeffRing) : q ∈ coefficientKernel k U ↔ vanishes k U q := Iff.rfl

private theorem mark_equation {F : Type} [Field F] (k : Geom →+* F) (S : Geom[X]) (q : CoeffRing)
    (h : vanishes k (S.map k) q) : MvPolynomial.eval (coeffPoint S) q = 0 := by
  unfold vanishes at h
  simp only [coeff_map] at h
  apply (map_eq_zero_iff _ k.injective).mp
  rw [MvPolynomial.eval₂_comp]
  exact h

private theorem transport_chart (P : JetIdeal) [P.IsPrime] (g : Row 4) (S : Geom[X])
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

theorem proof : K1_13_6_3_2.c3 := by
  intro g P hp hg hsep S hd hP hr
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
end PackSource_K1_13_6_3_2_3Proof

section PackSource_K1_14_3_2RCoprime
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

namespace K1_14_3_2R

noncomputable section

open K1_14 K1_14_3 K1_14_3_2

/-- When surviving original primes stay prime and contract to themselves,
a common irreducible in the image gives a common irreducible in the source. -/
theorem coprime_of_transport {B : Type*} [CommRing B] [IsDomain B] [UniqueFactorizationMonoid B]
    (φ : Jet →+* B) (transport : ∀ q : Surface, q.asIdeal.map φ = ⊤ ∨
      (q.asIdeal.map φ).IsPrime ∧ (q.asIdeal.map φ).comap φ = q.asIdeal)
    {P Q : Jet} (proper : ProperPair P Q) :
    φ P ≠ 0 ∧ φ Q ≠ 0 ∧ ∀ D, Irreducible D → D ∣ φ P → ¬ D ∣ φ Q := by
  have at_zero := transport ⟨⊥, Ideal.isPrime_bot⟩
  change Ideal.map φ ⊥ = ⊤ ∨ (Ideal.map φ ⊥).IsPrime ∧ (Ideal.map φ ⊥).comap φ = ⊥ at at_zero
  rw [Ideal.map_bot] at at_zero
  have inj : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).mpr <|
    (RingHom.ker_eq_comap_bot φ).trans (at_zero.resolve_left bot_ne_top).2
  refine ⟨(map_ne_zero_iff φ inj).mpr proper.left_ne, (map_ne_zero_iff φ inj).mpr proper.right_ne, ?_⟩
  intro D hirr hP hQ
  let J := Ideal.span ({D} : Set B)
  have hJ : J.IsPrime := (Ideal.span_singleton_prime hirr.ne_zero).mpr hirr.prime
  let I := J.comap φ
  have hI : I.IsPrime := Ideal.comap_isPrime φ J
  have hPI : P ∈ I := Ideal.mem_span_singleton.mpr hP
  have hQI : Q ∈ I := Ideal.mem_span_singleton.mpr hQ
  have hI₀ : I ≠ ⊥ := fun e => proper.left_ne (by simpa [e] using hPI)
  obtain ⟨r, hrI, hr⟩ := hI.exists_mem_prime_of_ne_bot hI₀
  let T := Ideal.span ({r} : Set Jet)
  have hT : T.IsPrime := (Ideal.span_singleton_prime hr.ne_zero).mpr hr
  have hle : T.map φ ≤ J := Ideal.map_le_iff_le_comap.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hrI)
  have hsurv := (transport ⟨T, hT⟩).resolve_left (fun e => hJ.ne_top (top_unique (e ▸ hle)))
  have hmap : T.map φ = Ideal.span {φ r} := by simp [T, Ideal.map_span]
  have hφr := (map_ne_zero_iff φ inj).mpr hr.ne_zero
  have hprime : Prime (φ r) := (Ideal.span_singleton_prime hφr).mp (hmap ▸ hsurv.1)
  have hassoc := hirr.associated_of_dvd hprime.irreducible (Ideal.mem_span_singleton.mp hrI : D ∣ φ r)
  have he : J = T.map φ := (Ideal.span_singleton_eq_span_singleton.mpr hassoc).trans hmap.symm
  have hIT : I = T := (congrArg (Ideal.comap φ) he).trans hsurv.2
  exact proper.no_common r hr.irreducible (Ideal.mem_span_singleton.mp (hIT ▸ hPI : P ∈ T))
    (Ideal.mem_span_singleton.mp (hIT ▸ hQI : Q ∈ T))

end
end K1_14_3_2R
end PackSource_K1_14_3_2RCoprime

section PackSource_K1_14_3R_3_3Chart
set_option autoImplicit true
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
abbrev Pre (σ : Type) := MvPolynomial σ Parameters
abbrev Over (σ : Type) := MvPolynomial σ SectionField
private abbrev Free := {k : Fin 4 // k ≠ 2}

def parameter (k : Fin 4) : SectionField :=
  algebraMap Parameters SectionField (MvPolynomial.X k)

def fieldLine {σ : Type} (i j : σ) : Over σ :=
  MvPolynomial.X i + C (parameter 0) * MvPolynomial.X j - C (parameter 2)

def sliceIdeal {σ : Type} (P : Ideal (Raw σ)) (i j : σ) : Ideal (Over σ) :=
  P.map (map (algebraMap FX SectionField)) ⊔ Ideal.span {fieldLine i j}

private def preLine {σ : Type} (i j : σ) : Pre σ :=
  MvPolynomial.X i + C (MvPolynomial.X (0 : Fin 4)) * MvPolynomial.X j - C (MvPolynomial.X (2 : Fin 4))

private def preIdeal {σ : Type} (P : Ideal (Raw σ)) (i j : σ) : Ideal (Pre σ) :=
  P.map (map (C : FX →+* Parameters)) ⊔ Ideal.span {preLine i j}

private def offsetValue {R : Type} [CommRing R] (x y : R) : MvPolynomial Free R :=
  C x + MvPolynomial.X ⟨0, by decide⟩ * C y

/-- Before inverting the parameters, solve for the offset as a polynomial in
the slope and the two coordinates of the quotient. -/
private def cutEval {σ : Type} (P : Ideal (Raw σ)) (i j : σ) :
    MvPolynomial (Fin 4) (Raw σ) →+* MvPolynomial Free (Raw σ ⧸ P) :=
  eval₂Hom (C.comp (Ideal.Quotient.mk P)) fun k =>
    if hk : k ≠ 2 then MvPolynomial.X ⟨k, hk⟩
    else offsetValue (Ideal.Quotient.mk P (MvPolynomial.X i)) (Ideal.Quotient.mk P (MvPolynomial.X j))

private theorem cutEval_ker {σ : Type} (P : Ideal (Raw σ)) (i j : σ) :
    RingHom.ker (cutEval P i j) =
      P.map C ⊔ Ideal.span {C (MvPolynomial.X i) +
        MvPolynomial.X (0 : Fin 4) * C (MvPolynomial.X j) - MvPolynomial.X 2} := by
  let g : MvPolynomial (Fin 4) (Raw σ) :=
    C (MvPolynomial.X i) + MvPolynomial.X (0 : Fin 4) * C (MvPolynomial.X j) - MvPolynomial.X (2 : Fin 4)
  let J : Ideal (MvPolynomial (Fin 4) (Raw σ)) := P.map C ⊔ Ideal.span {g}
  let q := Ideal.Quotient.mk J
  change RingHom.ker (cutEval P i j) = J
  have hc : ∀ a ∈ P, q (C a) = 0 := fun a ha =>
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_sup_left (Ideal.mem_map_of_mem (C : Raw σ →+* MvPolynomial (Fin 4) (Raw σ)) ha))
  let b := Ideal.Quotient.lift P (q.comp C) hc
  let back : MvPolynomial Free (Raw σ ⧸ P) →+* _ :=
    eval₂Hom b (fun k => q (MvPolynomial.X k.1))
  have hline : q g = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))
  have hright : back.comp (cutEval P i j) = q := by
    apply ringHom_ext
    · intro a
      simp [cutEval, back, b]
    · intro k
      by_cases hk : k ≠ 2
      · simp [cutEval, back, hk]
      · have h : k = 2 := not_ne_iff.mp hk
        subst k
        have he := sub_eq_zero.mp (show q (C (MvPolynomial.X i)) +
            q (MvPolynomial.X 0) * q (C (MvPolynomial.X j)) - q (MvPolynomial.X 2) = 0 by
          simpa only [g, map_add, map_mul, map_sub] using hline)
        simpa [cutEval, back, b, offsetValue] using he
  apply le_antisymm
  · intro a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← RingHom.congr_fun hright a]
    change back (cutEval P i j a) = 0
    rw [RingHom.mem_ker.mp ha, map_zero]
  · apply sup_le
    · apply Ideal.map_le_iff_le_comap.mpr
      intro a ha
      simp [RingHom.mem_ker, cutEval, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    · apply (Ideal.span_singleton_le_iff_mem _).mpr
      simp [RingHom.mem_ker, g, cutEval, offsetValue]

private def preEval {σ : Type} (P : Ideal (Raw σ)) (i j : σ) :
    Pre σ →+* MvPolynomial Free (Raw σ ⧸ P) :=
  (cutEval P i j).comp (commAlgEquiv FX σ (Fin 4)).toRingHom

private theorem preIdeal_eq_ker {σ : Type} (P : Ideal (Raw σ)) (i j : σ) :
    preIdeal P i j = RingHom.ker (preEval P i j) := by
  let e := (commAlgEquiv FX σ (Fin 4)).toRingEquiv
  have hcomp : e.toRingHom.comp (map (C : FX →+* Parameters)) = C := by
    apply ringHom_ext <;> simp [e]
  have hline : e.toRingHom (preLine i j) =
      C (MvPolynomial.X i) + MvPolynomial.X (0 : Fin 4) * C (MvPolynomial.X j) -
        MvPolynomial.X 2 := by
    simp [e, preLine]
  apply e.idealComapOrderIso.symm.injective
  simp only [RingEquiv.idealComapOrderIso_symm_apply]
  change (preIdeal P i j).map e.toRingHom =
    ((RingHom.ker (cutEval P i j)).comap e.toRingHom).map e.toRingHom
  rw [Ideal.map_comap_of_surjective e.toRingHom e.surjective, preIdeal, Ideal.map_sup, Ideal.map_map, hcomp,
    Ideal.map_span, Set.image_singleton, hline, cutEval_ker]

attribute [local instance] MvPolynomial.algebraMvPolynomial

private abbrev denominators (σ : Type) := Parameters⁰.map (C : Parameters →+* Pre σ)

private theorem extend_comp {σ : Type} :
    (algebraMap (Pre σ) (Over σ)).comp (map (C : FX →+* Parameters)) =
      map (algebraMap FX SectionField) := by
  change (map (algebraMap Parameters SectionField)).comp (map (C : FX →+* Parameters)) = _
  apply ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, map_C]
    rfl
  · intro i
    simp

private theorem slice_eq_map {σ : Type} (P : Ideal (Raw σ)) (i j : σ) :
    sliceIdeal P i j = (preIdeal P i j).map (algebraMap (Pre σ) (Over σ)) := by
  have hline : algebraMap (Pre σ) (Over σ) (preLine i j) = fieldLine i j := by
    change map (algebraMap Parameters SectionField) (preLine i j) = _
    simp [preLine, fieldLine, parameter]
  rw [preIdeal, Ideal.map_sup, Ideal.map_map, extend_comp, Ideal.map_span,
    Set.image_singleton, hline, sliceIdeal]

/-- A nonempty generic slice of a prime remains prime and contracts to that prime. -/
theorem prime_and_contract {σ : Type} (P : Ideal (Raw σ)) [P.IsPrime] (i j : σ)
    (hne : sliceIdeal P i j ≠ ⊤) :
    (sliceIdeal P i j).IsPrime ∧
      (sliceIdeal P i j).comap (map (algebraMap FX SectionField)) = P := by
  have hP : (preIdeal P i j).IsPrime := by
    rw [preIdeal_eq_ker]
    exact RingHom.ker_isPrime _
  have hd := (IsLocalization.map_algebraMap_ne_top_iff_disjoint
    (denominators σ) (Over σ) (preIdeal P i j)).mp (slice_eq_map P i j ▸ hne)
  have hcon := IsLocalization.under_map_of_isPrime_disjoint (denominators σ) (Over σ) hP hd
  have he : (preEval P i j).comp (map (C : FX →+* Parameters)) =
      C.comp (Ideal.Quotient.mk P) := by
    apply ringHom_ext <;> simp [preEval, cutEval]
  refine ⟨?_, ?_⟩
  · rw [slice_eq_map]
    exact IsLocalization.isPrime_of_isPrime_disjoint (denominators σ) (Over σ) _ hP hd
  · change ((preIdeal P i j).map (algebraMap (Pre σ) (Over σ))).comap
      (algebraMap (Pre σ) (Over σ)) = preIdeal P i j at hcon
    rw [← extend_comp, ← Ideal.comap_comap, slice_eq_map, hcon, preIdeal_eq_ker, RingHom.comap_ker, he,
      RingHom.ker_comp_of_injective _ (MvPolynomial.C_injective Free (Raw σ ⧸ P)), Ideal.mk_ker]

private theorem preIdeal_comap_rename {σ τ : Type} (r : σ → τ)
    (P : Ideal (Raw τ)) (i j : σ) :
    preIdeal (P.comap (rename r).toRingHom) i j =
      (preIdeal P (r i) (r j)).comap (rename r).toRingHom := by
  let Q : Ideal (Raw σ) := P.comap (rename r).toRingHom
  let f : (Raw σ ⧸ Q) →+* (Raw τ ⧸ P) := Ideal.quotientMap P (rename r).toRingHom le_rfl
  have hswap : (commAlgEquiv FX τ (Fin 4)).toRingHom.comp
      (rename r : Pre σ →ₐ[Parameters] Pre τ).toRingHom =
        (map (rename r : Raw σ →ₐ[FX] Raw τ).toRingHom).comp
          (commAlgEquiv FX σ (Fin 4)).toRingHom := by
    apply ringHom_ext
    · intro a
      change commAlgEquiv FX τ (Fin 4) (rename r (C a)) =
        map (rename r : Raw σ →ₐ[FX] Raw τ).toRingHom (commAlgEquiv FX σ (Fin 4) (C a))
      have hc : (rename r : Raw σ →ₐ[FX] Raw τ).toRingHom.comp C = (C : FX →+* Raw τ) := by
        ext x
        simp
      rw [rename_C, commAlgEquiv_C, commAlgEquiv_C, map_map, hc]
    · intro k
      simp
  have hcut : (map f).comp (cutEval Q i j) =
      (cutEval P (r i) (r j)).comp (map (rename r : Raw σ →ₐ[FX] Raw τ).toRingHom) := by
    apply ringHom_ext
    · intro a
      simp [cutEval, f]
    · intro k
      by_cases hk : k = 2 <;> simp [cutEval, offsetValue, hk, f]
  have hcomp : (map f).comp (preEval Q i j) =
      (preEval P (r i) (r j)).comp (rename r).toRingHom := by
    unfold preEval
    rw [← RingHom.comp_assoc, hcut, RingHom.comp_assoc, ← hswap, RingHom.comp_assoc]
  rw [preIdeal_eq_ker, preIdeal_eq_ker, RingHom.comap_ker, ← hcomp,
    RingHom.ker_comp_of_injective _ (map_injective f Ideal.quotientMap_injective)]

/-- Imposing the line equation commutes with contraction to its two coordinates. -/
theorem slice_comap_rename {σ τ : Type} (r : σ → τ)
    (P : Ideal (Raw τ)) (i j : σ) :
    sliceIdeal (P.comap (rename r).toRingHom) i j =
      (sliceIdeal P (r i) (r j)).comap (rename r).toRingHom := by
  let Q : Ideal (Raw σ) := P.comap (rename r).toRingHom
  let h : Over σ →+* Over τ := (rename r).toRingHom
  let g : Pre σ →+* Pre τ := (rename r).toRingHom
  have hcomp : h.comp (algebraMap (Pre σ) (Over σ)) =
      (algebraMap (Pre τ) (Over τ)).comp g := by
    exact (map_comp_rename (algebraMap Parameters SectionField) r).symm
  apply (IsLocalization.orderEmbedding (denominators σ) (Over σ)).injective
  ext x
  change algebraMap (Pre σ) (Over σ) x ∈ sliceIdeal Q i j ↔
    h (algebraMap (Pre σ) (Over σ) x) ∈ sliceIdeal P (r i) (r j)
  rw [show h (algebraMap (Pre σ) (Over σ) x) = algebraMap (Pre τ) (Over τ) (g x)
      from RingHom.congr_fun hcomp x, slice_eq_map, slice_eq_map,
    IsLocalization.algebraMap_mem_map_algebraMap_iff (denominators σ),
    IsLocalization.algebraMap_mem_map_algebraMap_iff (denominators τ)]
  rw [show preIdeal Q i j = (preIdeal P (r i) (r j)).comap g from
    preIdeal_comap_rename r P i j]
  simp only [Submonoid.mem_map, exists_exists_and_eq_and, Ideal.mem_comap,
    map_mul, g, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_C]

end

end K1_14_3R_3_3
end PackSource_K1_14_3R_3_3Chart

section PackSource_K1_14_3R_3_3Degree
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace K1_14_3R_3_3

open K1_14 K1_14_3

/-- The planar slice is the same quotient as the shared degree computation. -/
theorem seedSlice_finrank (f : Seeds) (hf : f ≠ 0) :
    Module.finrank SectionField (SectionSeeds ⧸ sliceIdeal (Ideal.span {f}) 0 1) =
      f.totalDegree := by
  have h : sliceIdeal (Ideal.span {f}) (0 : Fin 2) 1 = K1_14_3_2_5.curveSectionIdeal f := by
    unfold sliceIdeal K1_14_3_2_5.curveSectionIdeal K1_14_3_2_5.seedBase
    rw [Ideal.map_span, Set.image_singleton, ← Ideal.span_union, Set.singleton_union]
    rfl
  let e := Ideal.quotientEquivAlgOfEq SectionField h
  exact e.toLinearEquiv.finrank_eq.trans (K1_14_3_2_5_1.proof f hf)

end K1_14_3R_3_3
end PackSource_K1_14_3R_3_3Degree

section PackSource_K1_14_3R_3_3Proof
set_option autoImplicit true
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

private def nest (F : Type) [CommRing F] :
    MvPolynomial Coord F ≃ₐ[F] Polynomial (Polynomial (MvPolynomial (Fin 2) F)) :=
  (optionEquivLeft F (Option (Fin 2))).trans (Polynomial.mapAlgEquiv (optionEquivLeft F (Fin 2)))

private def rawIdeal (I : Ideal Jet) : Ideal (Raw Coord) :=
  I.comap (nest FX).toRingHom

private abbrev jetSlice (I : Ideal Jet) := sliceIdeal (rawIdeal I) (seedCoord 0) (seedCoord 1)

private theorem seedIdeal_eq (I : Ideal Jet) :
    seedIdeal I = (rawIdeal I).comap (rename seedCoord).toRingHom := by
  have h : (nest FX).toRingHom.comp (rename seedCoord).toRingHom = seedInclusion := by
    apply ringHom_ext <;> simp [nest, seedCoord, seedInclusion, Polynomial.mapAlgEquiv]
  rw [rawIdeal, Ideal.comap_comap, h, seedIdeal]

private def lineEquiv (I : Ideal Jet) :
    (Over Coord ⧸ jetSlice I) ≃ₐ[SectionField] LineSection I .seed := by
  let e := nest SectionField
  have hcomm : e.toRingHom.comp (map (algebraMap FX SectionField)) =
      sectionMap.comp (nest FX).toRingHom := by
    apply ringHom_ext
    · intro a
      simp [e, nest, sectionMap, Polynomial.mapAlgEquiv]
    · rintro (_ | (_ | i)) <;> simp [e, nest, sectionMap, Polynomial.mapAlgEquiv]
  have hline : e (fieldLine (seedCoord 0) (seedCoord 1)) = lineEquation .seed := by
    simp [e, nest, fieldLine, seedCoord, lineEquation, sectionScalar, parameter,
      Polynomial.mapAlgEquiv]
  refine Ideal.quotientEquivAlg _ _ e ?_
  change I.map sectionMap ⊔ Ideal.span {lineEquation .seed} =
    (((I.comap (nest FX).toRingHom).map (map (algebraMap FX SectionField))) ⊔
      Ideal.span {fieldLine (seedCoord 0) (seedCoord 1)}).map e.toRingHom
  rw [Ideal.map_sup, Ideal.map_map, hcomm, ← Ideal.map_map,
    Ideal.map_comap_of_surjective (nest FX).toRingHom (nest FX).surjective,
    Ideal.map_span, Set.image_singleton]
  change _ = _ ⊔ Ideal.span {e (fieldLine (seedCoord 0) (seedCoord 1))}
  rw [hline]

private theorem degree_le_slice (R : Ideal Jet) (f : Seeds)
    (he : HasSeedEquation R f) [FiniteDimensional SectionField (Over Coord ⧸ jetSlice R)] :
    f.totalDegree ≤ Module.finrank SectionField (Over Coord ⧸ jetSlice R) := by
  have h := slice_comap_rename seedCoord (rawIdeal R) 0 1
  rw [← seedIdeal_eq, he.2] at h
  let e : SectionSeeds →ₐ[SectionField] Over Coord := rename seedCoord
  let E := Ideal.quotientMapₐ (jetSlice R) e h.le
  rw [← seedSlice_finrank f he.1]
  exact LinearMap.finrank_le_finrank_of_injective (f := E.toLinearMap)
    (Ideal.quotientMap_injective' (H := h.le) h.ge)

private theorem maximal_of_finite {k A : Type} [Field k] [CommRing A] [Algebra k A]
    (P : Ideal A) [P.IsPrime] [Module.Finite k (A ⧸ P)] : P.IsMaximal := by
  let : Algebra.IsIntegral k (A ⧸ P) := Algebra.IsIntegral.of_finite k _
  exact Ideal.Quotient.maximal_of_isField _
    (isField_of_isIntegral_of_isField' (S := A ⧸ P) (Field.toIsField k))

theorem proof : K1_14_3R_3.c3 := by
  classical
  intro I T f hfinite hT
  let A := jetSlice I
  let B (R : T) := jetSlice R.val
  let : FiniteDimensional SectionField (LineSection I .seed) := hfinite
  let : FiniteDimensional SectionField (Over Coord ⧸ A) :=
    Module.Finite.equiv (lineEquiv I).symm.toLinearEquiv
  have hAB (R : T) : A ≤ B R := sup_le_sup_right
    (Ideal.map_mono (Ideal.comap_mono (hT R.val R.property).1)) _
  let q (R : T) := Ideal.Quotient.factorₐ SectionField (hAB R)
  let : ∀ R : T, FiniteDimensional SectionField (Over Coord ⧸ B R) := fun R =>
    Module.Finite.of_surjective ((q R).toLinearMap) (Ideal.Quotient.factor_surjective (hAB R))
  have hprime (R : T) (hR : B R ≠ ⊤) :
      (B R).IsPrime ∧ (B R).comap (map (algebraMap FX SectionField)) = rawIdeal R.val := by
    let : R.val.IsPrime := (hT R.val R.property).2.1.1
    let : (rawIdeal R.val).IsPrime := Ideal.IsPrime.comap (nest FX).toRingHom
    exact prime_and_contract _ _ _ hR
  have hmax (R : T) (hR : B R ≠ ⊤) : (B R).IsMaximal := by
    let : (B R).IsPrime := (hprime R hR).1
    exact maximal_of_finite (k := SectionField) (B R)
  -- Nonempty fibres contract to distinct original primes. Empty fibres have the unit ideal.
  have hcop : Pairwise (fun (R S : T) => IsCoprime (B R) (B S)) := by
    intro R S hne
    by_cases hR : B R = ⊤
    · simp [Ideal.isCoprime_iff_sup_eq, hR]
    by_cases hS : B S = ⊤
    · simp [Ideal.isCoprime_iff_sup_eq, hS]
    let : (B R).IsMaximal := hmax R hR
    let : (B S).IsMaximal := hmax S hS
    apply Ideal.isCoprime_of_isMaximal
    intro h
    have hc : rawIdeal R.val = rawIdeal S.val := calc
      _ = (B R).comap (map (algebraMap FX SectionField)) := (hprime R hR).2.symm
      _ = (B S).comap (map (algebraMap FX SectionField)) := congrArg (Ideal.comap _) h
      _ = _ := (hprime S hS).2
    exact hne (Subtype.ext ((Ideal.comap_injective_of_surjective
      (nest FX).toRingHom (nest FX).surjective) hc))
  let (R : T) : Module.Free SectionField (Over Coord ⧸ B R) :=
    Module.Free.of_divisionRing (K := SectionField) (V := Over Coord ⧸ B R)
  let Q : (Over Coord ⧸ A) →ₗ[SectionField] ∀ R : T, Over Coord ⧸ B R :=
    LinearMap.pi (fun R => (q R).toLinearMap)
  have hsur : Function.Surjective Q := by
    intro x
    obtain ⟨r, hr⟩ := Ideal.pi_quotient_surjective hcop x
    exact ⟨Ideal.Quotient.mk A r, funext hr⟩
  calc
    ∑ R ∈ T, (f R).totalDegree =
        ∑ R : T, (f R.val).totalDegree := (Finset.sum_coe_sort _ _).symm
    _ ≤ ∑ R : T, Module.finrank SectionField (Over Coord ⧸ B R) :=
      Finset.sum_le_sum fun R _ => degree_le_slice R.val (f R.val) (hT R.val R.property).2.2
    _ = Module.finrank SectionField (∀ R : T, Over Coord ⧸ B R) :=
      (Module.finrank_pi_fintype SectionField).symm
    _ ≤ Module.finrank SectionField (Over Coord ⧸ A) :=
      LinearMap.finrank_le_finrank_of_surjective hsur
    _ = lineLength I .seed := (lineEquiv I).toLinearEquiv.finrank_eq

end

end K1_14_3R_3_3
end PackSource_K1_14_3R_3_3Proof

section PackSource_K1_14_2_6Defs
set_option autoImplicit true
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

/-- Here the generic coordinates are Y and V. The same type of rational
function field is used, but its two indeterminates describe the jet plane. -/
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
end PackSource_K1_14_2_6Defs

section PackSource_K1_14_2_6Aux
set_option autoImplicit true
set_option maxHeartbeats 1000000

namespace K1_14_2_6

noncomputable section

open K1_14 K1_14_2 Polynomial
open scoped BigOperators nonZeroDivisors

private theorem eval_root (f : Equation) (y v : GenericClosure) :
    genericSeedPoint y v (rootIncl (toRoot f)) = (f.map toGenericClosure).eval y := by
  have hcoeff : (genericSeedPoint y v).comp (rootIncl.comp rootSeeds) =
      toGenericClosure := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [genericSeedPoint, rootIncl, rootSeeds, toGenericClosure]
      exact IsScalarTower.algebraMap_apply FX Seeds GenericClosure c
    · intro i
      fin_cases i <;> simp [genericSeedPoint, rootIncl, rootSeeds, toGenericClosure, generic]
  change genericSeedPoint y v (rootIncl (f.eval₂ rootSeeds (MvPolynomial.X 2))) = _
  have hy : genericSeedPoint y v (rootIncl (MvPolynomial.X 2)) = y := by
    simp [genericSeedPoint, rootIncl]
  rw [Polynomial.hom_eval₂, Polynomial.hom_eval₂]
  change f.eval₂ ((genericSeedPoint y v).comp (rootIncl.comp rootSeeds)) _ = _
  rw [hcoeff, hy, Polynomial.eval_map]

/-- At V-order equal to the V-degree, the outer Hasse derivative is constant.
The remaining Y-contact is the divisibility of the leading coefficient. -/
theorem leading_root_power {P : Jet} {y v : GenericClosure} {m : ℕ}
    (h : HasJetContact P y v m) :
    (Polynomial.X (R := GenericClosure) - C y) ^ (m - P.natDegree) ∣ P.leadingCoeff.map toGenericClosure := by
  have hcoeff : ∀ a < m - P.natDegree,
      (hasseDeriv a (P.leadingCoeff.map toGenericClosure)).eval y = 0 := by
    intro a ha
    have hh := h a P.natDegree (by omega)
    have hV : hasseDeriv P.natDegree (fibreRow P) =
        C (P.leadingCoeff.map toGenericClosure) := by
      rw [fibreRow, hasseDeriv_map, hasseDeriv_natDegree_eq_C, map_C]
      rfl
    rwa [hV, eval_C] at hh
  have hdiv : (Polynomial.X (R := GenericClosure)) ^ (m - P.natDegree) ∣
      taylor y (P.leadingCoeff.map toGenericClosure) :=
    X_pow_dvd_iff.mpr fun a ha => by rw [taylor_coeff, hcoeff a ha]
  have hb := map_dvd (taylorAlgHom (-y)).toRingHom hdiv
  simpa [taylor_taylor, sub_eq_add_neg, add_comm] using hb

private theorem minpoly_pow_dvd {y : GenericClosure} (hy : IsSeparable SeedField y)
    {g : SeedField[X]} (n : ℕ)
    (h : (Polynomial.X (R := GenericClosure) - C y) ^ n ∣ g.map (algebraMap SeedField GenericClosure)) :
    minpoly SeedField y ^ n ∣ g := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
      by_cases hg : g = 0
      · simp [hg]
      have hyroot : Polynomial.X (R := GenericClosure) - C y ∣ g.map (algebraMap SeedField GenericClosure) :=
        (dvd_pow_self _ (by omega)).trans h
      have hymin : minpoly SeedField y ∣ g := by
        apply minpoly.dvd SeedField y
        simpa only [IsRoot.def, eval_map_algebraMap] using dvd_iff_isRoot.mp hyroot
      obtain ⟨r, hr⟩ := hymin
      have hr0 : r ≠ 0 := by
        intro hz
        exact hg (by simp [hr, hz])
      have horder := (le_rootMultiplicity_iff (Polynomial.map_ne_zero hg)).mpr h
      rw [hr, Polynomial.map_mul, rootMultiplicity_mul
        (mul_ne_zero (Polynomial.map_ne_zero (minpoly.ne_zero hy.isIntegral))
          (Polynomial.map_ne_zero hr0))] at horder
      have hsep : ((minpoly SeedField y).map (algebraMap SeedField GenericClosure)).Separable :=
        (show (minpoly SeedField y).Separable from hy).map
      have hle := rootMultiplicity_le_one_of_separable hsep y
      have hrdvd : (Polynomial.X (R := GenericClosure) - C y) ^ n ∣
          r.map (algebraMap SeedField GenericClosure) :=
        (le_rootMultiplicity_iff (Polynomial.map_ne_zero hr0)).mp (by omega)
      rw [hr, pow_succ']
      exact mul_dvd_mul_left _ (ih hrdvd)

private theorem primitive_lift (q : SeedField[X]) (hq : q ≠ 0) :
    ∃ f : Equation, f.IsPrimitive ∧
      Associated (f.map (algebraMap Seeds SeedField)) q := by
  let : StrongNormalizationMonoid Seeds := UniqueFactorizationMonoid.strongNormalizationMonoid
  let : NormalizedGCDMonoid Seeds := UniqueFactorizationMonoid.toNormalizedGCDMonoid Seeds
  let g : Equation := IsLocalization.integerNormalization Seeds⁰ q
  have hg : g ≠ 0 := IsFractionRing.integerNormalization_eq_zero_iff.not.mpr hq
  let inc := algebraMap Seeds SeedField
  obtain ⟨b, hb, he⟩ := IsLocalization.integerNormalization_spec Seeds⁰ q
  have he' : C (inc g.content) * g.primPart.map inc = C (inc b) * q := by
    rw [← map_C, ← Polynomial.map_mul, ← g.eq_C_content_mul_primPart]
    simpa only [Algebra.smul_def, Polynomial.algebraMap_apply] using he
  have hunit (r : Seeds) (hr : r ≠ 0) : IsUnit (C (inc r)) := by
    apply isUnit_C.mpr
    apply isUnit_iff_ne_zero.mpr
    simpa only [inc, map_zero] using (IsFractionRing.injective Seeds SeedField).ne hr
  refine ⟨g.primPart, g.isPrimitive_primPart,
    (associated_unit_mul_left _ _ (hunit _ (content_eq_zero_iff.not.mpr hg))).symm.trans ?_⟩
  rw [he']
  exact associated_unit_mul_left _ _ (hunit _ (nonZeroDivisors.ne_zero hb))

/-- The distinct monic minimal polynomials give the reduced projected product
in the fraction field. Take its primitive representative over the seeds. -/
theorem primitive_projection (S : Finset (Ideal Ambient)) (hS : S.Nonempty)
    (hseed : ∀ I ∈ S, ∃ y v, OnSeedFibre I y v ∧ IsSeparable SeedField y) :
    ∃ f : Equation, 0 < f.natDegree ∧ f.IsPrimitive ∧
      (f.map (algebraMap Seeds SeedField)).Separable ∧
      (∀ I ∈ S, rootIncl (toRoot f) ∈ I) ∧
      ∀ (g : Equation) (n : ℕ),
        (∀ I ∈ S, ∀ y v, OnSeedFibre I y v →
          (Polynomial.X (R := GenericClosure) - C y) ^ n ∣ g.map toGenericClosure) → f ^ n ∣ g := by
  classical
  have hchoose : ∀ i : S, ∃ y v, OnSeedFibre i.val y v ∧ IsSeparable SeedField y :=
    fun i => hseed i.val i.property
  choose y v hpoint hsep using hchoose
  let factors : Finset SeedField[X] := Finset.univ.image fun i : S => minpoly SeedField (y i)
  have hmem (i : S) : minpoly SeedField (y i) ∈ factors := by
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hfac (r : SeedField[X]) (hr : r ∈ factors) :
      r.Monic ∧ Irreducible r ∧ r.Separable := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    exact ⟨minpoly.monic (hsep i).isIntegral, minpoly.irreducible (hsep i).isIntegral, hsep i⟩
  have hcop (r : SeedField[X]) (hr : r ∈ factors)
      (s : SeedField[X]) (hs : s ∈ factors) (hne : r ≠ s) : IsCoprime r s :=
    (hfac r hr).2.1.coprime_iff_not_dvd.mpr fun hd =>
      hne (Polynomial.eq_of_monic_of_associated (hfac r hr).1 (hfac s hs).1
        ((hfac r hr).2.1.associated_of_dvd (hfac s hs).2.1 hd))
  let q := ∏ r ∈ factors, r
  have hq : q.Monic := monic_prod_of_monic _ _ fun r hr => (hfac r hr).1
  have hqsep : q.Separable := separable_prod' hcop fun r hr => (hfac r hr).2.2
  obtain ⟨f, hf, hrel⟩ := primitive_lift q hq.ne_zero
  let inc := algebraMap Seeds SeedField
  have hdiv (i : S) : minpoly SeedField (y i) ∣ f.map inc :=
    (Finset.dvd_prod_of_mem id (hmem i)).trans hrel.dvd'
  obtain ⟨I, hI⟩ := hS
  have hd := natDegree_le_of_dvd (hdiv ⟨I, hI⟩) ((Polynomial.map_ne_zero_iff (IsFractionRing.injective Seeds SeedField)).2 hf.ne_zero)
  rw [natDegree_map_eq_of_injective (IsFractionRing.injective Seeds SeedField)] at hd
  refine ⟨f, (minpoly.natDegree_pos (hsep ⟨I, hI⟩).isIntegral).trans_le hd,
    hf, hrel.symm.separable hqsep, ?_, ?_⟩
  · intro J hJ
    let j : S := ⟨J, hJ⟩
    change rootIncl (toRoot f) ∈ j.val
    rw [← hpoint j, RingHom.mem_ker, eval_root]
    change (f.map ((algebraMap SeedField GenericClosure).comp inc)).eval (y j) = 0
    rw [← Polynomial.map_map, eval_map_algebraMap]
    exact minpoly.dvd_iff.mp (hdiv j)
  · intro g n hpowers
    have hqdiv : q ^ n ∣ g.map inc := by
      rw [show q = ∏ r ∈ factors, r from rfl, ← Finset.prod_pow]
      apply Finset.prod_dvd_of_coprime (fun r hr s hs hne => (hcop r hr s hs hne).pow)
      intro r hr
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
      apply minpoly_pow_dvd (hsep i) n
      rw [Polynomial.map_map]
      exact hpowers i.val i.property (y i) (v i) (hpoint i)
    let : StrongNormalizationMonoid Seeds := UniqueFactorizationMonoid.strongNormalizationMonoid
    let : NormalizedGCDMonoid Seeds := UniqueFactorizationMonoid.toNormalizedGCDMonoid Seeds
    have hprim (n : ℕ) : (f ^ n).IsPrimitive := by
      induction n with
      | zero => simpa only [pow_zero] using (isPrimitive_one (R := Seeds))
      | succ n ih => simpa only [pow_succ] using ih.mul hf
    apply (hprim n).dvd_of_fraction_map_dvd_fraction_map (K := SeedField)
    rw [Polynomial.map_pow]
    exact (pow_dvd_pow_of_dvd hrel.dvd n).trans hqdiv

end
end K1_14_2_6
end PackSource_K1_14_2_6Aux

section PackSource_K1_14_2_6Split
set_option autoImplicit true
namespace K1_14_2_6

noncomputable section

open K1 K1_14 K1_14_2 Polynomial

/-- Positive finite generic fibres of a prime give generic points, with
separability supplied by the two rank bounds. -/
def c1 : Prop :=
  ∀ I : Ideal Ambient, I.IsPrime →
    Module.Finite SeedField (OverSeeds I) →
    0 < Module.finrank SeedField (OverSeeds I) →
    Module.finrank SeedField (OverSeeds I) < p →
    Module.Finite SeedField (OverJets I) →
    0 < Module.finrank SeedField (OverJets I) →
    Module.finrank SeedField (OverJets I) < p →
    (∃ y v, OnSeedFibre I y v ∧ IsSeparable SeedField y) ∧ SeparableJetFibre I

/-- Mixed tangent induction, expressed with Hasse coefficients in both
the input seed variables and the output jet variables. -/
def c2 : Prop :=
  ∀ (I : Ideal Ambient), SeparableJetFibre I →
    ∀ (P : Jet) (m : ℕ), m < p → HasSeedContact I P m →
    ∀ y v, OnSeedFibre I y v → HasJetContact P y v m

private def contactOrder (w : ℤ) (W : ℕ) : ℕ :=
  1 + (full.m * 180265 - 1 - W) / (2 * w.toNat)

private theorem contactOrder_lt (w : ℤ) (W : ℕ) : contactOrder w W < p := by
  have hd := Nat.div_le_self (full.m * 180265 - 1 - W) (2 * w.toNat)
  calc
    contactOrder w W ≤ 1 + (full.m * 180265 - 1) :=
      Nat.add_le_add_left (hd.trans (Nat.sub_le _ _)) 1
    _ = full.m * 180265 := by decide
    _ < p := by decide

private theorem contact_of_shift {u del} {M : AnchorModel u del} {Γ}
    {F : AnchoredFamily M Γ} {rows : Banks} (src : JetSource M F rows)
    (hlo : 2601 ≤ M.overhead) (hhi : M.overhead ≤ 3554)
    (parents : RetainedParents rows) {I : Ideal Ambient} (hI : I ∈ parents.ideals)
    {s : Shape} (hs : s ∈ scheduled M.overhead)
    (hm : s.m = full.m) (hB : s.B = full.B) (hJ : s.J = full.J)
    (hU : s.U ≤ full.U) {W : ℕ} (hW : W < full.m * 180265)
    {P : Jet} (hP : P ∈ rows s W) :
    HasSeedContact I P (contactOrder M.overhead W) := by
  intro a b hab
  let d := 2 * M.overhead.toNat
  have hd : 0 < d := by dsimp [d]; omega
  have hr : a + b ≤ (full.m * 180265 - 1 - W) / d := by
    change a + b < 1 + (full.m * 180265 - 1 - W) / d at hab
    omega
  have hcost := (Nat.le_div_iff_mul_le hd).mp hr
  rw [Nat.mul_comm, Nat.mul_add] at hcost
  have hcut : W + d * b + d * a ≤ full.m * 180265 - 1 := by omega
  have hfull : full ∈ scheduled M.overhead := by simp [scheduled, hhi, full]
  have hPb := src.shift s hs W P hP 1 b
  have hPab := src.shift s hs (W + d * b) _ hPb 0 a
  exact parents.terminal I hI _ (src.nested s hs full hfull hm hB hJ hU _ _ hcut hPab)

theorem of_children (h1 : c1) (h2 : c2) : K1_14_2.c6 := by
  intro u del M Γ F hlo hhi rows src parents hp
  have hcharts (I : Ideal Ambient) (hI : I ∈ parents.ideals) :=
    h1 I (parents.prime I hI)
      (parents.seed_finite I hI) (parents.seed_size I hI).1 (parents.seed_size I hI).2
      (parents.jet_finite I hI) (parents.jet_size I hI).1 (parents.jet_size I hI).2
  obtain ⟨f, hdeg, hprim, hsep, hmem, hdiv⟩ :=
    primitive_projection parents.ideals hp (fun I hI => (hcharts I hI).1)
  have hpower (W j : ℕ) :
      forcedPower M.overhead W j = contactOrder M.overhead W - j := by
    simp [forcedPower, contactOrder, band, hhi, full]
  have hforced (s : Shape) (hs : s ∈ scheduled M.overhead)
      (hm : s.m = full.m) (hB : s.B = full.B) (hJ : s.J = full.J)
      (hU : s.U ≤ full.U) (W : ℕ) (hW : W < full.m * 180265)
      (P : Jet) (hP : P ∈ rows s W) :
      f ^ forcedPower M.overhead W P.natDegree ∣ P.leadingCoeff := by
    rw [hpower]
    apply hdiv
    intro I hI y v hpoint
    exact leading_root_power (h2 I (hcharts I hI).2 P _ (contactOrder_lt _ _)
      (contact_of_shift src hlo hhi parents hI hs hm hB hJ hU hW hP) y v hpoint)
  refine ⟨f, hdeg, hprim, hsep, hmem, ?_, ?_⟩
  · intro W hW P hP _
    have hs : full ∈ scheduled M.overhead := by simp [scheduled, hhi, full]
    exact hforced full hs rfl rfl rfl le_rfl W hW P hP
  · intro W hW P hP _
    let s := terminalShape M.overhead
    have hs : s ∈ scheduled M.overhead := by simp [s, scheduled, hhi]
    have hm : s.m = full.m := by simp [s, terminalShape, band, hhi, full]
    have hB : s.B = full.B := by simp [s, terminalShape, band, hhi, full]
    have hJ : s.J = full.J := by simp [s, terminalShape, band, hhi, full]
    have hU : s.U ≤ full.U := by simp [s, terminalShape, band, hhi, full]
    have hW' : W < full.m * 180265 := by
      simpa [band, hhi, full] using hW
    exact hforced s hs hm hB hJ hU W hW' P hP

end
end K1_14_2_6
end PackSource_K1_14_2_6Split

section PackSource_K1_14_2_6_1Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_14_2_6_1

noncomputable section

open K1 K1_14 K1_14_2 K1_14_2_6

attribute [local instance] MvPolynomial.algebraMvPolynomial

private abbrev Iterated := MvPolynomial (Fin 2) Seeds

-- The base-plane coordinates become coefficients in the outer polynomial ring.
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

private theorem seedMap : mapGenericSeed =
    (algebraMap Iterated FibreRing).comp (chartEquiv seedVariables).toRingHom := by
  rw [chartMap]
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [mapGenericSeed, MvPolynomial.eval₂Hom_C]
  · intro i
    simp only [mapGenericSeed, MvPolynomial.eval₂Hom_X', Function.comp_apply]
    fin_cases i <;> rfl

private theorem jetMap : mapGenericJets =
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

-- A proper localized prime contracts to the original prime. Its finite
-- quotient is a field, so embedding it in the algebraic closure preserves the kernel.
private theorem fibreHom (g : Ambient →+* FibreRing) (e : Ambient ≃+* Iterated)
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

private theorem seedPoint (f : FibreRing →ₐ[SeedField] GenericClosure) :
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

private theorem jetPoint (f : FibreRing →ₐ[SeedField] GenericClosure) :
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

theorem proof : K1_14_2_6.c1 := by
  intro I hI hfinS hposS hsizeS hfinJ hposJ hsizeJ
  obtain ⟨f, hf, hsep⟩ := fibreHom mapGenericSeed _ seedMap I hI hposS hsizeS
  obtain ⟨g, hg, hsep'⟩ := fibreHom mapGenericJets _ jetMap I hI hposJ hsizeJ
  exact ⟨⟨f (MvPolynomial.X 0), f (MvPolynomial.X 1), by
      rw [OnSeedFibre, seedPoint, hf], hsep _⟩,
    ⟨g (MvPolynomial.X 0), g (MvPolynomial.X 1), by rw [jetPoint, hg], hsep' _, hsep' _⟩⟩

end
end K1_14_2_6_1
end PackSource_K1_14_2_6_1Proof

section PackSource_K1_14_2_6_2Tangent
set_option autoImplicit true
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

/-- Extend an infinitesimal displacement of one generic jet coordinate across
the separable seed coordinates. -/
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

/-- Along a separable generic jet fibre, a zero identity whose two fixed-jet
seed derivatives still vanish can be differentiated in either jet direction. -/
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
end PackSource_K1_14_2_6_2Tangent

section PackSource_K1_14_2_6_2Hasse
set_option autoImplicit true
namespace K1_14_2_6_2

noncomputable section

open K1 K1_14 K1_14_2 K1_14_2_6 Polynomial

abbrev coordDeriv (i : Fin 4) : Ambient → Ambient := MvPolynomial.pderiv i

private theorem derivative_eval {R : Type*} [CommRing R]
    (f : Ambient →+* R[X]) (i : Fin 4)
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

private def seedIndex (i : Fin 2) : Fin 4 := Fin.castLE (by decide) i

private def translation (i : Fin 4) : Ambient →+* Ambient[X] :=
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

/-- Fixed-jet seed Hasse coefficients give the corresponding ordinary partials. -/
theorem seed_iter (i : Fin 2) (r : ℕ) (P : Jet) :
    (coordDeriv (seedIndex i))^[r] (toJet P) = r.factorial • toJet (seedHasse i r P) := by
  have h := (translation_derivative (seedIndex i)).iterate_right r (toJet P)
  have hc := congrArg (fun Q : Ambient[X] => Q.coeff 0) h
  simpa only [translation_zero, coeff_iterate_derivative, Nat.zero_add,
    Nat.descFactorial_self, translation_toJet] using hc

private def yFibre (v : GenericClosure) : Ambient →+* GenericClosure[X] :=
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

/-- Specializing an iterated ordinary jet partial gives the fibre Hasse coefficient
multiplied by the two factorials. -/
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
end PackSource_K1_14_2_6_2Hasse

section PackSource_K1_14_3R_1Bridge
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 4000
set_option maxHeartbeats 800000

namespace K1_14_3R_1

noncomputable section

open K1_14 K1_14_3 K1_14_2 Polynomial

local notation "SF" => K1_14_3.SeedField

private def jetCoordinates : Seeds ≃+* JetPlane :=
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

private def fractionCoordinates : JetField ≃+* SF :=
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

@[simp] private theorem toJet_C (x : FX) :
    toJet (C (C (MvPolynomial.C x))) = MvPolynomial.C x := by
  simp [toJet, toRoot, rootIncl, rootSeeds]

@[simp] private theorem toJet_seed (i : Fin 2) :
    toJet (C (C (MvPolynomial.X i))) = MvPolynomial.X (Fin.castLE (by decide) i) := by
  fin_cases i <;> simp [toJet, toRoot, rootIncl, rootSeeds]

@[simp] private theorem toJet_y :
    toJet (C (Polynomial.X (R := Seeds))) = MvPolynomial.X 2 := by
  simp [toJet, toRoot, rootIncl]

@[simp] private theorem toJet_v :
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

private theorem seedGeneric_C (x : FX) :
    seedGeneric (MvPolynomial.C x) = algebraMap FX SeedClosure x := by
  change algebraMap SF SeedClosure (algebraMap Seeds SF (algebraMap FX Seeds x)) = _
  rw [← IsScalarTower.algebraMap_apply Seeds SF SeedClosure,
    ← IsScalarTower.algebraMap_apply FX Seeds SeedClosure]

private theorem seed_chart (y v : SeedClosure) :
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

private theorem generic_C (x : FX) : jetCoordinates.symm (C (C x)) = MvPolynomial.C x :=
  jetCoordinates.symm_apply_eq.mpr (jetCoordinates_C x).symm

private theorem generic_Y : jetCoordinates.symm (C (Polynomial.X (R := FX))) = MvPolynomial.X 0 :=
  jetCoordinates.symm_apply_eq.mpr jetCoordinates_X0.symm

private theorem generic_V : jetCoordinates.symm (Polynomial.X (R := Polynomial FX)) =
    MvPolynomial.X 1 :=
  jetCoordinates.symm_apply_eq.mpr jetCoordinates_X1.symm

/-- Identify the rational jet field with the two-variable rational field
used by the ambient-coordinate tangent theorem. -/
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
end PackSource_K1_14_3R_1Bridge

section PackSource_K1_14_2_6_2Proof
set_option autoImplicit true
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
  | h k ih =>
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
end PackSource_K1_14_2_6_2Proof

section PackSource_K1_14_2_3_2Aux3
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace K1_14_2_3_2

noncomputable section

open K1_14 K1_14_2 Polynomial
open scoped BigOperators

private abbrev liftCoeffs : Seeds →+* MvPolynomial (Fin 2) SeedField :=
  MvPolynomial.map (algebraMap FX SeedField)

private def intercept : SeedField[X] :=
  Polynomial.C (generic 1) - Polynomial.C (generic 0) * Polynomial.X

private def substitute : MvPolynomial (Fin 2) SeedField →ₐ[SeedField] SeedField[X] :=
  MvPolynomial.aeval ![intercept, Polynomial.X]

private def sliced (P : Seeds) : SeedField[X] := substitute (liftCoeffs P)

/-- The leading coefficient in the line variable can be tested over the
polynomial ring of the slope, since the slope is transcendental. -/
private theorem slope_eval_injective :
    Function.Injective (Polynomial.eval₂RingHom (algebraMap FX SeedField) (-generic 0)) := by
  let f : FX[X] →+* Seeds := Polynomial.eval₂RingHom MvPolynomial.C (-MvPolynomial.X 0)
  let g : Seeds →+* FX[X] :=
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
  let slopePoly : FX[X] := ∑ m ∈ top, Polynomial.C (P.coeff m) * Polynomial.X ^ m 0
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

private def planeEquiv (P : Seeds) :
    PlaneSeedSection (Ideal.span {P}) ≃ₐ[SeedField] (SeedField[X] ⧸ Ideal.span {sliced P}) := by
  let J : Ideal (MvPolynomial (Fin 2) SeedField) :=
    (Ideal.span {P}).map liftCoeffs ⊔ Ideal.span {seedLine 0 1}
  let A := MvPolynomial (Fin 2) SeedField ⧸ J
  let B := SeedField[X] ⧸ Ideal.span {sliced P}
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
  let p : SeedField[X] →ₐ[SeedField] A := Polynomial.aeval (j (MvPolynomial.X 1))
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
    _ = Module.finrank SeedField (SeedField[X] ⧸ Ideal.span {sliced P}) :=
      (planeEquiv P).toLinearEquiv.finrank_eq
    _ = _ := finrank_quotient_span_eq_natDegree.trans (sliced_natDegree P hP)

end

end K1_14_2_3_2
end PackSource_K1_14_2_3_2Aux3

section PackSource_K1_14_3_2_4Bezout
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1200000

namespace K1_14_3_2_4

noncomputable section

open MvPolynomial Polynomial

variable {k : Type*} [Field k]

local notation "Biv" => MvPolynomial (Fin 2) k

/-- Finite colength in the plane excludes a common nonunit divisor. -/
private theorem noPrincipalOver {J : Ideal Biv}
    (hfin : Module.Finite k (Biv ⧸ J))
    {D : Biv} (hD : ¬ IsUnit D) (hle : J ≤ Ideal.span {D}) : False := by
  let : Module.Finite k (Biv ⧸ J) := hfin
  let : Module.Finite k (Biv ⧸ Ideal.span ({D} : Set Biv)) :=
    Module.Finite.of_surjective (Ideal.Quotient.factorₐ k hle).toLinearMap
      (Ideal.Quotient.factor_surjective hle)
  have hn : (affineHilbertPolynomial (Ideal.span {D})).natDegree = 0 := by
    rw [affineHilbertPolynomial_eq_C_finrank, Polynomial.natDegree_C]
  by_cases hzero : D = 0
  · simp [hzero, natDegree_affineHilbertPolynomial_bot, Nat.card_eq_fintype_card] at hn
  · have hd := natDegree_affineHilbertPolynomial_span_singleton_add_one hzero
      (mt Ideal.span_singleton_eq_top.mp hD)
    rw [hn] at hd
    simp [Nat.card_eq_fintype_card] at hd

/-- A finite plane quotient by two polynomials in one coordinate is zero. -/
theorem univariate_plane_length_zero (i : k[X] →+* Biv) (A B : k[X])
    (hfin : Module.Finite k (Biv ⧸ Ideal.span {i A, i B})) :
    Module.finrank k (Biv ⧸ Ideal.span {i A, i B}) = 0 := by
  let I : Ideal k[X] := Ideal.span {A, B}
  let J : Ideal Biv := Ideal.span {i A, i B}
  let d := Submodule.IsPrincipal.generator I
  have hgen : Ideal.span {d} = I := Ideal.span_singleton_generator I
  have hJ : J = Ideal.span {i d} := by
    have h : I.map i = J := by simp [I, J, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
    rw [← h, ← hgen, Ideal.map_span, Set.image_singleton]
  have hu : IsUnit (i d) := by
    by_contra hn
    exact noPrincipalOver (J := J) hfin hn (le_of_eq hJ)
  have htop : J = ⊤ := hJ.trans (Ideal.span_singleton_eq_top.mpr hu)
  let : Subsingleton (Biv ⧸ J) := Ideal.Quotient.subsingleton_iff.mpr htop
  change Module.finrank k (Biv ⧸ J) = 0
  exact Module.finrank_eq_zero_of_subsingleton k _

/-- Affine plane Bézout, including scheme length, for two equations of finite colength. -/
theorem planeBezout (F G : Biv) (u : ℕ)
    (hfin : Module.Finite k (Biv ⧸ Ideal.span {F, G}))
    (hF : F.totalDegree ≤ u) (hG : G.totalDegree ≤ u) :
    Module.finrank k (Biv ⧸ Ideal.span {F, G}) ≤ u ^ 2 := by
  let J : Ideal Biv := Ideal.span {F, G}
  let I : Ideal Biv := Ideal.span {F}
  change Module.finrank k (Biv ⧸ J) ≤ _
  by_cases htop : J = ⊤
  · let : Subsingleton (Biv ⧸ J) := Ideal.Quotient.subsingleton_iff.mpr htop
    rw [Module.finrank_eq_zero_of_subsingleton]
    exact Nat.zero_le _
  let : Module.Finite k (Biv ⧸ J) := hfin
  have hFJ : F ∈ J := Ideal.subset_span (by simp)
  have hGJ : G ∈ J := Ideal.subset_span (by simp)
  have hIle : I ≤ J := (Ideal.span_singleton_le_iff_mem J).mpr hFJ
  have hI : I ≠ ⊤ := fun he => htop (top_le_iff.mp (he ▸ hIle))
  have hFne : F ≠ 0 := by
    intro h
    have hGun : ¬ IsUnit G := by
      intro hu
      exact htop (Ideal.eq_top_of_isUnit_mem J hGJ hu)
    apply noPrincipalOver (J := J) hfin hGun
    rw [show J = Ideal.span ({0, G} : Set Biv) by simp [J, h],
      Ideal.span_pair_comm, Ideal.span_pair_zero]
  let : UniqueFactorizationMonoid k := PrincipalIdealRing.to_uniqueFactorizationMonoid
  let : UniqueFactorizationMonoid Biv := MvPolynomial.uniqueFactorizationMonoid (Fin 2)
  have hprime : ∀ {D : Biv}, D ∣ F → D ∣ G → ¬ Prime D := by
    intro D hDF hDG hD
    apply noPrincipalOver (J := J) hfin hD.not_isUnit
    apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Ideal.mem_span_singleton.mpr hDF
    · exact Ideal.mem_span_singleton.mpr hDG
  have hreg : IsLeftRegular (Ideal.Quotient.mk I G) := by
    intro x y he
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    let q : Biv →+* Biv ⧸ I := Ideal.Quotient.mk I
    have hmul : q ((x - y) * G) = 0 := by
      rw [mul_comm, map_mul, map_sub, mul_sub]
      exact sub_eq_zero.mpr he
    have hd : F ∣ (x - y) * G :=
      Ideal.mem_span_singleton.mp ((Ideal.Quotient.eq_zero_iff_mem (I := I)).mp hmul)
    have hdiv : F ∣ x - y :=
      UniqueFactorizationMonoid.dvd_of_dvd_mul_left_of_no_prime_factors hFne @hprime hd
    have hmem : x - y ∈ I := Ideal.mem_span_singleton.mpr hdiv
    have hz : q (x - y) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [map_sub, sub_eq_zero] at hz
    exact hz
  have hd : (affineHilbertPolynomial I).natDegree = 1 := by
    have h := natDegree_affineHilbertPolynomial_span_singleton_add_one hFne hI
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
    change (affineHilbertPolynomial (Ideal.span {F})).natDegree = 1
    omega
  have hl : (affineHilbertPolynomial I).leadingCoeff = (F.totalDegree : ℚ) := by
    have he := affineDegree_span_singleton hFne
    change affineDegree I = _ at he
    simpa [affineDegree, hd] using he
  have hJ : I ⊔ Ideal.span {G} = J := by
    change Ideal.span ({F} : Set Biv) ⊔ Ideal.span {G} = Ideal.span {F, G}
    rw [← Ideal.span_union]
    congr 1
  have h := (principalCut_natDegree_affineHilbertPolynomial_le_and_coeff_le hreg hG).2
  rw [hJ, hd, hl, affineHilbertPolynomial_eq_C_finrank] at h
  have h' : (Module.finrank k (Biv ⧸ J) : ℚ) ≤
      (u : ℚ) * (F.totalDegree : ℚ) := by simpa using h
  rw [pow_two]
  have hF' : (F.totalDegree : ℚ) ≤ (u : ℚ) := by exact_mod_cast hF
  have h'' := h'.trans (mul_le_mul_of_nonneg_left hF' (Nat.cast_nonneg u))
  exact_mod_cast h''

end

end K1_14_3_2_4
end PackSource_K1_14_3_2_4Bezout

section PackSource_K1_14_3_2_4Linear
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000

namespace K1_14_3_2_4

noncomputable section

open K1_14 K1_14_3 Polynomial

/-- The shared cutter elaborates its multiplier as the inner ordinate variable. -/
theorem cutter_eq_constant (g : ClearedEquation) :
    ordinaryCutter g =
      C (liftEquation (clearedDx g) + Polynomial.X (R := Seeds) * liftEquation g.derivative) := by
  change C (liftEquation (clearedDx g)) +
    (C (Polynomial.X (R := Seeds)) : Jet) * C (liftEquation g.derivative) = _
  rw [map_add, map_mul]

private theorem constant_section_row (s : Slice) (f : Equation)
    (t : Fin 2 → SectionField[X]) (y : SectionField[X])
    (ht : ∀ i, univariate (t i) = seedValues s i)
    (hy : univariate y = ordinateValue s) :
    ∃ H : SectionField[X], sectionRow s (C f) = univariate H := by
  let e : Seeds →+* SectionField[X] :=
    MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap FX SectionField)) t
  let j : SectionSeeds →+* Plane := MvPolynomial.eval₂Hom MvPolynomial.C (seedValues s)
  have he : j.comp (MvPolynomial.map (algebraMap FX SectionField)) =
      univariate.toRingHom.comp e := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [j, e, univariate, Polynomial.aeval_def]
    · intro i
      simpa [j, e] using (ht i).symm
  refine ⟨Polynomial.eval₂RingHom e y f, ?_⟩
  have h : (sectionEval s).toRingHom.comp (sectionMap.comp Polynomial.C) =
      univariate.toRingHom.comp (Polynomial.eval₂RingHom e y) := by
    apply Polynomial.ringHom_ext
    · intro r
      simpa only [RingHom.comp_apply, sectionMap, sectionEval, coe_mapRingHom,
        map_C, coe_eval₂RingHom, eval₂_C] using RingHom.congr_fun he r
    · simpa [sectionMap, sectionEval, e] using hy.symm
  exact RingHom.congr_fun h f

private theorem seed_row (f : Equation) :
    ∃ H : SectionField[X], sectionRow .seed (C f) = univariate H := by
  refine constant_section_row .seed f ![C (parameter 2), C (parameter 3)] Polynomial.X ?_ ?_
  · intro i
    fin_cases i <;> simp [seedValues, univariate, Polynomial.aeval_def]
  · simp [ordinateValue, univariate, Polynomial.aeval_def]

private theorem ordinate_row (f : Equation) :
    ∃ H : SectionField[X], sectionRow .ordinate (C f) = univariate H := by
  refine constant_section_row .ordinate f
    ![C (parameter 2) - C (parameter 0) * Polynomial.X, Polynomial.X] (C (parameter 3)) ?_ ?_
  · intro i
    fin_cases i <;> simp [seedValues, univariate, Polynomial.aeval_def]
  · simp [ordinateValue, univariate, Polynomial.aeval_def]

/-- For the present inner-variable cutter, fixing the seeds leaves both
polynomials in the ordinate alone. A finite section is therefore empty. -/
theorem seed_length_zero (f : Equation) (g : ClearedEquation)
    (hfin : Module.Finite SectionField
      (PlaneSection (sectionRow .seed (C f)) (sectionRow .seed (ordinaryCutter g)))) :
    Module.finrank SectionField
      (PlaneSection (sectionRow .seed (C f)) (sectionRow .seed (ordinaryCutter g))) = 0 := by
  obtain ⟨F, hF⟩ := seed_row f
  rw [cutter_eq_constant] at hfin ⊢
  obtain ⟨G, hG⟩ := seed_row
    (liftEquation (clearedDx g) + Polynomial.X (R := Seeds) * liftEquation g.derivative)
  rw [hF, hG] at hfin ⊢
  exact univariate_plane_length_zero univariate.toRingHom F G hfin

/-- The ordinate slice likewise leaves the two polynomials in one free seed coordinate. -/
theorem ordinate_length_zero (f : Equation) (g : ClearedEquation)
    (hfin : Module.Finite SectionField
      (PlaneSection (sectionRow .ordinate (C f)) (sectionRow .ordinate (ordinaryCutter g)))) :
    Module.finrank SectionField
      (PlaneSection (sectionRow .ordinate (C f)) (sectionRow .ordinate (ordinaryCutter g))) = 0 := by
  obtain ⟨F, hF⟩ := ordinate_row f
  rw [cutter_eq_constant] at hfin ⊢
  obtain ⟨G, hG⟩ := ordinate_row
    (liftEquation (clearedDx g) + Polynomial.X (R := Seeds) * liftEquation g.derivative)
  rw [hF, hG] at hfin ⊢
  exact univariate_plane_length_zero univariate.toRingHom F G hfin

end

end K1_14_3_2_4
end PackSource_K1_14_3_2_4Linear

section PackSource_K1_14_3_2_4Caps
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000

namespace K1_14_3_2_4

noncomputable section

open K1_14 K1_14_3 K1_14_3_2 Polynomial

private theorem seed_degree_coeff (f : Equation) (j : ℕ) :
    (f.coeff j).totalDegree ≤ ordinarySeedDegree f := by
  by_cases h : f.coeff j = 0
  · simp [h]
  · exact Finset.le_sup (f := fun y => (f.coeff y).totalDegree) (mem_support_iff.mpr h)

private def liftSeed : ClearedSeeds →+* Seeds := MvPolynomial.map (algebraMap L[X] FX)

private theorem liftSeed_injective : Function.Injective liftSeed :=
  MvPolynomial.map_injective (algebraMap L[X] FX) (IsFractionRing.injective L[X] FX)

private theorem liftSeed_degree (A : ClearedSeeds) :
    (liftSeed A).totalDegree = A.totalDegree := by
  unfold MvPolynomial.totalDegree
  exact congrArg (fun S => S.sup fun x => x.degree)
    (MvPolynomial.support_map_of_injective A (IsFractionRing.injective L[X] FX))

private theorem liftEquation_coeff (A : ClearedEquation) (j : ℕ) :
    (liftEquation A).coeff j = liftSeed (A.coeff j) :=
  coeff_map _ _

private theorem clearing_degree {f : Equation} {g : ClearedEquation} {a : L[X]}
    (ha : IsClearing f g a) :
    g.natDegree = f.natDegree ∧ ∀ j, (g.coeff j).totalDegree ≤ ordinarySeedDegree f := by
  let c : Seeds := MvPolynomial.C (algebraMap L[X] FX a)
  have hc : c ≠ 0 := MvPolynomial.C_ne_zero.mpr (by
    simpa only [map_zero] using (IsFractionRing.injective L[X] FX).ne ha.1)
  refine ⟨?_, ?_⟩
  · rw [← natDegree_map_eq_of_injective liftSeed_injective g]
    change (liftEquation g).natDegree = _
    rw [ha.2]
    exact natDegree_C_mul hc
  · intro j
    have h := congrArg (fun E : Equation => E.coeff j) ha.2
    rw [liftEquation_coeff, coeff_C_mul] at h
    rw [← liftSeed_degree, h]
    exact (MvPolynomial.totalDegree_mul _ _).trans (by
      simpa [c] using seed_degree_coeff f j)

private theorem dx_coeff (g : ClearedEquation) (j : ℕ) :
    (clearedDx g).coeff j = ∑ e ∈ (g.coeff j).support,
      MvPolynomial.monomial e (AddMonoidAlgebra.coeff (g.coeff j) e).derivative := by
  classical
  simp only [clearedDx, sum_def, finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq']
  by_cases h : j ∈ g.support
  · simp [h]
  · simp [h, notMem_support_iff.mp h]

private theorem dx_coeff_degree (g : ClearedEquation) (j : ℕ) :
    ((clearedDx g).coeff j).totalDegree ≤ (g.coeff j).totalDegree := by
  rw [dx_coeff]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro e he
  exact (MvPolynomial.totalDegree_monomial_le _ _).trans (MvPolynomial.le_totalDegree he)

private theorem ordinateDeriv_coeff (g : ClearedEquation) (j : ℕ) :
    (Polynomial.X (R := Seeds) * liftEquation g.derivative).coeff j =
      liftSeed (g.coeff j * (j : ClearedSeeds)) := by
  cases j with
  | zero => rw [coeff_X_mul_zero, Nat.cast_zero, mul_zero, map_zero]
  | succ j =>
    rw [coeff_X_mul, liftEquation_coeff, coeff_derivative, Nat.cast_succ]

private theorem caps_constant {E : Equation} {b u : ℕ}
    (hb : E.natDegree ≤ b) (hu : ∀ y, (E.coeff y).totalDegree ≤ u) :
    RowCaps (C E) ⟨0, b, 0, u⟩ := by
  intro v y hn
  cases v with
  | zero =>
    rw [coeff_C_zero] at hn ⊢
    exact ⟨by simpa using (le_natDegree_of_ne_zero hn).trans hb, le_rfl, hu y⟩
  | succ v => rw [coeff_C_succ, coeff_zero] at hn; exact False.elim (hn rfl)

/-- Clearing and the two derivatives preserve the factor's seed and total jet caps. -/
theorem ordinaryRowCaps {f : Equation} {g : ClearedEquation} {a : L[X]}
    (ha : IsClearing f g a) :
    RowCaps (C f) ⟨0, f.natDegree, 0, ordinarySeedDegree f⟩ ∧
      RowCaps (ordinaryCutter g) ⟨0, f.natDegree, 0, ordinarySeedDegree f⟩ := by
  obtain ⟨hd, hseed⟩ := clearing_degree ha
  refine ⟨caps_constant le_rfl (seed_degree_coeff f), ?_⟩
  rw [cutter_eq_constant]
  apply caps_constant
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    have hz : g.coeff j = 0 := coeff_eq_zero_of_natDegree_lt (hd.symm ▸ hj)
    rw [coeff_add, liftEquation_coeff, ordinateDeriv_coeff, dx_coeff, hz]
    simp
  · intro j
    rw [coeff_add, liftEquation_coeff, ordinateDeriv_coeff]
    apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · rw [liftSeed_degree]
      exact (dx_coeff_degree g j).trans (hseed j)
    · rw [liftSeed_degree]
      have hz : (j : ClearedSeeds).totalDegree = 0 := by
        rw [← map_natCast (MvPolynomial.C : L[X] →+* ClearedSeeds)]
        exact MvPolynomial.totalDegree_C _
      exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa [hz] using hseed j)

end

end K1_14_3_2_4
end PackSource_K1_14_3_2_4Caps

section PackSource_K1_14_3_2_5_2Proof
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000

namespace K1_14_3_2_5_2

noncomputable section

open K1_14 K1_14_3 K1_14_3_2_5 Polynomial

/-- The slicing parameters before passage to their fraction field. -/
abbrev Parameters := MvPolynomial (Fin 4) FX

abbrev PreSeeds := MvPolynomial (Fin 2) Parameters
abbrev PreJet := Polynomial (Polynomial PreSeeds)

def preSeedBase : Seeds →+* PreSeeds :=
  MvPolynomial.map MvPolynomial.C

def preSectionMap : Jet →+* PreJet :=
  Polynomial.mapRingHom (Polynomial.mapRingHom preSeedBase)

def preParameter (i : Fin 4) : PreSeeds :=
  MvPolynomial.C (MvPolynomial.X i)

def preSeedLine : PreSeeds :=
  MvPolynomial.X 0 + preParameter 0 * MvPolynomial.X 1 - preParameter 2

def preJetLine : PreJet :=
  let y : PreJet := C (Polynomial.X (R := PreSeeds))
  let v : PreJet := Polynomial.X
  let b : PreJet := C (C (preParameter 3))
  y + (C (C (preParameter 1)) : PreJet) * v - b

def preCurveIdeal (f : Seeds) : Ideal PreSeeds :=
  Ideal.span {preSeedBase f, preSeedLine}

def preInclude : PreSeeds →+* PreJet :=
  Polynomial.C.comp Polynomial.C

def preSectionIdeal (q : Surface) : Ideal PreJet :=
  q.asIdeal.map preSectionMap ⊔ Ideal.span {preInclude preSeedLine, preJetLine}

abbrev SeedRing (q : Surface) := Seeds ⧸ seedImage q
abbrev SurfaceRing (q : Surface) := Jet ⧸ q.asIdeal

local instance (q : Surface) : (seedImage q).IsPrime := seedImage_prime q

def seedToSurface (q : Surface) : SeedRing q →+* SurfaceRing q :=
  Ideal.quotientMap q.asIdeal (C.comp C) le_rfl

theorem seedToSurface_injective (q : Surface) : Function.Injective (seedToSurface q) :=
  Ideal.quotientMap_injective

def yCoord (q : Surface) : SurfaceRing q :=
  Ideal.Quotient.mk q.asIdeal (C (Polynomial.X (R := Seeds)))

def vCoord (q : Surface) : SurfaceRing q :=
  Ideal.Quotient.mk q.asIdeal Polynomial.X

private theorem map_eval_comp {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
    (i : R →+* S) (j : S →+* A) (z : A) :
    (eval₂RingHom j z).comp (mapRingHom i) = eval₂RingHom (j.comp i) z :=
  RingHom.ext fun p => by simp [Polynomial.eval₂_map]

/-- Both coordinates being algebraic would give two distinct primes above a nonzero
seed prime, contradicting height two. -/
private theorem either_eval_injective {R A : Type*} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    (P : Ideal R) [P.IsPrime] (j : (R ⧸ P) →+* A) (hj : Function.Injective j) (y v : A)
    (hne : P ≠ ⊥) (hh : (RingHom.ker (eval₂RingHom
      (eval₂RingHom (j.comp (Ideal.Quotient.mk P)) y) v)).height = 2) :
    Function.Injective (eval₂RingHom j y) ∨ Function.Injective (eval₂RingHom j v) := by
  classical
  by_contra! h
  have relation (z : A) (hz : ¬ Function.Injective (eval₂RingHom j z)) :
      ∃ u : (R ⧸ P)[X], u ≠ 0 ∧ eval₂RingHom j z u = 0 := by
    rw [injective_iff_map_eq_zero] at hz
    push Not at hz
    obtain ⟨u, hzero, hne⟩ := hz
    exact ⟨u, hne, hzero⟩
  let m : R →+* R ⧸ P := Ideal.Quotient.mk P
  let e : R[X] →+* A := eval₂RingHom (j.comp m) y
  let d := mapRingHom (mapRingHom m)
  let g := mapRingHom e
  let Q := RingHom.ker (eval₂RingHom e v)
  let P₀ := RingHom.ker d
  let P₁ := RingHom.ker g
  have : P₀.IsPrime := RingHom.ker_isPrime d
  have : P₁.IsPrime := RingHom.ker_isPrime g
  have : Q.IsPrime := RingHom.ker_isPrime _
  have hQ : (evalRingHom v).comp g = eval₂RingHom e v := by
    simpa [g, evalRingHom] using (map_eval_comp e (RingHom.id A) v)
  have he : (eval₂RingHom j y).comp (mapRingHom m) = e := map_eval_comp m j y
  have hd : (mapRingHom (eval₂RingHom j y)).comp d = g := by
    change (mapRingHom (eval₂RingHom j y)).comp (mapRingHom (mapRingHom m)) = _
    rw [Polynomial.mapRingHom_comp, he]
  have h₀ : P₀ ≠ ⊥ := by
    obtain ⟨a, ha, haz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    intro hp
    have hm : C (C a) ∈ P₀ := by
      change d (C (C a)) = 0
      simp [d, m, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    rw [hp, Ideal.mem_bot, C_eq_zero, C_eq_zero] at hm
    exact haz hm
  have h₀₁ : P₀ < P₁ := by
    apply lt_of_le_of_ne
    · change RingHom.ker d ≤ RingHom.ker g
      rw [← hd, ← RingHom.comap_ker]
      exact Ideal.ker_le_comap d
    · intro hp
      obtain ⟨u, hu, huz⟩ := relation y h.1
      obtain ⟨w, hw⟩ := Polynomial.map_surjective m Ideal.Quotient.mk_surjective u
      have hm : C w ∈ P₁ := by
        change g (C w) = 0
        have hw' : e w = 0 := by simpa [← he, hw] using huz
        simp [g, hw']
      rw [← hp] at hm
      have hz : d (C w) = 0 := hm
      exact hu (by simpa [d, hw] using hz)
  have h₁Q : P₁ < Q := by
    apply lt_of_le_of_ne
    · change RingHom.ker g ≤ RingHom.ker (eval₂RingHom e v)
      rw [← hQ, ← RingHom.comap_ker]
      exact Ideal.ker_le_comap g
    · intro hp
      obtain ⟨u, hu, huz⟩ := relation v h.2
      obtain ⟨w, hw⟩ := Polynomial.map_surjective m Ideal.Quotient.mk_surjective u
      let z : R[X][X] := w.map C
      have hz : g z = u.map j := by
        have hc : e.comp C = j.comp m := by ext a; simp [e]
        change (w.map C).map e = _
        rw [Polynomial.map_map, hc, ← Polynomial.map_map, hw]
      have hm : z ∈ Q := by
        change eval₂RingHom e v z = 0
        rw [← hQ, RingHom.comp_apply, hz]
        simpa [Polynomial.eval_map] using huz
      rw [← hp] at hm
      have hez : g z = 0 := hm
      rw [hz] at hez
      exact hu ((Polynomial.map_eq_zero_iff hj).mp hez)
  have hP₀ : 1 ≤ P₀.height := by
    simpa using Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr h₀)
  have hP₁ : 2 ≤ P₁.height :=
    (show (1 : ℕ∞) + 1 ≤ P₀.height + 1 from add_le_add_left hP₀ 1).trans
      (Ideal.height_add_one_le_of_lt_of_isPrime h₀₁)
  have hthree : 3 ≤ Q.height :=
    (show (2 : ℕ∞) + 1 ≤ P₁.height + 1 from add_le_add_left hP₁ 1).trans
      (Ideal.height_add_one_le_of_lt_of_isPrime h₁Q)
  exact (by decide : ¬ (3 : ℕ∞) ≤ 2) (hh ▸ hthree)

/-- A height-two surface over a nonzero seed contraction has a transcendental jet coordinate. -/
theorem jetCoord_transcendental (q : Surface) (hh : q.asIdeal.height = 2)
    (hz : seedImage q ≠ ⊥) :
    Function.Injective (eval₂RingHom (seedToSurface q) (yCoord q)) ∨
    Function.Injective (eval₂RingHom (seedToSurface q) (vCoord q)) := by
  apply either_eval_injective _ _ (seedToSurface_injective q) _ _ hz
  have he : eval₂RingHom (eval₂RingHom
      ((seedToSurface q).comp (Ideal.Quotient.mk (seedImage q))) (yCoord q)) (vCoord q) =
      Ideal.Quotient.mk q.asIdeal := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext
      · intro s
        simp [seedToSurface]
      · simp [yCoord]
    · simp [vCoord]
  rw [he, Ideal.mk_ker, hh]

/-- The first variable is the offset, and the second variable is the slope. -/
def pencilCore {B A : Type*} [CommRing B] [CommRing A] (i : B →+* A) (y v : A) :
    B[X][X] →+* A[X] :=
  eval₂RingHom (eval₂RingHom (C.comp i) (C y + Polynomial.X (R := A) * C v))
    (Polynomial.X (R := A))

private theorem pencil_specialize {B A : Type*} [CommRing B] [CommRing A]
    (i : B →+* A) (y v : A) (c : B) :
    (evalRingHom (i c)).comp (pencilCore i y v) =
      (eval₂RingHom i (y + i c * v)).comp (evalRingHom (C c)) := by
  apply Polynomial.ringHom_ext
  · suffices (evalRingHom (i c)).comp
      (eval₂RingHom (C.comp i) (C y + Polynomial.X (R := A) * C v)) =
      eval₂RingHom i (y + i c * v) by
      intro p
      simpa [pencilCore, RingHom.comp_apply] using DFunLike.congr_fun this p
    apply Polynomial.ringHom_ext
    · intro b
      simp
    · simp
      exact mul_comm v (i c)
  · simp [pencilCore]

private theorem pencilCore_injective_of_specialize {B A : Type*} [CommRing B] [IsDomain B]
    [CommRing A] [IsDomain A] (i : B →+* A) (y v : A) (c : B)
    (hc : Function.Injective (eval₂RingHom i (y + i c * v))) :
    Function.Injective (pencilCore i y v) := by
  apply (injective_iff_map_eq_zero _).mpr
  have haux (n : ℕ) : ∀ p : B[X][X], p.natDegree = n → pencilCore i y v p = 0 → p = 0 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hn hp
      have hs : p.eval (C c) = 0 := by
        apply hc
        have h := DFunLike.congr_fun (pencil_specialize i y v c) p
        simpa [RingHom.comp_apply, hp] using h.symm
      obtain ⟨g, hg⟩ := (dvd_iff_isRoot).mpr hs
      have hf : pencilCore i y v (Polynomial.X (R := B[X]) - C (C c)) =
          Polynomial.X (R := A) - C (i c) := by
        simp [pencilCore]
      have hzero : pencilCore i y v g = 0 := by
        rw [hg, map_mul, hf] at hp
        exact (mul_eq_zero.mp hp).resolve_left (X_sub_C_ne_zero _)
      by_cases hg0 : g = 0
      · simp [hg, hg0]
      have hlt : g.natDegree < n := by
        rw [← hn, hg, natDegree_mul (X_sub_C_ne_zero _) hg0, natDegree_X_sub_C]
        omega
      simp [hg, ih _ hlt _ rfl hzero]
  exact fun p hp => haux _ p rfl hp

/-- A generic pencil is transcendental as soon as one of its two coordinates is. -/
theorem pencilCore_injective {B A : Type*} [CommRing B] [IsDomain B]
    [CommRing A] [IsDomain A] (i : B →+* A) (y v : A)
    (h : Function.Injective (eval₂RingHom i y) ∨ Function.Injective (eval₂RingHom i v)) :
    Function.Injective (pencilCore i y v) := by
  rcases h with hy | hv
  · exact pencilCore_injective_of_specialize i y v 0 (by simpa using hy)
  · by_cases hy : Function.Injective (eval₂RingHom i y)
    · exact pencilCore_injective_of_specialize i y v 0 (by simpa using hy)
    let : Algebra B A := i.toAlgebra
    change ¬ Function.Injective (Polynomial.aeval y : B[X] →ₐ[B] A) at hy
    change Function.Injective (Polynomial.aeval v : B[X] →ₐ[B] A) at hv
    have hay := isAlgebraic_iff_not_injective.mpr hy
    have ht : Transcendental B (y + v) := fun h =>
      (transcendental_iff_injective.mpr hv) (by simpa [add_comm y v] using h.sub hay)
    apply pencilCore_injective_of_specialize i y v 1
    rw [map_one, one_mul]
    change Function.Injective (Polynomial.aeval (y + v) : B[X] →ₐ[B] A)
    exact transcendental_iff_injective.mp ht

abbrev PreCurveModel (q : Surface) := (SeedRing q)[X][X][X]
abbrev PreSectionModel (q : Surface) := (SurfaceRing q)[X][X]

/-- The generic jet substitution, with the seed slope carried along as the last variable. -/
def pencil (q : Surface) : PreCurveModel q →+* PreSectionModel q :=
  mapRingHom (pencilCore (seedToSurface q) (yCoord q) (vCoord q))

theorem pencil_injective (q : Surface) (hh : q.asIdeal.height = 2)
    (hz : K1_14_3_2_5.seedImage q ≠ ⊥) : Function.Injective (pencil q) :=
  Polynomial.map_injective _ <|
    pencilCore_injective _ _ _ (jetCoord_transcendental q hh hz)

private def preEval {R : Type*} [CommRing R] (s : Seeds →+* R) (p : Fin 4 → R) :
    PreSeeds →+* R :=
  MvPolynomial.eval₂Hom (MvPolynomial.eval₂Hom (s.comp MvPolynomial.C) p)
    (fun i => s (MvPolynomial.X i))

private theorem preEval_comp {R T : Type*} [CommRing R] [CommRing T]
    (e : R →+* T) (s : Seeds →+* R) (p : Fin 4 → R) :
    e.comp (preEval s p) = preEval (e.comp s) (e ∘ p) := by
  simp [preEval, MvPolynomial.comp_eval₂Hom, RingHom.comp_assoc, Function.comp_def]

private theorem preEval_base {R : Type*} [CommRing R] (s : Seeds →+* R) (p : Fin 4 → R) :
    (preEval s p).comp preSeedBase = s := by
  apply MvPolynomial.ringHom_ext <;> intro x <;> simp [preEval, preSeedBase]

private def curveCoeffs (q : Surface) : Seeds →+* PreCurveModel q :=
  (C.comp (C.comp C)).comp (Ideal.Quotient.mk (seedImage q))

private def surfaceCoeffs (q : Surface) : Seeds →+* PreSectionModel q :=
  (C.comp C).comp ((Ideal.Quotient.mk q.asIdeal).comp (C.comp C))

private def curveParams (q : Surface) : Fin 4 → PreCurveModel q :=
  let α : PreCurveModel q := Polynomial.X (R := (SeedRing q)[X][X])
  let β : PreCurveModel q := C (Polynomial.X (R := (SeedRing q)[X]))
  let b : PreCurveModel q := C (C (Polynomial.X (R := SeedRing q)))
  ![α, β, curveCoeffs q (MvPolynomial.X 0) + α * curveCoeffs q (MvPolynomial.X 1), b]

private def surfaceParams (q : Surface) : Fin 4 → PreSectionModel q :=
  let α : PreSectionModel q := Polynomial.X (R := (SurfaceRing q)[X])
  let β : PreSectionModel q := C (Polynomial.X (R := SurfaceRing q))
  let b : PreSectionModel q :=
    C (C (yCoord q) + Polynomial.X (R := SurfaceRing q) * C (vCoord q))
  ![α, β, surfaceCoeffs q (MvPolynomial.X 0) + α * surfaceCoeffs q (MvPolynomial.X 1), b]

/-- Present the seed slice by eliminating the seed offset before localization. -/
def curveEval (q : Surface) : PreSeeds →+* PreCurveModel q :=
  preEval (curveCoeffs q) (curveParams q)

/-- Evaluate the surface slice by eliminating both offsets before localization. -/
def surfaceEval (q : Surface) : PreJet →+* PreSectionModel q :=
  eval₂RingHom (eval₂RingHom (preEval (surfaceCoeffs q) (surfaceParams q))
    (C (C (yCoord q)))) (C (C (vCoord q)))

/-- The seed offset substitution has no kernel beyond the seed equation and line. -/
theorem curveEval_ker_le (q : Surface) (f : Seeds) (he : seedImage q = Ideal.span {f}) :
    RingHom.ker (curveEval q) ≤ preCurveIdeal f := by
  let I := preCurveIdeal f
  let m := Ideal.Quotient.mk I
  let s : SeedRing q →+* PreSeeds ⧸ I := Ideal.Quotient.lift _ (m.comp preSeedBase) (by
    have h : seedImage q ≤ RingHom.ker (m.comp preSeedBase) := by
      rw [he]
      rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (show preSeedBase f ∈ I from Ideal.subset_span (by simp))
    exact fun _ hx => h hx)
  let inv : PreCurveModel q →+* PreSeeds ⧸ I :=
    eval₂RingHom (eval₂RingHom (eval₂RingHom s (m (preParameter 3)))
      (m (preParameter 1))) (m (preParameter 0))
  have hcoeff : inv.comp (curveCoeffs q) = m.comp preSeedBase := by
    apply RingHom.ext
    intro r
    simp [inv, curveCoeffs, s]
  have hline : m (MvPolynomial.X 0) +
      m (preParameter 0) * m (MvPolynomial.X 1) = m (preParameter 2) := by
    have h : m preSeedLine = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (show preSeedLine ∈ I from Ideal.subset_span (by simp))
    simpa [preSeedLine, sub_eq_zero] using h
  have hp : inv ∘ curveParams q = m ∘ preParameter := by
    funext i
    fin_cases i <;> simp [curveParams, Function.comp_apply, inv, curveCoeffs, s, preSeedBase]
    rw [mul_comm (m (MvPolynomial.X 1)) (m (preParameter 0)), hline]
  have hinv : inv.comp (curveEval q) = m := by
    rw [curveEval, preEval_comp, hcoeff, hp]
    apply MvPolynomial.ringHom_ext
    · intro r
      have h : MvPolynomial.eval₂Hom ((m.comp preSeedBase).comp MvPolynomial.C)
          (m ∘ preParameter) = m.comp MvPolynomial.C := by
        apply MvPolynomial.ringHom_ext <;> intro x <;> simp [preParameter, preSeedBase]
      simpa only [preEval, MvPolynomial.eval₂Hom_C, RingHom.comp_apply] using
        DFunLike.congr_fun h r
    · intro i
      simp [preEval, preSeedBase]
  intro r hr
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have h := DFunLike.congr_fun hinv r
  simpa [RingHom.mem_ker.mp hr] using h.symm

theorem preSectionIdeal_le_ker (q : Surface) :
    preSectionIdeal q ≤ RingHom.ker (surfaceEval q) := by
  apply sup_le
  · rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker]
    have he : (surfaceEval q).comp preSectionMap =
        (C.comp C).comp (Ideal.Quotient.mk q.asIdeal) := by
      apply Polynomial.ringHom_ext'
      · apply Polynomial.ringHom_ext
        · intro r
          simpa [surfaceEval, preSectionMap, surfaceCoeffs, RingHom.comp_apply] using
            DFunLike.congr_fun (preEval_base (surfaceCoeffs q) (surfaceParams q)) r
        · simp [surfaceEval, preSectionMap, yCoord]
      · simp [surfaceEval, preSectionMap, vCoord]
    rw [he]
    exact fun r hr => RingHom.mem_ker.mpr (by simp [Ideal.Quotient.eq_zero_iff_mem.mpr hr])
  · apply Ideal.span_le.mpr
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    change surfaceEval q r = 0
    rcases hr with rfl | rfl
    · simp [surfaceEval, preInclude, preSeedLine, preParameter, preEval, surfaceParams]
    · simp [surfaceEval, preJetLine, preParameter, preEval, surfaceParams]
      exact sub_eq_zero.mpr (mul_comm _ _)

theorem pencil_curveEval (q : Surface) :
    (pencil q).comp (curveEval q) = (surfaceEval q).comp preInclude := by
  have hs : (pencil q).comp (curveCoeffs q) = surfaceCoeffs q := by
    apply RingHom.ext
    intro r
    simp [pencil, pencilCore, curveCoeffs, surfaceCoeffs, seedToSurface]
  have hp : pencil q ∘ curveParams q = surfaceParams q := by
    funext i
    fin_cases i <;> simp [Function.comp_apply, pencil, pencilCore, curveParams, surfaceParams,
      surfaceCoeffs, curveCoeffs, seedToSurface]
  calc
    _ = preEval (surfaceCoeffs q) (surfaceParams q) := by rw [curveEval, preEval_comp, hs, hp]
    _ = _ := by
      apply RingHom.ext
      intro r
      simp [surfaceEval, preInclude]

section

set_option maxSynthPendingDepth 16

private theorem map_comap_localization
    {R T Rₛ Tₛ : Type*} [CommRing R] [CommRing T] [CommRing Rₛ] [CommRing Tₛ]
    [Algebra R Rₛ] [Algebra T Tₛ] (M : Submonoid R)
    (e : R →+* T) (eₛ : Rₛ →+* Tₛ)
    [IsLocalization M Rₛ] [IsLocalization (M.map e.toMonoidHom) Tₛ]
    (hcomm : ∀ x, eₛ (algebraMap R Rₛ x) = algebraMap T Tₛ (e x)) (J : Ideal T) :
    (J.comap e).map (algebraMap R Rₛ) = (J.map (algebraMap T Tₛ)).comap eₛ := by
  ext z
  obtain ⟨x, d, rfl⟩ := IsLocalization.exists_mk'_eq M z
  rw [IsLocalization.mk'_mem_map_algebraMap_iff M]
  change (∃ r ∈ M, r * x ∈ J.comap e) ↔
    eₛ (IsLocalization.mk' Rₛ x d) ∈ J.map (algebraMap T Tₛ)
  let d' : M.map e.toMonoidHom := ⟨e d, Submonoid.mem_map_of_mem e.toMonoidHom d.property⟩
  have hd : eₛ (IsLocalization.mk' Rₛ x d) = IsLocalization.mk' Tₛ (e x) d' := by
    apply (IsLocalization.eq_mk'_iff_mul_eq).mpr
    change eₛ (IsLocalization.mk' Rₛ x d) * algebraMap T Tₛ (e d) = _
    rw [← hcomm, ← map_mul, IsLocalization.mk'_spec, hcomm]
  rw [hd, IsLocalization.mk'_mem_map_algebraMap_iff (M.map e.toMonoidHom)]
  constructor
  · rintro ⟨r, hr, hx⟩
    exact ⟨e r, Submonoid.mem_map_of_mem e.toMonoidHom hr, by simpa only [Ideal.mem_comap, map_mul] using hx⟩
  · rintro ⟨_, ⟨r, hr, rfl⟩, hx⟩
    change e r * e x ∈ J at hx
    exact ⟨r, hr, Ideal.mem_comap.mpr (by rwa [map_mul])⟩

attribute [local instance] MvPolynomial.algebraMvPolynomial Polynomial.algebra
  Polynomial.isLocalization

private abbrev seedDenominators : Submonoid PreSeeds :=
  (nonZeroDivisors Parameters).map MvPolynomial.C

private def sectionInclude : SectionSeeds →+* SectionJet :=
  Polynomial.C.comp Polynomial.C

private theorem seedBase_comp :
    (MvPolynomial.map (algebraMap Parameters SectionField)).comp preSeedBase = seedBase := by
  rw [seedBase, IsScalarTower.algebraMap_eq FX Parameters SectionField]
  exact RingHom.ext (MvPolynomial.map_map MvPolynomial.C _)

private theorem curveIdeal_map (f : Seeds) :
    (preCurveIdeal f).map (algebraMap PreSeeds SectionSeeds) = curveSectionIdeal f := by
  have hb : algebraMap PreSeeds SectionSeeds (preSeedBase f) = seedBase f :=
    DFunLike.congr_fun seedBase_comp f
  have hl : algebraMap PreSeeds SectionSeeds preSeedLine = seedLine := by
    change MvPolynomial.map (algebraMap Parameters SectionField) preSeedLine = seedLine
    simp [preSeedLine, preParameter, seedLine, sectionParameter]
  simp only [preCurveIdeal, Ideal.map_span, Set.image_insert_eq, Set.image_singleton, hb, hl,
    curveSectionIdeal]

private theorem sectionIdeal_map (q : Surface) :
    (preSectionIdeal q).map (algebraMap PreJet SectionJet) = sectionIdeal q .mixed := by
  have hcomp : (algebraMap PreJet SectionJet).comp preSectionMap = sectionMap := by
    change (Polynomial.mapRingHom (Polynomial.mapRingHom
      (MvPolynomial.map (algebraMap Parameters SectionField)))).comp preSectionMap = _
    simp [preSectionMap, sectionMap, seedBase_comp, seedBase]
  have hl : algebraMap PreJet SectionJet (preInclude preSeedLine) =
      (C (C (MvPolynomial.X 0)) + sectionScalar 0 * C (C (MvPolynomial.X 1)) -
        sectionScalar 2 : SectionJet) := by
    change (Polynomial.mapRingHom (Polynomial.mapRingHom
      (MvPolynomial.map (algebraMap Parameters SectionField)))) (preInclude preSeedLine) = _
    simp [preInclude, preSeedLine, preParameter, sectionScalar]
  have hj : algebraMap PreJet SectionJet preJetLine =
      (C (Polynomial.X (R := SectionSeeds)) + sectionScalar 1 * Polynomial.X -
        sectionScalar 3 : SectionJet) := by
    change (Polynomial.mapRingHom (Polynomial.mapRingHom
      (MvPolynomial.map (algebraMap Parameters SectionField)))) preJetLine = _
    simp [preJetLine, preParameter, sectionScalar]
  simp only [preSectionIdeal, Ideal.map_sup, Ideal.map_map, Ideal.map_span,
    Set.image_insert_eq, Set.image_singleton, hcomp, hl, hj, sectionIdeal, sectionEquations]

/-- A bound on the pre-localization contraction gives injectivity over the section field. -/
theorem injective_of_preContraction (q : Surface) (f : Seeds)
    (he : seedImage q = Ideal.span {f})
    (hpre : (preSectionIdeal q).comap preInclude ≤ preCurveIdeal f) :
    Function.Injective (curveSectionMap q f he) := by
  have : IsLocalization seedDenominators SectionSeeds :=
    MvPolynomial.isLocalization (nonZeroDivisors Parameters) SectionField
  let coeffDen : Submonoid (Polynomial PreSeeds) :=
    seedDenominators.map (Polynomial.C : PreSeeds →+* Polynomial PreSeeds).toMonoidHom
  have : IsLocalization coeffDen (Polynomial SectionSeeds) :=
    Polynomial.isLocalization seedDenominators SectionSeeds
  have : IsLocalization (seedDenominators.map preInclude.toMonoidHom) SectionJet := by
    have hDen : coeffDen.map (Polynomial.C : Polynomial PreSeeds →+* PreJet).toMonoidHom =
        seedDenominators.map preInclude.toMonoidHom := by
      dsimp only [coeffDen]
      rw [Submonoid.map_map]
      rfl
    rw [← hDen]
    exact Polynomial.isLocalization coeffDen (Polynomial SectionSeeds)
  have hcomp (x : PreSeeds) :
      sectionInclude (algebraMap PreSeeds SectionSeeds x) =
        algebraMap PreJet SectionJet (preInclude x) := by
    change C (C (MvPolynomial.map (algebraMap Parameters SectionField) x)) =
      (Polynomial.mapRingHom (Polynomial.mapRingHom
        (MvPolynomial.map (algebraMap Parameters SectionField)))) (C (C x))
    simp
  have hpost := map_comap_localization seedDenominators preInclude sectionInclude hcomp
    (preSectionIdeal q)
  have hle := Ideal.map_mono (f := algebraMap PreSeeds SectionSeeds) hpre
  rw [hpost, curveIdeal_map, sectionIdeal_map] at hle
  apply (injective_iff_map_eq_zero (curveSectionMap q f he).toRingHom).mpr
  intro x hx
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change Ideal.Quotient.mk (sectionIdeal q .mixed) (sectionInclude g) = 0 at hx
  exact hle (Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp hx))

end

theorem proof : K1_14_3_2_5.c2 := by
  intro q f hh hf he
  apply injective_of_preContraction q f he
  have hz : seedImage q ≠ ⊥ := by
    rw [he, ne_eq, Ideal.span_singleton_eq_bot]
    exact hf
  intro r hr
  apply curveEval_ker_le q f he
  change curveEval q r = 0
  have hs : surfaceEval q (preInclude r) = 0 :=
    preSectionIdeal_le_ker q (show preInclude r ∈ preSectionIdeal q from hr)
  have h := DFunLike.congr_fun (pencil_curveEval q) r
  apply pencil_injective q hh hz
  simpa only [RingHom.comp_apply, hs, map_zero] using h

end

end K1_14_3_2_5_2
end PackSource_K1_14_3_2_5_2Proof

section PackSource_K1_13_2_3_2Proof
set_option autoImplicit true
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

/-- `t` is `3000 - s`, and `u` is the largest allowed target weight in the block. -/
private theorem initialFlag_at (s : Fin 4013) (j : Fin 4650) (t u : ℕ)
    (ht : t ≤ 1350) (hst : s.val + t = 3000) (hju : j.val + u + 1 = 1650 + t) :
    initialFlag (s,j) = ⟨1650, (u : ℤ) - t + 1, 1650, 550, (u : ℤ) + 1⟩ := by
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
    oldCount ⟨1650, (u : ℤ) - t + 1, 1650, 550, (u : ℤ) + 1⟩ =
      cumulative 1650 1650 - cumulative 1650 ((u : ℤ) - t) := by
  simp only [oldCount, cappedCount, Int.reduceLT, ite_false, Int.reduceAdd, Int.reduceMul]
  rw [show (u : ℤ) - t + 1 - 1 = (u : ℤ) - t by omega,
    min_eq_right (show (u : ℤ) - t ≤ 1650 by omega)]
  have hz (x : ℤ) (hx : x < 0) : cumulative (1650 - 550 - 1) x = 0 := by
    simp [cumulative, hx]
  rw [hz _ (by omega), hz _ (by omega), sub_zero, sub_zero]

private theorem target_at (t u : ℕ) (ht : t ≤ 1350) :
    targetCount ⟨1650, (u : ℤ) - t + 1, 1650, 550, (u : ℤ) + 1⟩ =
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

/-- Any cutoff gives an upper bound. Bisection chooses the cutoff for the numeric certificate. -/
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

open private twice_den denPolynomial denPrefix denPrefixPolynomial from ProximityPrize.SubmissionLower.Numeric2Aux

-- Horner forms of the two integer polynomials, with nonnegative coefficients.
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

-- Below the removed weight, targetHead is the sum of two monotone functions.
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

-- Run the inexpensive comparisons against k to check the path and its final value.
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

-- The constant denPrefixNat 1650 is subtracted once per grade.
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

-- Base-2048 digits store the cutoffs, with the last grade of the block first.
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

-- The original 20-grade equalities follow from the checked cutoffs and positive polynomial sums.

private theorem k1232_evaluate_000 :
    evaluate (fun j => gradeEstimate (1350 - (0 + j))) 20 = 80832455229384 :=
  block_of_cuts 0 20
    1355734982926145082493178244025443689529811213480835456655399550575 80832455229384
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_020 :
    evaluate (fun j => gradeEstimate (1350 - (20 + j))) 20 = 79635592691832 :=
  block_of_cuts 20 20
    1355734580995378760752571953119439156713371305631332370778539914862 79635592691832
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_040 :
    evaluate (fun j => gradeEstimate (1350 - (40 + j))) 20 = 78440393723472 :=
  block_of_cuts 40 20
    1354911828716718157731494463080982856025945120518320594855570665069 78440393723472
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_060 :
    evaluate (fun j => gradeEstimate (1350 - (60 + j))) 20 = 77247047512416 :=
  block_of_cuts 60 20
    1354088674507291232969810693030875974683599091895802052075888797292 77247047512416
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_080 :
    evaluate (fun j => gradeEstimate (1350 - (80 + j))) 20 = 76055754794496 :=
  block_of_cuts 80 20
    1353265520297864308208126917533592766614667816113482176267354857067 76055754794496
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_100 :
    evaluate (fun j => gradeEstimate (1350 - (100 + j))) 20 = 74866722453312 :=
  block_of_cuts 100 20
    1352442366088437383446443142033651102554166708585354686338260227690 74866722453312
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_120 :
    evaluate (fun j => gradeEstimate (1350 - (120 + j))) 20 = 73680164934216 :=
  block_of_cuts 120 20
    1351619211879010458661912247635955400341716674018712845258557967977 73680164934216
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_140 :
    evaluate (fun j => gradeEstimate (1350 - (140 + j))) 20 = 72496300970568 :=
  block_of_cuts 140 20
    1350795655738817212182469300135739908299783650937413115918742142567 72496300970568
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_160 :
    evaluate (fun j => gradeEstimate (1350 - (160 + j))) 20 = 71315354680920 :=
  block_of_cuts 160 20
    1349149749250729684399708040047178024344226070908789929848767460966 71315354680920
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_180 :
    evaluate (fun j => gradeEstimate (1350 - (180 + j))) 20 = 70137564602976 :=
  block_of_cuts 180 20
    1348326595041206931875820633004281788858880029644400541830850225764 70137564602976
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_200 :
    evaluate (fun j => gradeEstimate (1350 - (200 + j))) 20 = 68963160075144 :=
  block_of_cuts 200 20
    1346680286622448910114656713552668646071647778109115555678522646115 68963160075144
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_220 :
    evaluate (fun j => gradeEstimate (1350 - (220 + j))) 20 = 67792386793464 :=
  block_of_cuts 220 20
    1345033978203595060591289162560761984633394992111305251554449362529 67792386793464
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_240 :
    evaluate (fun j => gradeEstimate (1350 - (240 + j))) 20 = 66625491000888 :=
  block_of_cuts 240 20
    1344210823797912878836567981647997329038983924040052080635989392991 66625491000888
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_260 :
    evaluate (fun j => gradeEstimate (1350 - (260 + j))) 20 = 65462720303784 :=
  block_of_cuts 260 20
    1342564515379059029313200430653430912901121372475412329018921512541 65462720303784
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_280 :
    evaluate (fun j => gradeEstimate (1350 - (280 + j))) 20 = 64304328567000 :=
  block_of_cuts 280 20
    1340918206960205179789832879658864496762949335900951232333128851035 64304328567000
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_300 :
    evaluate (fun j => gradeEstimate (1350 - (300 + j))) 20 = 63150570148488 :=
  block_of_cuts 300 20
    1338448744528179662497818958582495021373904852031724411713739736664 63150570148488
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_320 :
    evaluate (fun j => gradeEstimate (1350 - (320 + j))) 20 = 62001702709200 :=
  block_of_cuts 320 20
    1336802436109325812974440251768153013197886285448110956489271850582 62001702709200
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_340 :
    evaluate (fun j => gradeEstimate (1350 - (340 + j))) 20 = 60857989332096 :=
  block_of_cuts 340 20
    1335156127494216706458046451177882039646605105310597400925039664723 60857989332096
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_360 :
    evaluate (fun j => gradeEstimate (1350 - (360 + j))) 20 = 59719686384336 :=
  block_of_cuts 360 20
    1332686665062191189143185411198441614756297330951532678969639997009 59719686384336
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_380 :
    evaluate (fun j => gradeEstimate (1350 - (380 + j))) 20 = 58587059139312 :=
  block_of_cuts 380 20
    1330217202433910414880981198162486613958006847048688274201753318990 58587059139312
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_400 :
    evaluate (fun j => gradeEstimate (1350 - (400 + j))) 20 = 57460370517984 :=
  block_of_cuts 400 20
    1328570492084290243617007361706433535738719803048575184413136150091 57460370517984
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_420 :
    evaluate (fun j => gradeEstimate (1350 - (420 + j))) 20 = 56339882531856 :=
  block_of_cuts 420 20
    1326101029456009469331956035214583911531925975701579528190515365448 56339882531856
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_440 :
    evaluate (fun j => gradeEstimate (1350 - (440 + j))) 20 = 55225858815408 :=
  block_of_cuts 440 20
    1322808814549068092025827218686937741337625364934022415630109650500 55225858815408
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_460 :
    evaluate (fun j => gradeEstimate (1350 - (460 + j))) 20 = 54118560065088 :=
  block_of_cuts 460 20
    1320339351920787317717928778739193493722018558091185744944255077953 54118560065088
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_480 :
    evaluate (fun j => gradeEstimate (1350 - (480 + j))) 20 = 53018250987240 :=
  block_of_cuts 480 20
    1317869889096251286462687165732274916133263848429129215803384788541 53018250987240
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_500 :
    evaluate (fun j => gradeEstimate (1350 - (500 + j))) 20 = 51925188079944 :=
  block_of_cuts 500 20
    1314577272454798844386142350258211036605674327500831913527575959098 51925188079944
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_520 :
    evaluate (fun j => gradeEstimate (1350 - (520 + j))) 20 = 50839633362096 :=
  block_of_cuts 520 20
    1312107407895751748383331846316251503625078720798633492413657757238 50839633362096
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_540 :
    evaluate (fun j => gradeEstimate (1350 - (540 + j))) 20 = 49761840927024 :=
  block_of_cuts 540 20
    1308815192792555114084165629817641756640004248220102434877730821682 49761840927024
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_560 :
    evaluate (fun j => gradeEstimate (1350 - (560 + j))) 20 = 48692065869432 :=
  block_of_cuts 560 20
    1305522575954847415037430527828508924364279145090822931643595060782 48692065869432
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_580 :
    evaluate (fun j => gradeEstimate (1350 - (580 + j))) 20 = 47630560454832 :=
  block_of_cuts 580 20
    1302229959117139715990684275466776826776673789092585759151391594026 47630560454832
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_600 :
    evaluate (fun j => gradeEstimate (1350 - (600 + j))) 20 = 46577573150784 :=
  block_of_cuts 600 20
    1298114188266260349152466840312546875227048811854398350967692146213 46577573150784
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_620 :
    evaluate (fun j => gradeEstimate (1350 - (620 + j))) 20 = 45533347926264 :=
  block_of_cuts 620 20
    1294821571428456822366375225678213509678427550837856872671856365089 45533347926264
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_640 :
    evaluate (fun j => gradeEstimate (1350 - (640 + j))) 20 = 44498129823840 :=
  block_of_cuts 640 20
    1291528552660078629318390345428275379784944064039429125998478681628 44498129823840
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_660 :
    evaluate (fun j => gradeEstimate (1350 - (660 + j))) 20 = 43472154839544 :=
  block_of_cuts 660 20
    1287413183347455070280376316515679080902085524896677247460224056855 43472154839544
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_680 :
    evaluate (fun j => gradeEstimate (1350 - (680 + j))) 20 = 42455658222000 :=
  block_of_cuts 680 20
    1283297412496479875702802363271730725978064789461563529783178993170 42455658222000
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_700 :
    evaluate (fun j => gradeEstimate (1350 - (700 + j))) 20 = 41448869045472 :=
  block_of_cuts 700 20
    1279181641449345251894372335412715419688012342576677097014385733133 41448869045472
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_720 :
    evaluate (fun j => gradeEstimate (1350 - (720 + j))) 20 = 40452013687080 :=
  block_of_cuts 720 20
    1275065870206051198855119684056430959868116388088092134037372552712 40452013687080
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_740 :
    evaluate (fun j => gradeEstimate (1350 - (740 + j))) 20 = 39465313582800 :=
  block_of_cuts 740 20
    1270949697424405463508243563404643339552177539625053559542648937986 39465313582800
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_760 :
    evaluate (fun j => gradeEstimate (1350 - (760 + j))) 20 = 38488981885344 :=
  block_of_cuts 760 20
    1266011174098514455707431927456184090585111930059559084077838495229 38488981885344
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_780 :
    evaluate (fun j => gradeEstimate (1350 - (780 + j))) 20 = 37523232286272 :=
  block_of_cuts 780 20
    1261895001120709291129722032934528050793624021009713562987864767991 37523232286272
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_800 :
    evaluate (fun j => gradeEstimate (1350 - (800 + j))) 20 = 36568268216736 :=
  block_of_cuts 800 20
    1256956477598658854075240660030245270188911128797420727893436110321 36568268216736
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_820 :
    evaluate (fun j => gradeEstimate (1350 - (820 + j))) 20 = 35624289073704 :=
  block_of_cuts 820 20
    1252017552342097305505138007049204477766893305849309087162793156075 35624289073704
    (by decide +kernel) (by decide +kernel)

private theorem k1232_evaluate_840 :
    evaluate (fun j => gradeEstimate (1350 - (840 + j))) 20 = 34691489395248 :=
  block_of_cuts 840 20
    1247078627085535756935035354062846773361426334399760873122304044517 34691489395248
    (by decide +kernel) (by decide +kernel)

end
private theorem evaluate_check : evaluate (fun j => gradeEstimate (1350 - j)) 860 = 2443983978793296 := by
  have h000 : evaluate (fun j => gradeEstimate (1350 - j)) 0 = 0 := rfl
  have h020 : evaluate (fun j => gradeEstimate (1350 - j)) 20 = 80832455229384 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h000 k1232_evaluate_000 rfl rfl
  have h040 : evaluate (fun j => gradeEstimate (1350 - j)) 40 = 160468047921216 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h020 k1232_evaluate_020 rfl rfl
  have h060 : evaluate (fun j => gradeEstimate (1350 - j)) 60 = 238908441644688 :=
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
  have h280 : evaluate (fun j => gradeEstimate (1350 - j)) 280 = 1023551109766872 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h260 k1232_evaluate_260 rfl rfl
  have h300 : evaluate (fun j => gradeEstimate (1350 - j)) 300 = 1087855438333872 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h280 k1232_evaluate_280 rfl rfl
  have h320 : evaluate (fun j => gradeEstimate (1350 - j)) 320 = 1151006008482360 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h300 k1232_evaluate_300 rfl rfl
  have h340 : evaluate (fun j => gradeEstimate (1350 - j)) 340 = 1213007711191560 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h320 k1232_evaluate_320 rfl rfl
  have h360 : evaluate (fun j => gradeEstimate (1350 - j)) 360 = 1273865700523656 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h340 k1232_evaluate_340 rfl rfl
  have h380 : evaluate (fun j => gradeEstimate (1350 - j)) 380 = 1333585386907992 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h360 k1232_evaluate_360 rfl rfl
  have h400 : evaluate (fun j => gradeEstimate (1350 - j)) 400 = 1392172446047304 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h380 k1232_evaluate_380 rfl rfl
  have h420 : evaluate (fun j => gradeEstimate (1350 - j)) 420 = 1449632816565288 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h400 k1232_evaluate_400 rfl rfl
  have h440 : evaluate (fun j => gradeEstimate (1350 - j)) 440 = 1505972699097144 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h420 k1232_evaluate_420 rfl rfl
  have h460 : evaluate (fun j => gradeEstimate (1350 - j)) 460 = 1561198557912552 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h440 k1232_evaluate_440 rfl rfl
  have h480 : evaluate (fun j => gradeEstimate (1350 - j)) 480 = 1615317117977640 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h460 k1232_evaluate_460 rfl rfl
  have h500 : evaluate (fun j => gradeEstimate (1350 - j)) 500 = 1668335368964880 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h480 k1232_evaluate_480 rfl rfl
  have h520 : evaluate (fun j => gradeEstimate (1350 - j)) 520 = 1720260557044824 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h500 k1232_evaluate_500 rfl rfl
  have h540 : evaluate (fun j => gradeEstimate (1350 - j)) 540 = 1771100190406920 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h520 k1232_evaluate_520 rfl rfl
  have h560 : evaluate (fun j => gradeEstimate (1350 - j)) 560 = 1820862031333944 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h540 k1232_evaluate_540 rfl rfl
  have h580 : evaluate (fun j => gradeEstimate (1350 - j)) 580 = 1869554097203376 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h560 k1232_evaluate_560 rfl rfl
  have h600 : evaluate (fun j => gradeEstimate (1350 - j)) 600 = 1917184657658208 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h580 k1232_evaluate_580 rfl rfl
  have h620 : evaluate (fun j => gradeEstimate (1350 - j)) 620 = 1963762230808992 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h600 k1232_evaluate_600 rfl rfl
  have h640 : evaluate (fun j => gradeEstimate (1350 - j)) 640 = 2009295578735256 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h620 k1232_evaluate_620 rfl rfl
  have h660 : evaluate (fun j => gradeEstimate (1350 - j)) 660 = 2053793708559096 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h640 k1232_evaluate_640 rfl rfl
  have h680 : evaluate (fun j => gradeEstimate (1350 - j)) 680 = 2097265863398640 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h660 k1232_evaluate_660 rfl rfl
  have h700 : evaluate (fun j => gradeEstimate (1350 - j)) 700 = 2139721521620640 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h680 k1232_evaluate_680 rfl rfl
  have h720 : evaluate (fun j => gradeEstimate (1350 - j)) 720 = 2181170390666112 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h700 k1232_evaluate_700 rfl rfl
  have h740 : evaluate (fun j => gradeEstimate (1350 - j)) 740 = 2221622404353192 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h720 k1232_evaluate_720 rfl rfl
  have h760 : evaluate (fun j => gradeEstimate (1350 - j)) 760 = 2261087717935992 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h740 k1232_evaluate_740 rfl rfl
  have h780 : evaluate (fun j => gradeEstimate (1350 - j)) 780 = 2299576699821336 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h760 k1232_evaluate_760 rfl rfl
  have h800 : evaluate (fun j => gradeEstimate (1350 - j)) 800 = 2337099932107608 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h780 k1232_evaluate_780 rfl rfl
  have h820 : evaluate (fun j => gradeEstimate (1350 - j)) 820 = 2373668200324344 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h800 k1232_evaluate_800 rfl rfl
  have h840 : evaluate (fun j => gradeEstimate (1350 - j)) 840 = 2409292489398048 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h820 k1232_evaluate_820 rfl rfl
  have h860 : evaluate (fun j => gradeEstimate (1350 - j)) 860 = 2443983978793296 :=
    k1232_join_evaluations (f := (fun j => gradeEstimate (1350 - j))) h840 k1232_evaluate_840 rfl rfl
  exact h860

private theorem scaled_bound : 24 * (baselineSum 1650 2510 : ℤ) ≤ 2443983978793296 := by
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
end PackSource_K1_13_2_3_2Proof

section PackSource_K1_10Defs
set_option autoImplicit true
namespace K1_10
noncomputable section

open K1 Polynomial

/-- Coefficients of the first column as a pencil in T. The second amplitude in
the parent record is stored before the coefficient Frobenius. -/
def leftCoeff {u T R D} (B : RankThree u T R D) (l : Fin 2) : K[X] :=
  B.a * (B.β l).map twist

/-- Coefficients of the second column as a pencil in S. -/
def rightCoeff {u T R D} (B : RankThree u T R D) (j : Fin 2) : K[X] :=
  -(B.b * B.α j)

def planeNodes (d : ℕ) (u : Words) (deleted : Finset I) (U V : Fin 2 → K[X])
    (O : Fin 2 → Fin 2 → K[X]) : Prop :=
  ∀ i ∉ deleted, ∀ j l, (U l).eval (node i) * u j i + (V j).eval (node i) * (u l i)^d =
    (O j l).eval (node i)

/-- The coefficient of S^j T^l in the node identity is output j l.
Together U and V describe U₀+T U₁ and V₀+S V₁. -/
structure Plane (u : Words) (deleted : Finset I) (h : ℕ) (U V : Fin 2 → K[X]) where
  output : Fin 2 → Fin 2 → K[X]
  U_ne : ∃ l, U l ≠ 0
  V_ne : ∃ j, V j ≠ 0
  height_eq : max (amplitudeDegree (U 0) (U 1)) (amplitudeDegree (V 0) (V 1)) = h
  primitive : ∀ f : K[X], (∀ l, f ∣ U l) → (∀ j, f ∣ V j) → IsUnit f
  output_degree : ∀ j l, (output j l).degree < (131072 + h : ℕ)
  nodes : planeNodes p u deleted U V output

/-- The uncancelled adjugate identities hold even at zeros of the multiplier. -/
structure Adjugate (u : Words) (deleted : Finset I) (h : ℕ) where
  denom : K[X]
  nonzero : denom ≠ 0
  denom_degree : denom.natDegree ≤ 2 * h
  numer : Fin 2 → K[X]
  numer_degree : ∀ j, (numer j).degree < (131072 + 2 * h : ℕ)
  nodes : ∀ i ∉ deleted, ∀ j, denom.eval (node i) * u j i = (numer j).eval (node i)

abbrev SeedPoly := MvPolynomial (Fin 2) K

/-- Outer coordinates X,Y and inner coordinates S,T. The degree in X is
unrestricted after elimination. -/
structure ScalarSource where
  poly : MvPolynomial (Fin 2) SeedPoly
  nonzero : poly ≠ 0
  y_degree : poly.degreeOf 1 ≤ 5
  s_degree : ∀ e ∈ poly.support, (poly.coeff e).degreeOf 0 ≤ 26
  t_degree : ∀ e ∈ poly.support, (poly.coeff e).degreeOf 1 ≤ 21
  total : ∀ e ∈ poly.support, e 1 + (poly.coeff e).totalDegree ≤ 37

def ScalarSource.atLabel (A : ScalarSource) (γ : K) : MvPolynomial (Fin 2) K :=
  A.poly.map (MvPolynomial.eval ![γ, γ ^ p])

def ScalarSource.atDecoder (A : ScalarSource) (γ : K) (P : K[X]) : K[X] :=
  MvPolynomial.aeval ![Polynomial.X, P] (A.atLabel γ)

/-- Monomials with X + 131071(Y₀+Y₁) weight at most d, message degree
at most b, and bounds s,t on (S+Y₀,T+Y₁). -/
def sourceDim (d b s t : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (b + 1), ∑ j ∈ Finset.range (b + 1 - i),
    (d + 1 - 131071 * (i+j)) * (s+1-i) * (t+1-j)

/-- Local jets in X,Y₀,Y₁ of order less than m, with the two seed bounds. -/
def jetDim (m s t : ℕ) : ℕ :=
  ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range (m-i), (m-i-j) * (s+1-i) * (t+1-j)

def quotientSurplus (n h : ℕ) : Prop :=
  n * (jetDim 4 16 16 - jetDim 3 15 15) <
    sourceDim 721059 5 16 16 - sourceDim (721059 - 131071 - h) 4 15 15

/-- Degree of the proper node cut and the original-domain incidence ratio. -/
def regularPrice : ℕ :=
  ⌈(5 * 37 : ℚ) * (((262144 - 131071 : ℚ) / (180265 - 131071)) *
    ((2 * 131071 - 1) * (37 - 1) + 1)) ^ 2⌉₊

end
end K1_10
end PackSource_K1_10Defs

section PackSource_K1_10_1Defs
set_option autoImplicit true
set_option autoImplicit false

namespace K1_10_1
noncomputable section

open K1 K1_11 MvPolynomial

def relationBounds (h : ℕ) : Fin 4 → ℕ := ![131071 + h, 1, 1, 1]

/-- Put the ordinary X polynomial in coordinate zero of the retained ring. -/
def liftOrdinary : Polynomial K →+* MvPolynomial (Fin 4) K :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)

def pencil (A : Fin 2 → Polynomial K) (z : MvPolynomial (Fin 4) K) :
    MvPolynomial (Fin 4) K :=
  liftOrdinary (A 0) + z * liftOrdinary (A 1)

/-- The retained coordinates are X,Y₀,S,T, in that order. -/
def denominator (V : Fin 2 → Polynomial K) : MvPolynomial (Fin 4) K :=
  pencil V (MvPolynomial.X 2)

def numerator (U : Fin 2 → Polynomial K) (O : Fin 2 → Fin 2 → Polynomial K) :
    MvPolynomial (Fin 4) K :=
  pencil (fun j => O j 0) (MvPolynomial.X 2) + MvPolynomial.X 3 * pencil (fun j => O j 1) (MvPolynomial.X 2) -
    pencil U (MvPolynomial.X 3) * MvPolynomial.X 1

/-- The five-coordinate relation U(T)Y₀ + V(S)Y₁ − O(S,T). -/
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
end PackSource_K1_10_1Defs

section PackSource_K1_10_1Quotient
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace K1_10_1
noncomputable section

open MvPolynomial K1_11

private theorem exists_kernel_outside {F E G : Type*} [Field F]
    [AddCommGroup E] [Module F E] [Module.Finite F E]
    [AddCommGroup G] [Module F G] [Module.Finite F G]
    (f : E →ₗ[F] G) (R : Submodule F E)
    (hdim : Module.finrank F G + Module.finrank F R < Module.finrank F E) :
    ∃ q : E, f q = 0 ∧ q ∉ R := by
  by_contra hn
  have hle : LinearMap.ker f ≤ R := by
    intro q hq
    by_contra hnot
    exact hn ⟨q, LinearMap.mem_ker.mp hq, hnot⟩
  have hk := Submodule.finrank_mono hle
  have hf := LinearMap.finrank_range_add_finrank_ker f
  have hr := (LinearMap.range f).finrank_le
  omega

abbrev Source (F : Type*) [Field F] :=
  filtered (F := F) (sourceWeights 131071) (sourceBounds 721059 5 16 16)

abbrev Multipliers (F : Type*) [Field F] := JetSpace F 2 15 15

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

private def localMultiply (i : Fin N) : Multipliers F →ₗ[F] JetSpace F 3 16 16 where
  toFun Q := ⟨weightedTruncation contactWeight 4 (C.shifted i L * Q.val), by
    apply truncated_mul_mem_jet 2 15 15 1 1
    · exact (contactShift_parameter_weights _ _ _ _ _ L).1.trans (le_of_eq (hdeg 2))
    · exact (contactShift_parameter_weights _ _ _ _ _ L).2.trans (le_of_eq (hdeg 3))⟩
  map_add' Q R := by apply Subtype.ext; simp [mul_add]
  map_smul' a Q := by apply Subtype.ext; simp

private abbrev LocalSpace (i : Fin N) :=
  (JetSpace F 3 16 16) ⧸ LinearMap.range (localMultiply C hdeg i)

private theorem local_finrank (i : Fin N) :
    Module.finrank F (LocalSpace C hdeg i) = J 4 16 16 - J 3 15 15 := by
  have hinj : Function.Injective (localMultiply C hdeg i) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro Q hQ
    by_contra hn
    have hprod : weightedTruncation contactWeight 4 (C.shifted i L * Q.val) = 0 :=
      congrArg (fun x : JetSpace F 3 16 16 => x.val) hQ
    have horder := C.order_one i
    change (contactLift contactWeight (C.shifted i L)).natTrailingDegree = 1 at horder
    have hL : C.shifted i L ≠ 0 := by
      intro hz
      simp [hz] at horder
    exact contact_product_not_high_order contactWeight 4 (C.shifted i L) Q.val
      horder hL (fun hz => hn (Subtype.ext hz)) (jetSpace_support_bound _ _ _ Q)
      ((weightedTruncation_eq_zero_iff _ _ _).mp hprod)
  have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range (localMultiply C hdeg i))
  rw [LinearMap.finrank_range_of_inj hinj, jetSpace_finrank, jetSpace_finrank] at hq
  change Module.finrank F (LocalSpace C hdeg i) + J 3 15 15 = J 4 16 16 at hq
  omega

private def nodeMap (i : Fin N) : Source F →ₗ[F] LocalSpace C hdeg i :=
  (LinearMap.range (localMultiply C hdeg i)).mkQ.comp
    (sourceToJet 721059 131071 5 16 16 3 (C.x i) (C.first i) (C.firstSlope i)
      (C.second i) (C.secondSlope i))

include hdeg in
theorem quotientSource (hL : L ≠ 0) (hh : h ≤ 32670) (hs : K1_10.quotientSurplus N h) :
    ∃ G : Source F, ¬ L ∣ G.val ∧ ∀ i, ∃ R : Multipliers F,
      C.shifted i G.val - C.shifted i L * R.val ∈ restrictWeightedOrder contactWeight 4 := by
  have hfit : ∀ j, relationBounds h j ≤ sourceBounds 721059 5 16 16 j := by
    intro j
    fin_cases j <;> simp [relationBounds, sourceBounds] <;> omega
  have hshift : (fun j => sourceBounds 721059 5 16 16 j - relationBounds h j) =
      sourceBounds (721059 - 131071 - h) 4 15 15 := by
    funext j
    fin_cases j <;> simp [sourceBounds, relationBounds] <;> omega
  let mult := filteredMul (sourceWeights 131071) (sourceBounds 721059 5 16 16)
    (relationBounds h) L hL hdeg hfit
  have hmult : Module.finrank F (LinearMap.range mult) =
      V (721059 - 131071 - h) 131071 4 15 15 := by
    rw [LinearMap.finrank_range_of_inj (filteredMul_injective _ _ _ L hL hdeg hfit),
      hshift, source_filtered_finrank]
  letI (i : Fin N) : Module.Free F (LocalSpace C hdeg i) := Module.Free.of_divisionRing F _
  letI : Module F (∀ i : Fin N, LocalSpace C hdeg i) := Pi.module _ _ _
  have hlocal : Module.finrank F (∀ i : Fin N, LocalSpace C hdeg i) =
      N * (J 4 16 16 - J 3 15 15) := by
    rw [Module.finrank_pi_fintype]
    simp only [local_finrank C hdeg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hdim : Module.finrank F (∀ i : Fin N, LocalSpace C hdeg i) +
      Module.finrank F (LinearMap.range mult) < Module.finrank F (Source F) := by
    rw [hlocal, hmult, source_filtered_finrank]
    change N * (J 4 16 16 - J 3 15 15) <
      V 721059 131071 5 16 16 - V (721059 - 131071 - h) 131071 4 15 15 at hs
    omega
  obtain ⟨G, hG, hnot⟩ := exists_kernel_outside (G := ∀ i : Fin N, LocalSpace C hdeg i)
    (LinearMap.pi (nodeMap C hdeg)) (LinearMap.range mult) hdim
  refine ⟨G, (mem_filteredMul_range_iff _ _ _ L hL hdeg hfit G).not.mp hnot, ?_⟩
  intro i
  have hi : nodeMap C hdeg i G = 0 := congrFun hG i
  obtain ⟨R, hR⟩ := (Submodule.Quotient.mk_eq_zero _).mp hi
  refine ⟨R, (weightedTruncation_eq_zero_iff _ _ _).mp ?_⟩
  rw [map_sub]
  exact sub_eq_zero.mpr (congrArg Subtype.val hR).symm

end
end K1_10_1
end PackSource_K1_10_1Quotient

section PackSource_K1_10Height
set_option autoImplicit true
namespace K1_10
noncomputable section

open K1 FrobeniusLocator ProximityPrize.Benchmark Polynomial

theorem height_balance {u : Words} (T : TwoActive u) {R : Relation T} (D : Reduction u T R) :
    D.height + (fixedNodes R).card + nullity u = 32687 := by
  have h := D.height_eq
  unfold TwoActive.height at h
  have := T.degreeSum
  have := T.nullitySum
  have := T.top
  omega

theorem mark_disjoint {u : Words} {T : TwoActive u} {R : Relation T} (D : Reduction u T R)
    {γ : K} (hn : Normal u γ) (M : BadMark u γ) :
    Disjoint M.support (fixedNodes R) := by
  apply Finset.disjoint_left.mpr
  intro i hi hfix
  exact D.deleted_error γ hn M i hfix (M.hits i hi)

private theorem natDegree_lt_of_degree_lt_pos {P : K[X]} {m : ℕ} (hm : 0 < m)
    (h : P.degree < m) : P.natDegree < m := by
  by_cases hP : P = 0
  · simpa [hP] using hm
  · exact (natDegree_lt_iff_degree_lt hP).mpr h

/-- If the adjugate has overhead below A-k, agreement makes its cleared
decoder identity global. All errors lie on the fixed puncture or the zeros
of the multiplier, too few columns for a normal stacked matrix. -/
theorem no_small_normal {u : Words} (T : TwoActive u) {R : Relation T}
    (D : Reduction u T R) (J : Adjugate u (fixedNodes R) D.height)
    (hsmall : 2 * D.height < 49193) {γ : K} (hn : Normal u γ) (M : BadMark u γ) : False := by
  classical
  let F := J.numer 0 + C γ * J.numer 1 - J.denom * M.decoder
  have hdeg : F.natDegree < 180265 := by
    have hj (j : Fin 2) := natDegree_lt_of_degree_lt_pos (by omega) (J.numer_degree j)
    have hP : M.decoder.natDegree < 131072 := natDegree_lt_of_degree_lt_pos (by decide) M.degree
    have hnum := (natDegree_add_le (J.numer 0) (C γ * J.numer 1)).trans
      (max_le_max_left _ (natDegree_C_mul_le γ (J.numer 1)))
    have hprod := natDegree_mul_le (p := J.denom) (q := M.decoder)
    have hsub := natDegree_sub_le (J.numer 0 + C γ * J.numer 1) (J.denom * M.decoder)
    change (J.numer 0 + C γ * J.numer 1 - J.denom * M.decoder).natDegree < 180265
    have := J.denom_degree
    apply hsub.trans_lt
    apply max_lt
    · exact hnum.trans_lt (max_lt (by have := hj 0; omega) (by have := hj 1; omega))
    · exact hprod.trans_lt (by omega)
  have hF : F = 0 := by
    by_contra hf
    have hroot := Strata.root_nodes_card_le node IRSProfile.domain.injective F hf M.support
      (by
        intro i hi
        have hd : i ∉ fixedNodes R := fun h => (Finset.disjoint_left.mp (mark_disjoint D hn M)) hi h
        simp only [F, eval_sub, eval_add, eval_mul, eval_C, ← J.nodes i hd, M.hits i hi]
        ring)
    have := M.agreement
    omega
  let zeros := Finset.univ.filter (fun i : I => J.denom.eval (node i) = 0)
  let E := fixedNodes R ∪ zeros
  have hZ : zeros.card ≤ J.denom.natDegree := Strata.root_nodes_card_le node
    IRSProfile.domain.injective _ J.nonzero zeros (fun _ hi => (Finset.mem_filter.mp hi).2)
  have hE : E.card ≤ (fixedNodes R).card + 2 * D.height := (Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (hZ.trans J.denom_degree) _)
  have hoff (i : I) (hi : i ∉ E) : u 0 i + γ * u 1 i = M.decoder.eval (node i) := by
    have hd : i ∉ fixedNodes R := fun h => hi (Finset.mem_union_left _ h)
    have hz : J.denom.eval (node i) ≠ 0 :=
      fun h => hi (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    have hf : F.eval (node i) = 0 := by rw [hF, eval_zero]
    simp only [F, eval_sub, eval_add, eval_mul, eval_C, ← J.nodes i hd] at hf
    apply mul_left_cancel₀ hz
    linear_combination hf
  have hbal := height_balance T D
  have hs := actual_stackRank u
  have hcard : 131072 + 49193 + 81879 ≤ Fintype.card I := by rw [IRSProfile.card_index]
  have hfix (b : Fin 2) (i : I) : iterateFrobenius K p b.val (node i) = node i := by
    fin_cases b
    · exact iterateFrobenius_zero_apply K p _
    · exact (iterateFrobenius_one_apply K p _).trans (Native.native_domain_fixed i)
  change ((stacked p node (u 0) (u 1) 49193 81879).map (evalRingHom γ)).rank = stackRank u at hn
  rw [Strata.stacked_eq_frobeniusStacked, Strata.frobeniusStacked_eval,
    Strata.conjugateHankel_error_rank _ node _ IRSProfile.domain.injective hfix M.decoder
      131072 49193 81879 M.degree hcard E (by omega) hoff] at hn
  have hr := Matrix.rank_le_card_width (Strata.conjugateErrors
    (fun b : Fin 2 => iterateFrobenius K p b.val) (fun i : E => node i.val)
    (fun i : E => u 0 i.val + γ * u 1 i.val - M.decoder.eval (node i.val)) 49193)
  rw [Fintype.card_coe, hn] at hr
  omega

end
end K1_10
end PackSource_K1_10Height

section PackSource_K1_10Plane
set_option autoImplicit true
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false

namespace K1_10
noncomputable section
open K1 Polynomial FrobeniusLocator

-- Use the same finite-field instances in the two native power expressions.
-- This keeps kernel conversion from expanding a polynomial power of 2130706433.
attribute [local instance 2500] K1.Frac._proof_1 K1.ordinary._proof_1
local notation "KS" => @CommSemiring.toSemiring K
  (@Semifield.toCommSemiring K (@Field.toSemifield K
    (@CompPoly.Extension.Ext.instField KoalaBear.Field KoalaBear.instFieldField KoalaBear.ext6Params
      K1.Frac._proof_1 KoalaBear.instFactEqNatCardFieldQExt6Params
      KoalaBear.instFactIrreduciblePolynomialFieldPolyExt6Params)))

private def column (n : ℕ) (f : Fin 2 → K[X]) : Bivar :=
  liftX (f 0) + liftX (f 1) * C (Polynomial.X ^ n)

private theorem column_ne {n : ℕ} (hn : n ≠ 0) {f : Fin 2 → K[X]}
    (hf : ∃ j, f j ≠ 0) : column n f ≠ 0 := by
  intro hz
  have h := congrArg Polynomial.Bivariate.swap hz
  simp only [column, liftX, map_add, map_mul, Bivariate.swap_map_C, Bivariate.swap_C,
    Polynomial.map_pow, Polynomial.map_X, map_zero] at h
  have hcoeff (i : ℕ) := congrArg (fun q : Bivar => q.coeff i) h
  have h0 : f 0 = 0 := by simpa [coeff_C_mul_X_pow, Ne.symm hn] using hcoeff 0
  have h1 : f 1 = 0 := by simpa [coeff_C_mul_X_pow, coeff_C, hn] using hcoeff n
  obtain ⟨j,hj⟩ := hf
  fin_cases j
  · exact hj h0
  · exact hj h1

private theorem column_bound (n : ℕ) (f : Fin 2 → K[X]) :
    (column n f).natDegree ≤ amplitudeDegree (f 0) (f 1) :=
  (natDegree_add_le _ _).trans (max_le_max natDegree_map_le
    ((natDegree_mul_C_le _ _).trans natDegree_map_le))

private theorem column_dvd (n : ℕ) (f : Fin 2 → K[X]) (q : K[X])
    (hd : ∀ j, q ∣ f j) : liftX q ∣ column n f :=
  dvd_add ((Polynomial.mapRingHom Polynomial.C).map_dvd (hd 0))
    ((((Polynomial.mapRingHom Polynomial.C).map_dvd (hd 1))).mul_right _)

private theorem column_mul (a : K[X]) (n : ℕ) (f : Fin 2 → K[X]) :
    liftX a * (liftX (f 0) + seed ^ n * liftX (f 1)) =
      column n (fun j => a * f j) := by
  simp only [column, liftX, seed, Polynomial.map_mul, ← C_pow]
  ring

private def firstColumn (d : ℕ) (a : K[X]) (β : Fin 2 → K[X]) : Bivar :=
  liftX a * (liftX (@Polynomial.map K K KS KS twist (β 0)) +
    seed ^ d * liftX (@Polynomial.map K K KS KS twist (β 1)))

private theorem threeU_fun : threeU = firstColumn p := rfl

private theorem firstColumn_normal (d : ℕ) (a : K[X]) (β : Fin 2 → K[X]) :
    firstColumn d a β = column d (fun j => a * (β j).map twist) :=
  column_mul a d (fun j => (β j).map twist)

private theorem left_eq {u T R D} (B : RankThree u T R D) :
    threeU B.a B.β = column p (leftCoeff B) := by
  rw [threeU_fun]
  exact (firstColumn_normal p B.a B.β).trans (congrArg (column p)
    (show (fun j => B.a * (B.β j).map twist) = leftCoeff B by rfl))

private theorem right_eq {u T R D} (B : RankThree u T R D) :
    threeV B.b B.α = column 1 (rightCoeff B) := by
  simp only [threeV, rightCoeff, column, liftX, seed, Polynomial.map_mul, Polynomial.map_neg, pow_one]
  ring

/-- A polynomial pair in the direction of a coprime pair and of no greater
maximum degree can differ only by a unit of the coefficient field. -/
private theorem tight_pair {F : Type*} [Field F] (U V U' V' : F[X])
    (hneU : U ≠ 0) (hneV : V ≠ 0) (hne' : U' ≠ 0) (hc : IsCoprime U V)
    (he : U * V' = V * U') (hmax : max U'.natDegree V'.natDegree ≤ max U.natDegree V.natDegree) :
    max U'.natDegree V'.natDegree = max U.natDegree V.natDegree ∧ IsCoprime U' V' := by
  obtain ⟨a,b,hab⟩ := hc
  let m := a * U' + b * V'
  have hu : U' = m * U := by dsimp [m]; linear_combination -U' * hab - b * he
  have hv : V' = m * V := by dsimp [m]; linear_combination -V' * hab + a * he
  have hm : m ≠ 0 := by intro h; exact hne' (hu.trans (by simp [h]))
  have huD := congrArg Polynomial.natDegree hu
  have hvD := congrArg Polynomial.natDegree hv
  rw [natDegree_mul hm hneU] at huD
  rw [natDegree_mul hm hneV] at hvD
  have hdeg : m.natDegree = 0 := by omega
  have hunit : IsUnit m := isUnit_iff_degree_eq_zero.mpr (by rw [degree_eq_natDegree hm, hdeg]; rfl)
  obtain ⟨k,hk⟩ := isUnit_iff_dvd_one.mp hunit
  refine ⟨by omega, a*k, b*k, ?_⟩
  calc
    a*k*U' + b*k*V' = (m*k) * (a*U + b*V) := by rw [hu,hv]; ring
    _ = 1 := by rw [← hk,hab,one_mul]

private def slice (P : Bivar) (n : ℕ) : K[X] :=
  ∑ j ∈ Finset.range (P.natDegree + 1), monomial j ((P.coeff j).coeff n)

private theorem slice_eval (P : Bivar) (n : ℕ) (x : K) :
    (slice P n).eval x = (P.eval (C x)).coeff n := by
  rw [eval_eq_sum_range (C x)]
  simp only [slice, eval_finsetSum, eval_monomial, finsetSum_coeff, ← C_pow, coeff_mul_C]

private theorem slice_bound (P : Bivar) (n : ℕ) : (slice P n).natDegree ≤ P.natDegree := by
  apply natDegree_sum_le_of_forall_le
  intro i hi
  exact (natDegree_monomial_le _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

private theorem select_four (d : ℕ) (hd : 1 < d) (r : Fin 2 → Fin 2 → K) (j l : Fin 2) :
    ((C (r 0 0) + C (r 1 0)*Polynomial.X + C (r 0 1)*Polynomial.X^d +
      C (r 1 1)*Polynomial.X^(d+1)) : K[X]).coeff (j.val + d*l.val) = r j l := by
  fin_cases j <;> fin_cases l <;>
    simp only [coeff_add, coeff_C_mul_X, coeff_C_mul_X_pow, coeff_C, Nat.mul_zero,
      Nat.mul_one, Nat.zero_add, Nat.add_zero] <;>
    split_ifs <;> first | omega | simp_all

private theorem four_coeff (d : ℕ) (hd : 1 < d) (u v w z : Fin 2 → K) (j l : Fin 2) :
    (((C (u 0) + C (u 1) * Polynomial.X ^ d) * (C (w 0) + Polynomial.X * C (w 1)) +
      (C (v 0) + C (v 1) * Polynomial.X) * (C (z 0) + Polynomial.X^d * C (z 1)) : K[X]).coeff
      (j.val + d*l.val)) = u l*w j + v j*z l := by
  let r := fun j l => u l*w j + v j*z l
  have hex : (C (u 0) + C (u 1) * Polynomial.X ^ d) * (C (w 0) + Polynomial.X * C (w 1)) +
      (C (v 0) + C (v 1) * Polynomial.X) * (C (z 0) + Polynomial.X^d * C (z 1)) =
      C (r 0 0) + C (r 1 0)*Polynomial.X + C (r 0 1)*Polynomial.X^d +
      C (r 1 1)*Polynomial.X^(d+1) := by
    simp only [r, map_add, map_mul, pow_succ]
    ring
  rw [hex]
  exact select_four d hd r j l

private theorem column_eval (d : ℕ) (f : Fin 2 → K[X]) (x : K) :
    (column d f).eval (C x) = C ((f 0).eval x) + C ((f 1).eval x) * Polynomial.X^d := by
  simp only [column, liftX, eval_add, eval_mul, eval_C, eval_map_apply]

private theorem word_coeff (d : ℕ) (hd : 1 < d) (U V : Fin 2 → K[X]) (u : Words)
    (i : I) (j l : Fin 2) :
    (U l).eval (node i) * u j i + (V j).eval (node i) * (u l i)^d =
    (((C ((U 0).eval (node i)) + C ((U 1).eval (node i)) * Polynomial.X^d) *
          (C (u 0 i) + Polynomial.X * C (u 1 i)) +
        (C ((V 0).eval (node i)) + C ((V 1).eval (node i)) * Polynomial.X) *
          (C ((u 0 i)^d) + Polynomial.X^d * C ((u 1 i)^d))) : K[X]).coeff
        (j.val + d*l.val) :=
  (four_coeff d hd (fun l => (U l).eval (node i)) (fun j => (V j).eval (node i))
    (fun j => u j i) (fun l => (u l i)^d) j l).symm

private def relationAt (d : ℕ) (u : Words) (deleted : Finset I) (U V output : Bivar) : Prop :=
  ∀ i ∉ deleted,
    U.eval (C (node i)) * (C (u 0 i) + Polynomial.X (R := K) * C (u 1 i)) +
    V.eval (C (node i)) * (C (u 0 i ^ d) + Polynomial.X (R := K) ^ d * C (u 1 i ^ d)) =
      output.eval (C (node i))

private theorem relationOn_fun : relationOn = relationAt p := rfl

private def outputs (d : ℕ) (P : Bivar) (j l : Fin 2) := slice P (j.val + d*l.val)

private theorem nodes_of_columns (d : ℕ) (hd : 1 < d) (u : Words) (deleted : Finset I)
    (U V : Fin 2 → K[X]) (P : Bivar)
    (h : relationAt d u deleted (column d U) (column 1 V) P) :
    planeNodes d u deleted U V (outputs d P) := by
  intro i hi j l
  rw [outputs, slice_eval, ← h i hi, column_eval, column_eval, pow_one]
  exact word_coeff d hd U V u i j l

theorem plane_of_rankThree {u : Words} {T : TwoActive u} {R : Relation T}
    {D : Reduction u T R} (B : RankThree u T R D) :
    Nonempty (Plane u (fixedNodes R) D.height (leftCoeff B) (rightCoeff B)) := by
  let U := leftCoeff B
  let V := rightCoeff B
  have amp_ne (v : Fin 2 → K[X]) (hv : IsCoprime (v 0) (v 1)) : ∃ j, v j ≠ 0 := by
    by_contra! hz
    obtain ⟨a,b,hab⟩ := hv
    simp [hz] at hab
  obtain ⟨l,hl⟩ := amp_ne B.β B.β_primitive
  obtain ⟨j,hj⟩ := amp_ne B.α B.α_primitive
  have hU : ∃ l, U l ≠ 0 :=
    ⟨l, mul_ne_zero B.a_ne ((Polynomial.map_ne_zero_iff twist.injective).mpr hl)⟩
  have hV : ∃ j, V j ≠ 0 := ⟨j, neg_ne_zero.mpr (mul_ne_zero B.b_ne hj)⟩
  have hu : amplitudeDegree (U 0) (U 1) ≤ D.height := by
    unfold amplitudeDegree
    apply max_le
    all_goals
      apply natDegree_mul_le.trans
      apply le_trans _ B.first_degree
      apply Nat.add_le_add_left
      rw [natDegree_map_eq_of_injective twist.injective]
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hv : amplitudeDegree (V 0) (V 1) ≤ D.height := by
    unfold amplitudeDegree
    apply max_le
    all_goals
      simp only [V, rightCoeff, natDegree_neg]
      apply natDegree_mul_le.trans
      apply le_trans _ B.second_degree
      apply Nat.add_le_add_left
    · exact le_max_left _ _
    · exact le_max_right _ _
  let φ := algebraMap K[X] Frac
  have hinj : Function.Injective φ := IsFractionRing.injective K[X] Frac
  have hd (P : Bivar) : (extendSeed P).natDegree = P.natDegree := natDegree_map_eq_of_injective hinj _
  have hn {P : Bivar} (hp : P ≠ 0) : extendSeed P ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hp
  have hdir := B.same_direction
  rw [sameDirection, left_eq, right_eq] at hdir
  have he := congrArg (Polynomial.map φ) hdir
  simp only [Polynomial.map_mul] at he
  have hdom := max_le_max (column_bound p U) (column_bound 1 V)
  obtain ⟨htight,hcp⟩ := tight_pair (extendSeed D.U) (extendSeed D.V)
    (extendSeed (column p U)) (extendSeed (column 1 V))
    (hn D.U_ne) (hn D.V_ne) (hn (column_ne (by decide : p ≠ 0) hU)) D.coprime he
    (by simp only [hd, D.max_degree]; exact hdom.trans (max_le hu hv))
  simp only [hd, D.max_degree] at htight
  refine ⟨⟨outputs p B.output, hU, hV, ?_, ?_, ?_, ?_⟩⟩
  · exact le_antisymm (max_le hu hv) (htight ▸ hdom)
  · intro f hfU hfV
    have hunit := hcp.isUnit_of_dvd'
      ((mapRingHom φ).map_dvd (column_dvd p U f hfU))
      ((mapRingHom φ).map_dvd (column_dvd 1 V f hfV))
    apply isUnit_iff_degree_eq_zero.mpr
    change IsUnit ((f.map Polynomial.C).map φ) at hunit
    simpa only [degree_map_eq_of_injective hinj,
      degree_map_eq_of_injective Polynomial.C_injective] using isUnit_iff_degree_eq_zero.mp hunit
  · intro j l
    apply degree_le_natDegree.trans_lt
    have ht : B.output.natDegree < 131072 + D.height := by
      by_cases hz : B.output = 0
      · simp [hz]
      · exact (natDegree_lt_iff_degree_lt hz).mpr B.output_degree
    exact_mod_cast (slice_bound B.output _).trans_lt ht
  · apply nodes_of_columns p (by decide) u (fixedNodes R) U V B.output
    have h := B.nodes
    rwa [relationOn_fun, left_eq, right_eq] at h

end
end K1_10
end PackSource_K1_10Plane

section PackSource_K1_10Adjugate
set_option autoImplicit true
namespace K1_10
noncomputable section
open K1 Polynomial ProximityPrize.Benchmark FrobeniusLocator

private theorem amp_le (v : Fin 2 → K[X]) (j : Fin 2) :
    (v j).natDegree ≤ amplitudeDegree (v 0) (v 1) := by
  fin_cases j
  · exact le_max_left _ _
  · exact le_max_right _ _

private theorem amp_witness (v : Fin 2 → K[X]) (hc : IsCoprime (v 0) (v 1)) :
    ∃ j, v j ≠ 0 ∧ (v j).natDegree = amplitudeDegree (v 0) (v 1) := by
  by_cases hv : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h
      obtain ⟨a, b, hab⟩ := hc
      simp [hv, h] at hab
    exact ⟨1, h1, by simp [amplitudeDegree, hv]⟩
  by_cases hd : (v 1).natDegree ≤ (v 0).natDegree
  · exact ⟨0, hv, (max_eq_left hd).symm⟩
  · refine ⟨1, ?_, (max_eq_right (by omega)).symm⟩
    intro hz
    simp [hz] at hd

/-- Divide two compatible lifts by their primitive pair. The degree bound
uses a nonzero coefficient of maximum degree, including constant pairs. -/
private theorem primitive_lift (del : Finset I) (v L : Fin 2 → K[X]) (w : I → K)
    (t : ℕ) (hc : IsCoprime (v 0) (v 1)) (hL : ∀ j, (L j).natDegree < t)
    (he : ∀ i ∉ del, ∀ j, (L j).eval (node i) = (v j).eval (node i) * w i)
    (hpos : amplitudeDegree (v 0) (v 1) < t)
    (hroom : t + amplitudeDegree (v 0) (v 1) + del.card ≤ 262144) :
    ∃ P : K[X], P.natDegree + amplitudeDegree (v 0) (v 1) < t ∧
      ∀ i ∉ del, P.eval (node i) = w i := by
  classical
  have hcross : v 0 * L 1 - v 1 * L 0 = 0 := by
    by_contra hn
    have hb := Strata.root_nodes_card_le node IRSProfile.domain.injective _ hn (Finset.univ \ del)
      (by
        intro i hi
        simp only [eval_sub, eval_mul, he i (Finset.mem_sdiff.mp hi).2]
        ring)
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, IRSProfile.card_index] at hb
    have hprod (i j : Fin 2) : (v i * L j).natDegree < amplitudeDegree (v 0) (v 1) + t :=
      natDegree_mul_le.trans_lt (Nat.add_lt_add_of_le_of_lt (amp_le v i) (hL j))
    have hlt := (natDegree_sub_le (v 0 * L 1) (v 1 * L 0)).trans_lt
      (max_lt (hprod 0 1) (hprod 1 0))
    omega
  obtain ⟨a,b,hab⟩ := hc
  let P := a * L 0 + b * L 1
  have hdiv (j : Fin 2) : v j * P = L j := by
    dsimp [P]
    fin_cases j
    · change v 0 * (a * L 0 + b * L 1) = L 0
      linear_combination L 0 * hab + b * hcross
    · change v 1 * (a * L 0 + b * L 1) = L 1
      linear_combination L 1 * hab - a * hcross
  refine ⟨P, ?_, ?_⟩
  · by_cases hz : P = 0
    · simpa [hz] using hpos
    obtain ⟨j,hv,hd⟩ := amp_witness v ⟨a,b,hab⟩
    have hh := hL j
    rw [← hdiv j, natDegree_mul hv hz, hd, add_comm] at hh
    exact hh
  · intro i hi
    have hh := congrArg (Polynomial.eval (node i)) hab
    simp only [eval_add, eval_mul, eval_one] at hh
    simp only [P, eval_add, eval_mul, he i hi]
    linear_combination w i * hh

private theorem contraction_degree {U V P Q : K[X]} {s t : ℕ}
    (hU : U.natDegree ≤ s) (hV : V.natDegree ≤ s)
    (hP : P.natDegree < t) (hQ : Q.natDegree < t) :
    (U * P - V * Q).natDegree < t + s := by
  apply (natDegree_sub_le _ _).trans_lt
  rw [add_comm t s]
  exact max_lt (natDegree_mul_le.trans_lt (Nat.add_lt_add_of_le_of_lt hU hP))
    (natDegree_mul_le.trans_lt (Nat.add_lt_add_of_le_of_lt hV hQ))

theorem adjugate_of_plane {u : Words} {T : TwoActive u} {R : Relation T} {D : Reduction u T R}
    (B : RankThree u T R D) (hnp : Nonparallel B)
    (W : Plane u (fixedNodes R) D.height (leftCoeff B) (rightCoeff B))
    (hroom : D.height + (fixedNodes R).card ≤ 32670) :
    Nonempty (Adjugate u (fixedNodes R) D.height) := by
  let A := B.α
  let V := fun j => (B.β j).map twist
  let s := amplitudeDegree (A 0) (A 1)
  let t := amplitudeDegree (V 0) (V 1)
  have htw (P : K[X]) : (P.map twist).natDegree = P.natDegree :=
    natDegree_map_eq_of_injective twist.injective _
  have ht : t = amplitudeDegree (B.β 0) (B.β 1) := by simp only [t, V, amplitudeDegree, htw]
  have ha : B.a.natDegree + t ≤ D.height := ht ▸ B.first_degree
  have hb : B.b.natDegree + s ≤ D.height := B.second_degree
  have hv : IsCoprime (V 0) (V 1) := B.β_primitive.map (mapRingHom twist)
  have hout (j l : Fin 2) : (W.output j l).natDegree < 131072 + D.height := by
    by_cases hz : W.output j l = 0
    · simp [hz]
    · exact (natDegree_lt_iff_degree_lt hz).mpr (W.output_degree j l)
  let L := fun l => A 0 * W.output 1 l - A 1 * W.output 0 l
  let N := fun j => V 1 * W.output j 0 - V 0 * W.output j 1
  let w := fun i => B.a.eval (node i) * ((A 0).eval (node i) * u 1 i - (A 1).eval (node i) * u 0 i)
  let z := fun i => B.b.eval (node i) * ((V 0).eval (node i) * (u 1 i)^p - (V 1).eval (node i) * (u 0 i)^p)
  have hn (i : I) (hi : i ∉ fixedNodes R) (j l : Fin 2) :
      (W.output j l).eval (node i) =
        B.a.eval (node i) * (V l).eval (node i) * u j i -
        B.b.eval (node i) * (A j).eval (node i) * (u l i)^p := by
    rw [← W.nodes i hi]
    simp only [leftCoeff, rightCoeff, eval_mul, eval_neg, A, V]
    ring
  obtain ⟨P, hP, heP⟩ := primitive_lift (fixedNodes R) V L w (131072 + D.height + s) hv
    (fun l => contraction_degree (amp_le A 0) (amp_le A 1) (hout 1 l) (hout 0 l))
    (by intro i hi j; simp only [L, w, eval_sub, eval_mul, hn i hi]; ring)
    (by change t < _; omega) (by change _ + t + _ ≤ _; omega)
  obtain ⟨Q, hQ, heQ⟩ := primitive_lift (fixedNodes R) A N z (131072 + D.height + t) B.α_primitive
    (fun j => contraction_degree (amp_le V 1) (amp_le V 0) (hout j 0) (hout j 1))
    (by intro i hi j; simp only [N, z, eval_sub, eval_mul, hn i hi]; ring)
    (by change s < _; omega) (by change _ + s + _ ≤ _; omega)
  change P.natDegree + t < 131072 + D.height + s at hP
  change Q.natDegree + s < 131072 + D.height + t at hQ
  let σ := RingEquiv.ofBijective twist ⟨twist.injective, Finite.surjective_of_injective twist.injective⟩
  let τ := σ.symm.toRingHom
  have hundo (x : K) : τ (twist x) = x := σ.symm_apply_apply x
  have hfixed (i : I) : τ (node i) = node i := by
    have hh : twist (node i) = node i := Native.native_domain_fixed i
    simpa only [hh] using hundo (node i)
  have hmap (F : K[X]) (i : I) : (F.map τ).eval (node i) = τ (F.eval (node i)) :=
    Strata.eval_coefficient_map τ _ _ (hfixed i)
  have hβ (l : Fin 2) (i : I) : (V l).eval (node i) = twist ((B.β l).eval (node i)) :=
    Strata.eval_coefficient_map twist _ _ (Native.native_domain_fixed i)
  let b := B.b.map τ
  let Q' := Q.map τ
  have heQ' (i : I) (hi : i ∉ fixedNodes R) : Q'.eval (node i) = b.eval (node i) *
      ((B.β 0).eval (node i) * u 1 i - (B.β 1).eval (node i) * u 0 i) := by
    rw [show Q'.eval (node i) = τ (Q.eval (node i)) from hmap Q i, heQ i hi]
    change τ (B.b.eval (node i) * ((V 0).eval (node i) * twist (u 1 i) -
      (V 1).eval (node i) * twist (u 0 i))) = _
    simp only [b, hmap, hβ, map_mul, map_sub, hundo]
  let det := A 0 * B.β 1 - A 1 * B.β 0
  let denom := B.a * b * det
  let num := fun j => b * B.β j * P - B.a * A j * Q'
  have hb' : b.natDegree = B.b.natDegree := natDegree_map_eq_of_injective τ.injective _
  have hQ' : Q'.natDegree = Q.natDegree := natDegree_map_eq_of_injective τ.injective _
  have hvdeg (j : Fin 2) : (B.β j).natDegree ≤ t := ht ▸ amp_le B.β j
  have hadeg (j : Fin 2) : (A j).natDegree ≤ s := amp_le A j
  have ddet : det.natDegree ≤ s + t := (natDegree_sub_le _ _).trans (max_le
    (natDegree_mul_le.trans (Nat.add_le_add (hadeg 0) (hvdeg 1)))
    (natDegree_mul_le.trans (Nat.add_le_add (hadeg 1) (hvdeg 0))))
  refine ⟨⟨denom, mul_ne_zero (mul_ne_zero B.a_ne ((Polynomial.map_ne_zero_iff τ.injective).mpr B.b_ne)) hnp,
    ?_, num, ?_, ?_⟩⟩
  · calc
      denom.natDegree ≤ B.a.natDegree + b.natDegree + det.natDegree :=
        natDegree_mul_le.trans (Nat.add_le_add_right natDegree_mul_le _)
      _ ≤ 2 * D.height := by omega
  · intro j
    apply degree_le_natDegree.trans_lt
    exact_mod_cast (show (num j).natDegree < 131072 + 2 * D.height from by
      apply (natDegree_sub_le _ _).trans_lt
      apply max_lt
      · have := hvdeg j
        exact (natDegree_mul_le.trans (Nat.add_le_add_right natDegree_mul_le _)).trans_lt (by omega)
      · have := hadeg j
        exact (natDegree_mul_le.trans (Nat.add_le_add_right natDegree_mul_le _)).trans_lt (by omega))
  · intro i hi j
    fin_cases j
    · change denom.eval (node i) * u 0 i = (num 0).eval (node i)
      simp only [denom, num, det, eval_mul, eval_sub, heP i hi, heQ' i hi, w]
      ring
    · change denom.eval (node i) * u 1 i = (num 1).eval (node i)
      simp only [denom, num, det, eval_mul, eval_sub, heP i hi, heQ' i hi, w]
      ring
end
end K1_10
end PackSource_K1_10Adjugate

section PackSource_K1_10Split
set_option autoImplicit true
namespace K1_10
noncomputable section

open K1 Polynomial

/-- The (1,1) filtered quotient with m=4, B=5 and s=t=16 supplies one
nonzero scalar eliminant for every genuine marked decoder on the puncture. -/
def c1 : Prop :=
  ∀ u deleted h U V, Plane u deleted h U V → 24597 ≤ h → h + deleted.card ≤ 32670 →
    quotientSurplus (262144 - deleted.card) h →
    ∃ A : ScalarSource, ∀ γ (M : BadMark u γ), Disjoint M.support deleted →
      A.atDecoder γ M.decoder = 0

/-- Standalone Taylor incidence for the nonzero specialized equations. -/
def c2 : Prop :=
  ∀ u (A : ScalarSource) (Γ : Finset K),
    (∀ γ ∈ Γ, A.atLabel γ ≠ 0 ∧ ∃ M : BadMark u γ, A.atDecoder γ M.decoder = 0) →
    Γ.card ≤ regularPrice

theorem bank_surplus (n h : ℕ) (hn : n ≤ 262144) (hh : 24597 ≤ h) :
    quotientSurplus n h := by
  have hm : sourceDim (721059-131071-h) 4 15 15 ≤ sourceDim 565391 4 15 15 := by
    unfold sourceDim
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (by omega) _))
  have hsource : sourceDim 721059 5 16 16 = 1495435536 := by decide
  have hmultiple : sourceDim 565391 4 15 15 = 741118086 := by decide
  have hjet : jetDim 4 16 16 - jetDim 3 15 15 = 2875 := by decide
  unfold quotientSurplus
  rw [hmultiple] at hm
  rw [hsource, hjet]
  omega

theorem zero_specializations (A : ScalarSource) (Γ : Finset K)
    (hΓ : ∀ γ ∈ Γ, A.atLabel γ = 0) : Γ.card ≤ 44744835119 := by
  obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr A.nonzero
  apply frobenius_coefficient_exception_count p 26 21 (by decide) (A.poly.coeff e)
    (MvPolynomial.mem_support_iff.mp he) (A.s_degree e he) (by decide) (A.t_degree e he) Γ
  intro γ hγ
  have hh := congrArg (fun P : MvPolynomial (Fin 2) K => P.coeff e) (hΓ γ hγ)
  simpa only [ScalarSource.atLabel, MvPolynomial.coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hh

theorem of_children (h1 : c1) (h2 : c2) : K1.c10 := by
  classical
  intro u hu T R D B hsat hnp Γ hΓ
  let N := normalSlopes u Γ
  have hn : ∀ γ ∈ N, Normal u γ := normal_on_normalSlopes
  have hbad : BadFamily u N := normal_badFamily hΓ
  obtain ⟨W⟩ := plane_of_rankThree B
  have hbalance := height_balance T D
  have hh : D.height + (fixedNodes R).card ≤ 32670 := by have := hu.1; omega
  by_cases hsmall : 2 * D.height < 49193
  · obtain ⟨J⟩ := adjugate_of_plane B hnp W hh
    have hempty : N = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro γ hγ
      obtain ⟨M⟩ := bad_mark u N hbad γ hγ
      exact no_small_normal T D J hsmall (hn γ hγ) M)
    exact (add_rank_exceptions u hu Γ 0 (by change N.card ≤ 0; simp [hempty])).trans
      (by decide)
  have hmin : 24597 ≤ D.height := by omega
  obtain ⟨A, hA⟩ := h1 u _ D.height _ _ W hmin hh
    (bank_surplus _ _ (Nat.sub_le _ _) hmin)
  let good := N.filter (fun γ => A.atLabel γ ≠ 0)
  let exc := N.filter (fun γ => ¬ A.atLabel γ ≠ 0)
  have hexc : exc.card ≤ 44744835119 := zero_specializations A exc (by
    intro γ hγ
    exact not_ne_iff.mp (Finset.mem_filter.mp hγ).2)
  have hgood : good.card ≤ regularPrice := h2 u A good (by
    intro γ hγ
    obtain ⟨hγN, hnonzero⟩ := Finset.mem_filter.mp hγ
    obtain ⟨M⟩ := bad_mark u N hbad γ hγN
    exact ⟨hnonzero, M, hA γ M (mark_disjoint D (hn γ hγN) M)⟩)
  have hprice : regularPrice = 116963116437493992 := by norm_num [regularPrice]
  have hsum : good.card + exc.card = N.card :=
    Finset.card_filter_add_card_filter_not (s := N) (p := fun γ => A.atLabel γ ≠ 0)
  have hnormal : N.card ≤ 116963161182329111 := by omega
  have hwhole : Γ.card ≤ 117032792668608744 := add_rank_exceptions u hu Γ _ hnormal
  exact hwhole.trans (by decide)

end
end K1_10
end PackSource_K1_10Split

section PackSource_K1_10_2Defs
set_option autoImplicit true
set_option autoImplicit false

namespace K1_10_2
noncomputable section

open K1 MvPolynomial
open scoped Polynomial

abbrev Marks (u : Words) (Γ : Finset K) := ∀ γ ∈ Γ, BadMark u γ
abbrev Row := MvPolynomial (Fin 3) K[X]
abbrev GenericRow := MvPolynomial (Fin 3) Frac

/-- Coordinates are Y, S and T. The abscissa X remains in the coefficient ring. -/
def trajectory (γ : K) (P : K[X]) : Fin 3 → K[X] :=
  ![P, Polynomial.C γ, Polynomial.C (γ ^ p)]

def atTrajectory (g : Row) (γ : K) (P : K[X]) : K[X] :=
  MvPolynomial.eval (trajectory γ P) g

def derivativeOrder (g : Row) (j : Fin 5) : Row :=
  (MvPolynomial.pderiv (R := K[X]) (0 : Fin 3))^[j.val] g

def RegularRoot (g : Row) (γ : K) (P : K[X]) : Prop :=
  atTrajectory g γ P = 0 ∧ atTrajectory (MvPolynomial.pderiv 0 g) γ P ≠ 0

/-- Embed the coefficient ring into K(X). This evaluates X at the transcendental centre. -/
def toGeneric (g : Row) : GenericRow :=
  MvPolynomial.map (algebraMap K[X] Frac) g

def point (γ : K) (P : K[X]) : Fin 3 → Frac :=
  (algebraMap K[X] Frac) ∘ trajectory γ P

def cutDegree : ℕ := (2 * 131071 - 1) * (37 - 1) + 1
def incidenceRatio : ℚ := (131073 / 49194 : ℚ) * cutDegree

/-- Cleared Taylor cuts agree exactly with decoder evaluations on the selected chart. -/
structure TaylorCuts {u : Words} {Γ : Finset K} (F : Marks u Γ) where
  equation : I → GenericRow
  degree : ∀ i, (equation i).totalDegree ≤ cutDegree
  agrees : ∀ γ (hγ : γ ∈ Γ) i,
    MvPolynomial.eval (point γ (F γ hγ).decoder) (equation i) = 0 ↔
      (F γ hγ).decoder.eval (node i) = u 0 i + γ * u 1 i

end
end K1_10_2
end PackSource_K1_10_2Defs

section PackSource_K1_10_2Incidence
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace K1_10_2
noncomputable section

open MvPolynomial
open scoped BigOperators

-- The degree induction is adapted from K1_11Incidence for arbitrary chart data.

private theorem ncard_inter_filter {A : Type*} (S : Finset A) (locus : Set A) [DecidablePred (· ∈ locus)] :
    ((S : Set A) ∩ locus).ncard = (S.filter (· ∈ locus)).card := by
  rw [← Set.ncard_coe_finset, Finset.coe_filter]
  rfl

/-- A rational point supplies a chain of proper linear sections through it.
Bézout along the chain reduces the degree lower bound to dimension zero. -/
private theorem one_le_degree_of_point {F σ : Type*} [Field F] [Finite σ]
    (J : Ideal (MvPolynomial σ F)) [J.IsPrime] (x : σ → F) (hx : x ∈ zeroLocus F J) :
    1 ≤ affineDegree J := by
  classical
  generalize hd : (affineHilbertPolynomial J).natDegree = d
  induction d using Nat.strong_induction_on generalizing J with
  | h d ih =>
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

/-- The degree-weighted induction admits a bounded terminal set on a prime
with many persistent node equations. Each other step uses a proper cut. -/
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
  | h d ih =>
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
end PackSource_K1_10_2Incidence

section PackSource_K1_10_2Counting
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace K1_10_2
noncomputable section

open K1 Polynomial MvPolynomial ProximityPrize.Benchmark

private theorem pencil_count {u : Words} (Γ : Finset K) (F : Marks u Γ)
    (P Q : K[X]) (hP : P.degree < 131072) (hQ : Q.degree < 131072)
    (hpencil : ∀ γ (hγ : γ ∈ Γ), (F γ hγ).decoder = P + Polynomial.C γ * Q) :
    Γ.card ≤ 81880 := by
  classical
  rcases Γ.eq_empty_or_nonempty with rfl | ⟨r, hr⟩
  · simp
  let S := (F r hr).support
  let mismatch (i : I) := P.eval (node i) ≠ u 0 i ∨ Q.eval (node i) ≠ u 1 i
  have hits {γ : K} (hγ : γ ∈ Γ) {i : I} (hi : i ∈ (F γ hγ).support) :
      P.eval (node i) + γ * Q.eval (node i) = u 0 i + γ * u 1 i := by
    simpa only [hpencil γ hγ, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
      using (F γ hγ).hits i hi
  have unique {γ δ : K} (hγ : γ ∈ Γ) (hδ : δ ∈ Γ) {i : I}
      (hi : i ∈ (F γ hγ).support) (hj : i ∈ (F δ hδ).support) (hm : mismatch i) :
      γ = δ := by
    by_contra hne
    have hγi := hits hγ hi
    have hδi := hits hδ hj
    have h := show (γ - δ) * (Q.eval (node i) - u 1 i) = 0 by
      linear_combination hγi - hδi
    have he := sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hne))
    rw [he, add_right_cancel_iff] at hγi
    exact hm.elim (fun hbad => hbad hγi) (fun hbad => hbad he)
  have witness (γ : ↥(Γ.erase r)) :
      ∃ i ∈ (F γ.val (Finset.mem_erase.mp γ.property).2).support, mismatch i := by
    let M := F γ.val (Finset.mem_erase.mp γ.property).2
    by_contra hw
    apply M.nonjoint
    refine ⟨⟨P, hP, ?_⟩, ⟨Q, hQ, ?_⟩⟩
    · intro i hi
      by_contra hn
      exact hw ⟨i, hi, Or.inl hn⟩
    · intro i hi
      by_contra hn
      exact hw ⟨i, hi, Or.inr hn⟩
  choose index hindex hmismatch using witness
  let f : ↥(Γ.erase r) → ↥((Finset.univ : Finset I) \ S) := fun γ =>
    ⟨index γ, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hi =>
      (Finset.mem_erase.mp γ.property).1
        (unique (Finset.mem_erase.mp γ.property).2 hr (hindex γ) hi (hmismatch γ))⟩⟩
  have hf : Function.Injective f := by
    intro γ δ h
    have he : index γ = index δ := congrArg Subtype.val h
    have hδ := hindex δ
    rw [← he] at hδ
    exact Subtype.ext (unique (Finset.mem_erase.mp γ.property).2
      (Finset.mem_erase.mp δ.property).2 (hindex γ) hδ (hmismatch γ))
  have hcard := Finset.card_le_card_of_injective hf
  have he := Finset.card_erase_add_one hr
  have hS : 180265 ≤ S.card := (F r hr).agreement
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    IRSProfile.card_index] at hcard
  omega

private theorem persistent_count {u : Words} {Γ : Finset K} {F : Marks u Γ}
    (C : TaylorCuts F) (J : Ideal GenericRow) (W : Finset K) (hW : W ⊆ Γ)
    (hzero : ∀ γ (hγ : γ ∈ W), point γ (F γ (hW hγ)).decoder ∈ zeroLocus Frac J)
    (hpersistent : 131072 ≤ {i | C.equation i ∈ J}.ncard) :
    W.card ≤ 81880 := by
  classical
  let keep := Finset.univ.filter fun i => C.equation i ∈ J
  have hk : 131072 ≤ keep.card := by
    rw [← Set.ncard_coe_finset]
    exact hpersistent.trans_eq (congrArg Set.ncard (by ext i; simp [keep]))
  obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq hk
  let P := Lagrange.interpolate S node (u 0)
  let Q := Lagrange.interpolate S node (u 1)
  have hinj : Set.InjOn node (S : Set I) := node.injective.injOn
  have hP : P.degree < (131072 : ℕ) := by
    simpa only [P, hcard] using Lagrange.degree_interpolate_lt (u 0) hinj
  have hQ : Q.degree < (131072 : ℕ) := by
    simpa only [Q, hcard] using Lagrange.degree_interpolate_lt (u 1) hinj
  apply pencil_count W (fun γ hγ => F γ (hW hγ)) P Q hP hQ
  intro γ hγ
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq S hinj
  · rw [hcard]
    exact (F γ (hW hγ)).degree
  · rw [hcard]
    have hm : (Polynomial.C γ * Q).degree ≤ Q.degree := by
      refine (Polynomial.degree_mul_le _ _).trans ?_
      simpa only [zero_add] using add_le_add_left (Polynomial.degree_C_le (a := γ)) Q.degree
    exact (Polynomial.degree_add_le _ _).trans_lt (max_lt hP (hm.trans_lt hQ))
  · intro i hi
    have hcut := (Finset.mem_filter.mp (hS hi)).2
    have hz := hzero γ hγ _ hcut
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    exact (C.agrees γ (hW hγ) i).mp hz |>.trans (by
      rw [Lagrange.eval_interpolate_at_node _ hinj hi, Lagrange.eval_interpolate_at_node _ hinj hi])

theorem count_chart {u : Words} {Γ : Finset K} (F : Marks u Γ) (C : TaylorCuts F)
    (g s : GenericRow) (hg : g ≠ 0) (hdeg : g.totalDegree ≤ 37)
    (hroot : ∀ γ (hγ : γ ∈ Γ), MvPolynomial.eval (point γ (F γ hγ).decoder) g = 0 ∧
      MvPolynomial.eval (point γ (F γ hγ).decoder) s ≠ 0) :
    (Γ.card : ℚ) ≤ 37 * incidenceRatio ^ 2 := by
  classical
  let x : Γ → (Fin 3 → Frac) := fun γ => point γ (F γ γ.property).decoder
  have hinj : Function.Injective x := by
    intro γ δ h
    apply Subtype.ext
    apply Polynomial.C_injective
    apply IsFractionRing.injective K[X] Frac
    exact congrFun h 1
  let S := Γ.attach.image x
  have hcard : S.card = Γ.card := by
    simp only [S, Finset.card_image_of_injective _ hinj, Finset.card_attach]
  have hR : (81880 : ℚ) ≤ incidenceRatio := by norm_num [incidenceRatio, cutDegree]
  have hratio (m : ℕ) (hm : m < 131072) :
      (((Fintype.card I - m) * cutDegree : ℕ) : ℚ) ≤
        incidenceRatio * ((180265 - m : ℕ) : ℚ) := by
    rw [IRSProfile.card_index, Nat.cast_mul]
    have hn : (262144 - m) * 49194 ≤ 131073 * (180265 - m) := by omega
    have hq : ((262144 - m : ℕ) : ℚ) * 49194 ≤ 131073 * ((180265 - m : ℕ) : ℚ) := by
      exact_mod_cast hn
    have h := (show ((262144 - m : ℕ) : ℚ) ≤
        (131073 / 49194 : ℚ) * ((180265 - m : ℕ) : ℚ) by linarith)
    exact (mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ (cutDegree : ℚ))).trans_eq (by
      dsimp [incidenceRatio]; ring)
  rw [← hcard]
  refine surface_count_with_terminal g s hg C.equation (L := 131072) (A := 180265)
    (by decide) hdeg C.degree ((by norm_num : (1 : ℚ) ≤ 81880).trans hR) hratio S
    (fun y hy => ?_) (fun y hy => ?_) (fun J hJ => ?_)
  · obtain ⟨γ, -, rfl⟩ := Finset.mem_image.mp hy
    exact hroot γ γ.property
  · obtain ⟨γ, -, rfl⟩ := Finset.mem_image.mp hy
    let M := F γ γ.property
    have hsub : (M.support : Set I) ⊆ {i | aeval (x γ) (C.equation i) = 0} :=
      fun i hi => (C.agrees γ γ.property i).mpr (M.hits i hi)
    exact M.agreement.trans (by simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hsub)
  · let W := Γ.attach.filter fun γ => x γ ∈ zeroLocus Frac J
    let V := W.image (fun γ : Γ => (γ : K))
    have hV : V ⊆ Γ := fun γ hγ => by
      obtain ⟨δ, -, rfl⟩ := Finset.mem_image.mp hγ
      exact δ.property
    have hV0 : ∀ γ (hγ : γ ∈ V), point γ (F γ (hV hγ)).decoder ∈ zeroLocus Frac J := by
      intro γ hγ
      obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.mp hγ
      exact (Finset.mem_filter.mp hδ).2
    have hcount := persistent_count C J V hV hV0 hJ
    have hW : W.card = V.card := (Finset.card_image_of_injective W Subtype.val_injective).symm
    have he : (S : Set (Fin 3 → Frac)) ∩ zeroLocus Frac J = (W.image x : Finset _) := by
      ext y
      simp only [S, W, Set.mem_inter_iff, Finset.mem_coe, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨γ, hγ, rfl⟩, h⟩
        exact ⟨γ, ⟨hγ, h⟩, rfl⟩
      · rintro ⟨γ, ⟨hγ, h⟩, rfl⟩
        exact ⟨⟨γ, hγ, rfl⟩, h⟩
    rw [he, Set.ncard_coe_finset, Finset.card_image_of_injective _ hinj, hW]
    exact (by exact_mod_cast hcount : (V.card : ℚ) ≤ 81880).trans hR

end
end K1_10_2
end PackSource_K1_10_2Counting

section PackSource_K1_10_2_2Derivatives
set_option autoImplicit true
set_option autoImplicit false

namespace K1_10_2_2
noncomputable section

open K1 K1_10_2 MvPolynomial
open scoped Polynomial BigOperators

/-- Differentiate in the coefficient abscissa, holding the three chart coordinates fixed. -/
def dx (f : Row) : Row :=
  ∑ m ∈ f.support, monomial m (f.coeff m).derivative

abbrev dy (f : Row) : Row := MvPolynomial.pderiv 0 f

/-- The tangent derivative multiplied by the separant. -/
def flow (g f : Row) : Row :=
  dy g * dx f - dx g * dy f

/-- Numerator of the derivative of order n+1, with denominator (dy g)^(2*n+1). -/
def numerator (g : Row) : ℕ → Row
  | 0 => -dx g
  | n+1 => dy g * flow g (numerator g n) -
    MvPolynomial.C ((2*n+1 : ℕ) : K[X]) * flow g (dy g) * numerator g n

@[simp] private theorem coeff_dx (f : Row) (m : Fin 3 →₀ ℕ) :
    (dx f).coeff m = (f.coeff m).derivative := by
  classical
  rw [dx, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hm, map_zero]

private theorem dx_C (c : K[X]) :
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

private theorem trajectory_chain (γ : K) (P : K[X]) (f : Row) :
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

private theorem eval_flow (g f : Row) (γ : K) (P : K[X]) (hg : atTrajectory g γ P = 0) :
    atTrajectory (flow g f) γ P = atTrajectory (dy g) γ P * (atTrajectory f γ P).derivative := by
  have hz : atTrajectory (dx g) γ P + P.derivative * atTrajectory (dy g) γ P = 0 := by
    rw [← trajectory_chain, hg, map_zero]
  rw [trajectory_chain]
  simp only [flow, atTrajectory, map_sub, map_mul]
  unfold atTrajectory at hz
  linear_combination -MvPolynomial.eval (trajectory γ P) (dy f) * hz

private theorem cleared_product_rule (a : ℕ) (U V : K[X]) :
    U * (U * (U^a * V).derivative) - (a : K[X]) * (U * U.derivative) * (U^a * V) =
      U^(a+2) * V.derivative := by
  cases a with
  | zero => simp [pow_two, mul_assoc]
  | succ a =>
    rw [Polynomial.derivative_mul, Polynomial.derivative_pow, Nat.succ_sub_one,
      pow_add U (a+1) 2, pow_succ' U a]
    simp only [Polynomial.C_eq_natCast]
    push_cast
    ring

theorem eval_numerator (g : Row) (γ : K) (P : K[X])
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
      ((2*n+1 : ℕ) : K[X]) * atTrajectory (flow g (dy g)) γ P *
        atTrajectory (numerator g n) γ P = _
    rw [eval_flow _ _ _ _ hg, eval_flow _ _ _ _ hg, ih, cleared_product_rule,
      show 2*(n+1)+1 = 2*n+1+2 by omega]
    congr 1
    exact (Function.iterate_succ_apply' _ _ _).symm

private theorem dx_degree (f : Row) : (dx f).totalDegree ≤ f.totalDegree := by
  classical
  apply totalDegree_le_of_support_subset
  intro m hm
  contrapose! hm
  rw [MvPolynomial.notMem_support_iff] at hm ⊢
  rw [coeff_dx, hm, map_zero]

private theorem dy_degree (f : Row) : (dy f).totalDegree ≤ f.totalDegree - 1 := by
  simpa only [weightedTotalDegree_one, Pi.one_apply] using
    weightedTotalDegree_pderiv_le_sub (1 : Fin 3 → ℕ) (0 : Fin 3) f

theorem separant_degree {g : Row} (h : g.totalDegree ≤ 37) : (dy g).totalDegree ≤ 36 := by
  have := dy_degree g
  omega

private theorem flow_degree {g f : Row} {d : ℕ}
    (hg : g.totalDegree ≤ 37) (hf : f.totalDegree ≤ d) (hd : 0 < d) :
    (flow g f).totalDegree ≤ d + 36 := by
  have ha := separant_degree hg
  have hx := dx_degree g
  have hfx := dx_degree f
  have hfy := dy_degree f
  unfold flow
  apply (totalDegree_sub _ _).trans
  apply max_le
  · apply (totalDegree_mul _ _).trans
    omega
  · apply (totalDegree_mul _ _).trans
    omega

theorem numerator_degree {g : Row} (hg : g.totalDegree ≤ 37) (n : ℕ) :
    (numerator g n).totalDegree ≤ (2*n+1)*36+1 := by
  induction n with
  | zero =>
    simpa [numerator, totalDegree_neg] using (dx_degree g).trans hg
  | succ n ih =>
    have ha := separant_degree hg
    have hf := flow_degree hg ih (by omega)
    have hfa := flow_degree hg ha (by decide)
    rw [numerator]
    apply (totalDegree_sub _ _).trans
    apply max_le
    · apply (totalDegree_mul _ _).trans
      omega
    · apply (totalDegree_mul _ _).trans
      have hc := totalDegree_mul
        (MvPolynomial.C ((2*n+1 : ℕ) : K[X]) : Row) (flow g (dy g))
      rw [totalDegree_C, zero_add] at hc
      omega

end
end K1_10_2_2
end PackSource_K1_10_2_2Derivatives

section PackSource_K1_10_2Split
set_option autoImplicit true
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

namespace K1_10_2
noncomputable section

open K1 K1_10 MvPolynomial
open scoped Polynomial

/-- Put X in the coefficient ring, then assign a simple Y-derivative at each marked root. -/
def c1 : Prop :=
  ∀ (u : Words) (A : ScalarSource) (Γ : Finset K) (F : Marks u Γ),
    (∀ γ (hγ : γ ∈ Γ), A.atLabel γ ≠ 0 ∧ A.atDecoder γ (F γ hγ).decoder = 0) →
    ∃ g : Row, g.totalDegree ≤ 37 ∧
      ∀ γ (hγ : γ ∈ Γ), ∃ j : Fin 5,
        RegularRoot (derivativeOrder g j) γ (F γ hγ).decoder

/-- At simple roots, implicit Taylor reconstruction supplies cleared node cuts. -/
def c2 : Prop :=
  ∀ (u : Words) (Γ : Finset K) (F : Marks u Γ) (g : Row),
    g.totalDegree ≤ 37 →
    (∀ γ (hγ : γ ∈ Γ), RegularRoot g γ (F γ hγ).decoder) →
    Nonempty (TaylorCuts F)

private theorem pderiv_degree (g : Row) :
    (MvPolynomial.pderiv (0 : Fin 3) g).totalDegree ≤ g.totalDegree := by
  simpa only [weightedTotalDegree_one] using
    weightedTotalDegree_pderiv_le (1 : Fin 3 → ℕ) (0 : Fin 3) g

private theorem derivativeOrder_degree (g : Row) (j : Fin 5) :
    (derivativeOrder g j).totalDegree ≤ g.totalDegree := by
  have h (n : ℕ) :
      (((MvPolynomial.pderiv (R := K[X]) (0 : Fin 3))^[n]) g).totalDegree ≤
        g.totalDegree := by
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (pderiv_degree _).trans ih
  exact h j.val

private theorem eval_toGeneric (g : Row) (γ : K) (P : K[X]) :
    MvPolynomial.eval (point γ P) (toGeneric g) = algebraMap K[X] Frac (atTrajectory g γ P) := by
  rw [toGeneric, MvPolynomial.eval_map]
  exact (MvPolynomial.eval₂_comp (algebraMap K[X] Frac) (trajectory γ P) g).symm

theorem of_children (h1 : c1) (h2 : c2) : K1_10.c2 := by
  classical
  intro u A Γ hΓ
  let F : Marks u Γ := fun γ hγ => Classical.choose (hΓ γ hγ).2
  have hF (γ : K) (hγ : γ ∈ Γ) :
      A.atLabel γ ≠ 0 ∧ A.atDecoder γ (F γ hγ).decoder = 0 :=
    ⟨(hΓ γ hγ).1, Classical.choose_spec (hΓ γ hγ).2⟩
  obtain ⟨g, hg, hassign⟩ := h1 u A Γ F hF
  let charts (j : Fin 5) := Γ.filter fun γ =>
    ∃ hγ : γ ∈ Γ, RegularRoot (derivativeOrder g j) γ (F γ hγ).decoder
  have hsub (j : Fin 5) : charts j ⊆ Γ := Finset.filter_subset _ _
  have hcover : Γ ⊆ Finset.univ.biUnion charts := by
    intro γ hγ
    obtain ⟨j, hj⟩ := hassign γ hγ
    exact Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hγ, hγ, hj⟩⟩
  have hchart (j : Fin 5) : ((charts j).card : ℚ) ≤ 37 * incidenceRatio ^ 2 := by
    rcases (charts j).eq_empty_or_nonempty with hempty | ⟨γ₀, hγ₀⟩
    · simp only [hempty, Finset.card_empty, Nat.cast_zero]
      positivity
    let G := derivativeOrder g j
    let M : Marks u (charts j) := fun γ hγ => F γ (hsub j hγ)
    have hregular (γ : K) (hγ : γ ∈ charts j) : RegularRoot G γ (M γ hγ).decoder := by
      obtain ⟨_, hr⟩ := (Finset.mem_filter.mp hγ).2
      exact hr
    have hG : G.totalDegree ≤ 37 := (derivativeOrder_degree g j).trans hg
    obtain ⟨C⟩ := h2 u (charts j) M G hG hregular
    have hinj := IsFractionRing.injective K[X] Frac
    have hGne : G ≠ 0 := by
      intro h
      exact (hregular γ₀ hγ₀).2 (by simp [h, atTrajectory])
    have hgne : toGeneric G ≠ 0 := by
      intro h
      exact hGne (MvPolynomial.map_injective (algebraMap K[X] Frac) hinj
        (by simpa [toGeneric] using h))
    have hgd : (toGeneric G).totalDegree ≤ 37 := by
      simpa only [toGeneric, totalDegree, support_map_of_injective G hinj] using hG
    apply count_chart M C (toGeneric G) (toGeneric (MvPolynomial.pderiv 0 G)) hgne hgd
    intro γ hγ
    obtain ⟨hr, hs⟩ := hregular γ hγ
    rw [eval_toGeneric, eval_toGeneric, hr, map_zero]
    exact ⟨rfl, by simpa only [map_zero] using hinj.ne hs⟩
  have hnat : Γ.card ≤ ∑ j : Fin 5, (charts j).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hrat : (Γ.card : ℚ) ≤ 5 * 37 * incidenceRatio ^ 2 := by
    calc
      (Γ.card : ℚ) ≤ ∑ j : Fin 5, ((charts j).card : ℚ) := by exact_mod_cast hnat
      _ ≤ ∑ _j : Fin 5, (37 * incidenceRatio ^ 2 : ℚ) :=
        Finset.sum_le_sum fun j _ => hchart j
      _ = _ := by simp; ring
  have hceil : 5 * 37 * incidenceRatio ^ 2 ≤ (regularPrice : ℚ) := by
    norm_num [regularPrice, incidenceRatio, cutDegree]
  exact_mod_cast hrat.trans hceil

end
end K1_10_2
end PackSource_K1_10_2Split

section PackSource_K1_10_2_2Proof
set_option autoImplicit true
set_option autoImplicit false

namespace K1_10_2_2
noncomputable section

open K1 K1_10_2 MvPolynomial
open scoped Polynomial BigOperators

private def width : ℕ := 131071
private def clearPower : ℕ := 2 * width - 1

private abbrev fracMap : K[X] →+* Frac := algebraMap K[X] Frac
private abbrev embed : K →+* Frac := fracMap.comp Polynomial.C
private abbrev centre : Frac := fracMap Polynomial.X

private theorem eval_at_centre (P : K[X]) : (P.map embed).eval centre = fracMap P := by
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

private abbrev derivativeAt (P : K[X]) (n : ℕ) : Frac :=
  fracMap (((Polynomial.derivative (R := K))^[n]) P)

private def taylorScalar (x : K) (n : ℕ) : Frac :=
  (n.factorial : Frac)⁻¹ * (embed x - centre)^n

private theorem taylor_term (P : K[X]) (x : K) (n : ℕ) (hn : n < p) :
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

/-- At the transcendental centre, the ordinary derivatives give exact Taylor evaluation. -/
private theorem eval_taylor (P : K[X]) (hP : P.degree < 131072) (x : K) :
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

private abbrev separant (g : Row) : GenericRow := toGeneric (dy g)

/-- Common-denominator Taylor evaluation at x, represented in the three chart coordinates. -/
private def taylorNumerator (g : Row) (x : K) : GenericRow :=
  separant g ^ clearPower * MvPolynomial.X 0 +
    ∑ n ∈ Finset.range width,
      separant g ^ (clearPower - (2*n+1)) * toGeneric (numerator g n) *
        MvPolynomial.C (taylorScalar x (n+1))

private def received (u : Words) (i : I) : GenericRow :=
  MvPolynomial.C (embed (u 0 i)) + MvPolynomial.X 1 * MvPolynomial.C (embed (u 1 i))

private def nodeCut (u : Words) (g : Row) (i : I) : GenericRow :=
  taylorNumerator g (node i) - separant g ^ clearPower * received u i

private theorem toGeneric_degree (f : Row) : (toGeneric f).totalDegree ≤ f.totalDegree := by
  rw [totalDegree_eq, totalDegree_eq]
  exact Finset.sup_mono (MvPolynomial.support_map_subset fracMap f)

private theorem order_le_clearPower {n : ℕ} (hn : n ∈ Finset.range width) :
    2*n+1 ≤ clearPower := by
  have hn' := Finset.mem_range.mp hn
  unfold width at hn'
  unfold clearPower width
  omega

private theorem sep_pow_degree (g : Row) (hg : g.totalDegree ≤ 37) (a : ℕ) :
    (separant g ^ a).totalDegree ≤ a * 36 :=
  (totalDegree_pow _ _).trans
    (Nat.mul_le_mul_left a ((toGeneric_degree _).trans (separant_degree hg)))

private theorem taylorNumerator_degree (g : Row) (hg : g.totalDegree ≤ 37) (x : K) :
    (taylorNumerator g x).totalDegree ≤ cutDegree := by
  unfold taylorNumerator
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_mul _ _).trans
    rw [totalDegree_X]
    exact Nat.add_le_add_right (sep_pow_degree g hg clearPower) 1
  · apply totalDegree_finsetSum_le
    intro n hn
    apply (totalDegree_mul _ _).trans
    rw [totalDegree_C, add_zero]
    apply (totalDegree_mul _ _).trans
    have h1 := sep_pow_degree g hg (clearPower - (2*n+1))
    have h2 := (toGeneric_degree (numerator g n)).trans (numerator_degree hg n)
    have h3 := Nat.sub_add_cancel (order_le_clearPower hn)
    change _ ≤ clearPower * 36 + 1
    omega

private theorem received_degree (u : Words) (i : I) : (received u i).totalDegree ≤ 1 := by
  unfold received
  apply (totalDegree_add _ _).trans
  rw [totalDegree_C, Nat.zero_max]
  exact (totalDegree_mul _ _).trans (by rw [totalDegree_X, totalDegree_C])

private theorem nodeCut_degree (u : Words) (g : Row) (hg : g.totalDegree ≤ 37) (i : I) :
    (nodeCut u g i).totalDegree ≤ cutDegree := by
  unfold nodeCut
  apply (totalDegree_sub _ _).trans
  refine max_le (taylorNumerator_degree g hg _) ((totalDegree_mul _ _).trans ?_)
  exact Nat.add_le_add (sep_pow_degree g hg clearPower) (received_degree u i)

private theorem eval_toGeneric (f : Row) (γ : K) (P : K[X]) :
    MvPolynomial.eval (point γ P) (toGeneric f) = fracMap (atTrajectory f γ P) := by
  rw [toGeneric, MvPolynomial.eval_map]
  exact (MvPolynomial.eval₂_comp fracMap (trajectory γ P) f).symm

private theorem eval_taylorNumerator (g : Row) (γ : K) (P : K[X])
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

private theorem eval_nodeCut (u : Words) (g : Row) (γ : K) (P : K[X])
    (hg : RegularRoot g γ P) (hP : P.degree < 131072) (i : I) :
    MvPolynomial.eval (point γ P) (nodeCut u g i) = 0 ↔
      P.eval (node i) = u 0 i + γ * u 1 i := by
  have hsep : fracMap (atTrajectory (dy g) γ P) ≠ 0 :=
    (map_ne_zero_iff fracMap (IsFractionRing.injective K[X] Frac)).mpr hg.2
  have hreceived : MvPolynomial.eval (point γ P) (received u i) =
      embed (u 0 i + γ * u 1 i) := by
    simp only [received, map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      show point γ P 1 = embed γ from rfl]
  rw [nodeCut, map_sub, map_mul, map_pow, eval_taylorNumerator g γ P hg.1 hP,
    eval_toGeneric, hreceived, ← mul_sub, mul_eq_zero, or_iff_right (pow_ne_zero _ hsep),
    sub_eq_zero]
  exact embed.injective.eq_iff

theorem proof : K1_10_2.c2 := by
  intro u Γ F g hg hregular
  refine ⟨⟨nodeCut u g, nodeCut_degree u g hg, ?_⟩⟩
  intro γ hγ i
  exact eval_nodeCut u g γ (F γ hγ).decoder (hregular γ hγ) (F γ hγ).degree i

end
end K1_10_2_2
end PackSource_K1_10_2_2Proof

section PackSource_K1_10_2_1Proof
set_option autoImplicit true
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

/-- Embed the seed variables as the last two variables of a row. -/
private def seedRow : MvPolynomial (Fin 2) L →+* MvPolynomial (Fin 3) L[X] :=
  (rename (Fin.succ : Fin 2 → Fin 3)).toRingHom.comp (MvPolynomial.map Polynomial.C)

/-- Move X into the coefficient ring, keeping Y, S and T as variables. -/
private def regroup : MvPolynomial (Fin 2) (MvPolynomial (Fin 2) L) →+*
    MvPolynomial (Fin 3) L[X] :=
  eval₂Hom seedRow ![C Polynomial.X, MvPolynomial.X 0]

private theorem seedRow_degree (a : MvPolynomial (Fin 2) L) :
    (seedRow a).totalDegree ≤ a.totalDegree := by
  change (rename Fin.succ (MvPolynomial.map Polynomial.C a)).totalDegree ≤ a.totalDegree
  exact (totalDegree_rename_le _ _).trans (Finset.sup_mono (support_map_subset _ _))

end Regroup

private theorem regroup_degree (A : ScalarSource) : (regroup A.poly).totalDegree ≤ 37 := by
  classical
  have hsum : regroup A.poly =
      ∑ e ∈ A.poly.support, regroup (monomial e (A.poly.coeff e)) := by
    conv_lhs => rw [A.poly.as_sum]
    rw [map_sum]
  rw [hsum]
  apply totalDegree_finsetSum_le
  intro e he
  rw [regroup, eval₂Hom_monomial, Finsupp.prod_pow, Fin.prod_univ_two]
  change (seedRow (A.poly.coeff e) *
    ((C (Polynomial.X : K[X]) : Row) ^ e 0 * (MvPolynomial.X (0 : Fin 3) : Row) ^ e 1)).totalDegree ≤ 37
  have hx : ((C (Polynomial.X : K[X]) : Row) ^ e 0).totalDegree = 0 := by
    rw [← map_pow, totalDegree_C]
  calc
    _ ≤ (seedRow (A.poly.coeff e)).totalDegree +
        (((C (Polynomial.X : K[X]) : Row) ^ e 0) * (MvPolynomial.X (0 : Fin 3) : Row) ^ e 1).totalDegree :=
      totalDegree_mul _ _
    _ ≤ (A.poly.coeff e).totalDegree + e 1 := by
      apply Nat.add_le_add (seedRow_degree _)
      exact (totalDegree_mul _ _).trans (by rw [hx, zero_add, totalDegree_X_pow])
    _ ≤ 37 := by simpa only [Nat.add_comm] using A.total e he

section Specialize

variable {R : Type*} [CommRing R]

/-- Specialize the two seed variables, keeping Y as a univariate indeterminate. -/
private def specialize (s t : R) : MvPolynomial (Fin 3) R →+* R[X] :=
  eval₂Hom Polynomial.C ![Polynomial.X, Polynomial.C s, Polynomial.C t]

private theorem eval_specialize (g : MvPolynomial (Fin 3) R) (s t P : R) :
    (specialize s t g).eval P = MvPolynomial.eval ![P, s, t] g := by
  have h : (Polynomial.evalRingHom P).comp (specialize s t) =
      MvPolynomial.eval ![P, s, t] := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [specialize]
    · intro i
      fin_cases i <;> simp [specialize]
  exact RingHom.congr_fun h g

private theorem specialize_pderiv (g : MvPolynomial (Fin 3) R) (s t : R) :
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

private theorem specialize_iterate (s t : R) (g : MvPolynomial (Fin 3) R) (j : ℕ) :
    specialize s t ((pderiv (R := R) (0 : Fin 3))^[j] g) =
      Polynomial.derivative^[j] (specialize s t g) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply', specialize_pderiv, ih]

end Specialize

section DecoderView

variable {L : Type*} [CommRing L]

/-- The usual injective view of L[X,Y] as L[X][Y], with Y outermost. -/
private def decoderView : MvPolynomial (Fin 2) L →+* L[X][X] :=
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

private theorem decoderView_injective : Function.Injective (decoderView (L := L)) :=
  (Polynomial.map_injective _ (uniqueAlgEquiv L (Fin 1)).injective).comp
    ((finSuccEquiv L 1).injective.comp (rename_injective _ Fin.rev_injective))

private theorem decoderView_degree (v : MvPolynomial (Fin 2) L) :
    (decoderView v).natDegree ≤ v.degreeOf 1 := by
  change ((finSuccEquiv L 1 (rename Fin.rev v)).map _).natDegree ≤ v.degreeOf 1
  apply Polynomial.natDegree_map_le.trans
  rw [natDegree_finSuccEquiv, ← show Fin.rev (1 : Fin 2) = 0 by rfl]
  exact (degreeOf_rename_of_injective Fin.rev_injective 1).le

private theorem specialize_regroup (v : MvPolynomial (Fin 2) (MvPolynomial (Fin 2) L))
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

private theorem eval_decoderView (v : MvPolynomial (Fin 2) L) (P : L[X]) :
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
/-- The root of multiplicity μ becomes simple after μ-1 derivatives.
The argument is adapted from the rank-four DerivativeAssignment donor. -/
private theorem exists_simple_derivative {R : Type*} [CommRing R] [IsDomain R]
    (q B : ℕ) [CharP R q] (f : R[X]) (hf : f ≠ 0) (hdegree : f.natDegree ≤ B)
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

theorem proof : K1_10_2.c1 := by
  intro u A Γ F hF
  let g := regroup A.poly
  refine ⟨g, regroup_degree A, ?_⟩
  intro γ hγ
  let P := (F γ hγ).decoder
  let specializeLabel := specialize (Polynomial.C γ) (Polynomial.C (γ ^ p))
  have hview : specializeLabel g = decoderView (A.atLabel γ) :=
    specialize_regroup A.poly γ (γ ^ p)
  have hne : specializeLabel g ≠ 0 := by
    rw [hview]
    intro hz
    exact (hF γ hγ).1 (decoderView_injective (hz.trans (map_zero _).symm))
  have hdegree : (specializeLabel g).natDegree ≤ 5 := by
    rw [hview]
    apply (decoderView_degree _).trans
    rw [degreeOf_eq_sup, Finset.sup_le_iff]
    intro e he
    exact (le_degreeOf_of_mem_support 1 (support_map_subset _ _ he)).trans A.y_degree
  have hroot : (specializeLabel g).IsRoot P := by
    change (specializeLabel g).eval P = 0
    rw [hview, eval_decoderView]
    exact (hF γ hγ).2
  obtain ⟨j, hj, hz, hsep⟩ :=
    exists_simple_derivative p 5 _ hne hdegree (by decide) P hroot
  refine ⟨⟨j, hj⟩, ?_, ?_⟩
  · change MvPolynomial.eval ![P, Polynomial.C γ, Polynomial.C (γ ^ p)]
      (derivativeOrder g ⟨j, hj⟩) = 0
    rw [← eval_specialize, derivativeOrder, specialize_iterate]
    exact hz
  · change MvPolynomial.eval ![P, Polynomial.C γ, Polynomial.C (γ ^ p)]
      (pderiv 0 (derivativeOrder g ⟨j, hj⟩)) ≠ 0
    rw [← eval_specialize, specialize_pderiv, derivativeOrder, specialize_iterate]
    exact hsep

end
end K1_10_2_1
end PackSource_K1_10_2_1Proof

section PackSource_K1_14_4Degrees
set_option autoImplicit true
namespace K1_14_4

noncomputable section

open K1_14 Polynomial MvPolynomial

private abbrev Flat := MvPolynomial (Option (Fin 2)) FX

private def flatten : Equation ≃ₐ[FX] Flat := (optionEquivLeft FX (Fin 2)).symm

private def seedView : Equation ≃ₐ[FX] MvPolynomial (Fin 2) FX[X] :=
  flatten.trans (optionEquivRight FX (Fin 2))

/-- The total degree in the two seed variables, with Y in the coefficient ring. -/
def seedDegree (f : Equation) : ℕ := (seedView f).totalDegree

private theorem seedView_coeff (f : Equation) (i : ℕ) (d : Fin 2 →₀ ℕ) :
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

private theorem flatten_mem_bidegree {g : Equation} {a u : ℕ}
    (ha : g.natDegree ≤ a) (hu : seedDegree g ≤ u) :
    flatten g ∈ restrictBidegree (Fin 2) FX a u := by
  rw [mem_restrictBidegree]
  intro d hd
  have hy : d none ≤ (flatten g).degreeOf none := by
    rw [degreeOf_eq_sup]
    exact Finset.le_sup (f := fun d : Option (Fin 2) →₀ ℕ => d none) hd
  have hyeq := natDegree_optionEquivLeft FX (flatten g)
  have hy' : d none ≤ g.natDegree := hy.trans_eq (by simpa [flatten] using hyeq.symm)
  have hs := le_weightedTotalDegree (fun v : Option (Fin 2) ↦ v.elim 0 fun _ ↦ 1) hd
  rw [Finsupp.weight_elim_zero_one, ← totalDegree_optionEquivRight] at hs
  exact ⟨hy'.trans ha, hs.trans hu⟩

/-- Multiples are counted by the dimension of the entire space of possible quotients.
A nonzero quotient needs both an eligible Y position and sufficient seed degree. -/
theorem rank_multiples_le (C : Submodule FX Equation) {g : Equation} (hg : g ≠ 0)
    {a U spent : ℕ} (hspent : spent ≤ seedDegree g)
    (hC : ∀ c ∈ C, c ≠ 0 → c.natDegree < a ∧ SeedBound c U ∧ g ∣ c) :
    Module.rank FX C ≤ (↑(a * slots U spent) : Cardinal) := by
  have hquot : ∀ c ∈ C, c ≠ 0 → ∃ q : Equation,
      c = g * q ∧ q.natDegree < a ∧ spent + seedDegree q ≤ U := by
    intro c hc hn
    obtain ⟨hY, hU, q, rfl⟩ := hC c hc hn
    have hq : q ≠ 0 := right_ne_zero_of_mul hn
    refine ⟨q, rfl, ?_, ?_⟩
    · rw [Polynomial.natDegree_mul hg hq] at hY
      omega
    · have h := (seedDegree_le_iff _ _).mpr hU
      rw [seedDegree_mul hg hq] at h
      omega
  by_cases h : 0 < a ∧ spent ≤ U
  · let B := restrictBidegree (Fin 2) FX (a - 1) (U - spent)
    let m : B →ₗ[FX] Equation :=
      (LinearMap.mulLeft FX g).comp (flatten.symm.toLinearMap.comp B.subtype)
    have hm : C ≤ LinearMap.range m := by
      intro c hc
      by_cases hn : c = 0
      · rw [hn]
        exact (LinearMap.range m).zero_mem
      · obtain ⟨q, rfl, hq, hqU⟩ := hquot c hc hn
        refine ⟨⟨flatten q, flatten_mem_bidegree (by omega) (by omega)⟩, ?_⟩
        change g * flatten.symm (flatten q) = g * q
        rw [AlgEquiv.symm_apply_apply]
    have hB : Module.finrank FX B = a * slots U spent := by
      rw [MvPolynomial.finrank_restrictBidegree, slots, ite_eq_left h.2]
      simp [Nat.choose_two_right, triangle, Nat.mul_comm (U - spent + 2), show a - 1 + 1 = a by omega]
    calc
      _ ≤ Module.rank FX (LinearMap.range m) := Submodule.rank_mono hm
      _ ≤ Module.rank FX B := rank_range_le m
      _ = _ := by rw [← Module.finrank_eq_rank, hB]
  · have hc : C = ⊥ := by
      apply bot_unique
      intro c hmem
      rw [Submodule.mem_bot]
      by_contra hn
      obtain ⟨q, _, hq, hqU⟩ := hquot c hmem hn
      exact h ⟨by omega, by omega⟩
    rw [hc]
    simp

end
end K1_14_4
end PackSource_K1_14_4Degrees

section PackSource_K1_14_2_2RGraphs
set_option autoImplicit true
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

/-- Transfer a coprime jet pair to the four-variable ambient ring. -/
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

/-- An ordinary branch is a proper pair of shapes (b,0,u) and (b,1,u).
Its two equations vanish throughout every parent charged here. -/
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

/-- Peel one multiplicity-r factor at a time. The parents on that factor
use a single graph. On the complement every witnessed high factor is
coprime to the peeled factor and still divides the smaller product. -/
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
end PackSource_K1_14_2_2RGraphs

section PackSource_K1_14_2_2_4_3Factors
set_option autoImplicit true
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
/-- If an ordinary equation vanishes on a seed-dominant parent, the contraction
of that parent to the ordinary ring is generated by one positive-ordinate factor. -/
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
  let Q := P.map (algebraMap Equation SeedField[X])
  have : Q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint S SeedField[X] P inferInstance hdisj
  have hle := Ideal.height_le_ringKrullDim_of_isPrime (I := Q)
  have hdim : ringKrullDim SeedField[X] = 1 := by simp [ringKrullDim_eq_zero_of_field]
  rw [hdim] at hle
  have hheight : Ideal.height (R := SeedField[X]) Q = Ideal.height (R := Equation) P :=
    IsLocalization.height_map_of_disjoint (R := Equation) (S := SeedField[X]) S P hdisj
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

/-- All copies of the factor through the parent are isolated in one power.
The remaining factor is a unit at the parent. -/
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
end PackSource_K1_14_2_2_4_3Factors

section PackSource_K1_14_4Ranks
set_option autoImplicit true
namespace K1_14_4

noncomputable section

open K1_14 Polynomial Finset

section Filtration

variable {F A : Type*} [Field F] [CommRing A] [Algebra F A]

private def filtered (V : Submodule F A[X]) (n : ℕ) : Submodule F A[X] :=
  V ⊓ (degreeLT A n).restrictScalars F

private theorem mem_filtered {V : Submodule F A[X]} {P : A[X]} {n : ℕ} :
    P ∈ filtered V n ↔ P ∈ V ∧ P.degree < n :=
  and_congr_right fun _ => mem_degreeLT

private def gradeMap (V : Submodule F A[X]) (j : ℕ) :
    filtered V (j + 1) →ₗ[F] A :=
  ((lcoeff A j).restrictScalars F).comp (filtered V (j + 1)).subtype

private theorem gradeMap_ker_rank (V : Submodule F A[X]) (j : ℕ) :
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

private theorem filtered_rank_le (V : Submodule F A[X]) (g : ℕ → ℕ)
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

private theorem finrank_le_grades (V : Submodule F A[X]) (g : ℕ → ℕ) (n : ℕ)
    (h : ∀ j, Module.rank F (gradeMap V j).range ≤ (↑(g j) : Cardinal))
    (hdeg : ∀ P ∈ V, P.degree < n) :
    Module.finrank F V ≤ ∑ j ∈ range n, g j := by
  have heq : filtered V n = V :=
    inf_eq_left.mpr fun P hp => mem_degreeLT.mpr (hdeg P hp)
  have hr := filtered_rank_le V g h n
  rw [heq] at hr
  exact Module.finrank_le_of_rank_le hr

end Filtration

private theorem ranks_lt_gradeWidth {d j k B W : ℕ} (hk : 0 < k)
    (hB : d + j ≤ B) (hW : (d + j) * k ≤ W + j) :
    d < gradeWidth k B W j := by
  have hd := (Nat.le_div_iff_mul_le hk).2 hW
  unfold gradeWidth
  omega

private theorem ranks_range_rank_at (k v B U s W j : ℕ) (e : ℕ → ℕ) (V : Submodule FX Jet)
    {f : Equation} (hf : f ≠ 0) (hv : s + 1 ≤ seedDegree f)
    (hk : 0 < k)
    (hV : ∀ P ∈ V, P ≠ 0 →
      P.natDegree ≤ v ∧
      P.leadingCoeff.natDegree + P.natDegree ≤ B ∧
      (P.leadingCoeff.natDegree + P.natDegree) * (k) ≤ W + P.natDegree ∧
      SeedBound P.leadingCoeff U ∧
      f ^ e P.natDegree ∣ P.leadingCoeff) :
    Module.rank FX (gradeMap (F := FX) (A := Equation) V j).range ≤
      (↑(gradeWidth k B W j * slots U (e j * (s + 1))) : Cardinal) := by
  apply rank_multiples_le _ (pow_ne_zero (e j) hf)
  · rw [seedDegree_pow hf]
    exact Nat.mul_le_mul_left _ hv
  · rintro c ⟨⟨P, hP⟩, rfl⟩ hc
    change P.coeff j ≠ 0 at hc
    obtain ⟨hpV, hd⟩ := mem_filtered.mp hP
    have hp : P ≠ 0 := by
      intro hz
      exact hc (by simp [hz])
    have hj : P.natDegree = j :=
      le_antisymm (Nat.le_of_lt_succ ((natDegree_lt_iff_degree_lt hp).2 hd))
        (le_natDegree_of_ne_zero hc)
    obtain ⟨_, hB, hwidth, hseed, hdvd⟩ := hV P hpV hp
    rw [hj] at hB hwidth hdvd
    change (P.coeff j).natDegree < _ ∧ SeedBound (P.coeff j) _ ∧ _ ∣ P.coeff j
    rw [← hj, coeff_natDegree, hj]
    exact ⟨ranks_lt_gradeWidth hk hB hwidth, hseed, hdvd⟩

private theorem gradeMap_range_rank (w : ℤ) (W j : ℕ) (V : Submodule FX Jet)
    {f : Equation} (hf : f ≠ 0) (hv : (band w).seedBound + 1 ≤ seedDegree f)
    (hk : 0 < 131071 - w.toNat)
    (hV : ∀ P ∈ V, P ≠ 0 →
      P.natDegree ≤ (band w).vBound ∧
      P.leadingCoeff.natDegree + P.natDegree ≤ (band w).jetBound ∧
      (P.leadingCoeff.natDegree + P.natDegree) * (131071 - w.toNat) ≤ W + P.natDegree ∧
      SeedBound P.leadingCoeff (band w).subbankSeeds ∧
      f ^ forcedPower w W P.natDegree ∣ P.leadingCoeff) :
    Module.rank FX (gradeMap (F := FX) (A := Equation) V j).range ≤
      (↑(gradeCapacity w W j) : Cardinal) := by
  exact ranks_range_rank_at (131071 - w.toNat) (band w).vBound (band w).jetBound
    (band w).subbankSeeds (band w).seedBound W j (forcedPower w W) V hf hv hk hV

/-- Sum the rank bounds of the V-graded pieces at one cutoff. -/
theorem cutoff_finrank_le (w : ℤ) (W : ℕ) (V : Submodule FX Jet)
    {f : Equation} (hf : f ≠ 0) (hv : (band w).seedBound + 1 ≤ seedDegree f)
    (hk : 0 < 131071 - w.toNat)
    (hV : ∀ P ∈ V, P ≠ 0 →
      P.natDegree ≤ (band w).vBound ∧
      P.leadingCoeff.natDegree + P.natDegree ≤ (band w).jetBound ∧
      (P.leadingCoeff.natDegree + P.natDegree) * (131071 - w.toNat) ≤ W + P.natDegree ∧
      SeedBound P.leadingCoeff (band w).subbankSeeds ∧
      f ^ forcedPower w W P.natDegree ∣ P.leadingCoeff) :
    Module.finrank FX V ≤ cutoffCapacity w W := by
  unfold cutoffCapacity
  refine finrank_le_grades (F := FX) (A := Equation) V (gradeCapacity w W)
    ((band w).vBound + 1) ?_ ?_
  · intro j
    exact gradeMap_range_rank w W j V (f := f) hf hv hk hV
  · intro P hp
    by_cases hn : P = 0
    · simp [hn]
    · exact (natDegree_lt_iff_degree_lt hn).1 (Nat.lt_succ_of_le (hV P hp hn).1)

end
end K1_14_4
end PackSource_K1_14_4Ranks

section PackSource_K1_4Proof
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

namespace K1_4

open Polynomial FrobeniusLocator

theorem proof : K1.c4 := by
  intro u Γ hprincipal hΓ
  obtain ⟨a, g, hg, hga, ha, hkernel⟩ := hprincipal
  have hsum : a + (81879 - a) = 81879 := by omega
  have hcertificate : Native.GenericPrincipalCertificate (u 0) (u 1) := by
    refine ⟨a, 81879 - a, hsum, ⟨{
      generator := g
      nonzero := hg
      degree_bound := hga
      kernel_eq := ?_
    }⟩⟩
    intro f
    rw [hsum, Principal.recurrence_kernel_iff_matrix, Principal.recurrenceMatrix_parameter]
    change (f.natDegree ≤ 81879 ∧
      ((K1.twoBlock u).map (algebraMap K1.K[X] K1.Frac)).mulVec
        (fun i => f.coeff i.val) = 0) ↔
      ∃ Q : K1.Frac[X], Q.natDegree ≤ 81879 - a ∧ f = g * Q
    constructor
    · rintro ⟨hf, hker⟩
      exact (hkernel f hf).mp hker
    · rintro ⟨Q, hQ, rfl⟩
      have hdegree : (g * Q).natDegree ≤ 81879 :=
        natDegree_mul_le.trans ((Nat.add_le_add hga hQ).trans_eq hsum)
      exact ⟨hdegree, (hkernel _ hdegree).mpr ⟨Q, hQ, rfl⟩⟩
  exact (Native.native_generic_principal_MCA_count u hcertificate Γ hΓ).trans (by norm_num)

end K1_4
end PackSource_K1_4Proof

section PackSource_K1_13_7_6_2Defs
set_option autoImplicit true
set_option autoImplicit false

namespace K1_13_7_6_2
noncomputable section

open K1_13_7

/-- The minimal primes of a prefix, regarded as points of the spectrum. -/
def minPrimes (J : Ideal Lower) : Finset (PrimeSpectrum Lower) :=
  ((J.finite_minimalPrimes_of_isNoetherianRing).preimage
    (f := PrimeSpectrum.asIdeal) (by
      intro p _ q _ hpq
      exact PrimeSpectrum.ext_iff.mpr hpq)).toFinset

@[simp] theorem mem_minPrimes (J : Ideal Lower) (p : PrimeSpectrum Lower) :
    p ∈ minPrimes J ↔ p.asIdeal ∈ J.minimalPrimes :=
  Set.Finite.mem_toFinset _

/-- The minimal primes of a prefix that survive localization at the next prime. -/
def precedingPrimes (J : Ideal Lower) (q : PrimeSpectrum Lower) :
    Finset (PrimeSpectrum Lower) := by
  classical
  exact (minPrimes J).filter (fun p => p.asIdeal ≤ q.asIdeal)

theorem mem_precedingPrimes (J : Ideal Lower) (q p : PrimeSpectrum Lower) :
    p ∈ precedingPrimes J q ↔ p.asIdeal ∈ J.minimalPrimes ∧ p.asIdeal ≤ q.asIdeal := by
  classical
  rw [precedingPrimes, Finset.mem_filter, mem_minPrimes]

/-- Multiplication by the next equation is injective on the localized prefix quotient. -/
def RegularCut (q : PrimeSpectrum Lower) (J : Ideal Lower) (t : Lower) : Prop :=
  let A := Localization.AtPrime q.asIdeal
  IsSMulRegular (A ⧸ J.map (algebraMap Lower A)) (algebraMap Lower A t)

end
end K1_13_7_6_2
end PackSource_K1_13_7_6_2Defs
