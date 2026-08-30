import ProximityPrize.SubmissionLower.IntegralPointLifting
import ProximityPrize.SubmissionLower.InfinityResidueField
import ProximityPrize.SubmissionLower.CoordinatePlaceClassification

namespace ProximityPrize.SubmissionLower.NormalizationUnitWeights

open scoped Classical BigOperators WithZero
open IsDedekindDomain

noncomputable section

section PointFiber

variable {K R S : Type*} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable [Algebra.IsIntegral R S]

theorem pointFiber_quotient_integral (phi : R →ₐ[K] K) (P : Ideal S)
    (hP : P.comap (algebraMap R S) = RingHom.ker phi.toRingHom) :
    Algebra.IsIntegral K (S ⧸ P) := by
  have hcomp : (algebraMap K (S ⧸ P)).comp phi.toRingHom =
      (Ideal.Quotient.mk P).comp (algebraMap R S) := by
    ext r
    exact (IntegralPointLifting.quotient_scalar_compatibility phi P hP r).symm
  constructor
  intro z
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact IsIntegral.map_of_comp_eq phi.toRingHom (Ideal.Quotient.mk P) hcomp
    (Algebra.IsIntegral.isIntegral (R := R) s)

variable [IsAlgClosed K]

theorem pointFiber_constants_surjective (phi : R →ₐ[K] K) (P : Ideal S)
    [P.IsMaximal]
    (hP : P.comap (algebraMap R S) = RingHom.ker phi.toRingHom) :
    Function.Surjective (algebraMap K (S ⧸ P)) := by
  letI : Algebra.IsIntegral K (S ⧸ P) := pointFiber_quotient_integral phi P hP
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := S ⧸ P)).2

theorem inertiaDeg_eq_one_of_point_fiber (phi : R →ₐ[K] K) (P : Ideal S)
    [P.IsMaximal]
    (hP : P.comap (algebraMap R S) = RingHom.ker phi.toRingHom) :
    P.inertiaDeg R = 1 := by
  let p : Ideal R := RingHom.ker phi.toRingHom
  letI : p.IsMaximal := IntegralPointLifting.pointKernel_isMaximal phi
  letI : P.LiesOver p := ⟨hP.symm⟩
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI : Field (S ⧸ P) := Ideal.Quotient.field P
  have hsurj : Function.Surjective (algebraMap (R ⧸ p) (S ⧸ P)) := by
    intro z
    obtain ⟨c, hc⟩ := pointFiber_constants_surjective phi P hP z
    refine ⟨algebraMap K (R ⧸ p) c, ?_⟩
    rw [← IsScalarTower.algebraMap_apply K (R ⧸ p) (S ⧸ P), hc]
  rw [Ideal.inertiaDeg_eq_of_isMaximal p P]
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
    ⟨(algebraMap (R ⧸ p) (S ⧸ P)).injective, hsurj⟩

end PointFiber

variable (K : Type*) [Field K]

abbrev InfinityBase := FixedCurveNormSum.InfinityBase K

local instance : Algebra K (InfinityBase K) :=
  (InfinityResidueField.constantMap K).toAlgebra

def infinityBasePoint : InfinityBase K →ₐ[K] K where
  toRingHom := (InfinityResidueField.residueEquiv K).symm.toRingHom.comp
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (InfinityBase K)))
  commutes' c := by
    change (InfinityResidueField.residueEquiv K).symm
      (InfinityResidueField.residueEquiv K c) = c
    exact RingEquiv.symm_apply_apply _ _

theorem infinityBasePoint_kernel :
    RingHom.ker (infinityBasePoint K).toRingHom =
      (FixedCurveNormSum.infinityPlace K).asIdeal := by
  ext r
  change (InfinityResidueField.residueEquiv K).symm
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (InfinityBase K)) r) = 0 ↔
    r ∈ IsLocalRing.maximalIdeal (InfinityBase K)
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (InfinityResidueField.residueEquiv K).symm.injective
    simpa only [map_zero] using h
  · intro h
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

variable [IsAlgClosed K]

theorem finiteBase_natDegree_eq_one (f : Polynomial K) (hf : Irreducible f) :
    f.natDegree = 1 :=
  Polynomial.natDegree_eq_of_degree_eq_some
    (IsAlgClosed.degree_eq_one_of_irreducible K hf)

theorem finiteBase_exists_point (p : HeightOneSpectrum (Polynomial K)) :
    ∃ phi : Polynomial K →ₐ[K] K, RingHom.ker phi.toRingHom = p.asIdeal := by
  obtain ⟨f, hf, hm, hplace⟩ := RatFuncProductFormula.exists_monic_primePlace K p
  obtain ⟨alpha, hroot⟩ := IsAlgClosed.exists_root f (by
    rw [IsAlgClosed.degree_eq_one_of_irreducible K hf]
    exact one_ne_zero)
  let phi : Polynomial K →ₐ[K] K := Polynomial.aeval alpha
  have hkermax : (RingHom.ker phi.toRingHom).IsMaximal :=
    IntegralPointLifting.pointKernel_isMaximal phi
  have hle : p.asIdeal ≤ RingHom.ker phi.toRingHom := by
    rw [← hplace]
    change Ideal.span {f} ≤ RingHom.ker phi.toRingHom
    apply (Ideal.span_singleton_le_iff_mem (I := RingHom.ker phi.toRingHom)).mpr
    change f.eval alpha = 0
    exact hroot
  refine ⟨phi, ?_⟩
  exact ((p.isPrime.isMaximal p.ne_bot).eq_of_le hkermax.ne_top hle).symm

variable (L : Type*) [Field L]
variable [Algebra K L] [Algebra (Polynomial K) L] [Algebra (RatFunc K) L]
variable [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L]
variable [IsScalarTower (Polynomial K) (RatFunc K) L]
variable [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L]

abbrev FiniteNormalization := FixedCurveNormSum.FiniteNormalization K L

abbrev InfiniteNormalization := FixedCurveNormSum.InfiniteNormalization K L

omit [Algebra K L] [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L] in
theorem finitePlace_inertia_one
    (q : HeightOneSpectrum (FiniteNormalization K L)) :
    q.asIdeal.inertiaDeg (Polynomial K) = 1 := by
  letI : Algebra K (FiniteNormalization K L) :=
    ((algebraMap (Polynomial K) (FiniteNormalization K L)).comp Polynomial.C).toAlgebra
  letI : IsScalarTower K (Polynomial K) (FiniteNormalization K L) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : q.asIdeal.IsMaximal := q.isPrime.isMaximal q.ne_bot
  obtain ⟨phi, hphi⟩ := finiteBase_exists_point K
    (HeightOneSpectrum.under (Polynomial K) q)
  apply inertiaDeg_eq_one_of_point_fiber phi q.asIdeal
  exact hphi.symm

omit [Algebra K L] [Algebra (Polynomial K) L] [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L] [IsScalarTower (Polynomial K) (RatFunc K) L] [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L] in
theorem infinitePlace_inertia_one
    (q : HeightOneSpectrum (InfiniteNormalization K L)) :
    q.asIdeal.inertiaDeg (InfinityBase K) = 1 := by
  letI : Algebra K (InfiniteNormalization K L) :=
    ((algebraMap (InfinityBase K) (InfiniteNormalization K L)).comp
      (algebraMap K (InfinityBase K))).toAlgebra
  letI : IsScalarTower K (InfinityBase K) (InfiniteNormalization K L) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : q.asIdeal.IsMaximal := q.isPrime.isMaximal q.ne_bot
  letI := CoordinatePlaceClassification.infinitePlace_liesOver K L q
  apply inertiaDeg_eq_one_of_point_fiber
    (infinityBasePoint K) q.asIdeal
  rw [infinityBasePoint_kernel]
  exact (Ideal.over_def q.asIdeal (FixedCurveNormSum.infinityPlace K).asIdeal).symm

omit [Algebra K L] [Algebra (Polynomial K) L] [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L] [IsScalarTower (Polynomial K) (RatFunc K) L] [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L] in
theorem infinitePlace_inertia'_one
    (q : HeightOneSpectrum (InfiniteNormalization K L)) :
    (FixedCurveNormSum.infinityPlace K).asIdeal.inertiaDeg' q.asIdeal = 1 := by
  letI : q.asIdeal.IsMaximal := q.isPrime.isMaximal q.ne_bot
  letI := CoordinatePlaceClassification.infinitePlace_liesOver K L q
  rw [Ideal.inertiaDeg'_eq_inertiaDeg]
  exact infinitePlace_inertia_one K L q

omit [Algebra K L] [Algebra (Polynomial K) L] [IsScalarTower K (Polynomial K) L] [IsScalarTower K (RatFunc K) L] [IsScalarTower (Polynomial K) (RatFunc K) L] in
theorem infiniteFiber_weight_one
    (Q : {Q : Ideal (InfiniteNormalization K L) //
      Q ∈ IsDedekindDomain.primesOverFinset
        (FixedCurveNormSum.infinityPlace K).asIdeal (InfiniteNormalization K L)}) :
    (Q.1.inertiaDeg (InfinityBase K) : ℤ) = 1 := by
  have hQ := infinitePlace_inertia_one K L
    (NormValuationTransport.placeAbove (InfinityBase K) (InfiniteNormalization K L)
      (FixedCurveNormSum.infinityPlace K) Q)
  exact_mod_cast hQ

end

end ProximityPrize.SubmissionLower.NormalizationUnitWeights
