import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.IntegralPointLifting
import ProximityPrize.SubmissionLower.LocalMathlib_RingTheory_RamificationInertia_Inertia
import ProximityPrize.SubmissionLower.LocalMathlib_NumberTheory_RamificationInertia_Inertia


/-!
# Unit inertia weights above actual constant-field points

Model label: gpt-5.

For an actual K-point phi of R, an integral R-algebra S, and a maximal
ideal P lying over ker(phi), the quotient S/P is proved integral over K.
If K is algebraically closed, constants already surject onto S/P.
Consequently the actual inertia degree over R equals one.

No residue-field isomorphism upstairs, finrank, or unit-weight statement
is assumed. These generic facts will be instantiated at the actual
finite and infinity base points.
-/

namespace ProximityPrize.SubmissionLower.UnitResidueWeights

open scoped Classical

noncomputable section

variable {K R S : Type*} [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
variable [Algebra.IsIntegral R S]

/-- The actual quotient above the point is integral over its constant
field, by mapping the monic relations and using the proved scalar square. -/
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

/-- The actual inertia degree is one, proved through the actual
quotient algebra map rather than postulated as a residue weight. -/
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

/-- The older ramification-sum API uses inertiaDeg'; its weight is
identified with the same proved unit value. -/
theorem inertiaDeg'_eq_one_of_point_fiber (phi : R →ₐ[K] K) (P : Ideal S)
    [P.IsMaximal]
    (hP : P.comap (algebraMap R S) = RingHom.ker phi.toRingHom) :
    (RingHom.ker phi.toRingHom).inertiaDeg' P = 1 := by
  letI : (RingHom.ker phi.toRingHom).IsMaximal :=
    IntegralPointLifting.pointKernel_isMaximal phi
  letI : P.LiesOver (RingHom.ker phi.toRingHom) := ⟨hP.symm⟩
  rw [Ideal.inertiaDeg'_eq_inertiaDeg]
  exact inertiaDeg_eq_one_of_point_fiber phi P hP

end

end ProximityPrize.SubmissionLower.UnitResidueWeights
