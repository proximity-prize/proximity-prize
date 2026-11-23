import ProximityPrize.SubmissionLower.R6960NormalizedFiber
import Mathlib.RingTheory.Localization.NumDen

noncomputable section
set_option Elab.async false
namespace Lower6960.ChartIntegrality
open Polynomial
open scoped Polynomial
variable {A F E : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
    [Field F] [Algebra A F] [IsFractionRing A F] [Field E] [Algebra F E]
    [Algebra A E] [IsScalarTower A F E] [FiniteDimensional F E]

private theorem in_base (v : F) (loc : ∀ q : A,Irreducible q →
    ∃ d c : A, ¬q∣d ∧ algebraMap A F c=v*algebraMap A F d) :
    ∃ c : A,algebraMap A F c=v := by
  classical
  let a:=IsFractionRing.num A v
  let b:A:=IsFractionRing.den A v
  let i:=algebraMap A F
  have inj:=IsFractionRing.injective A F
  have nb : b≠0 := mem_nonZeroDivisors_iff_ne_zero.mp (IsFractionRing.den A v).property
  have eq : i a=v*i b := (div_eq_iff ((map_ne_zero_iff _ inj).mpr nb)).mp (IsFractionRing.mk'_num_den' A v)
  have unit : IsUnit b := by
    by_contra nu
    obtain ⟨q,ir,dv⟩ := WfDvdMonoid.exists_irreducible_factor nu nb
    obtain ⟨d,c,nd,hc⟩ := loc q ir
    have cross : a*d=c*b := inj (by
      change i (a*d)=i (c*b); rw [map_mul,map_mul,eq,hc]; ring)
    have product : q∣a*d := cross ▸ dv.trans (dvd_mul_left ..)
    have qa := (ir.prime.dvd_mul.mp product).resolve_right nd
    exact ir.not_isUnit (IsFractionRing.num_den_reduced A v qa dv)
  obtain ⟨u,hu⟩ := unit
  refine ⟨a*↑u⁻¹,?_⟩
  rw [map_mul,eq,←hu,mul_assoc,←map_mul,Units.mul_inv,map_one,mul_one]

/-- Normalization on the affine plane can be tested one irreducible base
divisor at a time. Different monic ordinate coordinates can therefore be
used at different abscissa places. -/
theorem integral_from_places (F : Type*) [Field F] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [IsScalarTower A F E] [FiniteDimensional F E]
    (x : E) (loc : ∀ q : A,Irreducible q →
      ∃ d : A, ¬q∣d ∧ IsIntegral A (algebraMap A E d*x)) : IsIntegral A x := by
  let ι:=algebraMap A F
  have inj : Function.Injective ι := IsFractionRing.injective A F
  have : FaithfulSMul A E := (faithfulSMul_iff_algebraMap_injective A E).mpr
    (by rw [IsScalarTower.algebraMap_eq A F E]; exact (algebraMap F E).injective.comp inj)
  let f:=minpoly F x
  have intF : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have lift : f∈Polynomial.lifts ι := by
    apply (lifts_iff_coeff_lifts _).mpr
    intro j
    apply in_base (f.coeff j)
    intro q ir
    obtain ⟨d,nd,di⟩ := loc q ir
    have dn : d≠0 := fun eq=>nd (eq ▸ dvd_zero _)
    let n:=f.natDegree-j
    refine ⟨d^n,(minpoly A (algebraMap A E d*x)).coeff j,
      fun div=>nd (ir.prime.dvd_of_dvd_pow div),?_⟩
    have mp:=minpoly.isIntegrallyClosed_eq_field_fractions' F di
    have scale : algebraMap A E d*x=ι d • x := by
      simp only [ι,Algebra.smul_def,←IsScalarTower.algebraMap_apply]
    rw [scale,IsIntegrallyClosed.minpoly_smul ((map_ne_zero_iff _ inj).mpr dn) intF] at mp
    have c:=congrArg (fun g : F[X]=>g.coeff j) mp
    simpa only [n,f,scale,coeff_map,coeff_scaleRoots,map_pow,ι] using c.symm
  obtain ⟨g,hg⟩:=lift
  change g.map ι=f at hg
  have monic : g.Monic := inj.monic_map_iff.mpr (hg ▸ minpoly.monic intF)
  refine ⟨g,monic,?_⟩
  have root : aeval x f=0 := minpoly.aeval F x
  rwa [←hg,aeval_map_algebraMap] at root

#print axioms integral_from_places
end Lower6960.ChartIntegrality
