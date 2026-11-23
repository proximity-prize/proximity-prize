import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Ideal.Quotient.Basic

noncomputable section
set_option Elab.async false
namespace Lower6960.NormalizedFiber
open Polynomial
open scoped Polynomial

section
variable {A F : Type*} [CommRing A] [Field F]
private theorem clear_coeff [DecompositionMonoid A] (ι : A→+*F) (inj : Function.Injective ι) (a b : A) (ne : a≠0)
    (cop : IsRelPrime a b) (v : F) {u w : A} (hu : ι u=v*ι a) (hw : ι w=v*ι b) :
    ∃ q : A,ι q=v := by
  have cross : u*b=w*a := inj (by rw [map_mul,map_mul,hu,hw]; ring)
  have divides : a∣u*b := cross ▸ dvd_mul_left a w
  obtain ⟨q,hq⟩ := cop.dvd_of_dvd_mul_right divides
  refine ⟨q, mul_right_cancel₀ ((map_ne_zero_iff ι inj).mpr ne) ?_⟩
  rw [←hu,hq,map_mul,mul_comm]

variable [IsDomain A] [UniqueFactorizationMonoid A] {E : Type*} [Field E] [Algebra A E]

/-- Two relatively prime denominator clearings of the same element suffice
for integrality over the base. This uses no Bezout identity in the plane. -/
theorem integral_of_coprime_clearings (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra K E] [IsScalarTower A K E] [FiniteDimensional K E]
    {a b : A} (na : a≠0) (nb : b≠0) (cop : IsRelPrime a b) (v : E)
    (ca : IsIntegral A (algebraMap A E a*v)) (cb : IsIntegral A (algebraMap A E b*v)) :
    IsIntegral A v := by
  let ι:=algebraMap A K
  let p:=minpoly K v
  have inj : Function.Injective ι := IsFractionRing.injective A K
  have : FaithfulSMul A E := (faithfulSMul_iff_algebraMap_injective A E).mpr
    (by rw [IsScalarTower.algebraMap_eq A K E]; exact (algebraMap K E).injective.comp inj)
  have vint : IsIntegral K v := Algebra.IsIntegral.isIntegral v
  have scaled (c : A) (cn : c≠0) (ci : IsIntegral A (algebraMap A E c*v)) (i : ℕ) :
      ι ((minpoly A (algebraMap A E c*v)).coeff i) = p.coeff i*ι (c^(p.natDegree-i)) := by
    have idpoly := minpoly.isIntegrallyClosed_eq_field_fractions' K ci
    have eq : algebraMap A E c*v = ι c • v := by
      simp only [ι,Algebra.smul_def,←IsScalarTower.algebraMap_apply]
    rw [eq,IsIntegrallyClosed.minpoly_smul ((map_ne_zero_iff ι inj).mpr cn) vint] at idpoly
    have d := congrArg (fun q : K[X]=>q.coeff i) idpoly
    simpa only [p,eq,coeff_map,coeff_scaleRoots,map_pow,ι] using d.symm
  have lift : p∈Polynomial.lifts ι := by
    apply (lifts_iff_coeff_lifts _).mpr
    intro i
    let n:=p.natDegree-i
    have disjoint : IsRelPrime (a^n) b := cop.pow_left
    exact clear_coeff ι inj (a^n) (b^n) (pow_ne_zero _ na) disjoint.pow_right
      (p.coeff i) (scaled a na ca i) (scaled b nb cb i)
  obtain ⟨q,hq⟩ := lift
  change q.map ι=p at hq
  have monic : q.Monic := by
    apply inj.monic_map_iff.mpr
    rw [hq]; exact minpoly.monic vint
  refine ⟨q,monic,?_⟩
  have root := minpoly.aeval K v
  rw [←show p=minpoly K v from rfl,←hq,aeval_map_algebraMap] at root
  exact root

/-- Divisibility by a base parameter in the normalized order is saturated
with respect to every relatively prime multiplier in the base. -/
theorem cancel_on_normalization (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra K E] [IsScalarTower A K E] [FiniteDimensional K E]
    {a b : A} (na : a≠0) (nb : b≠0) (cop : IsRelPrime a b)
    (u : integralClosure A E)
    (div : algebraMap A (integralClosure A E) a ∣ algebraMap A (integralClosure A E) b*u) :
    algebraMap A (integralClosure A E) a∣u := by
  obtain ⟨s,eq⟩ := div
  have inj : Function.Injective (algebraMap A E) := by
    rw [IsScalarTower.algebraMap_eq A K E]
    exact (algebraMap K E).injective.comp (IsFractionRing.injective A K)
  have av := (map_ne_zero_iff _ inj).mpr na
  let v := (u:E)/algebraMap A E a
  have aa : algebraMap A E a*v=u := by dsimp [v]; field_simp
  have bb : algebraMap A E b*v=s := by
    have eq' : algebraMap A E b*(u:E)=algebraMap A E a*(s:E) := congrArg Subtype.val eq
    dsimp [v]
    field_simp
    simpa only [mul_comm (s:E)] using eq'
  have vi := integral_of_coprime_clearings K na nb cop v (aa ▸ u.property) (bb ▸ s.property)
  exact ⟨⟨v,vi⟩,Subtype.ext aa.symm⟩
end

#print axioms integral_of_coprime_clearings
#print axioms cancel_on_normalization

section Plane
variable {k : Type*} [Field k]
abbrev Plane (k : Type*) [Field k] := Polynomial k[X]
variable (E : Type*) [Field E] [Algebra (Plane k) E]
abbrev Order (k E : Type*) [Field k] [Field E] [Algebra (Plane k) E] := integralClosure (Plane k) E

def sliceIdeal (z : k) : Ideal (Order k E) :=
  Ideal.span {algebraMap (Plane k) (Order k E) (Polynomial.X-C (C z))}

abbrev Fiber (z : k) : Type _ := @HasQuotient.Quotient (↥(Order k E)) _
  (Ideal.instHasQuotient (R:=↥(Order k E))) (sliceIdeal E z)

def quotientMap (z : k) := @Ideal.Quotient.mk (↥(Order k E)) (Order k E).toRing (sliceIdeal E z)
theorem quotientMap_surjective (z : k) : Function.Surjective (quotientMap E z) :=
  fun u=>Ideal.Quotient.mk_surjective u

def baseMap (z : k) : k[X] →+* Fiber E z :=
  ((Ideal.Quotient.mk _).comp (algebraMap (Plane k) (Order k E))).comp C

variable [Algebra (FractionRing (Plane k)) E] [IsScalarTower (Plane k) (FractionRing (Plane k)) E]
    [FiniteDimensional (FractionRing (Plane k)) E]

/-- Every scalar fibre of the true integral closure is torsion-free over
the abscissa line, including at a branch collision. -/
theorem torsion_free (z : k) (q : k[X]) (nz : q≠0) (u : Fiber E z)
    (zero : baseMap E z q * u=0) : u=0 := by
  obtain ⟨v,rfl⟩ := Ideal.Quotient.mk_surjective u
  let a : Plane k := Polynomial.X-C (C z)
  let b : Plane k := C q
  have div : algebraMap (Plane k) (Order k E) a ∣ (algebraMap (Plane k) (Order k E) b)*v :=
    Ideal.mem_span_singleton.mp ((Ideal.Quotient.eq_zero_iff_mem).mp
      (show Ideal.Quotient.mk (sliceIdeal E z) (_*v)=0 by
        simpa only [map_mul,baseMap,b,RingHom.comp_apply] using zero))
  have an : a≠0 := X_sub_C_ne_zero _
  have bn : b≠0 := C_ne_zero.mpr nz
  have cop : IsRelPrime a b := (irreducible_X_sub_C _).isRelPrime_iff_not_dvd.mpr (by
    intro h
    exact nz (by simpa [b,Polynomial.IsRoot] using (dvd_iff_isRoot.mp h)))
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.mem_span_singleton.mpr
    (cancel_on_normalization (FractionRing (Plane k)) an bn cop v div)

omit [Algebra (FractionRing (Plane k)) E] [IsScalarTower (Plane k) (FractionRing (Plane k)) E]
    [FiniteDimensional (FractionRing (Plane k)) E] in
private theorem specialize (z : k) (f : Plane k) :
    Ideal.Quotient.mk (sliceIdeal E z) (algebraMap (Plane k) (Order k E) f) =
      baseMap E z (f.eval (C z)) := by
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_span_singleton.mpr
  have h := map_dvd (algebraMap (Plane k) (Order k E)) (X_sub_C_dvd_sub_C_eval (a:=C z) (p:=f))
  simpa only [map_sub] using h

private theorem finite_image {A R M N : Type*} [Semiring A] [Semiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module A M] [Module R N] [source : Module.Finite A M]
    (f : M →+ N) (surj : Function.Surjective f) (specializeScalar : A→R)
    (compat : ∀ a v,f (a • v)=specializeScalar a • f v) : Module.Finite R N := by
  classical
  obtain ⟨s,span⟩ := source.1
  let t:=s.image f
  refine ⟨⟨t,top_unique ?_⟩⟩
  intro u trivialMem
  clear trivialMem
  obtain ⟨v,rfl⟩ := surj u
  have inside : v∈Submodule.span A (s : Set M) := span ▸ Submodule.mem_top
  induction inside using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (Finset.mem_image_of_mem f hx)
  | zero => exact f.map_zero ▸ Submodule.zero_mem _
  | add a b _ _ ha hb => exact (f.map_add a b) ▸ Submodule.add_mem _ ha hb
  | smul c a _ ha => exact (compat c a) ▸ Submodule.smul_mem _ _ ha

set_option maxHeartbeats 1400000 in
/-- Each scalar fibre is finite free over the abscissa polynomial ring.
Finite generation comes from normalization in a finite separable extension;
the base coefficients specialize by polynomial division. -/
theorem finite_free [Algebra.IsSeparable (FractionRing (Plane k)) E] (z : k) :
    letI : Module k[X] (Fiber E z) := Module.compHom (Fiber E z) (baseMap E z)
    Module.Finite k[X] (Fiber E z) ∧ Module.Free k[X] (Fiber E z) := by
  classical
  let : Module k[X] (Fiber E z) := Module.compHom (Fiber E z) (baseMap E z)
  have sourceFin : Module.Finite (Plane k) (Order k E) :=
    IsIntegralClosure.finite (Plane k) (FractionRing (Plane k)) E (Order k E)
  let m:=quotientMap E z
  have fin : Module.Finite k[X] (Fiber E z) :=
    finite_image (A:=Plane k) (R:=k[X]) (M:=↥(Order k E)) (N:=Fiber E z)
      m.toAddMonoidHom (quotientMap_surjective E z) (fun c=>c.eval (C z)) (by
        intro c v
        rw [Algebra.smul_def c v]
        change m (algebraMap (Plane k) (Order k E) c*v) = baseMap E z (c.eval (C z)) * m v
        rw [map_mul]; exact congrArg (·*m v) (specialize E z c))
  have tor : Module.IsTorsionFree k[X] (Fiber E z) := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro r u eq
    by_cases zero : r=0
    · exact Or.inl zero
    · exact Or.inr (torsion_free E z r zero u eq)
  exact ⟨fin,inferInstance⟩

end Plane
#print axioms torsion_free
#print axioms finite_free
end Lower6960.NormalizedFiber
