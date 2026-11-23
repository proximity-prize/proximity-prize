import ProximityPrize.SubmissionLower.R6960RetainedCompressionAssembly
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Localization.NumDen

set_option Elab.async false
set_option maxRecDepth 14000
set_option maxHeartbeats 2500000

namespace Lower6960.RetainedLinear
noncomputable section
open Polynomial
open scoped Polynomial nonZeroDivisors

variable {F E : Type} [Field F] [Field E] [Algebra F E]

abbrev Fn (F : Type) [Field F] := FractionRing F[X]

def constants : F[X] →+* E[X] := mapRingHom (algebraMap F E)

theorem constants_injective : Function.Injective (constants (F:=F) (E:=E)) :=
  Polynomial.map_injective _ (algebraMap F E).injective

def rationalConstants : Fn F →+* Fn E :=
  IsFractionRing.map (constants_injective (F:=F) (E:=E))

abbrev incl (F : Type) [Field F] := algebraMap F[X] (Fn F)

theorem incl_injective (F : Type) [Field F] : Function.Injective (incl F) :=
  IsFractionRing.injective F[X] (Fn F)

@[simp] theorem rationalConstants_incl (a : F[X]) :
    rationalConstants (E:=E) (incl F a)=incl E (constants a) := by
  unfold rationalConstants IsFractionRing.map
  exact IsLocalization.map_eq _ _

@[simp] theorem eval_constants (a : F[X]) (x : F) :
    (constants (E:=E) a).eval (algebraMap F E x)=algebraMap F E (a.eval x) :=
  Polynomial.eval_map_apply (algebraMap F E) (p:=a) x

/-- An algebraic linear factor away from a rational abscissa divides the
lift of a polynomial of the base field also avoiding that abscissa. -/
private theorem base_multiple_linear [Algebra.IsAlgebraic F E] (x : F) (r : E)
    (away : r≠algebraMap F E x) :
    ∃ b : F[X], b.eval x≠0 ∧ (Polynomial.X-C r)∣constants b := by
  have integ : IsIntegral F r := Algebra.IsIntegral.isIntegral r
  let b := minpoly F r
  have root : (constants (E:=E) b).eval r=0 := by
    change (b.map (algebraMap F E)).eval r=0
    rw [eval_map]
    exact minpoly.aeval F r
  refine ⟨b,?_ ,dvd_iff_isRoot.mpr root⟩
  intro zero
  have dvd : Polynomial.X-C x∣b := dvd_iff_isRoot.mpr zero
  have assoc := (irreducible_X_sub_C x).associated_of_dvd (minpoly.irreducible integ) dvd
  obtain ⟨a,eq⟩ := assoc.symm.dvd
  have mapped := congrArg (fun g : F[X] => (constants (E:=E) g).eval r) eq
  change (constants (E:=E) (Polynomial.X-C x)).eval r=(constants (E:=E) (b*a)).eval r at mapped
  rw [map_mul,eval_mul,root,zero_mul] at mapped
  have eq' : (constants (E:=E) (Polynomial.X-C x)).eval r=r-algebraMap F E x := by
    simp only [constants,coe_mapRingHom,Polynomial.map_sub,Polynomial.map_X,
      Polynomial.map_C,eval_sub,eval_X,eval_C]
  rw [eq'] at mapped
  exact away (sub_eq_zero.mp mapped)

/-- Rational functions over the geometric constant field admit a denominator
over the arithmetic constant field that stays nonzero at a prescribed node. -/
theorem base_multiple [IsAlgClosed E] [Algebra.IsAlgebraic F E]
    (x : F) (q : E[X]) (regular : q.eval (algebraMap F E x)≠0) :
    ∃ b : F[X], b.eval x≠0 ∧ q∣constants b := by
  induction q using WfDvdMonoid.induction_on_irreducible with
  | zero => simp at regular
  | unit q hu => exact ⟨1,by simp,hu.dvd⟩
  | mul a q an ir ih =>
    rw [eval_mul] at regular
    have qa : a.eval (algebraMap F E x)≠0 := fun z=>regular (by rw [z,mul_zero])
    have qq : q.eval (algebraMap F E x)≠0 := fun z=>regular (by rw [z,zero_mul])
    obtain ⟨u,hu,dU⟩ := ih qa
    obtain ⟨r,hr⟩ := IsAlgClosed.exists_root q (degree_pos_of_irreducible ir).ne'
    have away : r≠algebraMap F E x := fun h=>qq (h ▸ hr)
    have n : Polynomial.X-C r∣q := dvd_iff_isRoot.mpr hr
    have tied := (irreducible_X_sub_C r).associated_of_dvd ir n
    obtain ⟨v,hv,dV⟩ := base_multiple_linear x r away
    exact ⟨v*u,by rw [eval_mul]; exact mul_ne_zero hv hu,
      by rw [map_mul]; exact mul_dvd_mul (tied.symm.dvd.trans dV) dU⟩

/-- Arithmetic polynomials viewed in the geometric rational function field. -/
def base : F[X] →+* Fn E := (incl E).comp constants

/-- Every geometric polynomial is integral over the original arithmetic
polynomial ring. The proof only uses algebraicity of the constants. -/
theorem polynomial_integral [Algebra.IsAlgebraic F E] (p : E[X]) :
    (base (F:=F) (E:=E)).IsIntegralElem (incl E p) := by
  let j := base (F:=F) (E:=E)
  letI : Algebra F[X] (Fn E) := j.toAlgebra
  have const (a : E) : IsIntegral F[X] (incl E (C a)) := by
    let η : E →+* Fn E := (incl E).comp C
    have h : (algebraMap F E).IsIntegralElem a := Algebra.IsIntegral.isIntegral a
    have mapped := h.map η
    have eq : η.comp (algebraMap F E)=j.comp C := by
      apply RingHom.ext
      intro t
      simp [η,j,base,constants]
    rw [eq] at mapped
    exact mapped.of_comp
  have abscissa : IsIntegral F[X] (incl E (Polynomial.X : E[X])) := by
    have eq : (algebraMap F[X] (Fn E)) Polynomial.X=incl E (Polynomial.X : E[X]) := by
      change j Polynomial.X=_
      simp [j,base,constants]
    exact eq ▸ isIntegral_algebraMap
  change IsIntegral F[X] (incl E p)
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial,map_mul,map_pow]
    exact (const a).mul (abscissa.pow n)

/-- An element integral over the arithmetic polynomial ring has no
abscissa denominator in the geometric polynomial ring. -/
theorem integral_is_polynomial {r : Fn E} (h : (base (F:=F) (E:=E)).IsIntegralElem r) :
    ∃ p : E[X], incl E p=r := by
  have integral : IsIntegral E[X] r := h.of_comp
  exact (isIntegrallyClosed_iff (K:=Fn E)).mp (inferInstance : IsIntegrallyClosed E[X]) integral

end
end Lower6960.RetainedLinear
