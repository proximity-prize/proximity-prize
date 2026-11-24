import ProximityPrize.SubmissionLower.R6960DifferentialPoles
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Expand

noncomputable section
set_option Elab.async false
namespace Lower6960.FrobeniusConstants
open Polynomial Algebra
open scoped Differential Polynomial

/-- Differentiating the monic minimal polynomial of a constant kills all
of its coefficients. Its coefficient derivative has strictly smaller degree. -/
theorem coefficients_constant {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E]
    {u : E} (integral : IsIntegral F u) (constant : u′=0) (j : ℕ) :
    ((minpoly F u).coeff j)′=0 := by
  let f:=minpoly F u
  let g:=Differential.mapCoeffs f
  have mon : f.Monic := minpoly.monic integral
  have root : aeval u f=0 := minpoly.aeval F u
  have eq:=Differential.deriv_aeval_eq u f
  rw [root,map_zero,constant,mul_zero,add_zero] at eq
  have div : f∣g := minpoly.dvd F u eq.symm
  have zero : g=0 := by
    by_contra ng
    have upper : g.natDegree≤f.natDegree := by
      apply natDegree_le_iff_coeff_eq_zero.mpr
      intro i high
      change (f.coeff i)′=0
      rw [coeff_eq_zero_of_natDegree_lt high,map_zero]
    have degree := Nat.le_antisymm upper (natDegree_le_of_dvd div ng)
    have leading : g.coeff g.natDegree≠0 := by rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr ng
    apply leading
    rw [degree]
    change f.leadingCoeff′=0
    rw [mon.leadingCoeff]; exact Differential.deriv.map_one_eq_zero
  exact congrArg (fun q : (Polynomial F)=>q.coeff j) zero

/-- In a degree below the characteristic a root of a polynomial defined
over the Frobenius image is itself in that image. -/
theorem root_of_coefficients {E : Type*} [Field E] (p : ℕ) [Fact p.Prime] [CharP E p]
    (f : (Polynomial E)) (nonzero : f≠0) (degree : f.natDegree<p) (x : E) (root : f.eval x=0)
    (coefficients : ∀ i,∃ r:E,r^p=f.coeff i) : ∃ y:E,y^p=x := by
  classical
  have lifts : f∈Polynomial.lifts (frobenius E p) := (lifts_iff_coeff_lifts _).mpr coefficients
  obtain ⟨h,eq⟩ := lifts
  change h.map (frobenius E p)=f at eq
  have hn : h≠0 := fun z=>nonzero (by rw [←eq,z,Polynomial.map_zero])
  have deg : h.natDegree=f.natDegree := eq ▸ (natDegree_map_eq_of_injective (frobenius E p).injective h).symm
  by_contra! no
  have ir := X_pow_sub_C_irreducible_of_prime (Fact.out : p.Prime) no
  have div : Polynomial.X-C x∣f := dvd_iff_isRoot.mpr root
  have dv := map_dvd (expand E p).toRingHom div
  change expand E p (Polynomial.X-C x) ∣ expand E p f at dv
  rw [map_sub,expand_X,expand_C,←eq,←map_expand,map_frobenius_expand] at dv
  have hle := natDegree_le_of_dvd (ir.prime.dvd_of_dvd_pow dv) hn
  rw [natDegree_X_pow_sub_C,deg] at hle
  omega

/-- Descent of a common Frobenius coboundary to the original integral
charts. Scaling each chart by its own equation also handles negative twists. -/
theorem descend_chart {A E : Type*} [CommRing A] [Field E] [Algebra A E]
    (p : ℕ) [Fact p.Prime] [CharP E p] (u b t : E) (n : ℕ)
    (given : IsIntegral A ((u^p-b^p)/t^(p*n))) :
    IsIntegral A ((u-b)/t^n) := by
  apply IsIntegral.of_pow (n:=p) (Fact.out : p.Prime).pos
  rw [div_pow,sub_pow_char,←pow_mul,Nat.mul_comm n p]
  exact given

#print axioms coefficients_constant
#print axioms root_of_coefficients
#print axioms descend_chart
end Lower6960.FrobeniusConstants
