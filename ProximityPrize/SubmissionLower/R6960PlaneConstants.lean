import ProximityPrize.SubmissionLower.R6960FrobeniusConstants
import ProximityPrize.SubmissionLower.R6960QuadraticProjection
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Localization.NumDen

noncomputable section
set_option Elab.async false
namespace Lower6960.PlaneConstants
open Polynomial
open scoped Polynomial

/-- Extract a polynomial p-th root by contracting the exponents and
lifting each remaining coefficient through Frobenius. -/
private theorem polynomial_power {R : Type*} [CommRing R] [IsDomain R] (p : ℕ)
    [Fact p.Prime] [CharP R p] (f : (Polynomial R)) (zero : f.derivative=0)
    (coeffs : ∀ i,∃ r:R,r^p=f.coeff i) : ∃ g:(Polynomial R),g^p=f := by
  classical
  have hp := (Fact.out : p.Prime).ne_zero
  have hr : contract p f∈Polynomial.lifts (frobenius R p) := by
    apply (lifts_iff_coeff_lifts _).mpr
    intro i
    rw [coeff_contract hp]
    exact coeffs _
  obtain ⟨g,eq⟩:=hr
  change g.map (frobenius R p)=contract p f at eq
  refine ⟨g,?_⟩
  rw [←map_frobenius_expand p,map_expand,eq,expand_contract p zero hp]

variable {k : Type} [Field k]
abbrev Plane (k : Type) [Field k] := Polynomial (Polynomial k)

theorem plane_power (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (f : Plane k) (horizontal : f.derivative=0) (vertical : (Bivariate.swap f).derivative=0) :
    ∃ g : Plane k,g^p=f := by
  apply polynomial_power p f horizontal
  intro j
  apply polynomial_power p (f.coeff j) _ (fun i=>surjective_frobenius k p _)
  ext i
  have eq := congrArg (fun g : Plane k=>(g.coeff i).coeff j) vertical
  rw [coeff_derivative,show ((i:(Polynomial k))+1)=C ((i:k)+1) by simp,
    coeff_mul_C,CurvatureSquares.coeff_swap,coeff_zero,coeff_zero] at eq
  simpa only [coeff_derivative,coeff_zero] using eq

private theorem coprime_derivatives {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid (Polynomial R)] {f g : (Polynomial R)} (cop : IsRelPrime f g)
    (zero : f.derivative*g=f*g.derivative) : f.derivative=0 ∧ g.derivative=0 := by
  have vanish (h : (Polynomial R)) (div : h∣h.derivative) : h.derivative=0 := by
    by_contra ne
    have pos : h.natDegree≠0 := by intro z; apply ne; rw [eq_C_of_natDegree_eq_zero z,derivative_C]
    exact (not_le_of_gt (natDegree_derivative_lt pos)) (natDegree_le_of_dvd div ne)
  exact ⟨vanish f (cop.dvd_of_dvd_mul_right (zero ▸ dvd_mul_right ..)),
    vanish g (cop.symm.dvd_of_dvd_mul_left (zero.symm ▸ dvd_mul_left ..))⟩

variable {F : Type*} [Field F] [Algebra (Plane k) F] [IsFractionRing (Plane k) F]

/-- The two quotient-rule numerators suffice on the actual rational
function field in two variables; no choice of a p-basis is required. -/
theorem fraction_power (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (x : F)
    (horizontal : let a:=IsFractionRing.num (Plane k) x; let b:Plane k:=IsFractionRing.den (Plane k) x
      a.derivative*b=a*b.derivative)
    (vertical : let a:=Bivariate.swap (IsFractionRing.num (Plane k) x)
                let b:=Bivariate.swap (IsFractionRing.den (Plane k) x : Plane k)
                a.derivative*b=a*b.derivative) :
    ∃ y : F,y^p=x := by
  classical
  let a:=IsFractionRing.num (Plane k) x
  let b:Plane k:=IsFractionRing.den (Plane k) x
  have cop : IsRelPrime a b := IsFractionRing.num_den_reduced _ _
  have swap : IsRelPrime (Bivariate.swap a) (Bivariate.swap b) := by
    intro d da db
    have dvd_a := map_dvd Bivariate.swap.toRingHom da
    have dvd_b := map_dvd Bivariate.swap.toRingHom db
    change Bivariate.swap d∣Bivariate.swap (Bivariate.swap a) at dvd_a
    change Bivariate.swap d∣Bivariate.swap (Bivariate.swap b) at dvd_b
    rw [Bivariate.swap_swap_apply] at dvd_a dvd_b
    have unit := (cop dvd_a dvd_b).map Bivariate.swap.toRingHom
    change IsUnit (Bivariate.swap (Bivariate.swap d)) at unit
    rwa [Bivariate.swap_swap_apply] at unit
  obtain ⟨ah,bh⟩ := coprime_derivatives cop horizontal
  obtain ⟨av,bv⟩ := coprime_derivatives swap vertical
  obtain ⟨u,hu⟩ := plane_power p a ah av
  obtain ⟨v,hv⟩ := plane_power p b bh bv
  let ι:=algebraMap (Plane k) F
  refine ⟨ι u/ι v,?_⟩
  rw [div_pow,←map_pow,←map_pow,hu,hv]
  exact IsFractionRing.mk'_num_den' _ _

#print axioms plane_power
#print axioms fraction_power

private theorem cross {x : F} (D : Derivation ℤ F F)
    (op : Plane k→Plane k)
    (agrees : ∀ q,D (algebraMap (Plane k) F q)=algebraMap (Plane k) F (op q))
    (constant : D x=0) :
    let a:=IsFractionRing.num (Plane k) x; let b:Plane k:=IsFractionRing.den (Plane k) x
    op a*b=a*op b := by
  let a:=IsFractionRing.num (Plane k) x
  let b:Plane k:=IsFractionRing.den (Plane k) x
  let ι:=algebraMap (Plane k) F
  have inj:=IsFractionRing.injective (Plane k) F
  have bn : b≠0 := mem_nonZeroDivisors_iff_ne_zero.mp (IsFractionRing.den _ x).property
  have eq : ι a=x*ι b := (div_eq_iff ((map_ne_zero_iff _ inj).mpr bn)).mp (IsFractionRing.mk'_num_den' _ x)
  have deq:=congrArg D eq
  rw [D.leibniz,constant,smul_zero,add_zero,smul_eq_mul,agrees,agrees] at deq
  change op a*b=a*op b
  apply inj
  rw [map_mul,map_mul,deq,eq]; ring

theorem base_constant (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (dx dz : Derivation ℤ F F)
    (xaction : ∀ q, dx (algebraMap (Plane k) F q)=algebraMap (Plane k) F q.derivative)
    (zaction : ∀ q, dz (algebraMap (Plane k) F q)=algebraMap (Plane k) F
      (Bivariate.swap (Bivariate.swap q).derivative)) (x : F) (hx : dx x=0) (hz : dz x=0) :
    ∃ y:F,y^p=x := by
  apply fraction_power p x (cross dx _ xaction hx)
  have second:=congrArg Bivariate.swap (cross dz _ zaction hz)
  simpa only [map_mul,Bivariate.swap_swap_apply] using second

private theorem coefficient_zero {L E : Type*} [Field L] [Field E] [Algebra L E]
    (d : Derivation ℤ L L) (D : Derivation ℤ E E)
    (agree : ∀ x,D (algebraMap L E x)=algebraMap L E (d x))
    (u : E) (integral : IsIntegral L u) (du : D u=0) (i : ℕ) :
    d ((minpoly L u).coeff i)=0 := by
  let : Differential L := ⟨d⟩
  let : Differential E := ⟨D⟩
  let : DifferentialAlgebra L E := ⟨agree⟩
  exact FrobeniusConstants.coefficients_constant integral du i

/-- Applied to the two extended coordinate derivations of the root field:
a common constant is a p-th power *in that field*. -/
theorem root_field_constant (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    {E : Type*} [Field E] [Algebra F E] [FiniteDimensional F E] [CharP E p]
    (dx dz : Derivation ℤ F F) (Dx Dz : Derivation ℤ E E)
    (xaction : ∀ q,dx (algebraMap (Plane k) F q)=algebraMap (Plane k) F q.derivative)
    (zaction : ∀ q,dz (algebraMap (Plane k) F q)=algebraMap (Plane k) F
      (Bivariate.swap (Bivariate.swap q).derivative))
    (ex : ∀ a,Dx (algebraMap F E a)=algebraMap F E (dx a))
    (ez : ∀ a,Dz (algebraMap F E a)=algebraMap F E (dz a))
    (small : Module.finrank F E<p) (u : E) (hx : Dx u=0) (hz : Dz u=0) :
    ∃ y:E,y^p=u := by
  have integral : IsIntegral F u := Algebra.IsIntegral.isIntegral u
  let f:=minpoly F u
  let ι:=algebraMap F E
  apply FrobeniusConstants.root_of_coefficients p (f.map ι)
    ((Polynomial.map_ne_zero_iff ι.injective).mpr (minpoly.ne_zero integral))
    (Polynomial.natDegree_map_le.trans_lt ((minpoly.natDegree_le u).trans_lt small)) u
  · rw [eval_map_algebraMap]; exact minpoly.aeval _ _
  · intro i
    obtain ⟨y,eq⟩ := base_constant p dx dz xaction zaction (f.coeff i)
      (coefficient_zero dx Dx ex u integral hx i) (coefficient_zero dz Dz ez u integral hz i)
    exact ⟨ι y,by rw [←map_pow,eq,coeff_map]⟩

#print axioms root_field_constant
end Lower6960.PlaneConstants
