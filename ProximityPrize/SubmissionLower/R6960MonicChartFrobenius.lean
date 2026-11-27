import ProximityPrize.SubmissionLower.R6960MonicChartInfinityRing
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Expand
import ProximityPrize.SubmissionLower.R6960QuadraticProjection
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Localization.NumDen
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Etale.Field
import ProximityPrize.SubmissionLower.R6960MonicChartActual
import Mathlib.RingTheory.Localization.Integral

set_option Elab.async false

-- merged module R6960FrobeniusConstants
section Merged_R6960FrobeniusConstants
noncomputable section
set_option Elab.async false
namespace Lower6960.FrobeniusConstants
open Polynomial Algebra
open scoped Differential Polynomial
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







end Lower6960.FrobeniusConstants

end
end Merged_R6960FrobeniusConstants

-- merged module R6960PlaneConstants
section Merged_R6960PlaneConstants
noncomputable section
set_option Elab.async false
namespace Lower6960.PlaneConstants
open Polynomial
open scoped Polynomial
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
end Lower6960.PlaneConstants

end
end Merged_R6960PlaneConstants

-- merged module R6960ChartDerivations
section Merged_R6960ChartDerivations
noncomputable section
set_option Elab.async false
namespace Lower6960.ChartDerivations
open Polynomial Algebra TrivSqZeroExt
open scoped Polynomial
section Smooth
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
private abbrev Dual (B : Type*) := TrivSqZeroExt B B
private def twist (d : Derivation ℤ A A) : A→+* Dual B where
  toFun x:=⟨algebraMap A B x,algebraMap A B (d x)⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by
    ext
    · exact map_add (algebraMap A B) _ _
    · change algebraMap A B (d (x+y))=algebraMap A B (d x)+algebraMap A B (d y)
      rw [map_add,map_add]
  map_mul' x y := by
    ext
    · exact map_mul (algebraMap A B) _ _
    · change algebraMap A B (d (x*y))=algebraMap A B x*algebraMap A B (d y)+algebraMap A B (d x)*algebraMap A B y
      simp [d.leibniz,smul_eq_mul,mul_comm]
theorem extend [Algebra.FormallySmooth A B] (d : Derivation ℤ A A) :
    ∃ D : Derivation ℤ B B,∀ x,D (algebraMap A B x)=algebraMap A B (d x) := by
  classical
  let S:=Dual B
  let π : S→+*B := (fstHom ℤ B B).toRingHom
  have onto : Function.Surjective π := fun b=>⟨⟨b,0⟩,rfl⟩
  let I:=RingHom.ker π
  have nil : I^2=⊥ := by
    rw [pow_two,eq_bot_iff]
    apply Ideal.mul_le.mpr
    intro a ha b hb
    have az : a.fst=0 := RingHom.mem_ker.mp ha
    have bz : b.fst=0 := RingHom.mem_ker.mp hb
    change a*b=0
    apply TrivSqZeroExt.ext
    · change a.fst*b.fst=0
      rw [az,zero_mul]
    · change a.fst*b.snd+a.snd*b.fst=0
      simp [az,bz]
  let : Algebra A S := (twist (B:=B) d).toAlgebra
  let eq := RingHom.quotientKerEquivOfSurjective onto
  let inv : B →ₐ[A] S ⧸ I := { eq.symm.toRingHom with
    commutes' := by
      intro r
      change eq.symm (π (twist d r))=Ideal.Quotient.mk I (twist d r)
      exact RingHom.quotientKerEquivOfSurjective_symm_apply onto _ }
  obtain ⟨g,hg⟩ := Algebra.FormallySmooth.exists_lift I ⟨2,nil⟩ inv
  have fstId (b : B) : (g b).fst=b := by
    have same:=congrArg eq (DFunLike.congr_fun hg b)
    change eq (Ideal.Quotient.mk I (g b))=eq (eq.symm b) at same
    exact (RingHom.quotientKerEquivOfSurjective_apply_mk onto (g b)).symm.trans
      (same.trans (eq.apply_symm_apply b))
  let sndAdd : B→+B := {
    toFun:=fun x=>(g x).snd
    map_zero':=by simp
    map_add':=fun x y=>by rw [map_add]; rfl }
  let D : Derivation ℤ B B := {
    sndAdd.toIntLinearMap with
    map_one_eq_zero':=by change (g 1).snd=0; simp
    leibniz':=by
      intro x y
      change (g (x*y)).snd=x*(g y).snd+y*(g x).snd
      rw [map_mul,snd_mul,fstId,fstId]
      simp [smul_eq_mul,mul_comm] }
  refine ⟨D,?_⟩
  intro x
  exact congrArg TrivSqZeroExt.snd (g.commutes x)
end Smooth
section Coordinates
open PlaneConstants (Plane)
variable {k : Type} [Field k]
def dx : Derivation ℤ (Plane k) (Plane k) :=
  (Polynomial.derivative' : Derivation (Polynomial k) (Plane k) (Plane k)).restrictScalars ℤ
def dz : Derivation ℤ (Plane k) (Plane k) :=
  letI : Differential (Polynomial k) := ⟨(Polynomial.derivative' : Derivation k (Polynomial k) (Polynomial k)).restrictScalars ℤ⟩
  Differential.mapCoeffs
theorem dz_apply (q : Plane k) : dz q=Bivariate.swap (Bivariate.swap q).derivative := by
  ext i j
  change (q.coeff i).derivative.coeff j=_
  rw [CurvatureSquares.coeff_swap,coeff_derivative,coeff_derivative,
    show ((j:(Polynomial k))+1)=C ((j:k)+1) by simp,coeff_mul_C,CurvatureSquares.coeff_swap]




























end Coordinates
end Lower6960.ChartDerivations

end
end Merged_R6960ChartDerivations

-- merged module R6960MonicChartPlane
section Merged_R6960MonicChartPlane

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2600000

namespace Lower6960.MonicChart
noncomputable section
open Polynomial
open K1_14 (L)
open PlaneConstants (Plane)
open scoped Polynomial
open Lower6960.ChartDerivations (dx dz dz_apply)

abbrev ChartField := RatFunc Scalar

private abbrev scalarIncl : (Polynomial L) →+* Scalar := algebraMap (Polynomial L) Scalar

private def planeIncl : Plane L →+* ChartField :=
  (algebraMap (Polynomial Scalar) ChartField).comp (Polynomial.mapRingHom scalarIncl)

scoped instance (priority := 2000) chartIntAlgebra : Algebra ℤ ChartField := Ring.toIntAlgebra _

scoped instance planeAlgebra : Algebra (Plane L) ChartField := planeIncl.toAlgebra

theorem plane_fractionRing : IsFractionRing (Plane L) ChartField := by
  have pinj : Function.Injective (planeIncl) :=
    (IsFractionRing.injective (Polynomial Scalar) ChartField).comp
      (Polynomial.map_injective _ (IsFractionRing.injective (Polynomial L) Scalar))
  let : FaithfulSMul (Plane L) ChartField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr pinj
  apply IsFractionRing.of_field
  intro z
  obtain ⟨p,q,_,eq⟩ := IsFractionRing.div_surjective (Polynomial Scalar) z
  let M := nonZeroDivisors (Polynomial L)
  obtain ⟨a,ha,ea⟩ := IsLocalization.integerNormalization_spec M p
  obtain ⟨b,hb,eb⟩ := IsLocalization.integerNormalization_spec M q
  let ι := algebraMap (Polynomial Scalar) ChartField
  refine ⟨IsLocalization.integerNormalization M p * C b,
    IsLocalization.integerNormalization M q * C a,?_⟩
  change z = planeIncl _ / planeIncl _
  simp only [planeIncl,RingHom.comp_apply,coe_mapRingHom,map_C,ea,eb,Algebra.smul_def,map_mul]
  rw [←eq]
  change ι p / ι q = ι (C (scalarIncl a)) * ι p * ι (C (scalarIncl b)) /
    (ι (C (scalarIncl b)) * ι q * ι (C (scalarIncl a)))
  have nz (u : (Polynomial L)) (hu : u∈M) : ι (C (scalarIncl u)) ≠ 0 := by
    simpa only [Function.comp_apply,map_zero] using
      ((IsFractionRing.injective (Polynomial Scalar) ChartField).comp
        (C_injective.comp (IsFractionRing.injective (Polynomial L) Scalar))).ne
          (mem_nonZeroDivisors_iff_ne_zero.mp hu)
  rw [show ι (C (scalarIncl a)) * ι p * ι (C (scalarIncl b)) =
        (ι (C (scalarIncl a))*ι (C (scalarIncl b)))*ι p by ring,
      show ι (C (scalarIncl b)) * ι q * ι (C (scalarIncl a)) =
        (ι (C (scalarIncl a))*ι (C (scalarIncl b)))*ι q by ring,
    mul_div_mul_left _ _ (mul_ne_zero (nz a ha) (nz b hb))]

private theorem incl_C (a : (Polynomial L)) :
    algebraMap (Plane L) ChartField (C a) = RatFunc.C (scalarIncl a) := by
  change planeIncl (C a) = _
  simp [planeIncl,RatFunc.algebraMap_C]

private theorem incl_X : algebraMap (Plane L) ChartField (Polynomial.X (R:=(Polynomial L))) = RatFunc.X := by
  change planeIncl (Polynomial.X (R:=(Polynomial L))) = _
  simp [planeIncl,RatFunc.algebraMap_X]

private theorem dz_C (a : (Polynomial L)) : Lower6960.ChartDerivations.dz (C a) = C a.derivative := by
  apply Polynomial.ext
  intro j
  change ((C a).coeff j).derivative = (C a.derivative).coeff j
  by_cases eq : j = 0 <;> simp [eq,coeff_C]

private theorem dz_X : Lower6960.ChartDerivations.dz (Polynomial.X (R:=(Polynomial L))) = 0 := by
  apply Polynomial.ext
  intro j
  change ((Polynomial.X (R:=(Polynomial L))).coeff j : (Polynomial L)).derivative = (0 : Polynomial (Polynomial L)).coeff j
  by_cases eq : j = 1 <;> simp [eq,Ne.symm,coeff_X]

private theorem on_scalar (D : Derivation ℤ ChartField ChartField)
    (numerator : ∀ a : (Polynomial L),∃ b : Scalar,D (RatFunc.C (scalarIncl a))=RatFunc.C b)
    (s : Scalar) : ∃ t : Scalar,D (RatFunc.C s)=RatFunc.C t := by
  obtain ⟨a,b,_,eq⟩ := IsFractionRing.div_surjective (Polynomial L) s
  obtain ⟨a',ha⟩ := numerator a
  obtain ⟨b',hb⟩ := numerator b
  refine ⟨(scalarIncl b)⁻¹ ^ 2 * (scalarIncl b*a'-scalarIncl a*b'),?_⟩
  rw [←eq,map_div₀,D.leibniz_div,smul_eq_mul,smul_eq_mul,smul_eq_mul,ha,hb]
  simp only [map_mul,map_pow,map_inv₀,map_sub]

/-- The coordinate derivations on the actual two-variable fraction field,
with their action on its polynomial coordinates and its localized scalars. -/
theorem base_coordinates : ∃ dx dz : Derivation ℤ ChartField ChartField,
    (∀ q,dx (algebraMap (Plane L) ChartField q)=algebraMap (Plane L) ChartField q.derivative) ∧
    (∀ q,dz (algebraMap (Plane L) ChartField q)=algebraMap (Plane L) ChartField
      (Bivariate.swap (Bivariate.swap q).derivative)) ∧
    dx RatFunc.X=1 ∧ dz RatFunc.X=0 ∧
    (∀ a : Scalar,∃ b : Scalar,dx (RatFunc.C a)=RatFunc.C b) ∧
    (∀ a : Scalar,∃ b : Scalar,dz (RatFunc.C a)=RatFunc.C b) := by
  let : IsFractionRing (Plane L) ChartField := plane_fractionRing
  have : Algebra.FormallyEtale (Plane L) ChartField :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (Plane L))
  obtain ⟨dx,hx⟩ := ChartDerivations.extend (B:=ChartField) (Lower6960.ChartDerivations.dx (k:=L))
  obtain ⟨dz,hz⟩ := ChartDerivations.extend (B:=ChartField) (Lower6960.ChartDerivations.dz (k:=L))
  have hx' (q : Plane L) : dx (algebraMap (Plane L) ChartField q) =
      algebraMap (Plane L) ChartField q.derivative := hx q
  refine ⟨dx,dz,hx',fun q=>(hz q).trans (congrArg _ (Lower6960.ChartDerivations.dz_apply q)),
    ?_,?_,on_scalar dx ?_,on_scalar dz ?_⟩
  · simpa only [incl_X,derivative_X,map_one] using hx' (Polynomial.X (R:=(Polynomial L)))
  · rw [←incl_X]
    exact (hz _).trans ((congrArg (algebraMap (Plane L) ChartField) dz_X).trans (map_zero _))
  · intro a
    refine ⟨0,?_⟩
    simpa only [incl_C,derivative_C,map_zero] using hx' (C a)
  · intro a
    refine ⟨scalarIncl a.derivative,?_⟩
    rw [←incl_C]
    exact (hz _).trans ((congrArg (algebraMap (Plane L) ChartField) (dz_C a)).trans (incl_C _))

end
end Lower6960.MonicChart

end Merged_R6960MonicChartPlane

-- merged module R6960MonicChartDerivationRings
section Merged_R6960MonicChartDerivationRings
set_option Elab.async false
set_option maxHeartbeats 2900000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MonicChart
noncomputable section
open Polynomial
open scoped Polynomial Lower6960.MonicChart
scoped instance (priority := 2000) chartPolyIntAlgebra : Algebra ℤ (Polynomial Scalar) :=
  Ring.toIntAlgebra _
private theorem derivation_restrict {R F : Type*} [CommRing R] [CommRing F]
    (j : R →+* F) (inj : Function.Injective j) (D : Derivation ℤ F F)
    (closed : ∀ r,∃ s,D (j r)=j s) :
    ∃ d : Derivation ℤ R R,∀ r,D (j r)=j (d r) := by
  classical
  choose d hd using closed
  let add : R →+ R := {
    toFun := d
    map_zero' := inj (by rw [←hd,map_zero,map_zero])
    map_add' r s := inj (by rw [←hd,map_add,map_add,map_add,hd,hd]) }
  let out : Derivation ℤ R R := {
    add.toIntLinearMap with
    map_one_eq_zero' := inj (by change j (d 1)=j 0; rw [←hd,map_one,D.map_one_eq_zero,map_zero])
    leibniz' r s := inj (by
      change j (d (r*s)) = j (r*d s+s*d r)
      rw [←hd,map_mul,D.leibniz,smul_eq_mul,smul_eq_mul,hd,hd,map_add,map_mul,map_mul]) }
  exact ⟨out,hd⟩
private theorem derivation_polynomial_image {K R F : Type*} [CommRing K] [CommRing R]
    [CommRing F] (g : (Polynomial K) →+* R) (j : R →+* F) (D : Derivation ℤ F F)
    (coeffs : ∀ a,∃ b,D (j (g (C a)))=j b) (gen : ∃ t,D (j (g (Polynomial.X (R:=K))))=j t)
    (p : (Polynomial K)) : ∃ q,D (j (g p))=j q := by
  obtain ⟨t,ht⟩ := gen
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨p',ep⟩ := hp
    obtain ⟨q',eq⟩ := hq
    exact ⟨p'+q',by rw [map_add,map_add,map_add,ep,eq,map_add]⟩
  | monomial n a =>
    obtain ⟨a',ha⟩ := coeffs a
    refine ⟨g (C a) * ((n:R)*(g (Polynomial.X (R:=K)))^(n-1)*t) + (g (Polynomial.X (R:=K)))^n*a',?_⟩
    rw [←C_mul_X_pow_eq_monomial,map_mul,map_mul,D.leibniz,map_pow,map_pow,
      D.leibniz_pow,ha,ht]
    simp only [smul_eq_mul,nsmul_eq_mul,map_mul,map_pow,map_add,map_natCast,mul_assoc]
theorem finite_derivation (D : Derivation ℤ ChartField ChartField)
    (on_scalars : ∀ a : Scalar,∃ b : Scalar,D (RatFunc.C a)=RatFunc.C b)
    (on_X : D RatFunc.X=1 ∨ D RatFunc.X=0) :
    ∃ d : Derivation ℤ (Polynomial Scalar) (Polynomial Scalar),∀ r,
      D (algebraMap (Polynomial Scalar) ChartField r)=algebraMap (Polynomial Scalar) ChartField (d r) := by
  let j := algebraMap (Polynomial Scalar) ChartField
  apply derivation_restrict j (IsFractionRing.injective _ _) D
  apply derivation_polynomial_image (RingHom.id _) j D
  · intro a
    obtain ⟨b,hb⟩ := on_scalars a
    exact ⟨C b,by simpa only [j,RingHom.id_apply,RatFunc.algebraMap_C] using hb⟩
  · rcases on_X with eq|eq
    · exact ⟨1,by simpa only [j,RingHom.id_apply,RatFunc.algebraMap_X,map_one] using eq⟩
    · exact ⟨0,by simpa only [j,RingHom.id_apply,RatFunc.algebraMap_X,map_zero] using eq⟩
theorem infinity_ratio {K : Type*} [Field K] [DecidableEq (RatFunc K)] (v : Infinity K) :
    ∃ p q : (Polynomial K), q.coeff 0≠0 ∧
      algebraMap (Infinity K) (RatFunc K) v = AtInfinity K p / AtInfinity K q := by
  let j := algebraMap (Polynomial K) (RatFunc K)
  obtain ⟨a,b,bmem,eq⟩ := IsFractionRing.div_surjective (Polynomial K) (v:RatFunc K)
  have bn : b≠0 := mem_nonZeroDivisors_iff_ne_zero.mp bmem
  by_cases an : a=0
  · refine ⟨0,1,by simp,?_⟩
    change (v:RatFunc K)=_
    rw [←eq,an]
    simp
  have fit : a.natDegree≤b.natDegree := by
    have val : RatFunc.inftyValuation K (j a/j b)≤1 := eq ▸ v.property
    rw [map_div₀,div_le_one₀] at val
    · change RatFunc.inftyValuationDef K (j a)≤RatFunc.inftyValuationDef K (j b) at val
      rwa [RatFunc.inftyValuation.polynomial _ an,RatFunc.inftyValuation.polynomial _ bn,
        WithZero.exp_le_exp,Int.ofNat_le] at val
    · exact (RatFunc.inftyValuation K).pos_iff.mpr
        ((map_ne_zero_iff _ (IsFractionRing.injective (Polynomial K) (RatFunc K))).mpr bn)
  refine ⟨a.reflect b.natDegree,b.reverse,by rw [coeff_zero_reverse]; exact leadingCoeff_ne_zero.mpr bn,?_⟩
  change (v:RatFunc K)=_
  rw [reverse_atInfinity _ _ fit,Polynomial.reverse,reverse_atInfinity _ _ le_rfl,
    mul_div_mul_right _ _ (pow_ne_zero _ (inv_ne_zero RatFunc.X_ne_zero))]
  exact eq.symm
theorem infinity_derivation [DecidableEq ChartField] (D : Derivation ℤ ChartField ChartField)
    (on_scalars : ∀ a : Scalar,∃ b : Scalar,D (RatFunc.C a)=RatFunc.C b)
    (on_X : D RatFunc.X=1 ∨ D RatFunc.X=0) :
    ∃ d : Derivation ℤ (Infinity Scalar) (Infinity Scalar),∀ r,
      D (algebraMap (Infinity Scalar) ChartField r)=algebraMap (Infinity Scalar) ChartField (d r) := by
  let j := algebraMap (Infinity Scalar) ChartField
  let g := inftyRingEval Scalar
  have Cmap (a : Scalar) : j (g (C a))=RatFunc.C a := aeval_C _ _
  have Xmap : j (g (Polynomial.X : (Polynomial Scalar)))=RatFunc.X⁻¹ := mapped_X_infty
  have hpoly : ∀ p : (Polynomial Scalar),∃ q,D (j (g p))=j q := by
    apply derivation_polynomial_image g j D
    · intro a
      obtain ⟨b,hb⟩ := on_scalars a
      exact ⟨g (C b),by rw [Cmap,Cmap,hb]⟩
    · rw [Xmap,D.leibniz_inv,smul_eq_mul]
      rcases on_X with eq|eq
      · exact ⟨-(g (Polynomial.X : (Polynomial Scalar)))^2,by rw [map_neg,map_pow,Xmap,eq,mul_one]⟩
      · exact ⟨0,by rw [eq,mul_zero,map_zero]⟩
  apply derivation_restrict j (ValuationSubring.algebraMap_injective _ ChartField) D
  intro v
  obtain ⟨p,q,qnz,eq⟩ := infinity_ratio v
  change j v=j (g p)/j (g q) at eq
  obtain ⟨a,ha⟩ := hpoly p
  obtain ⟨b,hb⟩ := hpoly q
  obtain ⟨u,hu⟩ := inftyRingEval_isUnit q qnz
  change (u : Infinity Scalar)=g q at hu
  refine ⟨(↑u⁻¹:Infinity Scalar)^2*(g q*a-g p*b),?_⟩
  rw [eq,D.leibniz_div,smul_eq_mul,smul_eq_mul,smul_eq_mul,ha,hb]
  simp only [map_mul,map_pow,map_sub,map_units_inv,hu]
end
end Lower6960.MonicChart

end Merged_R6960MonicChartDerivationRings

-- merged module R6960MonicChartFrobenius
section Merged_R6960MonicChartFrobenius
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3700000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MonicChart
noncomputable section
open Polynomial
open K1_14 (L)
open PlaneConstants (Plane)
open RetainedCompression (Curve ordinate view view_y height heightCap)
open scoped Polynomial Lower6960.MonicChart
variable {E : Type*} [Field E]
    [Algebra ChartField E] [Algebra (Polynomial Scalar) E] [IsScalarTower (Polynomial Scalar) ChartField E]
theorem root_finrank (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate)
    (b : PowerBasis ChartField E) (root : aeval b.gen (RetainedLinear.toSeed (view f))=0) :
    Module.finrank ChartField E=f.degreeOf ordinate := by
  let P := RetainedLinear.toSeed (view f)
  let j := algebraMap (Polynomial Scalar) ChartField
  have deg : P.natDegree=f.degreeOf ordinate := (RetainedLinear.toSeed_degree _).trans (view_y _)
  have pir : Irreducible P := RetainedLinear.toSeed_irreducible
    ((MulEquiv.irreducible_iff view).mpr ir) (by rw [view_y]; omega)
  have prim := pir.isPrimitive (by omega : P.natDegree≠0)
  have iq : Irreducible (P.map j) := prim.irreducible_iff_irreducible_map_fraction_map.mp pir
  have rq : aeval b.gen (P.map j)=0 := by rw [aeval_map_algebraMap]; exact root
  have dvd := minpoly.dvd ChartField b.gen rq
  have assoc := (minpoly.irreducible b.isIntegral_gen).associated_of_dvd iq dvd
  have size : (P.map j).natDegree=(minpoly ChartField b.gen).natDegree :=
    le_antisymm (natDegree_le_of_dvd assoc.symm.dvd (minpoly.ne_zero b.isIntegral_gen))
      (natDegree_le_of_dvd dvd iq.ne_zero)
  rw [b.finrank,←b.natDegree_minpoly,←size,
    natDegree_map_eq_of_injective (IsFractionRing.injective (Polynomial Scalar) ChartField),deg]
variable [DecidableEq ChartField] [Algebra (Infinity Scalar) E] [IsScalarTower (Infinity Scalar) ChartField E]







































































end
end Lower6960.MonicChart

end Merged_R6960MonicChartFrobenius
