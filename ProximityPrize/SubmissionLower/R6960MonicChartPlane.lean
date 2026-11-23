import ProximityPrize.SubmissionLower.R6960MonicChartActual
import ProximityPrize.SubmissionLower.R6960ChartDerivations
import Mathlib.RingTheory.Localization.Integral

set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2600000

namespace Lower6960.MonicChart
noncomputable section
open Polynomial
open K1_14 (L)
open PlaneConstants (Plane)
open scoped Polynomial
open private Lower6960.ChartDerivations.dx Lower6960.ChartDerivations.dz
  Lower6960.ChartDerivations.dz_apply from ProximityPrize.SubmissionLower.R6960ChartDerivations

abbrev ChartField := RatFunc Scalar

private abbrev scalarIncl : L[X] →+* Scalar := algebraMap L[X] Scalar

private def planeIncl : Plane L →+* ChartField :=
  (algebraMap Scalar[X] ChartField).comp (Polynomial.mapRingHom scalarIncl)

scoped instance (priority := 2000) chartIntAlgebra : Algebra ℤ ChartField := Ring.toIntAlgebra _

scoped instance planeAlgebra : Algebra (Plane L) ChartField := planeIncl.toAlgebra

theorem plane_fractionRing : IsFractionRing (Plane L) ChartField := by
  have pinj : Function.Injective (planeIncl) :=
    (IsFractionRing.injective Scalar[X] ChartField).comp
      (Polynomial.map_injective _ (IsFractionRing.injective L[X] Scalar))
  let : FaithfulSMul (Plane L) ChartField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr pinj
  apply IsFractionRing.of_field
  intro z
  obtain ⟨p,q,_,eq⟩ := IsFractionRing.div_surjective Scalar[X] z
  let M := nonZeroDivisors L[X]
  obtain ⟨a,ha,ea⟩ := IsLocalization.integerNormalization_spec M p
  obtain ⟨b,hb,eb⟩ := IsLocalization.integerNormalization_spec M q
  let ι := algebraMap Scalar[X] ChartField
  refine ⟨IsLocalization.integerNormalization M p * C b,
    IsLocalization.integerNormalization M q * C a,?_⟩
  change z = planeIncl _ / planeIncl _
  simp only [planeIncl,RingHom.comp_apply,coe_mapRingHom,map_C,ea,eb,Algebra.smul_def,map_mul]
  rw [←eq]
  change ι p / ι q = ι (C (scalarIncl a)) * ι p * ι (C (scalarIncl b)) /
    (ι (C (scalarIncl b)) * ι q * ι (C (scalarIncl a)))
  have nz (u : L[X]) (hu : u∈M) : ι (C (scalarIncl u)) ≠ 0 := by
    simpa only [Function.comp_apply,map_zero] using
      ((IsFractionRing.injective Scalar[X] ChartField).comp
        (C_injective.comp (IsFractionRing.injective L[X] Scalar))).ne
          (mem_nonZeroDivisors_iff_ne_zero.mp hu)
  rw [show ι (C (scalarIncl a)) * ι p * ι (C (scalarIncl b)) =
        (ι (C (scalarIncl a))*ι (C (scalarIncl b)))*ι p by ring,
      show ι (C (scalarIncl b)) * ι q * ι (C (scalarIncl a)) =
        (ι (C (scalarIncl a))*ι (C (scalarIncl b)))*ι q by ring,
    mul_div_mul_left _ _ (mul_ne_zero (nz a ha) (nz b hb))]

private theorem incl_C (a : L[X]) :
    algebraMap (Plane L) ChartField (C a) = RatFunc.C (scalarIncl a) := by
  change planeIncl (C a) = _
  simp [planeIncl,RatFunc.algebraMap_C]

private theorem incl_X : algebraMap (Plane L) ChartField (Polynomial.X (R:=L[X])) = RatFunc.X := by
  change planeIncl (Polynomial.X (R:=L[X])) = _
  simp [planeIncl,RatFunc.algebraMap_X]

private theorem dz_C (a : L[X]) : Lower6960.ChartDerivations.dz (C a) = C a.derivative := by
  apply Polynomial.ext
  intro j
  change (coeff (C a) j).derivative = coeff (C a.derivative) j
  by_cases eq : j = 0 <;> simp [eq,coeff_C]

private theorem dz_X : Lower6960.ChartDerivations.dz (Polynomial.X (R:=L[X])) = 0 := by
  apply Polynomial.ext
  intro j
  change (coeff (Polynomial.X (R:=L[X])) j : L[X]).derivative = coeff 0 j
  by_cases eq : j = 1 <;> simp [eq,Ne.symm,coeff_X]

private theorem on_scalar (D : Derivation ℤ ChartField ChartField)
    (numerator : ∀ a : L[X],∃ b : Scalar,D (RatFunc.C (scalarIncl a))=RatFunc.C b)
    (s : Scalar) : ∃ t : Scalar,D (RatFunc.C s)=RatFunc.C t := by
  obtain ⟨a,b,_,eq⟩ := IsFractionRing.div_surjective L[X] s
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
  · simpa only [incl_X,derivative_X,map_one] using hx' (Polynomial.X (R:=L[X]))
  · rw [←incl_X]
    exact (hz _).trans ((congrArg (algebraMap (Plane L) ChartField) dz_X).trans (map_zero _))
  · intro a
    refine ⟨0,?_⟩
    simpa only [incl_C,derivative_C,map_zero] using hx' (C a)
  · intro a
    refine ⟨scalarIncl a.derivative,?_⟩
    rw [←incl_C]
    exact (hz _).trans ((congrArg (algebraMap (Plane L) ChartField) (dz_C a)).trans (incl_C _))

#print axioms plane_fractionRing
#print axioms base_coordinates
end
end Lower6960.MonicChart
