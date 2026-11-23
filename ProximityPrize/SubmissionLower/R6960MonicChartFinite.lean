import ProximityPrize.SubmissionLower.R6960MonicChartScaled
import ProximityPrize.SubmissionLower.R6960ChartIntegrality
import ProximityPrize.SubmissionLower.R6960RetainedLinearAssembly

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000

namespace Lower6960.MonicChart
noncomputable section
open Polynomial
open scoped Polynomial Differential

/-- A primitive equation has a constant evaluation avoiding each
irreducible abscissa divisor. -/
theorem constant_evaluation_avoids {K : Type*} [Field K] [Infinite K]
    (f : K[X][X]) (primitive : f.IsPrimitive) (q : K[X]) (ir : Irreducible q) :
    ∃ c : K, ¬q∣f.eval (C c) := by
  let J : Ideal K[X] := Ideal.span {q}
  letI : J.IsPrime := (Ideal.span_singleton_prime ir.ne_zero).mpr ir.prime
  let ρ := Ideal.Quotient.mk J
  let embed : K→+*(K[X]⧸J) := ρ.comp C
  by_contra! no
  have roots : (Set.range embed : Set (K[X]⧸J)) ⊆ {z | (f.map ρ).IsRoot z} := by
    rintro _ ⟨c,rfl⟩
    change (f.map ρ).eval (ρ (C c))=0
    rw [Polynomial.eval_map_apply]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton.mpr (no c)
  have zero : f.map ρ=0 := eq_zero_of_infinite_isRoot (f.map ρ)
    ((Set.infinite_range_of_injective embed.injective).mono roots)
  apply ir.not_isUnit
  apply (isPrimitive_iff_isUnit_of_C_dvd.mp primitive) q
  apply (C_dvd_iff_dvd_coeff ..).mpr
  intro j
  have vanish := congrArg (fun P : (K[X]⧸J)[X] => P.coeff j) zero
  rw [coeff_map,coeff_zero] at vanish
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp vanish)

section Finite

variable {K F E : Type*} [Field K] [Infinite K] [Field F] [Field E]
    [Algebra K[X] F] [IsFractionRing K[X] F] [Algebra F E] [Algebra K[X] E]
    [IsScalarTower K[X] F E] [Algebra.IsSeparable F E] [FiniteDimensional F E]
    [Differential K[X]] [Differential E] [DifferentialAlgebra K[X] E]

/-- The original padded resultant controls the derivative over the whole
finite abscissa line. The local auxiliary evaluation values disappear
by the intersection of the codimension-one tests. -/
theorem clears_finite (b : PowerBasis F E) (f : K[X][X]) (primitive : f.IsPrimitive)
    (e2 : 2≤f.natDegree) (degree : f.natDegree=b.dim) (tame : (f.natDegree:F)≠0)
    (root : aeval b.gen f=0) (x : E) (integral : IsIntegral K[X] x) :
    IsIntegral K[X] (algebraMap K[X] E ((paddedRes f)^2)*x′) := by
  apply ChartIntegrality.integral_from_places F
  intro q ir
  obtain ⟨c,n⟩ := constant_evaluation_avoids f primitive q ir
  let u := f.eval (C c)
  have un : u≠0 := by
    intro h
    apply n
    change q∣u
    rw [h]
    exact dvd_zero q
  let k := 2*((f.natDegree-1)*(f.natDegree-2))
  refine ⟨u^k,fun h=>n (ir.prime.dvd_of_dvd_pow h),?_⟩
  rw [←mul_assoc,←map_mul]
  exact scaled_raw_square_clears b f (C c) un e2 degree tame root x integral

end Finite

section Actual

open K1_14 (L)
open RetainedCompression (Curve ordinate view view_y)

abbrev Scalar := RetainedLinear.Seed

/-- The weighted-compression factor over the generic scalar carries the
same finite derivative clearing as its arithmetic plane equation. -/
theorem actual_finite {E : Type*} [Field E] [Algebra (RatFunc Scalar) E]
    [Algebra Scalar[X] E] [IsScalarTower Scalar[X] (RatFunc Scalar) E]
    [Algebra.IsSeparable (RatFunc Scalar) E] [FiniteDimensional (RatFunc Scalar) E]
    [Differential Scalar[X]] [Differential E] [DifferentialAlgebra Scalar[X] E]
    (f : Curve L[X]) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<48)
    (b : PowerBasis (RatFunc Scalar) E) (root : aeval b.gen (RetainedLinear.toSeed (view f))=0)
    (x : E) (int : IsIntegral Scalar[X] x) :
    IsIntegral Scalar[X]
      (algebraMap Scalar[X] E ((paddedRes (RetainedLinear.toSeed (view f)))^2)*x′) := by
  let P := RetainedLinear.toSeed (view f)
  have deg : P.natDegree=f.degreeOf ordinate := (RetainedLinear.toSeed_degree _).trans (view_y _)
  have pos : 0<(view f).natDegree := by rw [view_y]; omega
  have pir : Irreducible P :=
    RetainedLinear.toSeed_irreducible ((MulEquiv.irreducible_iff view).mpr ir) pos
  have pd : P.natDegree≠0 := by omega
  have prim := pir.isPrimitive pd
  let ι := algebraMap Scalar[X] (RatFunc Scalar)
  let Q := P.map ι
  have irrQ : Irreducible Q := prim.irreducible_iff_irreducible_map_fraction_map.mp pir
  have rootQ : aeval b.gen Q=0 := by rw [aeval_map_algebraMap]; exact root
  have dvd : minpoly (RatFunc Scalar) b.gen∣Q := minpoly.dvd _ _ rootQ
  have assoc := (minpoly.irreducible b.isIntegral_gen).associated_of_dvd irrQ dvd
  have oq : Q.natDegree=(minpoly (RatFunc Scalar) b.gen).natDegree :=
    le_antisymm (natDegree_le_of_dvd assoc.symm.dvd (minpoly.ne_zero b.isIntegral_gen))
      (natDegree_le_of_dvd dvd irrQ.ne_zero)
  have dim : P.natDegree=b.dim :=
    (natDegree_map_eq_of_injective (IsFractionRing.injective Scalar[X] (RatFunc Scalar)) P).symm.trans
      (oq.trans b.natDegree_minpoly)
  let seed : L→+*Scalar := (algebraMap L[X] Scalar).comp C
  letI : Infinite Scalar := Infinite.of_injective seed seed.injective
  haveI : CharP (RatFunc Scalar) K1.p :=
    charP_of_injective_ringHom ((RatFunc.C : Scalar→+*RatFunc Scalar).comp seed).injective K1.p
  have tame : (P.natDegree:RatFunc Scalar)≠0 := by
    intro zero
    have h := (CharP.cast_eq_zero_iff (RatFunc Scalar) K1.p P.natDegree).mp zero
    have lt : P.natDegree<K1.p := by rw [deg]; exact hi.trans (by decide)
    exact pd (Nat.eq_zero_of_dvd_of_lt h lt)
  exact clears_finite b P prim (by omega) dim tame root x int

end Actual

#print axioms clears_finite
#print axioms actual_finite
end
end Lower6960.MonicChart
