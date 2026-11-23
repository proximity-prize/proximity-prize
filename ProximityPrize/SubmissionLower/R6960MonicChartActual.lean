import ProximityPrize.SubmissionLower.R6960MonicChartCoboundary

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4200000

namespace Lower6960.MonicChart
noncomputable section
open Polynomial
open K1_14 (L)
open RetainedCompression (Curve ordinate view view_y height heightCap wordDegree abscissa_coeff_height)
open scoped Polynomial Differential
open private Lower6960.RetainedCompression.derivative_weighted_add_le
  from ProximityPrize.SubmissionLower.R6960RetainedCompressionDiscriminant

private theorem width_at_cutoff (e d : ℕ) (pos : 0<e) :
    resultantWidth e (heightCap e d) d=(3*e-1)*(e-1)*d := by
  have mul : d*e≤heightCap e d := by
    unfold heightCap
    rw [mul_comm d e]
    exact Nat.mul_le_mul_right d (by omega)
  have eq := resultantWidth_eq (e:=e) (d:=d) pos mul
  have identity : (2*e-1)*heightCap e d=d*e^2+(3*e-1)*(e-1)*d := by
    obtain ⟨k,h⟩ := Nat.exists_eq_add_of_le (show 1≤e from pos)
    unfold heightCap
    rw [h,show 2*(1+k)-1=2*k+1 by omega,show 3*(1+k)-1=3*k+2 by omega,
      show 1+k-1=k by omega]
    ring
  omega

/-- For the actual bounded projected factor, the overlap of the finite
and infinity chart coefficients has zero derivative. The only overlap
input is their Frobenius relation in the root field. -/
theorem actual_coboundary_zero {E : Type*} [Field E] [DecidableEq (RatFunc Scalar)]
    [Algebra (RatFunc Scalar) E] [Algebra Scalar[X] E]
    [IsScalarTower Scalar[X] (RatFunc Scalar) E]
    [Algebra (Infinity Scalar) E] [IsScalarTower (Infinity Scalar) (RatFunc Scalar) E]
    [Algebra.IsSeparable (RatFunc Scalar) E] [FiniteDimensional (RatFunc Scalar) E]
    [Differential Scalar[X]] [Differential (Infinity Scalar)] [Differential E]
    [DifferentialAlgebra Scalar[X] E] [DifferentialAlgebra (Infinity Scalar) E]
    (f : Curve L[X]) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<48)
    (bounded : height wordDegree f≤heightCap (f.degreeOf ordinate) wordDegree)
    (b : PowerBasis (RatFunc Scalar) E) (root : aeval b.gen (RetainedLinear.toSeed (view f))=0)
    (x y z : E) (fx : IsIntegral Scalar[X] x) (iy : IsIntegral (Infinity Scalar) y)
    (overlap : y=(algebraMap (RatFunc Scalar) E RatFunc.X)^K1.p*x+z^K1.p) :
    x′=0 := by
  let seed : L→+*Scalar := (algebraMap L[X] Scalar).comp C
  letI : Infinite Scalar := Infinite.of_injective seed seed.injective
  letI : CharP Scalar K1.p := charP_of_injective_ringHom seed.injective K1.p
  let inE : Scalar→+*E := (algebraMap (RatFunc Scalar) E).comp RatFunc.C
  letI : CharP E K1.p := charP_of_injective_ringHom inE.injective K1.p
  let P := RetainedLinear.toSeed (view f)
  let e := f.degreeOf ordinate
  let H := heightCap e wordDegree
  have deg : P.natDegree=e := (RetainedLinear.toSeed_degree _).trans (view_y _)
  have e2 : 2≤P.natDegree := by omega
  have ep : 0<P.natDegree := by omega
  have pir : Irreducible P := RetainedLinear.toSeed_irreducible
    ((MulEquiv.irreducible_iff view).mpr ir) (by rw [view_y]; omega)
  have tame : (P.natDegree:Scalar)≠0 := by
    intro zero
    have dvd := (CharP.cast_eq_zero_iff Scalar K1.p P.natDegree).mp zero
    exact ep.ne' (Nat.eq_zero_of_dvd_of_lt dvd (deg.symm ▸ hi.trans (by decide)))
  have coefficient (j : ℕ) : (P.coeff j).natDegree=((view f).coeff j).natDegree := by
    unfold P RetainedLinear.toSeed
    simp only [coe_mapRingHom,coeff_map,natDegree_map_eq_of_injective (RetainedLinear.incl_injective L)]
  have weights (j : ℕ) (jle : j≤P.natDegree) :
      (P.coeff j).natDegree+wordDegree*j≤H := by
    rw [coefficient]
    by_cases zero : (view f).coeff j=0
    · rw [zero,natDegree_zero,zero_add,mul_comm wordDegree]
      exact Nat.mul_le_mul_right _ (by omega)
    exact (abscissa_coeff_height f wordDegree j zero).trans bounded
  have Hfit : wordDegree*P.natDegree≤H :=
    (Nat.le_add_left ..).trans (weights _ le_rfl)
  have resBound : (paddedRes P).natDegree≤resultantWidth P.natDegree H wordDegree := by
    have h := Lower6960.RetainedCompression.derivative_weighted_add_le P P.natDegree
      H wordDegree ep weights
    have eq := resultantWidth_eq (e:=P.natDegree) (d:=wordDegree) (H:=H) ep Hfit
    exact Nat.le_of_add_le_add_right (h.trans_eq eq.symm)
  have room : 2*resultantWidth P.natDegree H wordDegree<K1.p := by
    rw [deg,width_at_cutoff e wordDegree (by omega)]
    exact (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right wordDegree
      (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.mul_le_mul_left 3 (by omega : e≤47)) 1)
       (Nat.sub_le_sub_right (by omega : e≤47) 1)))).trans_lt (by decide +kernel)
  have tameA : (P.natDegree:Scalar[X])≠0 := by
    simpa only [map_natCast] using
      (map_ne_zero_iff (Polynomial.C : Scalar→+*Scalar[X]) Polynomial.C_injective).mpr tame
  have dp := derivative_degree P ep tameA
  have der : P.derivative≠0 := by intro zero; rw [zero,natDegree_zero] at dp; omega
  have resNZ : paddedRes P≠0 := Polynomial.resultant_derivative_ne_zero_of_irreducible P pir der
  have prim := pir.isPrimitive ep.ne'
  let ι := algebraMap Scalar[X] (RatFunc Scalar)
  let Q := P.map ι
  have iq : Irreducible Q := prim.irreducible_iff_irreducible_map_fraction_map.mp pir
  have rq : aeval b.gen Q=0 := by rw [aeval_map_algebraMap]; exact root
  have dvd : minpoly (RatFunc Scalar) b.gen∣Q := minpoly.dvd _ _ rq
  have associated := (minpoly.irreducible b.isIntegral_gen).associated_of_dvd iq dvd
  have size : Q.natDegree=(minpoly (RatFunc Scalar) b.gen).natDegree :=
    le_antisymm (natDegree_le_of_dvd associated.symm.dvd (minpoly.ne_zero b.isIntegral_gen))
      (natDegree_le_of_dvd dvd iq.ne_zero)
  have dimension : P.natDegree=b.dim :=
    (natDegree_map_eq_of_injective (IsFractionRing.injective Scalar[X] (RatFunc Scalar)) P).symm.trans
      (size.trans b.natDegree_minpoly)
  exact common_coboundary_zero_generic b P H wordDegree K1.p prim e2 dimension tame weights
    resBound room resNZ root x y z fx iy overlap

#print axioms actual_coboundary_zero
end
end Lower6960.MonicChart
