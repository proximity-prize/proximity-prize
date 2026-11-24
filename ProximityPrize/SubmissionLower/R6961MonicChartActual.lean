import ProximityPrize.SubmissionLower.R6961MonicChartCoboundary

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4200000

namespace Lower6961.MonicChart
open Lower6960.MonicChart
noncomputable section
open Polynomial
open K1_14 (L)
open RetainedCompression (Curve ordinate view view_y height heightCap MarkedBand abscissa_coeff_height)
open scoped Polynomial Differential
open Lower6961.RetainedCompression (derivative_weighted_add_le)

private theorem width_at_cutoff (e d : ℕ) (he : 2≤e) (hd4 : 4 ∣ d) :
    resultantWidth e (heightCap e d) d = (10*e^2 - 13*e + 3) * (d / 4) := by
  obtain ⟨d₀, hd₀⟩ := hd4
  have hdiv : d / 4 = d₀ := by rw [hd₀]; exact Nat.mul_div_cancel_left d₀ (by decide)
  have mul : d*e≤heightCap e d := by
    unfold heightCap
    rw [hdiv, hd₀]
    have h1 : 4 * d₀ * e = (4 * e) * d₀ := by ring
    rw [h1]
    exact Nat.mul_le_mul_right d₀ (by omega)
  have eq := resultantWidth_eq (e:=e) (d:=d) (by omega) mul
  have identity : (2*e-1)*heightCap e d = d*e^2 + (10*e^2 - 13*e + 3) * (d / 4) := by
    obtain ⟨k,h⟩ := Nat.exists_eq_add_of_le he
    unfold heightCap
    rw [hdiv, hd₀, h]
    have h1 : 2*(2+k)-1 = 2*k+3 := by omega
    have h2 : 7*(2+k)-3 = 7*k+11 := by omega
    have h3 : 10*(2+k)^2 - 13*(2+k) + 3 = 10*k^2 + 27*k + 17 := by
      have hsq : 10*(2+k)^2 = 10*k^2 + 40*k + 40 := by ring
      have hlin : 13*(2+k) = 13*k + 26 := by ring
      rw [hsq, hlin]
      omega
    rw [h1, h2, h3]
    ring
  omega

theorem actual_coboundary_zero {E : Type*} [Field E] [DecidableEq (RatFunc Scalar)]
    [Algebra (RatFunc Scalar) E] [Algebra (Polynomial Scalar) E]
    [IsScalarTower (Polynomial Scalar) (RatFunc Scalar) E]
    [Algebra (Infinity Scalar) E] [IsScalarTower (Infinity Scalar) (RatFunc Scalar) E]
    [Algebra.IsSeparable (RatFunc Scalar) E] [FiniteDimensional (RatFunc Scalar) E]
    [Differential (Polynomial Scalar)] [Differential (Infinity Scalar)] [Differential E]
    [DifferentialAlgebra (Polynomial Scalar) E] [DifferentialAlgebra (Infinity Scalar) E]
    (B : MarkedBand)
    (f : Curve (Polynomial L)) (ir : Irreducible f) (lo : 3≤f.degreeOf ordinate) (hi : f.degreeOf ordinate<B.maxOrd)
    (bounded : height B.wordDegree f≤heightCap (f.degreeOf ordinate) B.wordDegree)
    (b : PowerBasis (RatFunc Scalar) E) (root : aeval b.gen (RetainedLinear.toSeed (view f))=0)
    (x y z : E) (fx : IsIntegral (Polynomial Scalar) x) (iy : IsIntegral (Infinity Scalar) y)
    (overlap : y=(algebraMap (RatFunc Scalar) E RatFunc.X)^K1.p*x+z^K1.p) :
    x′=0 := by
  let seed : L→+*Scalar := (algebraMap (Polynomial L) Scalar).comp C
  letI : Infinite Scalar := Infinite.of_injective seed seed.injective
  letI : CharP Scalar K1.p := charP_of_injective_ringHom seed.injective K1.p
  let inE : Scalar→+*E := (algebraMap (RatFunc Scalar) E).comp RatFunc.C
  letI : CharP E K1.p := charP_of_injective_ringHom inE.injective K1.p
  let P := RetainedLinear.toSeed (view f)
  let e := f.degreeOf ordinate
  let H := heightCap e B.wordDegree
  have deg : P.natDegree=e := (RetainedLinear.toSeed_degree _).trans (view_y _)
  have e2 : 2≤P.natDegree := by omega
  have ep : 0<P.natDegree := by omega
  have pir : Irreducible P := RetainedLinear.toSeed_irreducible
    ((MulEquiv.irreducible_iff view).mpr ir) (by rw [view_y]; omega)
  have tame : (P.natDegree:Scalar)≠0 := by
    intro zero
    have dvd := (CharP.cast_eq_zero_iff Scalar K1.p P.natDegree).mp zero
    exact ep.ne' (Nat.eq_zero_of_dvd_of_lt dvd (deg.symm ▸ hi.trans B.small_E))
  have coefficient (j : ℕ) : (P.coeff j).natDegree=((view f).coeff j).natDegree := by
    unfold P RetainedLinear.toSeed
    simp only [coe_mapRingHom,coeff_map,natDegree_map_eq_of_injective (RetainedLinear.incl_injective L)]
  have weights (j : ℕ) (jle : j≤P.natDegree) :
      (P.coeff j).natDegree+B.wordDegree*j≤H := by
    rw [coefficient]
    by_cases zero : (view f).coeff j=0
    · rw [zero,natDegree_zero,zero_add]
      obtain ⟨d₀, hd₀⟩ := B.dvd4
      have hdiv : B.wordDegree / 4 = d₀ := by rw [hd₀]; exact Nat.mul_div_cancel_left d₀ (by decide)
      dsimp only [H]; unfold heightCap; rw [hdiv, hd₀]
      have h1 : 4 * d₀ * j = (4 * j) * d₀ := by ring
      rw [h1]
      exact Nat.mul_le_mul_right d₀ (by omega)
    exact (abscissa_coeff_height f B.wordDegree j zero).trans bounded
  have Hfit : B.wordDegree*P.natDegree≤H :=
    (Nat.le_add_left ..).trans (weights _ le_rfl)
  have resBound : (paddedRes P).natDegree≤resultantWidth P.natDegree H B.wordDegree := by
    have h := Lower6961.RetainedCompression.derivative_weighted_add_le P P.natDegree
      H B.wordDegree ep weights
    have eq := resultantWidth_eq (e:=P.natDegree) (d:=B.wordDegree) (H:=H) ep Hfit
    exact Nat.le_of_add_le_add_right (h.trans_eq eq.symm)
  have room : 2*resultantWidth P.natDegree H B.wordDegree<K1.p := by
    rw [deg,width_at_cutoff e B.wordDegree (by omega) B.dvd4]
    exact B.room e hi lo
  have tameA : (P.natDegree:(Polynomial Scalar))≠0 := by
    simpa only [map_natCast] using
      (map_ne_zero_iff (Polynomial.C : Scalar→+*(Polynomial Scalar)) Polynomial.C_injective).mpr tame
  have dp := derivative_degree P ep tameA
  have der : P.derivative≠0 := by intro zero; rw [zero,natDegree_zero] at dp; omega
  have resNZ : paddedRes P≠0 := Polynomial.resultant_derivative_ne_zero_of_irreducible P pir der
  have prim := pir.isPrimitive ep.ne'
  let ι := algebraMap (Polynomial Scalar) (RatFunc Scalar)
  let Q := P.map ι
  have iq : Irreducible Q := prim.irreducible_iff_irreducible_map_fraction_map.mp pir
  have rq : aeval b.gen Q=0 := by rw [aeval_map_algebraMap]; exact root
  have dvd : minpoly (RatFunc Scalar) b.gen∣Q := minpoly.dvd _ _ rq
  have associated := (minpoly.irreducible b.isIntegral_gen).associated_of_dvd iq dvd
  have size : Q.natDegree=(minpoly (RatFunc Scalar) b.gen).natDegree :=
    le_antisymm (natDegree_le_of_dvd associated.symm.dvd (minpoly.ne_zero b.isIntegral_gen))
      (natDegree_le_of_dvd dvd iq.ne_zero)
  have dimension : P.natDegree=b.dim :=
    (natDegree_map_eq_of_injective (IsFractionRing.injective (Polynomial Scalar) (RatFunc Scalar)) P).symm.trans
      (size.trans b.natDegree_minpoly)
  exact common_coboundary_zero_generic b P H B.wordDegree K1.p prim e2 dimension tame weights
    resBound room resNZ root x y z fx iy overlap

end
end Lower6961.MonicChart
