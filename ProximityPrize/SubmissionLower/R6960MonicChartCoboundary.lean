import ProximityPrize.SubmissionLower.R6960MonicChartInfinityClearing

set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3600000

namespace Lower6960.MonicChart
noncomputable section
open Polynomial Algebra
open scoped Polynomial Differential
open private Lower6960.RetainedCompression.derivative_weighted_add_le
  from ProximityPrize.SubmissionLower.R6960RetainedCompressionDiscriminant

/-- The inverse abscissa has derivative (-X^{-2}) for the abscissa
derivation. This is the conversion between the two coordinate derivatives. -/
theorem inverse_abscissa_derivative {E : Type*} [Field E] [Differential E]
    (x : E) (coordinate : x′=1) : (x⁻¹)′=-(x⁻¹)^2 := by
  have h := (Differential.deriv (R:=E)).leibniz_inv x
  rw [coordinate,smul_eq_mul,mul_one] at h
  exact h

private theorem derivative_power_zero {E : Type*} [Field E] [Differential E]
    (p : ℕ) [CharP E p] (x : E) : (x^p)′=0 := by
  rw [Differential.deriv.leibniz_pow,nsmul_eq_mul,CharP.cast_eq_zero,zero_mul]

section Inverse

variable {K E : Type*} [Field K] [Infinite K] [DecidableEq (RatFunc K)]
    [Field E] [Algebra (RatFunc K) E] [Algebra K[X] E]
    [IsScalarTower K[X] (RatFunc K) E]
    [Algebra (Infinity K) E] [IsScalarTower (Infinity K) (RatFunc K) E]
    [Algebra.IsSeparable (RatFunc K) E] [FiniteDimensional (RatFunc K) E]
    [Differential (Infinity K)] [Differential E] [DifferentialAlgebra (Infinity K) E]

local notation "S" => Infinity K
local notation "F" => RatFunc K

/-- At infinity the finite resultant loses exactly its unused
homogenizing width. The remaining factor is a unit of the valuation ring. -/
theorem clears_inverse_power (b : PowerBasis F E) (f : K[X][X]) (H d : ℕ)
    (e2 : 2≤f.natDegree) (dim : f.natDegree=b.dim) (tame : (f.natDegree:K)≠0)
    (weights : ∀ i≤f.natDegree,(f.coeff i).natDegree+d*i≤H)
    (resBound : (paddedRes f).natDegree≤resultantWidth f.natDegree H d)
    (nonzero : paddedRes f≠0) (root : aeval b.gen f=0) (x : E) (hx : IsIntegral S x) :
    IsIntegral S (algebraMap F E (((RatFunc.X : F)⁻¹)^
      (2*(resultantWidth f.natDegree H d-(paddedRes f).natDegree)))*x′) := by
  let r := resultantWidth f.natDegree H d-(paddedRes f).natDegree
  let t := inftyRingEval K (Polynomial.X : K[X])
  let u := inftyRingEval K (paddedRes f).reverse
  have co : ((paddedRes f).reverse).coeff 0≠0 := by
    rw [coeff_zero_reverse]
    exact leadingCoeff_ne_zero.mpr nonzero
  have unit : IsUnit u := inftyRingEval_isUnit _ co
  obtain ⟨w,hw⟩ := unit
  have hom := clears_homogeneous_infinity b f H d e2 dim weights root x hx
  rw [infinity_resultant f H d (by omega) tame weights resBound,
    reflected_local_factor _ _ resBound] at hom
  change IsIntegral S (algebraMap S E ((t^r*u)^2)*x′) at hom
  have cancel : (↑w⁻¹:S)^2*(t^r*u)^2=t^(2*r) := by
    have single : (↑w⁻¹:S)*(t^r*u)=t^r := by
      rw [←hw,mul_comm (↑w⁻¹:S),mul_assoc,Units.mul_inv,mul_one]
    rw [←mul_pow,single,←pow_mul,Nat.mul_comm]
  have mul := (isIntegral_algebraMap (x:=(↑w⁻¹:S)^2)).mul hom
  rw [←mul_assoc,←map_mul,cancel] at mul
  have loc : algebraMap S F t=(RatFunc.X : F)⁻¹ := mapped_X_infty
  rw [IsScalarTower.algebraMap_apply S F E,map_pow,loc] at mul
  exact mul

section Both

variable [Differential K[X]] [DifferentialAlgebra K[X] E]

/-- The Frobenius overlap identity gives one common derivative on the
finite and infinity coordinates. Together with the checked pole bounds
it forces that derivative to vanish. -/
theorem common_coboundary_zero_generic (b : PowerBasis F E) (f : K[X][X]) (H d p : ℕ)
    [CharP E p] (primitive : f.IsPrimitive) (e2 : 2≤f.natDegree) (dim : f.natDegree=b.dim)
    (tame : (f.natDegree:K)≠0)
    (weights : ∀ i≤f.natDegree,(f.coeff i).natDegree+d*i≤H)
    (resBound : (paddedRes f).natDegree≤resultantWidth f.natDegree H d)
    (widthRoom : 2*resultantWidth f.natDegree H d<p)
    (nonzero : paddedRes f≠0) (root : aeval b.gen f=0)
    (x y z : E) (fx : IsIntegral K[X] x) (iy : IsIntegral S y)
    (overlap : y=(algebraMap F E RatFunc.X)^p*x+z^p) :
    x′=0 := by
  let r := resultantWidth f.natDegree H d-(paddedRes f).natDegree
  let Xval := algebraMap F E (RatFunc.X : F)
  have xn : Xval≠0 := (map_ne_zero_iff _ (algebraMap F E).injective).mpr RatFunc.X_ne_zero
  have inv := clears_inverse_power b f H d e2 dim tame weights resBound nonzero root y iy
  have dv : y′=Xval^p*x′ := by
    rw [overlap,map_add,Differential.deriv.leibniz,derivative_power_zero p,
      derivative_power_zero p,smul_eq_mul,smul_eq_mul,mul_zero,add_zero,add_zero]
  rw [dv] at inv
  have le : 2*r≤p := by dsimp only [r]; omega
  have cancel : (Xval⁻¹)^(2*r)*Xval^p=Xval^(p-2*r) := by
    have e : p=2*r+(p-2*r) := (Nat.add_sub_of_le le).symm
    calc
      _ = (Xval⁻¹)^(2*r)*(Xval^(2*r)*Xval^(p-2*r)) := by
        rw [←pow_add,←e]
      _ = _ := by rw [←mul_assoc,←mul_pow,inv_mul_cancel₀ xn,one_pow,one_mul]
  have hi : IsIntegral S (Xval^(p-2*r)*x′) := by
    rw [←cancel,mul_assoc]
    change IsIntegral S (((algebraMap F E (RatFunc.X : F))⁻¹)^(2*r)*(Xval^p*x′))
    rw [←map_inv₀,←map_pow]
    exact inv
  have fit : 2*(paddedRes f).natDegree<p-2*r := by dsimp only [r]; omega
  have tame' : (f.natDegree:F)≠0 := by
    simpa only [map_natCast] using
      (map_ne_zero_iff (algebraMap K F) (algebraMap K F).injective).mpr tame
  exact DifferentialPoles.pole_budget (paddedRes f) nonzero (p-2*r) fit (x′)
    (clears_finite b f primitive e2 dim tame' root x fx) hi

end Both
end Inverse

#print axioms clears_inverse_power
#print axioms common_coboundary_zero_generic
end
end Lower6960.MonicChart
