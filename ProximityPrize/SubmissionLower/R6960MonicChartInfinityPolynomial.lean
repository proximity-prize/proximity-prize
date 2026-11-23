import ProximityPrize.SubmissionLower.R6960MonicChartScaled
import Mathlib.FieldTheory.RatFunc.AsPolynomial

set_option Elab.async false
set_option maxRecDepth 17000
set_option maxHeartbeats 3100000

namespace Lower6960.MonicChart
noncomputable section
open Polynomial
open scoped Polynomial BigOperators

variable {K : Type*} [Field K]

abbrev AtInfinity (K : Type*) [Field K] : K[X]→+*RatFunc K :=
  (aeval ((RatFunc.X : RatFunc K)⁻¹)).toRingHom

theorem atInfinity_injective : Function.Injective (AtInfinity K) := by
  have tx := RatFunc.transcendental_X (K:=K)
  have ti : Transcendental K ((RatFunc.X : RatFunc K)⁻¹) := by
    simpa only [Transcendental,IsAlgebraic.inv_iff] using tx
  exact transcendental_iff_injective.mp ti

/-- Inverting the abscissa and multiplying by its homogenizing power
preserves a polynomial with the declared degree bound. -/
theorem reverse_atInfinity (g : K[X]) (n : ℕ) (ng : g.natDegree≤n) :
    AtInfinity K (g.reflect n) =
      algebraMap K[X] (RatFunc K) g*((RatFunc.X : RatFunc K)⁻¹)^n := by
  let x : RatFunc K := RatFunc.X
  have xn : x≠0 := RatFunc.X_ne_zero
  letI : Invertible x := invertibleOfNonzero xn
  have h := eval₂_reflect_mul_pow (algebraMap K (RatFunc K)) x n g ng
  have evalX : g.eval₂ (algebraMap K (RatFunc K)) x=algebraMap K[X] (RatFunc K) g :=
    RatFunc.aeval_X_left_eq_algebraMap g
  rw [invOf_eq_inv,evalX] at h
  apply mul_right_cancel₀ (pow_ne_zero _ xn)
  change (g.reflect n).eval₂ (algebraMap K (RatFunc K)) x⁻¹*x^n=_
  rw [h,mul_assoc,←mul_pow,inv_mul_cancel₀ xn,one_pow,mul_one]

/-- The infinity equation uses the base coordinate (T=1/X) and the
ordinate (T^d Y). Its coefficients are separately homogenized. -/
def weightedInfinity (f : K[X][X]) (H d : ℕ) : K[X][X] :=
  ∑ i∈f.support, monomial i ((f.coeff i).reflect (H-d*i))

theorem coeff_weightedInfinity (f : K[X][X]) (H d i : ℕ) :
    (weightedInfinity f H d).coeff i=(f.coeff i).reflect (H-d*i) := by
  classical
  by_cases mem : i∈f.support
  · rw [weightedInfinity,Polynomial.finsetSum_coeff,Finset.sum_eq_single_of_mem i mem]
    · simp
    · intro j _ neq; simp [coeff_monomial,neq]
  · simp [weightedInfinity,Polynomial.finsetSum_coeff,coeff_monomial,mem,notMem_support_iff.mp mem]

theorem infinity_degree (f : K[X][X]) (H d : ℕ) : (weightedInfinity f H d).natDegree=f.natDegree := by
  by_cases fn : f=0
  · simp [fn,weightedInfinity]
  apply le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [coeff_weightedInfinity,coeff_eq_zero_of_natDegree_lt hj,reflect_zero]
  · apply le_natDegree_of_ne_zero
    rw [coeff_weightedInfinity,coeff_natDegree]
    intro zero
    let b := f.leadingCoeff
    have nz : b≠0 := leadingCoeff_ne_zero.mpr fn
    apply nz
    apply Polynomial.ext
    intro j
    have req := congrArg (fun q : K[X] => q.coeff (revAt (H-d*f.natDegree) j)) zero
    simp only [coeff_reflect,revAt_invol,coeff_zero] at req
    exact req

theorem infinity_leading (f : K[X][X]) (H d : ℕ) :
    (weightedInfinity f H d).leadingCoeff=f.leadingCoeff.reflect (H-d*f.natDegree) := by
  rw [leadingCoeff,infinity_degree,coeff_weightedInfinity,coeff_natDegree]

/-- The infinity equation agrees with homogeneous coordinate change over
the abscissa function field, with the leading scalar explicitly tracked. -/
theorem infinity_field (f : K[X][X]) (H d : ℕ)
    (weights : ∀ i≤f.natDegree,(f.coeff i).natDegree+d*i≤H) :
    (weightedInfinity f H d).map (AtInfinity K)=
      C (((RatFunc.X : RatFunc K)⁻¹)^(H-d*f.natDegree))*
        ((f.map (algebraMap K[X] (RatFunc K))).scaleRoots (((RatFunc.X : RatFunc K)⁻¹)^d)) := by
  let j := algebraMap K[X] (RatFunc K)
  let t := ((RatFunc.X : RatFunc K)⁻¹)
  let e := f.natDegree
  have hf : (f.map j).natDegree=e := natDegree_map_eq_of_injective (IsFractionRing.injective _ _) _
  have de : d*e ≤ H := (Nat.le_add_left ..).trans (weights _ le_rfl)
  apply Polynomial.ext
  intro i
  rw [coeff_map,coeff_weightedInfinity,coeff_C_mul,coeff_scaleRoots,coeff_map,hf]
  change AtInfinity K ((f.coeff i).reflect (H-d*i))=t^(H-d*e)*(j (f.coeff i)*(t^d)^(e-i))
  by_cases small : i≤e
  · have hi := weights i small
    have eq : H-d*i=(H-d*e)+d*(e-i) := by
      have hd : d*(e-i)+d*i=d*e := by rw [← Nat.mul_add,Nat.sub_add_cancel small]
      omega
    rw [reverse_atInfinity _ _ (by omega),eq,pow_add,pow_mul]
    ring
  · have large : f.natDegree < i := Nat.lt_of_not_ge small
    rw [coeff_eq_zero_of_natDegree_lt large,reflect_zero,map_zero,map_zero,zero_mul,mul_zero]

/-- The exponent of the homogenized padded derivative resultant. -/
def resultantWidth (e H d : ℕ) : ℕ :=
  (H-d*e)*(e+(e-1))+d*(e*(e-1))

theorem resultantWidth_eq {e H d : ℕ} (pos : 0<e) (fit : d*e≤H) :
    resultantWidth e H d+d*e^2=(2*e-1)*H := by
  let a := H-d*e
  have eqH : H=a+d*e := (Nat.sub_add_cancel fit).symm
  obtain ⟨k,eq⟩ := Nat.exists_eq_add_of_le (show 1≤e from pos)
  unfold resultantWidth
  change a*(e+(e-1))+d*(e*(e-1))+d*e^2=(2*e-1)*H
  rw [eqH,eq,show 1+k-1=k by omega,show 2*(1+k)-1=2*k+1 by omega]
  ring

/-- Padded resultants commute with weighted inversion. The identical
declared ordinate degree is used in the finite and infinity equations. -/
theorem infinity_resultant (f : K[X][X]) (H d : ℕ) (pos : 0<f.natDegree)
    (tame : (f.natDegree:K)≠0)
    (weights : ∀ i≤f.natDegree,(f.coeff i).natDegree+d*i≤H)
    (resBound : (paddedRes f).natDegree≤resultantWidth f.natDegree H d) :
    paddedRes (weightedInfinity f H d)=
      (paddedRes f).reflect (resultantWidth f.natDegree H d) := by
  let e := f.natDegree
  let t := ((RatFunc.X : RatFunc K)⁻¹)
  let j := algebraMap K[X] (RatFunc K)
  let g := weightedInfinity f H d
  let P := f.map j
  have pdeg : P.natDegree=e := natDegree_map_eq_of_injective (IsFractionRing.injective _ _) _
  have tn : t≠0 := inv_ne_zero RatFunc.X_ne_zero
  have etame : (e : RatFunc K)≠0 := by
    simpa only [map_natCast,e] using
      (map_ne_zero_iff (algebraMap K (RatFunc K)) (algebraMap K (RatFunc K)).injective).mpr tame
  have pder : P.derivative.natDegree=P.natDegree-1 := derivative_degree P
    (pdeg ▸ pos) (pdeg ▸ etame)
  have fromFinite : j (paddedRes f)=P.resultant P.derivative e (e-1) := by
    unfold paddedRes
    rw [←resultant_map_map,←derivative_map]
  have power := resultant_scaleRoots P P.derivative (t^d)
  have scale : (P.scaleRoots (t^d)).resultant (P.derivative.scaleRoots (t^d)) e (e-1)=
      t^(d*(e*(e-1)))*j (paddedRes f) := by
    rw [natDegree_scaleRoots,natDegree_scaleRoots,pder,pdeg,←pow_mul,←fromFinite] at power
    exact power
  apply atInfinity_injective (K:=K)
  change AtInfinity K (paddedRes g)=_
  rw [reverse_atInfinity _ _ resBound]
  change AtInfinity K (g.resultant g.derivative g.natDegree (g.natDegree-1))=_
  rw [←resultant_map_map,←derivative_map,infinity_degree,
    infinity_field f H d weights,derivative_C_mul,scaleRoots_derivative _ _ pder,
    resultant_C_mul_left,resultant_C_mul_right]
  change (t^(H-d*e))^(e-1)*((t^(H-d*e))^e*
      (P.scaleRoots (t^d)).resultant (P.derivative.scaleRoots (t^d)) e (e-1))=_
  rw [scale,←mul_assoc,←pow_add,←pow_mul,←mul_assoc,←pow_add]
  unfold resultantWidth
  ring

#print axioms infinity_resultant
end
end Lower6960.MonicChart
