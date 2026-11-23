import ProximityPrize.SubmissionLower.R6960MonicChartInfinityPolynomial

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 2700000

namespace Lower6960.MonicChart
noncomputable section
open Polynomial
open scoped Polynomial

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]

abbrev Infinity (K : Type*) [Field K] [DecidableEq (RatFunc K)] := SheetNorm.Infinity K

private theorem valuation_reciprocal_pow (n : ℕ) :
    RatFunc.inftyValuation K (((RatFunc.X : RatFunc K)⁻¹)^n)=WithZero.exp (-(n:ℤ)) := by
  rw [show ((RatFunc.X : RatFunc K)⁻¹)^n=RatFunc.X^(-(n:ℤ)) by rw [zpow_neg,zpow_natCast,inv_pow],
    RatFunc.inftyValuation.X_zpow]

private theorem invert_poly (p : K[X]) :
    AtInfinity K p=algebraMap K[X] (RatFunc K) p.reverse * ((RatFunc.X : RatFunc K)⁻¹)^p.natDegree := by
  have reflect_twice : p.reverse.reflect p.natDegree=p := by
    apply Polynomial.ext
    intro i
    rw [coeff_reflect,coeff_reverse,revAt_invol]
  have eq := reverse_atInfinity p.reverse p.natDegree (reverse_natDegree_le p)
  rwa [reflect_twice] at eq

/-- A polynomial in the inverse abscissa has its expected valuation at
infinity. In particular a nonzero constant coefficient is a unit test. -/
theorem val_poly_infinity (p : K[X]) (pn : p≠0) :
    RatFunc.inftyValuation K (AtInfinity K p)=WithZero.exp (-(p.natTrailingDegree:ℤ)) := by
  rw [invert_poly,map_mul,valuation_reciprocal_pow]
  change RatFunc.inftyValuationDef K (algebraMap K[X] (RatFunc K) p.reverse) * _ = _
  rw [RatFunc.inftyValuation.polynomial _ (reverse_eq_zero.not.mpr pn),←WithZero.exp_add]
  have d := congrArg (fun n : ℕ => (n:ℤ)) (natDegree_eq_reverse_natDegree_add_natTrailingDegree p)
  push_cast at d
  congr 1
  omega

def inftyRingEval (K : Type*) [Field K] [DecidableEq (RatFunc K)] : K[X]→+*Infinity K where
  toFun p := ⟨AtInfinity K p,by
    change RatFunc.inftyValuation K (AtInfinity K p)≤1
    by_cases h : p=0
    · simp [h]
    rw [val_poly_infinity p h,←WithZero.exp_zero,WithZero.exp_le_exp]
    omega⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' p q := Subtype.ext (map_add _ _ _)
  map_mul' p q := Subtype.ext (map_mul _ _ _)

theorem inftyRingEval_injective : Function.Injective (inftyRingEval K) :=
  fun a b eq => atInfinity_injective (K:=K) (congrArg Subtype.val eq)

theorem inftyRingEval_isUnit (p : K[X]) (co : p.coeff 0≠0) :
    IsUnit (inftyRingEval K p) := by
  let a := inftyRingEval K p
  have pn : p≠0 := fun h=>co (by rw [h,coeff_zero])
  have val : RatFunc.inftyValuation K (a:RatFunc K)=1 := by
    change RatFunc.inftyValuation K (AtInfinity K p)=1
    rw [val_poly_infinity p pn,natTrailingDegree_eq_zero.mpr (Or.inr co)]
    simp
  have an : (a:RatFunc K)≠0 :=
    (map_ne_zero_iff _ (atInfinity_injective (K:=K))).mpr pn
  let inv : Infinity K := ⟨(a:RatFunc K)⁻¹,by
    change RatFunc.inftyValuation K (a:RatFunc K)⁻¹≤1
    rw [map_inv₀,val,inv_one]⟩
  exact ⟨⟨a,inv,Subtype.ext (mul_inv_cancel₀ an),Subtype.ext (inv_mul_cancel₀ an)⟩,rfl⟩

theorem mapped_X_infty :
    ((inftyRingEval K (Polynomial.X : K[X])):RatFunc K)=RatFunc.X⁻¹ := by
  change (AtInfinity K) (Polynomial.X : K[X])=_
  exact aeval_X _

/-- The homogeneous resultant has a unit factor times the exact
remaining inverse-abscissa power. -/
theorem reflected_local_factor (p : K[X]) (d : ℕ) (fit : p.natDegree≤d) :
    inftyRingEval K (p.reflect d)=
      (inftyRingEval K (Polynomial.X : K[X]))^(d-p.natDegree)*inftyRingEval K p.reverse := by
  apply Subtype.ext
  change AtInfinity K (p.reflect d) =
    ((inftyRingEval K (Polynomial.X : K[X])):RatFunc K)^(d-p.natDegree)*AtInfinity K p.reverse
  have tail : AtInfinity K p.reverse=
      algebraMap K[X] (RatFunc K) p*((RatFunc.X : RatFunc K)⁻¹)^p.natDegree :=
    reverse_atInfinity p p.natDegree le_rfl
  have eq : ((RatFunc.X : RatFunc K)⁻¹)^d =
      ((RatFunc.X : RatFunc K)⁻¹)^(d-p.natDegree)*((RatFunc.X : RatFunc K)⁻¹)^p.natDegree := by
    rw [←pow_add,Nat.sub_add_cancel fit]
  rw [mapped_X_infty,reverse_atInfinity _ _ fit,tail,eq]
  ring

#print axioms reflected_local_factor
end
end Lower6960.MonicChart
