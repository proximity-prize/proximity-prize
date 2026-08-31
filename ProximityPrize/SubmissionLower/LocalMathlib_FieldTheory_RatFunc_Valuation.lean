/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:Anne Baanen,Ashvni Narayanan
-/
import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.LocalMathlibPortLicense
import ProximityPrize.SubmissionLower.LocalMathlib_FieldTheory_RatFunc_Degree
section ProximityFlatProofPort
noncomputable section
namespace RatFunc
variable (F K:Type*) [Field F] [Field K]
section InftyValuation
open Multiplicative WithZero Polynomial
variable [DecidableEq (RatFunc F)]
def inftyValuationDef (r:RatFunc F):ℤᵐ⁰:=
  if r=0 then 0 else exp r.intDegree
theorem InftyValuation.map_zero':inftyValuationDef F 0=0:=
  if_pos rfl
theorem InftyValuation.map_one':inftyValuationDef F 1=1:=
  (if_neg one_ne_zero).trans <| by simp
theorem InftyValuation.map_mul' (x y:RatFunc F):
    inftyValuationDef F (x*y)=inftyValuationDef F x*inftyValuationDef F y:=by
  rw [inftyValuationDef,inftyValuationDef,inftyValuationDef]
  by_cases hx:x=0
  · rw [hx,zero_mul,if_pos (Eq.refl _),zero_mul]
  · by_cases hy:y=0
    · rw [hy,mul_zero,if_pos (Eq.refl _),mul_zero]
    · simp_all [RatFunc.intDegree_mul]
theorem InftyValuation.map_add_le_max' (x y:RatFunc F):
    inftyValuationDef F (x+y) ≤ max (inftyValuationDef F x) (inftyValuationDef F y):=by
  unfold inftyValuationDef
  have:=@RatFunc.intDegree_add_le F
  aesop
@[simp]
theorem inftyValuation_of_nonzero {x:RatFunc F} (hx:x≠0):
    inftyValuationDef F x=exp x.intDegree:=by
  rw [inftyValuationDef,if_neg hx]
def inftyValuation:Valuation (RatFunc F) ℤᵐ⁰ where
  toFun:=inftyValuationDef F
  map_zero':=InftyValuation.map_zero' F
  map_one':=InftyValuation.map_one' F
  map_mul':=InftyValuation.map_mul' F
  map_add_le_max':=InftyValuation.map_add_le_max' F
theorem inftyValuation_apply {x:RatFunc F}:inftyValuation F x=inftyValuationDef F x:=
  rfl
@[simp]
theorem inftyValuation.C {k:F} (hk:k≠0):
    inftyValuation F (RatFunc.C k)=1:=by
  simp [inftyValuation_apply,hk]
@[simp]
theorem inftyValuation.X:inftyValuation F RatFunc.X=exp 1:=by
  simp [inftyValuation_apply,inftyValuationDef,if_neg RatFunc.X_ne_zero,RatFunc.intDegree_X]
lemma inftyValuation.X_zpow (m:ℤ):inftyValuation F (RatFunc.X^m)=exp m:=by simp
theorem inftyValuation.X_inv:inftyValuation F (1/RatFunc.X)=exp (-1):=by
  rw [one_div, ←zpow_neg_one,inftyValuation.X_zpow]
theorem inftyValuation.polynomial {p:F[X]} (hp:p≠0):
    inftyValuationDef F (algebraMap F[X] (RatFunc F) p)=exp (p.natDegree:ℤ):=by
  rw [inftyValuationDef,if_neg (by simpa),RatFunc.intDegree_polynomial]
instance:Valuation.IsNontrivial (inftyValuation F):=⟨RatFunc.X,by simp⟩
instance:Valuation.IsTrivialOn F (inftyValuation F):=
  ⟨fun _ hx↦by simp [inftyValuation.C _ hx]⟩
@[implicit_reducible]
def inftyValued:Valued (RatFunc F) ℤᵐ⁰:=
  Valued.mk' <| inftyValuation F
theorem inftyValued.def {x:RatFunc F}:
    (inftyValued F).v x=inftyValuationDef F x:=
  rfl
namespace CompletionAtInfty
attribute [-instance] RatFunc.valuedRatFunc
scoped instance:UniformSpace (RatFunc F):=(inftyValued F).toUniformSpace
def _root_.RatFunc.CompletionAtInfty:=UniformSpace.Completion (RatFunc F)
deriving Field,Algebra (RatFunc F),Coe (RatFunc F),Inhabited
instance:Valued (CompletionAtInfty F) ℤᵐ⁰:=
  inferInstanceAs <| Valued (UniformSpace.Completion (RatFunc F)) ℤᵐ⁰
end CompletionAtInfty
theorem valuedCompletionAtInfty.def {x:CompletionAtInfty F}:
  Valued.v x=(inftyValued F).extensionValuation x:=rfl
end InftyValuation
end RatFunc
