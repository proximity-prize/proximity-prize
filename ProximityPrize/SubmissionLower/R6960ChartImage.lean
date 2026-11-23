import ProximityPrize.SubmissionLower.R6960MonicChartInfinityRing
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section
set_option Elab.async false
namespace Lower6960.ChartImage
open Polynomial MonicChart
open scoped Polynomial BigOperators
variable {K J : Type*} [Field K] [Fintype J] [DecidableEq (RatFunc K)]

/-- Scalar corrections made independently in ambient coordinates land back in a fixed
field-linear subspace once the negative abscissa twist exceeds its equation degrees. -/
theorem eventually_in_subspace (V : Submodule (RatFunc K) (J → RatFunc K)) :
    ∃ H : ℕ, ∀ a : ℕ, H<a → ∀ c v w : J → RatFunc K, v∈V → w∈V →
      (∀ j, c j-v j ∈ (algebraMap K[X] (RatFunc K)).range) →
      (∀ j, RatFunc.X^a*(c j-w j) ∈ (Infinity K)) → c∈V := by
  classical
  obtain ⟨Q,compl⟩ := V.exists_isCompl
  let P := Q.projection V compl.symm
  let M := LinearMap.toMatrix' P
  let ι := algebraMap K[X] (RatFunc K)
  obtain ⟨d,clear⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors K[X]) (fun x : J×J => M x.1 x.2)
  choose pol value using clear
  have entry (i j : J) : ι (pol (i,j))=ι (d:K[X])*M i j := by
    simpa only [Algebra.smul_def] using value (i,j)
  let H:=Finset.univ.sup (fun p : J×J => (pol p).natDegree)
  refine ⟨H,fun a ha c v w hv hw finite infinity => ?_⟩
  have equation (i : J) (u : J → RatFunc K) :
      ι (d:K[X])*P u i=∑ j,ι (pol (i,j))*u j := by
    rw [←LinearMap.toMatrix'_mulVec P u]
    change _*(∑ j,M i j*u j) = _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [entry,mul_assoc])
  have residual (i : J) (l : J→RatFunc K) (hl : l∈V) :
      ι (d:K[X])*P c i=∑ j,ι (pol (i,j))*(c j-l j) := by
    have pl : P l=0 := Q.projection_apply_of_mem_right compl.symm hl
    simpa only [map_sub,pl,sub_zero,Pi.sub_apply,Pi.zero_apply] using equation i (c-l)
  have projected : P c=0 := by
    funext i
    let q:=ι (d:K[X])*P c i
    have fin : q∈ι.range := by
      dsimp only [q]
      rw [residual i v hv]
      exact ι.range.sum_mem (fun j _ => ι.range.mul_mem ⟨_,rfl⟩ (finite j))
    have inf : RatFunc.X*q ∈ (Infinity K) := by
      change RatFunc.X*(ι (d:K[X])*P c i) ∈ (Infinity K)
      rw [residual i w hw,Finset.mul_sum]
      apply (Infinity K).sum_mem
      intro j _
      have bound : (pol (i,j)).natDegree ≤ a-1 :=
        (Finset.le_sup (f:=fun p:J×J=>(pol p).natDegree) (Finset.mem_univ (i,j))).trans
          (show H≤a-1 by omega)
      let r:=inftyRingEval K ((pol (i,j)).reflect (a-1))
      have form : (r:RatFunc K)=ι (pol (i,j))*RatFunc.X⁻¹^(a-1) :=
        reverse_atInfinity _ _ bound
      have eq : (r:RatFunc K)*(RatFunc.X^a*(c j-w j)) =
          RatFunc.X*(ι (pol (i,j))*(c j-w j)) := by
        have split : a-1+1=a := Nat.sub_add_cancel (by omega)
        have cancel : (RatFunc.X⁻¹ : RatFunc K)^(a-1)*RatFunc.X^a=RatFunc.X := by
          conv_lhs => rhs; rw [←split,pow_succ]
          rw [←mul_assoc,←mul_pow,inv_mul_cancel₀ RatFunc.X_ne_zero,one_pow,one_mul]
        rw [form]
        linear_combination ι (pol (i,j))*(c j-w j)*cancel
      exact eq ▸ (Infinity K).toSubring.mul_mem r.property (infinity j)
    obtain ⟨p,pe⟩:=fin
    have integral : IsIntegral K[X] q := pe ▸ isIntegral_algebraMap
    have intInf : IsIntegral (Infinity K) (RatFunc.X*q) :=
      isIntegral_algebraMap (x:=(⟨_,inf⟩ : Infinity K))
    have zero : q=0 := DifferentialPoles.negative_twist q integral (by simpa using intInf)
    exact (mul_eq_zero.mp zero).resolve_left
      ((map_ne_zero_iff _ (IsFractionRing.injective K[X] _)).mpr (mem_nonZeroDivisors_iff_ne_zero.mp d.property))
  exact (Q.projection_apply_eq_zero_iff compl.symm).mp projected

#print axioms eventually_in_subspace
end Lower6960.ChartImage
