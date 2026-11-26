import ProximityPrize.SubmissionLower.R6966ProofNonlinearMarkDegrees
import ProximityPrize.SubmissionLower.UpperBranch3

set_option Elab.async false

-- Source: Research6969.ShortenedOdeRows
set_option autoImplicit true
namespace Research6969.ShortenedOdeRows
noncomputable section
open K1 (K I p node)
open K1_14 (L FX atX liftPoly seedEmbedding)
open K1_14_2_4_2 (center eval_center factorial_ne_zero)
open Research6966 Research6966.NonlinearMarkRows Research6966.NonlinearMarkDegrees
open Polynomial Finset
open scoped Polynomial Differential BigOperators
attribute [local instance] GenericPhysicalCentre.physical GenericPhysicalCentre.seeds

private theorem jet_factor (S:K[X]) (j:ℕ) :
    Differential.deriv^[j] (atX S) =
        (j.factorial:FX)*(Polynomial.taylor center (S.map seedEmbedding)).coeff j := by
  rw [show Differential.deriv^[j] (atX S) = atX (Polynomial.derivative^[j] S) from by
    rw [atX,GenericPhysicalCentre.physical_iterate]
    simp [atX,liftPoly]]
  rw [Polynomial.taylor_coeff, Polynomial.hasseDeriv_map, eval_center]
  have h:=congrFun (Polynomial.factorial_smul_hasseDeriv (R:=K) j) S
  rw [← h, LinearMap.smul_apply]
  simp only [nsmul_eq_mul, atX, liftPoly, Polynomial.map_mul, Polynomial.map_natCast,
    map_mul, map_natCast]

/-- Concrete tests on regular solutions of the original ODE. The number of
Taylor orders used is the degree left after the common agreement nodes. -/
theorem exists_test {σ:Type*} (sites:Finset I) (recv:I→K) (d t:ℕ) (short:d≤sites.card+t)
    (tame:t<p) {r:ℕ} (rp:1≤r) (A B:Eqn σ FX)
    (ay:A.natDegree≤r) (byDeg:B.natDegree≤r+1) (i:I) :
    ∃ Q:Eqn σ FX, Q.natDegree≤(2*t-1)*r+1 ∧
      (∀ (axis:σ→ℕ) (u:ℕ), cap axis u A → cap axis u B → cap axis ((2*t-1)*u) Q) ∧
      ∀ (z:σ→FX) (S:K[X]), (∀ j,Differential.deriv (z j)=0) → S.natDegree≤d →
        (∀ k∈sites,S.eval (node k)=recv k) →
        evaluate z (atX S) A * atX S.derivative = evaluate z (atX S) B →
        evaluate z (atX S) A ≠ 0 →
        (evaluate z (atX S) Q=0 ↔ S.eval (node i)=recv i) := by
  obtain ⟨c,v,interpolate⟩:=P1_7_3.interpolation_weights sites d t short recv (node i)
  let weights (j:Fin (t+1)):=v j/(j.val.factorial:FX)
  refine ⟨weightedRow A B t (c-seedEmbedding (recv i)) weights,
    weightedRow_ordinate rp ay byDeg t _ weights,
    fun _ _ az bz=>weightedRow_seeds az bz t _ weights,?_⟩
  intro z S fixed deg common law regular
  have dx:Differential.deriv (atX S)=atX S.derivative := by
    rw [atX,GenericPhysicalCentre.physical_poly]
    simp [atX,liftPoly]
  have identity:=interpolate (S.map seedEmbedding) (natDegree_map_le.trans deg)
    (fun k hk=>by rw [Polynomial.eval_map_apply,common k hk])
  rw [Polynomial.eval_map_apply] at identity
  have jets (j:Fin (t+1)) : weights j*Differential.deriv^[j.val] (atX S) =
      v j*(Polynomial.taylor center (S.map seedEmbedding)).coeff j.val := by
    rw [jet_factor,show weights j=v j/(j.val.factorial:FX) from rfl,←mul_assoc]
    rw [div_mul_cancel₀ _ (factorial_ne_zero ((Nat.le_of_lt_succ j.isLt).trans_lt tame))]
  have ode : evaluate z (atX S) A * Differential.deriv (atX S) = evaluate z (atX S) B := by
    rwa [dx]
  rw [weightedRow_at z fixed (atX S) A B ode]
  simp_rw [jets]
  rw [mul_eq_zero,or_iff_right (pow_ne_zero _ regular)]
  rw [← seedEmbedding.injective.eq_iff (a:=S.eval (node i)) (b:=recv i), identity]
  constructor <;> intro h <;> linear_combination h

end
end Research6969.ShortenedOdeRows
