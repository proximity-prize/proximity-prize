/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833LinearKernel
namespace Frontier.LinearKernel
open Polynomial Finset
open scoped Polynomial Classical
noncomputable section
variable {K I : Type*} [Field K]
theorem polynomial_slope_joint (σ : K →+* K) (x : I ↪ K) (u v : I → K) (S : Finset I)
    (w : ℕ) (g : K) (P V a b L R : K[X]) (ha : a≠0) (deg : P.natDegree≤w) (dv : V.natDegree≤w)
    (compat : a.map σ*R=b*L.map σ) (poly : a*V=L)
    (fit : ∀ i∈S,P.eval (x i)=u i+g*v i)
    (fixed : ∀ i∈S,σ (x i)=x i)
    (active : ∀ i∈S,a.eval (x i)≠0 ∨ b.eval (x i)≠0)
    (raw : ∀ i∈S,a.eval (x i)*v i=L.eval (x i) ∧ b.eval (x i)*σ (v i)=R.eval (x i)) :
    ∃ M N : K[X], M.natDegree≤w ∧ N.natDegree≤w ∧
       ∀ i∈S, M.eval (x i)=u i ∧ N.eval (x i)=v i := by
  have other : R=b*V.map σ := by
    apply mul_left_cancel₀ (show a.map σ≠0 from Polynomial.map_ne_zero ha)
    rw [compat,←poly,Polynomial.map_mul]
    ring
  refine ⟨P-C g*V,V,(natDegree_sub_le ..).trans (max_le deg ((natDegree_C_mul_le ..).trans dv)),dv,?_⟩
  intro i hi
  obtain ⟨left,right⟩ := raw i hi
  rw [←poly,eval_mul] at left
  rw [other,eval_mul] at right
  have eq : V.eval (x i) = v i := by
    rcases active i hi with nz|nz
    · exact (mul_left_cancel₀ nz left).symm
    · apply σ.injective
      have im := eval_map_apply (p:=V) σ (x i)
      rw [fixed i hi] at im
      exact im.symm.trans (mul_left_cancel₀ nz right).symm
  simp [eval_sub,eval_mul,eval_C,eq,fit i hi]
#print axioms polynomial_slope_joint
end
end Frontier.LinearKernel
