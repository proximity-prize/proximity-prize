/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
import ProximityPrize.SubmissionLower.Mid6833TwistResidual
import ProximityPrize.SubmissionLower.Mid6833FrobeniusModule

namespace Frontier6969.GenuineMoving
open Polynomial Finset ProximityPrize.SubmissionLower
open Koala6831Separation (NormalForm Seeds pairDegree)
open Koala6831Comparison (SymbolicRow primitiveExcess)
open scoped Polynomial Classical
noncomputable section
variable {K : Type} [Field K]

private theorem pair_active (x : K) (A : Fin 2 → K[X]) (cp : IsCoprime (A 0) (A 1)) :
    ∃ j, (A j).eval x ≠ 0 := by
  by_contra! hz
  obtain ⟨u,v,id⟩ := cp
  have h := congrArg (Polynomial.eval x) id
  simp only [eval_add,eval_mul,eval_one,hz,mul_zero,add_zero] at h
  exact zero_ne_one h

/-- In a varying normalized family the two fixed denominators have identical
root sets in the fixed field of the coefficient endomorphism. -/
theorem fixed_pole_equiv (σ : K →+* K) {q : SymbolicRow (Seeds K)} {w δ : ℕ}
    (N : NormalForm q w δ) (ker : CommonKernel σ N) (x : K) (hx : σ x=x) :
    N.d₀.eval x=0 ↔ N.d₁.eval x=0 := by
  obtain ⟨R,rn,row⟩ := ker
  have at_x (j : Fin 2) : ∃ a : K, a≠0 ∧
      N.d₁.eval x * σ ((N.A j).eval x) * σ a =
      σ (N.d₀.eval x) * (N.B j).eval x * a := by
    let L := N.d₁*(N.A j).map σ
    let Q := N.d₀.map σ*N.B j
    obtain ⟨H,hn,hs,minimal⟩ := KoalaFrontier.exists_minimal σ L Q ⟨R,rn,row j⟩
    refine ⟨H.eval x,KoalaFrontier.generator_avoids_fixed_nodes σ L Q H hn hs minimal x hx,?_⟩
    have he := congrArg (Polynomial.eval x) hs
    have ev (P : K[X]) : (P.map σ).eval x=σ (P.eval x) := by simpa only [hx] using eval_map_apply (p:=P) σ x
    simpa only [L,Q,eval_mul,ev] using he
  constructor
  · intro h0
    obtain ⟨j,nj⟩ := pair_active x N.A N.A_coprime
    obtain ⟨a,na,eq⟩ := at_x j
    simp only [h0,map_zero,zero_mul] at eq
    exact (mul_eq_zero.mp ((mul_eq_zero.mp eq).resolve_right ((map_ne_zero σ).mpr na))).resolve_right ((map_ne_zero σ).mpr nj)
  · intro h1
    obtain ⟨j,nj⟩ := pair_active x N.B N.B_coprime
    obtain ⟨a,na,eq⟩ := at_x j
    simp only [h1,zero_mul] at eq
    exact (map_eq_zero σ).mp ((mul_eq_zero.mp ((mul_eq_zero.mp eq.symm).resolve_right na)).resolve_right nj)

/-- Coprime denominators therefore preserve every selected agreement when
polynomial remainders are decoded into intercept and slope. -/
theorem coprime_poles_avoid_nodes (σ : K →+* K) {q : SymbolicRow (Seeds K)} {w δ : ℕ}
    (N : NormalForm q w δ) (ker : CommonKernel σ N) (cp : IsCoprime N.d₀ N.d₁)
    (x : K) (hx : σ x=x) : N.d₀.eval x ≠ 0 ∧ N.d₁.eval x ≠ 0 := by
  have eq := fixed_pole_equiv σ N ker x hx
  obtain ⟨u,v,id⟩ := cp
  have both : N.d₀.eval x ≠ 0 := by
    intro h0
    have h := congrArg (Polynomial.eval x) id
    simp only [eval_add,eval_mul,eval_one,h0,eq.mp h0,mul_zero,add_zero] at h
    exact zero_ne_one h
  exact ⟨both,fun h1 => both (eq.mpr h1)⟩

#print axioms fixed_pole_equiv
#print axioms coprime_poles_avoid_nodes
end
end Frontier6969.GenuineMoving
