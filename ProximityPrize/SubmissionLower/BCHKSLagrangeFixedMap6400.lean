import ProximityPrize.SubmissionLower.BCHKSReceivedBivariate6400

/-! # Mapping Lagrange interpolation across fixed nodes -/

namespace ProximityPrize.SubmissionLower
namespace BCHKSGlobalInhomogeneousKeyEquation6400

open Polynomial

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

theorem lagrange_basis_map_of_fixed
    {F I : Type} [Field F] [DecidableEq I]
    (s : Finset I) (v : I → F) (sigma : F ≃+* F)
    (hfixed : ∀ i, sigma (v i) = v i) (i : I) :
    (Lagrange.basis s v i).map sigma.toRingHom =
      Lagrange.basis s v i := by
  classical
  simp only [Lagrange.basis, Lagrange.basisDivisor,
    Polynomial.map_prod, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_sub, Polynomial.map_X, map_inv₀, map_sub]
  apply Finset.prod_congr rfl
  intro j _hj
  rw [show sigma.toRingHom (v i) = v i from hfixed i,
    show sigma.toRingHom (v j) = v j from hfixed j]

theorem lagrange_interpolate_map_of_fixed
    {F I : Type} [Field F] [DecidableEq I]
    (s : Finset I) (v r : I → F) (sigma : F ≃+* F)
    (hfixed : ∀ i, sigma (v i) = v i) :
    (Lagrange.interpolate s v r).map sigma.toRingHom =
      Lagrange.interpolate s v (fun i ↦ sigma (r i)) := by
  classical
  simp only [Lagrange.interpolate_apply, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_C]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [lagrange_basis_map_of_fixed s v sigma hfixed i]
  rfl

/-- A polynomial of sufficiently small degree is the interpolation of its
coefficientwise image at fixed nodes.  This formulation treats the polynomial
as opaque and therefore avoids unfolding a concrete full-domain interpolator. -/
theorem polynomial_map_eq_lagrange_interpolate_of_fixed_eval
    {F I : Type} [Field F] [DecidableEq I]
    (s : Finset I) (v : I → F) (r : I → F)
    (sigma : F ≃+* F) (hfixed : ∀ i, sigma (v i) = v i)
    (W : F[X]) (hv : Set.InjOn v s)
    (hdegree : (W.map sigma.toRingHom).degree < (s.card : WithBot Nat))
    (heval : ∀ i ∈ s, W.eval (v i) = r i) :
    W.map sigma.toRingHom =
      Lagrange.interpolate s v (fun i ↦ sigma (r i)) := by
  apply Lagrange.eq_interpolate_of_eval_eq
    (fun i ↦ sigma (r i)) hv hdegree
  intro i hi
  have hmap := Polynomial.eval_map_apply
    (p := W) sigma.toRingHom (v i)
  calc
    (W.map sigma.toRingHom).eval (v i) =
        sigma.toRingHom (W.eval (v i)) := by
          simpa only [show sigma.toRingHom (v i) = v i from hfixed i]
            using hmap
    _ = sigma (r i) := by
      rw [heval i hi]
      rfl

/-- Two polynomials below the node-count degree bound are equal when their
values agree on all injective nodes.  Keeping both polynomials abstract avoids
any interpolation-expression conversion in concrete specializations. -/
theorem polynomial_eq_of_degree_lt_card_of_eval_eq
    {F I : Type} [Field F] [DecidableEq I]
    (s : Finset I) (v : I → F) (P Q : F[X])
    (hv : Set.InjOn v s)
    (hPdegree : P.degree < (s.card : WithBot Nat))
    (hQdegree : Q.degree < (s.card : WithBot Nat))
    (heval : ∀ i ∈ s, P.eval (v i) = Q.eval (v i)) :
    P = Q := by
  have hP := Lagrange.eq_interpolate_of_eval_eq
    (fun i ↦ P.eval (v i)) hv hPdegree (fun i _hi ↦ rfl)
  have hQ := Lagrange.eq_interpolate_of_eval_eq
    (fun i ↦ P.eval (v i)) hv hQdegree (fun i hi ↦ (heval i hi).symm)
  exact hP.trans hQ.symm

end BCHKSGlobalInhomogeneousKeyEquation6400
end ProximityPrize.SubmissionLower
