import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic
import ProximityPrize.SubmissionLower.KoalaTwoCutMarkedFacts

set_option autoImplicit false

namespace SplitCut.StableNode

open Polynomial

private theorem splitTrailing {R : Type*} [CommRing R] (P : R[X]) :
    ∃ Q : R[X], P = X ^ P.natTrailingDegree * Q ∧
      Q.coeff 0 = P.coeff P.natTrailingDegree := by
  obtain ⟨Q, hQ⟩ := (X_pow_dvd_iff.mpr fun _ h =>
    coeff_eq_zero_of_lt_natTrailingDegree (p := P) h)
  refine ⟨Q, hQ, ?_⟩
  have h := congrArg (fun F : R[X] => F.coeff (0 + P.natTrailingDegree)) hQ
  rwa [coeff_X_pow_mul, zero_add, eq_comm] at h

/-- Evaluate the inner polynomial variable on a polynomial in the outer variable. -/
noncomputable def substitute {R : Type*} [CommRing R] (s : R[X]) : Polynomial R[X] →+* R[X] :=
  eval₂RingHom (eval₂RingHom C s) X

private theorem eval_substitute_zero {R : Type*} [CommRing R] (s : R[X])
    (Q : Polynomial R[X]) : (substitute s Q).eval 0 = (Q.coeff 0).eval (s.eval 0) := by
  change evalRingHom (0 : R) (Q.eval₂ (eval₂RingHom C s) X) = _
  rw [hom_eval₂]
  change Q.eval₂ _ ((X : R[X]).eval 0) = _
  rw [eval_X, eval₂_at_zero]
  change evalRingHom (0 : R) ((Q.coeff 0).eval₂ C s) = _
  rw [hom_eval₂]
  change (Q.coeff 0).eval₂ _ (s.eval 0) = _
  rw [← eval₂_id]
  congr 1
  ext a
  simp

/-- A single coefficient cuts every hitting specialization of a root branch.
    The source polynomial is expressed in the shifted variables. The generic
    branch has a nonzero value at the node, while a hitting mark sends it to zero. -/
theorem separating_coefficient {R A : Type*} [CommRing R] [CommRing A] [IsDomain A]
    (ι : R →+* A) (G : Polynomial R[X]) (s : A[X])
    (hG : G.map (mapRingHom ι) ≠ 0) (hroot : substitute s (G.map (mapRingHom ι)) = 0)
    (hs : s.eval 0 ≠ 0) :
    ∃ i j : ℕ, ι ((G.coeff i).coeff j) ≠ 0 ∧
      ∀ {F : Type*} [CommRing F] (ψ : A →+* F), ψ (s.eval 0) = 0 →
        ψ (ι ((G.coeff i).coeff j)) = 0 := by
  let P := G.map (mapRingHom ι)
  obtain ⟨Q, hQ, hc⟩ := splitTrailing P
  have hQzero : substitute s Q = 0 := by
    change substitute s P = 0 at hroot
    rw [hQ, map_mul, map_pow, show substitute s (X : Polynomial A[X]) = X by
      exact eval₂_X _ _] at hroot
    exact (mul_eq_zero.mp hroot).resolve_left (pow_ne_zero _ X_ne_zero)
  have hH : (P.coeff P.natTrailingDegree).eval (s.eval 0) = 0 := by
    rw [← hc, ← eval_substitute_zero, hQzero, eval_zero]
  let H := P.coeff P.natTrailingDegree
  have hHne : H ≠ 0 := coeff_natTrailingDegree_ne_zero.mpr hG
  obtain ⟨L, hL, he⟩ := splitTrailing H
  have hLzero : L.eval (s.eval 0) = 0 := by
    change H.eval (s.eval 0) = 0 at hH
    rw [hL, eval_mul, eval_pow, eval_X] at hH
    exact (mul_eq_zero.mp hH).resolve_left (pow_ne_zero _ hs)
  have hh : ι ((G.coeff P.natTrailingDegree).coeff H.natTrailingDegree) = L.coeff 0 := by
    rw [he]
    simp [H, P]
  refine ⟨P.natTrailingDegree, H.natTrailingDegree, ?_, ?_⟩
  · rw [hh, he]
    exact coeff_natTrailingDegree_ne_zero.mpr hHne
  · intro F _ ψ hψ
    rw [hh]
    have he : ψ (L.eval (s.eval 0)) = ψ (L.coeff 0) := by
      change ψ (L.eval₂ (RingHom.id A) (s.eval 0)) = _
      rw [hom_eval₂, hψ, eval₂_at_zero, RingHom.comp_id]
    exact he.symm.trans ((congrArg ψ hLzero).trans ψ.map_zero)

end SplitCut.StableNode

#print axioms SplitCut.StableNode.separating_coefficient
