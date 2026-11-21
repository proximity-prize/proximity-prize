import ProximityPrize.SubmissionLower.KoalaStableNode
import ProximityPrize.SubmissionLower.KoalaJetTaylor

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SplitCut.FreshRoot

open Polynomial StableNode
open HighCore82229Upper_4 (coeffDeriv coeff_coeffDeriv coeffDeriv_C coeffDeriv_X)

private theorem derivative_constant {E : Type} [Field E] (δ : Derivation ℤ E E)
    {P : E[X]} (h : coeffDeriv δ P = 0) : coeffDeriv δ P.derivative = 0 := by
  apply Polynomial.ext
  intro i
  have hi := congrArg (fun R : E[X] => R.coeff (i+1)) h
  rw [coeff_coeffDeriv, coeff_zero] at hi
  have hd : δ ((i : E) + 1) = 0 := by simp only [map_add, δ.map_natCast, δ.map_one_eq_zero, add_zero]
  rw [coeff_coeffDeriv, coeff_derivative, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
    hd, hi, mul_zero, mul_zero, add_zero, coeff_zero]

/-- A polynomial of degree below the characteristic with differential-constant
    coefficients is determined by its value at a point whose derivative is one. -/
theorem fresh_identity {E : Type} [Field E] (p : ℕ) [CharP E p] (δ : Derivation ℤ E E)
    (x : E) (hx : δ x = 1) (P : E[X]) (hc : coeffDeriv δ P = 0)
    (hp : P.natDegree < p) (hz : P.eval x = 0) : P = 0 := by
  by_cases h : P.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero h] at hz ⊢
    rw [eval_C] at hz
    rw [hz, map_zero]
  · have hcoeff : δ.mapCoeffs P = 0 := by
      apply PolynomialModule.coeff_injective
      apply Finsupp.ext
      intro i
      have hi := congrArg (fun Q : E[X] => Q.coeff i) hc
      simpa only [coeff_coeffDeriv, coeff_zero, Derivation.mapCoeffs_apply,
        PolynomialModule.coeff_zero, Finsupp.zero_apply] using hi
    have h' := δ.apply_eval_eq x P
    rw [hz, map_zero, hcoeff, map_zero, zero_add, hx, smul_eq_mul, mul_one] at h'
    have hd := fresh_identity p δ x hx P.derivative (derivative_constant δ hc)
      ((natDegree_derivative_lt h).trans hp) h'.symm
    have he := congrArg (fun Q : E[X] => Q.coeff (P.natDegree-1)) hd
    have hh : P.natDegree-1+1 = P.natDegree := by omega
    simp only [coeff_derivative, hh, coeff_natDegree, coeff_zero] at he
    have hhE : ((P.natDegree-1 : ℕ) : E)+1 = (P.natDegree : E) := by
      simpa only [Nat.cast_add, Nat.cast_one] using congrArg (Nat.cast (R:=E)) hh
    rw [hhE] at he
    rcases mul_eq_zero.mp he with hl | hn
    · exact leadingCoeff_eq_zero.mp hl
    · exact (hp.not_ge (Nat.le_of_dvd (by omega) ((CharP.cast_eq_zero_iff E p _).mp hn))).elim
termination_by P.natDegree
decreasing_by exact natDegree_derivative_lt h

theorem substitute_eval {E : Type} [CommRing E] (P : Polynomial E[X]) (s : E[X]) (x : E) :
    (substitute s P).eval x = P.eval₂ (evalRingHom (s.eval x)) x := by
  change evalRingHom x (P.eval₂ (eval₂RingHom C s) (Polynomial.X : E[X])) = _
  rw [hom_eval₂]
  have h : (evalRingHom x).comp (eval₂RingHom C s) = evalRingHom (s.eval x) := by
    apply Polynomial.ringHom_ext
    · intro a
      change (evalRingHom x ((C a).eval₂ C s)) = _
      rw [eval₂_C]
      simp
    · change evalRingHom x ((Polynomial.X : Polynomial E).eval₂ (C : E →+* E[X]) s) = _
      rw [eval₂_X]
      change s.eval x = (Polynomial.X : E[X]).eval (s.eval x)
      rw [eval_X]
  rw [h]
  change P.eval₂ (evalRingHom (s.eval x)) ((Polynomial.X : E[X]).eval x) = _
  rw [eval_X]

theorem map_substitute {R E : Type} [CommRing R] [CommRing E] (φ : R →+* E)
    (P : Polynomial R[X]) (S : R[X]) :
    (substitute S P).map φ = substitute (S.map φ) (P.map (mapRingHom φ)) := by
  let ψ := mapRingHom φ
  let β : R[X] →+* R[X] := eval₂RingHom C S
  let γ : E[X] →+* E[X] := eval₂RingHom C (S.map φ)
  change ψ (P.eval₂ β (Polynomial.X : R[X])) = (P.map ψ).eval₂ γ (Polynomial.X : E[X])
  rw [hom_eval₂, eval₂_map, show ψ (Polynomial.X : R[X]) = Polynomial.X from map_X _]
  congr 1
  apply Polynomial.ringHom_ext
  · intro a
    change (mapRingHom φ) ((C a).eval₂ C S) = ((C a).map φ).eval₂ C (S.map φ)
    rw [eval₂_C, map_C, eval₂_C]
    exact map_C φ
  · change (mapRingHom φ) ((Polynomial.X : R[X]).eval₂ C S) =
      ((Polynomial.X : R[X]).map φ).eval₂ C (S.map φ)
    rw [eval₂_X, map_X, eval₂_X]
    rfl

private theorem substitute_degree {R E : Type} [CommRing R] [Field E] (φ : R →+* E)
    (G : Polynomial R[X]) (S : E[X]) {e d : ℕ} (he : ∀ i, (G.coeff i).natDegree ≤ e)
    (hS : S.natDegree ≤ d) :
    (substitute S (G.map (mapRingHom φ))).natDegree ≤ G.natDegree + e*d := by
  let Q := G.map (mapRingHom φ)
  let a : E[X] →+* E[X] := eval₂RingHom C S
  change (Q.eval₂ a (Polynomial.X : E[X])).natDegree ≤ _
  rw [eval₂_eq_sum_range]
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have h₁ : i ≤ G.natDegree := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans natDegree_map_le
  have h₂ : (a (Q.coeff i)).natDegree ≤ e*d := by
    change (((Q.coeff i).comp S).natDegree ≤ e*d)
    apply natDegree_comp_le.trans
    exact Nat.mul_le_mul (by dsimp only [Q]; rw [coeff_map, coe_mapRingHom]; exact natDegree_map_le.trans (he i)) hS
  exact natDegree_mul_le.trans (by rw [natDegree_X_pow]; omega)

private theorem substitute_constant {R E : Type} [CommRing R] [Field E] (φ : R →+* E)
    (G : Polynomial R[X]) (S : E[X]) (δ : Derivation ℤ E E)
    (hφ : ∀ a, δ (φ a) = 0) (hS : coeffDeriv δ S = 0) :
    coeffDeriv δ (substitute S (G.map (mapRingHom φ))) = 0 := by
  let Q := G.map (mapRingHom φ)
  let a : E[X] →+* E[X] := eval₂RingHom C S
  have hpow (P : E[X]) (hP : coeffDeriv δ P = 0) (i : ℕ) : coeffDeriv δ (P^i) = 0 := by
    rw [Derivation.leibniz_pow, hP, smul_zero, nsmul_zero]
  have ha (H : R[X]) : coeffDeriv δ (a (H.map φ)) = 0 := by
    change coeffDeriv δ ((H.map φ).eval₂ C S) = 0
    rw [eval₂_eq_sum_range, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    simp only [coeff_map, Derivation.leibniz, hpow S hS, coeffDeriv_C, hφ, map_zero, smul_zero, add_zero]
  change coeffDeriv δ (Q.eval₂ a (Polynomial.X : E[X])) = 0
  rw [eval₂_eq_sum_range, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  have hz : coeffDeriv δ (a (Q.coeff i)) = 0 := by
    dsimp only [Q]
    rw [coeff_map, coe_mapRingHom]
    exact ha _
  simp only [Derivation.leibniz, hpow _ (coeffDeriv_X δ), hz, smul_zero, add_zero]

theorem root_at_fresh_variable {R E : Type} [CommRing R] [Field E]
    (p : ℕ) [CharP E p] (φ : R →+* E) (δ : Derivation ℤ E E) (x : E)
    (G : Polynomial R[X]) (S : E[X]) (hx : δ x = 1) (hφ : ∀ a, δ (φ a) = 0)
    (hS : coeffDeriv δ S = 0) {e d : ℕ} (he : ∀ i, (G.coeff i).natDegree ≤ e)
    (hd : S.natDegree ≤ d) (hp : G.natDegree+e*d < p)
    (hroot : (G.map (mapRingHom φ)).eval₂ (evalRingHom (S.eval x)) x = 0) :
    substitute S (G.map (mapRingHom φ)) = 0 :=
  fresh_identity p δ x hx _ (substitute_constant φ G S δ hφ hS)
    ((substitute_degree φ G S he hd).trans_lt hp) ((substitute_eval _ S x).trans hroot)

end SplitCut.FreshRoot

#print axioms SplitCut.FreshRoot.root_at_fresh_variable
