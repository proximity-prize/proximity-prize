import Mathlib.Algebra.MvPolynomial.Equiv
import ProximityPrize.SubmissionLower.Koala6844VirtualShortGermDegrees


namespace ProximityPrize.SubmissionLower.Koala6844VirtualShort

open Polynomial
open scoped BigOperators Classical Matrix

noncomputable section
set_option autoImplicit false

variable {R : Type*} [CommRing R]

abbrev packValue := MvPolynomial.finSuccEquiv R 1

abbrev seedIntoSecond : MvPolynomial (Fin 1) R →+* MvPolynomial (Fin 2) R :=
  (MvPolynomial.rename Fin.succ).toRingHom

theorem packValue_seedIntoSecond (Q : MvPolynomial (Fin 1) R) :
    packValue (seedIntoSecond Q) = Polynomial.C Q := by
  have he : (packValue (R := R)).toRingHom.comp seedIntoSecond =
      (Polynomial.C : MvPolynomial (Fin 1) R →+* Polynomial (MvPolynomial (Fin 1) R)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [packValue, MvPolynomial.finSuccEquiv_apply]
    · intro i
      simp [packValue, MvPolynomial.finSuccEquiv_X_succ]
  exact DFunLike.congr_fun he Q

theorem eval_packValue (J : MvPolynomial (Fin 2) R) (v z : R) :
    (packValue J).eval₂ (MvPolynomial.eval (fun _ : Fin 1 => z)) v =
      MvPolynomial.eval ![v,z] J := by
  have he : (Polynomial.eval₂RingHom (MvPolynomial.eval (fun _ : Fin 1 => z)) v).comp
      (packValue (R := R)).toRingHom = MvPolynomial.eval ![v,z] := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [packValue, MvPolynomial.finSuccEquiv_apply]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [packValue, MvPolynomial.finSuccEquiv_X_zero]
      · simp [packValue, MvPolynomial.finSuccEquiv_X_succ]
  exact DFunLike.congr_fun he J


def affineGermNumerator (J : MvPolynomial (Fin 2) R) (a b d : R) : MvPolynomial (Fin 2) R :=
  homogeneousEval seedIntoSecond (packValue J) (packValue J).natDegree
    (MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1) (MvPolynomial.C d)

set_option maxHeartbeats 800000 in
theorem affineGermNumerator_ne_zero [IsDomain R] (J : MvPolynomial (Fin 2) R) (hJ : J ≠ 0)
    (a b d : R) (ha : a ≠ 0) : affineGermNumerator J a b d ≠ 0 := by
  let E := (packValue (R := R)).toRingHom
  let Q : Polynomial (MvPolynomial (Fin 1) R) := E J
  let N : MvPolynomial (Fin 2) R :=
    MvPolynomial.C a * MvPolynomial.X (0 : Fin 2) +
      MvPolynomial.C b * MvPolynomial.X (1 : Fin 2)
  have hp : Q ≠ 0 := fun h => hJ ((packValue (R := R)).injective (h.trans (map_zero E).symm))
  have hc0 : (MvPolynomial.C a : MvPolynomial (Fin 1) R) ≠ 0 :=
    fun h => ha (MvPolynomial.C_injective (Fin 1) R (h.trans (map_zero _).symm))
  have h := homogeneousEval_affine_ne_zero (RingHom.id (MvPolynomial (Fin 1) R))
    Function.injective_id Q hp (MvPolynomial.C a)
    (MvPolynomial.C b * MvPolynomial.X 0) (MvPolynomial.C d) hc0
  have he : E.comp seedIntoSecond = Polynomial.C :=
    RingHom.ext (fun P => packValue_seedIntoSecond P)
  have hC (e : R) : E (MvPolynomial.C e) = Polynomial.C (MvPolynomial.C e) := by
    simp [E, packValue, MvPolynomial.finSuccEquiv_apply]
  have hX0 : E (MvPolynomial.X 0) = Polynomial.X :=
    MvPolynomial.finSuccEquiv_X_zero
  have hX1 : E (MvPolynomial.X 1) = Polynomial.C (MvPolynomial.X (0 : Fin 1)) :=
    MvPolynomial.finSuccEquiv_X_succ (j := (0 : Fin 1))
  have hN : E N = Polynomial.C (MvPolynomial.C a) * Polynomial.X +
      Polynomial.C (MvPolynomial.C b * MvPolynomial.X 0) := by
    simp only [N, map_add, map_mul, hC, hX0, hX1]
  intro hz
  have H := map_homogeneousEval seedIntoSecond E Q Q.natDegree N (MvPolynomial.C d)
  change E (affineGermNumerator J a b d) = _ at H
  rw [hz,map_zero,he,hN,hC] at H
  exact h (by simpa only [RingHom.comp_id] using H.symm)


theorem seedIntoSecond_degree_zero (P : MvPolynomial (Fin 1) R) :
    (seedIntoSecond P).degreeOf (0 : Fin 2) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro e he
  have hinj : Function.Injective (Fin.succ : Fin 1 → Fin 2) := Fin.succ_injective _
  rw [show (seedIntoSecond P) = MvPolynomial.rename Fin.succ P from rfl,
    MvPolynomial.support_rename_of_injective hinj] at he
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
  exact le_of_eq (Finsupp.mapDomain_of_notMem_range (f := (Fin.succ : Fin 1 → Fin 2)) f 0 (by rintro ⟨i,hi⟩; exact Fin.succ_ne_zero i hi))

theorem affineGermNumerator_caps [Nontrivial R] (J : MvPolynomial (Fin 2) R) (a b d : R) (u v : ℕ)
    (hy : J.degreeOf 0 ≤ u) (ht : J.totalDegree ≤ v) :
    (affineGermNumerator J a b d).degreeOf 0 ≤ u ∧
      (affineGermNumerator J a b d).totalDegree ≤ v := by
  let N := MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X (1 : Fin 2)
  have hn : N.degreeOf 0 ≤ 1 := by
    apply (MvPolynomial.degreeOf_add_le _ _ _).trans
    apply max_le
    · exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (by simp [MvPolynomial.degreeOf_X])
    · exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (by simp [MvPolynomial.degreeOf_X])
  have htN : N.totalDegree ≤ 1 := by
    apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le <;>
      exact (MvPolynomial.totalDegree_mul _ _).trans ((Nat.add_le_add
        (le_of_eq (MvPolynomial.totalDegree_C _)) (by rw [MvPolynomial.totalDegree_X])).trans (by simp))
  refine ⟨?_,?_⟩
  · apply homogeneousEval_degreeOf_le
    intro j hj
    simp only [seedIntoSecond_degree_zero, MvPolynomial.degreeOf_C, mul_zero, add_zero, zero_add]
    exact (Nat.mul_le_mul_left _ hn).trans (by
      rw [mul_one]
      exact (Polynomial.le_natDegree_of_mem_supp _ hj).trans
        ((MvPolynomial.natDegree_finSuccEquiv _).trans_le hy))
  · apply homogeneousEval_totalDegree_le
    intro j hj
    simp only [MvPolynomial.totalDegree_C, mul_zero, add_zero]
    have hc := (MvPolynomial.totalDegree_rename_le Fin.succ ((packValue J).coeff j)).trans
      (totalDegree_coeff_pack_le J j v ht)
    have hju : j ≤ v := (Polynomial.le_natDegree_of_mem_supp _ hj).trans
      ((MvPolynomial.natDegree_finSuccEquiv J).trans_le (MvPolynomial.degreeOf_le_totalDegree J 0 |>.trans ht))
    exact (Nat.add_le_add hc (Nat.mul_le_mul_left _ htN)).trans (by omega)

theorem affineGermNumerator_eval (J : MvPolynomial (Fin 2) R) (a b d v z y : R)
    (he : a*v+b*z=d*y) :
    MvPolynomial.eval ![v,z] (affineGermNumerator J a b d) =
      d^(packValue J).natDegree * MvPolynomial.eval ![y,z] J := by
  rw [affineGermNumerator, map_homogeneousEval]
  have hmap : (MvPolynomial.eval ![v,z]).comp seedIntoSecond =
      MvPolynomial.eval (fun _ : Fin 1 => z) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      fin_cases i
      simp [seedIntoSecond]
  rw [hmap, homogeneousEval_eq_mul_eval₂ _ _ _ le_rfl _ _ y, eval_packValue]
  · simp
  · simpa using he

variable {E : Type*} [Field E]

private theorem coeff_mul_at_first (P Q : Polynomial E) (n : ℕ)
    (h : ∀ k < n, P.coeff k = 0) :
    (P*Q).coeff n = P.coeff n * Q.eval 0 := by
  rw [Polynomial.coeff_mul, ← Polynomial.coeff_zero_eq_eval_zero]
  apply Finset.sum_eq_single (n,0)
  · intro a ha hne
    have hsum : a.1 + a.2 = n := by simpa using ha
    have ha' : a.1 < n := by
      rcases a with ⟨i,j⟩
      simp only at hsum ⊢
      by_contra! hk
      have hi : i = n := by omega
      have hj : j = 0 := by omega
      exact hne (Prod.ext hi hj)
    rw [h _ ha', zero_mul]
  · intro bad
    exact False.elim (bad (by simp))

theorem eval_firstCoeffLayer_zero (P : MvPolynomial (Fin 2) (Polynomial E)) (n : ℕ)
    (hlow : ∀ k < n, coeffLayer k P = 0) (V : Polynomial E) (z : E)
    (he : MvPolynomial.eval ![V, Polynomial.C z] P = 0) :
    MvPolynomial.eval ![V.eval 0,z] (coeffLayer n P) = 0 := by
  have hcoef (e : Fin 2 →₀ ℕ) (k : ℕ) (hk : k < n) : (P.coeff e).coeff k = 0 := by
    have h := congrArg (fun Q : MvPolynomial (Fin 2) E => Q.coeff e) (hlow k hk)
    simpa [coeff_coeffLayer] using h
  have hsum := congrArg (fun Q : Polynomial E => Q.coeff n) he
  rw [← MvPolynomial.support_sum_monomial_coeff P, map_sum, Polynomial.finsetSum_coeff] at hsum
  rw [coeffLayer, map_sum]
  rw [Polynomial.coeff_zero] at hsum
  refine (?_ : _ = _).trans hsum
  apply Finset.sum_congr rfl
  intro e he'
  simp only [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [coeff_mul_at_first _ _ _ (hcoef e)]
  simp

end

end ProximityPrize.SubmissionLower.Koala6844VirtualShort
