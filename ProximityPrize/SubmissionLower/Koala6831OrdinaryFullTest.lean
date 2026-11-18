import ProximityPrize.SubmissionLower.Koala6831OrdinaryJetCut

namespace ProximityPrize.SubmissionLower.Koala6831Ordinary

open Koala6831Intrinsic (implicitRegularity tailNumerator)
open scoped Polynomial BigOperators

variable {K E L : Type*} [Field K] [Field E] [Field L] [Algebra E L]

noncomputable def ordinaryJet (φ : K[X] →+* E) (F : Carrier K) (v : Fin 3 → L) : ℕ → L
  | 0 => v 1
  | j + 1 =>
    MvPolynomial.aeval v (ordinarySurface φ (tailNumerator F j)) *
      algebraMap E L (φ (Polynomial.C (((j + 1).factorial : K)⁻¹))) /
      (MvPolynomial.aeval v (ordinarySurface φ (implicitRegularity F))) ^ (2 * j + 1)

theorem eval_clearedTaylorCoeff (φ : K[X] →+* E) (F : Carrier K) (v : Fin 3 → L)
    (u j : ℕ) (hj : j ≤ u)
    (hreg : MvPolynomial.aeval v (ordinarySurface φ (implicitRegularity F)) ≠ 0) :
    MvPolynomial.aeval v (ordinarySurface φ (clearedTaylorCoeff F u j)) =
      (MvPolynomial.aeval v (ordinarySurface φ (implicitRegularity F))) ^ (2 * u) *
        ordinaryJet φ F v j := by
  cases j with
  | zero => simp [clearedTaylorCoeff, ordinaryJet]
  | succ j =>
    simp only [clearedTaylorCoeff, ordinaryJet, map_mul, map_pow,
      ordinarySurface_C, MvPolynomial.aeval_C]
    let s := MvPolynomial.aeval v (ordinarySurface φ (implicitRegularity F))
    have hpow : s ^ (2 * u - (2 * j + 1)) * s ^ (2 * j + 1) = s ^ (2 * u) := by
      rw [← pow_add, show 2 * u - (2 * j + 1) + (2 * j + 1) = 2 * u by omega]
    rw [← hpow]
    field_simp [s, hreg]
    ring

noncomputable def reconstructedOrdinary (φ : K[X] →+* E) (F : Carrier K)
    (v : Fin 3 → L) (w : ℕ) : Polynomial L :=
  Polynomial.taylor (-algebraMap E L (φ Polynomial.X))
    (∑ j ∈ Finset.range (w + 1), Polynomial.monomial j (ordinaryJet φ F v j))

theorem reconstructedOrdinary_degree (φ : K[X] →+* E) (F : Carrier K)
    (v : Fin 3 → L) (w : ℕ) : (reconstructedOrdinary φ F v w).natDegree ≤ w := by
  rw [reconstructedOrdinary, Polynomial.natDegree_taylor]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

theorem reconstructedOrdinary_coeff (φ : K[X] →+* E) (F : Carrier K)
    (v : Fin 3 → L) (w j : ℕ) (hj : j ≤ w) :
    (Polynomial.taylor (algebraMap E L (φ Polynomial.X))
      (reconstructedOrdinary φ F v w)).coeff j = ordinaryJet φ F v j := by
  rw [reconstructedOrdinary, Polynomial.taylor_taylor, add_neg_cancel, Polynomial.taylor_zero]
  simp [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finset.mem_range.mpr (Nat.lt_succ_of_le hj)]

noncomputable def fullOrdinaryTest (φ : K[X] →+* E) (F : Carrier K)
    (w : ℕ) (x a b : K) : MvPolynomial (Fin 3) E :=
  (∑ j ∈ Finset.range (w + 1),
      MvPolynomial.C ((φ (Polynomial.C x) - φ Polynomial.X) ^ j) *
        ordinarySurface φ (clearedTaylorCoeff F w j)) -
    ordinarySurface φ (implicitRegularity F) ^ (2 * w) *
      (MvPolynomial.C (φ (Polynomial.C a)) + MvPolynomial.X 0 * MvPolynomial.C (φ (Polynomial.C b)))

theorem eval_fullOrdinaryTest (φ : K[X] →+* E) (F : Carrier K) (w : ℕ)
    (x a b : K) (v : Fin 3 → L)
    (hreg : MvPolynomial.aeval v (ordinarySurface φ (implicitRegularity F)) ≠ 0) :
    MvPolynomial.aeval v (fullOrdinaryTest φ F w x a b) =
      (MvPolynomial.aeval v (ordinarySurface φ (implicitRegularity F))) ^ (2 * w) *
        ((reconstructedOrdinary φ F v w).eval (algebraMap E L (φ (Polynomial.C x))) -
          (algebraMap E L (φ (Polynomial.C a)) + v 0 * algebraMap E L (φ (Polynomial.C b)))) := by
  simp only [fullOrdinaryTest, map_sub, map_sum, map_mul, map_pow, map_add,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  rw [mul_sub]
  congr 1
  simp only [reconstructedOrdinary, Polynomial.taylor_eval, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, sub_eq_add_neg, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [eval_clearedTaylorCoeff φ F v w j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hreg]
  ring

theorem polynomialHom_eval (φ : K[X] →+* E) (Q : K[X]) :
    φ Q = (Q.map (φ.comp Polynomial.C)).eval (φ Polynomial.X) := by
  have h : φ = Polynomial.eval₂RingHom (φ.comp Polynomial.C) (φ Polynomial.X) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp
  have he := RingHom.congr_fun h Q
  exact he.trans (Polynomial.eval₂_eq_eval_map _)

theorem ordinaryJet_eq_selected (φ : K[X] →+* E) (F : Carrier K)
    (selected : K → K[X]) (p u j : ℕ) [CharP E p] (hj : j ≤ u) (hchar : u < p) (g : K)
    (hroot : Koala6831Intrinsic.graphSpecialize (selected g) g (g ^ p) F = 0)
    (hreg : MvPolynomial.aeval (ordinaryPoint φ selected p g)
      (ordinarySurface φ (implicitRegularity F)) ≠ 0) :
    ordinaryJet φ F (ordinaryPoint φ selected p g) j =
      (Polynomial.taylor (φ Polynomial.X) ((selected g).map (φ.comp Polynomial.C))).coeff j := by
  let v := ordinaryPoint φ selected p g
  let c := φ.comp Polynomial.C
  let s := MvPolynomial.aeval v (ordinarySurface φ (implicitRegularity F))
  have hEval (A : Carrier K) : MvPolynomial.aeval v (ordinarySurface φ A) =
      φ (Koala6831Intrinsic.graphSpecialize (selected g) g (g ^ p) A) :=
    eval_ordinarySurface φ selected p g A
  have hfac := RCN347.factorial_cast_ne_zero_below_characteristic (L := E) p j (hj.trans_lt hchar)
  have hi : φ (Polynomial.C ((j.factorial : K)⁻¹)) = (j.factorial : E)⁻¹ := by
    change c ((j.factorial : K)⁻¹) = _
    simp
  apply mul_left_cancel₀ (pow_ne_zero _ (show s ≠ 0 from hreg))
  calc
    s ^ (2 * u) * ordinaryJet φ F v j =
        MvPolynomial.aeval v (ordinarySurface φ (clearedTaylorCoeff F u j)) :=
      (eval_clearedTaylorCoeff φ F v u j hj hreg).symm
    _ = _ := by
      rw [hEval, graphSpecialize_clearedTaylorCoeff F (selected g) g (g ^ p) hroot u j hj,
        map_mul, map_pow, map_mul, hi, ← hEval]
      congr 1
      rw [RCN229.taylor_coeff_eq_derivative_div_factorial _ _ _ hfac, div_eq_mul_inv]
      rw [polynomialHom_eval, Polynomial.iterate_derivative_map]

theorem reconstructedOrdinary_eq_selected (φ : K[X] →+* E) (F : Carrier K)
    (selected : K → K[X]) (p w : ℕ) [CharP E p] (hchar : w < p) (g : K)
    (hdegree : (selected g).natDegree ≤ w)
    (hroot : Koala6831Intrinsic.graphSpecialize (selected g) g (g ^ p) F = 0)
    (hreg : MvPolynomial.aeval (ordinaryPoint φ selected p g)
      (ordinarySurface φ (implicitRegularity F)) ≠ 0) :
    reconstructedOrdinary φ F (ordinaryPoint φ selected p g) w =
      (selected g).map (φ.comp Polynomial.C) := by
  let v := ordinaryPoint φ selected p g
  let c := φ.comp Polynomial.C
  let center := φ Polynomial.X
  have hTaylor : Polynomial.taylor center (reconstructedOrdinary φ F v w) =
      Polynomial.taylor center ((selected g).map c) := by
    ext j
    by_cases hj : j ≤ w
    · rw [show center = algebraMap E E (φ Polynomial.X) from rfl,
        reconstructedOrdinary_coeff φ F v w j hj]
      exact ordinaryJet_eq_selected φ F selected p w j hj hchar g hroot hreg
    · have h₀ : (Polynomial.taylor center (reconstructedOrdinary φ F v w)).coeff j = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [Polynomial.natDegree_taylor]
        exact (reconstructedOrdinary_degree φ F v w).trans_lt (Nat.lt_of_not_ge hj)
      have h₁ : (Polynomial.taylor center ((selected g).map c)).coeff j = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [Polynomial.natDegree_taylor]
        exact Polynomial.natDegree_map_le.trans_lt (hdegree.trans_lt (Nat.lt_of_not_ge hj))
      rw [h₀, h₁]
  have he := congrArg (Polynomial.taylor (-center)) hTaylor
  simpa only [Polynomial.taylor_taylor, neg_add_cancel, Polynomial.taylor_zero] using he

theorem fullOrdinaryTest_graph_iff (φ : K[X] →+* E) (F : Carrier K)
    (selected : K → K[X]) (p w : ℕ) [CharP E p] (hchar : w < p) (g x a b : K)
    (hdegree : (selected g).natDegree ≤ w)
    (hroot : Koala6831Intrinsic.graphSpecialize (selected g) g (g ^ p) F = 0)
    (hreg : MvPolynomial.aeval (ordinaryPoint φ selected p g)
      (ordinarySurface φ (implicitRegularity F)) ≠ 0) :
    MvPolynomial.aeval (ordinaryPoint φ selected p g) (fullOrdinaryTest φ F w x a b) = 0 ↔
      (selected g).eval x = a + g * b := by
  rw [eval_fullOrdinaryTest φ F w x a b _ hreg,
    reconstructedOrdinary_eq_selected φ F selected p w hchar g hdegree hroot hreg]
  let c := φ.comp Polynomial.C
  let s := MvPolynomial.aeval (ordinaryPoint φ selected p g)
    (ordinarySurface φ (implicitRegularity F))
  change s ^ (2 * w) * (((selected g).map c).eval (c x) - (c a + c g * c b)) = 0 ↔ _
  rw [Polynomial.eval_map_apply, ← map_mul, ← map_add, ← map_sub,
    mul_eq_zero, or_iff_right (pow_ne_zero _ (show s ≠ 0 from hreg)),
    map_eq_zero_iff _ c.injective, sub_eq_zero]

end ProximityPrize.SubmissionLower.Koala6831Ordinary
