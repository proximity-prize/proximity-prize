import ProximityPrize.SubmissionLower.ContactImplicitContactLift

namespace ProximityPrize.SubmissionLower.ContactPost6464MinkowskiRecurrence

open scoped BigOperators
open ContactFactorCaps ContactImplicitContactLift ContactTaylorNumerators

noncomputable section

variable {K : Type*} [Field K]

abbrev Poly4 (K : Type*) [Field K] := MvPolynomial (Fin 4) K

def wt (weights : Fin 4 → ℕ) (P : Poly4 K) : ℕ :=
  MvPolynomial.weightedTotalDegree weights P

theorem pderiv_eq_zero_of_wt_lt (weights : Fin 4 → ℕ) (P : Poly4 K) (i : Fin 4)
    (hP : wt weights P < weights i) : MvPolynomial.pderiv i P = 0 := by
  apply MvPolynomial.support_eq_empty.mp
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro d hd
  have hh := MvPolynomial.le_weightedTotalDegree weights
    (support_before_pderiv i P d hd)
  simp only [map_add, Finsupp.weight_single, one_nsmul] at hh
  change Finsupp.weight weights d + weights i ≤ wt weights P at hh
  omega

theorem wt_mul_le (weights : Fin 4 → ℕ) (P Q : Poly4 K) :
    wt weights (P * Q) ≤ wt weights P + wt weights Q :=
  weighted_mul_le weights P Q

theorem wt_add_le (weights : Fin 4 → ℕ) (P Q : Poly4 K) :
    wt weights (P + Q) ≤ max (wt weights P) (wt weights Q) :=
  weighted_add_le weights P Q

theorem wt_sub_le (weights : Fin 4 → ℕ) (P Q : Poly4 K) :
    wt weights (P - Q) ≤ max (wt weights P) (wt weights Q) := by
  unfold wt
  rw [← degree_weightedLift, map_sub]
  simpa only [degree_weightedLift] using
    MvPolynomial.degreeOf_sub_le (4 : Fin 5)
      (weightedLift K weights P) (weightedLift K weights Q)

theorem wt_neg (weights : Fin 4 → ℕ) (P : Poly4 K) :
    wt weights (-P) = wt weights P := by
  unfold wt
  rw [← degree_weightedLift, map_neg, MvPolynomial.degreeOf_neg,
    degree_weightedLift]

theorem wt_pow_le (weights : Fin 4 → ℕ) (P : Poly4 K) (n : ℕ) :
    wt weights (P ^ n) ≤ n * wt weights P := by
  unfold wt
  rw [← degree_weightedLift, map_pow]
  simpa only [degree_weightedLift] using
    MvPolynomial.degreeOf_pow_le (4 : Fin 5) (weightedLift K weights P) n

theorem wt_C (weights : Fin 4 → ℕ) (c : K) :
    wt weights (MvPolynomial.C c : Poly4 K) = 0 := by
  unfold wt MvPolynomial.weightedTotalDegree
  simp

theorem wt_X (weights : Fin 4 → ℕ) (i : Fin 4) :
    wt weights (MvPolynomial.X i : Poly4 K) = weights i := by
  unfold wt
  exact weighted_X weights i

theorem wt_natCast (weights : Fin 4 → ℕ) (n : ℕ) :
    wt weights (n : Poly4 K) = 0 := by
  rw [← map_natCast (MvPolynomial.C : K →+* Poly4 K), wt_C]

theorem wt_sum_le (weights : Fin 4 → ℕ) (I : Finset ℕ)
    (f : ℕ → Poly4 K) (a : ℕ) (hf : ∀ i ∈ I, wt weights (f i) ≤ a) :
    wt weights (∑ i ∈ I, f i) ≤ a := by
  unfold wt
  rw [← degree_weightedLift, map_sum]
  apply (MvPolynomial.degreeOf_sum_le (4 : Fin 5) I
    (fun i => weightedLift K weights (f i))).trans
  apply Finset.sup_le
  intro i hi
  rw [degree_weightedLift]
  exact hf i hi

theorem wt_finset_prod_le_sum {ι : Type*} [DecidableEq ι]
    (weights : Fin 4 → ℕ) (I : Finset ι) (f : ι → Poly4 K) :
    wt weights (∏ i ∈ I, f i) ≤ ∑ i ∈ I, wt weights (f i) := by
  induction I using Finset.induction_on with
  | empty => simp [wt, MvPolynomial.weightedTotalDegree]
  | @insert i I hi ih =>
      simp only [Finset.prod_insert hi, Finset.sum_insert hi]
      exact (wt_mul_le weights (f i) (∏ j ∈ I, f j)).trans
        (Nat.add_le_add le_rfl ih)

theorem wt_finset_sum_le {ι : Type*} [DecidableEq ι]
    (weights : Fin 4 → ℕ) (I : Finset ι) (f : ι → Poly4 K) (cap : ℕ)
    (hf : ∀ i ∈ I, wt weights (f i) ≤ cap) :
    wt weights (∑ i ∈ I, f i) ≤ cap := by
  unfold wt
  rw [← degree_weightedLift, map_sum]
  apply (MvPolynomial.degreeOf_sum_le (4 : Fin 5) I
    (fun i ↦ weightedLift K weights (f i))).trans
  apply Finset.sup_le
  intro i hi
  rw [degree_weightedLift]
  exact hf i hi

theorem wt_pderiv_le (weights : Fin 4 → ℕ) (P : Poly4 K)
    (i : Fin 4) (A : ℕ) (hP : wt weights P ≤ A) :
    wt weights (MvPolynomial.pderiv i P) ≤ A - weights i :=
  pderiv_weight_sub_bound weights P i A hP

theorem wt_polyH_le (weights : Fin 4 → ℕ) (F : Poly4 K)
    (C : ℕ) (hF : wt weights F ≤ C) :
    wt weights (polyH K F) ≤ C - weights 2 :=
  wt_pderiv_le weights F 2 C hF

theorem shiftedX_wt_eq_zero (weights : Fin 4 → ℕ) (hX : weights 0 = 0)
    (x : K) :
    wt weights (MvPolynomial.C x - MvPolynomial.X (0 : Fin 4) : Poly4 K) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply (wt_sub_le weights _ _).trans
  rw [wt_C, wt_X, hX]
  simp

theorem affineSeedPolynomial_wt_le (weights : Fin 4 → ℕ) (u₀ u₁ : K) :
    wt weights (affineSeedPolynomial u₀ u₁) ≤ weights 3 := by
  unfold affineSeedPolynomial
  apply (wt_add_le weights _ _).trans
  apply max_le
  · rw [wt_C]
    exact Nat.zero_le _
  · have hm := wt_mul_le weights (MvPolynomial.X (3 : Fin 4) : Poly4 K)
      (MvPolynomial.C u₁)
    rw [wt_X, wt_C, Nat.add_zero] at hm
    exact hm

end

end ProximityPrize.SubmissionLower.ContactPost6464MinkowskiRecurrence
