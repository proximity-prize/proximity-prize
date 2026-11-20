import ProximityPrize.SubmissionLower.LowerFoundation

namespace ProximityPrize.SubmissionLower.Koala6831Intrinsic

open MvPolynomial
open RCN234

noncomputable section

set_option maxHeartbeats 1800000

variable {K : Type*} [Field K]

abbrev Carrier (K : Type*) [Field K] := MvPolynomial (Fin 4) K

def implicitRegularity (F : Carrier K) : Carrier K :=
  pderiv 1 F

def clearedImplicit (F H : Carrier K) : Carrier K :=
  implicitRegularity F * pderiv 0 H - pderiv 0 F * pderiv 1 H

def tailNumerator (F : Carrier K) : ℕ → Carrier K
  | 0 => -pderiv 0 F
  | j + 1 =>
    implicitRegularity F * clearedImplicit F (tailNumerator F j) -
      ((2 * j + 1 : ℕ) : Carrier K) * tailNumerator F j * clearedImplicit F (implicitRegularity F)

def graphSpecialize (P : Polynomial K) (g h : K) : Carrier K →+* Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, P, Polynomial.C g, Polynomial.C h]

theorem derivative_graphSpecialize (P : Polynomial K) (g h : K) (Q : Carrier K) :
    (graphSpecialize P g h Q).derivative =
      graphSpecialize P g h (pderiv 0 Q) +
        P.derivative * graphSpecialize P g h (pderiv 1 Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [graphSpecialize]
  | add Q S hQ hS =>
      simp only [map_add, hQ, hS]
      ring
  | mul_X Q i hQ =>
      simp only [MvPolynomial.pderiv_mul, map_add, map_mul, Polynomial.derivative_mul, hQ]
      fin_cases i <;> simp [graphSpecialize] <;> ring

theorem graphSpecialize_clearedImplicit (F Q : Carrier K) (P : Polynomial K) (g h : K)
    (hF : graphSpecialize P g h F = 0) :
    graphSpecialize P g h (clearedImplicit F Q) =
      graphSpecialize P g h (implicitRegularity F) * (graphSpecialize P g h Q).derivative := by
  have hrel := derivative_graphSpecialize P g h F
  rw [hF, Polynomial.derivative_zero] at hrel
  dsimp only [clearedImplicit, implicitRegularity]
  rw [map_sub, map_mul, map_mul, derivative_graphSpecialize P g h Q]
  linear_combination (graphSpecialize P g h (pderiv 1 Q)) * hrel

private theorem quotient_numerator_step (S U : Polynomial K) (k : ℕ) :
    S ^ 2 * (S ^ (k + 1) * U).derivative -
      ((k + 1 : ℕ) : Polynomial K) * (S ^ (k + 1) * U) * (S * S.derivative) =
    S ^ (k + 3) * U.derivative := by
  rw [Polynomial.derivative_mul, Polynomial.derivative_pow, Nat.add_sub_cancel,
    show k + 3 = (k + 1) + 2 by omega, pow_add]
  simp only [Nat.cast_add, Nat.cast_one, map_add, map_one, map_natCast]
  ring

theorem graphSpecialize_tailNumerator (F : Carrier K) (P : Polynomial K) (g h : K)
    (hF : graphSpecialize P g h F = 0) (j : ℕ) :
    graphSpecialize P g h (tailNumerator F j) =
      (graphSpecialize P g h (implicitRegularity F)) ^ (2 * j + 1) *
        (Polynomial.derivative^[j + 1]) P := by
  induction j with
  | zero =>
      have hrel := derivative_graphSpecialize P g h F
      rw [hF, Polynomial.derivative_zero] at hrel
      simp only [tailNumerator, map_neg, Nat.mul_zero, Nat.zero_add, pow_one,
        Function.iterate_one, implicitRegularity]
      linear_combination hrel
  | succ j ih =>
      rw [tailNumerator]
      simp only [map_sub, map_mul, map_natCast,
        graphSpecialize_clearedImplicit F _ P g h hF, ih]
      have hiter : (Polynomial.derivative^[j + 1 + 1]) P =
          ((Polynomial.derivative^[j + 1]) P).derivative :=
        Function.iterate_succ_apply' Polynomial.derivative (j + 1) P
      rw [hiter, show 2 * (j + 1) + 1 = 2 * j + 3 by omega]
      have hstep := quotient_numerator_step (graphSpecialize P g h (implicitRegularity F))
        ((Polynomial.derivative^[j + 1]) P) (2 * j)
      rw [pow_two, mul_assoc] at hstep
      exact hstep

theorem graphSpecialize_tailNumerator_eq_zero (F : Carrier K) (P : Polynomial K) (g h : K)
    (hF : graphSpecialize P g h F = 0) (j : ℕ) (hdegree : P.natDegree ≤ j) :
    graphSpecialize P g h (tailNumerator F j) = 0 := by
  rw [graphSpecialize_tailNumerator F P g h hF j,
    Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_of_le hdegree), mul_zero]

private theorem wt_pderiv_le_sub (weights : Fin 4 → ℕ) (i : Fin 4) (P : Carrier K)
    {cap : ℕ} (hcap : wt weights P ≤ cap) :
    wt weights (pderiv i P) ≤ cap - weights i := by
  apply (RCN081.weightedTotalDegree_le_iff weights _ _).mpr
  intro e he
  have h := (MvPolynomial.le_weightedTotalDegree weights
    (RCN313.support_before_pderiv i P e he)).trans hcap
  simp only [map_add, Finsupp.weight_single, one_nsmul] at h
  omega

private theorem wt_mul_pderiv_le (weights : Fin 4 → ℕ) (i : Fin 4)
    (U P : Carrier K) (gain : ℕ) (hU : wt weights U ≤ weights i + gain) :
    wt weights (U * pderiv i P) ≤ wt weights P + gain := by
  by_cases hz : pderiv i P = 0
  · simp [hz, wt, MvPolynomial.weightedTotalDegree]
  · obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hz
    have h := MvPolynomial.le_weightedTotalDegree weights (RCN313.support_before_pderiv i P d hd)
    have hpos : weights i ≤ wt weights P := by
      simp only [map_add, Finsupp.weight_single, one_nsmul] at h
      unfold wt
      omega
    have hp := (wt_mul_le weights U (pderiv i P)).trans
      (Nat.add_le_add hU (wt_pderiv_le_sub weights i P le_rfl))
    exact hp.trans (by omega)

theorem clearedImplicit_wt_le (weights : Fin 4 → ℕ) (F P : Carrier K) (cap : ℕ)
    (hx : weights 0 = 0) (hy : weights 1 ≤ cap) (hcap : wt weights F ≤ cap) :
    wt weights (clearedImplicit F P) ≤ wt weights P + (cap - weights 1) := by
  unfold clearedImplicit implicitRegularity
  apply (wt_sub_le _ _ _).trans
  apply max_le
  · apply wt_mul_pderiv_le
    rw [hx, zero_add]
    exact wt_pderiv_le_sub _ _ _ hcap
  · apply wt_mul_pderiv_le
    rw [Nat.add_sub_of_le hy]
    have h := wt_pderiv_le_sub weights 0 F hcap
    rwa [hx, Nat.sub_zero] at h

private theorem wt_natCast_le (weights : Fin 4 → ℕ) (n : ℕ) :
    wt weights (n : Carrier K) ≤ 0 := by
  simpa only [map_natCast] using (wt_C weights (n : K)).le

theorem tailNumerator_wt_le (weights : Fin 4 → ℕ) (F : Carrier K) (cap : ℕ)
    (hx : weights 0 = 0) (hy : weights 1 ≤ cap) (hcap : wt weights F ≤ cap) (j : ℕ) :
    wt weights (tailNumerator F j) ≤ weights 1 + (2 * j + 1) * (cap - weights 1) := by
  let gain := cap - weights 1
  have hreg : wt weights (implicitRegularity F) ≤ gain :=
    wt_pderiv_le_sub weights 1 F hcap
  have hfield (Q : Carrier K) : wt weights (clearedImplicit F Q) ≤ wt weights Q + gain :=
    clearedImplicit_wt_le weights F Q cap hx hy hcap
  induction j with
  | zero =>
      rw [tailNumerator, RCN234.wt_neg]
      have h := wt_pderiv_le_sub weights 0 F hcap
      rw [hx, Nat.sub_zero] at h
      simpa [Nat.add_sub_of_le hy] using h
  | succ j ih =>
      change wt weights (tailNumerator F j) ≤ weights 1 + (2 * j + 1) * gain at ih
      rw [tailNumerator]
      have hleft := (wt_mul_le weights _ _).trans
        (Nat.add_le_add hreg ((hfield _).trans (Nat.add_le_add_right ih gain)))
      have hright0 := (wt_mul_le weights ((2 * j + 1 : ℕ) : Carrier K) _).trans
        (Nat.add_le_add (wt_natCast_le weights (2 * j + 1)) ih)
      have hright := (wt_mul_le weights _ _).trans
        (Nat.add_le_add hright0 ((hfield _).trans (Nat.add_le_add_right hreg gain)))
      change wt weights ((implicitRegularity F * clearedImplicit F (tailNumerator F j)) -
        ((2 * j + 1 : ℕ) : Carrier K) * tailNumerator F j * clearedImplicit F (implicitRegularity F)) ≤
        weights 1 + (2 * (j + 1) + 1) * gain
      have hnew : (2 * (j + 1) + 1) * gain = (2 * j + 1) * gain + 2 * gain := by ring
      rw [hnew]
      exact (wt_sub_le _ _ _).trans (max_le (hleft.trans (by omega)) (hright.trans (by omega)))

end

end ProximityPrize.SubmissionLower.Koala6831Intrinsic
