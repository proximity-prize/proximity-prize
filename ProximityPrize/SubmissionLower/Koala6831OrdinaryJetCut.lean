import ProximityPrize.SubmissionLower.Koala6831IntrinsicTail
import ProximityPrize.SubmissionLower.Koala6831OrdinarySurface

namespace ProximityPrize.SubmissionLower.Koala6831Ordinary

open Koala6831Intrinsic (implicitRegularity tailNumerator graphSpecialize
  tailNumerator_wt_le graphSpecialize_tailNumerator)
open RCN234 MvPolynomial
open scoped Polynomial BigOperators

variable {K : Type*} [Field K]

noncomputable def clearedTaylorCoeff (F : Carrier K) (u : ℕ) : ℕ → Carrier K
  | 0 => implicitRegularity F ^ (2 * u) * MvPolynomial.X 1
  | j + 1 => implicitRegularity F ^ (2 * u - (2 * j + 1)) *
      tailNumerator F j * MvPolynomial.C (((j + 1).factorial : K)⁻¹)

private theorem separant_weight_le (weights : Fin 4 → ℕ) (F : Carrier K) (cap : ℕ)
    (hw : weights 1 = 1) (hf : wt weights F ≤ cap) :
    wt weights (implicitRegularity F) ≤ cap - 1 := by
  apply (RCN081.weightedTotalDegree_le_iff weights _ _).mpr
  intro d hd
  have h := (MvPolynomial.le_weightedTotalDegree weights
    (RCN313.support_before_pderiv 1 F d hd)).trans hf
  simp only [map_add, Finsupp.weight_single, one_nsmul, hw] at h
  omega

theorem clearedTaylorCoeff_wt_le (weights : Fin 4 → ℕ) (F : Carrier K) (u j cap : ℕ)
    (hx : weights 0 = 0) (hy : weights 1 = 1) (hcap : 1 ≤ cap)
    (hf : wt weights F ≤ cap) (hj : j ≤ u) :
    wt weights (clearedTaylorCoeff F u j) ≤ 1 + 2 * u * (cap - 1) := by
  have hs := separant_weight_le weights F cap hy hf
  have hpow (n : ℕ) : wt weights (implicitRegularity F ^ n) ≤ n * (cap - 1) :=
    (wt_pow_le weights _ _).trans (Nat.mul_le_mul_left _ hs)
  cases j with
  | zero =>
    unfold clearedTaylorCoeff
    apply (wt_mul_le weights _ _).trans
    rw [wt_X, hy, Nat.add_comm]
    exact Nat.add_le_add_left (hpow _) _
  | succ j =>
    unfold clearedTaylorCoeff
    have htail := tailNumerator_wt_le weights F cap hx (hy.symm ▸ hcap) hf j
    rw [hy] at htail
    apply (wt_mul_le weights _ _).trans
    rw [wt_C, Nat.add_zero]
    apply (wt_mul_le weights _ _).trans
    apply (Nat.add_le_add (hpow _) htail).trans
    have hsplit : 2 * u - (2 * j + 1) + (2 * j + 1) = 2 * u := by omega
    rw [show (2 * u - (2 * j + 1)) * (cap - 1) + (1 + (2 * j + 1) * (cap - 1)) =
      1 + (2 * u - (2 * j + 1) + (2 * j + 1)) * (cap - 1) by ring, hsplit]

theorem graphSpecialize_clearedTaylorCoeff (F : Carrier K) (P : Polynomial K) (g h : K)
    (hF : graphSpecialize P g h F = 0) (u j : ℕ) (hj : j ≤ u) :
    graphSpecialize P g h (clearedTaylorCoeff F u j) =
      (graphSpecialize P g h (implicitRegularity F)) ^ (2 * u) *
        ((Polynomial.derivative^[j]) P * Polynomial.C ((j.factorial : K)⁻¹)) := by
  cases j with
  | zero => simp [clearedTaylorCoeff, graphSpecialize]
  | succ j =>
    have hconst (x : K) : graphSpecialize P g h (MvPolynomial.C x) = Polynomial.C x := by
      simp [graphSpecialize]
    simp only [clearedTaylorCoeff, map_mul, map_pow, hconst,
      graphSpecialize_tailNumerator F P g h hF]
    let S := graphSpecialize P g h (implicitRegularity F)
    have hsplit : 2 * u - (2 * j + 1) + (2 * j + 1) = 2 * u := by omega
    have hpow : S ^ (2 * u - (2 * j + 1)) * S ^ (2 * j + 1) = S ^ (2 * u) := by
      rw [← pow_add, hsplit]
    calc
      _ = (S ^ (2 * u - (2 * j + 1)) * S ^ (2 * j + 1)) *
          ((Polynomial.derivative^[j + 1]) P * Polynomial.C (((j + 1).factorial : K)⁻¹)) := by
        simp only [S, mul_assoc]
      _ = _ := by rw [hpow]

end ProximityPrize.SubmissionLower.Koala6831Ordinary
