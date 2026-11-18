/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Copyright (c) 2026 ArkLib Contributors. Released under Apache 2.0.
Adapted from Quang Dao's RationalTaylorDerivativeDegree proof. This version
retains the Taylor-index weight of every initial jet variable. -/
import ProximityPrize.SubmissionLower.Mid6833BiChartCaps
namespace PolynomialDifferential
open MvPolynomial
noncomputable section
variable {F : Type*} {r : ℕ}

private theorem jetX [CommSemiring F] [Nontrivial F] (i : Fin (r+1)) :
    weightedTotalDegree Fin.val (X i : MvPolynomial (Fin (r+1)) F) = i.val := by
  change weightedTotalDegree Fin.val (monomial (Finsupp.single i 1) (1:F)) = _
  rw [weightedTotalDegree_monomial _ _ _ one_ne_zero, Finsupp.weight_single]
  simp

theorem weighted_initial_separant [CommSemiring F] [Nontrivial F]
    (center : F) (Q : DifferentialPolynomial F r) :
    (initialJetSeparant center Q).weightedTotalDegree Fin.val ≤
      Q.weightedTotalDegree (indexWeight (r+1)) - r := by
  apply le_trans (weightedTotalDegree_aeval_le_of_le (indexWeight (r+1)) Fin.val _ _ ?_)
  · exact weightedTotalDegree_pderiv_le_sub _ _ Q
  · intro i
    cases i with
    | none => simp [weightedTotalDegree_C,indexWeight]
    | some j => exact (jetX j).le

/-- Taylor coefficients with denominator exponent d have total initial-index weight
at most d(V-r)+l for an equation of index weight V. -/
theorem weighted_rational_numerator [Field F] (center : Polynomial F)
    (Q : DifferentialPolynomial (Polynomial F) r) (V : ℕ) (hrV : r≤V)
    (hQ : Q.weightedTotalDegree (indexWeight (r+1)) ≤ V) (l : ℕ) :
    (rationalTaylorNumeratorOver F center Q l).weightedTotalDegree Fin.val ≤
       (2*(l-r)-1)*(V-r)+l := by
  have hsep := (weighted_initial_separant center Q).trans (Nat.sub_le_sub_right hQ r)
  induction l using Nat.strong_induction_on with
  | h l ih =>
    rw [rationalTaylorNumeratorOver]
    split_ifs with hl
    · have hden : 2*(l-r)-1=0 := by omega
      rw [hden,zero_mul,zero_add]
      exact (jetX _).le
    · have hden : ∀ m ∈ ((optionEquivLeft (Polynomial F) (Fin l)
            (universalTaylorResidual l center Q)).coeff (l-r)).support,
          Finsupp.weight (fun i : Fin l ↦ 2*(i.val-r)-1) m ≤ 2*(l-r)-2 :=
        fun m hm => denominator_weight_le_of_mem_universalTaylorResidual_coeff
          (r:=r) (K:=l) (h:=l-r) (by omega) center Q m hm
      have hd := weightedTotalDegree_clearedSubstitution_le_of_coeff C
        (initialJetSeparant center Q) (fun i : Fin l ↦ rationalTaylorNumeratorOver F center Q i.val)
        (fun i ↦ 2*(i.val-r)-1) Fin.val Fin.val (2*(l-r)-2) (V-r) (l-r+V)
        ((optionEquivLeft (Polynomial F) (Fin l) (universalTaylorResidual l center Q)).coeff (l-r))
        hsep (fun i => ih i.val i.isLt) hden (by
          intro m hm
          rw [weightedTotalDegree_C,zero_add]
          exact (indexWeight_le_of_mem_universalTaylorResidual_coeff l center Q _ m hm).trans
            (Nat.add_le_add_left hQ _))
      rw [← map_neg]
      apply (weightedTotalDegree_mul_le _ _ _).trans
      rw [weightedTotalDegree_C,zero_add]
      refine hd.trans ?_
      have he : 2*(l-r)-1=(2*(l-r)-2)+1 := by omega
      rw [he,Nat.add_mul,one_mul]
      omega

theorem weighted_padded_numerator [Field F] (center : Polynomial F)
    (Q : DifferentialPolynomial (Polynomial F) r) (V K τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hrV : r≤V)
    (hQ : Q.weightedTotalDegree (indexWeight (r+1)) ≤ V) (l : Fin K) :
    (commonTaylorNumeratorOver (F:=F) center Q τ l.val).weightedTotalDegree Fin.val ≤
      τ*(V-r)+l.val := by
  have hd := weighted_rational_numerator center Q V hrV hQ l.val
  have hs := (weighted_initial_separant center Q).trans (Nat.sub_le_sub_right hQ r)
  have hp := (weightedTotalDegree_pow_le Fin.val (initialJetSeparant center Q)
      (τ-(2*(l.val-r)-1))).trans (Nat.mul_le_mul_left _ hs)
  unfold commonTaylorNumeratorOver
  apply (weightedTotalDegree_mul_le _ _ _).trans
  have he := Nat.sub_add_cancel (hτ l)
  nlinarith

/-- An index-weight W bounds the degree in jet j by the quotient W/j. -/
theorem degreeOf_le_index_quotient [CommSemiring F] (f : MvPolynomial (Fin (r+1)) F)
    (i : Fin (r+1)) (hi : 0 < i.val) {W : ℕ} (hW : f.weightedTotalDegree Fin.val ≤ W) :
    f.degreeOf i ≤ W/i.val := by
  classical
  rw [degreeOf_le_iff]
  intro m hm
  apply (Nat.le_div_iff_mul_le hi).mpr
  have h := (le_weightedTotalDegree Fin.val hm).trans hW
  rw [Finsupp.weight_apply,Finsupp.sum_fintype _ _ (by simp)] at h
  simpa [nsmul_eq_mul] using
    (Finset.single_le_sum (f:=fun j : Fin (r+1) => m j • j.val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans h

#print axioms weighted_rational_numerator
#print axioms degreeOf_le_index_quotient
end
end PolynomialDifferential
