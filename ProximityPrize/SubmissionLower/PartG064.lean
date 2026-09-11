import ProximityPrize.SubmissionLower.PartG063


section Compact_SecondJetPairBounds
/-! Degree and numerical interfaces for the global proper-intersection count. -/
namespace ProximityPrize.SubmissionLower.SecondJetPairBounds
open MvPolynomial RCN260 RCN052 RCN294 RCN234 RCN156
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {K : Type} [Field K]

theorem degree_caps_of_weights (Q : MvPolynomial (Fin 4) K) (r y t : ℕ)
    (hw : wt residualSWeights Q ≤ r ∧ wt residualYSWeights Q ≤ y ∧
      wt residualTotalWeights Q ≤ t) :
    Q.degreeOf 1 ≤ y ∧ Q.degreeOf 2 ≤ r ∧ Q.degreeOf 3 ≤ t := by
  refine ⟨?_,?_,?_⟩
  all_goals
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
  · have h := (RCN081.weightedTotalDegree_le_iff _ _ _).mp hw.2.1 e he
    simp only [residualYSWeights,RCN081.weight_fin4] at h
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Fin.isValue,Nat.mul_zero,Nat.mul_one,Nat.zero_add,Nat.add_zero] at h
    omega
  · have h := (RCN081.weightedTotalDegree_le_iff _ _ _).mp hw.1 e he
    simpa [residualSWeights,RCN081.weight_fin4] using h
  · have h := (RCN081.weightedTotalDegree_le_iff _ _ _).mp hw.2.2 e he
    simp [residualTotalWeights,RCN081.weight_fin4] at h
    omega

theorem leading_degree_caps (P : SecondJetSupport.Poly (K := K)) (B U L : ℕ)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ L) :
    (SecondJetCoefficients.asS P).leadingCoeff.degreeOf 1 ≤ U ∧
    (SecondJetCoefficients.asS P).leadingCoeff.degreeOf 2 ≤ B ∧
    (SecondJetCoefficients.asS P).leadingCoeff.degreeOf 3 ≤ L := by
  apply degree_caps_of_weights
  have h := SecondJetHelperWeights.derivative_coefficient_weights P B U L 0
    (SecondJetCoefficients.asS P).natDegree hP
  simp only [Function.iterate_zero,id_eq,Nat.mul_zero,Nat.sub_zero] at h
  change wt residualSWeights ((SecondJetCoefficients.asS P).coeff _) ≤ B ∧
    wt residualYSWeights ((SecondJetCoefficients.asS P).coeff _) ≤ U ∧
    wt residualTotalWeights ((SecondJetCoefficients.asS P).coeff _) ≤ L
  omega

theorem left_numerator_le (P : UnequalParameters) (F : MvPolynomial (Fin 4) K)
    (hY : F.degreeOf 1 ≤ P.leftY) (hR : F.degreeOf 2 ≤ P.leftR)
    (hZ : F.degreeOf 3 ≤ P.leftZ) :
    (P.n-P.w)*dot P.leftAgreement (regularVector P F)+
      (P.errors+1)*P.gap*(regularVector P F).z ≤ P.regularNumerator := by
  have hy : (regularVector P F).y ≤ P.mixedCost.y :=
    Nat.add_le_add (Nat.mul_le_mul_right P.rightZ hR) (Nat.mul_le_mul_right P.rightR hZ)
  have hr : (regularVector P F).r ≤ P.mixedCost.r :=
    Nat.add_le_add (Nat.mul_le_mul_right P.rightZ hY) (Nat.mul_le_mul_right P.rightY hZ)
  have hz : (regularVector P F).z ≤ P.mixedCost.z :=
    Nat.add_le_add (Nat.mul_le_mul_right P.rightR hY) (Nat.mul_le_mul_right P.rightY hR)
  have hd : dot P.leftAgreement (regularVector P F) ≤ dot P.agreement P.mixedCost :=
    Nat.add_le_add (Nat.add_le_add
      (Nat.mul_le_mul (le_max_left _ _) hy)
      (Nat.mul_le_mul (le_max_left _ _) hr))
      (Nat.mul_le_mul (le_max_left _ _) hz)
  exact Nat.add_le_add (Nat.mul_le_mul_left _ hd) (Nat.mul_le_mul_left _ hz)

theorem count_le_cap (P : UnequalParameters) (F : MvPolynomial (Fin 4) K)
    (hY : F.degreeOf 1 ≤ P.leftY) (hR : F.degreeOf 2 ≤ P.leftR)
    (hZ : F.degreeOf 3 ≤ P.leftZ) (count : ℕ) (hgap : 0 < P.gap)
    (hc : count*P.gap ≤ (P.n-P.w)*dot P.leftAgreement (regularVector P F)+
      (P.errors+1)*P.gap*(regularVector P F).z) : count ≤ P.regularCountCap :=
  P.regular_count_le count hgap (hc.trans (left_numerator_le P F hY hR hZ))

end
end ProximityPrize.SubmissionLower.SecondJetPairBounds

end Compact_SecondJetPairBounds
