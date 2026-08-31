import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactNestedFiveCapCoefficientBox6750Research
import ProximityPrize.SubmissionLower.ContactIdentityResidualGlobalFlagResearch
import ProximityPrize.SubmissionLower.ContactFactorCaps

 








namespace ProximityPrize.SubmissionLower.ContactNestedFiveCapQuotientSupport6750Research

open ContactFactorCaps
open ContactIdentityResidualGlobalFlagResearch
open ContactNestedFiveCapCoefficientBox6750Research

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

variable {K : Type*} [Field K]

 

theorem mem_nestedFiveCapCoefficientBox_iff
    (P : MvPolynomial (Fin 4) K) (D w T YS S : Nat) (hD : 0 < D) :
    P ∈ nestedFiveCapCoefficientBox K D w T YS S ↔
      MvPolynomial.weightedTotalDegree residualTotalWeights P ≤ T ∧
      MvPolynomial.weightedTotalDegree residualYSWeights P ≤ YS ∧
      MvPolynomial.weightedTotalDegree residualSWeights P ≤ S ∧
      MvPolynomial.weightedTotalDegree (contactWeights w) P ≤ D - 1 := by
  constructor
  · intro hP
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply (weightedTotalDegree_le_iff residualTotalWeights P T).mpr
      intro d hd
      have h := hP hd
      rw [weight_fin4]
      simpa [residualTotalWeights, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using h.1
    · apply (weightedTotalDegree_le_iff residualYSWeights P YS).mpr
      intro d hd
      have h := hP hd
      rw [weight_fin4]
      simpa [residualYSWeights, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using h.2.1
    · apply (weightedTotalDegree_le_iff residualSWeights P S).mpr
      intro d hd
      have h := hP hd
      rw [weight_fin4]
      simpa [residualSWeights] using h.2.2.1
    · apply (weightedTotalDegree_le_iff (contactWeights w) P (D - 1)).mpr
      intro d hd
      have h := hP hd
      rw [contact_weight]
      exact Nat.le_sub_one_of_lt h.2.2.2
  · rintro ⟨hTotal, hYS, hS, hContact⟩ d hd
    have ht :=
      (MvPolynomial.le_weightedTotalDegree residualTotalWeights hd).trans hTotal
    have hy :=
      (MvPolynomial.le_weightedTotalDegree residualYSWeights hd).trans hYS
    have hs :=
      (MvPolynomial.le_weightedTotalDegree residualSWeights hd).trans hS
    have hc :=
      (MvPolynomial.le_weightedTotalDegree (contactWeights w) hd).trans hContact
    rw [contact_weight] at hc
    have ht' : d 1 + d 2 + d 3 ≤ T := by
      simpa [weight_fin4, residualTotalWeights, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using ht
    have hy' : d 1 + d 2 ≤ YS := by
      simpa [weight_fin4, residualYSWeights, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using hy
    have hs' : d 2 ≤ S := by
      simpa [weight_fin4, residualSWeights] using hs
    exact ⟨ht', hy', hs', by omega⟩

 

theorem quotient_mem_nestedFiveCapCoefficientBox_of_mul_eq
    {G Q P : MvPolynomial (Fin 4) K}
    {D w T YS S c t y s : Nat}
    (hG : G ≠ 0) (hQ : Q ≠ 0) (hmul : G * Q = P)
    (hPbox : P ∈ nestedFiveCapCoefficientBox K D w T YS S)
    (hGc : MvPolynomial.weightedTotalDegree (contactWeights w) G = c)
    (hGt : MvPolynomial.weightedTotalDegree residualTotalWeights G = t)
    (hGy : MvPolynomial.weightedTotalDegree residualYSWeights G = y)
    (hGs : MvPolynomial.weightedTotalDegree residualSWeights G = s) :
    Q ∈ nestedFiveCapCoefficientBox K (D - c) w
      (T - t) (YS - y) (S - s) := by
  have hP : P ≠ 0 := by simpa [← hmul] using mul_ne_zero hG hQ
  have hD : 0 < D := by
    obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hP
    exact Nat.zero_lt_of_lt (hPbox hd).2.2.2
  have hcaps := (mem_nestedFiveCapCoefficientBox_iff P D w T YS S hD).mp hPbox
  have hcadd :
      MvPolynomial.weightedTotalDegree (contactWeights w) P =
        c + MvPolynomial.weightedTotalDegree (contactWeights w) Q := by
    rw [← hmul, weightedTotalDegree_mul (contactWeights w) G Q hG hQ, hGc]
  have htadd :
      MvPolynomial.weightedTotalDegree residualTotalWeights P =
        t + MvPolynomial.weightedTotalDegree residualTotalWeights Q := by
    rw [← hmul, weightedTotalDegree_mul residualTotalWeights G Q hG hQ, hGt]
  have hyadd :
      MvPolynomial.weightedTotalDegree residualYSWeights P =
        y + MvPolynomial.weightedTotalDegree residualYSWeights Q := by
    rw [← hmul, weightedTotalDegree_mul residualYSWeights G Q hG hQ, hGy]
  have hsadd :
      MvPolynomial.weightedTotalDegree residualSWeights P =
        s + MvPolynomial.weightedTotalDegree residualSWeights Q := by
    rw [← hmul, weightedTotalDegree_mul residualSWeights G Q hG hQ, hGs]
  have hDc : 0 < D - c := by omega
  apply (mem_nestedFiveCapCoefficientBox_iff Q
    (D - c) w (T - t) (YS - y) (S - s) hDc).mpr
  omega

end

end ProximityPrize.SubmissionLower.ContactNestedFiveCapQuotientSupport6750Research

#print axioms ProximityPrize.SubmissionLower.ContactNestedFiveCapQuotientSupport6750Research.mem_nestedFiveCapCoefficientBox_iff
#print axioms ProximityPrize.SubmissionLower.ContactNestedFiveCapQuotientSupport6750Research.quotient_mem_nestedFiveCapCoefficientBox_of_mul_eq
