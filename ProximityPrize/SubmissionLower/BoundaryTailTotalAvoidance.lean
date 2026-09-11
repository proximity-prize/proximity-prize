import ProximityPrize.SubmissionLower.SecondJetRefinements
import ProximityPrize.SubmissionLower.BoundaryTailInterpolation
import ProximityPrize.SubmissionLower.BoundaryTailLeadingCoefficient

namespace ProximityPrize.SubmissionLower.BoundaryTailTotalAvoidance
open MvPolynomial SecondJetSupport SecondJetCoefficients SecondJetCoefficientSpecialization
open SecondJetClearedHelper SecondJetHelperWeights BoundaryTailInterpolation
open SecondJetRelaxedCoefficientsReceipt RCN234 RCN156
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K N : Type*} [Field K] [Fintype N]

def ProperHelper (F Q : MvPolynomial (Fin 4) K) (B U L s capR capY capT : ℕ)
    (nodes : N ↪ K) (u0 u1 : N → K) : Prop :=
  IsRelPrime F Q ∧
  (wt residualSWeights Q ≤ B+s*(capR-1) ∧
    wt residualYSWeights Q ≤ U+s*(capY-1) ∧
    wt residualTotalWeights Q ≤ L+s*(capT-1)) ∧
  ∀ f : Polynomial K, f.natDegree ≤ 131071 → ∀ z : K, ∀ S : Finset N,
    181333 ≤ S.card → (∀ i ∈ S, f.eval (nodes i) = u0 i+u1 i*z) →
    RCN319.specialization K f z F = 0 → RCN319.specialization K f z Q = 0

theorem helper_or_divisibility (P : Poly (K := K)) (F : MvPolynomial (Fin 4) K)
    (m B s U L k n0 capR capY capT : ℕ)
    (nodes : N ↪ K) (u0 u1 : N → K)
    (hP : Interpolant m B s U L k n0 nodes u0 u1 P)
    (hFi : Irreducible F) (hFT : L < wt residualTotalWeights F)
    (hsB : 2*s ≤ B) (hsU : s ≤ U) (hsL : s ≤ L) (hks : k ≤ s) (hsm : s < m)
    (hR : 1 ≤ capR) (hY : 1 ≤ capY) (hT : 1 ≤ capT)
    (hF : wt residualSWeights F ≤ capR ∧ wt residualYSWeights F ≤ capY ∧
      wt residualTotalWeights F ≤ capT)
    (hfact : ∀ d ≤ s, (d.factorial : K) ≠ 0) :
    (∃ Q, ProperHelper F Q B U L s capR capY capT nodes u0 u1) ∨
      (n0 ≤ (asS P).natDegree ∧ ∀ d ≤ k, F ∣ helper P F (s-d) d) := by
  classical
  have hflags : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ L := by
    intro e he
    have h := hP.2.1 e he
    exact ⟨h.1,h.2.2.1,h.2.2.2.1⟩
  have hS : ∀ e ∈ P.support, e 1 ≤ s := fun e he => (hP.2.1 e he).2.1
  have hdegree : (asS P).natDegree ≤ s := by
    simpa using asS_derivative_degree P s 0 hS
  by_cases hn : (asS P).natDegree < n0
  · left
    let n := (asS P).natDegree
    let Q := (asS P).leadingCoeff
    have hQ := SecondJetTotalAvoidance.leading_not_dvd P hP.1 F L
      (fun e he => (hflags e he).2.2) hFT
    refine ⟨Q,hFi.isRelPrime_iff_not_dvd.mpr hQ.2,?_,?_⟩
    · have hw := derivative_coefficient_weights P B U L 0 n hflags
      simp only [Function.iterate_zero, id_eq, Nat.mul_zero, Nat.sub_zero] at hw
      change wt residualSWeights ((asS P).coeff n) ≤ B+s*(capR-1) ∧
        wt residualYSWeights ((asS P).coeff n) ≤ U+s*(capY-1) ∧
        wt residualTotalWeights ((asS P).coeff n) ≤ L+s*(capT-1)
      omega
    · intro f hf z S hSc hvalues _hFzero
      have hweight : ∀ e ∈ P.support,
          e 0+131071*e 2+131070*e 3+131069*e 1+
            SecondJetRelaxedDifferentiation.reserve k n0 (e 1)*50264 < m*181333 := by
        intro e he
        have hw := (hP.2.1 e he).2.2.2.2
        dsimp [BoundaryTailInterpolation.cutoff] at hw
        omega
      apply BoundaryTailLeadingCoefficient.low_coefficient_vanish P m k n0 n
        (by dsimp [n]; omega) hn (hfact n hdegree) hweight nodes u0 u1 hP.2.2.1
        f hf z S hSc hvalues
      intro j hj
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hj,map_zero]
  · by_cases hdiv : ∀ d ≤ k, F ∣ helper P F (s-d) d
    · exact Or.inr ⟨Nat.le_of_not_gt hn,hdiv⟩
    · left
      push_neg at hdiv
      obtain ⟨d,hd,hproper⟩ := hdiv
      refine ⟨helper P F (s-d) d,hFi.isRelPrime_iff_not_dvd.mpr hproper,?_,?_⟩
      · have hw := helper_weights P F B U L s d capT capY capR hsB hsU hsL
          (hd.trans hks) hR hY hT hflags hF
        have hr := Nat.mul_le_mul_right (capR-1) (Nat.sub_le s d)
        have hy := Nat.mul_le_mul_right (capY-1) (Nat.sub_le s d)
        have ht := Nat.mul_le_mul_right (capT-1) (Nat.sub_le s d)
        omega
      · intro f hf z S hSc hvalues hFzero
        exact helper_vanish P F (s-d) d (asS_derivative_degree P s d hS) f z hFzero
          (hP.2.2.2 d hd f hf z S hSc hvalues)

end
end ProximityPrize.SubmissionLower.BoundaryTailTotalAvoidance
