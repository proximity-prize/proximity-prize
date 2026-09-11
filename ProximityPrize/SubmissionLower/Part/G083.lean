import ProximityPrize.SubmissionLower.Part.G082


section Compact_SecondJetRelaxedInterpolation
/-! The three concrete relaxed second-jet interpolants. Their nonzero source,
all requested derivative vanishings, and degree budgets are unconditional
consequences of the checked dimensions. Geometric counting is separate. -/
namespace ProximityPrize.SubmissionLower.SecondJetRelaxedInterpolation
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetSpecialize SecondJetDifferentiation
open SecondJetRelaxedCoefficientsReceipt SecondJetRelaxedDifferentiation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K N : Type*} [Field K] [Fintype N]

/-- The complete interpolation interface: support, local contact, and vanishing
on codewords with the required number of agreements. -/
def Interpolant (m B s U L k n0 : ℕ) (nodes : N ↪ K) (u0 u1 : N → K)
    (P : Poly (K := K)) : Prop :=
  P ≠ 0 ∧
  (∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1 ≤ s ∧ e 1+e 2+e 3 ≤ U ∧
    e 1+e 2+e 3+e 4 ≤ L ∧
    e 0+131071*e 2+131070*e 3+131069*e 1 < cutoff m k n0 (e 1)) ∧
  (∀ i, MvPolynomial.X 0^m ∣ substitute (K := K)
    (localize (nodes i) (u0 i) (u1 i) P)) ∧
  ∀ d ≤ k, ∀ f : Polynomial K, f.natDegree ≤ 131071 → ∀ z : K, ∀ S : Finset N,
    181353 ≤ S.card → (∀ i ∈ S, f.eval (nodes i) = u0 i+u1 i*z) →
      specialize f z ((pderiv 1)^[d] P) = 0

theorem exists_of_dimension (m B s U L k n0 : ℕ) (hsB : 2*s ≤ B) (hkm : k < m)
    (hN : Fintype.card N = 262144) (nodes : N ↪ K) (u0 u1 : N → K)
    (hcard : 262144*SecondJetRelaxedGlobalMap.rankBound m L B s U
        (fun h => (cutoff m k n0 h+B-1)/131071) <
      Fintype.card (SecondJetRelaxedGlobalIndex.Index (cutoff m k n0) 131071 L B s U)) :
    ∃ P, Interpolant m B s U L k n0 nodes u0 u1 P := by
  obtain ⟨P,hP,hbounds,hcontact⟩ := SecondJetRelaxedGlobalIndex.exists_weighted_global_contact
    (cutoff m k n0) 131071 L B s U m hsB (by decide) nodes u0 u1 (by simpa only [hN] using hcard)
  have hc : ∀ i, MvPolynomial.X 0^m ∣ substitute (K := K)
      (localize (nodes i) (u0 i) (u1 i) P) := fun i =>
    SecondJetGlobalDifferentiation.nested_to_flat_contact _ m (hcontact i)
  refine ⟨P,hP,hbounds,hc,?_⟩
  intro d hd f hf z S hS hvalues
  apply derivative_vanish P m 181353 131071 k n0 d (by decide) (by decide)
    (by omega) hd ?_ nodes u0 u1 hc f hf z S hS hvalues
  intro e he
  have hb := (hbounds e he).2.2.2.2
  dsimp [cutoff] at hb
  norm_num
  omega

theorem exists_116 (hN : Fintype.card N = 262144) (nodes : N ↪ K) (u0 u1 : N → K) :
    ∃ P, Interpolant 116 47 21 157 2233 5 7 nodes u0 u1 P := by
  apply exists_of_dimension _ _ _ _ _ _ _ (by decide) (by decide) hN nodes u0 u1
  rw [SecondJetRelaxedRanksReceipt.exact_rank_116, card_116]
  decide

theorem exists_96 (hN : Fintype.card N = 262144) (nodes : N ↪ K) (u0 u1 : N → K) :
    ∃ P, Interpolant 96 38 17 130 2141 4 5 nodes u0 u1 P := by
  apply exists_of_dimension _ _ _ _ _ _ _ (by decide) (by decide) hN nodes u0 u1
  rw [SecondJetRelaxedRanksReceipt.exact_rank_96, card_96]
  decide

theorem exists_108 (hN : Fintype.card N = 262144) (nodes : N ↪ K) (u0 u1 : N → K) :
    ∃ P, Interpolant 108 41 19 146 2111 4 7 nodes u0 u1 P := by
  apply exists_of_dimension _ _ _ _ _ _ _ (by decide) (by decide) hN nodes u0 u1
  rw [SecondJetRelaxedRanksReceipt.exact_rank_108, card_108]
  decide

end
end ProximityPrize.SubmissionLower.SecondJetRelaxedInterpolation

end Compact_SecondJetRelaxedInterpolation
