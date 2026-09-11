import ProximityPrize.SubmissionLower.SecondJetRefinements

namespace ProximityPrize.SubmissionLower.BoundaryTailInterpolation
open SecondJetDifferentiation
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetSpecialize
open SecondJetRelaxedCoefficientsReceipt SecondJetRelaxedDifferentiation
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
variable {K N : Type*} [Field K] [Fintype N]

def cutoff (m k n0 h : ℕ) : ℕ := m*181333-SecondJetRelaxedDifferentiation.reserve k n0 h*50264

def Interpolant (m B s U L k n0 : ℕ) (nodes : N ↪ K) (u0 u1 : N → K)
    (P : Poly (K := K)) : Prop :=
  P ≠ 0 ∧
  (∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1 ≤ s ∧ e 1+e 2+e 3 ≤ U ∧
    e 1+e 2+e 3+e 4 ≤ L ∧
    e 0+131071*e 2+131070*e 3+131069*e 1 < cutoff m k n0 (e 1)) ∧
  (∀ i, MvPolynomial.X 0^m ∣ substitute (K := K)
    (localize (nodes i) (u0 i) (u1 i) P)) ∧
  ∀ d ≤ k, ∀ f : Polynomial K, f.natDegree ≤ 131071 → ∀ z : K, ∀ S : Finset N,
    181333 ≤ S.card → (∀ i ∈ S, f.eval (nodes i) = u0 i+u1 i*z) →
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
  apply derivative_vanish P m 181333 131071 k n0 d (by decide) (by decide)
    (by omega) hd ?_ nodes u0 u1 hc f hf z S hS hvalues
  intro e he
  have hb := (hbounds e he).2.2.2.2
  dsimp [cutoff] at hb
  norm_num
  omega


end
end ProximityPrize.SubmissionLower.BoundaryTailInterpolation
