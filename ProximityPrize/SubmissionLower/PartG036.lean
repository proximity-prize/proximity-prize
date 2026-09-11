import ProximityPrize.SubmissionLower.PartG035


section Compact_SecondJetVanish
/-! A second-jet interpolant vanishes on every codeword with enough agreements. -/
namespace ProximityPrize.SubmissionLower.SecondJetVanish
open MvPolynomial SecondJetSupport SecondJetGlobalSupport SecondJetDifferentiation SecondJetSpecialize
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
variable {K N : Type*} [Field K]
local instance : DecidableEq K := Classical.decEq K
local instance : DecidableEq N := Classical.decEq N

theorem eq_zero_of_contact_degree (P : Poly (K := K)) (f : Polynomial K) (z : K)
    (nodes : N ↪ K) (u0 u1 : N → K) (S : Finset N) (m : ℕ)
    (hcontact : ∀ i ∈ S, MvPolynomial.X 0^m ∣ substitute (K := K)
      (localize (nodes i) (u0 i) (u1 i) P))
    (hvalues : ∀ i ∈ S, f.eval (nodes i) = u0 i+u1 i*z)
    (hdegree : (specialize f z P).natDegree < m*S.card) : specialize f z P = 0 := by
  classical
  by_contra hn
  have hmult : ∀ i ∈ S, m ≤ (specialize f z P).rootMultiplicity (nodes i) := by
    intro i hi
    exact (Polynomial.le_rootMultiplicity_iff hn).mpr
      (root_contact P f (nodes i) (u0 i) (u1 i) z m (hvalues i hi) (hcontact i hi))
  have hh := BCHKSSubstitutionVanish.mul_card_le_natDegree_of_rootMultiplicity
    (specialize f z P) nodes S m hmult
  exact (Nat.not_le_of_gt hdegree) hh

variable [Fintype N]

end
end ProximityPrize.SubmissionLower.SecondJetVanish

end Compact_SecondJetVanish
