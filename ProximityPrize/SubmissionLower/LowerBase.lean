import ProximityPrize.SubmissionLower.GoldBranch6N7
set_option Elab.async false
set_option autoImplicit true
section
namespace P1_6
noncomputable section
open Polynomial
open P1 (K I k node AnchorModel AnchoredFamily)
open K1_13 (Geom embed extend atJet PoleData)
open scoped BigOperators
theorem degree_at_height {u D Γ} (M : AnchorModel u D) (F : AnchoredFamily M Γ)
    (γ : K) (hγ : γ ∈ Γ) : (F.scalar γ).natDegree ≤ k - 1 + M.overhead.toNat := by
  rcases (F.mark γ hγ).scalar_degree with h | h
  · simp [h]
  · change (F.scalar γ).natDegree ≤ k - 1 + (P1.ModelAt.overhead M).toNat
    omega
end
end P1_6
end
