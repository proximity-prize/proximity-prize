import ProximityPrize.SubmissionLower.Peer653High53Pairs
import ProximityPrize.SubmissionLower.High53Model
import ProximityPrize.SubmissionLower.HighFamilyBase82180

-- Adapted from the pinned peer revision d3db79e374b16bebd9780b96f1c1fe0c156679bc, HighCore82229Family.lean.

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace Peer653High53
export P1 (K I p node twist blockLength)
export High53Model (AnchorModel AnchoredFamily AdjacentChart)
abbrev t : ℕ := blockLength - agreement

theorem degree_at_height {u D Γ} (M : AnchorModel u D) (F : AnchoredFamily M Γ)
    (γ : K) (hγ : γ ∈ Γ) : (F.scalar γ).natDegree ≤ P1.k - 1 + M.overhead.toNat := by
  rcases (F.mark γ hγ).scalar_degree with h | h
  · simp [h]
  · change (F.scalar γ).natDegree ≤ P1.k - 1 + (P1.ModelAt.overhead M).toNat
    omega

def prefixFee (b : Band) : ℕ :=
  let f := fees b
  f.loss + f.point + f.lowSeed + f.lowJet + f.fixedODE + f.content

end Peer653High53
