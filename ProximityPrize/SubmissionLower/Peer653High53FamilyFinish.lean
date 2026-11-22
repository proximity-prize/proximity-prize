import ProximityPrize.SubmissionLower.Peer653High53FamilyAssembly

-- Adapted from the pinned peer revision d3db79e374b16bebd9780b96f1c1fe0c156679bc, HighCore82229Family.lean.

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace Peer653High53

theorem all_high_of_prefix_and_retained
    (hSource : CRTSourceExists) (hPrefix : c3) (hRetained : ∀ b, RetainedCountAt b)
    {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (hl : 2390 ≤ M.overhead) (hu : M.overhead ≤ (heightCap : ℤ)) :
    Γ.card ≤ 272512621865658327 := by
  obtain ⟨b, hlo, hhi⟩ := height_cover (h := M.overhead.toNat) (by omega) (by omega)
  have h := of_children hSource
    (fun b _ _ M _ F hb _ _ src => buffered_pairs b M F hb src)
    hPrefix hRetained
    b u del M Γ F (by omega) (by omega)
  have hb : prefixFee b + retainedCap b + 1 ≤ 272512621865658327 := by
    exact (accounting b).1.le.trans (accounting b).2
  exact h.trans hb

#print axioms all_high_of_prefix_and_retained
end Peer653High53
