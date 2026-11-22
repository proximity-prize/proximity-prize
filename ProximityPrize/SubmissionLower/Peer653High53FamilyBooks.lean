import ProximityPrize.SubmissionLower.Peer653High53FamilyTariffs

-- Adapted from the pinned peer revision d3db79e374b16bebd9780b96f1c1fe0c156679bc, HighCore82229Family.lean.

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

section
namespace Peer653High53
open Peer653High53 (K Band)
abbrev PrefixFees := P1_7.PrefixFees
structure PrefixBooks (b : Band) where
  loss : Finset K
  point : Finset K
  lowSeed : Finset K
  lowJet : Finset K
  fixedODE : Finset K
  content : Finset K
  loss_le : loss.card ≤ (fees b).loss
  point_le : point.card ≤ (fees b).point
  lowSeed_le : lowSeed.card ≤ (fees b).lowSeed
  lowJet_le : lowJet.card ≤ (fees b).lowJet
  fixedODE_le : fixedODE.card ≤ (fees b).fixedODE
  content_le : content.card ≤ (fees b).content
noncomputable def PrefixBooks.union {b} (B : PrefixBooks b) : Finset K := by
  classical exact B.loss ∪ B.point ∪ B.lowSeed ∪ B.lowJet ∪ B.fixedODE ∪ B.content
private theorem union_le {A B : Finset K} {a b : ℕ} (ha : A.card ≤ a) (hb : B.card ≤ b) :
    (A ∪ B).card ≤ a+b := (Finset.card_union_le _ _).trans (Nat.add_le_add ha hb)
theorem PrefixBooks.card_union {b} (B : PrefixBooks b) : B.union.card ≤ (prefixFee b) := by
  exact union_le (union_le (union_le (union_le (union_le B.loss_le B.point_le)
    B.lowSeed_le) B.lowJet_le) B.fixedODE_le) B.content_le
end Peer653High53
end
