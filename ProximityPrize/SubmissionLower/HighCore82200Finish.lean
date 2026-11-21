import ProximityPrize.SubmissionLower.HighCore82200PrefixGeometry
import ProximityPrize.SubmissionLower.HighCore82200Ledger
import ProximityPrize.SubmissionLower.HighCore82200BankProof

set_option Elab.async false

namespace HighCore82200

theorem prefix_inventory : c3 :=
  HighCore82200_3.of_children HighCore82200_3_1.proof HighCore82200_3_2.proof
    schedule loss_ledger

theorem ordinary_high {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (hl : 2367 ≤ M.overhead) (hu : M.overhead ≤ (heightCap : ℤ)) :
    Γ.card ≤ 266550994122107653 :=
  all_high_of_prefix_and_retained HighCore82200BankProof.interpolation_sources
    prefix_inventory tangent_count M F hl hu

#print axioms ordinary_high
end HighCore82200
