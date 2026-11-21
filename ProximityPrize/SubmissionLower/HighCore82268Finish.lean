import ProximityPrize.SubmissionLower.HighCore82268PrefixGeometry
import ProximityPrize.SubmissionLower.HighCore82268Ledger
import ProximityPrize.SubmissionLower.HighCore82268Tangent

set_option Elab.async false

namespace HighCore82268

theorem prefix_inventory : c3 :=
  HighCore82268_3.of_children HighCore82268_3_1.proof HighCore82268_3_2.proof
    schedule loss_ledger

theorem ordinary_high {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (hl : 2536 ≤ M.overhead) (hu : M.overhead ≤ (heightCap : ℤ)) :
    Γ.card ≤ 264677500244581301 :=
  all_high_of_prefix_and_retained prefix_inventory tangent_count M F hl hu

theorem ordinary_high_from2527 {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (hl : 2527 ≤ M.overhead) (hu : M.overhead ≤ (heightCap : ℤ)) :
    Γ.card ≤ 268077798305256115 :=
  all_high_from2527_of_prefix_and_retained prefix_inventory tangent_count M F hl hu

#print axioms ordinary_high_from2527
#print axioms ordinary_high
end HighCore82268
