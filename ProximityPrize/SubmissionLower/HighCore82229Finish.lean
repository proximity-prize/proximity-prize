import ProximityPrize.SubmissionLower.HighCore82229PrefixGeometry
import ProximityPrize.SubmissionLower.HighCore82229Ledger
import ProximityPrize.SubmissionLower.HighCore82229BankProof

set_option Elab.async false

namespace HighCore82229

theorem prefix_inventory : c3 :=
  HighCore82229_3.of_children HighCore82229_3_1.proof HighCore82229_3_2.proof
    schedule loss_ledger

theorem ordinary_high
    (hBridge : RetainedCountAt .h2367) {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (hl : 2356 ≤ M.overhead) (hu : M.overhead ≤ (heightCap : ℤ)) :
    Γ.card ≤ 268265986140156442 :=
  all_high_of_prefix_and_retained HighCore82229BankProof.interpolation_sources_for_crt
    prefix_inventory (fun band => by
      by_cases hb : band = .h2367
      · subst band
        exact hBridge
      · exact legacy_retained tangent_count band hb) M F hl hu

#print axioms ordinary_high
end HighCore82229
