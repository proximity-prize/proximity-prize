import ProximityPrize.SubmissionLower.HighCore82209PrefixGeometry
import ProximityPrize.SubmissionLower.HighCore82209Ledger
import ProximityPrize.SubmissionLower.HighCore82209BankProof

set_option Elab.async false

namespace HighCore82209

theorem prefix_inventory : c3 :=
  HighCore82209_3.of_children HighCore82209_3_1.proof HighCore82209_3_2.proof
    schedule loss_ledger

theorem ordinary_high
    (hBridge : RetainedCountAt .h2367) {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (hl : 2356 ≤ M.overhead) (hu : M.overhead ≤ (heightCap : ℤ)) :
    Γ.card ≤ 266959677023545845 :=
  all_high_of_prefix_and_retained HighCore82209BankProof.interpolation_sources_for_crt
    prefix_inventory (fun band => by
      by_cases hb : band = .h2367
      · subst band
        exact hBridge
      · exact legacy_retained tangent_count band hb) M F hl hu

#print axioms ordinary_high
end HighCore82209
