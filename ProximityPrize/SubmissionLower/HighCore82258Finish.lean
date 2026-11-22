import ProximityPrize.SubmissionLower.HighCore82258PrefixGeometry
import ProximityPrize.SubmissionLower.HighCore82258Ledger
import ProximityPrize.SubmissionLower.HighCore82258BankProof


namespace HighCore82258

theorem prefix_inventory : c3 :=
  HighCore82258_3.of_children HighCore82258_3_1.proof HighCore82258_3_2.proof
    schedule loss_ledger

theorem ordinary_high
    (hBridge : RetainedCountAt .h2367) {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (hl : 2414 ≤ M.overhead) (hu : M.overhead ≤ (heightCap : ℤ)) :
    Γ.card ≤ 267872462194200158 :=
  all_high_of_prefix_and_retained HighCore82258BankProof.interpolation_sources_for_crt
    prefix_inventory (fun band => by
      by_cases hb : band = .h2367
      · subst band
        exact hBridge
      · exact legacy_retained tangent_count band hb) M F hl hu

#print axioms ordinary_high
end HighCore82258
