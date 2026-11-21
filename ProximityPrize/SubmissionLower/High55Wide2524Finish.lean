import ProximityPrize.SubmissionLower.High55Wide2524PrefixGeometry
import ProximityPrize.SubmissionLower.High55Wide2524Ledger
import ProximityPrize.SubmissionLower.High55Wide2524Regular

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000


namespace High55Wide2524

theorem prefix_inventory : c3 :=
  High55Wide2524_3.of_children High55Wide2524_3_1.proof High55Wide2524_3_2.proof
    schedule loss_ledger

theorem ordinary_high_2524_2526 {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (hl : 2524 ≤ M.overhead) (hu : M.overhead ≤ 2526) :
    Γ.card ≤ 271937844038970720 :=
  first_high_of_prefix_and_retained prefix_inventory tangent_count M F hl hu

#print axioms ordinary_high_2524_2526
end High55Wide2524
