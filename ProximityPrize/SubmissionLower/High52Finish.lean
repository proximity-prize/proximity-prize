import ProximityPrize.SubmissionLower.OrdinaryTransfer
import ProximityPrize.SubmissionLower.High55Wide
import ProximityPrize.SubmissionLower.High52PrefixGeometry
import ProximityPrize.SubmissionLower.High52Ledger
import ProximityPrize.SubmissionLower.High52Regular

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000


namespace High52

theorem prefix_inventory : c3 :=
  High52_3.of_children High52_3_1.proof High52_3_2.proof
    schedule loss_ledger

theorem intermediate_high {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (hl : 2452 ≤ M.overhead) (hu : M.overhead ≤ 2523) :
    Γ.card ≤ 271879479853429943 :=
  first_high_of_prefix_and_retained prefix_inventory tangent_count M F hl hu

#print axioms intermediate_high
/-- The ordinary estimate through the common model height cap. -/
theorem ordinary_high {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (hl : 2452 ≤ M.overhead) (hu : M.overhead ≤ 33463) :
    Γ.card ≤ 271937844038970720 := by
  by_cases hmid : M.overhead ≤ 2523
  · exact (intermediate_high M F hl hmid).trans (by decide)
  · exact (High55Wide.ordinary_high_from2524 M
      (OrdinaryTransfer.family M F le_rfl (by decide : 179876 ≤ agreement)) (by omega) hu).trans (by decide)

#print axioms ordinary_high
end High52
