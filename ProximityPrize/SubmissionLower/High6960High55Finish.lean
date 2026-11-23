import ProximityPrize.SubmissionLower.High6960High55PrefixGeometry
import ProximityPrize.SubmissionLower.High6960High55Ledger
import ProximityPrize.SubmissionLower.High6960High55Tangent

set_option Elab.async false

namespace High6960High55

theorem prefix_inventory : c3 :=
  High6960High55_3.of_children High6960High55_3_1.proof High6960High55_3_2.proof
    schedule loss_ledger

theorem ordinary_high {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (hl:2696≤M.overhead) (hu:M.overhead≤(heightCap:ℤ)) :
    Γ.card≤272515177455741613:=by
  obtain ⟨b,hlo,hhi⟩:=height_cover (h:=M.overhead.toNat) (by omega) (by omega)
  have h := of_children High6960High55BankProof.interpolation_sources
    (fun b _ _ M _ F hb _ _ src => buffered_pairs b M F hb src)
    prefix_inventory (fun b _ hl hu x => High6960High55Terminal.terminal_bounds b hl hu x) tangent_count
    b u del M Γ F (by omega) (by omega)
  apply h.trans
  exact (accounting b).1.le.trans (accounting b).2

#print axioms ordinary_high
end High6960High55
