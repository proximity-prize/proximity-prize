import ProximityPrize.SubmissionLower.Rect52PrefixBankProof
import ProximityPrize.SubmissionLower.Rect52PrefixPrefixGeometry
import ProximityPrize.SubmissionLower.Rect52PrefixLedger

set_option autoImplicit true

namespace Rect52Prefix

open Polynomial
open K1_14 (L)
open K1_14_1 (PoleData CRTLift evaluated poleProduct)

theorem prefix_at {u del} (M : AnchorModel u del) {Γ} (F : AnchoredFamily M Γ)
    (hw : InBand .h2391 M.overhead) (hshift : M.shift ∉ Γ) (H : L[X])
    (hH : AdjacentChart M F H) (tariff : CurveTariff .h2391 M F) :
    ∃ (D : PoleData M.overhead.toNat) (Crt : CRTLift D),
      poleProduct D = H * H.map (frobenius L p) ∧
      let rows := evaluated Crt (fun i => algebraMap K L (M.word i))
      Source .h2391 M F rows ∧ ∃ pairs : Pairs .h2391 M.overhead.toNat rows,
        Nonempty (PrefixInventory .h2391 M F pairs) := by
  obtain ⟨D,Crt,hprod,src⟩ := Rect52PrefixBankProof.interpolation_sources .h2391 u del M Γ F hw hshift H hH
  obtain ⟨pairs⟩ := buffered_pairs .h2391 M F hw src
  refine ⟨D,Crt,hprod,src,pairs,?_⟩
  exact Rect52Prefix_3.of_children Rect52Prefix_3_1.proof Rect52Prefix_3_2.proof schedule loss_ledger
    .h2391 u del M Γ F hw hshift H hH (fun _ => tariff) _ src pairs

theorem paid_bound {u del} {M : AnchorModel u del} {Γ} {F : AnchoredFamily M Γ} {rows}
    {pairs : Pairs .h2391 M.overhead.toNat rows} (Q : PrefixInventory .h2391 M F pairs) :
    Q.books.card ≤ 100178949002651624 := Q.paid

theorem terminal_moment : P1_7_1.groupedPoleMoment 8648 1834 ≤ 150928392143200 :=
  (Rect52PrefixBankProof.listed_ok .h2391 (terminal .h2391) (Or.inl rfl)).moment.1

theorem terminal_nodes : P1_7_1.nodeRows (terminal .h2391).shape = 7102499896688640 :=
  (Rect52PrefixBankProof.listed_ok .h2391 (terminal .h2391) (Or.inl rfl)).nodes

#print axioms prefix_at
#print axioms paid_bound
end Rect52Prefix
