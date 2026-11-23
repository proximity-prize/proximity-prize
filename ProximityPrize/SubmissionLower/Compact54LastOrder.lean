import ProximityPrize.SubmissionLower.Compact54Packed

set_option Elab.async false
set_option maxRecDepth 16000

namespace Compact54LastOrder

open Compact50Cover (Tile PaidBatch)
open Compact54Packed (unpack readWords)
open Compact54FastPrice (paysFast fastBatch)
open Final50PriceCaps (Band start endWidth allowance actualAllowance activeCap)
open Final50PriceActualOrder (raised raisedBefore)
open private paidFast supportsOrder contractedFast exactPointFast
  from ProximityPrize.SubmissionLower.Compact54FastPrice

private theorem lastOrder_eq (b j t w l : Nat) :
    raised .two7last b j t w l = raisedBefore .two7last b j t w l := by
  change max (raisedBefore .two7last b j t w l) 0 = _
  exact Nat.max_zero _

/-- The last band for top two has no extra orders. Use its existing order directly. -/
private def paidPoint (b j t l : Nat) : Prop :=
  let k : Band := .two7last
  let top := (start k).t + t
  0 < l ∧ supportsOrder k ⟨b,j,t⟩ l ∧
    (contractedFast ⟨b,j,t⟩ (start k) l (activeCap k) ≤ allowance top k b j t ∨
      ∀ w : Fin 27, (start k).b ≤ w.val → w.val ≤ endWidth k → w.val + b ≤ 137 →
        contractedFast ⟨b,j,t⟩ ⟨w.val,(start k).j,(start k).t⟩
          (raisedBefore k b j t w.val l) (activeCap k) ≤ actualAllowance top k w.val b j t)

private def paidLast (t : Nat) : Tile → Prop
  | .point b j l => paidPoint b j t l
  | tile => paidFast .two7last t tile

private instance (t : Nat) (tile : Tile) : Decidable (paidLast t tile) := by
  cases tile <;> unfold paidLast
  · infer_instance
  · infer_instance
  · unfold paidPoint
    infer_instance
  · infer_instance

private theorem paidLast_iff (t : Nat) (tile : Tile) :
    paidLast t tile ↔ paidFast .two7last t tile := by
  cases tile <;> simp only [paidLast]
  simp only [paidPoint, paidFast, exactPointFast, lastOrder_eq]
  tauto

private def paysLast (t : Nat) (tiles : List Tile) : Bool :=
  tiles.all (fun tile => decide (paidLast t tile))

private theorem paysFast_of_last (t : Nat) (tiles : List Tile)
    (checked : paysLast t tiles = true) : paysFast .two7last t tiles = true := by
  apply List.all_eq_true.mpr
  intro tile ht
  exact decide_eq_true ((paidLast_iff t tile).mp (of_decide_eq_true (List.all_eq_true.mp checked tile ht)))

def paidGroupLast {t : Nat} (codes : List String)
    (checked : codes.all (fun code => paysLast t (unpack (readWords code))) = true := by
      decide +kernel) : List (PaidBatch .two7last t) := by
  have paid := (List.all_eq_true (l := codes)
    (p := fun code => paysLast t (unpack (readWords code)))).mp checked
  exact codes.attach.map fun code =>
    fastBatch (k := .two7last) (t := t) (unpack (readWords code.val))
      (paysFast_of_last t _ (paid code.val code.property))

end Compact54LastOrder
