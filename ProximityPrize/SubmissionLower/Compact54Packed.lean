import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
namespace Compact54Packed
open Compact50Cover (Tile PaidBatch tilesOf checks )
open K1_13 (Shape)
open K1_13_8 (Valid)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered)

/-- The low bits store tag, width, index and order. The payload stores a point run,
the two rectangle spans, or the shared rate and its amount. -/
def decode (word : ℕ) : List Tile :=
  let z := word / 4
  let b := z % 256
  let j := z / 256 % 64
  let l := z / 16384 % 256
  let q := z / 4194304
  match word % 4 with
  | 0 => (List.range (q+1)).map fun i => .point b (j+i) l
  | 1 => [.rectangle b j (b+q%256) (j+q/256) l]
  | _ =>
    let pivot : Fin 3 := ⟨q / 4 % 4 % 3, Nat.mod_lt _ (by decide)⟩
    let split := match q / 16 % 4 with | 0 => 1 | 1 => 2 | _ => 10
    [.shared b j l ⟨if q%2=1 then .tilted else .ordinary, pivot, split, q/2%2=1, q/64⟩]



end Compact54Packed
