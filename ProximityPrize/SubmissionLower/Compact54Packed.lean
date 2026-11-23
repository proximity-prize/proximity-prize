/- Modified from public PR657. Expanded the packed receipt notation. -/
import ProximityPrize.SubmissionLower.Compact50Cover
import ProximityPrize.SubmissionLower.Compact54FastPrice

set_option Elab.async false
namespace Compact54Packed
open Compact50Cover (Tile PaidBatch tilesOf checks apply_batches windowTiles checks_window checks_join)
open Compact54FastPrice (paysFast fastBatch)
open K1_13 (Shape)
open K1_13_8 (Valid)
open Final50PriceCaps (Band start)
open Final50PriceTableBase (Covered)

/-- The low bits store tag, width, index and order. The payload stores a point run,
the two rectangle spans, or the shared rate and its amount. -/
def decode (word : ℕ) : List Tile :=
  let z:=word / 4
  let b:=z % 256
  let j:=z / 256 % 64
  let l:=z / 16384 % 256
  let q:=z / 4194304
  match word % 4 with
  | 0 => (List.range (q+1)).map fun i => .point b (j+i) l
  | 1 => [.rectangle b j (b+q%256) (j+q/256) l]
  | 3 => [.mixrect b j (b+q%256) (j+q/256) l]
  | _ =>
    let pivot:Fin 3:=⟨q / 4 % 4 % 3,Nat.mod_lt _ (by decide)⟩
    let split:=match q / 16 % 16 with | 0 => 1 | 1 => 2 | 2 => 10 | 3 => 24 | 4 => 32 | 5 => 40 | 6 => 48 | 7 => 64 | 8 => 96 | _ => 16
    [.shared b j l ⟨if q%2=1 then .tilted else .ordinary,pivot,split,q/2%2=1,q/256⟩]

def unpack (words:List ℕ):List Tile:=words.flatMap decode


-- The numeric tile words and the proof checks come from the weighted PR657 port.
-- The wrapper expands the original p54 construction without custom syntax.

/-- The printed radix-92 digits are ASCII 33 through 126, without quote or backslash.
A space ends a word. The words are the original numeric tile receipts. -/
private def readDigit (b : Nat) : Nat :=
  Nat.sub b (cond (Nat.blt b 35) 33 (cond (Nat.blt b 93) 34 35))

def readWords (code : String) : List ℕ :=
  let (digit, words) := code.toByteArray.data.toList.foldl
    (fun (state : ℕ × List ℕ) byte =>
      let b := byte.toNat
      if Nat.beq b 32 then (0, state.1 :: state.2)
      else (Nat.add (Nat.mul 92 state.1) (readDigit b), state.2)) (0, [])
  (digit :: words).reverse

def paidWords {k : Band} {t : ℕ} (code : String)
    (ok : paysFast k t (unpack (readWords code)) = true) : PaidBatch k t :=
  fastBatch _ ok

/-- Check a bounded group of the original packed batches. -/
def paidGroup {k : Band} {t : ℕ} (codes : List String)
    (ok : codes.all (fun code => paysFast k t (unpack (readWords code))) = true := by decide +kernel) :
    List (PaidBatch k t) := by
  have paid := (List.all_eq_true (l := codes)
    (p := fun code => paysFast k t (unpack (readWords code)))).mp ok
  exact codes.attach.map fun c => paidWords (k := k) (t := t) c.val (paid c.val c.property)

private def checkWindows (tiles : List Tile) (width : Nat) : Nat → List Nat → Bool
  | _, [] => true
  | first, count :: rest =>
    checks (windowTiles first count tiles) width first count &&
      checkWindows tiles width (first + count) rest

private theorem checks_of_windows (tiles : List Tile) (width first : Nat) (sizes : List Nat)
    (h : checkWindows tiles width first sizes = true) :
    checks tiles width first sizes.sum = true := by
  induction sizes generalizing first with
  | nil => simp [checks]
  | cons count rest ih =>
    rw [checkWindows, Bool.and_eq_true] at h
    exact checks_join (checks_window h.1) (ih _ h.2)

/-- Check disjoint index windows against one list of paid tiles. -/
theorem checkedWindows (tiles : List Tile) (width first : Nat) (sizes : List Nat)
    (h : checkWindows tiles width first sizes = true := by decide +kernel) :
    checks tiles width first sizes.sum = true :=
  checks_of_windows tiles width first sizes h

theorem coverAt {k : Band} {t w j : ℕ} {bs : List (PaidBatch k t)}
    (h:checks (tilesOf bs) w (3*t) (j+1-3*t)=true)
    (a:Shape) (ha:Valid a) (ht:a.t=t) (hb:a.b≤w) (hj:a.j≤j) :
    Covered ((start k).t+t) k a:=by
  have hi:=ha.2.1
  exact apply_batches h a ha ht hb (by omega) (by omega)
end Compact54Packed
