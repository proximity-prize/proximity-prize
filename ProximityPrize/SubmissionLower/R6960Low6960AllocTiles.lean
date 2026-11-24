import ProximityPrize.SubmissionLower.R6960Low6960FastPrice
import ProximityPrize.SubmissionLower.Compact54Packed

set_option Elab.async false
set_option maxHeartbeats 2800000
set_option maxRecDepth 18000

namespace Low6960Allocation
open K1_13 (Shape InBox)
open K1_13_8 (Valid)
open Compact50Cover (Tile checks)
open Low6960Prices (physicalPrice physicalPriceOld tiltedFits activeFitsPrice)
open Low6960RetainedCut (contractedPrice)
open Low6960WeightedRate (Allowed)
open Low6960Monotone (physicalPrice_le_old physical_mono)
open Compact50Cover (InRectangle fold_cover step)

def actualRate (u : Final50SharedPrice.Rate) : Low6960SharedPrice.Rate :=
  ⟨(match u.kind with | .ordinary=>.ordinary | .tilted=>.tilted),
    u.pivot,u.split,u.topIndex,u.amount⟩

def Covered {k : Band} (cells : List (MassCell k)) (x : Shape) : Prop :=
  (∃ l,0<l ∧ l≤order cells x ∧ contractedPrice x (start k) l 165 ≤
    allowance k ((start k).t+x.t) x.b x.j x.t) ∨
  ∃ u l,k=empty ∧ 0<l ∧ l≤order cells x ∧ Allowed x u ∧
    Low6960SharedPrice.price x l 165 u ≤ allowance k x.t x.b x.j x.t

/-- Tag 3 encodes a four-surface rectangle or a tilted width interval. -/
def decode (word : ℕ) : List Tile :=
  if word % 4 = 3 then
    let z := word / 4
    let b := z % 256
    let j := z / 256 % 64
    let l := z / 16384 % 256
    let q := z / 4194304
    let marker := if 65536≤q then 512 else 256
    [.rectangle b j (b+q%256) (j+q%65536/256) (marker+l)]
  else Compact54Packed.decode word

def unpack (words : List ℕ) : List Tile := words.flatMap decode

def Paid {k : Band} (cells : List (MassCell k)) (t : ℕ) : Tile→Prop
  | .rectangle b j B J l =>
      if 512≤l then J=j ∧ Low6960Rectangle.PaidTilted cells t b j B (l-512)
      else if 256≤l then Low6960Rectangle.PaidFour cells t b j B J (l-256)
      else 0<l ∧ l≤order cells ⟨b,j,0⟩ ∧
        physicalPriceOld ⟨B,J,t⟩ l ≤ allowance k ((start k).t+t) b j t
  | .point b j l => 0<l ∧ l≤order cells ⟨b,j,t⟩ ∧
      contractedPrice ⟨b,j,t⟩ (start k) l 165 ≤ allowance k ((start k).t+t) b j t
  | .shared b j l u => k=empty ∧ 0<l ∧ l≤order cells ⟨b,j,t⟩ ∧
      Allowed ⟨b,j,t⟩ (actualRate u) ∧
      Low6960SharedPrice.price ⟨b,j,t⟩ l 165 (actualRate u) ≤ allowance k t b j t

instance {k : Band} (cells : List (MassCell k)) (t : ℕ) (tile : Tile) :
    Decidable (Paid cells t tile) := by cases tile <;> unfold Paid <;> infer_instance

/-- `Paid` on the closed price forms; the kernel checks receipts against this copy. -/
def PaidF {k : Band} (cells : List (MassCell k)) (t : ℕ) : Tile→Prop
  | .rectangle b j B J l =>
      if 512≤l then J=j ∧ Low6960FastPrice.PaidTiltedF cells t b j B (l-512)
      else if 256≤l then Low6960FastPrice.PaidFourF cells t b j B J (l-256)
      else 0<l ∧ l≤order cells ⟨b,j,0⟩ ∧
        Low6960FastPrice.physicalPriceOldF ⟨B,J,t⟩ l ≤ allowance k ((start k).t+t) b j t
  | .point b j l => 0<l ∧ l≤order cells ⟨b,j,t⟩ ∧
      Low6960FastPrice.contractedPriceF ⟨b,j,t⟩ (start k) l 165 ≤ allowance k ((start k).t+t) b j t
  | .shared b j l u => k=empty ∧ 0<l ∧ l≤order cells ⟨b,j,t⟩ ∧
      Low6960FastPrice.AllowedF ⟨b,j,t⟩ (actualRate u) ∧
      Low6960FastPrice.priceF ⟨b,j,t⟩ l 165 (actualRate u) ≤ allowance k t b j t

instance {k : Band} (cells : List (MassCell k)) (t : ℕ) (tile : Tile) :
    Decidable (PaidF cells t tile) := by cases tile <;> unfold PaidF <;> infer_instance

theorem paidF_iff {k : Band} (cells : List (MassCell k)) (t : ℕ) (tile : Tile) :
    PaidF cells t tile ↔ Paid cells t tile := by
  cases tile <;> simp only [PaidF, Paid, Low6960FastPrice.paidTiltedF_iff,
    Low6960FastPrice.paidFourF_iff, Low6960FastPrice.physicalPriceOldF_eq,
    Low6960FastPrice.contractedPriceF_eq, Low6960FastPrice.allowedF_iff, Low6960FastPrice.priceF_eq]

def pays {k : Band} (cells : List (MassCell k)) (t : ℕ) (tiles : List Tile) : Bool :=
  tiles.all (fun tile=>decide (PaidF cells t tile))

abbrev PaidBatch {k : Band} (cells : List (MassCell k)) (t : ℕ) :=
  {tiles : List Tile // pays cells t tiles=true}

def tilesOf {k : Band} {cells : List (MassCell k)} {t : ℕ} (batches : List (PaidBatch cells t)) : List Tile :=
  batches.flatMap Subtype.val

private theorem batches_pay {k : Band} {cells : List (MassCell k)} {t : ℕ} (batches : List (PaidBatch cells t)) :
    pays cells t (tilesOf batches)=true := by
  induction batches with
  | nil => rfl
  | cons head tail ih =>
    change pays cells t (head.val ++ tilesOf tail)=true
    rw [show pays cells t (head.val ++ tilesOf tail)=
      (pays cells t head.val && pays cells t (tilesOf tail)) by simp [pays,List.all_append]]
    rw [head.property,ih]
    rfl

private theorem contracted_le (x h : Shape) (l : ℕ) :
    contractedPrice x h l 165 ≤ physicalPrice x l 165 := by
  dsimp only [contractedPrice]
  split
  · refine (min_le_left _ _).trans ?_
    split
    · exact min_le_left _ _
    · exact le_rfl
  · split
    · exact min_le_left _ _
    · exact le_rfl

private theorem tile_cover {tile : Tile} {k : Band} {cells : List (MassCell k)} {t : ℕ} {a : Shape}
    (paid : Paid cells t tile) (bounds : InRectangle tile.bounds a.b a.j)
    (ht : a.t=t) (hi : 3*a.t≤a.j) : Covered cells a := by
  rcases tile with ⟨b,j,B,J,l⟩ | ⟨b,j,l⟩ | ⟨b,j,l,u⟩
  · obtain ⟨hb,hB,hj,hJ⟩ := bounds
    by_cases tilted : 512 ≤ l
    · have receipt : J=j ∧ Low6960Rectangle.PaidTilted cells t b j B (l-512) := by
        simpa only [Paid,ite_eq_left tilted] using paid
      have hja : a.j≤J := hJ
      exact Or.inl (Low6960Rectangle.tilted receipt.2 hb hB
        (Nat.le_antisymm (hja.trans_eq receipt.1) hj) ht)
    by_cases h : 256 ≤ l
    · have receipt : Low6960Rectangle.PaidFour cells t b j B J (l-256) := by
        simpa only [Paid, ite_eq_right tilted, ite_eq_left h] using paid
      exact Or.inl (Low6960Rectangle.four receipt hb hj hB hJ ht hi)
    have receipt : 0<l ∧ l≤order cells ⟨b,j,0⟩ ∧
        physicalPriceOld ⟨B,J,t⟩ l ≤ allowance k ((start k).t+t) b j t := by
      simpa only [Paid, ite_eq_right tilted, ite_eq_right h] using paid
    obtain ⟨lp,lo,fee⟩ := receipt
    have ord := lo.trans (order_mono cells hb hj)
    have box : InBox a ⟨B,J,t⟩ := ⟨hB,hJ,ht.le⟩
    have charge : allowance k ((start k).t+t) b j t≤allowance k ((start k).t+t) a.b a.j a.t :=
      Nat.div_le_div_right (Nat.mul_le_mul_left _ (weight_mono k hb hj ht.ge))
    exact Or.inl ⟨l,lp,ord,
      ((contracted_le _ _ _).trans (physicalPrice_le_old _ _ _)).trans
        ((physical_mono box hi (ht ▸ hi.trans hJ) l).trans (fee.trans (by simpa only [ht] using charge)))⟩
  · obtain ⟨hb,hB,hj,hJ⟩ := bounds
    have beq : a.b=b := Nat.le_antisymm hB hb
    have jeq : a.j=j := Nat.le_antisymm hJ hj
    have eq : a=⟨b,j,t⟩ := by
      cases a
      simp_all only [Shape.mk.injEq, and_self]
    rw [eq]
    exact Or.inl ⟨l,paid⟩
  · obtain ⟨hb,hB,hj,hJ⟩ := bounds
    have beq : a.b=b := Nat.le_antisymm hB hb
    have jeq : a.j=j := Nat.le_antisymm hJ hj
    have eq : a=⟨b,j,t⟩ := by
      cases a
      simp_all only [Shape.mk.injEq, and_self]
    rw [eq]
    exact Or.inr ⟨actualRate u,l,paid⟩

theorem cover_at {k : Band} {cells : List (MassCell k)} {t maxWidth maxIndex : ℕ}
    {batches : List (PaidBatch cells t)}
    (hcover : Compact50Cover.checks (tilesOf batches) maxWidth (3*t) (maxIndex+1-3*t) = true)
    (a : Shape) (ha : Valid a) (ht : a.t=t) (hb : a.b≤maxWidth) (hj : a.j≤maxIndex) :
    Covered cells a := by
  let i := a.j-3*t
  have hleft : 3*t≤a.j := ht ▸ ha.2.1
  have hi : i∈List.range (maxIndex+1-3*t) := List.mem_range.mpr (by dsimp [i]; omega)
  have eq : 3*t+i=a.j := by dsimp [i]; omega
  have row := List.all_eq_true.mp hcover i hi
  change decide (maxWidth < (tilesOf batches).foldl (step (3*t+i)) ((3*t+i+2)/3))=true at row
  rw [eq] at row
  obtain ⟨tile,mem,bounds⟩ := fold_cover (tilesOf batches) a.j ((a.j+2)/3) a.b
    (by have := ha.2.2; omega) (hb.trans_lt (of_decide_eq_true row))
  have proof := (List.all_eq_true.mp (batches_pay batches)) tile mem
  exact tile_cover ((paidF_iff cells t tile).mp (of_decide_eq_true proof)) bounds ht ha.2.1

structure Receipt (k : Band) where
  orders : List (MassCell k)
  covers : ∀ a : Shape,Valid a → InBox ((start k).plus a) (Low6960Prices.fullCap 14) → Covered orders a

#print axioms cover_at
end Low6960Allocation
