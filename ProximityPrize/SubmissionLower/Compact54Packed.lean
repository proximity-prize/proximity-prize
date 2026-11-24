import ProximityPrize.SubmissionLower.Final50Price
import ProximityPrize.SubmissionLower.KoalaRetainedAssembly
import ProximityPrize.SubmissionLower.KoalaWeightedRate
import ProximityPrize.SubmissionLower.Final50PriceCaps
import ProximityPrize.SubmissionLower.Final50SurfaceLinearFour

-- merged module Final50PriceMonotone
section Merged_Final50PriceMonotone
set_option Elab.async false
section
namespace Final50PriceMonotone
open K1_13 (Shape InBox chart liftedChart mixed32 ceilDiv)
open K1_13_8_2 (Chamber mixed_mono)
theorem box_refl (x : Shape) : InBox x x := ⟨le_rfl, le_rfl, le_rfl⟩
theorem normalize_mono {x y : Shape} (h : InBox x y) :
    InBox x.chamber y.chamber := ⟨max_le_max h.1 h.2.1, h.2.1, h.2.2⟩
theorem normalize_chamber (x : Shape) (h : 3 * x.t ≤ x.j) :
    Chamber x.chamber := ⟨le_max_right _ _, h⟩
theorem plus_mono {x y u v : Shape} (h : InBox x y) (h' : InBox u v) :
    InBox (x.plus u) (y.plus v) :=
  ⟨Nat.add_le_add h.1 h'.1, Nat.add_le_add h.2.1 h'.2.1, Nat.add_le_add h.2.2 h'.2.2⟩
theorem plus_chamber {x y : Shape} (hx : Chamber x) (hy : Chamber y) :
    Chamber (x.plus y) := by
  exact ⟨Nat.add_le_add hx.1 hy.1, by simp only [Shape.plus, Nat.mul_add]; exact Nat.add_le_add hx.2 hy.2⟩
theorem scale_mono {x y : Shape} (h : InBox x y) (k : ℕ) :
    InBox (x.scale k) (y.scale k) :=
  ⟨Nat.mul_le_mul_left k h.1, Nat.mul_le_mul_left k h.2.1, Nat.mul_le_mul_left k h.2.2⟩
theorem scale_chamber {x : Shape} (hx : Chamber x) (k : ℕ) :
    Chamber (x.scale k) :=
  ⟨Nat.mul_le_mul_left k hx.1, by simpa [Shape.scale, Nat.mul_left_comm 3 k] using Nat.mul_le_mul_left k hx.2⟩
private theorem min_fits_index (a i : ℕ) : 3 * min a (i / 3) ≤ i := by
  have h := min_le_right a (i / 3)
  omega
theorem chart_chamber (L : ℕ) (x : Shape) : Chamber (chart L x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩
private theorem lifted_chamber (L : ℕ) (x : Shape) : Chamber (liftedChart L x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩
theorem chart_mono (L : ℕ) {x y : Shape} (h : InBox x y) :
    InBox (chart L x) (chart L y) := by
  obtain ⟨hb, hj, ht⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [chart] <;> gcongr
private theorem lifted_mono (L : ℕ) {x y : Shape} (h : InBox x y) :
    InBox (liftedChart L x) (liftedChart L y) := by
  obtain ⟨hb, hj, ht⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [liftedChart] <;> gcongr
private def graphShape (p : Shape) : Shape :=
  ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
private theorem graph_chamber (x : Shape) : Chamber (graphShape x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩
private theorem graph_mono {x y : Shape} (h : InBox x y) :
    InBox (graphShape x) (graphShape y) := by
  obtain ⟨hb, hj, ht⟩ := h
  refine ⟨?_, ?_, ?_⟩ <;> dsimp [graphShape] <;> gcongr
private theorem surface_mono {p p' q : Shape} (hp : InBox p p') (hp' : Chamber p') (hq : Chamber q) :
    Final50Price.surfaceNumerator32 p q ≤ Final50Price.surfaceNumerator32 p' q := by
  let L := Final50Price.taylorLength
  have hchart : mixed32 p q (chart (L+1) p) (chart (L+2) p) ≤
      mixed32 p' q (chart (L+1) p') (chart (L+2) p') :=
    mixed_mono hp (box_refl q) (chart_mono _ hp) (chart_mono _ hp) hp' hq
      (chart_chamber _ _) hq (chart_chamber _ _) (chart_chamber _ _)
  have hlift : mixed32 p q (liftedChart (L+1) p) (liftedChart (L+2) p) ≤
      mixed32 p' q (liftedChart (L+1) p') (liftedChart (L+2) p') :=
    mixed_mono hp (box_refl q) (lifted_mono _ hp) (lifted_mono _ hp) hp' hq
      (lifted_chamber _ _) hq (lifted_chamber _ _) (lifted_chamber _ _)
  have hgraph (M : ℕ) :
      mixed32 p q (graphShape p) (liftedChart M p) ≤ mixed32 p' q (graphShape p') (liftedChart M p') :=
    mixed_mono hp (box_refl q) (graph_mono hp) (lifted_mono _ hp) hp' hq
      (graph_chamber _) hq (graph_chamber _) (lifted_chamber _ _)
  exact min_le_min hchart (Nat.add_le_add (Nat.add_le_add hlift (Nat.mul_le_mul_left _ (hgraph _)))
    (Nat.mul_le_mul_left _ (hgraph _)))
theorem ceil_mono {a b : ℕ} (h : a ≤ b) (l : ℕ) : ceilDiv a l ≤ ceilDiv b l :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h l) 1)
theorem physical_mono {x y : Shape} (h : InBox x y) (hx : 3 * x.t ≤ x.j)
    (hy : 3 * y.t ≤ y.j) (l : ℕ) : Final50Price.physicalPriceOld x l ≤ Final50Price.physicalPriceOld y l := by
  let p := x.chamber
  let p' := y.chamber
  let q : Shape := Final50Price.primaryBox
  let L := Final50Price.taylorLength
  let A := q.plus (p.scale 4)
  let A' := q.plus (p'.scale 4)
  have hp := normalize_mono h
  have hpc : Chamber p := normalize_chamber x hx
  have hp'c : Chamber p' := normalize_chamber y hy
  have hqc : Chamber q := ⟨by decide, le_rfl⟩
  have ha : InBox A A' := plus_mono (box_refl q) (scale_mono hp 4)
  have hac : Chamber A := plus_chamber hqc (scale_chamber hpc 4)
  have ha'c : Chamber A' := plus_chamber hqc (scale_chamber hp'c 4)
  have hs := surface_mono hp hp'c hqc
  have hb := (chart_mono (L+1) hp).1
  have hmain : (Final50Price.errors + 2*Final50Price.incidenceGap) * x.b * q.b * (chart (L+1) p).b ≤
      (Final50Price.errors + 2*Final50Price.incidenceGap) * y.b * q.b * (chart (L+1) p').b := by
    have := h.1
    gcongr
  have hcurve := mixed_mono hp (box_refl q) ha (chart_mono L hp) hp'c hqc ha'c hqc hac (chart_chamber L p)
  have hpoint := mixed_mono hp (box_refl q) ha hp hp'c hqc ha'c hqc hac hpc
  have hcurve' := mixed_mono hp hp hp (chart_mono L hp) hp'c hp'c hp'c hpc hpc (chart_chamber L p)
  have hpoint' := mixed_mono hp hp hp hp hp'c hp'c hp'c hpc hpc hpc
  have htc := Nat.mul_le_mul_left 2 h.2.2
  have hc := Nat.add_le_add hcurve (Nat.mul_le_mul htc hcurve')
  have hn := Nat.add_le_add hpoint (Nat.mul_le_mul htc hpoint')
  have hgeom := Nat.add_le_add (Nat.mul_le_mul_left Final50Price.errors hc) (Nat.mul_le_mul_left (2*Final50Price.incidenceGap) hn)
  have hraw := Nat.mul_le_mul_right q.b (Nat.mul_le_mul_left (2*Final50Price.physicalDegree) h.1)
  exact Nat.add_le_add
    (Nat.add_le_add (ceil_mono (Nat.add_le_add (ceil_mono hs _) (ceil_mono hmain _)) l) hraw)
    (ceil_mono hgeom _)
end Final50PriceMonotone
end

namespace Final50PriceMonotone
open K1_13 (Shape)
open Final50Price (physicalPrice physicalPriceOld physicalPriceTilted physicalPriceActive physicalPriceWith)

theorem physicalPrice_le_old (x : Shape) (l K : ℕ) : physicalPrice x l K ≤ physicalPriceOld x l := by
  unfold physicalPrice
  split
  · split
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact min_le_left _ _
  · exact le_rfl

private theorem with_anti (a : Shape) (s : ℕ) {l u : ℕ} (hl : 0 < l) (h : l ≤ u) :
    physicalPriceWith a u s ≤ physicalPriceWith a l s := by
  unfold physicalPriceWith
  exact Nat.add_le_add_right
    (Nat.add_le_add_right (K1_13_8.ceilDiv_anti _ hl h) _) _

theorem physicalPrice_anti (a : Shape) (K : ℕ) {l u : ℕ} (hl : 0 < l) (h : l ≤ u) :
    physicalPrice a u K ≤ physicalPrice a l K := by
  have hold : physicalPriceOld a u ≤ physicalPriceOld a l := by
    unfold physicalPriceOld
    exact Nat.add_le_add_right
      (Nat.add_le_add_right (K1_13_8.ceilDiv_anti _ hl h) _) _
  have hnew : physicalPriceTilted a u ≤ physicalPriceTilted a l := with_anti a _ hl h
  have hactive : physicalPriceActive a u K ≤ physicalPriceActive a l K := with_anti a _ hl h
  unfold physicalPrice
  split
  · split
    · exact min_le_min (min_le_min hold hnew) hactive
    · exact min_le_min hold hnew
  · exact hold
end Final50PriceMonotone

end Merged_Final50PriceMonotone

-- merged module Final50PriceTableBase
section Merged_Final50PriceTableBase

set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Final50PriceTableBase
open K1_13 (Shape InBox)
open KoalaRetainedCut (contractedPrice)
open Final50Price (physicalPrice physicalPriceOld)
open Final50PriceCaps (Band order allowance activeCap start)
open Final50PriceMonotone (physicalPrice_le_old physicalPrice_anti physical_mono)

theorem contracted_le (x h : Shape) (l K : ℕ) :
    contractedPrice x h l K ≤ physicalPrice x l K := by
  dsimp only [contractedPrice]
  split
  · refine (min_le_left _ _).trans ?_
    split
    · exact min_le_left _ _
    · exact le_rfl
  · split
    · exact min_le_left _ _
    · exact le_rfl

abbrev OldReceipt (top : ℕ) (k : Band) (bl jl bh jh t l : ℕ) : Prop :=
  0 < l ∧ l ≤ order k ⟨bl,jl,0⟩ ∧ physicalPriceOld ⟨bh,jh,t⟩ l ≤ allowance top k bl jl t

abbrev PointReceipt (top : ℕ) (k : Band) (b j t l : ℕ) : Prop :=
  0 < l ∧ l ≤ order k ⟨b,j,t⟩ ∧ contractedPrice ⟨b,j,t⟩ (start k) l (activeCap k) ≤ allowance top k b j t


open Final50SharedPrice (Rate)
open KoalaWeightedRate (Allowed)

def Covered (top : ℕ) (k : Band) (a : Shape) : Prop :=
  (∃ l, 0 < l ∧ l ≤ order k a ∧ contractedPrice a (start k) l (activeCap k) ≤ allowance top k a.b a.j a.t) ∨
  ∃ u l, k = .empty ∧ 0 < l ∧ l ≤ order k a ∧ Allowed a u ∧
    Final50SharedPrice.price a l (activeCap k) u ≤ allowance top k a.b a.j a.t

abbrev SharedReceipt (t b j l : ℕ) (u : Rate) : Prop :=
  0 < l ∧ l ≤ order .empty ⟨b,j,t⟩ ∧ Allowed ⟨b,j,t⟩ u ∧
    Final50SharedPrice.price ⟨b,j,t⟩ l (activeCap .empty) u ≤ allowance t .empty b j t




end Final50PriceTableBase

end Merged_Final50PriceTableBase

-- merged module Compact50Cover
section Merged_Compact50Cover
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace Compact50Cover
open K1_13 (Shape)
open K1_13_8 (Valid)
open Final50PriceCaps (Band start)
open Final50SharedPrice (Rate)
open Final50PriceTableBase (Covered OldReceipt PointReceipt SharedReceipt
    )
inductive Tile where
  | rectangle (widthLow indexLow widthHigh indexHigh order : ℕ)
  | point (width index order : ℕ)
  | shared (width index order : ℕ) (rate : Rate)
structure Rectangle where
  widthLow : ℕ
  indexLow : ℕ
  widthHigh : ℕ
  indexHigh : ℕ
def Tile.bounds : Tile → Rectangle
  | .rectangle b j B J _ => ⟨b,j,B,J⟩
  | .point b j _ | .shared b j _ _ => ⟨b,j,b,j⟩
def Tile.Paid (k : Band) (t : ℕ) : Tile → Prop
  | .rectangle b j B J l => OldReceipt ((start k).t+t) k b j B J t l
  | .point b j l => PointReceipt ((start k).t+t) k b j t l
  | .shared b j l u => k = .empty ∧ SharedReceipt t b j l u
instance (k : Band) (t : ℕ) (tile : Tile) : Decidable (tile.Paid k t) := by
  cases tile <;> unfold Tile.Paid <;> infer_instance
def pays (k : Band) (t : ℕ) (tiles : List Tile) : Bool :=
  tiles.all (fun tile => decide (tile.Paid k t))
theorem pays_append (k : Band) (t : ℕ) (a b : List Tile) :
    pays k t (a ++ b) = (pays k t a && pays k t b) := by
  simp [pays, List.all_append]
abbrev PaidBatch (k : Band) (t : ℕ) := {tiles : List Tile // pays k t tiles = true}
def tilesOf {k : Band} {t : ℕ} (batches : List (PaidBatch k t)) : List Tile :=
  batches.flatMap Subtype.val
private theorem batches_pay {k : Band} {t : ℕ} (batches : List (PaidBatch k t)) :
    pays k t (tilesOf batches) = true := by
  induction batches with
  | nil => rfl
  | cons head tail ih =>
    change pays k t (head.val ++ tilesOf tail) = true
    rw [pays_append, head.property, ih]
    rfl
def InRectangle (r : Rectangle) (width index : ℕ) : Prop :=
  r.widthLow ≤ width ∧ width ≤ r.widthHigh ∧ r.indexLow ≤ index ∧ index ≤ r.indexHigh
def step (index firstMissing : ℕ) (tile : Tile) : ℕ :=
  let r := tile.bounds
  if r.indexLow ≤ index ∧ index ≤ r.indexHigh ∧ r.widthLow ≤ firstMissing then
    max firstMissing (r.widthHigh+1)
  else firstMissing
private theorem step_cover {tile : Tile} {j first b : ℕ}
    (hFirst : first ≤ b) (h : b < step j first tile) : InRectangle tile.bounds b j := by
  dsimp only [step] at h
  split at h
  · rename_i hit
    obtain ⟨hj,hJ,hb⟩ := hit
    exact ⟨hb.trans hFirst, by omega, hj, hJ⟩
  · omega
theorem fold_cover (tiles : List Tile) (j first b : ℕ)
    (hFirst : first ≤ b) (h : b < tiles.foldl (step j) first) :
    ∃ tile ∈ tiles, InRectangle tile.bounds b j := by
  induction tiles generalizing first with
  | nil => simp only [List.foldl_nil] at h; omega
  | cons tile rest ih =>
    rw [List.foldl_cons] at h
    by_cases hb : step j first tile ≤ b
    · obtain ⟨r,hr,hrb⟩ := ih _ hb h
      exact ⟨r,List.mem_cons_of_mem _ hr,hrb⟩
    · exact ⟨tile,List.mem_cons_self,step_cover hFirst (by omega)⟩
def checks (tiles : List Tile) (maxWidth first count : ℕ) : Bool :=
  (List.range count).all fun i =>
    let j := first+i
    decide (maxWidth < tiles.foldl (step j) ((j+2)/3))
theorem checks_join {tiles : List Tile} {maxWidth first left right : ℕ}
    (hl : checks tiles maxWidth first left = true)
    (hr : checks tiles maxWidth (first+left) right = true) :
    checks tiles maxWidth first (left+right) = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hn := List.mem_range.mp hi
  by_cases h : i < left
  · exact (List.all_eq_true.mp hl) i (List.mem_range.mpr h)
  · have he : first + i = first + left + (i-left) := by omega
    change decide (maxWidth < tiles.foldl (step (first+i)) ((first+i+2)/3)) = true
    rw [he]
    exact (List.all_eq_true.mp hr) (i-left) (List.mem_range.mpr (by omega))
end Compact50Cover

end Merged_Compact50Cover

-- merged module Compact54Packed
section Merged_Compact54Packed

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

end Merged_Compact54Packed
