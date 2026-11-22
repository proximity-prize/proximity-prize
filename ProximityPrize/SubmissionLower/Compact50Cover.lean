import ProximityPrize.SubmissionLower.Final50PriceTableBase

-- merged module Final54MixReceipt
section Merged_Final54MixReceipt
set_option maxHeartbeats 4000000

/- A rectangle receipt for the four-surface contracted price: the cut price at the top corner
with the residual hull `q` of the band start, which is the same for every shape of the band. -/
namespace Final54MixReceipt
open K1_13 (Shape InBox ceilDiv)
open K1_13_8_2 (Chamber mixed_mono)
open KoalaRetainedCut (contractedPrice cutPrice fourSurface chamberHull residualBox hull_valid)
open Final50Price (physicalPrice physicalPriceOld)
open Final50PriceCaps (Band order allowance activeCap start)
open Final50PriceTableBase (Covered)
open private chargedPrice from ProximityPrize.SubmissionLower.Final50GeometryCut
open private Final50PriceMonotone.box_refl Final50PriceMonotone.normalize_mono
  Final50PriceMonotone.normalize_chamber Final50PriceMonotone.plus_mono
  Final50PriceMonotone.plus_chamber Final50PriceMonotone.scale_mono
  Final50PriceMonotone.scale_chamber Final50PriceMonotone.chart_mono
  Final50PriceMonotone.chart_chamber
  from ProximityPrize.SubmissionLower.Final50PriceMonotone
open Final50PriceMonotone (box_refl normalize_mono normalize_chamber plus_mono plus_chamber scale_mono scale_chamber chart_mono chart_chamber)

/-- `physicalPriceOld` with the mixed surface numerator left free. -/
def oldWith (x : Shape) (l S : ℕ) : ℕ :=
  let p := x.chamber
  let q := Final50Price.primaryBox
  let h := K1_13.chart Final50Price.taylorLength p
  let numerator := ceilDiv S 32 +
    ceilDiv ((Final50Price.errors + 2 * Final50Price.incidenceGap) * x.b * q.b *
      (K1_13.chart (Final50Price.taylorLength + 1) p).b) Final50Price.incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := K1_13.mixed32 p q auxBox h + 2 * x.t * K1_13.mixed32 p p p h
  let points := K1_13.mixed32 p q auxBox p + 2 * x.t * K1_13.mixed32 p p p p
  ceilDiv numerator l + 2 * Final50Price.physicalDegree * x.b * q.b +
    ceilDiv (Final50Price.errors * curves + 2 * Final50Price.incidenceGap * points)
      (32 * Final50Price.incidenceGap)

theorem cut_eq (x : Shape) (l S : ℕ) : cutPrice x l 32 S = oldWith x l S := by
  simp only [cutPrice, oldWith, chargedPrice, Final50GeometryCut.auxCurves32,
    Final50GeometryCut.auxPoints32, Final50GeometryCut.membershipDegree, Nat.mul_assoc]
  rfl

theorem oldWith_mono {x y : Shape} (h : InBox x y) (hx : 3 * x.t ≤ x.j)
    (hy : 3 * y.t ≤ y.j) (l : ℕ) {S S' : ℕ} (hS : S ≤ S') : oldWith x l S ≤ oldWith y l S' := by
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
  have hb := (chart_mono (L+1) hp).1
  have hmain : (Final50Price.errors + 2*Final50Price.incidenceGap) * x.b * q.b * (K1_13.chart (L+1) p).b ≤
      (Final50Price.errors + 2*Final50Price.incidenceGap) * y.b * q.b * (K1_13.chart (L+1) p').b := by
    have := h.1
    gcongr
  have hcurve := mixed_mono hp (box_refl q) ha (chart_mono L hp) hp'c hqc ha'c hqc hac (chart_chamber L p)
  have hpoint := mixed_mono hp (box_refl q) ha hp hp'c hqc ha'c hqc hac hpc
  have hcurve' := mixed_mono hp hp hp (chart_mono L hp) hp'c hp'c hp'c hpc hpc (chart_chamber L p)
  have hpoint' := mixed_mono hp hp hp hp hp'c hp'c hp'c hpc hpc hpc
  have htc := Nat.mul_le_mul_left 2 h.2.2
  have hc := Nat.add_le_add hcurve (Nat.mul_le_mul htc hcurve')
  have hn := Nat.add_le_add hpoint (Nat.mul_le_mul htc hpoint')
  have hgeom := Nat.add_le_add (Nat.mul_le_mul_left Final50Price.errors hc)
    (Nat.mul_le_mul_left (2*Final50Price.incidenceGap) hn)
  have hraw := Nat.mul_le_mul_right q.b (Nat.mul_le_mul_left (2*Final50Price.physicalDegree) h.1)
  exact Nat.add_le_add
    (Nat.add_le_add (Final50PriceMonotone.ceil_mono (Nat.add_le_add
      (Final50PriceMonotone.ceil_mono hS _) (Final50PriceMonotone.ceil_mono hmain _)) l) hraw)
    (Final50PriceMonotone.ceil_mono hgeom _)

/-- The residual hull of the band start at order `l`. -/
abbrev hullOf (k : Band) (l : ℕ) : Shape := chamberHull (residualBox (start k) l)

abbrev MixReceipt (top : ℕ) (k : Band) (bl jl bh jh t l : ℕ) : Prop :=
  0 < l ∧ l ≤ order k ⟨bl,jl,0⟩ ∧ 0 < (hullOf k l).t ∧
    cutPrice ⟨bh,jh,t⟩ l 32 (fourSurface (Shape.chamber ⟨bh,jh,t⟩) (hullOf k l)) ≤
      allowance top k bl jl t

theorem mixRectangle {top : ℕ} {k : Band} {a : Shape} {bl jl bh jh t l : ℕ}
    (h : MixReceipt top k bl jl bh jh t l)
    (hb : bl ≤ a.b) (hj : jl ≤ a.j) (hb' : a.b ≤ bh) (hj' : a.j ≤ jh)
    (ht : a.t = t) (ha : 3 * a.t ≤ a.j) :
    (∃ l, 0 < l ∧ l ≤ order k a ∧ contractedPrice a (start k) l (activeCap k) ≤ allowance top k a.b a.j a.t) := by
  obtain ⟨hl, hlo, hq, hbill⟩ := h
  have hu : l ≤ order k a := hlo.trans (Final50PriceCaps.order_mono k hb hj)
  have hi : 3*t ≤ jh := by omega
  have hbox : InBox a ⟨bh,jh,t⟩ := ⟨hb', hj', ht.le⟩
  have hallow : allowance top k bl jl t ≤ allowance top k a.b a.j a.t :=
    Nat.div_le_div_right (Nat.mul_le_mul_left _ (Final50PriceCaps.weight_mono k hb hj ht.ge))
  refine ⟨l, hl, hu, ?_⟩
  have hqc : Chamber (hullOf k l) := by
    have := hull_valid (residualBox (start k) l)
    exact ⟨this.1, this.2.1⟩
  have hp := normalize_mono hbox
  have hpc' : Chamber (Shape.chamber ⟨bh,jh,t⟩) := normalize_chamber _ hi
  have hsurf : fourSurface a.chamber (hullOf k l) ≤
      fourSurface (Shape.chamber ⟨bh,jh,t⟩) (hullOf k l) :=
    mixed_mono hp (box_refl _) (chart_mono _ hp) (chart_mono _ hp) hpc' hqc
      (chart_chamber _ _) hqc (chart_chamber _ _) (chart_chamber _ _)
  have hcut : cutPrice a l 32 (fourSurface a.chamber (hullOf k l)) ≤
      cutPrice ⟨bh,jh,t⟩ l 32 (fourSurface (Shape.chamber ⟨bh,jh,t⟩) (hullOf k l)) := by
    rw [cut_eq, cut_eq]
    exact oldWith_mono hbox ha hi l hsurf
  have hc : contractedPrice a (start k) l (activeCap k) ≤ cutPrice a l 32 (fourSurface a.chamber (hullOf k l)) := by
    unfold contractedPrice
    dsimp only
    rw [if_pos hq]
    split
    · exact (min_le_left _ _).trans (min_le_right _ _)
    · exact min_le_right _ _
  exact hc.trans (hcut.trans (hbill.trans hallow))

end Final54MixReceipt
end Merged_Final54MixReceipt

set_option maxHeartbeats 1000000

namespace Compact50Cover
open K1_13 (Shape)
open K1_13_8 (Valid)
open Final50PriceCaps (Band start)
open Final50SharedPrice (Rate)
open Final50PriceTableBase (Covered OldReceipt PointReceipt SharedReceipt
  coveredRectangle coveredPoint sharedPoint)

/-- A price bound for a rectangle, or an exact price bound for a single shape. -/
inductive Tile where
  | rectangle (widthLow indexLow widthHigh indexHigh order : ℕ)
  | mixrect (widthLow indexLow widthHigh indexHigh order : ℕ)
  | point (width index order : ℕ)
  | shared (width index order : ℕ) (rate : Rate)

structure Rectangle where
  widthLow : ℕ
  indexLow : ℕ
  widthHigh : ℕ
  indexHigh : ℕ

def Tile.bounds : Tile → Rectangle
  | .rectangle b j B J _ | .mixrect b j B J _ => ⟨b,j,B,J⟩
  | .point b j _ | .shared b j _ _ => ⟨b,j,b,j⟩

def Tile.Paid (k : Band) (t : ℕ) : Tile → Prop
  | .rectangle b j B J l => OldReceipt ((start k).t+t) k b j B J t l
  | .mixrect b j B J l => Final54MixReceipt.MixReceipt ((start k).t+t) k b j B J t l
  | .point b j l => PointReceipt ((start k).t+t) k b j t l
  | .shared b j l u => k = .empty ∧ SharedReceipt t b j l u

instance (k : Band) (t : ℕ) (tile : Tile) : Decidable (tile.Paid k t) := by
  cases tile <;> unfold Tile.Paid <;> infer_instance

/-- This numeric check evaluates each price once in its batch. -/
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

private def InRectangle (r : Rectangle) (width index : ℕ) : Prop :=
  r.widthLow ≤ width ∧ width ≤ r.widthHigh ∧ r.indexLow ≤ index ∧ index ≤ r.indexHigh

private theorem tile_covered {tile : Tile} {k : Band} {t : ℕ} {a : Shape}
    (paid : tile.Paid k t) (bounds : InRectangle tile.bounds a.b a.j)
    (ht : a.t = t) (hi : 3 * a.t ≤ a.j) : Covered ((start k).t+t) k a := by
  rcases tile with ⟨b,j,B,J,l⟩ | ⟨b,j,B,J,l⟩ | ⟨b,j,l⟩ | ⟨b,j,l,u⟩
  · exact coveredRectangle paid bounds.1 bounds.2.2.1 bounds.2.1 bounds.2.2.2 ht hi
  · exact Or.inl (Final54MixReceipt.mixRectangle paid bounds.1 bounds.2.2.1 bounds.2.1 bounds.2.2.2 ht hi)
  · obtain ⟨hb,hB,hj,hJ⟩ := bounds
    exact coveredPoint paid (Nat.le_antisymm hB hb) (Nat.le_antisymm hJ hj) ht hi
  · obtain ⟨rfl,h⟩ := paid
    obtain ⟨hb,hB,hj,hJ⟩ := bounds
    simpa only [start, Nat.zero_add] using
      sharedPoint h (Nat.le_antisymm hB hb) (Nat.le_antisymm hJ hj) ht

/-- Extend the covered width prefix when this tile contains its next width. -/
private def step (index firstMissing : ℕ) (tile : Tile) : ℕ :=
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

private theorem fold_cover (tiles : List Tile) (j first b : ℕ)
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

/-- Check index rows in the half-open interval `[first, first + count)`. -/
def checks (tiles : List Tile) (maxWidth first count : ℕ) : Bool :=
  (List.range count).all fun i =>
    let j := first+i
    decide (maxWidth < tiles.foldl (step j) ((j+2)/3))

/-- Join adjacent ranges of checked index rows. -/
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

/-- The row check excludes widths with `j > 3 * b`, as required by `Valid`. -/
theorem apply_checked {tiles : List Tile} {k : Band} {t maxWidth first count : ℕ}
    (hpay : pays k t tiles = true) (hcover : checks tiles maxWidth first count = true)
    (a : Shape) (ha : Valid a) (ht : a.t = t) (hb : a.b ≤ maxWidth)
    (hLeft : first ≤ a.j) (hRight : a.j < first+count) : Covered ((start k).t+t) k a := by
  let i := a.j-first
  have hi : i ∈ List.range count := List.mem_range.mpr (by dsimp [i]; omega)
  have hj : first+i = a.j := by dsimp [i]; omega
  have hrow := (List.all_eq_true.mp hcover) i hi
  change decide (maxWidth < tiles.foldl (step (first+i)) ((first+i+2)/3)) = true at hrow
  rw [hj] at hrow
  obtain ⟨r,hr,hrb⟩ := fold_cover tiles a.j ((a.j+2)/3) a.b
    (by have hi := ha.2.2; omega) (hb.trans_lt (of_decide_eq_true hrow))
  have hp := (List.all_eq_true.mp hpay) r hr
  exact tile_covered (of_decide_eq_true hp) hrb ht ha.2.1

/-- Apply a cover assembled from separately checked price batches. -/
theorem apply_batches {k : Band} {t maxWidth first count : ℕ} {batches : List (PaidBatch k t)}
    (hcover : checks (tilesOf batches) maxWidth first count = true)
    (a : Shape) (ha : Valid a) (ht : a.t = t) (hb : a.b ≤ maxWidth)
    (hLeft : first ≤ a.j) (hRight : a.j < first+count) : Covered ((start k).t+t) k a :=
  apply_checked (batches_pay batches) hcover a ha ht hb hLeft hRight

end Compact50Cover