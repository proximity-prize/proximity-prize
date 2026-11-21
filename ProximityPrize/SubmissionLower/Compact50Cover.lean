import ProximityPrize.SubmissionLower.Final50PriceTableBase

set_option Elab.async false
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
  rcases tile with ⟨b,j,B,J,l⟩ | ⟨b,j,l⟩ | ⟨b,j,l,u⟩
  · exact coveredRectangle paid bounds.1 bounds.2.2.1 bounds.2.1 bounds.2.2.2 ht hi
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
