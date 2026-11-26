import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Fat6966Factors
import ProximityPrize.SubmissionLower.Final50Order
import ProximityPrize.SubmissionLower.Final50PriceCaps
import ProximityPrize.SubmissionLower.Final50SurfaceLinearFive
import ProximityPrize.SubmissionLower.High6966RescueGeometry
import ProximityPrize.SubmissionLower.HighCore82258PrefixGeometry
import ProximityPrize.SubmissionLower.KoalaRetainedAssembly
import ProximityPrize.SubmissionLower.KoalaWeightedRate
import ProximityPrize.SubmissionLower.Low48BentCyclePrice
import ProximityPrize.SubmissionLower.Low48BentSupport
import ProximityPrize.SubmissionLower.Low6966ActiveCycleBound
import ProximityPrize.SubmissionLower.Low6966ActiveCycleCaps
import ProximityPrize.SubmissionLower.Low6966ActiveCycleMixed
import ProximityPrize.SubmissionLower.Low6966GeometryCut
import ProximityPrize.SubmissionLower.R6960Front6960Rank4
import ProximityPrize.SubmissionLower.R6960Low6960Rectangle

section Merged6967_Compact54Packed
set_option Elab.async false






set_option Elab.async false

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

end Merged6967_Compact54Packed

section Merged6967_High6966Rates
set_option Elab.async false



set_option Elab.async false

-- merged module R6960Rescue6966Tariffs
section Merged_R6960Rescue6966Tariffs

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.Rescue6966
open Finset Polynomial ProximityPrize.Benchmark
open P1 (K I node p)
open K1_14 (Shape FX Seeds)
open K1_14_2 (ODE fixedAt RootSeedSection SeedField)
open K1_14_2_2 (ODECaps)
open K1_14_2_4 (taylorPower ordinateBound)
open P1_7_3 (persistentNodes hits_persistent section_bounds regular_chart persistent_taylor)
open P1_7_4 (ODEGuard)
open P1_7_4_3 (mix mix_eq cast_mixed short_cut)
open K1_13 (Geom Row extend embed)
open K1_13_5 (RegularAt)
open K1_13_5_3
open K1_14_2_5 (clear_equation factor_cover)
open K1_14_3_6 (power totalCap topCap)
open scoped Classical BigOperators

private abbrev agreement : ℕ := 179759
private abbrev blockLength : ℕ := 262144
abbrev endpointDegree : ℕ := 133593

structure FixedWord (w : I → K) (U : Finset K) (s : K → (Polynomial K)) (d : ℕ) : Prop where
  distinct : Set.InjOn s (U : Set K)
  degree : ∀ γ ∈ U, (s γ).natDegree ≤ d
  hits : ∀ γ ∈ U, ∃ B : Finset I, agreement ≤ B.card ∧ ∀ i ∈ B, (s γ).eval (node i) = w i
theorem persistent_card_le {w U s d} (hw : FixedWord w U s d) (hU : 1 < U.card) :
    (persistentNodes w U s).card ≤ d := by
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp hU
  let P := s a - s b
  have hp : P ≠ 0 := sub_ne_zero.mpr fun eq => hab (hw.distinct ha hb eq)
  refine (FrobeniusLocator.Strata.root_nodes_card_le node IRSProfile.domain.injective P hp _ ?_).trans
    ((natDegree_sub_le _ _).trans (max_le (hw.degree a ha) (hw.degree b hb)))
  intro i hi
  change ((s a) - (s b)).eval (node i) = 0
  rw [Polynomial.eval_sub, hits_persistent ha hi, hits_persistent hb hi, sub_self]
theorem section_incidence {w U s d} (hw : FixedWord w U s d) (D : ℕ)
    (hsection : ∀ i : I, (∃ γ ∈ U, (s γ).eval (node i) ≠ w i) →
      (U.filter fun γ => (s γ).eval (node i) = w i).card ≤ D) :
    (agreement - (persistentNodes w U s).card) * U.card ≤
      (blockLength - (persistentNodes w U s).card) * D := by
  classical
  let sites := persistentNodes w U s
  let nodes : Finset I := univ \ sites
  let hits (γ : K) := nodes.filter fun i => (s γ).eval (node i) = w i
  let occ (i : I) := U.filter fun γ => (s γ).eval (node i) = w i
  have hhit (γ : K) (hγ : γ ∈ U) : agreement - sites.card ≤ (hits γ).card := by
    obtain ⟨B, hB, hvals⟩ := hw.hits γ hγ
    let good : Finset I := univ.filter fun i => (s γ).eval (node i) = w i
    have hgood : agreement ≤ good.card :=
      hB.trans (card_le_card fun i hi => mem_filter.mpr ⟨mem_univ _, hvals i hi⟩)
    have hZG : sites ⊆ good := fun i hi => mem_filter.mpr ⟨mem_univ _, hits_persistent hγ hi⟩
    have heq : hits γ = good \ sites := by
      ext i
      simp only [hits, nodes, good, mem_filter, mem_sdiff, mem_univ, true_and]
      exact and_comm
    rw [heq, card_sdiff_of_subset hZG]
    exact Nat.sub_le_sub_right hgood _
  have hnodes : nodes.card = blockLength - sites.card := by
    rw [card_sdiff_of_subset (subset_univ sites), card_univ, IRSProfile.card_index]
  calc
    _ = ∑ γ ∈ U, (agreement - sites.card) := by rw [sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ γ ∈ U, (hits γ).card := sum_le_sum hhit
    _ = ∑ i ∈ nodes, (occ i).card := by simp only [hits, occ, card_filter]; rw [sum_comm]
    _ ≤ ∑ _i ∈ nodes, D := by
      apply sum_le_sum
      intro i hi
      apply hsection i
      by_contra! h
      exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _, h⟩)
    _ = _ := by rw [sum_const, smul_eq_mul, hnodes]
private def rho (s : ℕ) : ℚ :=
  ((blockLength - s : ℕ) : ℚ) / ((agreement - s : ℕ) : ℚ)
abbrev density : ℚ := (blockLength : ℚ) / agreement
private theorem weights {s d : ℕ} (hs : s ≤ d) (hd : d < agreement)
    (haux : rho d ≤ density * d) :
    rho s ≤ rho d ∧ rho s * (max 1 (d-s) : ℕ) ≤ density * d := by
  have hAN : agreement ≤ blockLength := by decide
  have hsA := hs.trans_lt hd
  have hdN := hd.le.trans hAN
  have hsN := hs.trans hdN
  have hAs : (0 : ℚ) < (agreement : ℚ) - s := sub_pos.mpr (by exact_mod_cast hsA)
  have hAd : (0 : ℚ) < (agreement : ℚ) - d := sub_pos.mpr (by exact_mod_cast hd)
  have hmain : rho s ≤ rho d := by
    unfold rho
    rw [Nat.cast_sub hsN, Nat.cast_sub hsA.le, Nat.cast_sub hdN, Nat.cast_sub hd.le]
    apply (div_le_div_iff₀ hAs hAd).mpr
    have h := mul_nonneg (sub_nonneg.mpr (show (s : ℚ) ≤ d by exact_mod_cast hs))
      (sub_nonneg.mpr (show (agreement : ℚ) ≤ blockLength by exact_mod_cast hAN))
    nlinarith only [h]
  refine ⟨hmain, ?_⟩
  by_cases heq : s = d
  · subst s
    simpa using haux
  have hpos : 1 ≤ d - s := by omega
  rw [max_eq_right hpos]
  have hden : (0 : ℚ) < (agreement : ℚ) := by exact_mod_cast (by decide : 0 < agreement)
  have hfrac : ((d-s : ℕ) : ℚ) / ((agreement-s : ℕ) : ℚ) ≤ (d : ℚ) / agreement := by
    rw [Nat.cast_sub hs, Nat.cast_sub hsA.le]
    apply (div_le_div_iff₀ hAs hden).mpr
    have h := mul_nonneg (Nat.cast_nonneg s : (0 : ℚ) ≤ s) hAd.le
    nlinarith only [h]
  calc
    _ = ((blockLength-s : ℕ) : ℚ) * (((d-s : ℕ) : ℚ) / ((agreement-s : ℕ) : ℚ)) := by
      unfold rho
      ring
    _ ≤ (blockLength : ℚ) * ((d : ℚ) / agreement) :=
      mul_le_mul (by exact_mod_cast Nat.sub_le blockLength s) hfrac (by positivity) (by positivity)
    _ = density * d := by ring
private theorem rho_at_endpoint {d : ℕ} (hl : 131071 ≤ d) (hh : d ≤ 133593) :
    rho d ≤ density * d := by
  have hdA : d < agreement := hh.trans_lt (by decide)
  have hdN : d ≤ blockLength := hh.trans (by decide)
  have hrho : rho d ≤ 17 := by
    unfold rho
    have hp : (0 : ℚ) < ((agreement - d : ℕ) : ℚ) := by exact_mod_cast Nat.sub_pos_of_lt hdA
    apply (div_le_iff₀ hp).mpr
    rw [Nat.cast_sub hdN, Nat.cast_sub hdA.le]
    change (262144 : ℚ) - d ≤ 17 * ((179759 : ℚ) - d)
    have hQ : (d : ℚ) ≤ 133593 := by exact_mod_cast hh
    linarith only [hQ]
  have hDensity : 1 ≤ density := by
    apply (le_div_iff₀ (show (0 : ℚ) < (agreement : ℚ) by positivity)).mpr
    rw [one_mul]
    exact_mod_cast (by decide : agreement ≤ blockLength)
  exact hrho.trans (calc
    (17 : ℚ) ≤ (d : ℚ) := by exact_mod_cast (show 17 ≤ d by omega)
    _ = 1 * (d : ℚ) := (one_mul _).symm
    _ ≤ density * d := mul_le_mul_of_nonneg_right hDensity (Nat.cast_nonneg _))
private theorem taylorPower_cast {g : ℕ} (hg : 0 < g) :
    (taylorPower g : ℚ) = 2 * (g : ℚ) - 1 := by
  unfold taylorPower
  rw [Nat.cast_sub (by omega)]
  push_cast
  rfl
private theorem regular_count {n g H d : ℕ} {U : Finset K} {s : K → Polynomial K} {w}
    (A : K1_14_2_4.RegularChart U s g H n) (hw : FixedWord w U s d)
    (hg : 0 < g) (hl : 131071 ≤ d) (hh : d ≤ 133593) :
    (U.card : ℚ) ≤ (2 * density * d * (taylorPower g : ℚ) + rho d) * H + 1 := by
  have hbound : 0 ≤ (2 * density * d * (taylorPower g : ℚ) + rho d) * (H : ℚ) := by
    unfold rho
    positivity
  by_cases hc : U.card ≤ 1
  · have h : (U.card : ℚ) ≤ 1 := by exact_mod_cast hc
    linarith only [h, hbound]
  let sites := persistentNodes w U s
  let t := max 1 (d-sites.card)
  have hd : d < agreement := hh.trans_lt (by decide)
  have hs : sites.card ≤ d := persistent_card_le hw (by omega)
  have ht : 0 < t := (by decide : 0 < 1).trans_le (le_max_left _ _)
  have htp : t < p := (max_le (by omega : 1 ≤ d) (Nat.sub_le _ _)).trans_lt
    (hh.trans_lt (by decide))
  have hdt : d ≤ sites.card + t := by
    have h := le_max_right 1 (d-sites.card)
    omega
  obtain ⟨C, hreconstruct⟩ := persistent_taylor sites w hdt htp hg A.equation A.equation_degree
  let D := taylorPower t * (g * H) + ordinateBound t g * H
  have hsection := section_bounds (w := w) A ht hw.distinct C fun γ hγ =>
    hreconstruct _ _ (hw.degree γ hγ) (fun _ hi => hits_persistent hγ hi) (A.root γ hγ) (A.simple γ hγ)
  have hinc : ((agreement - sites.card : ℕ) : ℚ) * U.card ≤ ((blockLength - sites.card : ℕ) : ℚ) * D := by
    exact_mod_cast section_incidence hw D hsection
  have hden : (0 : ℚ) < ((agreement - sites.card : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hs.trans_lt hd)
  have hcard : (U.card : ℚ) ≤ rho sites.card * (D : ℚ) := by
    rw [rho, div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).mpr
    calc
      _ = ((agreement - sites.card : ℕ) : ℚ) * U.card := mul_comm _ _
      _ ≤ _ := hinc
  obtain ⟨hρ, hρt⟩ := weights hs hd (rho_at_endpoint hl hh)
  have hρb : rho sites.card * (taylorPower t : ℚ) ≤ 2 * density * d := by
    have hb : (taylorPower t : ℚ) ≤ 2 * (t : ℚ) := by
      exact_mod_cast (Nat.sub_le (2*t) 1 : taylorPower t ≤ 2*t)
    have hρ0 : 0 ≤ rho sites.card := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have h := mul_le_mul_of_nonneg_left hb hρ0
    nlinarith only [h, hρt]
  have hsum : g + (g - 1) = taylorPower g := by unfold taylorPower; omega
  have hD : D = (taylorPower t * taylorPower g + 1) * H := by
    rw [← hsum]
    dsimp [D, ordinateBound]
    ring
  refine hcard.trans (le_add_of_le_of_nonneg ?_ zero_le_one)
  calc
    _ = (rho sites.card * (taylorPower t : ℚ) * (taylorPower g : ℚ) + rho sites.card) * H := by
      rw [hD]
      push_cast
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_right hρb (Nat.cast_nonneg _)) hρ) (Nat.cast_nonneg _)

/-- Degree and agreement at the new upper height, for an arbitrary set
of marks from the actual anchored family. -/
theorem fixed_word {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat≤2522) {T : Finset K} (hT : T⊆Γ) :
    FixedWord M.word T F.scalar endpointDegree where
  distinct := F.distinct.mono hT
  degree := by
    intro γ hγ
    rcases (F.mark γ (hT hγ)).scalar_degree with zero | bound
    · simp [zero]
    · change ((F.scalar γ).natDegree : ℤ)≤131071+M.overhead at bound
      change (F.scalar γ).natDegree≤133593
      omega
  hits := by
    intro γ hγ
    let A := F.mark γ (hT hγ)
    exact ⟨A.bad.support,A.bad.agreement,A.scalar_hits⟩

def curveUnit (g : ℕ) : ℚ :=
  (2*(g : ℚ)-1)*(1+2*density*endpointDegree)+rho endpointDegree

def CurveTariff {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ) : Prop :=
  ∀ T⊆Γ,∀ J g H,0<g → g≤80 →
    K1_14_2.SmallRootCurve J g H →
    Module.finrank SeedField (RootSeedSection J)<p →
    (∀ γ∈T,K1_14_2.OnRoot J (M.label γ) (F.scalar γ)) →
    (T.card : ℚ)≤curveUnit g*H+g

theorem curve_tariff {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat≤2522) : CurveTariff F := by
  intro T hT J g H hg hgLimit hcurve _ hmarks
  obtain ⟨U,hU,hexc,n,⟨A⟩⟩ := regular_chart T M.label F.scalar J g H hg
    (hgLimit.trans_lt (by decide)) hcurve (label_injective M).injOn hmarks
  have hregular := regular_count A (fixed_word F hi (hU.trans hT)) hg (by decide) (by decide)
  have hgQ : (1 : ℚ)≤g := by exact_mod_cast hg
  have hexcQ : ((T \ U).card : ℚ)≤(taylorPower g : ℚ)*H := by exact_mod_cast hexc
  calc
    (T.card : ℚ) = ((T \ U).card : ℚ)+(U.card : ℚ) := by
      exact_mod_cast (card_sdiff_add_card_eq_card hU).symm
    _ ≤ (taylorPower g : ℚ)*H + ((2*density*endpointDegree*(taylorPower g : ℚ)+rho endpointDegree)*H+1) :=
      add_le_add hexcQ hregular
    _ ≤ (taylorPower g : ℚ)*H + ((2*density*endpointDegree*(taylorPower g : ℚ)+rho endpointDegree)*H+g) :=
      add_le_add le_rfl (add_le_add le_rfl hgQ)
    _ = curveUnit g*H+g := by rw [taylorPower_cast hg]; unfold curveUnit; ring

theorem section_bound {w : I → K} {T : Finset K} {s : K → (Polynomial K)} {d a v : ℕ}
    (hw : FixedWord w T s d) (f : Row 2) (hf : Irreducible f) (hfpos : 0 < f.degreeOf 1)
    (hreg : ∀ γ ∈ T, RegularAt 1 f (extend (s γ))) (ha : 0 < a) (hv : 0 < v)
    (i : I) (hmiss : ∃ γ ∈ T, (s γ).eval (node i) ≠ w i)
    (cut : MvPolynomial (Fin 2) CenterField)
    (hcut : cut ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1 a v)
    (heval : ∀ γ ∈ T, MvPolynomial.aeval (marked (extend (s γ))) cut = 0 ↔
      (s γ).eval (node i) = w i) :
    (T.filter fun γ => (s γ).eval (node i) = w i).card ≤
      MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1) a v := by
  classical
  let x (γ : K) := marked (extend (s γ))
  have hx : Set.InjOn x (T : Set K) := fun _ ha _ hb heq =>
    hw.distinct ha hb (Polynomial.map_injective _ embed.injective (marked_injective heq))
  have hroot (γ : K) (hγ : γ ∈ T) : MvPolynomial.aeval (x γ) (plane f) = 0 := by
    dsimp only [x]
    rw [aeval_plane, (hreg γ hγ).1, map_zero]
  have hproper : cut ∉ Ideal.span {plane f} := by
    obtain ⟨η, hη, hbad⟩ := hmiss
    intro hmem
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hmem
    exact hbad ((heval η hη).mp (by rw [hq, map_mul, hroot η hη, zero_mul]))
  let hits := T.filter fun γ => (s γ).eval (node i) = w i
  have hplane : plane f ∈ MvPolynomial.restrictCappedDegree (Fin 2) CenterField 1
      f.totalDegree (f.degreeOf 1) := by
    intro m hm
    have hm' := MvPolynomial.support_map_subset toCenter f hm
    exact ⟨MvPolynomial.le_totalDegree hm', MvPolynomial.monomial_le_degreeOf 1 hm'⟩
  have hc := capped_cut_card ha hv (plane_ne_zero hf.ne_zero) (plane_prime hf hfpos)
    hplane hcut hproper (hits.image x) (by
      intro z hz
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hγT, hγi⟩ := Finset.mem_filter.mp hγ
      exact ⟨hroot γ hγT, (heval γ hγT).mpr hγi⟩)
  rwa [Finset.card_image_of_injOn (hx.mono (Finset.filter_subset _ _))] at hc

theorem fixed_bound {w T s d B J} (hw : FixedWord w T s d) (guard : ODEGuard B J)
    (G : ODE) (hG : ODECaps G B J) (hroot : ∀ γ ∈ T, fixedAt G (s γ) = 0)
    (a v : ℚ) (hv : 0 ≤ v) (hva : v ≤ a)
    (count : ∀ U ⊆ T, ∀ f : Row 2, Irreducible f → 0 < f.degreeOf 1 →
      f.totalDegree ≤ B → f.degreeOf 1 ≤ J →
      (∀ γ ∈ U, RegularAt 1 f (extend (s γ))) →
      (U.card : ℚ) ≤ mix f.totalDegree (f.degreeOf 1) a v + 1) :
    (T.card : ℚ) ≤ mix B J a v + (B^2 : ℕ) := by
  classical
  obtain ⟨q, hq, hb, hj, hsolve⟩ := clear_equation G hG.1 hG.2.1 hG.2.2
  obtain ⟨A, R, hA, hAb, hAj, hR, hRd, hcover⟩ :=
    factor_cover q hq guard.bmin guard.small hb hj
  let ordinary := T.filter fun γ => R.eval (extend (s γ)) = 0
  let reg (g : Row 2) := T.filter fun γ => RegularAt 1 g (extend (s γ))
  have hord : ordinary.card ≤ B * (B - 1) := by
    let v (γ : K) := extend (s γ)
    have hinj : Set.InjOn v (ordinary : Set K) := fun _ ha _ hb he =>
      hw.distinct (Finset.filter_subset _ _ ha) (Finset.filter_subset _ _ hb)
        (Polynomial.map_injective embed embed.injective he)
    have hcard : (ordinary.image v).card ≤ R.natDegree := by
      apply Polynomial.card_le_degree_of_subset_roots
      intro z hz
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
      exact (Polynomial.mem_roots hR).mpr (Finset.mem_filter.mp hγ).2
    rw [Finset.card_image_of_injOn hinj] at hcard
    exact hcard.trans hRd
  have htotal : T.card ≤ ordinary.card + ∑ g ∈ A, (reg g).card := by
    have hsub : T ⊆ ordinary ∪ A.biUnion reg := by
      intro γ hγ
      rcases hcover _ (hsolve _ (hroot γ hγ)) with hr | ⟨g, ha, hr⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hγ, hr⟩)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨g, ha, Finset.mem_filter.mpr ⟨hγ, hr⟩⟩)
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left Finset.card_biUnion_le _))
  have hnum : A.card ≤ B := by
    calc
      A.card = ∑ _ ∈ A, 1 := by simp
      _ ≤ ∑ g ∈ A, g.totalDegree := Finset.sum_le_sum fun g hg =>
        (hA g hg).2.trans_le (g.degreeOf_le_totalDegree 1)
      _ ≤ B := hAb
  have hlocal (f : Row 2) (hf : f ∈ A) :
      ((reg f).card : ℚ) ≤ mix f.totalDegree (f.degreeOf 1) a v + 1 :=
    count (reg f) (Finset.filter_subset _ _) f (hA f hf).1 (hA f hf).2
      ((Finset.single_le_sum (fun g _ => Nat.zero_le g.totalDegree) hf).trans hAb)
      ((Finset.single_le_sum (fun g _ => Nat.zero_le (g.degreeOf 1)) hf).trans hAj)
      (fun γ hγ => (Finset.mem_filter.mp hγ).2)
  have hreg : (∑ g ∈ A, ((reg g).card : ℚ)) ≤ mix B J a v + B := by
    refine (Finset.sum_le_sum hlocal).trans ?_
    simp only [mix_eq (MvPolynomial.degreeOf_le_totalDegree _ _), mix_eq guard.jb,
      Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hbt : (∑ g ∈ A, (g.totalDegree : ℚ)) ≤ B := by exact_mod_cast hAb
    have hjt : (∑ g ∈ A, (g.degreeOf 1 : ℚ)) ≤ J := by exact_mod_cast hAj
    have hnr : (A.card : ℚ) ≤ B := by exact_mod_cast hnum
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hbt hv)
      (mul_le_mul_of_nonneg_right hjt (sub_nonneg.mpr hva))) hnr
  have hbox : B * (B-1) + B = B^2 := by
    calc
      _ = B * ((B-1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = _ := by rw [Nat.sub_add_cancel ((by decide : 1 ≤ 2).trans guard.bmin), pow_two]
  have hs : (T.card : ℚ) ≤ ordinary.card + ∑ g ∈ A, ((reg g).card : ℚ) := by exact_mod_cast htotal
  have ho : (ordinary.card : ℚ) ≤ (B * (B-1) : ℕ) := by exact_mod_cast hord
  have hboxQ : (↑(B * (B-1) : ℕ) : ℚ) + B = (B^2 : ℕ) := by exact_mod_cast hbox
  linarith only [hs,ho,hreg,hboxQ]



private theorem word_subset {w T s d} (hw : FixedWord w T s d) {U : Finset K}
    (hU : U ⊆ T) : FixedWord w U s d :=
  ⟨hw.distinct.mono hU, fun γ hγ => hw.degree γ (hU hγ), fun γ hγ => hw.hits γ (hU hγ)⟩
def siteRatio (m : ℕ) : ℚ :=
  ((blockLength - m : ℕ) : ℚ) / ((agreement - m : ℕ) : ℚ)
def persistentTotal (d B : ℕ) : ℚ := siteRatio d + 2 * density * d * (B-1 : ℕ)
def persistentTop (d B J : ℕ) : ℚ :=
  min (persistentTotal d B) (density * d * (2*J-1 : ℕ))
private theorem persistentTotal_nonneg (d B : ℕ) : 0 ≤ persistentTotal d B := by
  unfold persistentTotal siteRatio
  positivity
private theorem caps_weighted {d m B J : ℕ} (hl : 131071 ≤ d) (hh : d ≤ 133593)
    (hm : m ≤ d) (hJ : 0 < J) :
    let t := max 1 (d-m)
    siteRatio m * totalCap t B ≤ persistentTotal d B ∧
      siteRatio m * topCap t B J ≤ persistentTop d B J := by
  let t := max 1 (d-m)
  have hd : d < agreement := hh.trans_lt (by decide)
  obtain ⟨hMu, hLambda⟩ := weights hm hd (rho_at_endpoint hl hh)
  change siteRatio m ≤ siteRatio d at hMu
  change siteRatio m * t ≤ density * d at hLambda
  have hRatio : 0 ≤ siteRatio m := by unfold siteRatio; positivity
  have hp : (power t : ℚ) ≤ 2 * (t : ℚ) := by
    exact_mod_cast (Nat.sub_le (2 * t) 3)
  have hpow : siteRatio m * power t ≤ 2 * (density * d) := by
    have h := mul_le_mul_of_nonneg_left hp hRatio
    linarith only [h,hLambda]
  have htot : siteRatio m * totalCap t B ≤ persistentTotal d B := by
    unfold totalCap persistentTotal
    push_cast
    rw [mul_add, mul_one, ← mul_assoc, show 2 * density * (d : ℚ) = 2 * (density * d) from
      mul_assoc _ _ _]
    exact add_le_add hMu (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _))
  refine ⟨htot, ?_⟩
  unfold persistentTop
  apply le_min
  · exact (mul_le_mul_of_nonneg_left (by exact_mod_cast
      (show topCap t B J ≤ totalCap t B from min_le_left _ _)) hRatio).trans htot
  · have hcap : topCap t B J ≤ t * (2*J-1) := by
      apply (min_le_right _ _).trans
      rw [show 2*J-1 = 2*(J-1)+1 by omega, Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add_right ((Nat.mul_le_mul_right _ (Nat.sub_le (2*t) 3)).trans_eq (by ring)) _
    calc
      _ ≤ siteRatio m * ((t * (2*J-1) : ℕ) : ℚ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hcap) hRatio
      _ = (siteRatio m * t) * (2*J-1 : ℕ) := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hLambda (Nat.cast_nonneg _)
private theorem persistent_regular {w T s d B J} (hw : FixedWord w T s d)
    (hl : 131071 ≤ d) (hh : d ≤ 133593) (hJ : 0 < J)
    (f : Row 2) (hf : Irreducible f) (hfpos : 0 < f.degreeOf 1)
    (hb : f.totalDegree ≤ B) (hj : f.degreeOf 1 ≤ J)
    (hreg : ∀ γ ∈ T, RegularAt 1 f (extend (s γ))) :
    (T.card : ℚ) ≤
      mix f.totalDegree (f.degreeOf 1) (persistentTotal d B) (persistentTop d B J) + 1 := by
  have hpos : 0 ≤ mix f.totalDegree (f.degreeOf 1) (persistentTotal d B) (persistentTop d B J) := by
    have ha : 0 ≤ persistentTotal d B := persistentTotal_nonneg d B
    have hv : 0 ≤ persistentTop d B J := le_min ha (by positivity)
    unfold mix
    positivity
  by_cases hsmall : T.card ≤ 1
  · exact (show (T.card : ℚ) ≤ 1 from by exact_mod_cast hsmall).trans (by linarith only [hpos])
  let sites := persistentNodes w T s
  let t := max 1 (d-sites.card)
  have hs : sites.card ≤ d := persistent_card_le hw (by omega)
  have ht : t ≤ d := max_le (by omega) (Nat.sub_le _ _)
  have htpos : 0 < t := (Nat.le_max_left _ _)
  have hsum : d ≤ sites.card + t := by
    have h := Nat.le_max_right 1 (d-sites.card)
    omega
  have hd : d < agreement := hh.trans_lt (by decide)
  have hdp := hd.trans (by decide : agreement < p)
  have ha : 0 < totalCap t B := by simp [totalCap]
  have hv : 0 < topCap t B J := lt_min ha ((Nat.le_add_left _ _).trans' htpos)
  let D := MvPolynomial.cappedDegreeMixedVolume f.totalDegree (f.degreeOf 1) (totalCap t B) (topCap t B J)
  have hcount := section_incidence hw D (fun i hi => by
    obtain ⟨cut, hc, he⟩ := short_cut f hdp ht hJ hb hj sites hsum w i
    exact section_bound hw f hf hfpos hreg ha hv i hi cut hc
      (fun γ hγ => he _ (hw.degree γ hγ) (hreg γ hγ) (fun _ hj => hits_persistent hγ hj)))
  have hgap : (0 : ℚ) < ((agreement-sites.card : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hs.trans_lt hd)
  have hratio : (T.card : ℚ) ≤ siteRatio sites.card * D := by
    unfold siteRatio
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hgap).mpr
    rw [mul_comm (T.card : ℚ)]
    exact_mod_cast hcount
  have hvle : topCap t B J ≤ totalCap t B := min_le_left _ _
  dsimp only [D] at hratio
  rw [cast_mixed (f.degreeOf_le_totalDegree 1) hvle] at hratio
  obtain ⟨hcapA, hcapV⟩ := caps_weighted (B := B) hl hh hs hJ
  refine hratio.trans ?_
  unfold mix
  calc
    _ = (↑(f.totalDegree - f.degreeOf 1 : ℕ) : ℚ) * (siteRatio sites.card * topCap t B J) +
        f.degreeOf 1 * (siteRatio sites.card * totalCap t B) := by ring
    _ ≤ (↑(f.totalDegree - f.degreeOf 1 : ℕ) : ℚ) * persistentTop d B J +
        f.degreeOf 1 * persistentTotal d B :=
      add_le_add (mul_le_mul_of_nonneg_left hcapV (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left hcapA (Nat.cast_nonneg _))
    _ ≤ _ := le_add_of_nonneg_right (by decide)

/-- The explicit persistent ODE tariff on the actual family. -/
def fixedFee (B J : ℕ) : ℕ :=
  (mix B J (persistentTotal endpointDegree B) (persistentTop endpointDegree B J)).ceil.toNat+B^2

theorem fixed_count {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat≤2522) {B J : ℕ} (guard : ODEGuard B J)
    (G : ODE) (caps : ODECaps G B J) {T : Finset K} (hT : T⊆Γ)
    (roots : ∀ γ∈T,fixedAt G (F.scalar γ)=0) :
    T.card≤fixedFee B J := by
  have hw := fixed_word F hi hT
  let a := persistentTotal endpointDegree B
  let v := persistentTop endpointDegree B J
  have ha : 0≤a := persistentTotal_nonneg _ _
  have hv : 0≤v := le_min ha (by positivity)
  have h := fixed_bound hw guard G caps roots a v hv (min_le_left _ _)
    (fun U hU=>persistent_regular (word_subset hw hU) (by decide) (by decide) guard.jpos)
  let r := mix B J a v
  have hceil : r≤(r.ceil.toNat : ℕ) := by
    have hs : (r.ceil : ℚ)≤(r.ceil.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat r.ceil
    exact Rat.le_ceil.trans hs
  change T.card≤r.ceil.toNat+B^2
  have bound : (T.card : ℚ)≤(r.ceil.toNat : ℚ)+(B^2 : ℕ) :=
    h.trans (add_le_add hceil le_rfl)
  exact_mod_cast bound

#print axioms curve_tariff
#print axioms fixed_count

end Lower6960.Rescue6966

end
end Merged_R6960Rescue6966Tariffs

-- merged module R6960Rescue6966Rates
section Merged_R6960Rescue6966Rates

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.Rescue6966
open Finset Polynomial
open K1 (K p)
open K1_14 (Seeds graphEval)
open K1_14_2 (Ambient OnJet SeedField RootSeedSection)
open K1_14_2_2 (CutCover CurveGeometry)
open K1_14_2_3 (SeedSlice seedImage rootImage constantCoefficients DefinedOverConstants seedLength yLength)
open K1_14_2_3 (on_root on_seed moving_graph_count seed_graph_count equal_image_degree union_card_le)
open scoped Classical BigOperators

structure RateOK (a h : ℚ) : Prop where
  degree : ((p+1 : ℕ) : ℚ)/81≤a
  height : 0≤h
  interpolation : ∀ g : ℕ,0<g → g≤80 →
    max 0 (1-a*g/((p+1 : ℕ) : ℚ))*curveUnit g≤h

def curveMarks {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ) (C : CutCover) : Finset K :=
  C.curves.biUnion (fun J=>Γ.filter (OnMark F J))

theorem mem_curveMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {C : CutCover} {J : Ideal Ambient} {γ : K} (mark : γ∈Γ)
    (curve : J∈C.curves) (on : OnMark F J γ) : γ∈curveMarks F C :=
  mem_biUnion.mpr ⟨J,curve,mem_filter.mpr ⟨mark,on⟩⟩

private theorem projected_curve : K1_14_2_3.c2 :=
  K1_14_2_3_2.of_children K1_14_2_3_2_1.proof K1_14_2_3_2_2.proof
private theorem seed_slice {I : Ideal Ambient} (h : CurveGeometry I) : SeedSlice I :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
private theorem mark_graph {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {I : Ideal Ambient} {C : Seeds} (hC : seedImage I = Ideal.span {C}) :
    ∀ z ∈ (Γ.filter (OnMark F I)).image M.label, graphEval z C = 0 := by
  intro z hz
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hz
  apply on_seed (Finset.mem_filter.mp hγ).2
  rw [hC]
  exact Ideal.mem_span_singleton_self C
private theorem translated_card {u del} (M : Model u del) (T : Finset K) :
    (T.image M.label).card = T.card :=
  Finset.card_image_of_injective _ (fun _ _ hab => sub_left_inj.mp hab)
private theorem direct_count {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {I : Ideal Ambient} {C : Seeds} (hC : C ≠ 0) (hI : seedImage I = Ideal.span {C})
    (hp : C.totalDegree < p) :
    (Γ.filter (OnMark F I)).card ≤ (p+1)*C.totalDegree := by
  have h := seed_graph_count C hC hp ((Γ.filter (OnMark F I)).image M.label) (mark_graph F hI)
  rwa [translated_card] at h
private theorem interpolate (g : ℕ) (a h d H T : ℚ) (hg : 0 < g)
    (hH : 0 ≤ H) (hd : 0 ≤ d) (hu : RateOK a h)
    (direct : T ≤ ((p+1 : ℕ) : ℚ)*d)
    (tariff : g ≤ 80 → T ≤ curveUnit g * H + g) :
    T ≤ a*(d*g) + h*H + g := by
  let q : ℚ := (p+1 : ℕ)
  have hq : 0 < q := Nat.cast_pos.mpr (Nat.succ_pos p)
  have ha : 0 ≤ a := (show 0 ≤ q/81 by positivity).trans hu.degree
  by_cases large : q ≤ a*g
  · calc
      T ≤ q*d := direct
      _ ≤ (a*g)*d := mul_le_mul_of_nonneg_right large hd
      _ = a*(d*g) := by ring
      _ ≤ _ := by
        have hn := mul_nonneg hu.height hH
        have hgq : (0 : ℚ) ≤ g := Nat.cast_nonneg _
        linarith
  · have hgsmall : g ≤ 80 := by
      by_contra! h
      have hgQ : (81 : ℚ) ≤ g := by exact_mod_cast Nat.succ_le_of_lt h
      have he : q/81*81 = q := by ring
      apply large
      rw [← he]
      exact mul_le_mul hu.degree hgQ (by norm_num) ha
    let θ := a*g/q
    have hθ : 0 ≤ θ := div_nonneg (mul_nonneg ha (Nat.cast_nonneg _)) hq.le
    have hc : 0 ≤ 1-θ := sub_nonneg.mpr ((div_le_iff₀ hq).mpr (by simpa using (le_of_lt (lt_of_not_ge large))))
    have hh : (1-θ)*curveUnit g ≤ h := by
      have hf := hu.interpolation g hg hgsmall
      rw [max_eq_right hc] at hf
      exact hf
    calc
      T = θ*T+(1-θ)*T := by ring
      _ ≤ θ*(q*d)+(1-θ)*(curveUnit g*H+g) :=
        add_le_add (mul_le_mul_of_nonneg_left direct hθ)
          (mul_le_mul_of_nonneg_left (tariff hgsmall) hc)
      _ = a*(d*g)+((1-θ)*curveUnit g)*H+(1-θ)*g := by
        dsimp only [θ]
        field_simp [hq.ne']; ring
      _ ≤ _ := by
        have hlast : (1-θ)*(g : ℚ) ≤ g := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right (sub_le_self 1 hθ) (Nat.cast_nonneg (α := ℚ) g)
        exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hh hH)) hlast
private theorem rated_component {u del} {M : Model u del} {Γ} (F : Family M Γ)
    (tariff : CurveTariff F) {a h globalCap localCap : ℚ} (hu : RateOK a h)
    (hmin : min globalCap localCap ≤ a) {I : Ideal Ambient} (geom : CurveGeometry I)
    (hglobal : (seedLength I : ℚ) ≤ globalCap) (hlocal : (seedLength I : ℚ) ≤ localCap)
    (hp : seedLength I < p) :
    ((Γ.filter (OnMark F I)).card : ℚ) ≤
      a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I := by
  let T := Γ.filter (OnMark F I)
  let D := seedLength I
  let H := yLength I
  have hD : (0 : ℚ) ≤ D := Nat.cast_nonneg _
  have hH : (0 : ℚ) ≤ H := Nat.cast_nonneg _
  have ha : 0 ≤ a := (show (0 : ℚ) ≤ ((p+1 : ℕ) : ℚ)/81 by positivity).trans hu.degree
  obtain ⟨f, hf, he, hpos, hd⟩ := K1_14_2_3_1.proof I (seed_slice geom)
  have hdq : (f.totalDegree : ℚ) ≤ D := by exact_mod_cast hd
  by_cases hconst : DefinedOverConstants (seedImage I)
  · obtain ⟨Q, hQ, heQ⟩ := hconst
    have hdeg : f.totalDegree = Q.totalDegree := equal_image_degree f hf.ne_zero Q (he.symm.trans heQ)
    obtain ⟨g, hg, hroot, hgD⟩ := projected_curve I Q (seed_slice geom) geom.2.2.2.2 hQ heQ
    have hgcap : g ≤ D := (Nat.le_mul_of_pos_left g (hdeg ▸ hpos)).trans hgD
    have hp' : Module.finrank SeedField (RootSeedSection (rootImage I)) < p := by
      obtain ⟨_, Q', hQ', hQ'proj, _, hlen, _, _⟩ := hroot
      have heQ' : seedImage I = Ideal.span {MvPolynomial.map constantCoefficients Q'} := hQ'proj
      have hdeg' := equal_image_degree f hf.ne_zero Q' (he.symm.trans heQ')
      rw [hlen, ← hdeg', hdeg]
      exact hgD.trans_lt hp
    have hdir : (T.card : ℚ) ≤ ((p+1 : ℕ) : ℚ)*(Q.totalDegree : ℚ) := by
      have hcount := direct_count F hf.ne_zero he (hd.trans_lt hp)
      rw [hdeg] at hcount
      exact_mod_cast hcount
    have htar (hgi : g ≤ 80) : (T.card : ℚ) ≤ curveUnit g * H + g :=
      tariff T (Finset.filter_subset _ _) (rootImage I) g H hg hgi hroot hp'
        (fun _ hz => on_root (Finset.mem_filter.mp hz).2)
    have hfirst := interpolate g a h Q.totalDegree H T.card hg hH
      (Nat.cast_nonneg _) hu hdir htar
    have hgDq : (Q.totalDegree : ℚ)*g ≤ D := by exact_mod_cast hgD
    have hgcapq : (g : ℚ) ≤ D := by exact_mod_cast hgcap
    exact hfirst.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hgDq ha) le_rfl)
      hgcapq)
  · have hmov := moving_graph_count p f hf (he ▸ hconst)
      (T.image M.label) (mark_graph F he)
    rw [translated_card] at hmov
    have hcard : (T.card : ℚ) ≤ (f.totalDegree : ℚ)^2 := by exact_mod_cast hmov
    have hd0 : (0 : ℚ) ≤ f.totalDegree := Nat.cast_nonneg _
    have har : (f.totalDegree : ℚ) ≤ a :=
      (le_min (hdq.trans hglobal) (hdq.trans hlocal)).trans hmin
    calc
      _ ≤ (f.totalDegree : ℚ)^2 := hcard
      _ ≤ a*D := by rw [pow_two]; exact mul_le_mul har hdq hd0 ha
      _ ≤ _ := by
        have hn := mul_nonneg hu.height hH
        linarith
theorem rated_curve_count {u del} {M : Model u del} {Γ}
    (F : Family M Γ) (tariff : CurveTariff F)
    {a h globalCap : ℚ} (hu : RateOK a h) (C : CutCover)
    (hglobal : (C.cost 0 : ℚ) ≤ globalCap)
    (hdegree : min globalCap (C.cost 0 : ℚ) ≤ a) (hp : C.cost 0 < p) :
    ((curveMarks F C).card : ℚ) ≤ a*(C.cost 0 : ℚ)+h*(C.cost 1 : ℚ)+C.cost 0 := by
  have hsum : ∑ I ∈ C.curves, seedLength I = C.cost 0 := rfl
  have hsumH : ∑ I ∈ C.curves, yLength I = C.cost 1 := rfl
  have hcount (I : Ideal Ambient) (hI : I ∈ C.curves) :
      ((Γ.filter (OnMark F I)).card : ℚ) ≤
        a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I := by
    have hn : seedLength I ≤ C.cost 0 := hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) hI
    have hq : (seedLength I : ℚ) ≤ (C.cost 0 : ℚ) := by exact_mod_cast hn
    exact rated_component F tariff hu hdegree (C.geometric I hI) (hq.trans hglobal) hq (hn.trans_lt hp)
  calc
    _ ≤ ∑ I ∈ C.curves, ((Γ.filter (OnMark F I)).card : ℚ) := union_card_le _ _
    _ ≤ ∑ I ∈ C.curves, (a*(seedLength I : ℚ)+h*(yLength I : ℚ)+seedLength I) :=
      Finset.sum_le_sum hcount
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Nat.cast_sum, hsum, hsumH]

#print axioms rated_curve_count
end Lower6960.Rescue6966

end
end Merged_R6960Rescue6966Rates

end Merged6967_High6966Rates

section Merged6967_High6966RescueBills
set_option Elab.async false


set_option Elab.async false

-- merged module High6966RescueCaps
section Merged_High6966RescueCaps

namespace Lower6960.Rescue6966
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift)
open K1_14_2_2 (mass mass_mono)
open Rescue6966Source (data bank reserve)
theorem Run.terminal_cap {u deleted} {M:Model u deleted} {Γ} {F:Family M Γ}
    {D:PoleData M.overhead.toNat} {Crt:CRTLift D} {G:Jet} (R:Run F Crt G) (k:Fin 2) :
    mass R.final (Fin.castLE (by decide : 2≤4) k) ≤ (data R.rect).bound k := by
  classical
  let route:=data R.rect
  let i:=route.pivot k
  let c:=Fin.castLE (by decide : 2≤4) k
  have hit:=R.cap i 17 i.isLt c
  have small:=route.tight k
  have sub : R.final⊆R.kept 17:=Finset.filter_subset _ _
  have paid := (Nat.mul_le_mul_left (reserve R.rect i+1) (mass_mono sub c)).trans hit
  have cost : (reserve R.rect i+1)*mass R.final c<(reserve R.rect i+1)*(route.bound k+1) :=
    paid.trans_lt small
  exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_left cost)

theorem Run.terminal_ordinate {u deleted} {M:Model u deleted} {Γ} {F:Family M Γ}
    {D:PoleData M.overhead.toNat} {Crt:CRTLift D} {G:Jet} (R:Run F Crt G) :
    mass R.final 0 ≤157 :=
  (R.terminal_cap 0).trans (data R.rect).degree_cap
#print axioms Run.terminal_cap
#print axioms Run.terminal_ordinate
end Lower6960.Rescue6966

end Merged_High6966RescueCaps

-- merged module High6966RescueBills
section Merged_High6966RescueBills
section Merged_R6960Rescue6966Bills
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
namespace Lower6960.Rescue6966
open Finset Polynomial
open K1 (I K)
open K1_14 (Shape Jet atX jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient)
open K1_14_2_2 (mass weight dot CutCover emptyCut mass_mono)
open K1_14_2_2_4 (pairCap)
open K1_14_3 (Surface Parent)
open Rescue6966Source (bank reserve)
open P1_7_4 (Mass massQ dotQ massQ_mono weightedBill bill_bound)
open scoped Classical
def cutWeight (rect : Fin 54) (fee : Fin 3) (i : ℕ) : Mass :=
  fun k => weight (cutShape rect i) fee k
def seedLimit (rect : Fin 54) : ℚ := weightedBill 17 (cutWeight rect 0) (history rect)
def pointLimit (rect : Fin 54) : ℚ := weightedBill 17 (cutWeight rect 2) (fun _ => initialMass rect)
def initialSeedLimit (rect : Fin 54) : ℕ := (K1.p+1)*initialCap rect 2+initialCap rect 3
theorem seed_limit_small (rect : Fin 54) : seedLimit rect < (K1.p : ℚ) := by
  fin_cases rect <;> decide +kernel
def Initial.seedMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 54} (ini : Initial F G Q₀ rect) : Finset K :=
  Γ.filter (fun γ=>ini.seeds.Covers (M.label γ))
def Initial.ordinateMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 54} (ini : Initial F G Q₀ rect) : Finset K :=
  Γ.filter (fun γ=>atX (F.scalar γ)∈ini.ordinates)
theorem Initial.seed_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 54} (ini : Initial F G Q₀ rect) :
    ini.seedMarks.card ≤ initialSeedLimit rect := by
  have bound := K1_14_3.seed_count (T := ini.seedMarks) (label_injective M).injOn ini.seeds
    (ini.seed_degree.trans_lt (initial_small rect 2)) (fun _ hγ => (mem_filter.mp hγ).2)
  exact bound.trans (Nat.add_le_add (Nat.mul_le_mul_left _ ini.seed_degree) ini.seed_points)
theorem Initial.ordinate_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 54} (ini : Initial F G Q₀ rect) :
    ini.ordinateMarks.card ≤ initialCap rect 0 := by
  refine (card_le_card_of_injOn (fun γ=>atX (F.scalar γ)) (fun _ hγ=>(mem_filter.mp hγ).2) ?_).trans ini.ordinate_card
  intro γ hγ δ hδ eq
  exact F.distinct (mem_filter.mp hγ).1 (mem_filter.mp hδ).1 (K1_14_3.scalar_atX_injective eq)
structure CutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) where
  cover : ℕ→CutCover
  cost : ∀ i<17,∀ fee,(cover i).cost fee ≤ dot (weight (cutShape R.rect i) fee) (mass (R.lost i))
  covers : ∀ i<17,∀ γ∈Γ,(∃ J∈R.lost i,OnMark F J γ) →
    γ∈(cover i).direct ∨ ∃ Q∈(cover i).curves,OnMark F Q γ
theorem Run.cutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) : Nonempty (CutBooks R) := by
  have pick (i : ℕ) : ∃ C : CutCover,i<17 →
      (∀ fee,C.cost fee ≤ dot (weight (cutShape R.rect i) fee) (mass (R.lost i))) ∧
      ∀ γ∈Γ,(∃ J∈R.lost i,OnMark F J γ) → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark F Q γ := by
    by_cases hi : i<17
    · obtain ⟨C,cap,cover⟩ := R.cutCover noPole residues hi
      exact ⟨C,fun _=>⟨cap,cover⟩⟩
    · exact ⟨emptyCut,fun h=>(hi h).elim⟩
  choose C hC using pick
  exact ⟨⟨C,fun i h=>(hC i h).1,fun i h=>(hC i h).2⟩⟩
theorem CutBooks.costQ {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) {i : ℕ} (hi : i<17) (fee : Fin 3) :
    ((C.cover i).cost fee : ℚ)≤dotQ (cutWeight R.rect fee i) (massQ (R.lost i)) := by
  have bound := (Nat.cast_le (α:=ℚ)).mpr (C.cost i hi fee)
  simpa only [cutWeight,dotQ,dot,massQ,Nat.cast_sum,Nat.cast_mul] using bound
theorem CutBooks.seed_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) : (∑ i∈range 17,((C.cover i).cost 0 : ℚ))≤seedLimit R.rect :=
  (sum_le_sum fun _ h=>C.costQ (mem_range.mp h) 0).trans
    (bill_bound 17 _ _ R.live R.lost (fun _ hi=>R.next_sub hi) (fun _ _=>subset_rfl)
      (fun _ hi=>R.live_history hi))
def CutBooks.pointMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) : Finset K := (range 17).biUnion fun i=>(C.cover i).direct
theorem CutBooks.point_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) : (C.pointMarks.card : ℚ) ≤ pointLimit R.rect := by
  calc
    _ ≤ ∑ i∈range 17,((C.cover i).cost 2 : ℚ) := by
      exact_mod_cast (show C.pointMarks.card ≤ ∑ i∈range 17,(C.cover i).direct.card from card_biUnion_le)
    _ ≤ ∑ i∈range 17,dotQ (cutWeight R.rect 2 i) (massQ (R.lost i)) :=
      sum_le_sum fun i h=>C.costQ (mem_range.mp h) 2
    _ ≤ _ := bill_bound 17 _ _ R.live R.lost (fun _ hi=>R.next_sub hi) (fun _ _=>subset_rfl)
      (fun _ hi=>R.live_initial hi)
def beforeCuts (first : Mass) (rest : ℕ → Mass) : ℕ → Mass
  | 0 => first
  | i+1 => rest i
private def Run.jointLive {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    ℕ→Finset (Ideal Ambient)
  | 0 => R.initial.rankExit∪R.initial.parents
  | i+1 => R.live i
private def Run.jointLost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G) :
    ℕ→Finset (Ideal Ambient)
  | 0 => R.initial.rankExit
  | i+1 => R.lost i
theorem Run.joint_bill_with_final {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (rank : Mass) (cut : ℕ→Mass) :
    dotQ rank (massQ R.initial.rankExit) + (∑ i∈range 17,dotQ (cut i) (massQ (R.lost i))) +
      dotQ (P1_7_4.running (beforeCuts rank cut) 18) (massQ R.final) ≤
      weightedBill 18 (beforeCuts rank cut) (beforeCuts (initialMass R.rect) (history R.rect)) := by
  have bill := P1_7_4.bill_bound_with_final 18 (beforeCuts rank cut) (beforeCuts (initialMass R.rect) (history R.rect))
    R.jointLive R.jointLost ?_ ?_ ?_
  · rw [show 18=17+1 by decide,sum_range_succ'] at bill
    have final : R.jointLive 18 = R.final := by simp [Run.jointLive,Run.live]
    simpa only [beforeCuts,Run.jointLost,final,add_comm] using bill
  · intro i hi
    cases i with
    | zero => simpa only [Run.jointLive,R.live_start] using
        (subset_union_right : R.initial.parents⊆ R.initial.rankExit∪R.initial.parents)
    | succ i => exact R.next_sub (by omega)
  · intro i hi
    cases i with
    | zero =>
      intro J mem
      apply mem_sdiff.mpr
      refine ⟨mem_union_left _ mem,?_⟩
      rw [Run.jointLive,R.live_start]
      exact fun h=>(disjoint_left.mp R.initial.disjoint) mem h
    | succ i => exact subset_rfl
  · intro i hi k
    cases i with
    | zero => exact (Nat.cast_le (α:=ℚ)).mpr (R.initial.fits k)
    | succ i => exact R.live_history (by omega) k
theorem Run.joint_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} (R : Run F Crt G)
    (rank : Mass) (cut : ℕ→Mass) :
    dotQ rank (massQ R.initial.rankExit) + (∑ i∈range 17,dotQ (cut i) (massQ (R.lost i))) ≤
      weightedBill 18 (beforeCuts rank cut) (beforeCuts (initialMass R.rect) (history R.rect)) :=
  (le_add_of_nonneg_right (P1_7_4.final_credit_nonneg 18 (beforeCuts rank cut) R.final)).trans
    (R.joint_bill_with_final rank cut)

#print axioms Run.joint_bill_with_final
end Lower6960.Rescue6966
end
end Merged_R6960Rescue6966Bills

end Merged_High6966RescueBills

end Merged6967_High6966RescueBills

section Merged6967_Low6966RetainedAssembly
set_option Elab.async false






set_option Elab.async false

-- merged module R6960Low6966SharedCycleLegacy
section Merged_R6960Low6966SharedCycleLegacy
set_option Elab.async false

namespace Low6966SharedCycleLegacy
noncomputable section
open Low6966Prices (SmallFactor primaryBox taylorLength)
open Low6966GeometryCut_2 (Branch Slice5 budget5)
open P0_9_6_2_3 (cylinder_comparison cycle_comparison divisor_comparison proper_cut_comparison)
open K1_13 (Row Shape shape InBox liftedChart)
open K1_13_6 (GeoJets GeoField toGeneric intersectionIdeal cycleLength)
open K1_13_6_2 (JetPoint GeoJets5 Box5 graphBox)
open K1_13_6_2_4 (Admissible Chamber Component DimLE DivisorBound OfDim LengthAt
  ambient_dim cylinder cylinder_injective dim_le_after_section mixedDegree oldEmbedding
  old_section_box point_bound pointIdeal sectionIdeal)
open scoped BigOperators
open Low6966GeometryCut_2_3 (boxes graphLift last_caps boxes_admissible chart_index_eq
  graphLift_same_chart membership_same_chart graphLift_comap member_proper_on_graph ambient_budget)
open Low6966GeometryCut_2_3 (bound_marks)

private theorem initial_bound
    (f Q : Row 4) (weight : Ideal GeoJets → ℕ) (hf : SmallFactor f) (hQ : ¬ f ∣ Q)
    (hQbox : InBox (shape Q) primaryBox) (S : Finset (Ideal GeoJets))
    (hS : ∀ P ∈ S, ∃ h : (intersectionIdeal f Q).IsMinimalPrime P,
      (weight P : ℕ∞) ≤ cycleLength (intersectionIdeal f Q) P h.isPrime) :
    (∀ P ∈ S, (cylinder P).IsPrime ∧ OfDim (cylinder P) 3) ∧
      (∑ P ∈ S, (weight P : ℚ) * mixedDegree (boxes (shape f).chamber) (cylinder P) {2, 3, 4}) ≤
        mixedDegree (boxes (shape f).chamber) ⊥ Finset.univ := by
  classical
  let p := (shape f).chamber
  let B := boxes p
  have hB := boxes_admissible p (K1_13_7_1.shape_chamber f)
  let A := sectionIdeal ⊥ (oldEmbedding (toGeneric f))
  let J := sectionIdeal A (oldEmbedding (toGeneric Q))
  obtain ⟨hregQ, hAlgebra⟩ := cylinder_comparison f Q hf.1 hQ
  have hregf : IsLeftRegular (Ideal.Quotient.mk (⊥ : Ideal GeoJets5)
      (oldEmbedding (toGeneric f))) := by
    apply IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]
    exact (MvPolynomial.rename_injective _ (Fin.castSucc_injective 4)).ne
      (K1_13_6_3_6.toGeneric_ne_zero hf.1.ne_zero)
  have hboxf : Box5 p 0 (oldEmbedding (toGeneric f)) :=
    old_section_box ⟨le_max_left _ _, le_rfl, le_rfl⟩
  have hAdim : DimLE A 4 := dim_le_after_section hregf ambient_dim
  have hJdim : DimLE J 3 := dim_le_after_section hregQ hAdim
  have hgeom (P : Ideal GeoJets) (hP : P ∈ S) :
      (cylinder P).IsPrime ∧ OfDim (cylinder P) 3 ∧
        ∃ hc : J.IsMinimalPrime (cylinder P), (weight P : ℕ∞) ≤ LengthAt J (cylinder P) hc.isPrime := by
    obtain ⟨h, hw⟩ := hS P hP
    obtain ⟨hd, hc, hl⟩ := hAlgebra P h
    exact ⟨hc.isPrime, hd, hc, hw.trans hl⟩
  refine ⟨fun P hP => ⟨(hgeom P hP).1, (hgeom P hP).2.1⟩, ?_⟩
  have hs := cycle_comparison B hB J {2, 3, 4} hJdim S cylinder weight cylinder_injective.injOn
    (fun P hP => (hgeom P hP).2.2)
  have hcutQ := proper_cut_comparison B hB A {2, 3, 4} 1 (by decide) hAdim
    (oldEmbedding (toGeneric Q)) (old_section_box hQbox) hregQ
  have hcutf := proper_cut_comparison B hB ⊥ {1, 2, 3, 4} 0 (by decide) ambient_dim
    (oldEmbedding (toGeneric f)) hboxf hregf
  have hall : (insert (0 : Fin 5) {1, 2, 3, 4} : Finset (Fin 5)) = Finset.univ := by decide
  rw [hall] at hcutf
  exact hs.trans (hcutQ.trans hcutf)
theorem bound_with_weights
    (f Q : Row 4) (l : ℕ) (hf : SmallFactor f) (hproper : ¬ f ∣ Q)
    (hQ : InBox (shape Q) primaryBox)
    (weight : Ideal GeoJets → ℕ)
    (F : Finset (Branch f Q l)) (T : Branch f Q l → Finset JetPoint)
    (hF : ∀ b ∈ F, Box5 (graphBox (shape f).chamber) 1 b.graph ∧
       (∃ E, Box5 (liftedChart (taylorLength + 1) (shape f).chamber)
          (taylorLength + 1) E ∧ Associated (b.onGraph E) (b.localMap b.member)) ∧
       (∀ p ∈ T b, b.Contains p) ∧ Slice5 b (T b))
    (hcut : ∀ b ∈ F, (weight b.surface : ℕ∞) ≤
      cycleLength (intersectionIdeal f Q) b.surface b.base.isPrime) :
    32 * (∑ b ∈ F, (weight b.surface : ℚ) * ((b.weight : ℚ) * (T b).card)) ≤
      (budget5 (shape f).chamber : ℚ) := by
  classical
  have hdiv := divisor_comparison
  have hgraph := @Low6966GeometryCut_2_3_1.proof f Q l
  have hmember := @Low6966GeometryCut_2_3_2.proof f Q l
  let p := (shape f).chamber
  have hp : Chamber p := K1_13_7_1.shape_chamber f
  let B := boxes p
  have hB : Admissible B := boxes_admissible p hp
  let S := F.image Branch.surface
  let fibre (P : Ideal GeoJets) := F.filter fun b => b.surface = P
  let charge (b : Branch f Q l) : ℚ := (b.weight : ℚ) * (T b).card
  obtain ⟨hZ, hsumZ⟩ := initial_bound f Q weight hf hproper hQ S (by
    intro P hP
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hP
    exact ⟨b.base, hcut b hb⟩)
  have hfibre (P : Ideal GeoJets) (hP : P ∈ S) :
      (∑ c ∈ fibre P, charge c) ≤ mixedDegree B (cylinder P) {2, 3, 4} := by
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hP
    let G := graphLift b b.surface
    let C (c : Branch f Q l) := graphLift c c.curve
    obtain ⟨hboxG, ⟨E, hboxE, hE⟩, _, _⟩ := hF b hb
    obtain ⟨hZprime, hZdim⟩ := hZ _ hP
    obtain ⟨hproperG, hG, hGdim⟩ := hgraph b hZprime hZdim
    have hC (c : Branch f Q l) (hcs : c.surface = b.surface) :
        Component G E (C c) c.weight ∧ OfDim (C c) 1 := by
      have hr := chart_index_eq hcs
      have hsame : graphLift c c.surface = G :=
        (graphLift_same_chart hr c.surface).trans (congrArg (graphLift b) hcs)
      have hE' := (membership_same_chart hr E).mpr hE
      rw [← hsame]
      exact hmember c E (hsame.symm ▸ hG.minimal.isPrime) (hsame.symm ▸ hGdim) hE'
    have hproperE := member_proper_on_graph b hE
    have inj : Set.InjOn C (fibre b.surface : Set (Branch f Q l)) := by
      intro c hc d hd he
      have hcs := (Finset.mem_filter.mp hc).2
      have hds := (Finset.mem_filter.mp hd).2
      apply Branch.eq_of_surface_curve (hcs.trans hds.symm)
      rw [← graphLift_comap c c.curve c.divisor.isPrime c.regularCurve,
        ← graphLift_comap d d.curve d.divisor.isPrime d.regularCurve]
      exact congrArg (Ideal.comap oldEmbedding) he
    have hmarks : (∑ c ∈ fibre b.surface, charge c) ≤
        ∑ c ∈ fibre b.surface, (c.weight : ℚ) * mixedDegree B (C c) {4} := by
      apply Finset.sum_le_sum
      intro c hc
      obtain ⟨hcF, hcs⟩ := Finset.mem_filter.mp hc
      obtain ⟨_, _, hon, hslice⟩ := hF c hcF
      obtain ⟨hcomp, hdim⟩ := hC c hcs
      exact mul_le_mul_of_nonneg_left
        (bound_marks hdiv hB c (T c) rfl hon hslice hcomp.minimal.isPrime hdim)
        (Nat.cast_nonneg _)
    have hEbound := hdiv B hB G {4} 3 hG.minimal.isPrime (by decide) hGdim E hboxE hproperE
      (fibre b.surface) C Branch.weight inj (fun c hc => (hC c (Finset.mem_filter.mp hc).2).1)
    have hGbound := hdiv B hB (cylinder b.surface) {3, 4} 2 hZprime (by decide) hZdim
      b.graph hboxG hproperG {G} id (fun _ => 1) (fun _ _ _ _ h => h) (by
        intro P hP
        obtain rfl := Finset.mem_singleton.mp hP
        exact hG)
    have hGbound' : mixedDegree B G {3, 4} ≤ mixedDegree B (cylinder b.surface) {2, 3, 4} := by
      simpa only [Finset.sum_singleton, Nat.cast_one, one_mul, id_eq] using hGbound
    exact hmarks.trans (hEbound.trans hGbound')
  have hcharge :
      (∑ c ∈ F, (weight c.surface : ℚ) * charge c) ≤
        ∑ P ∈ S, (weight P : ℚ) * mixedDegree B (cylinder P) {2, 3, 4} := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := Branch.surface)
      (fun b hb => Finset.mem_image_of_mem Branch.surface hb)
      (fun b => (weight b.surface : ℚ) * charge b)]
    apply Finset.sum_le_sum
    intro P hP
    change (∑ c ∈ fibre P, (weight c.surface : ℚ) * charge c) ≤ _
    calc
      _ = ∑ c ∈ fibre P, (weight P : ℚ) * charge c := by
        apply Finset.sum_congr rfl
        intro c hc
        simp [(Finset.mem_filter.mp hc).2]
      _ = (weight P : ℚ) * ∑ c ∈ fibre P, charge c := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hfibre P hP) (Nat.cast_nonneg _)
  exact (mul_le_mul_of_nonneg_left (hcharge.trans hsumZ) (by norm_num)).trans
    (ambient_budget p hp)

#print axioms bound_with_weights
end
end Low6966SharedCycleLegacy

end Merged_R6960Low6966SharedCycleLegacy

-- merged module R6960Low6966SharedTally
section Merged_R6960Low6966SharedTally

set_option Elab.async false
namespace Low6966SharedTally
noncomputable section

open P3 (K)
open K1_13 (Row extend embed chart liftedChart shape)
open K1_13_6 (GeoJets Pieces CurveSections toGeneric)
open K1_13_6_2 (JetPoint actualPoint actualPoint_injective Demand maximal_demand Box4 Box5 graphBox)
open Low6966GeometryCut (CutInput)
open Low6966GeometryCut_2 (Branch Chart4 Chart5 Slice4 Slice5 chart4)
open Low6966ActiveCycle (Chart Section Slice)
open Low6966Prices (taylorLength)
open scoped Polynomial BigOperators

def hasBranch (f Q : Row 4) (l : ℕ) (S : Set (Ideal GeoJets)) (g : (Polynomial K1_13.Geom)) : Prop :=
  ∃ b : Branch f Q l, b.surface ∈ S ∧ b.Contains (actualPoint g)

structure Data (Γ : Finset K) (s : K→(Polynomial K)) (f Q : Row 4) (l : ℕ)
    (S : Set (Ideal GeoJets)) where
  branches : Finset (Branch f Q l)
  allowed : ∀ b∈branches, b.surface∈S
  labels : Branch f Q l → Finset K
  label_sub : ∀ b, labels b ⊆ Γ
  label_on : ∀ b γ, γ∈labels b → b.Contains (actualPoint (extend (s γ)))
  demanded : Branch f Q l → Finset K
  demand_sub : ∀ b, demanded b ⊆ labels b
  demand_simple : ∀ b, b.Simple → demanded b=labels b
  demand_multiple : ∀ b∈branches, ¬b.Simple → 0<(demanded b).card ∧
    CurveSections (labels b) s (demanded b).card ∧ Demand (labels b) s (demanded b)
  covered : ∀ γ∈Γ, hasBranch f Q l S (extend (s γ)) → ∃ b∈branches, γ∈labels b

private def point {s : K→(Polynomial K)} (γ : K) : JetPoint := actualPoint (extend (s γ))

def Data.points {Γ s f Q l S} (D : Data Γ s f Q l S) (b : Branch f Q l) :
    Finset JetPoint := by
  classical
  exact (D.demanded b).image (point (s := s))

def build {Γ s f Q l} (S : Set (Ideal GeoJets)) : Data Γ s f Q l S := by
  classical
  let marked := Γ.filter (fun γ => hasBranch f Q l S (extend (s γ)))
  let assign (γ : marked) : Branch f Q l :=
    Classical.choose (Finset.mem_filter.mp γ.property).2
  let branches := marked.attach.image assign
  let labels (b : Branch f Q l) :=
    marked.filter (fun γ => ∃ h : γ ∈ marked, assign ⟨γ, h⟩ = b)
  let point := point (s := s)
  have label_sub (b : Branch f Q l) : labels b ⊆ Γ :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have contains_label (b : Branch f Q l) (γ : K) (hγ : γ ∈ labels b) :
      b.Contains (point γ) := by
    obtain ⟨h, rfl⟩ := (Finset.mem_filter.mp hγ).2
    exact (Classical.choose_spec (Finset.mem_filter.mp h).2).2
  have labels_nonempty (b : Branch f Q l) (hb : b ∈ branches) : (labels b).Nonempty := by
    obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp hb
    exact ⟨γ.val, Finset.mem_filter.mpr ⟨γ.property, γ.property, rfl⟩⟩
  have available (b : Branch f Q l) : ∃ T ⊆ labels b,
      (b.Simple → T = labels b) ∧
      (b ∈ branches → ¬ b.Simple → 0 < T.card ∧ CurveSections (labels b) s T.card ∧
        Demand (labels b) s T) := by
    by_cases hs : b.Simple
    · exact ⟨labels b, Finset.Subset.rfl, fun _ => rfl, fun _ hn => (hn hs).elim⟩
    by_cases hb : b ∈ branches
    · obtain ⟨T, hsub, hd⟩ := maximal_demand (labels b) s (labels_nonempty b hb)
      exact ⟨T, hsub, fun h => (hs h).elim, fun _ _ => hd⟩
    · exact ⟨∅, Finset.empty_subset _, fun h => (hs h).elim, fun h _ => (hb h).elim⟩
  choose demanded demand_sub demand_simple demand_multiple using available
  refine ⟨branches,?_,labels,label_sub,contains_label,demanded,demand_sub,
    demand_simple,demand_multiple,?_⟩
  · intro b hb
    obtain ⟨γ,_,rfl⟩ := Finset.mem_image.mp hb
    exact (Classical.choose_spec (Finset.mem_filter.mp γ.property).2).1
  · intro γ hγ hcase
    have hmark : γ∈marked := Finset.mem_filter.mpr ⟨hγ,hcase⟩
    exact ⟨assign ⟨γ,hmark⟩,Finset.mem_image.mpr ⟨_,Finset.mem_attach _ _,rfl⟩,
      Finset.mem_filter.mpr ⟨hmark,hmark,rfl⟩⟩

variable {Γ : Finset K} {s : K→(Polynomial K)} {f Q : Row 4} {l : ℕ} {S : Set (Ideal GeoJets)}

theorem Data.points_card (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l) (b : Branch f Q l) : (D.points b).card = (D.demanded b).card := by
  classical
  unfold Data.points
  apply Finset.card_image_of_injOn
  intro γ hγ δ hδ heq
  exact input.distinct (D.label_sub b (D.demand_sub b hγ)) (D.label_sub b (D.demand_sub b hδ))
    (Polynomial.map_injective embed embed.injective (actualPoint_injective heq))

theorem Data.points_on (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l) (b : Branch f Q l) (p : JetPoint) (hp : p ∈ D.points b) : b.Contains p := by
  classical
  unfold Data.points at hp
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
  exact D.label_on b γ (D.demand_sub b hγ)

theorem Data.points_next (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l) (b : Branch f Q l) (p : JetPoint) (hp : p ∈ D.points b) :
    MvPolynomial.eval p b.next = 0 := by
  classical
  unfold Data.points at hp
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
  apply b.next_actual (D.label_on b γ (D.demand_sub b hγ))
  simpa only [Polynomial.natDegree_map] using input.degree γ (D.label_sub b (D.demand_sub b hγ))


theorem Data.four (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l) :
    ∀ b∈D.branches, Box4 (chart (taylorLength+1) (shape f).chamber) b.member ∧
      (∀ p∈D.points b, b.Contains p) ∧ Slice4 b (D.points b) := by
  let points := D.points
  let points_card := D.points_card input
  let points_on := D.points_on input
  let points_next := D.points_next input
  let contains_label := D.label_on
  let label_sub := D.label_sub
  let demand_sub := D.demand_sub
  let demand_multiple := D.demand_multiple
  intro b hb
  obtain ⟨hmember, hnext, hvalue⟩ := chart4 input.small b
  refine ⟨hmember, points_on b, ?_⟩
  by_cases hs : b.Simple
  · exact Or.inr ⟨b.next, hnext, b.next_proper hs, points_next b⟩
  rcases (demand_multiple b hb hs).2.2 with hone | ⟨x, a, hwit, heq⟩
  · exact Or.inl (by rw [points_card, hone])
  obtain ⟨D, hD, hEval⟩ := hvalue x a
  obtain ⟨δ, hδ, hδvalue⟩ := hwit
  have hδon := contains_label b δ hδ
  have hproper : D ∉ b.curve := fun hmem =>
    hδvalue ((hEval _ (input.degree δ (label_sub b hδ)) hδon).mp (hδon.1 hmem))
  refine Or.inr ⟨D, hD, hproper, ?_⟩
  intro p hp
  classical
  unfold Data.points at hp
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
  have hvalueγ := (Finset.mem_filter.mp (heq ▸ hγ)).2
  exact (hEval _ (input.degree γ (label_sub b (demand_sub b hγ)))
    (contains_label b γ (demand_sub b hγ))).mpr hvalueγ

theorem Data.five (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l) :
    ∀ b∈D.branches, Box5 (graphBox (shape f).chamber) 1 b.graph ∧
      (∃ E, Box5 (liftedChart (taylorLength+1) (shape f).chamber) (taylorLength+1) E ∧
        Associated (b.onGraph E) (b.localMap b.member)) ∧
      (∀ p∈D.points b, b.Contains p) ∧ Slice5 b (D.points b) := by
  let points := D.points
  let points_card := D.points_card input
  let points_on := D.points_on input
  let points_next := D.points_next input
  let contains_label := D.label_on
  let label_sub := D.label_sub
  let demand_sub := D.demand_sub
  let demand_multiple := D.demand_multiple
  intro b hb
  obtain ⟨hgraph, E, H, hE, hEeq, hH, hHeq, hvalue⟩ := Low6966GeometryCut_2_1.proof f Q l input.small b
  refine ⟨hgraph, ⟨E, hE, hEeq⟩, points_on b, ?_⟩
  by_cases hs : b.Simple
  · exact Or.inr ⟨H, hH, b.lifted_proper_of_associated hHeq (b.next_proper hs),
      fun p hp hon => b.lifted_zero_of_associated hHeq hon (points_next b p hp)⟩
  rcases (demand_multiple b hb hs).2.2 with hone | ⟨x, a, hwit, heq⟩
  · exact Or.inl (by rw [points_card, hone])
  obtain ⟨D, hD, hEval⟩ := hvalue x a
  obtain ⟨δ, hδ, hδvalue⟩ := hwit
  have hδon := contains_label b δ hδ
  refine Or.inr ⟨D, hD, b.lifted_proper_of_nonzero (point δ) hδon ?_, ?_⟩
  · exact fun hzero => hδvalue ((hEval _ (input.degree δ (label_sub b hδ)) hδon).mp hzero)
  · intro p hp hon
    classical
  unfold Data.points at hp
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
    have hvalueγ := (Finset.mem_filter.mp (heq ▸ hγ)).2
    exact (hEval _ (input.degree γ (label_sub b (demand_sub b hγ))) hon).mpr hvalueγ

theorem Data.bent {R : Low48BentCycle.Family} (D : Data Γ s f Q l S)
    (input : CutInput Γ s f Q l) (hchart : ∀ b : Branch f Q l, Chart R b) :
    ∀ b∈D.branches, Section R 2 b.graph ∧
      (∃ E, Section R 3 E ∧ Associated (b.onGraph E) (b.localMap b.member)) ∧
      (∀ p∈D.points b,b.Contains p) ∧ Slice R b (D.points b) := by
  let points := D.points
  let points_card := D.points_card input
  let points_on := D.points_on input
  let points_next := D.points_next input
  let contains_label := D.label_on
  let label_sub := D.label_sub
  let demand_sub := D.demand_sub
  let demand_multiple := D.demand_multiple
  intro b hb
  obtain ⟨hgraph, E, H, hE, hEeq, hH, hHeq, hvalue⟩ := hchart b
  refine ⟨hgraph, ⟨E, hE, hEeq⟩, points_on b, ?_⟩
  by_cases hs : b.Simple
  · exact Or.inr ⟨H, hH, b.lifted_proper_of_associated hHeq (b.next_proper hs),
      fun p hp hon => b.lifted_zero_of_associated hHeq hon (points_next b p hp)⟩
  rcases (demand_multiple b hb hs).2.2 with hone | ⟨x, a, hwit, heq⟩
  · exact Or.inl (by rw [points_card, hone])
  obtain ⟨D, hD, hEval⟩ := hvalue x a
  obtain ⟨δ, hδ, hδvalue⟩ := hwit
  have hδon := contains_label b δ hδ
  refine Or.inr ⟨D, hD, b.lifted_proper_of_nonzero (point δ) hδon ?_, ?_⟩
  · exact fun hzero => hδvalue ((hEval _ (input.degree δ (label_sub b hδ)) hδon).mp hzero)
  · intro p hp hon
    classical
  unfold Data.points at hp
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hp
    have hvalueγ := (Finset.mem_filter.mp (heq ▸ hγ)).2
    exact (hEval _ (input.degree γ (label_sub b (demand_sub b hγ))) hon).mpr hvalueγ

theorem Data.pieces (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l) :
    ∃ (C : Pieces Γ) (B : Finset K), C.curves s ∧ (∀ i, 0<C.degree i) ∧
      (∀ γ∈Γ, hasBranch f Q l S (extend (s γ)) → γ ∈ C.union ∪ B) ∧
      2*C.total+B.card ≤ ∑ b∈D.branches, b.weight*(D.points b).card := by
  classical
  let branches := D.branches
  let labels := D.labels
  let demanded := D.demanded
  let demand_simple := D.demand_simple
  let points := D.points
  let points_card := D.points_card input
  let points_on := D.points_on input
  let points_next := D.points_next input
  let contains_label := D.label_on
  let label_sub := D.label_sub
  let demand_sub := D.demand_sub
  let demand_multiple := D.demand_multiple
  let simple := branches.filter Branch.Simple
  let multiple := branches.filter (fun b => ¬ b.Simple)
  let e := multiple.equivFin
  let C : Pieces Γ :=
    { n := multiple.card
      piece := fun i => labels (e.symm i).val
      subset := fun i => label_sub (e.symm i).val
      degree := fun i => (demanded (e.symm i).val).card }
  let B := simple.biUnion labels
  have hmultiple (i : Fin C.n) := Finset.mem_filter.mp (e.symm i).property
  refine ⟨C, B,
    fun i => (demand_multiple _ (hmultiple i).1 (hmultiple i).2).2.1,
    fun i => (demand_multiple _ (hmultiple i).1 (hmultiple i).2).1, ?_, ?_⟩
  · intro γ hγ hm
    obtain ⟨b,hb,hlabel⟩ := D.covered γ hγ hm
    by_cases hs : b.Simple
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨b, Finset.mem_filter.mpr ⟨hb, hs⟩, hlabel⟩)
    have hbm : b ∈ multiple := Finset.mem_filter.mpr ⟨hb, hs⟩
    apply Finset.mem_union_left _
    refine Finset.mem_biUnion.mpr ⟨e ⟨b, hbm⟩, Finset.mem_univ _, ?_⟩
    change γ ∈ labels (e.symm (e ⟨b, hbm⟩)).val
    simpa only [Equiv.symm_apply_apply] using hlabel
  · have htotal : C.total = ∑ b ∈ multiple, (demanded b).card := by
      calc
        C.total = ∑ b : multiple, (demanded b.val).card :=
          Equiv.sum_comp e.symm (fun b : multiple => (demanded b.val).card)
        _ = _ := by
          rw [Finset.univ_eq_attach]
          exact Finset.sum_attach multiple (fun b => (demanded b).card)
    have hsimple : (∑ b ∈ simple, b.weight * (points b).card) =
        ∑ b ∈ simple, (labels b).card := by
      apply Finset.sum_congr rfl
      intro b hb
      have hs := (Finset.mem_filter.mp hb).2
      rw [points_card, demand_simple b hs, Branch.weight, ite_eq_left hs, one_mul]
    have hmult : (∑ b ∈ multiple, b.weight * (points b).card) = 2 * C.total := by
      rw [htotal, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      have hs := (Finset.mem_filter.mp hb).2
      rw [points_card, Branch.weight, ite_eq_right hs]
    have hpart : (∑ b ∈ simple, b.weight * (points b).card) +
        (∑ b ∈ multiple, b.weight * (points b).card) =
        ∑ b ∈ branches, b.weight * (points b).card :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    have hB : B.card ≤ ∑ b ∈ simple, (labels b).card := Finset.card_biUnion_le
    have hpay : 2 * C.total + B.card ≤ ∑ b ∈ branches, b.weight * (points b).card := by
      rw [← hpart, hsimple, hmult, Nat.add_comm (∑ b ∈ simple, (labels b).card)]
      exact Nat.add_le_add_left hB _
    exact hpay

#print axioms Data.pieces
#print axioms Data.bent
end
end Low6966SharedTally

end Merged_R6960Low6966SharedTally

-- merged module R6960Low6966RetainedGeometry
section Merged_R6960Low6966RetainedGeometry

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000

namespace Low6966RetainedCut
noncomputable section

open P3 (K I)
open K1_13 (Row Shape InBox shape mixed32 chart)
open Low6966Prices (Messages tiltedFits tiltedSurface taylorLength)
open Low6966GeometryCut (CutInput MixedBound)
open Low6966GeometryCut (chargedPrice assemble_charge continued_bound)
open Low6966ActiveCycle (mixed)
open scoped Polynomial BigOperators

/-- The accepted physical charge with an arbitrary mixed surface budget. -/
def cutPrice (x : Shape) (l scale surface : ℕ) := chargedPrice x l scale surface

def fourSurface (p q : Shape) :=
  mixed32 p q (chart (taylorLength+1) p) (chart (taylorLength+2) p)

variable {w : I → K} {Γ : Finset K} {s : K → (Polynomial K)} {f Q : Row 4} {l : ℕ}

theorem smaller_tilted (hm : Messages w Γ s) (input : CutInput Γ s f Q l)
    (q : Shape) (hQ : InBox (shape Q) q) (hq : Low48BentLattice.Chamber (q,0))
    (hguard : tiltedFits (shape f)) :
    Γ.card ≤ cutPrice (shape f) l (60*32) (tiltedSurface (shape f).chamber q) := by
  let p := (shape f).chamber
  have hp := K1_13_7_1.shape_chamber f
  have ht : 1 ≤ p.t := input.small.2.1
  have hCh := Low6966SharedBentCaps.caps_chamber (p := p) hp.1 ht hguard.1 hq
  apply assemble_charge Low6966GeometryCut_1.proof continued_bound hm input (by decide : 0 < 60*32)
  apply Low6966ActiveCycle.mixed (R := Low48BentCycle.rawFamily (Low6966SharedBentCaps.caps p q))
    (B := Low48BentCycle.capFamily (Low6966SharedBentCaps.caps p q)) input Low6966SharedBentCaps.ordinary_doubled
  · exact Low48BentCycle.old_section ⟨le_max_left _ _,le_rfl,le_rfl⟩
  · exact Low48BentCycle.old_section hQ
  · exact Low6966SharedBentCaps.chart q ht
  · exact Low6966SharedBentCaps.ordinary_budget hCh

theorem smaller_four (hm : Messages w Γ s) (input : CutInput Γ s f Q l)
    (q : Shape) (hQ : InBox (shape Q) q) (hq : K1_13_6_2_3.ChamberBox q) :
    Γ.card ≤ cutPrice (shape f) l 32 (fourSurface (shape f).chamber q) := by
  classical
  let D : Low6966SharedTally.Data Γ s f Q l Set.univ := Low6966SharedTally.build Set.univ
  have h := Low6966SharedCycleFour.bound_with_cut K1_13_6_2_3_1.proof
    (K1_13_6_2_3_2.of_children
      K1_13_6_2_3_2_1.proof K1_13_6_2_3_2_2.proof K1_13_6_2_3_2_3.proof
      K1_13_6_2_3_2_4.proof K1_13_6_2_3_2_5.proof K1_13_6_2_3_2_6.proof)
    (K1_13_6_2_3_3.of_children K1_13_6_2_3_3_1.proof
      (K1_13_6_2_3_3_2.of_children K1_13_6_2_3_3_2_1.proof K1_13_6_2_3_3_2_2.proof))
    f Q Q l input.small input.proper q hq hQ (fun _ => l)
    D.branches D.points (D.four input) (fun b _ => ⟨b.base,b.high⟩)
  have hh := (le_div_iff₀ (by norm_num : (0:ℚ)<32)).mp h
  have hn : 32*l*(∑ b∈D.branches, b.weight*(D.points b).card) ≤ fourSurface (shape f).chamber q := by
    apply (Nat.cast_le (α := ℚ)).mp
    simp only [fourSurface,Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat]
    simpa only [Nat.cast_mul,← Finset.mul_sum,mul_comm (32:ℚ),mul_assoc,mul_left_comm] using hh
  apply assemble_charge Low6966GeometryCut_1.proof continued_bound hm input (by decide : 0 < 32)
  obtain ⟨C,B,hcurve,hpos,hcover,hcost⟩ := D.pieces input
  refine ⟨C,B,hcurve,hpos,?_,(Nat.mul_le_mul_left (32*l) hcost).trans hn⟩
  intro γ hγ hmixed
  obtain ⟨b,hb⟩ := Low6966GeometryCut_2.branch_of_mixed hmixed
  exact hcover γ hγ ⟨b,Set.mem_univ _,hb⟩

#print axioms smaller_tilted
#print axioms smaller_four

end
end Low6966RetainedCut

end Merged_R6960Low6966RetainedGeometry

-- merged module R6960Low6966RetainedAssembly
section Merged_R6960Low6966RetainedAssembly

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
namespace Low6966RetainedCut
noncomputable section

open P3 (I K)
open K1_13 (Geom Row Shape shape InBox OrderAt atJet extend)
open Low6966Prices (primaryBox primaryCutoff TrueWeightLE ActiveFits SmallFactor Messages
  tiltedFits tiltedSurface physicalPrice ProperCut)
open scoped Polynomial BigOperators

def chamberHull (x : Shape) : Shape := ⟨max x.b x.j,x.j,min x.t (x.j/3)⟩

theorem hull_includes {Q : Row 4} {x : Shape} (hb : InBox (shape Q) x) :
    InBox (shape Q) (chamberHull x) := by
  have h := (K1_13_7_1.shape_chamber Q).2
  change 3*(shape Q).t ≤ (shape Q).j at h
  exact ⟨hb.1.trans (le_max_left _ _),hb.2.1, le_min hb.2.2 (by have := hb.2.1; omega)⟩

theorem hull_valid (x : Shape) : Low48BentLattice.Chamber (chamberHull x,0) := by
  refine ⟨le_max_right _ _,?_,Nat.zero_le _⟩
  change 3*min x.t (x.j/3) ≤ x.j
  have := min_le_right x.t (x.j/3)
  omega

def contractedPrice (x h : Shape) (l active : ℕ) : ℕ :=
  let q := chamberHull (residualBox h l)
  let old := physicalPrice x l active
  let four := if 0 < q.t then min old (cutPrice x l 32 (fourSurface x.chamber q)) else old
  if tiltedFits x then min four (cutPrice x l (60*32) (tiltedSurface x.chamber q)) else four

/-- Physical count for the actual extremal bank witness and the selected (off-retained) marks. -/
theorem price_of_witness_floor {w : I → K} {Γ : Finset K} {s : K → (Polynomial K)} {P H f : Row 4}
    {k a l active : ℕ} (hm : Messages w Γ s) (hsmall : SmallFactor f)
    (hactive : ActiveFits f active) (hchar : f.degreeOf 3 < K1.p)
    (hon : ∀ γ∈Γ, K1_13.OnFactor f (extend (s γ)))
    (hoff : ∀ γ∈Γ, atJet H (extend (s γ)) ≠ 0)
    (hP : P ≠ 0) (hH : H ≠ 0) (hc : IsRelPrime f H) (hpos : 0 < l) (hl : l ≤ k-a)
    (hbox : InBox (shape P) primaryBox) (hweight : TrueWeightLE P primaryCutoff)
    (htaper : ActiveFits P 5164) (hord : ∀ γ∈Γ, OrderAt P (extend (s γ)) k)
    (divH : H^k ∣ P) (divF : f^a ∣ P) (exactF : ¬ f^(a+1) ∣ P) :
    ∀ h : Shape, InBox h (shape H) → Γ.card ≤ contractedPrice (shape f) h l active := by
  intro h hfloor
  obtain ⟨Q,hproper,hboxQ,hweightQ,hactiveQ,horderQ⟩ :=
    exists_divided_cut hP hH hsmall.1 hsmall.2.1 hchar hc hl hbox hweight htaper divH divF exactF
  have hQP : InBox (shape Q) primaryBox :=
    ⟨hboxQ.1.trans (Nat.sub_le _ _), hboxQ.2.1.trans (Nat.sub_le _ _),
      hboxQ.2.2.trans (Nat.sub_le _ _)⟩
  have horder (γ) (hγ : γ∈Γ) := horderQ _ (hoff γ hγ) (hord γ hγ)
  have hfloorQ : InBox (shape Q) (residualBox h l) :=
    ⟨hboxQ.1.trans (Nat.sub_le_sub_left (Nat.mul_le_mul_left l hfloor.1) _),
      hboxQ.2.1.trans (Nat.sub_le_sub_left (Nat.mul_le_mul_left l hfloor.2.1) _),
      hboxQ.2.2.trans (Nat.sub_le_sub_left (Nat.mul_le_mul_left l hfloor.2.2) _)⟩
  let q := chamberHull (residualBox h l)
  have hQ : InBox (shape Q) q := hull_includes hfloorQ
  have hch := hull_valid (residualBox h l)
  have input : Low6966GeometryCut.CutInput Γ s f Q l :=
    ⟨hm.distinct,hm.degree,hsmall,hon,hpos,hproper,hQP,hweightQ,horder⟩
  have hold := Low6966ActiveCycle.proof w Γ s hm f hsmall active hactive hon l hpos
    ⟨Q,hproper,hQP,hweightQ,hactiveQ,horder⟩
  have hfour : Γ.card ≤ (if 0 < q.t then min (physicalPrice (shape f) l active)
      (cutPrice (shape f) l 32 (fourSurface (shape f).chamber q)) else physicalPrice (shape f) l active) := by
    split
    next ht => exact le_min hold (smaller_four hm input q hQ ⟨hch.1,hch.2.1,ht⟩)
    next => exact hold
  unfold contractedPrice
  split
  next hg => exact le_min hfour (smaller_tilted hm input q hQ hch hg)
  next => exact hfour

/-- Physical count for the actual extremal bank witness and the selected (off-retained) marks. -/
theorem price_of_witness {w : I → K} {Γ : Finset K} {s : K → (Polynomial K)} {P H f : Row 4}
    {k a l active : ℕ} (hm : Messages w Γ s) (hsmall : SmallFactor f)
    (hactive : ActiveFits f active) (hchar : f.degreeOf 3 < K1.p)
    (hon : ∀ γ∈Γ, K1_13.OnFactor f (extend (s γ)))
    (hoff : ∀ γ∈Γ, atJet H (extend (s γ)) ≠ 0)
    (hP : P ≠ 0) (hH : H ≠ 0) (hc : IsRelPrime f H) (hpos : 0 < l) (hl : l ≤ k-a)
    (hbox : InBox (shape P) primaryBox) (hweight : TrueWeightLE P primaryCutoff)
    (htaper : ActiveFits P 5164) (hord : ∀ γ∈Γ, OrderAt P (extend (s γ)) k)
    (divH : H^k ∣ P) (divF : f^a ∣ P) (exactF : ¬ f^(a+1) ∣ P) :
    Γ.card ≤ contractedPrice (shape f) (shape H) l active :=
  price_of_witness_floor hm hsmall hactive hchar hon hoff hP hH hc hpos hl hbox hweight
    htaper hord divH divF exactF (shape H) ⟨le_rfl,le_rfl,le_rfl⟩

#print axioms price_of_witness_floor
#print axioms price_of_witness

end
end Low6966RetainedCut

end Merged_R6960Low6966RetainedAssembly

end Merged6967_Low6966RetainedAssembly

section Merged6967_R6960Low6960FastPrice
set_option Elab.async false





set_option Elab.async false

-- merged module R6960Low6960TiltedRectangle
section Merged_R6960Low6960TiltedRectangle

-- merged module R6960Low6960SurfaceLinearFive
section Merged_R6960Low6960SurfaceLinearFive

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 800000

namespace Low6960SharedPrice

open K1_13 (Shape)
open K1_13_8 (Valid)
open Low6960Prices (BentCap addBent bentIntegral bentGraph bentLift taylorLength tiltedFits)
open Low48BentLattice (Chamber)

open Final50SharedPrice (signedFive signed_five_linear signed_five_nonneg)

/-- The tilted signed surface is linear in the cutter shape. Chamber positivity
also certifies the exact natural-number coefficients in the price ledger. -/
theorem surface_tilted_eq_weights {f : Shape} (hf : Valid f) (ht : tiltedFits f) (q : Shape) :
    surface .tilted f q = (weights .tilted f).b*q.b + (weights .tilted f).j*q.j +
      (weights .tilted f).t*q.t := by
  let p := f.chamber
  let g := bentGraph p
  let l := bentLift (taylorLength-4) p
  let r := bentLift (taylorLength-3) p
  have hb : p.j ≤ p.b := le_max_right _ _
  have hp : Chamber (p,0) := ⟨hb,hf.2.1,Nat.zero_le _⟩
  have hg : Chamber g := Low48BentSupport.graph_chamber hf.1 ht.1
  have hl : Chamber l := Low48BentSupport.lifted_chamber hb ht.1 (by decide : 3 ≤ taylorLength-4)
  have hr : Chamber r := Low48BentSupport.lifted_chamber hb ht.1 (by decide : 3 ≤ taylorLength-3)
  have hnonneg (u : Shape) : 0 ≤ signedFive (p,0) (u,0) g l r :=
    signed_five_nonneg u _ _ _ _ hp hg hl hr
  refine surface_eq_weights_of_signed .tilted f _ _ _ (hnonneg ⟨1,0,0⟩)
    (hnonneg ⟨0,1,0⟩) (hnonneg ⟨0,0,1⟩) (fun u => ?_) q
  change (↑(signedFive (p,0) (u,0) g l r).toNat : ℤ) = _
  rw [Int.toNat_of_nonneg (hnonneg u)]
  exact signed_five_linear u _ _ _ _

#print axioms surface_tilted_eq_weights
end Low6960SharedPrice

end Merged_R6960Low6960SurfaceLinearFive

-- merged module R6960Low6960WidthAffine
section Merged_R6960Low6960WidthAffine

set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Low6960WidthAffine
open K1_13 (Shape)
open Low6960Prices (BentCap addBent bentIntegral ambientMix tiltedSurface tiltedFits
  bentGraph bentLift taylorLength)
open Final50SharedPrice (signedFive signed_five_nonneg)

private abbrev Slot := BentCap × ℕ
private def atWidth (x : ℕ) (s : Slot) : BentCap :=
  (⟨s.1.1.b+x*s.2,s.1.1.j,s.1.1.t⟩,s.1.2)
private def add (a b : Slot) : Slot := (addBent a.1 b.1,a.2+b.2)
private def zero : Slot := ((⟨0,0,0⟩,0),0)

private theorem at_add (x : ℕ) (a b : Slot) :
    atWidth x (add a b) = addBent (atWidth x a) (atWidth x b) := by
  simp only [atWidth,add,addBent,Shape.plus,Prod.mk.injEq,Shape.mk.injEq,and_true]
  ring

private theorem fold_slots (x : ℕ) (s : List Slot) :
    (s.map (atWidth x)).foldl addBent (⟨0,0,0⟩,0) = atWidth x (s.foldl add zero) := by
  change (s.map (atWidth x)).foldl addBent (atWidth x zero) = _
  rw [List.foldl_map]
  exact List.foldl_hom (atWidth x) (fun a b => (at_add x a b).symm)

private def raw (s : List BentCap) : ℤ :=
  s.sublists.foldl (fun acc boxes =>
    let p := boxes.foldl addBent (⟨0,0,0⟩,0)
    acc + (-1 : ℤ) ^ (5-boxes.length) * bentIntegral p.1.b p.1.j p.1.t p.2) 0

private theorem integral_affine (B x W J T H : ℤ) :
    bentIntegral (B+x*W) J T H = bentIntegral B J T H + x *
      (bentIntegral (B+W) J T H-bentIntegral B J T H) := by
  simp only [bentIntegral]
  ring

private def integralTerm (boxes : List Slot) (x : ℕ) : ℤ :=
  let p := atWidth x (boxes.foldl add zero)
  (-1 : ℤ) ^ (5-boxes.length) * bentIntegral p.1.b p.1.j p.1.t p.2

private theorem term_affine (boxes : List Slot) (x : ℕ) :
    integralTerm boxes x = integralTerm boxes 0 + (x : ℤ) *
      (integralTerm boxes 1-integralTerm boxes 0) := by
  simp only [integralTerm, atWidth, Nat.cast_add, Nat.cast_mul, zero_mul, one_mul, add_zero, integral_affine]
  ring

private theorem raw_eq_sum (s : List Slot) (x : ℕ) :
    raw (s.map (atWidth x)) = (s.sublists.map (fun a => integralTerm a x)).sum := by
  simp only [raw,List.sublists_map,List.sum_eq_foldl]
  rw [List.foldl_map,List.foldl_map]
  simp only [fold_slots,List.length_map,integralTerm]

private theorem raw_affine (s : List Slot) (x : ℕ) :
    raw (s.map (atWidth x)) = raw (s.map (atWidth 0)) + (x : ℤ) *
      (raw (s.map (atWidth 1))-raw (s.map (atWidth 0))) := by
  simp only [raw_eq_sum]
  generalize s.sublists = rows
  induction rows with
  | nil => simp
  | cons boxes rows ih =>
    simp only [List.map_cons,List.sum_cons,term_affine boxes x,ih]
    ring

private def slots (j t : ℕ) (q : Shape) : List Slot :=
  let p : Shape := ⟨j+1,j,t⟩
  [((p,0),1), ((q,0),0), (bentGraph p,1),
    (bentLift (taylorLength-4) p,taylorLength-4),
    (bentLift (taylorLength-3) p,taylorLength-3)]

private theorem map_slots (j t x : ℕ) (q : Shape) :
    (slots j t q).map (atWidth x) =
      let p : Shape := ⟨j+1+x,j,t⟩
      [(p,0),(q,0),bentGraph p,bentLift (taylorLength-4) p,bentLift (taylorLength-3) p] := by
  simp [slots, atWidth, bentGraph, bentLift, Nat.add_mul, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm, Nat.mul_comm]

private theorem raw_nonneg (j t x : ℕ) (q : Shape) (ht : 1≤t) (hj : 3*t+3≤j) :
    0 ≤ raw ((slots j t q).map (atWidth x)) := by
  rw [map_slots]
  let p : Shape := ⟨j+1+x,j,t⟩
  have hb : p.j ≤ p.b := by dsimp [p]; omega
  change 0 ≤ signedFive (p,0) (q,0) (bentGraph p) (bentLift (taylorLength-4) p)
    (bentLift (taylorLength-3) p)
  have hch : 3*p.t≤p.j := by dsimp [p]; omega
  exact signed_five_nonneg _ _ _ _ _ ⟨hb,hch,Nat.zero_le _⟩
    (Low48BentSupport.graph_chamber ht hj)
    (Low48BentSupport.lifted_chamber hb hj (by decide))
    (Low48BentSupport.lifted_chamber hb hj (by decide))

/-- Within one index and top degree, the tilted surface increases with width. -/
theorem tilted_width_mono (q : Shape) {b B j t : ℕ} (hb : j+1≤b) (hB : b≤B)
    (ht : 1≤t) (hj : 3*t+3≤j) :
    tiltedSurface (⟨b,j,t⟩ : Shape).chamber q ≤ tiltedSurface (⟨B,j,t⟩ : Shape).chamber q := by
  let s := slots j t q
  let f (x : ℕ) := raw (s.map (atWidth x))
  have ha (x : ℕ) : f x = f 0 + (x : ℤ) * (f 1-f 0) := raw_affine s x
  have hp (x : ℕ) : 0≤f x := raw_nonneg j t x q ht hj
  have hs : 0≤f 1-f 0 := by
    by_contra! h
    have hle : f 1-f 0 ≤ -1 := by omega
    let wid := (f 0).toNat+1
    have hwid : (wid : ℤ)=f 0+1 := by simp [wid,Int.toNat_of_nonneg (hp 0)]
    have hmul := mul_le_mul_of_nonneg_left hle (Int.natCast_nonneg wid)
    have hx := hp wid
    rw [ha wid,hwid] at hx
    rw [hwid] at hmul
    simp only [mul_neg,mul_one] at hmul
    omega
  have hr (a : ℕ) (h : j+1≤a) :
      tiltedSurface (⟨a,j,t⟩ : Shape).chamber q = (f (a-(j+1))).toNat := by
    have hmax : max a j = a := max_eq_left (by omega)
    have eq : j+1+(a-(j+1))=a := Nat.add_sub_of_le h
    simp only [f,s,map_slots,eq,tiltedSurface,Shape.chamber,hmax,ambientMix,raw]
  rw [hr _ hb,hr _ (hb.trans hB)]
  apply Int.toNat_le_toNat
  rw [ha (b-(j+1)),ha (B-(j+1))]
  have hw : ((b-(j+1) : ℕ) : ℤ) ≤ ((B-(j+1) : ℕ) : ℤ) := by
    exact_mod_cast Nat.sub_le_sub_right hB (j+1)
  exact add_le_add (le_refl (f 0)) (mul_le_mul_of_nonneg_right hw hs)

#print axioms tilted_width_mono
end Low6960WidthAffine

end Merged_R6960Low6960WidthAffine

-- merged module R6960Low6960TiltedRectangle
section Merged_R6960Low6960TiltedRectangle

set_option Elab.async false
set_option maxRecDepth 2400
namespace Low6960Rectangle
open K1_13 (Shape InBox)
open Low6960RetainedCut (cutPrice contractedPrice)
open Low6960Prices (tiltedSurface tiltedFits)
open Low6960Allocation (Band MassCell start order allowance weight_mono order_mono)

/-- A tilted-surface price certificate for a width interval of one index and degree. -/
def PaidTilted {k : Band} (cells : List (MassCell k)) (t b j B l : ℕ) : Prop :=
  0<l ∧ l≤order cells ⟨b,j,0⟩ ∧ 1≤t ∧ 3*t+3≤j ∧ j+1≤b ∧
    cutPrice ⟨B,j,t⟩ l 1920 (tiltedSurface (⟨B,j,t⟩ : Shape).chamber (hullOf k l)) ≤
      allowance k ((start k).t+t) b j t

instance {k : Band} (cells : List (MassCell k)) (t b j B l : ℕ) :
    Decidable (PaidTilted cells t b j B l) := inferInstanceAs (Decidable (_ ∧ _))

theorem tilted {k : Band} {cells : List (MassCell k)} {a : Shape} {b j B t l : ℕ}
    (h : PaidTilted cells t b j B l) (hb : b≤a.b) (hB : a.b≤B)
    (hj : a.j=j) (ht : a.t=t) :
    ∃ l, 0<l ∧ l≤order cells a ∧ contractedPrice a (start k) l 169≤
      allowance k ((start k).t+a.t) a.b a.j a.t := by
  obtain ⟨lp,lo,ht',hj',hw,fee⟩ := h
  cases a with
  | mk a d z =>
    change d=j at hj
    change z=t at ht
    subst d z
    have geom : tiltedFits ⟨a,j,t⟩ := ⟨hj',hw.trans hb⟩
    have hprice : contractedPrice ⟨a,j,t⟩ (start k) l 169 ≤
        cutPrice ⟨a,j,t⟩ l 1920 (tiltedSurface (⟨a,j,t⟩ : Shape).chamber (hullOf k l)) := by
      unfold contractedPrice
      dsimp only
      rw [ite_eq_left geom]
      exact min_le_right _ _
    have ha : 3*t≤j := by omega
    have mono := Low6960WidthAffine.tilted_width_mono (hullOf k l) (hw.trans hb) hB ht' hj'
    have hcut : cutPrice ⟨a,j,t⟩ l 1920 (tiltedSurface (⟨a,j,t⟩ : Shape).chamber (hullOf k l)) ≤
        cutPrice ⟨B,j,t⟩ l 1920 (tiltedSurface (⟨B,j,t⟩ : Shape).chamber (hullOf k l)) := by
      have box : InBox ⟨a,j,t⟩ ⟨B,j,t⟩ := ⟨hB,le_rfl,le_rfl⟩
      rw [cut_eq,cut_eq]
      exact charge_mono box ha ha l 1920 mono
    exact ⟨l,lp,lo.trans (order_mono cells hb le_rfl), hprice.trans
      (hcut.trans (fee.trans (Nat.div_le_div_right
        (Nat.mul_le_mul_left _ (weight_mono k hb le_rfl le_rfl)))))⟩

#print axioms tilted
end Low6960Rectangle

end Merged_R6960Low6960TiltedRectangle

end Merged_R6960Low6960TiltedRectangle

-- merged module R6960Low6960FastPrice
section Merged_R6960Low6960FastPrice

-- merged module R6960Low6960WeightedRate
section Merged_R6960Low6960WeightedRate

set_option Elab.async false

namespace Low6960WeightedRate
open K1_13 (Shape)
open Low6960SharedPrice (Rate weights)

abbrev unit : ℕ := 1000000000
abbrev split : ℕ := 10

def boxFee (w x : Shape) : ℕ := w.b * max x.b x.j + w.j * x.j + w.t * min x.t (x.j / 3)
def sepBox (x : Shape) : Shape := ⟨x.b - 1, x.j - 3, x.t - 1⟩
def charge (r a d e : ℕ) : ℕ := e * (24 * (r - e*a) + d * (e - 1))

structure Envelope where
  widthLow : ℕ
  indexLow : ℕ
  topLow : ℕ
  widthHigh : ℕ
  indexHigh : ℕ
  taperLow : ℕ
  taperHigh : ℕ
  coeff : Shape
  sep : ℕ

def Fits (p : Envelope) (x : Shape) : Prop :=
  p.widthLow ≤ x.b ∧ x.b ≤ p.widthHigh ∧ p.indexLow ≤ x.j ∧ x.j ≤ p.indexHigh ∧
    p.topLow ≤ x.t ∧ p.taperLow ≤ 26*x.b ∧ min (26*x.b+25*x.j) (x.b+25*169) ≤ p.taperHigh

def RayBounds (p : Envelope) (x : Shape) (amount : ℕ) : Prop :=
  let w := weights .tilted x
  let scale := 1920*amount
  unit*w.b ≤ scale*p.coeff.b ∧
    unit*(w.b+w.j) ≤ scale*(p.coeff.b+p.coeff.j) ∧
    unit*(3*(w.b+w.j)+w.t) ≤ scale*(3*(p.coeff.b+p.coeff.j)+p.coeff.t) ∧
    unit*boxFee w (sepBox x) ≤ scale*p.sep

def Pays (p : Envelope) (x : Shape) (u : Rate) : Prop :=
  Fits p x ∧ u.kind = .tilted ∧ u.split = split ∧ 0 < u.amount ∧ Low6960Prices.tiltedFits x ∧
    RayBounds p x u.amount

instance (p : Envelope) (x : Shape) (u : Rate) : Decidable (Pays p x u) := by
  unfold Pays Fits RayBounds
  infer_instance

def first : Envelope := ⟨106,48,4,132,53,2756,4257,⟨4886433,26118015,6676780⟩,1966580209⟩

def Allowed (x : Shape) (u : Rate) : Prop :=
  Low6960SharedPrice.RateFits x u ∨ Pays first x u

instance (x : Shape) (u : Rate) : Decidable (Allowed x u) := by unfold Allowed; infer_instance

private theorem ray_expansion (w : Shape) (b j t : ℕ) (hb : j ≤ b) (ht : 3*t ≤ j) :
    w.b*b+w.j*j+w.t*t = w.b*(b-j)+(w.b+w.j)*(j-3*t)+(3*(w.b+w.j)+w.t)*t := by
  let B := b-j
  let J := j-3*t
  change w.b*b+w.j*j+w.t*t = w.b*B+(w.b+w.j)*J+(3*(w.b+w.j)+w.t)*t
  have hB : b = B+J+3*t := by dsimp [B,J]; omega
  have hJ : j = J+3*t := by dsimp [J]; omega
  rw [hB, hJ]
  ring

theorem fee_le {p : Envelope} {x : Shape} {amount : ℕ} (h : RayBounds p x amount) (y : Shape) :
    unit * boxFee (weights .tilted x) y ≤ (1920 * amount) * boxFee p.coeff y := by
  let b := max y.b y.j
  let j := y.j
  let t := min y.t (y.j/3)
  let w := weights .tilted x
  have hb : j ≤ b := le_max_right _ _
  have ht : 3*t ≤ j := by
    have hd : t ≤ y.j/3 := min_le_right _ _
    dsimp only [j]
    omega
  change unit*(w.b*b+w.j*j+w.t*t) ≤ (1920*amount)*(p.coeff.b*b+p.coeff.j*j+p.coeff.t*t)
  rw [ray_expansion w b j t hb ht, ray_expansion p.coeff b j t hb ht]
  calc
    _ = (unit*w.b)*(b-j) + (unit*(w.b+w.j))*(j-3*t) + (unit*(3*(w.b+w.j)+w.t))*t := by ring
    _ ≤ _ := by
      rw [show (1920*amount)*(p.coeff.b*(b-j)+(p.coeff.b+p.coeff.j)*(j-3*t)+
          (3*(p.coeff.b+p.coeff.j)+p.coeff.t)*t) =
          ((1920*amount)*p.coeff.b)*(b-j) + ((1920*amount)*(p.coeff.b+p.coeff.j))*(j-3*t) +
          ((1920*amount)*(3*(p.coeff.b+p.coeff.j)+p.coeff.t))*t by ring]
      exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right _ h.1) (Nat.mul_le_mul_right _ h.2.1))
        (Nat.mul_le_mul_right _ h.2.2.1)

theorem transfer {p : Envelope} {x : Shape} {u : Rate} (h : Pays p x u) (y : Shape) (r a d e : ℕ)
    (hp : (split+1-e)*(24*boxFee p.coeff y+d*p.sep) ≤ split*unit*charge r a d e) :
    (u.split+1-e)*(24*boxFee (weights u.kind x) y+d*boxFee (weights u.kind x) (sepBox x)) ≤
      (Low6960SharedPrice.surfaceScale u.kind*(u.split*u.amount))*charge r a d e := by
  obtain ⟨_, hk, hs, _, _, hw⟩ := h
  rw [hk, hs]
  let w := weights .tilted x
  let z := 24*boxFee w y+d*boxFee w (sepBox x)
  let cap := 1920*u.amount
  let bound := 24*boxFee p.coeff y+d*p.sep
  have hz : unit*z ≤ cap*bound := by
    calc
      _ = 24*(unit*boxFee w y)+d*(unit*boxFee w (sepBox x)) := by dsimp [z]; ring
      _ ≤ 24*(cap*boxFee p.coeff y)+d*(cap*p.sep) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ (fee_le hw y)) (Nat.mul_le_mul_left _ hw.2.2.2)
      _ = _ := by dsimp [bound]; ring
  change (split+1-e)*z ≤ (1920*(split*u.amount))*charge r a d e
  apply Nat.le_of_mul_le_mul_left _ (by decide : 0 < unit)
  calc
    unit*((split+1-e)*z) = (split+1-e)*(unit*z) := by ring
    _ ≤ (split+1-e)*(cap*bound) := Nat.mul_le_mul_left _ hz
    _ = cap*((split+1-e)*bound) := by ring
    _ ≤ cap*(split*unit*charge r a d e) := Nat.mul_le_mul_left _ hp
    _ = _ := by dsimp [cap]; ring

#print axioms transfer
end Low6960WeightedRate

end Merged_R6960Low6960WeightedRate

-- merged module R6960Low6960FastPrice
section Merged_R6960Low6960FastPrice
set_option autoImplicit false
set_option Elab.async false
namespace Low6960FastPrice
open K1_13 (Shape mixed32 volume32 difference chart liftedChart ceilDiv)
open Low6960Prices (BentCap bentIntegral addBent ambientMix tiltedSurface bentGraph bentLift
  taylorLength primaryBox errors incidenceGap physicalDegree tiltedFits activeFitsPrice activeLoss
  activeClips surfaceNumerator32 physicalPriceOld physicalPriceWith physicalPriceTilted
  physicalPriceActive physicalPrice tiltedSurfaceActive)
def mixPos (pb pj pt qb qj qt rb rj rt sb sj st : ℕ) : ℕ :=
  16 * pb * qj * rj * st +
    16 * pb * qj * rt * sj +
    16 * pb * qt * rj * sj +
    144 * pb * qt * rt * st +
    16 * pj * qb * rj * st +
    16 * pj * qb * rt * sj +
    16 * pj * qj * rb * st +
    16 * pj * qj * rt * sb +
    56 * pj * qj * rt * st +
    16 * pj * qt * rb * sj +
    16 * pj * qt * rj * sb +
    56 * pj * qt * rj * st +
    56 * pj * qt * rt * sj +
    16 * pt * qb * rj * sj +
    144 * pt * qb * rt * st +
    16 * pt * qj * rb * sj +
    16 * pt * qj * rj * sb +
    56 * pt * qj * rj * st +
    56 * pt * qj * rt * sj +
    144 * pt * qt * rb * st +
    56 * pt * qt * rj * sj +
    144 * pt * qt * rt * sb +
    216 * pt * qt * rt * st
def mixNeg (pb pj pt qb qj qt rb rj rt sb sj st : ℕ) : ℕ :=
  48 * pb * qj * rt * st +
    48 * pb * qt * rj * st +
    48 * pb * qt * rt * sj +
    48 * pj * qb * rt * st +
    24 * pj * qj * rj * st +
    24 * pj * qj * rt * sj +
    48 * pj * qt * rb * st +
    24 * pj * qt * rj * sj +
    48 * pj * qt * rt * sb +
    120 * pj * qt * rt * st +
    48 * pt * qb * rj * st +
    48 * pt * qb * rt * sj +
    48 * pt * qj * rb * st +
    24 * pt * qj * rj * sj +
    48 * pt * qj * rt * sb +
    120 * pt * qj * rt * st +
    48 * pt * qt * rb * sj +
    48 * pt * qt * rj * sb +
    120 * pt * qt * rj * st +
    120 * pt * qt * rt * sj
def mix4 (pb pj pt qb qj qt rb rj rt sb sj st : ℕ) : ℕ :=
  mixPos pb pj pt qb qj qt rb rj rt sb sj st - mixNeg pb pj pt qb qj qt rb rj rt sb sj st
def mixF (p q r s : Shape) : ℕ :=
  mix4 p.b p.j p.t q.b q.j q.t r.b r.j r.t s.b s.j s.t
theorem mixF_eq (p q r s : Shape) : mixF p q r s = mixed32 p q r s := by
  obtain ⟨pb,pj,pt⟩ := p
  obtain ⟨qb,qj,qt⟩ := q
  obtain ⟨rb,rj,rt⟩ := r
  obtain ⟨sb,sj,st⟩ := s
  have key : difference (difference (difference (difference volume32 ⟨pb,pj,pt⟩) ⟨qb,qj,qt⟩)
      ⟨rb,rj,rt⟩) ⟨sb,sj,st⟩ ⟨0,0,0⟩ = (mixPos pb pj pt qb qj qt rb rj rt sb sj st : ℤ) -
        (mixNeg pb pj pt qb qj qt rb rj rt sb sj st : ℤ) := by
    simp only [difference, volume32, K1_13.Shape.plus, mixPos, mixNeg]
    push_cast
    ring
  unfold mixF mix4 mixed32
  dsimp only
  rw [key]
  omega
def bentPos (B J T H : ℕ) : ℕ :=
  H * (160*T^2*H^2 + 540*T^4 + 960*J*H^3 + 960*J*T^2*H + 840*J^2*T^2 + 240*J^3*H +
    640*B*T*H^2 + 1440*B*T^3 + 640*B*J*H^2 + 960*B*J*T*H + 480*B*J^2*T)
def bentNeg (B J T H : ℕ) : ℕ :=
  H * (576*H^4 + 480*T^3*H + 320*J*T*H^2 + 1200*J*T^3 + 480*J^2*H^2 + 480*J^2*T*H +
    240*J^3*T + 960*B*H^3 + 1440*B*T^2*H + 1440*B*J*T^2 + 480*B*J^2*H)
theorem bent_eq (B J T H : ℕ) :
    bentIntegral B J T H = (bentPos B J T H : ℤ) - (bentNeg B J T H : ℤ) := by
  simp only [bentIntegral, bentPos, bentNeg]
  push_cast
  ring
def mixStep (acc : ℕ × ℕ) (boxes : List BentCap) : ℕ × ℕ :=
  let s := boxes.foldl addBent (⟨0,0,0⟩, 0)
  let a := bentPos s.1.b s.1.j s.1.t s.2
  let n := bentNeg s.1.b s.1.j s.1.t s.2
  if (5 - boxes.length) % 2 = 0 then (acc.1 + a, acc.2 + n) else (acc.1 + n, acc.2 + a)
def ambientMixF (caps : List BentCap) : ℕ :=
  let r := caps.sublists.foldl mixStep (0,0)
  r.1 - r.2
private theorem fold_eq (Ls : List (List BentCap)) (a : ℤ) (acc : ℕ × ℕ)
    (h : a = acc.1 - acc.2) :
    Ls.foldl (fun acc boxes =>
      let s := boxes.foldl addBent (⟨0,0,0⟩, 0)
      acc + (-1 : ℤ) ^ (5 - boxes.length) * bentIntegral s.1.b s.1.j s.1.t s.2) a =
      ((Ls.foldl mixStep acc).1 : ℤ) - (Ls.foldl mixStep acc).2 := by
  induction Ls generalizing a acc with
  | nil => simpa using h
  | cons boxes rest ih =>
    simp only [List.foldl_cons]
    apply ih
    rw [bent_eq, h, neg_one_pow_eq_pow_mod_two]
    rcases Nat.mod_two_eq_zero_or_one (5 - boxes.length) with e | e
    · simp only [mixStep, e, ↓reduceIte, pow_zero, one_mul]
      push_cast; ring
    · simp only [mixStep, e, Nat.one_ne_zero, ↓reduceIte, pow_one]
      push_cast; ring
theorem ambientMix_eq (caps : List BentCap) : ambientMix caps = ambientMixF caps := by
  have key := fold_eq caps.sublists 0 (0,0) (by simp)
  unfold ambientMix ambientMixF
  dsimp only at key ⊢
  rw [key]
  omega
def tiltF (p q : Shape) : ℕ :=
  ambientMixF [(p, 0), (q, 0), bentGraph p,
    bentLift (taylorLength - 4) p, bentLift (taylorLength - 3) p]
theorem tiltF_eq (p q : Shape) : tiltF p q = tiltedSurface p q := by
  unfold tiltF tiltedSurface
  rw [ambientMix_eq]
def surfaceNumerator32F (p q : Shape) : ℕ :=
  let L := taylorLength
  let g : Shape := ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
  let a := liftedChart (L + 1) p
  let b := liftedChart (L + 2) p
  min (mixF p q (chart (L + 1) p) (chart (L + 2) p))
    (mixF p q a b + (L + 1) * mixF p q g b + (L + 2) * mixF p q g a)
def physicalPriceOldF (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv (surfaceNumerator32F p q) 32 +
    ceilDiv ((errors + 2 * incidenceGap) * x.b * q.b * (chart (taylorLength + 1) p).b)
      incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixF p q auxBox h + 2 * x.t * mixF p p p h
  let points := mixF p q auxBox p + 2 * x.t * mixF p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (errors * curves + 2 * incidenceGap * points) (32 * incidenceGap)
def physicalPriceWithF (x : Shape) (l surface : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv surface (60 * 32) +
    ceilDiv ((errors + 2 * incidenceGap) * x.b * q.b * (chart (taylorLength + 1) p).b)
      incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixF p q auxBox h + 2 * x.t * mixF p p p h
  let points := mixF p q auxBox p + 2 * x.t * mixF p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (errors * curves + 2 * incidenceGap * points) (32 * incidenceGap)
def physicalPriceF (x : Shape) (l K : ℕ) : ℕ :=
  if tiltedFits x then
    let base := min (physicalPriceOldF x l) (physicalPriceWithF x l (tiltF x.chamber primaryBox))
    if activeFitsPrice x K then
      min base (physicalPriceWithF x l (tiltF x.chamber primaryBox - activeLoss (activeClips x.chamber K)))
    else base
  else physicalPriceOldF x l
theorem physicalPriceOldF_eq (x : Shape) (l : ℕ) : physicalPriceOldF x l = physicalPriceOld x l := by
  simp only [physicalPriceOldF, physicalPriceOld, surfaceNumerator32F, surfaceNumerator32, mixF_eq]
theorem physicalPriceWithF_eq (x : Shape) (l s : ℕ) : physicalPriceWithF x l s = physicalPriceWith x l s := by
  simp only [physicalPriceWithF, physicalPriceWith, mixF_eq]
theorem physicalPriceF_eq (x : Shape) (l K : ℕ) : physicalPriceF x l K = physicalPrice x l K := by
  simp only [physicalPriceF, physicalPrice, physicalPriceTilted, physicalPriceActive,
    tiltedSurfaceActive, physicalPriceOldF_eq, physicalPriceWithF_eq, tiltF_eq]
def chargeF (x : Shape) (l scale S : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let numerator := ceilDiv S scale +
    ceilDiv ((errors + 2 * incidenceGap) * x.b * q.b *
      (chart (taylorLength + 1) p).b) incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixF p q auxBox h + 2 * x.t * mixF p p p h
  let points := mixF p q auxBox p + 2 * x.t * mixF p p p p
  ceilDiv numerator l + 2 * physicalDegree * x.b * q.b +
    ceilDiv (errors * curves + 2 * incidenceGap * points) (32 * incidenceGap)
theorem chargeF_eq (x : Shape) (l scale S : ℕ) :
    chargeF x l scale S = Low6960RetainedCut.cutPrice x l scale S := by
  rw [Low6960Rectangle.cut_eq]
  simp only [chargeF, Low6960Rectangle.charge, mixF_eq]
def fourSurfaceF (p q : Shape) : ℕ :=
  mixF p q (chart (taylorLength+1) p) (chart (taylorLength+2) p)
theorem fourSurfaceF_eq (p q : Shape) : fourSurfaceF p q = Low6960RetainedCut.fourSurface p q := by
  simp only [fourSurfaceF, Low6960RetainedCut.fourSurface, mixF_eq]
def contractedPriceF (x h : Shape) (l active : ℕ) : ℕ :=
  let q := Low6960RetainedCut.chamberHull (Low6960RetainedCut.residualBox h l)
  let old := physicalPriceF x l active
  let four := if 0 < q.t then min old (chargeF x l 32 (fourSurfaceF x.chamber q)) else old
  if tiltedFits x then min four (chargeF x l (60*32) (tiltF x.chamber q)) else four
theorem contractedPriceF_eq (x h : Shape) (l active : ℕ) :
    contractedPriceF x h l active = Low6960RetainedCut.contractedPrice x h l active := by
  simp only [contractedPriceF, Low6960RetainedCut.contractedPrice, physicalPriceF_eq, chargeF_eq,
    fourSurfaceF_eq, tiltF_eq]
open Low6960SharedPrice (Surface Rate surfaceScale coord expression deficit slope)
def surfaceF (kind : Surface) (f q : Shape) : ℕ :=
  match kind with
  | .ordinary =>
    let p := f.chamber
    mixF p q (chart (taylorLength + 1) p) (chart (taylorLength + 2) p)
  | .tilted => tiltF f.chamber q
theorem surfaceF_eq (kind : Surface) (f q : Shape) :
    surfaceF kind f q = Low6960SharedPrice.surface kind f q := by
  cases kind <;> simp only [surfaceF, Low6960SharedPrice.surface, mixF_eq, tiltF_eq]
def weightsF (kind : Surface) (f : Shape) : Shape :=
  let b := surfaceF kind f ⟨1,0,0⟩
  let j := surfaceF kind f ⟨1,1,0⟩ - b
  let t := surfaceF kind f ⟨3,3,1⟩ - 3 * (b+j)
  ⟨b,j,t⟩
theorem weightsF_eq (kind : Surface) (f : Shape) :
    weightsF kind f = Low6960SharedPrice.weights kind f := by
  simp only [weightsF, Low6960SharedPrice.weights, surfaceF_eq]
def RateFitsF (f : Shape) (u : Rate) : Prop :=
  let p := coord slope u.pivot
  let q := coord f u.pivot
  let w := weightsF u.kind f
  let target := 3 * surfaceScale u.kind * u.amount
  (u.kind = .tilted → tiltedFits f) ∧
  0 < u.split ∧ u.split*p < q ∧
  (∀ i, p * coord f i ≤ q * coord slope i) ∧
  (∀ useIndex : Bool, expression w slope useIndex u.topIndex ≤ target) ∧
  (∀ useIndex : Bool, expression w (deficit q p f) useIndex u.topIndex ≤ target*(q-u.split*p))
instance (f : Shape) (u : Rate) : Decidable (RateFitsF f u) := by
  unfold RateFitsF
  infer_instance
theorem rateFitsF_iff (f : Shape) (u : Rate) : RateFitsF f u ↔ Low6960SharedPrice.RateFits f u := by
  simp only [RateFitsF, Low6960SharedPrice.RateFits, weightsF_eq]
def additiveBaseF (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := chart taylorLength p
  let h1 := chart (taylorLength+1) p
  let cont := ceilDiv ((errors+2*incidenceGap)*x.b*q.b*h1.b) incidenceGap
  let z := q.plus (p.scale 4)
  let cv := mixF p q z h + 2*x.t*mixF p p p h
  let pt := mixF p q z p + 2*x.t*mixF p p p p
  ceilDiv cont l + 2*physicalDegree*x.b*q.b +
    ceilDiv (errors*cv+2*incidenceGap*pt) (32*incidenceGap)
def priceF (x : Shape) (l K : ℕ) (u : Rate) : ℕ :=
  ceilDiv (physicalPriceF x l K + u.split*additiveBaseF x l + u.split*u.amount + 1)
    (u.split+1) + Low6960SharedPrice.nonsharedFee x l
theorem priceF_eq (x : Shape) (l K : ℕ) (u : Rate) :
    priceF x l K u = Low6960SharedPrice.price x l K u := by
  simp only [priceF, Low6960SharedPrice.price, Low6960SharedPrice.additiveBase, additiveBaseF,
    physicalPriceF_eq, mixF_eq]
open Low6960WeightedRate (Envelope Fits unit boxFee sepBox first)
def RayBoundsF (p : Envelope) (x : Shape) (amount : ℕ) : Prop :=
  let w := weightsF .tilted x
  let scale := 1920*amount
  unit*w.b ≤ scale*p.coeff.b ∧
    unit*(w.b+w.j) ≤ scale*(p.coeff.b+p.coeff.j) ∧
    unit*(3*(w.b+w.j)+w.t) ≤ scale*(3*(p.coeff.b+p.coeff.j)+p.coeff.t) ∧
    unit*boxFee w (sepBox x) ≤ scale*p.sep
def PaysF (p : Envelope) (x : Shape) (u : Rate) : Prop :=
  Fits p x ∧ u.kind = .tilted ∧ u.split = Low6960WeightedRate.split ∧ 0 < u.amount ∧
    tiltedFits x ∧ RayBoundsF p x u.amount
instance (p : Envelope) (x : Shape) (u : Rate) : Decidable (PaysF p x u) := by
  unfold PaysF Fits RayBoundsF
  infer_instance
def AllowedF (x : Shape) (u : Rate) : Prop :=
  RateFitsF x u ∨ PaysF first x u
instance (x : Shape) (u : Rate) : Decidable (AllowedF x u) := by unfold AllowedF; infer_instance
theorem allowedF_iff (x : Shape) (u : Rate) : AllowedF x u ↔ Low6960WeightedRate.Allowed x u := by
  simp only [AllowedF, Low6960WeightedRate.Allowed, PaysF, Low6960WeightedRate.Pays, RayBoundsF,
    Low6960WeightedRate.RayBounds, rateFitsF_iff, weightsF_eq]
open Low6960Allocation (Band MassCell start order allowance)
open Low6960Rectangle (hullOf)
def PaidFourF {k : Band} (cells : List (MassCell k)) (t bl jl bh jh l : ℕ) : Prop :=
  0 < l ∧ l ≤ order cells ⟨bl,jl,0⟩ ∧ 0 < (hullOf k l).t ∧
    chargeF ⟨bh,jh,t⟩ l 32 (fourSurfaceF (Shape.chamber ⟨bh,jh,t⟩) (hullOf k l)) ≤
      allowance k ((start k).t+t) bl jl t
instance {k : Band} (cells : List (MassCell k)) (t bl jl bh jh l : ℕ) :
    Decidable (PaidFourF cells t bl jl bh jh l) := inferInstanceAs (Decidable (_ ∧ _))
theorem paidFourF_iff {k : Band} (cells : List (MassCell k)) (t bl jl bh jh l : ℕ) :
    PaidFourF cells t bl jl bh jh l ↔ Low6960Rectangle.PaidFour cells t bl jl bh jh l := by
  simp only [PaidFourF, Low6960Rectangle.PaidFour, chargeF_eq, fourSurfaceF_eq]
def PaidTiltedF {k : Band} (cells : List (MassCell k)) (t b j B l : ℕ) : Prop :=
  0<l ∧ l≤order cells ⟨b,j,0⟩ ∧ 1≤t ∧ 3*t+3≤j ∧ j+1≤b ∧
    chargeF ⟨B,j,t⟩ l 1920 (tiltF (⟨B,j,t⟩ : Shape).chamber (hullOf k l)) ≤
      allowance k ((start k).t+t) b j t
instance {k : Band} (cells : List (MassCell k)) (t b j B l : ℕ) :
    Decidable (PaidTiltedF cells t b j B l) := inferInstanceAs (Decidable (_ ∧ _))
theorem paidTiltedF_iff {k : Band} (cells : List (MassCell k)) (t b j B l : ℕ) :
    PaidTiltedF cells t b j B l ↔ Low6960Rectangle.PaidTilted cells t b j B l := by
  simp only [PaidTiltedF, Low6960Rectangle.PaidTilted, chargeF_eq, tiltF_eq]
end Low6960FastPrice

end Merged_R6960Low6960FastPrice

end Merged_R6960Low6960FastPrice

end Merged6967_R6960Low6960FastPrice

section Merged6967_R6960Low6960Mass0
set_option Elab.async false


set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 4000000

namespace Low6960Allocation.Group0

private def m0 : MassCell 0 :=
  ⟨⟨2,9,5⟩,mass_cell 0 2 9 5 187 (by decide)
    (by decide +kernel) [4674578000546, 3875436487257, 3132763614105, 2488388285121, 1936360460625, 1470473119689, 1084262260137, 771006898545, 523729070241, 335193829305, 197909248569, 104126419617, 45839452785, 14785477161, 2444640585, 49499494] (by decide +kernel) (by decide +kernel)⟩
private def m1 : MassCell 0 :=
  ⟨⟨3,12,17⟩,mass_cell 0 3 12 17 153 (by decide)
    (by decide +kernel) [4881692334132, 4601315954784, 3562260545350, 2645289798310, 1896861162502, 1301756819302, 844042313926, 507066555430, 273461816710, 125143734502, 43311309382, 8446905766, 318404865] (by decide +kernel) (by decide +kernel)⟩
private def m2 : MassCell 0 :=
  ⟨⟨4,13,20⟩,mass_cell 0 4 13 20 145 (by decide)
    (by decide +kernel) [4881692334132, 4755268561988, 3727893528936, 2704987986476, 1885357925360, 1248195384180, 771978675320, 434472384956, 212727373056, 83080773380, 21155993480, 1862714700, 357348] (by decide +kernel) (by decide +kernel)⟩
private def m3 : MassCell 0 :=
  ⟨⟨3,14,22⟩,mass_cell 0 3 14 22 138 (by decide)
    (by decide +kernel) [4881692334132, 4829467408728, 3864391096672, 2755773358808, 1876001717584, 1202108836552, 709572123968, 372313732792, 162700560688, 51544250024, 8101187872, 130640521] (by decide +kernel) (by decide +kernel)⟩
private def m4 : MassCell 0 :=
  ⟨⟨3,15,24⟩,mass_cell 0 3 15 24 133 (by decide)
    (by decide +kernel) [4881692334132, 4873288215009, 4019812685506, 2811045778966, 1864877267386, 1153658416366, 647570987506, 314627238406, 120669922666, 29372289886, 2238085666, 3683] (by decide +kernel) (by decide +kernel)⟩
private def m5 : MassCell 0 :=
  ⟨⟨4,16,26⟩,mass_cell 0 4 16 26 128 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4200308249971, 2875843868208, 1855661524848, 1106006073520, 588705874416, 263324363568, 87160052848, 15246529968, 382177948] (by decide +kernel) (by decide +kernel)⟩
private def m6 : MassCell 0 :=
  ⟨⟨5,18,29⟩,mass_cell 0 5 18 29 119 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4459228964208, 2989946900082, 1828730519274, 1010776472418, 479982225882, 177101004882, 39741793482, 2369334594] (by decide +kernel) (by decide +kernel)⟩
private def m7 : MassCell 0 :=
  ⟨⟨3,19,30⟩,mass_cell 0 3 19 30 115 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4541037290271, 3047175141939, 1827022162411, 976872933891, 437807751099, 144411819859, 24775257099, 563225234] (by decide +kernel) (by decide +kernel)⟩
private def m8 : MassCell 0 :=
  ⟨⟨2,21,32⟩,mass_cell 0 2 21 32 109 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4681877922537, 3159285335112, 1806026199492, 895451406672, 352178406444, 89110446744, 7436573652, 392844] (by decide +kernel) (by decide +kernel)⟩
private def m9 : MassCell 0 :=
  ⟨⟨5,23,34⟩,mass_cell 0 5 23 34 104 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4792819515141, 3286435980104, 1774494932444, 807933566256, 274437073028, 50505569816, 1504636410] (by decide +kernel) (by decide +kernel)⟩
private def m10 : MassCell 0 :=
  ⟨⟨8,24,35⟩,mass_cell 0 8 24 35 102 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4834903666394, 3362738070824, 1758421175912, 764608505768, 240142643432, 36986464808, 546987532] (by decide +kernel) (by decide +kernel)⟩
private def m11 : MassCell 0 :=
  ⟨⟨1,27,36⟩,mass_cell 0 1 27 36 96 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4865495146485, 3437552907507, 1689113149275, 646754708019, 152180914107, 9953749299] (by decide +kernel) (by decide +kernel)⟩
private def m12 : MassCell 0 :=
  ⟨⟨9,8,4⟩,mass_cell 0 9 8 4 209 (by decide)
    (by decide +kernel) [4614569596201, 3790456040782, 3058160436702, 2433344910702, 1905659857918, 1465208658318, 1102547676702, 808686262702, 575086750782, 393664460238, 256787695198, 157277744622, 88408882302, 43908366862, 17956441758, 5186335278, 684260542, 5475301] (by decide +kernel) (by decide +kernel)⟩
private def m13 : MassCell 0 :=
  ⟨⟨1,28,37⟩,mass_cell 0 1 28 37 94 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 3577780466648, 1727907124744, 640712384056, 140193638504, 7258369244] (by decide +kernel) (by decide +kernel)⟩
private def m14 : MassCell 0 :=
  ⟨⟨1,30,38⟩,mass_cell 0 1 30 38 92 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 3698018593223, 1703271706916, 576819477572, 101816431268, 2428387832] (by decide +kernel) (by decide +kernel)⟩
private def m15 : MassCell 0 :=
  ⟨⟨2,32,39⟩,mass_cell 0 2 32 39 89 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 3822295702462, 1688461118564, 521669227332, 73203499556, 616443204] (by decide +kernel) (by decide +kernel)⟩
private def m16 : MassCell 0 :=
  ⟨⟨7,34,40⟩,mass_cell 0 7 34 40 87 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 3938633772976, 1663376974626, 464579035074, 50894280226, 91047647] (by decide +kernel) (by decide +kernel)⟩
private def m17 : MassCell 0 :=
  ⟨⟨7,37,41⟩,mass_cell 0 7 37 41 84 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4060164227100, 1636425406335, 394330676599, 27895990431] (by decide +kernel) (by decide +kernel)⟩
private def m18 : MassCell 0 :=
  ⟨⟨3,41,42⟩,mass_cell 0 3 41 42 81 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4183267993065, 1606475191342, 315773754890, 10930555214] (by decide +kernel) (by decide +kernel)⟩
private def m19 : MassCell 0 :=
  ⟨⟨6,45,43⟩,mass_cell 0 6 45 43 78 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4299116170062, 1569922173267, 247144734267, 3534608496] (by decide +kernel) (by decide +kernel)⟩
private def m20 : MassCell 0 :=
  ⟨⟨16,7,4⟩,mass_cell 0 16 7 4 238 (by decide)
    (by decide +kernel) [4606889813659, 3765015856248, 3024402618468, 2398816790248, 1875684410244, 1443159357624, 1090123352068, 806185953768, 581684563428, 407684422264, 275978612004, 179088054888, 110261513668, 63475591608, 33434732484, 15571220584, 6045180708, 1744578168, 285218788, 10749804] (by decide +kernel) (by decide +kernel)⟩
private def m21 : MassCell 0 :=
  ⟨⟨15,11,18⟩,mass_cell 0 15 11 18 167 (by decide)
    (by decide +kernel) [4881692334132, 4644078560979, 3557453995757, 2599020272221, 1844001267181, 1262531199197, 826943056237, 511768595677, 293738344301, 151781598301, 67026423277, 22799654237, 4626895597, 232540463] (by decide +kernel) (by decide +kernel)⟩
private def m22 : MassCell 0 :=
  ⟨⟨9,50,44⟩,mass_cell 0 9 50 44 76 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4413641641756, 1528694145820, 179913477668, 498345953] (by decide +kernel) (by decide +kernel)⟩
private def m23 : MassCell 0 :=
  ⟨⟨18,11,19⟩,mass_cell 0 18 11 19 168 (by decide)
    (by decide +kernel) [4881692334132, 4696778814289, 3604764974578, 2606350477270, 1828680974762, 1237167945262, 800084027170, 488563019078, 276599879770, 141050728222, 61632843602, 20924665270, 4365792778, 256985870] (by decide +kernel) (by decide +kernel)⟩
private def m24 : MassCell 0 :=
  ⟨⟨17,56,45⟩,mass_cell 0 17 56 45 73 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4523338941257, 1476427762482, 119835416898, 2490670] (by decide +kernel) (by decide +kernel)⟩
private def m25 : MassCell 0 :=
  ⟨⟨22,6,5⟩,mass_cell 0 22 6 5 279 (by decide)
    (by decide +kernel) [4660126313490, 3820638580887, 3060802681419, 2417906186463, 1879505691987, 1433847556263, 1069867899867, 777192605679, 546137318883, 367707446967, 233598159723, 136194389247, 68571603217, 24870666391, 3352786251, 14545201, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m26 : MassCell 0 :=
  ⟨⟨21,9,15⟩,mass_cell 0 21 9 15 197 (by decide)
    (by decide +kernel) [4881692334132, 4445927934302, 3392522416788, 2529833031240, 1843219629996, 1306911444864, 897178441092, 592331317368, 372721505820, 220741172016, 120823214964, 59441267112, 25109694348, 8383596000, 1858804836, 171887064, 832620] (by decide +kernel) (by decide +kernel)⟩
private def m27 : MassCell 0 :=
  ⟨⟨25,6,8⟩,mass_cell 0 25 6 8 282 (by decide)
    (by decide +kernel) [4786292207151, 3985160169384, 3158430623928, 2462626165896, 1883543713560, 1407777442920, 1022718787704, 716556439368, 478276347096, 297661717800, 165293016904, 72767552726, 16917795165, 539877640, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m28 : MassCell 0 :=
  ⟨⟨27,9,18⟩,mass_cell 0 27 9 18 200 (by decide)
    (by decide +kernel) [4881692334132, 4640745988855, 3543229708566, 2581776752370, 1829705261334, 1254307233282, 825640993590, 516531195186, 302568818550, 162111171714, 76281890262, 28970937330, 6851966126, 256277988, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m29 : MassCell 0 :=
  ⟨⟨29,9,19⟩,mass_cell 0 29 9 19 201 (by decide)
    (by decide +kernel) [4881692334132, 4696566570078, 3603871649064, 2605739256012, 1828876285344, 1238181701988, 801562663128, 489934518204, 277220808912, 140353269204, 59271825288, 16952975088, 1195545634, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m30 : MassCell 0 :=
  ⟨⟨28,17,31⟩,mass_cell 0 28 17 31 127 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4594799507516, 3019652363322, 1760399272358, 938917725290, 441651641094, 171514886906, 47891278022, 6634577898, 98852733] (by decide +kernel) (by decide +kernel)⟩
private def m31 : MassCell 0 :=
  ⟨⟨28,25,37⟩,mass_cell 0 28 25 37 102 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 3525319770465, 1694787261033, 671097784201, 188692299969, 24887768337, 241604369] (by decide +kernel) (by decide +kernel)⟩
private def m32 : MassCell 0 :=
  ⟨⟨35,17,32⟩,mass_cell 0 35 17 32 128 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4664580641835, 3067755267995, 1740326984563, 898312046803, 406125526715, 150357498667, 39773039395, 5312228003, 95684932] (by decide +kernel) (by decide +kernel)⟩
private def m33 : MassCell 0 :=
  ⟨⟨29,19,33⟩,mass_cell 0 29 19 33 118 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4731172517891, 3147338931663, 1741652262215, 862652347799, 362395219647, 116025290687, 21775355543, 966846483] (by decide +kernel) (by decide +kernel)⟩
private def m34 : MassCell 0 :=
  ⟨⟨35,26,38⟩,mass_cell 0 35 26 38 100 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 3647633359117, 1674838982986, 622193228234, 158319085066, 16990837258, 62058415] (by decide +kernel) (by decide +kernel)⟩
private def m35 : MassCell 0 :=
  ⟨⟨36,54,45⟩,mass_cell 0 36 54 45 74 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4517046081495, 1469001456549, 131720578641, 57544248] (by decide +kernel) (by decide +kernel)⟩
private def m36 : MassCell 0 :=
  ⟨⟨38,5,17⟩,mass_cell 0 38 5 17 346 (by decide)
    (by decide +kernel) [4881692334132, 4614331871188, 3614437456294, 2715837719162, 1961588774950, 1336984998058, 828061210886, 421874198940, 124732122172, 6775409804, 14950, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m37 : MassCell 0 :=
  ⟨⟨34,21,35⟩,mass_cell 0 34 21 35 112 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4831619185493, 3298873995761, 1707937858985, 770412460217, 280479303329, 69766930913, 7350924281, 28587347] (by decide +kernel) (by decide +kernel)⟩
private def m38 : MassCell 0 :=
  ⟨⟨21,30,39⟩,mass_cell 0 21 30 39 93 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 3793448384372, 1668332083108, 545400581764, 97724573860, 2983976418] (by decide +kernel) (by decide +kernel)⟩
private def m39 : MassCell 0 :=
  ⟨⟨30,23,36⟩,mass_cell 0 30 23 36 106 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4864671476237, 3408995338616, 1707689939044, 726646545304, 235917236756, 44828000728, 1979573486] (by decide +kernel) (by decide +kernel)⟩
private def m40 : MassCell 0 :=
  ⟨⟨37,28,39⟩,mass_cell 0 37 28 39 96 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 3774904169338, 1654716342780, 562407995244, 119731108060, 7818154572] (by decide +kernel) (by decide +kernel)⟩
private def m41 : MassCell 0 :=
  ⟨⟨35,34,41⟩,mass_cell 0 35 34 41 88 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4031009024461, 1608162363850, 422419123594, 47099690762, 183451721] (by decide +kernel) (by decide +kernel)⟩
private def m42 : MassCell 0 :=
  ⟨⟨43,4,19⟩,mass_cell 0 43 4 19 430 (by decide)
    (by decide +kernel) [4881692334132, 4727738536138, 3774330684628, 2825722764292, 2008029001268, 1310348093284, 722286678943, 251507698844, 20335238335, 4911290, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m43 : MassCell 0 :=
  ⟨⟨41,12,28⟩,mass_cell 0 41 12 28 164 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4344134677452, 2868795320202, 1776295681290, 1025138492298, 536646309642, 242317923210, 83828356362, 13780936415, 37806161, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m44 : MassCell 0 :=
  ⟨⟨36,24,37⟩,mass_cell 0 36 24 37 104 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 3511400175208, 1681637057704, 672432656104, 198382638376, 31413565288, 805676592] (by decide +kernel) (by decide +kernel)⟩
private def m45 : MassCell 0 :=
  ⟨⟨34,31,40⟩,mass_cell 0 34 31 40 92 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 3906369103777, 1636729481206, 494268741770, 78686205094, 1800586606] (by decide +kernel) (by decide +kernel)⟩
private def m46 : MassCell 0 :=
  ⟨⟨42,30,40⟩,mass_cell 0 42 30 40 94 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 3898149235185, 1627634971369, 499104332461, 86416524433, 3055904195] (by decide +kernel) (by decide +kernel)⟩
private def m47 : MassCell 0 :=
  ⟨⟨31,38,42⟩,mass_cell 0 31 38 42 84 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4160783527351, 1588099997584, 348344774536, 22110859904] (by decide +kernel) (by decide +kernel)⟩
private def m48 : MassCell 0 :=
  ⟨⟨44,13,30⟩,mass_cell 0 44 13 30 155 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4518461308754, 2973208776516, 1777393993280, 979356020540, 480545836920, 196278932276, 55736785526, 4581769169, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m49 : MassCell 0 :=
  ⟨⟨40,20,35⟩,mass_cell 0 40 20 35 116 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4831438559546, 3296291740996, 1709118849156, 777642014916, 290748022276, 78242695236, 10850897796, 223591934] (by decide +kernel) (by decide +kernel)⟩
private def m50 : MassCell 0 :=
  ⟨⟨44,21,36⟩,mass_cell 0 44 21 36 113 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4864304876405, 3389619901644, 1689923714616, 727181341380, 249497053488, 57785048892, 5769451944, 32889748] (by decide +kernel) (by decide +kernel)⟩
private def m51 : MassCell 0 :=
  ⟨⟨43,33,41⟩,mass_cell 0 43 33 41 90 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4024460413860, 1601161693266, 428959734726, 53434178202, 481098570] (by decide +kernel) (by decide +kernel)⟩
private def m52 : MassCell 0 :=
  ⟨⟨43,41,43⟩,mass_cell 0 43 41 43 82 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4276014797124, 1545743893628, 282449937920, 10977565350] (by decide +kernel) (by decide +kernel)⟩
private def m53 : MassCell 0 :=
  ⟨⟨44,18,34⟩,mass_cell 0 44 18 34 124 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4785088187550, 3201688320897, 1709280278085, 812488996137, 326363559213, 100539704145, 19239820437, 1272950265, 1355942] (by decide +kernel) (by decide +kernel)⟩
private def m54 : MassCell 0 :=
  ⟨⟨50,8,27⟩,mass_cell 0 50 8 27 232 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4298932786942, 2939072617428, 1880549325876, 1090313980564, 523082568755, 145185456486, 4620632196, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m55 : MassCell 0 :=
  ⟨⟨46,15,32⟩,mass_cell 0 46 15 32 141 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4664374052796, 3065564336364, 1735566216264, 891420977484, 398076607224, 142386084684, 33107390528, 1876989281, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m56 : MassCell 0 :=
  ⟨⟨49,22,37⟩,mass_cell 0 49 22 37 111 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 3500084695894, 1671776432198, 675915992182, 210098565094, 40660783766, 2680724614, 1408482] (by decide +kernel) (by decide +kernel)⟩
private def m57 : MassCell 0 :=
  ⟨⟨38,47,44⟩,mass_cell 0 38 47 44 78 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4399365047123, 1511142935886, 202687475290, 2034078349] (by decide +kernel) (by decide +kernel)⟩
private def m58 : MassCell 0 :=
  ⟨⟨40,37,42⟩,mass_cell 0 40 37 42 85 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4153385270874, 1578002594242, 354564657222, 26209524234, 1027212] (by decide +kernel) (by decide +kernel)⟩
private def m59 : MassCell 0 :=
  ⟨⟨53,52,45⟩,mass_cell 0 53 52 45 75 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4512287693932, 1463750160832, 143056265680, 264954475] (by decide +kernel) (by decide +kernel)⟩
private def m60 : MassCell 0 :=
  ⟨⟨54,45,44⟩,mass_cell 0 54 45 44 79 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4393671723615, 1505963629482, 216641480622, 3836655540] (by decide +kernel) (by decide +kernel)⟩
private def m61 : MassCell 0 :=
  ⟨⟨61,51,45⟩,mass_cell 0 61 51 45 76 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4510267415221, 1461100276311, 148152024303, 453575717] (by decide +kernel) (by decide +kernel)⟩
private def m62 : MassCell 0 :=
  ⟨⟨62,44,44⟩,mass_cell 0 62 44 44 80 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4390637388987, 1500596298164, 221392739284, 4886644186] (by decide +kernel) (by decide +kernel)⟩
private def m63 : MassCell 0 :=
  ⟨⟨63,30,41⟩,mass_cell 0 63 30 41 95 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4015213283280, 1592751180394, 442652904082, 67940351290, 2274616718] (by decide +kernel) (by decide +kernel)⟩
private def m64 : MassCell 0 :=
  ⟨⟨62,34,42⟩,mass_cell 0 62 34 42 89 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4141787829493, 1564418454295, 370430812643, 38154150031, 220564289] (by decide +kernel) (by decide +kernel)⟩
private def m65 : MassCell 0 :=
  ⟨⟨58,39,43⟩,mass_cell 0 58 39 43 84 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4269729309592, 1539601024949, 295773046037, 15925806197] (by decide +kernel) (by decide +kernel)⟩
private def m66 : MassCell 0 :=
  ⟨⟨57,25,39⟩,mass_cell 0 57 25 39 104 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 3760638201914, 1640125372252, 569822424544, 136355661236, 15278322328, 191023862] (by decide +kernel) (by decide +kernel)⟩
private def m67 : MassCell 0 :=
  ⟨⟨65,38,43⟩,mass_cell 0 65 38 43 85 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4267267832665, 1536407881978, 300315859242, 18308997018, 246957] (by decide +kernel) (by decide +kernel)⟩
private def m68 : MassCell 0 :=
  ⟨⟨67,26,40⟩,mass_cell 0 67 26 40 102 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 3887908617559, 1617207623222, 508227663638, 100829490102, 7186819094, 5844240] (by decide +kernel) (by decide +kernel)⟩
private def m69 : MassCell 0 :=
  ⟨⟨69,50,45⟩,mass_cell 0 69 50 45 77 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4508177216989, 1456974527224, 152329122592, 701586243] (by decide +kernel) (by decide +kernel)⟩
private def m70 : MassCell 0 :=
  ⟨⟨72,14,36⟩,mass_cell 0 72 14 36 152 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4865515441455, 3458178728483, 1761699705055, 727013352187, 168758136443, 2085565806, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m71 : MassCell 0 :=
  ⟨⟨69,43,44⟩,mass_cell 0 69 43 44 81 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4388876221918, 1498824189991, 226442163631, 6039233311] (by decide +kernel) (by decide +kernel)⟩
private def m72 : MassCell 0 :=
  ⟨⟨76,49,45⟩,mass_cell 0 76 49 45 77 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4506969301425, 1456051047551, 156791521607, 1014752916] (by decide +kernel) (by decide +kernel)⟩
private def m73 : MassCell 0 :=
  ⟨⟨68,33,42⟩,mass_cell 0 68 33 42 91 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4140788262169, 1564523187275, 374543225219, 41203228619, 415556228] (by decide +kernel) (by decide +kernel)⟩
private def m74 : MassCell 0 :=
  ⟨⟨72,37,43⟩,mass_cell 0 72 37 43 86 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4264629365325, 1531052129783, 302152105511, 20198954175, 6411133] (by decide +kernel) (by decide +kernel)⟩
private def m75 : MassCell 0 :=
  ⟨⟨76,42,44⟩,mass_cell 0 76 42 44 82 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4387007057553, 1495332213147, 229698761535, 7132592532] (by decide +kernel) (by decide +kernel)⟩
private def m76 : MassCell 0 :=
  ⟨⟨80,31,42⟩,mass_cell 0 80 31 42 94 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4138114239674, 1557846924183, 372154151447, 41612944367, 510515895] (by decide +kernel) (by decide +kernel)⟩
private def m77 : MassCell 0 :=
  ⟨⟨79,27,41⟩,mass_cell 0 79 27 41 101 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4016178562350, 1593987662307, 441314025267, 65242103403, 1275204296, 0] (by decide +kernel) (by decide +kernel)⟩
private def m78 : MassCell 0 :=
  ⟨⟨83,48,45⟩,mass_cell 0 83 48 45 78 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4505701462068, 1453785369204, 160177866708, 1367160846] (by decide +kernel) (by decide +kernel)⟩
private def m79 : MassCell 0 :=
  ⟨⟨84,57,46⟩,mass_cell 0 84 57 46 73 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4620207423282, 1406715642373, 94042020613, 8630690] (by decide +kernel) (by decide +kernel)⟩
private def m80 : MassCell 0 :=
  ⟨⟨78,36,43⟩,mass_cell 0 78 36 43 87 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4263778250082, 1530298480752, 304648768368, 21787112304, 25600464] (by decide +kernel) (by decide +kernel)⟩
private def m81 : MassCell 0 :=
  ⟨⟨83,41,44⟩,mass_cell 0 83 41 44 83 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4385028766015, 1490038821205, 230849127205, 8008179108] (by decide +kernel) (by decide +kernel)⟩
private def m82 : MassCell 0 :=
  ⟨⟨79,17,38⟩,mass_cell 0 79 17 38 134 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 3673948247883, 1706884070204, 612865324088, 104080164843, 120501316, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m83 : MassCell 0 :=
  ⟨⟨77,24,40⟩,mass_cell 0 77 24 40 107 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 3890514122277, 1617647585768, 499776512552, 88658324024, 2146974795, 0] (by decide +kernel) (by decide +kernel)⟩
private def m84 : MassCell 0 :=
  ⟨⟨85,30,42⟩,mass_cell 0 85 30 42 96 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4139086094351, 1559210096576, 370612429616, 39365116260, 173206100] (by decide +kernel) (by decide +kernel)⟩
private def m85 : MassCell 0 :=
  ⟨⟨90,47,45⟩,mass_cell 0 90 47 45 79 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4504373188636, 1450115740447, 162267038399, 1720360113] (by decide +kernel) (by decide +kernel)⟩
private def m86 : MassCell 0 :=
  ⟨⟨91,24,41⟩,mass_cell 0 91 24 41 108 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4028553315036, 1612887570288, 430841607408, 40419361249, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m87 : MassCell 0 :=
  ⟨⟨91,56,46⟩,mass_cell 0 91 56 46 74 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4619427194692, 1405699351546, 96952937578, 25735208] (by decide +kernel) (by decide +kernel)⟩
private def m88 : MassCell 0 :=
  ⟨⟨83,19,39⟩,mass_cell 0 83 19 39 124 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 3788205390566, 1670748890942, 548499979362, 76609977949, 6949300, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m89 : MassCell 0 :=
  ⟨⟨90,6,36⟩,mass_cell 0 90 6 36 310 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4868570367221, 3627826487185, 1896291226885, 560883278780, 9702080295, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m90 : MassCell 0 :=
  ⟨⟨91,20,40⟩,mass_cell 0 91 20 40 121 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 3917940906688, 1655145157028, 479801800180, 39712769023, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m91 : MassCell 0 :=
  ⟨⟨84,35,43⟩,mass_cell 0 84 35 43 89 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4262779079807, 1527615476220, 304288959304, 22265989908, 44202087] (by decide +kernel) (by decide +kernel)⟩
private def m92 : MassCell 0 :=
  ⟨⟨96,46,45⟩,mass_cell 0 96 46 45 79 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4503953535985, 1450142721069, 164727973113, 2073547944] (by decide +kernel) (by decide +kernel)⟩
private def m93 : MassCell 0 :=
  ⟨⟨89,40,44⟩,mass_cell 0 89 40 44 84 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4384370507154, 1488955115606, 232476227174, 8722268022] (by decide +kernel) (by decide +kernel)⟩
private def m94 : MassCell 0 :=
  ⟨⟨98,55,46⟩,mass_cell 0 98 55 46 75 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4618618172736, 1403642006063, 99244049991, 55839374] (by decide +kernel) (by decide +kernel)⟩
private def m95 : MassCell 0 :=
  ⟨⟨99,32,43⟩,mass_cell 0 99 32 43 93 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4264975854633, 1530433771514, 298037578186, 16417194937, 0] (by decide +kernel) (by decide +kernel)⟩
private def m96 : MassCell 0 :=
  ⟨⟨94,39,44⟩,mass_cell 0 94 39 44 85 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4385061775492, 1492549004858, 235051565342, 9239066762, 6060] (by decide +kernel) (by decide +kernel)⟩
private def m97 : MassCell 0 :=
  ⟨⟨98,9,38⟩,mass_cell 0 98 9 38 220 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 3797594664654, 1825942562211, 469469836219, 3639854586, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m98 : MassCell 0 :=
  ⟨⟨98,22,41⟩,mass_cell 0 98 22 41 115 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4039384718008, 1626401043683, 411223850757, 20380629959, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m99 : MassCell 0 :=
  ⟨⟨102,45,45⟩,mass_cell 0 102 45 45 80 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4503483730730, 1448929369086, 165772737186, 2323455424] (by decide +kernel) (by decide +kernel)⟩
private def m100 : MassCell 0 :=
  ⟨⟨105,54,46⟩,mass_cell 0 105 54 46 75 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4617780177195, 1400497672176, 100772134848, 97613874] (by decide +kernel) (by decide +kernel)⟩
private def m101 : MassCell 0 :=
  ⟨⟨105,37,44⟩,mass_cell 0 105 37 44 87 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4384768264267, 1489122560884, 230201024952, 7469734266, 0] (by decide +kernel) (by decide +kernel)⟩
private def m102 : MassCell 0 :=
  ⟨⟨107,30,43⟩,mass_cell 0 107 30 43 97 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4269973095522, 1539968990346, 288979370658, 8799354203, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m103 : MassCell 0 :=
  ⟨⟨108,44,45⟩,mass_cell 0 108 44 45 81 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4502963338212, 1446420046972, 165169770108, 2362728050] (by decide +kernel) (by decide +kernel)⟩
private def m104 : MassCell 0 :=
  ⟨⟨109,36,44⟩,mass_cell 0 109 36 44 88 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4386704015112, 1495296544494, 229804247118, 6128462892, 0] (by decide +kernel) (by decide +kernel)⟩
private def m105 : MassCell 0 :=
  ⟨⟨97,27,42⟩,mass_cell 0 97 27 42 102 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4149091017393, 1578385683111, 363817013871, 23796474812, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m106 : MassCell 0 :=
  ⟨⟨111,53,46⟩,mass_cell 0 111 53 46 76 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4617510951528, 1400553462729, 102542905593, 149360411] (by decide +kernel) (by decide +kernel)⟩
private def m107 : MassCell 0 :=
  ⟨⟨113,43,45⟩,mass_cell 0 113 43 45 82 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4503378478545, 1448167387441, 165185828833, 2214581629] (by decide +kernel) (by decide +kernel)⟩
private def m108 : MassCell 0 :=
  ⟨⟨113,35,44⟩,mass_cell 0 113 35 44 90 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4388586757320, 1500382211573, 227242501621, 4337894114, 0] (by decide +kernel) (by decide +kernel)⟩
private def m109 : MassCell 0 :=
  ⟨⟨117,52,46⟩,mass_cell 0 117 52 46 76 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4617217766987, 1399652612936, 103456453496, 197320395] (by decide +kernel) (by decide +kernel)⟩
private def m110 : MassCell 0 :=
  ⟨⟨118,42,45⟩,mass_cell 0 118 42 45 83 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4503753602325, 1448814761727, 163508682651, 1723692606] (by decide +kernel) (by decide +kernel)⟩
private def m111 : MassCell 0 :=
  ⟨⟨120,13,41⟩,mass_cell 0 120 13 41 166 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4116837907117, 1722770225450, 265077561884, 367290, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m112 : MassCell 0 :=
  ⟨⟨110,29,43⟩,mass_cell 0 110 29 43 98 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4274423255611, 1551126911197, 286319742112, 5950479717, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m113 : MassCell 0 :=
  ⟨⟨123,41,45⟩,mass_cell 0 123 41 45 84 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4504088339596, 1448313469420, 159908606488, 994870382] (by decide +kernel) (by decide +kernel)⟩
private def m114 : MassCell 0 :=
  ⟨⟨123,51,46⟩,mass_cell 0 123 51 46 77 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4616900463048, 1397753758135, 103354504111, 218836945] (by decide +kernel) (by decide +kernel)⟩
private def m115 : MassCell 0 :=
  ⟨⟨117,34,44⟩,mass_cell 0 117 34 44 91 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4390415856370, 1504327382500, 222256747884, 2472646251, 0] (by decide +kernel) (by decide +kernel)⟩
private def m116 : MassCell 0 :=
  ⟨⟨122,12,41⟩,mass_cell 0 122 12 41 177 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4126706890092, 1732467618024, 247285013169, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m117 : MassCell 0 :=
  ⟨⟨124,32,44⟩,mass_cell 0 124 32 44 94 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4395424027669, 1516273195744, 209833873026, 345800825, 0] (by decide +kernel) (by decide +kernel)⟩
private def m118 : MassCell 0 :=
  ⟨⟨127,40,45⟩,mass_cell 0 127 40 45 85 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4505386114266, 1452699018254, 157399528149, 438788763, 0] (by decide +kernel) (by decide +kernel)⟩
private def m119 : MassCell 0 :=
  ⟨⟨117,27,43⟩,mass_cell 0 117 27 43 103 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4281033992286, 1561293520584, 265252310794, 1152540354, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m120 : MassCell 0 :=
  ⟨⟨128,31,44⟩,mass_cell 0 128 31 44 96 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4397098940937, 1516693880054, 197410565599, 38825480, 0] (by decide +kernel) (by decide +kernel)⟩
private def m121 : MassCell 0 :=
  ⟨⟨128,50,46⟩,mass_cell 0 128 50 46 78 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4617164916470, 1399493333369, 103614079085, 201850283] (by decide +kernel) (by decide +kernel)⟩
private def m122 : MassCell 0 :=
  ⟨⟨125,4,40⟩,mass_cell 0 125 4 40 451 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4104967669915, 1826004089319, 184391409533, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m123 : MassCell 0 :=
  ⟨⟨131,39,45⟩,mass_cell 0 131 39 45 86 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4506654365976, 1456166726376, 153078680841, 91434245, 0] (by decide +kernel) (by decide +kernel)⟩
private def m124 : MassCell 0 :=
  ⟨⟨127,3,40⟩,mass_cell 0 127 3 40 589 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4116290458795, 1823313776104, 163190085861, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m125 : MassCell 0 :=
  ⟨⟨133,49,46⟩,mass_cell 0 133 49 46 78 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4617410371455, 1400389437434, 102801101614, 118508841] (by decide +kernel) (by decide +kernel)⟩
private def m126 : MassCell 0 :=
  ⟨⟨131,30,44⟩,mass_cell 0 131 30 44 98 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4400252545677, 1523895391038, 189147078571, 2123555, 0, 0] (by decide +kernel) (by decide +kernel)⟩
private def m127 : MassCell 0 :=
  ⟨⟨135,38,45⟩,mass_cell 0 135 38 45 87 (by decide)
    (by decide +kernel) [4881692334132, 4881692334132, 4881692334132, 4507892802703, 1458675709624, 147019887283, 4082925, 0] (by decide +kernel) (by decide +kernel)⟩

def orders : List (MassCell 0) := [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, m25, m26, m27, m28, m29, m30, m31, m32, m33, m34, m35, m36, m37, m38, m39, m40, m41, m42, m43, m44, m45, m46, m47, m48, m49, m50, m51, m52, m53, m54, m55, m56, m57, m58, m59, m60, m61, m62, m63, m64, m65, m66, m67, m68, m69, m70, m71, m72, m73, m74, m75, m76, m77, m78, m79, m80, m81, m82, m83, m84, m85, m86, m87, m88, m89, m90, m91, m92, m93, m94, m95, m96, m97, m98, m99, m100, m101, m102, m103, m104, m105, m106, m107, m108, m109, m110, m111, m112, m113, m114, m115, m116, m117, m118, m119, m120, m121, m122, m123, m124, m125, m126, m127]

end Low6960Allocation.Group0

end Merged6967_R6960Low6960Mass0

section Merged6967_R6960MainGeometryInvoice
set_option Elab.async false


set_option Elab.async false

-- merged module R6960RescueGeometryFee
section Merged_R6960RescueGeometryFee
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2200000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false
namespace Lower6960.RescueGeometry
open Finset Polynomial
open K1 (K p)
open K1_14 (Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL evaluated)
open K1_14_2 (Ambient ODE)
open K1_14_2_2 (mass mass_mono ODECaps)
open K1_14_3 (Surface Parent)
open P1_7_4 (ODEGuard Mass massQ dotQ dotQ_mono_mass massQ_mono dotQ_scale_add)
open P1_7_4_3 (mix)
open HighCore82268JointRank (fixed_fee_linear)
open Lower6960.RescueGeometry (persistentTotal persistentTop siteRatio density)
open scoped Classical BigOperators
def Initial.rankMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (ini : Initial F G Q₀ rect) : Finset K :=
  Γ.filter (fun γ=>∃ J∈ini.rankExit,OnMark F J γ)
theorem fixedFee_eq (B J : ℕ) :
    fixedFee B J = (mix B J (mu+2*lambda*(B-1 : ℕ))
      (min (mu+2*lambda*(B-1 : ℕ)) (lambda*(2*J-1 : ℕ)))).ceil.toNat+B^2 := by
  have he : 2*density*(endpointDegree : ℚ)=2*lambda := by unfold lambda density; ring
  have hl : density*(endpointDegree : ℚ)=lambda := rfl
  have hm : siteRatio endpointDegree=mu := rfl
  unfold fixedFee persistentTop persistentTotal
  rw [he,hl,hm]
theorem Initial.rank_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (ini : Initial F G Q₀ rect) (hi : M.overhead.toNat≤33579) :
    (ini.rankMarks.card : ℚ)≤dotQ (rankWeight rect) (massQ ini.rankExit)+rankRound rect := by
  let S := ini.rankExit
  let B := max 2 (mass S 2)
  let J := max 1 (min (mass S 1) B)
  obtain ⟨E,caps,roots⟩ := ini.rank_ode
  have mass_cap (k : Fin 4) : mass S k ≤ initialCap rect k :=
    (mass_mono (subset_union_left : S⊆ini.rankExit∪ini.parents) k).trans (ini.fits k)
  have hBm : B≤mass S 2+2 := max_le (by omega) (by omega)
  have hJm : J≤mass S 1+1 := max_le (by omega) ((min_le_left _ _).trans (by omega))
  have hB : B≤rankB rect := hBm.trans (Nat.add_le_add_right (mass_cap 2) 2)
  have hJ : J≤rankJ rect := hJm.trans (Nat.add_le_add_right (mass_cap 1) 1)
  have hB2 : 2≤B := le_max_left _ _
  have hJ1 : 1≤J := le_max_left _ _
  have hJB : J≤B := max_le (by omega) (min_le_right _ _)
  have degree : E.natDegree≤B := by
    have top : E.coeff E.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr caps.1
    have hn : (E.coeff E.natDegree).coeff (E.coeff E.natDegree).natDegree≠0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr top
    exact (Nat.le_add_left _ _).trans ((caps.2.2 _ _ hn).trans (le_max_right _ _))
  have ocaps : ODECaps E B J := ⟨caps.1,(le_min caps.2.1 degree).trans (le_max_right _ _),
    fun j i hz => (caps.2.2 j i hz).trans (le_max_right _ _)⟩
  obtain ⟨small,cJ,cB⟩ := rank_guard rect
  have guard : ODEGuard B J := ⟨hB2,hJ1,hJB,hB.trans_lt small⟩
  have count : ini.rankMarks.card≤fixedFee B J :=
    fixed_count F hi guard E ocaps (filter_subset _ _)
      (fun γ mem => roots γ (mem_filter.mp mem).1 (mem_filter.mp mem).2)
  have lin := fixed_fee_linear lambda mu tau (pivot rect) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hJB hB hJ
  have fee : (fixedFee B J : ℚ) ≤
      rankWeight rect 1 * J + rankWeight rect 2 * B + 2*lambda*pivot rect^2+1 := by
    rw [fixedFee_eq]
    exact lin
  have hJq : (J : ℚ)≤(mass S 1 : ℚ)+1 := by exact_mod_cast hJm
  have hBq : (B : ℚ)≤(mass S 2 : ℚ)+2 := by exact_mod_cast hBm
  have hjfee := mul_le_mul_of_nonneg_left hJq cJ
  have hbfee := mul_le_mul_of_nonneg_left hBq cB
  have hdot : dotQ (rankWeight rect) (massQ ini.rankExit) =
      rankWeight rect 1 * (mass S 1 : ℚ)+rankWeight rect 2 * (mass S 2 : ℚ) := by
    simp [dotQ,rankWeight,massQ,Fin.sum_univ_succ,S]
  refine (Nat.cast_le.mpr count).trans (fee.trans ?_)
  rw [hdot,rankRound]
  linarith only [hjfee,hbfee]
private theorem card_round {a : ℕ} {q : ℚ} (bound : (a : ℚ)≤q) : a≤q.ceil.toNat := by
  have ceil_cast : (q.ceil : ℚ) ≤ (q.ceil.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat q.ceil
  exact_mod_cast bound.trans (Rat.le_ceil.trans ceil_cast)
theorem CutBooks.curve_bin_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) (hiM : M.overhead.toNat≤33579) {i : ℕ} (hi : i<17) :
    ((curveMarks F (C.cover i)).card : ℚ)≤
      dotQ (lossWeight R.rect i) (massQ (R.lost i))+((C.cover i).cost 0 : ℚ) := by
  have global : ((C.cover i).cost 0 : ℚ)≤seedLimit R.rect :=
    (single_le_sum (fun j _=>Nat.cast_nonneg (α:=ℚ) ((C.cover j).cost 0))
      (mem_range.mpr hi)).trans C.seed_bill
  have localCap : ((C.cover i).cost 0 : ℚ)≤ dotQ (cutWeight R.rect 0 i) (history R.rect i) :=
    (C.costQ hi 0).trans (dotQ_mono_mass (fun _=>Nat.cast_nonneg _)
      (fun k=>(massQ_mono sdiff_subset k).trans (R.live_history hi k)))
  have prime : (C.cover i).cost 0 < p := by exact_mod_cast global.trans_lt (seed_limit_small R.rect)
  obtain ⟨ok,degree⟩ := rate_spec R.rect hi
  have count := rated_curve_count F (curve_tariff F hiM) ok (C.cover i)
    global ((min_le_min le_rfl localCap).trans degree) prime
  calc
    _ ≤ (degreeRate R.rect i : ℚ)*((C.cover i).cost 0 : ℚ) +
          (heightRate R.rect i : ℚ)*((C.cover i).cost 1 : ℚ)+((C.cover i).cost 0 : ℚ) := count
    _ ≤ (degreeRate R.rect i : ℚ)*dotQ (cutWeight R.rect 0 i) (massQ (R.lost i)) +
          (heightRate R.rect i : ℚ)*dotQ (cutWeight R.rect 1 i) (massQ (R.lost i)) +
          ((C.cover i).cost 0 : ℚ) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left (C.costQ hi 0) (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left (C.costQ hi 1) (Nat.cast_nonneg _))) le_rfl
    _ = _ := by rw [dotQ_scale_add]; rfl
def CutBooks.lossMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G} (C : CutBooks R) :
    Finset K := R.initial.rankMarks ∪ (range 17).biUnion (fun i=>curveMarks F (C.cover i))
theorem CutBooks.loss_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) (hi : M.overhead.toNat≤33579) : C.lossMarks.card ≤ (lossLimit R.rect).ceil.toNat := by
  apply card_round
  have cum : (C.lossMarks.card : ℚ) ≤ (R.initial.rankMarks.card : ℚ) +
      ∑ i∈range 17,((curveMarks F (C.cover i)).card : ℚ) := by
    exact_mod_cast (show C.lossMarks.card ≤ R.initial.rankMarks.card +
      ∑ i∈range 17,(curveMarks F (C.cover i)).card from
        (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  have sum_cuts := sum_le_sum (fun _ mem=>C.curve_bin_count hi (mem_range.mp mem))
    (s:=range 17)
  rw [sum_add_distrib] at sum_cuts
  have both := add_le_add (R.initial.rank_count hi) sum_cuts
  have joint := R.joint_bill (rankWeight R.rect) (lossWeight R.rect)
  have seed := C.seed_bill
  have total := cum.trans both
  unfold lossLimit
  linarith only [total,joint,seed]
def CutBooks.paid {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G} (C : CutBooks R) :
    Finset K := ((C.lossMarks ∪ C.pointMarks) ∪ R.initial.seedMarks) ∪ R.initial.ordinateMarks
theorem CutBooks.paid_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {R : Run F Crt G}
    (C : CutBooks R) (hi : M.overhead.toNat≤33579) : C.paid.card≤rescueFee R.rect := by
  have h1 := card_union_le ((C.lossMarks∪C.pointMarks)∪R.initial.seedMarks) R.initial.ordinateMarks
  have h2 := card_union_le (C.lossMarks∪C.pointMarks) R.initial.seedMarks
  have h3 := card_union_le C.lossMarks C.pointMarks
  have rate := C.loss_count hi
  have points := card_round C.point_bill
  have seeds := R.initial.seed_count
  have ordinates := R.initial.ordinate_count
  unfold rescueFee CutBooks.paid
  omega
theorem exceptional_prefix {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2359≤M.overhead.toNat) (hi : M.overhead.toNat≤33579)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (common : PrefixRows.Common
      (evaluated Crt (word M) HelperSource.helperBank.shape (HelperSource.helperCutoff M.overhead.toNat)) G) :
    ∃ (paid : Finset K) (S : Finset Surface),
      paid.card ≤ 118460744183568976 ∧
      (∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 → γ∈paid ∨ ∃ q∈S,OnSurface F q γ := by
  obtain ⟨R,C,S,geom,cover⟩ := inventory F Crt lo hi noPole residues common
  refine ⟨C.paid,S,(C.paid_count hi).trans (rescue_fee_bound R.rect),geom,?_⟩
  intro γ hγ zero
  rcases cover γ hγ zero with seed | ordinate | rank | point | ⟨i,hi,curve,mem,on⟩ | retained
  · exact Or.inl (mem_union_left _ (mem_union_right _ seed))
  · exact Or.inl (mem_union_right _ ordinate)
  · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _
      (mem_union_left _ (mem_filter.mpr ⟨hγ,rank⟩)))))
  · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_right _ point)))
  · have cuts : γ∈(range 17).biUnion (fun i=>curveMarks F (C.cover i)) :=
      mem_biUnion.mpr ⟨i,mem_range.mpr hi,mem_curveMarks (F:=F) hγ mem on⟩
    exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ cuts))))
  · exact Or.inr retained
#print axioms exceptional_prefix
end Lower6960.RescueGeometry

end
end Merged_R6960RescueGeometryFee

-- merged module R6960MainGeometry
section Merged_R6960MainGeometry

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000

namespace Lower6960.MainGeometry
open Finset Polynomial
open K1 (I K)
open K1_14 (L Shape Jet jetAt seedHasse)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient toJet jetMarkHom)
open K1_14_2_2 (RowCaps Active dual orderOn FixedPart)
open K1_14_2_2R (chainCompatible)
open HelperPrefix (timesShape)
open HelperSource (helperBank helperCutoff)
open MainPrefixSource (copies hasse_at_mark)
open FreeSource (bank reserve cutoff)
open RescueGeometry (Model Family word OnMark terminalShape contact_at_mark zero_of_contact reserve_small)
open DifferentialContact (Native)
open PrefixRows (Prepared)
open P1_7_4 (ODEGuard degreeVector introJump introWeight)
open scoped Classical

def freeShape (i : Fin 17) : Shape := (bank i).shape

def movingShape (i : Fin 17) : Shape := timesShape (copies i) helperBank.shape

def stage (i : Fin 17) : P1_7.Stage := ⟨reserve i,bank i,⟨movingShape i,0,0⟩⟩

def cutShape (i : ℕ) : Shape :=
  if hi : i+1<17 then HighCore82258_3.envelope (stage ⟨i+1,hi⟩) else terminalShape

theorem cutShape_fit (i : ℕ) : (cutShape i).J≤(cutShape i).B := by
  unfold cutShape
  split
  · exact Nat.le_add_left _ _
  · decide

def introIndices : List (Fin 17) := [1,2,3,4,5,6,7,8,9,10,11,12]

def introAccount (k : Fin 4) : List (Fin 17) → (Fin 3→ℕ) → (Fin 3→ℕ) → ℕ
  | [], cap, old =>
      introJump cap old (movingShape 0) k +
        K1_14_2_2_2.ordinaryBudget (cap 2) (cap 0) k
  | i::rest, cap, old =>
      let s := freeShape i
      introJump cap old s k + introAccount k rest
        (fun j=>min (cap j) (degreeVector s j/(reserve i+1)))
        (fun j=>max (old j) (introWeight s k j))

def initialCap (k : Fin 4) : ℕ :=
  introAccount k introIndices (degreeVector (freeShape 0)) (fun _=>0)

theorem initial_small (k : Fin 4) : initialCap k < K1.p := by
  fin_cases k <;> decide +kernel

theorem free_ode_guard (i : Fin 17) : ODEGuard (freeShape i).B (freeShape i).J := by
  fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩

theorem moving_ode_guard (i : Fin 17) : ODEGuard (movingShape i).B (movingShape i).J := by
  fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩

theorem free_seed_small (i : Fin 17) : (freeShape i).U<K1.p :=
  (FreeSource.shape_guards i).2.2.2.1

theorem moving_seed_small (i : Fin 17) : (movingShape i).U<K1.p := by
  fin_cases i <;> decide +kernel

theorem reserve_pos {i : Fin 17} (hi : 0 < i.val) : 0<reserve i := by
  have checks (j : Fin 17) : (j.val=0) ∨ 0<reserve j := by
    fin_cases j <;> decide +kernel
  exact (checks i).resolve_left (by omega)

/-- The main branch retains the single preparation object, including the
original helper, its one possible exception, and the 17 stripped free rows. -/
structure Rows {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) where
  source : Fin 17→Jet
  out : Prepared source freeShape copies
    (evaluated Crt (word M) helperBank.shape (helperCutoff M.overhead.toNat)) helperBank.shape
  contact : ∀ i γ, γ∈Γ → jetAt out.exception (M.label γ) (F.scalar γ)≠0 →
    Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (reserve i+1) (out.free i) ∧
    Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (reserve i+1) (out.helper^copies i)
  fixedFree : ∀ i, FixedPart (out.free i) (freeShape i)
  fixedMoving : ∀ i, FixedPart (out.helper^copies i) (movingShape i)

theorem rows {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2359≤M.overhead.toNat) (hi : M.overhead.toNat≤33579)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    Nonempty (Rows F Crt) := by
  obtain ⟨P,out,_,inside,_⟩ := MainPrefixSource.rows Crt (word M) lo hi
  refine ⟨⟨P,out,?_,?_,?_⟩⟩
  · intro i γ mem regular
    have fit : reserve i+1 ≤ copies i*11 := by unfold copies; omega
    refine out.contacts i _ (RingHom.ker_isPrime _) ?_ (reserve i+1) 11 fit ?_ ?_
    · intro van
      apply regular
      simpa only [K1_14_2.eval_toJet] using RingHom.mem_ker.mp van
    · exact contact_at_mark F Crt noPole residues (inside i) (FreeSource.cutoff_fit lo hi i) γ mem
    · intro H hm
      have wh := HelperSource.helper_width lo hi
      have width : helperCutoff M.overhead.toNat+2*M.overhead.toNat*10 < helperBank.shape.m*179818 :=
        FreeSource.buffered_fit helperBank 179818 _ 10 wh
      exact contact_at_mark F Crt noPole residues hm width γ mem
  · intro i
    exact Classical.choice (K1_14_2_2_1.proof _ _ (out.free_ne i) (out.free_caps i))
  · intro i
    exact Classical.choice (K1_14_2_2_1.proof _ _ (pow_ne_zero _ out.helper_ne) (out.moving_caps i))

def Rows.marks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) : Finset K :=
  Γ.filter (fun γ=>jetAt R.out.exception (M.label γ) (F.scalar γ)≠0)

def Rows.family {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) : Family M R.marks :=
  ⟨F.scalar,fun γ hγ=>F.mark γ (mem_filter.mp hγ).1,F.distinct.mono (filter_subset _ _)⟩

theorem Rows.main_contact {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 17) (γ : K) (mem : γ∈R.marks) :
    Native (RingHom.ker (jetMarkHom (M.label γ) (R.family.scalar γ))) (reserve i+1) (R.out.free i) ∧
    Native (RingHom.ker (jetMarkHom (M.label γ) (R.family.scalar γ))) (reserve i+1) (R.out.helper^copies i) :=
  R.contact i γ (mem_filter.mp mem).1 (mem_filter.mp mem).2

theorem Rows.intro_tests {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 17) (j : Fin 2) (a : ℕ) (ha : a≤reserve i) (γ : K) (mem : γ∈R.marks) :
    jetAt (seedHasse j a (R.out.free i)) (M.label γ) (R.family.scalar γ)=0 :=
  hasse_at_mark (R.main_contact i γ mem).1 j a ha (ha.trans_lt (reserve_small i))

def Rows.Passes {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 17) (J : Ideal Ambient) : Prop :=
  orderOn J (R.out.free i) (reserve i+1) ∧
  orderOn J (R.out.helper^copies i) (reserve i+1) ∧ chainCompatible (R.out.free i) (R.out.helper^copies i) J

theorem Rows.failed_cut {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 17) {J : Ideal Ambient} (active : Active J) (dualJ : dual J) (fail : ¬R.Passes i J) :
    ∃ C : Jet,(RowCaps C (freeShape i) ∨ RowCaps C (movingShape i)) ∧ toJet C∉J ∧
      ∀ γ∈R.marks,OnMark R.family J γ → jetAt C (M.label γ) (R.family.scalar γ)=0 := by
  rcases PrefixStage.order_or_cut active dualJ (reserve_small i) (R.out.free_caps i) (R.out.moving_caps i)
    (pow_ne_zero _ R.out.helper_ne) (moving_ode_guard i).jpos with passes | ⟨C,cap,proper,zero⟩
  · exact (fail passes).elim
  · refine ⟨C,cap,proper,?_⟩
    intro γ hγ on
    obtain ⟨free,moving⟩ := R.main_contact i γ hγ
    exact zero _ _ on free moving

#print axioms rows
#print axioms Rows.failed_cut
end Lower6960.MainGeometry

end
end Merged_R6960MainGeometry

-- merged module R6960MainGeometryIntro
section Merged_R6960MainGeometryIntro

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.MainGeometry
open Finset Polynomial
open K1 (K)
open K1_14 (Shape Jet Seeds FX jetAt graphEval seedHasse atX)
open K1_14_1 (PoleData CRTLift)
open K1_14_2 (Ambient OnJet ODE fixedAt)
open K1_14_2_2 (RowCaps Active dual Fits FixedPart fixedOn mass sectionDegree sum_union_le ordinateIncl ODECaps)
open K1_14_2_2_2 (ordinaryBudget ordinate_eq length_le_mass)
open K1_14_3 (NoMovingCommon SeedCover joinCovers joinCovers_covers joinCovers_degree joinCovers_points)
open P1_7_4 (degreeVector introJump introWeight)
open P1_7_4_1 (SectionGeometry IntroFactors factorDegree factorMass factorMass_mono factorTariff
  weightedDegree tariff_step ordinary_charge residual_tariff collect proper_cover own_J_le_B own_caps retained_mass
  Stripped initial_factors strip)
open RescueGeometry (Model Family OnMark label_injective zero_of_contact)
open FreeSource (reserve)
open MainPrefixSource (copies)
open P1_7_4_1 (irreducible_cut terminal_piece)
open P0_10R_1 (seed_projection)
open scoped Classical BigOperators

private theorem intro_components
    {P Q : Jet} (hQ : Q ≠ 0) (hnc : NoMovingCommon P Q)
    (hQc : RowCaps Q (movingShape 0)) (later : Fin 17 → Jet)
    (rows : ∀ i, later i ≠ 0 ∧ RowCaps (later i) (freeShape i)) :
    ∀ (is : List (Fin 17)),
    ∀ (D : Finset Jet) (cap : Fin 3 → ℕ), IntroFactors P D → (∀ j, factorMass D j ≤ cap j) →
    ∃ S : Finset (Ideal Ambient), SectionGeometry S ∧
      (∀ k old, mass S k ≤ introAccount k is cap old + weightedDegree old D) ∧
      ∀ z R, (∀ i ∈ is, ∀ j a, a ≤ reserve i →
        jetAt (seedHasse j a (later i)) z R = 0) →
        jetAt Q z R = 0 → (∃ f ∈ D, jetAt f z R = 0) → ∃ I ∈ S, OnJet I z R := by
  classical
  intro is
  induction is with
  | nil =>
    intro D cap hD hcap
    let t := movingShape 0
    have gt := moving_ode_guard 0
    obtain ⟨S, hG, hS, hC⟩ := collect D
      (fun f k => factorTariff t k f + ordinaryBudget (factorDegree f 2) (factorDegree f 0) k)
      (fun f z R => jetAt f z R = 0 ∧ jetAt Q z R = 0)
      (terminal_piece hD hnc hQc gt.jb gt.small hQ)
    refine ⟨S, hG, ?_, ?_⟩
    · intro k old
      have hstep := tariff_step (Finset.empty_subset D) cap old t k hcap
      simp only [Finset.sdiff_empty, weightedDegree, factorMass, Finset.sum_empty,
        mul_zero, Finset.sum_const_zero, Nat.add_zero] at hstep
      have hsum := Nat.add_le_add hstep (ordinary_charge D cap hcap k)
      calc
        _ ≤ ∑ f ∈ D, (factorTariff t k f +
            ordinaryBudget (factorDegree f 2) (factorDegree f 0) k) := hS k
        _ ≤ (weightedDegree old D + introJump cap old t k) +
            ordinaryBudget (cap 2) (cap 0) k := by
          rw [Finset.sum_add_distrib]
          exact hsum
        _ = _ := by
          simp only [introAccount]
          ac_rfl
    · intro z R _ hq ⟨f, hf, hz⟩
      exact hC f hf z R ⟨hz, hq⟩
  | cons i is ih =>
    intro D cap hD hcap
    let s := freeShape i
    let r := reserve i
    let T := D.filter fun f => ∀ j a, a ≤ r → f ∣ seedHasse j a (later i)
    have hT : T ⊆ D := Finset.filter_subset _ _
    have gt := free_ode_guard i
    obtain ⟨hrow, hc⟩ := rows i
    have hTcap (j : Fin 3) :
        factorMass T j ≤ min (cap j) (degreeVector s j / (r+1)) :=
      le_min ((factorMass_mono hT j).trans (hcap j))
        (retained_mass (hD.mono hT) hrow hc (free_seed_small i) r
          (fun f hf => (Finset.mem_filter.mp hf).2) j)
    obtain ⟨laterCover, hLaterGeom, hLaterCap, hLater⟩ :=
      ih T _ (hD.mono hT) hTcap
    obtain ⟨discard, hDiscardGeom, hDiscardCap, hDiscard⟩ :=
      collect (D \ T) (fun f k => factorTariff s k f)
        (fun f z R => jetAt f z R = 0 ∧
          ∀ j a, a ≤ r → jetAt (seedHasse j a (later i)) z R = 0) (by
        intro f hf
        obtain ⟨hfD, hfT⟩ := Finset.mem_sdiff.mp hf
        have hn : ¬ ∀ j a, a ≤ r → f ∣ seedHasse j a (later i) :=
          fun hall => hfT (Finset.mem_filter.mpr ⟨hfD, hall⟩)
        push Not at hn
        obtain ⟨j, a, ha, hd⟩ := hn
        have hirr := (hD.factors f hfD).1
        obtain ⟨S, hG, hF, hC⟩ := proper_cover (irreducible_cut hirr hd)
          (own_J_le_B hirr.ne_zero) gt.jb (own_caps f) (P1_7_4_1_2.proof s (later i) hc j a)
        exact ⟨S, hG, fun k => (hF k).trans_eq (residual_tariff f s gt.jb k),
          fun z R hr => hC z R hr.1 (hr.2 j a ha)⟩)
    refine ⟨discard ∪ laterCover, ?_, ?_, ?_⟩
    · intro I hI
      exact (Finset.mem_union.mp hI).elim (hDiscardGeom I) (hLaterGeom I)
    · intro k old
      let w := fun j => max (old j) (introWeight s k j)
      let newCap := fun j => min (cap j) (degreeVector s j / (r+1))
      have hstep := tariff_step hT cap old s k hcap
      calc
        _ ≤ mass discard k + mass laterCover k := sum_union_le (fun I => sectionDegree I k) _ _
        _ ≤ (∑ f ∈ D \ T, factorTariff s k f) +
            (introAccount k is newCap w + weightedDegree w T) :=
          Nat.add_le_add (hDiscardCap k) (hLaterCap k w)
        _ = introAccount k is newCap w +
            ((∑ f ∈ D \ T, factorTariff s k f) + weightedDegree w T) := by ac_rfl
        _ ≤ introAccount k is newCap w + (weightedDegree old D + introJump cap old s k) :=
          Nat.add_le_add_left hstep _
        _ = _ := by
          change _ = (introJump cap old s k + introAccount k is newCap w) + weightedDegree old D
          ac_rfl
    · intro z R hder hq ⟨f, hf, hz⟩
      by_cases h : f ∈ T
      · obtain ⟨I, hI, hMark⟩ := hLater z R
          (fun l hl => hder l (List.mem_cons_of_mem _ hl)) hq ⟨f, h, hz⟩
        exact ⟨I, Finset.mem_union_right _ hI, hMark⟩
      · obtain ⟨I, hI, hMark⟩ := hDiscard f (Finset.mem_sdiff.mpr ⟨hf, h⟩) z R
          ⟨hz, hder i (List.mem_cons_self ..)⟩
        exact ⟨I, Finset.mem_union_left _ hI, hMark⟩

def Rows.fixedMarksOf {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) (G : ODE) : Finset K :=
  R.marks.filter (fun γ=>fixedAt G (R.family.scalar γ)=0)

def Rows.fixedMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) : Finset K :=
  (univ : Finset (Fin 17)).biUnion (fun i=>
    R.fixedMarksOf (R.fixedFree i).equation ∪ R.fixedMarksOf (R.fixedMoving i).equation)

theorem Rows.mem_fixed_free {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    {γ : K} (mark : γ∈R.marks) (i : Fin 17)
    (root : fixedAt (R.fixedFree i).equation (R.family.scalar γ)=0) : γ∈R.fixedMarks :=
  mem_biUnion.mpr ⟨i,mem_univ _,mem_union_left _ (mem_filter.mpr ⟨mark,root⟩)⟩

theorem Rows.mem_fixed_moving {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    {γ : K} (mark : γ∈R.marks) (i : Fin 17)
    (root : fixedAt (R.fixedMoving i).equation (R.family.scalar γ)=0) : γ∈R.fixedMarks :=
  mem_biUnion.mpr ⟨i,mem_univ _,mem_union_right _ (mem_filter.mpr ⟨mark,root⟩)⟩

def Rows.Clean {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) (J : Ideal Ambient) : Prop :=
  ∀ i, ¬ fixedOn (R.fixedFree i).equation J ∧ ¬ fixedOn (R.fixedMoving i).equation J

private theorem Rows.fixed_of_not_clean {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    {J : Ideal Ambient} {γ : K} (mark : γ∈R.marks) (on : OnMark R.family J γ)
    (bad : ¬R.Clean J) : γ∈R.fixedMarks := by
  by_contra absent
  apply bad
  intro i
  constructor
  · intro h
    apply absent (R.mem_fixed_free mark i ?_)
    simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on h)
  · intro h
    apply absent (R.mem_fixed_moving mark i ?_)
    simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on h)

private theorem Rows.sections {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) :
    ∃ S : Finset (Ideal Ambient),SectionGeometry S ∧ Fits S initialCap ∧
      ∃ content : Seeds, content≠0 ∧ content.totalDegree≤(freeShape 0).U ∧
      ∀ γ∈R.marks,γ∈R.fixedMarks ∨ graphEval (M.label γ) content=0 ∨ ∃ J∈S,OnMark R.family J γ := by
  obtain ⟨a⟩ := strip (R.out.free_ne 0) (R.out.free_caps 0) (R.fixedFree 0)
  obtain ⟨A,hA,hcap,hroot⟩ := initial_factors a
  obtain ⟨S,geom,fit,cover⟩ := intro_components (pow_ne_zero _ R.out.helper_ne)
    (R.out.no_moving 0) (R.out.moving_caps 0) R.out.free
    (fun i=>⟨R.out.free_ne i,R.out.free_caps i⟩) introIndices A _ hA hcap
  refine ⟨S,geom,?_,a.content,a.content_ne,a.content_le,?_⟩
  · intro k
    simpa only [initialCap,weightedDegree,zero_mul,Finset.sum_const_zero,Nat.add_zero] using fit k (fun _=>0)
  · intro γ hγ
    obtain ⟨p,q⟩ := R.main_contact 0 γ hγ
    rcases a.covers _ _ (zero_of_contact p) with hs | hf | hp
    · exact Or.inr (Or.inl hs)
    · exact Or.inl (R.mem_fixed_free hγ 0 hf)
    · exact Or.inr (Or.inr (cover _ _ (fun i _ j r hr=>R.intro_tests i j r hr γ hγ)
        (zero_of_contact q) (hroot _ _ hp)))

structure Initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) where
  seed : SeedCover
  seed_cap : seed.curve.totalDegree ≤ initialCap 2
  seed_points : seed.points.card ≤ initialCap 3
  ordinates : Finset FX
  ordinate_cap : ordinates.card ≤ initialCap 0
  content : Seeds
  content_ne : content≠0
  content_cap : content.totalDegree≤(freeShape 0).U
  rankExit : Finset (Ideal Ambient)
  parents : Finset (Ideal Ambient)
  fits : Fits (rankExit∪parents) initialCap
  disjoint : Disjoint rankExit parents
  rank_geom : ∀ J∈rankExit,Active J ∧ ¬dual J
  parent_geom : ∀ J∈parents,Active J ∧ dual J ∧ J.height=2 ∧ R.Clean J
  covers : ∀ γ∈R.marks,γ∈R.fixedMarks ∨ graphEval (M.label γ) content=0 ∨
    seed.Covers (M.label γ) ∨ atX (R.family.scalar γ)∈ordinates ∨
      (∃ J∈rankExit,OnMark R.family J γ) ∨ ∃ J∈parents,OnMark R.family J γ

/-- Form the initial affine section cover, remove fixed-factor marks, and
split the remaining active parents at the actual rank-exit index zero. -/
theorem Rows.initial_cover {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) :
    Nonempty (Initial R) := by
  obtain ⟨S,geom,fit,content,cn,cc,cover⟩ := R.sections
  let noSeeds := S.filter (fun J=>sectionDegree J 0=0)
  let constY := S.filter (fun J=>0<sectionDegree J 0 ∧
    ¬Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl))
  let active := S.filter (fun J=>0<sectionDegree J 0 ∧
    Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl))
  let rank := active.filter (fun J=>R.Clean J ∧ ¬dual J)
  let parents := active.filter (fun J=>R.Clean J ∧ dual J)
  have geomActive (J : Ideal Ambient) (mem : J∈active) : Active J ∧ J.height=2 := by
    obtain ⟨hin,seedPos,ord⟩ := mem_filter.mp mem
    obtain ⟨prime,dim,height,finite⟩ := geom J hin
    have small (k : Fin 4) := (length_le_mass hin k).trans_lt ((fit k).trans_lt (initial_small k))
    exact ⟨⟨prime,dim,finite.seeds,finite.ordinate,finite.mixed,finite.jets,
      ⟨seedPos,small 0⟩,small 2,small 3,ord⟩,height⟩
  have seed_exists (J : Ideal Ambient) (mem : J∈noSeeds) :
      ∃ C : SeedCover,C.curve.totalDegree≤sectionDegree J 2 ∧ C.points.card≤sectionDegree J 3 ∧
        ∀ z T,OnJet J z T → C.Covers z := by
    obtain ⟨hin,zero⟩ := mem_filter.mp mem
    obtain ⟨prime,dim,_,finite⟩ := geom J hin
    exact seed_projection J prime dim finite zero
  let seedImage (J : Ideal Ambient) : SeedCover :=
    if mem : J∈noSeeds then Classical.choose (seed_exists J mem) else ⟨1,one_ne_zero,∅⟩
  have seed_spec (J : Ideal Ambient) (mem : J∈noSeeds) :
      (seedImage J).curve.totalDegree≤sectionDegree J 2 ∧
        (seedImage J).points.card≤sectionDegree J 3 ∧
        ∀ z T,OnJet J z T → (seedImage J).Covers z := by
    simpa only [seedImage,dite_eq_left mem] using Classical.choose_spec (seed_exists J mem)
  let onY (J : Ideal Ambient) :=
    (R.marks.filter (OnMark R.family J)).image fun γ=>atX (R.family.scalar γ)
  have ordinate_bound (J : Ideal Ambient) (mem : J∈constY) : (onY J).card≤sectionDegree J 0 := by
    obtain ⟨hin,seedPos,ord⟩ := mem_filter.mp mem
    apply le_trans (b:=1) _ seedPos
    apply card_le_one.mpr
    intro y hy z hz
    obtain ⟨γ,hγ,rfl⟩ := mem_image.mp hy
    obtain ⟨δ,hδ,rfl⟩ := mem_image.mp hz
    exact ordinate_eq (geom J hin).1 ord (mem_filter.mp hγ).2 (mem_filter.mp hδ).2
  refine ⟨⟨joinCovers noSeeds seedImage,?_,?_,constY.biUnion onY,?_,content,cn,cc,
    rank,parents,?_,?_,?_,?_,?_⟩⟩
  · exact (joinCovers_degree _ _).trans ((sum_le_sum fun J mem=>(seed_spec J mem).1).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 2).trans (fit 2)))
  · exact (joinCovers_points _ _).trans ((sum_le_sum fun J mem=>(seed_spec J mem).2.1).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 3).trans (fit 3)))
  · exact card_biUnion_le.trans ((sum_le_sum ordinate_bound).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 0).trans (fit 0)))
  · apply K1_14_2_2.fits_mono _ fit
    exact union_subset ((filter_subset _ _).trans (filter_subset _ _))
      ((filter_subset _ _).trans (filter_subset _ _))
  · exact disjoint_left.mpr fun _ a b=>(mem_filter.mp a).2.2 (mem_filter.mp b).2.2
  · intro J mem
    exact ⟨(geomActive J (mem_filter.mp mem).1).1,(mem_filter.mp mem).2.2⟩
  · intro J mem
    obtain ⟨hin,c,d⟩ := mem_filter.mp mem
    obtain ⟨act,ht⟩ := geomActive J hin
    exact ⟨act,d,ht,c⟩
  · intro γ hγ
    rcases cover γ hγ with fixed | seed | ⟨J,hin,on⟩
    · exact Or.inl fixed
    · exact Or.inr (Or.inl seed)
    · by_cases z : sectionDegree J 0=0
      · have mem : J∈noSeeds := mem_filter.mpr ⟨hin,z⟩
        exact Or.inr (Or.inr (Or.inl (joinCovers_covers mem ((seed_spec J mem).2.2 _ _ on))))
      · by_cases ord : Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl)
        · have mem : J∈active := mem_filter.mpr ⟨hin,Nat.pos_of_ne_zero z,ord⟩
          by_cases clean : R.Clean J
          · by_cases d : dual J
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨J,mem_filter.mpr ⟨mem,clean,d⟩,on⟩))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨J,mem_filter.mpr ⟨mem,clean,d⟩,on⟩))))
          · exact Or.inl (R.fixed_of_not_clean hγ on clean)
        · have mem : J∈constY := mem_filter.mpr ⟨hin,Nat.pos_of_ne_zero z,ord⟩
          exact Or.inr (Or.inr (Or.inr (Or.inl (mem_biUnion.mpr ⟨J,mem,
            mem_image.mpr ⟨γ,mem_filter.mpr ⟨hγ,on⟩,rfl⟩⟩))))

theorem Initial.rank_ode {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ∃ E : ODE, ODECaps E (mass ini.rankExit 2) (mass ini.rankExit 1) ∧
      ∀ γ∈R.marks,(∃ J∈ini.rankExit,OnMark R.family J γ) → fixedAt E (R.family.scalar γ)=0 := by
  obtain ⟨E,caps,roots⟩ := P1_7_4.rank_equation ini.rankExit ini.rank_geom le_rfl le_rfl
  refine ⟨E,caps,?_⟩
  rintro γ _ ⟨J,hJ,on⟩
  simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on (roots J hJ))

#print axioms Rows.initial_cover
#print axioms Initial.rank_ode
end Lower6960.MainGeometry

end
end Merged_R6960MainGeometryIntro

-- merged module R6960MainGeometryProcess
section Merged_R6960MainGeometryProcess

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.MainGeometry
open Finset Polynomial
open K1 (K)
open K1_14 (Shape Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues evaluated evaluated_shape nodeL)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 (RowCaps Active dual mass mass_mono sectionDegree CutCover weight dot
  emptyCut joinCuts joinCuts_cost sum_dot)
open K1_14_3 (Surface Parent)
open P0_10R.Bridge (surfaceOf parent_of_dual)
open P1_7_4 (Mass massQ massQ_mono pairedCap)
open RescueGeometry (Model Family OnMark OnSurface SurfacePass TerminalPass word terminalShape terminalCutoff
  contact_at_mark zero_of_contact reserve_small)
open MainPrefixSource (copies)
open FreeSource (reserve)
open HighCore82258_3 (envelope_caps)
open Lower6960.RescueGeometry (proper_cut)
open scoped Classical BigOperators

def Initial.kept {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) : Finset (Ideal Ambient) :=
  ini.parents.filter (fun J=>∀ i : Fin 17,0 < i.val → i.val≤n → R.Passes i J)

theorem Initial.kept_zero {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ini.kept 0=ini.parents := by
  ext J
  constructor
  · exact fun h=>(mem_filter.mp h).1
  · intro h
    apply mem_filter.mpr
    refine ⟨h,fun i pos zero=>?_⟩
    omega

theorem Initial.kept_anti {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    Antitone ini.kept := by
  intro m n le J mem
  obtain ⟨p,pass⟩ := mem_filter.mp mem
  exact mem_filter.mpr ⟨p,fun i hi hm=>pass i hi (hm.trans le)⟩

theorem Initial.kept_geom {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {n : ℕ} {J : Ideal Ambient} (mem : J∈ini.kept n) :
    Active J ∧ dual J ∧ J.height=2 ∧ R.Clean J :=
  ini.parent_geom J (mem_filter.mp mem).1

def Initial.final {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    Finset (Ideal Ambient) :=
  (ini.kept 16).filter (TerminalPass Crt (word M))

def Initial.live {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) : Finset (Ideal Ambient) := if n<17 then ini.kept n else ini.final

def Initial.lost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) : Finset (Ideal Ambient) := ini.live n \ ini.live (n+1)

theorem Initial.live_zero {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ini.live 0=ini.parents := by
  rw [Initial.live,ite_eq_left (by decide : 0<17),ini.kept_zero]

theorem Initial.next_sub {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<17) : ini.live (i+1)⊆ini.live i := by
  by_cases hn : i+1<17
  · simp only [Initial.live,ite_eq_left hi,ite_eq_left hn]
    exact ini.kept_anti (Nat.le_succ _)
  · have eq : i=16 := by omega
    subst i
    exact filter_subset _ _

theorem Initial.stage_mass {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (i : Fin 17) (hi : 0 < i.val) {n : ℕ} (step : i.val≤n) (k : Fin 4) :
    massQ (ini.kept n) k≤pairedCap (freeShape i) (movingShape i) (reserve i) true k := by
  have s := free_ode_guard i
  have t := moving_ode_guard i
  apply P1_7_4_2.proof (freeShape i) (movingShape i) (reserve i) true (R.out.free i)
    (R.out.helper^copies i) (reserve_pos hi) (reserve_small i) s.small t.small
    (free_seed_small i) (moving_seed_small i) s.jb t.jb (R.out.free_ne i)
    (pow_ne_zero _ R.out.helper_ne) (R.out.free_caps i) (R.out.moving_caps i)
    (R.out.no_moving i) (R.fixedFree i) (R.fixedMoving i)
  · intro _ J mem
    exact (ini.kept_geom mem).2.1
  · intro J mem
    have geom := ini.kept_geom mem
    have pass := (mem_filter.mp mem).2 i hi step
    have clean := geom.2.2.2 i
    exact ⟨geom.1,pass.2.2,clean.1,clean.2,pass.1,pass.2.1⟩

/-- Every failing parent has a marked cutter with the exact stage envelope.
The terminal failure uses a row of the common full bank. -/
theorem Initial.marked_cutter {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {i : ℕ} {J : Ideal Ambient} (hi : i<17) (mem : J∈ini.lost i) :
    ∃ C : Jet,RowCaps C (cutShape i) ∧ toJet C∉J ∧
      ∀ γ∈R.marks,OnMark R.family J γ → jetAt C (M.label γ) (R.family.scalar γ)=0 := by
  obtain ⟨prev,lost⟩ := mem_sdiff.mp mem
  rw [Initial.live,ite_eq_left hi] at prev
  by_cases hn : i+1<17
  · let j : Fin 17 := ⟨i+1,hn⟩
    have hf : ¬R.Passes j J := by
      intro p
      apply lost
      rw [Initial.live,ite_eq_left hn]
      apply mem_filter.mpr
      refine ⟨(mem_filter.mp prev).1,?_⟩
      intro z hz ht
      by_cases same : z.val=i+1
      · exact (Fin.ext same : z=j) ▸ p
      · exact (mem_filter.mp prev).2 z hz (by omega)
    have geom := ini.kept_geom prev
    obtain ⟨C,cap,proper,zero⟩ := R.failed_cut j geom.1 geom.2.1 hf
    refine ⟨C,?_,proper,zero⟩
    rw [cutShape,dite_eq_left hn]
    exact envelope_caps (s:=stage j) (free_ode_guard j).jb (moving_ode_guard j).jb cap
  · have eq : i=16 := by omega
    subst i
    have hf : ¬ TerminalPass Crt (word M) J := fun p =>
      lost (mem_filter.mpr ⟨prev,p⟩)
    obtain ⟨s,C,sm,inside,cap,proper⟩ := RescueGeometry.terminal_failure Crt (word M) hf
    refine ⟨C,cap,proper,?_⟩
    intro γ hγ _
    apply zero_of_contact (r:=0)
    exact contact_at_mark R.family Crt noPole
      (fun δ hd=>residues δ (mem_filter.mp hd).1) inside
      (by simpa only [Nat.mul_zero,Nat.add_zero] using Nat.sub_lt (Nat.mul_pos sm (by decide : 0<179818)) (by decide : 0<1)) γ hγ

theorem Initial.cutCover {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {i : ℕ} (hi : i<17) :
    ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight (cutShape i) fee) (mass (ini.lost i))) ∧
      ∀ γ∈R.marks,(∃ J∈ini.lost i,OnMark R.family J γ) → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark R.family Q γ := by
  have oneCut (J : Ideal Ambient) (mem : J∈ini.lost i) :
      ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight (cutShape i) fee) (sectionDegree J)) ∧
        ∀ γ∈R.marks,OnMark R.family J γ → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark R.family Q γ := by
    obtain ⟨P,cap,proper,zero⟩ := ini.marked_cutter noPole residues hi mem
    have prev := (mem_sdiff.mp mem).1
    rw [Initial.live,ite_eq_left hi] at prev
    let sub := R.marks.filter (OnMark R.family J)
    let G : Family M sub :=
      ⟨R.family.scalar,fun γ hγ=>R.family.mark γ (mem_filter.mp hγ).1,
        R.family.distinct.mono (filter_subset _ _)⟩
    obtain ⟨C,cost,cover⟩ := proper_cut G (cutShape i) (cutShape_fit i)
      (ini.kept_geom prev).1 cap proper
      (fun γ hγ=>zero γ (mem_filter.mp hγ).1 (mem_filter.mp hγ).2)
    exact ⟨C,cost,fun γ hγ on=>cover γ (mem_filter.mpr ⟨hγ,on⟩) on⟩
  let C (J : Ideal Ambient) : CutCover :=
    if mem : J∈ini.lost i then Classical.choose (oneCut J mem) else emptyCut
  have spec (J : Ideal Ambient) (mem : J∈ini.lost i) :
      (∀ fee,(C J).cost fee≤dot (weight (cutShape i) fee) (sectionDegree J)) ∧
        ∀ γ∈R.marks,OnMark R.family J γ → γ∈(C J).direct ∨ ∃ Q∈(C J).curves,OnMark R.family Q γ := by
    simpa only [C,dite_eq_left mem] using Classical.choose_spec (oneCut J mem)
  refine ⟨joinCuts (ini.lost i) C,?_,?_⟩
  · intro fee
    exact (joinCuts_cost _ _ _).trans ((sum_le_sum fun J mem => (spec J mem).1 fee).trans_eq (sum_dot _ _))
  · rintro γ hγ ⟨J,mem,on⟩
    rcases (spec J mem).2 γ hγ on with point | ⟨Q,hQ,hmark⟩
    · exact Or.inl (mem_biUnion.mpr ⟨J,mem,point⟩)
    · exact Or.inr ⟨Q,mem_biUnion.mpr ⟨J,mem,hQ⟩,hmark⟩

theorem Initial.retained_or_lost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {J : Ideal Ambient} (mem : J∈ini.parents) :
    J∈ini.final ∨ ∃ i<17,J∈ini.lost i := by
  by_cases h : ∃ i<17,J∈ini.lost i
  · exact Or.inr h
  · have alive : ∀ n≤17,J∈ini.live n := by
      intro n hn
      induction n with
      | zero => exact ini.live_zero.symm ▸ mem
      | succ n ih =>
        by_contra absent
        exact h ⟨n,by omega,mem_sdiff.mpr ⟨ih (by omega),absent⟩⟩
    exact Or.inl (by simpa [Initial.live] using alive 17 le_rfl)

theorem Initial.terminal_surfaces_with_origins {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ∃ S : Finset Surface,(∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      (∀ q∈S,∃ J∈ini.final,q.asIdeal=J.comap K1_14_2.toJet) ∧
      ∀ γ∈R.marks,(∃ J∈ini.final,OnMark R.family J γ) → ∃ q∈S,OnSurface F q γ := by
  let geom (J : ini.final) := ini.kept_geom (mem_filter.mp J.property).1
  let surface (J : ini.final) := surfaceOf J.val (geom J).1.prime
  let S := ini.final.attach.image surface
  refine ⟨S,?_,?_,?_⟩
  · intro q hq
    obtain ⟨J,_,rfl⟩ := mem_image.mp hq
    have hJ := geom J
    exact ⟨parent_of_dual hJ.1 hJ.2.2.1 hJ.2.1,(mem_filter.mp J.property).2⟩
  · intro q hq
    obtain ⟨J,_,rfl⟩:=mem_image.mp hq
    exact ⟨J.val,J.property,rfl⟩
  · rintro γ _ ⟨J,hJ,on⟩
    let q : ini.final := ⟨J,hJ⟩
    refine ⟨surface q,mem_image.mpr ⟨q,mem_attach _ _,rfl⟩,?_⟩
    intro P mem
    rw [←K1_14_2.eval_toJet]
    exact RingHom.mem_ker.mp (on mem)

theorem Initial.terminal_surfaces {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ∃ S : Finset Surface,(∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈R.marks,(∃ J∈ini.final,OnMark R.family J γ) → ∃ q∈S,OnSurface F q γ := by
  obtain ⟨S,geom,_,marks⟩:=ini.terminal_surfaces_with_origins
  exact ⟨S,geom,marks⟩

#print axioms Initial.stage_mass
#print axioms Initial.cutCover
#print axioms Initial.terminal_surfaces
end Lower6960.MainGeometry

end
end Merged_R6960MainGeometryProcess

-- merged module R6960MainGeometryBills
section Merged_R6960MainGeometryBills

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000

namespace Lower6960.MainGeometry
open Finset Polynomial
open K1 (K)
open K1_14 (Jet atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient)
open K1_14_2_2 (mass mass_mono weight dot CutCover emptyCut)
open P1_7_4 (Mass massQ massQ_mono dotQ pairedCap weightedBill bill_bound)
open RescueGeometry (Model Family OnMark label_injective beforeCuts fixedFee fixed_count)
open FreeSource (reserve)
open scoped Classical BigOperators

def initialMass : Mass := fun k=>initialCap k

private def historyTable : List Mass :=
  [
    ![10597, 106674, 492190, 2145993],
    ![5756, 165809/2, 375084, 1980456],
    ![22349/9, 351832/9, 375084, 1915456],
    ![13715/8, 390915/16, 1775816/9, 9168368/9],
    ![5216/5, 407313/25, 130626, 734373],
    ![4699/6, 145283/12, 248109/2, 2772225/4],
    ![34803/64, 501165/64, 80446, 1016044/3],
    ![39209/121, 579508/121, 2652560/49, 259081],
    ![39209/121, 579508/121, 48147, 259081],
    ![39209/121, 579508/121, 48147, 1006009/4],
    ![11153/40, 865023/200, 1943756/49, 216225],
    ![253791/961, 3699363/961, 4120626/121, 15944049/100],
    ![38497/150, 3699363/961, 4115580/121, 15944049/100],
    ![38497/150, 3699363/961, 4115580/121, 15944049/100],
    ![1173662/4761, 5666773/1587, 8407560/289, 99765932/729],
    ![1140713/5184, 17363647/5184, 141744/5, 99765932/729],
    ![1140713/5184, 17363647/5184, 3051745/108, 48750750/361]
  ]

def history (i : ℕ) : Mass := historyTable.getD i initialMass

theorem history_zero (k : Fin 4) : history 0 k=initialMass k := by
  fin_cases k <;> decide +kernel

theorem history_step (i : Fin 16) (k : Fin 4) :
    let j : Fin 17 := ⟨i.val+1,by have := i.isLt; omega⟩
    history (i.val+1) k =
      min (history i.val k) (pairedCap (freeShape j) (movingShape j) (reserve j) true k) := by
  fin_cases i <;> fin_cases k <;> decide +kernel

theorem Initial.cap_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) (k : Fin 4) : massQ (ini.kept n) k ≤ initialMass k := by
  exact (Nat.cast_le (α:=ℚ)).mpr ((mass_mono
    ((filter_subset _ _).trans subset_union_right) k).trans (ini.fits k))

theorem Initial.cap_kept {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<17) (k : Fin 4) : massQ (ini.kept i) k≤history i k := by
  induction i with
  | zero => rw [history_zero]; exact ini.cap_initial _ _
  | succ i ih =>
    have hl : i<16 := by omega
    have hstep := history_step ⟨i,hl⟩ k
    dsimp only at hstep
    rw [hstep]
    exact le_min ((massQ_mono (ini.kept_anti (Nat.le_succ i)) k).trans (ih (by omega)))
      (ini.stage_mass ⟨i+1,hi⟩ (Nat.succ_pos _) le_rfl k)

theorem Initial.cap_live {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<17) (k : Fin 4) : massQ (ini.live i) k≤history i k := by
  rw [Initial.live,ite_eq_left hi]
  exact ini.cap_kept hi k

theorem Initial.live_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<17) (k : Fin 4) : massQ (ini.live i) k ≤ initialMass k := by
  rw [Initial.live,ite_eq_left hi]
  exact ini.cap_initial _ k

def cutWeight (fee : Fin 3) (i : ℕ) : Mass := fun k=>weight (cutShape i) fee k

def seedLimit : ℚ := weightedBill 17 (cutWeight 0) history

def pointLimit : ℚ := weightedBill 17 (cutWeight 2) (fun _=>initialMass)

def initialSeedLimit : ℕ := (K1.p+1)*initialCap 2+initialCap 3

def contentLimit : ℕ := (K1.p+1)*(freeShape 0).U

def fixedLimit : ℕ :=
  ∑ i : Fin 17, (fixedFee (freeShape i).B (freeShape i).J+fixedFee (movingShape i).B (movingShape i).J)

theorem seed_limit_small : seedLimit < (K1.p : ℚ) := by decide +kernel

theorem Initial.ordinary_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    (R.marks.filter (fun γ=>atX (R.family.scalar γ)∈ini.ordinates)).card ≤ initialCap 0 := by
  apply (card_le_card_of_injOn (fun γ=>atX (R.family.scalar γ))
    (fun _ hγ=>(mem_filter.mp hγ).2) ?_).trans ini.ordinate_cap
  intro γ hγ δ hδ eq
  exact R.family.distinct (mem_filter.mp hγ).1 (mem_filter.mp hδ).1
    (K1_14_3.scalar_atX_injective eq)

theorem Initial.seed_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    (R.marks.filter (fun γ=>ini.seed.Covers (M.label γ))).card ≤ initialSeedLimit := by
  have bound := K1_14_3.seed_count
    (T:=R.marks.filter (fun γ=>ini.seed.Covers (M.label γ))) (label_injective M).injOn ini.seed
    (ini.seed_cap.trans_lt (initial_small 2)) (fun _ hγ=>(mem_filter.mp hγ).2)
  exact bound.trans (Nat.add_le_add (Nat.mul_le_mul_left _ ini.seed_cap) ini.seed_points)

theorem Initial.content_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    (R.marks.filter (fun γ=>graphEval (M.label γ) ini.content=0)).card≤contentLimit := by
  let C : K1_14_3.SeedCover := ⟨ini.content,ini.content_ne,∅⟩
  have bound := K1_14_3.seed_count
    (T:=R.marks.filter (fun γ=>graphEval (M.label γ) ini.content=0)) (label_injective M).injOn C
    (ini.content_cap.trans_lt (free_seed_small 0)) (fun _ hγ=>Or.inl (mem_filter.mp hγ).2)
  exact (by simpa only [C,card_empty,Nat.add_zero] using bound :
    (R.marks.filter (fun γ=>graphEval (M.label γ) ini.content=0)).card≤(K1.p+1)*ini.content.totalDegree)
    |>.trans (Nat.mul_le_mul_left _ ini.content_cap)

theorem Rows.fixed_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) (hi : M.overhead.toNat≤33579) :
    R.fixedMarks.card≤fixedLimit := by
  calc
    _ ≤ ∑ i : Fin 17, (R.fixedMarksOf (R.fixedFree i).equation ∪ R.fixedMarksOf (R.fixedMoving i).equation).card :=
      card_biUnion_le
    _ ≤ _ := sum_le_sum fun i _=>(card_union_le _ _).trans (Nat.add_le_add
      (RescueGeometry.fixed_count R.family hi (free_ode_guard i) _ (R.fixedFree i).equation_caps (filter_subset _ _)
        (fun _ hm=>(mem_filter.mp hm).2))
      (RescueGeometry.fixed_count R.family hi (moving_ode_guard i) _ (R.fixedMoving i).equation_caps (filter_subset _ _)
        (fun _ hm=>(mem_filter.mp hm).2)))

structure CutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) where
  cover : ℕ→CutCover
  cost : ∀ i<17,∀ fee,(cover i).cost fee ≤ dot (weight (cutShape i) fee) (mass (ini.lost i))
  covers : ∀ i<17,∀ γ∈R.marks,(∃ J∈ini.lost i,OnMark R.family J γ) →
    γ∈(cover i).direct ∨ ∃ Q∈(cover i).curves,OnMark R.family Q γ

theorem Initial.cutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) : Nonempty (CutBooks ini) := by
  have pick (i : ℕ) : ∃ C : CutCover,i<17 →
      (∀ fee,C.cost fee ≤ dot (weight (cutShape i) fee) (mass (ini.lost i))) ∧
      ∀ γ∈R.marks,(∃ J∈ini.lost i,OnMark R.family J γ) → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark R.family Q γ := by
    by_cases hi : i<17
    · obtain ⟨C,cap,cover⟩ := ini.cutCover noPole residues hi
      exact ⟨C,fun _=>⟨cap,cover⟩⟩
    · exact ⟨emptyCut,fun h=>(hi h).elim⟩
  choose C hC using pick
  exact ⟨⟨C,fun i h=>(hC i h).1,fun i h=>(hC i h).2⟩⟩

theorem CutBooks.costQ {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) {i : ℕ} (hi : i<17) (fee : Fin 3) :
    ((C.cover i).cost fee : ℚ)≤dotQ (cutWeight fee i) (massQ (ini.lost i)) := by
  have bound := (Nat.cast_le (α:=ℚ)).mpr (C.cost i hi fee)
  simpa only [cutWeight,dotQ,dot,massQ,Nat.cast_sum,Nat.cast_mul] using bound

theorem CutBooks.seed_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : (∑ i∈range 17,((C.cover i).cost 0 : ℚ))≤seedLimit :=
  (sum_le_sum fun _ h=>C.costQ (mem_range.mp h) 0).trans
    (bill_bound 17 _ _ ini.live ini.lost (fun _ hi=>ini.next_sub hi) (fun _ _=>subset_rfl)
      (fun _ hi=>ini.cap_live hi))

def CutBooks.pointMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : Finset K := (range 17).biUnion fun i=>(C.cover i).direct

theorem CutBooks.point_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : (C.pointMarks.card : ℚ) ≤ pointLimit := by
  calc
    _ ≤ ∑ i∈range 17,((C.cover i).cost 2 : ℚ) := by
      exact_mod_cast (show C.pointMarks.card ≤ ∑ i∈range 17,(C.cover i).direct.card from card_biUnion_le)
    _ ≤ ∑ i∈range 17,dotQ (cutWeight 2 i) (massQ (ini.lost i)) :=
      sum_le_sum fun i h=>C.costQ (mem_range.mp h) 2
    _ ≤ _ := bill_bound 17 _ _ ini.live ini.lost (fun _ hi=>ini.next_sub hi) (fun _ _=>subset_rfl)
      (fun _ hi=>ini.live_initial hi)

private def Initial.jointLive {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ℕ→Finset (Ideal Ambient)
  | 0 => ini.rankExit∪ini.parents
  | i+1 => ini.live i

private def Initial.jointLost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ℕ→Finset (Ideal Ambient)
  | 0 => ini.rankExit
  | i+1 => ini.lost i

/-- The rank exit and the seventeen cut bins spend a single weighted
history, starting from the mass of the initial proper cover. -/
theorem Initial.joint_bill_with_final {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (rank : Mass) (cut : ℕ→Mass) :
    dotQ rank (massQ ini.rankExit) + (∑ i∈range 17,dotQ (cut i) (massQ (ini.lost i))) +
      dotQ (P1_7_4.running (beforeCuts rank cut) 18) (massQ ini.final) ≤
      weightedBill 18 (beforeCuts rank cut) (beforeCuts (initialMass) (history)) := by
  have bill := P1_7_4.bill_bound_with_final 18 (beforeCuts rank cut) (beforeCuts (initialMass) (history))
    ini.jointLive ini.jointLost ?_ ?_ ?_
  · rw [show 18=17+1 by decide,sum_range_succ'] at bill
    have final : ini.jointLive 18 = ini.final := by simp [Initial.jointLive,Initial.live]
    simpa only [beforeCuts,Initial.jointLost,final,add_comm] using bill
  · intro i hi
    cases i with
    | zero => simpa only [Initial.jointLive,ini.live_zero] using
        (subset_union_right : ini.parents⊆ ini.rankExit∪ini.parents)
    | succ i => exact ini.next_sub (by omega)
  · intro i hi
    cases i with
    | zero =>
      intro J mem
      apply mem_sdiff.mpr
      refine ⟨mem_union_left _ mem,?_⟩
      rw [Initial.jointLive,ini.live_zero]
      exact fun h=>(disjoint_left.mp ini.disjoint) mem h
    | succ i => exact subset_rfl
  · intro i hi k
    cases i with
    | zero => exact (Nat.cast_le (α:=ℚ)).mpr (ini.fits k)
    | succ i => exact ini.cap_live (by omega) k


#print axioms history_step
#print axioms Rows.fixed_count
theorem Initial.joint_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (rank : Mass) (cut : ℕ→Mass) :
    dotQ rank (massQ ini.rankExit) + (∑ i∈range 17,dotQ (cut i) (massQ (ini.lost i))) ≤
      weightedBill 18 (beforeCuts rank cut) (beforeCuts initialMass history) :=
  (le_add_of_nonneg_right (P1_7_4.final_credit_nonneg 18 (beforeCuts rank cut) ini.final)).trans
    (ini.joint_bill_with_final rank cut)

#print axioms Initial.joint_bill
#print axioms CutBooks.point_bill
end Lower6960.MainGeometry

end
end Merged_R6960MainGeometryBills

-- merged module R6960MainGeometryInvoice
section Merged_R6960MainGeometryInvoice

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.MainGeometry
open Finset
open K1 (p)
open P1_7_4 (Mass dotQ weightedBill)
open RescueGeometry (RateOK beforeCuts lambda mu tau)
open Lower6960.RescueGeometry (heightBound height_spec)
open scoped Classical BigOperators

def degreeRates : List ℕ :=
  [155997388, 155997388, 155997388, 155997388, 155997388, 155997388, 155997388, 80403997, 41020580, 80403997, 118503960, 41707115, 117383052, 94698036, 94698036, 132932404, 218921550]

def heightRates : List ℕ :=
  [3042427, 3042427, 3042427, 3042427, 3042427, 3042427, 3042427, 6114031, 12228062, 6114031, 4076021, 12022955, 4114661, 5152695, 5152695, 3606887, 2100971]

def degreeRate (i : ℕ) : ℕ := degreeRates.getD i 0

def heightRate (i : ℕ) : ℕ := heightRates.getD i 0

private theorem checked_rates (i : Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate i.val : ℚ) ∧
      min seedLimit (dotQ (cutWeight 0 i.val) (history i.val)) ≤ (degreeRate i.val : ℚ) ∧
      heightBound (degreeRate i.val) ≤ (heightRate i.val : ℚ) := by
  fin_cases i <;> decide +kernel

theorem rate_spec {i : ℕ} (hi : i<17) :
    RateOK (degreeRate i) (heightRate i) ∧
      min seedLimit (dotQ (cutWeight 0 i) (history i)) ≤ degreeRate i := by
  obtain ⟨base,degree,height⟩ := checked_rates ⟨i,hi⟩
  exact ⟨⟨base,Nat.cast_nonneg _,fun g hp hg=>(height_spec _ g hp hg).trans height⟩,degree⟩

def rankB : ℕ := initialCap 2+2

def rankJ : ℕ := initialCap 1+1

def pivot : ℚ := min (47843/5) (tau*rankB)

def rankWeight : Mass :=
  ![0,4*lambda*rankB*tau+mu-4*lambda*pivot,4*lambda*rankJ*(1-tau)+rankB,0]

def rankRound : ℚ := rankWeight 1+2*rankWeight 2+2*lambda*pivot^2+1

def lossWeight (i : ℕ) : Mass :=
  fun k=>(degreeRate i : ℚ)*cutWeight 0 i k+(heightRate i : ℚ)*cutWeight 1 i k

def lossLimit : ℚ :=
  weightedBill 18 (beforeCuts rankWeight lossWeight) (beforeCuts initialMass history)+seedLimit+rankRound

def mainFee : ℕ := lossLimit.ceil.toNat+pointLimit.ceil.toNat+initialSeedLimit+initialCap 0+
  fixedLimit+contentLimit

theorem main_fee_bound : mainFee ≤ 116835760512599839 := by decide +kernel

theorem rank_guard : rankB<p ∧ 0≤rankWeight 1 ∧ 0≤rankWeight 2 := by decide +kernel

#print axioms main_fee_bound
#print axioms rate_spec
end Lower6960.MainGeometry

end
end Merged_R6960MainGeometryInvoice

end Merged6967_R6960MainGeometryInvoice

section Merged6967_R6966ProofPadeIntegralGraph
set_option Elab.async false


set_option Elab.async false

namespace Research6966.PadeIntegralGraph
open Polynomial Finset Module
open K1_14 (L FX Seeds)
open K1_14_1 (jetConstant)
open K1_14_1_4 (doubleMap evalRaw)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 16

private abbrev k:=K1_14_1.SeedField
private abbrev B:=K1_14_3.SeedField

def joint : FractionRing k[X] →+* B := IsFractionRing.lift PadeRawField.eval_injective

theorem joint_raw (x:k[X]) : joint (algebraMap k[X] (FractionRing k[X]) x)=evalRaw x :=
  IsFractionRing.lift_algebraMap PadeRawField.eval_injective x

private theorem restrict_joint : joint.comp (algebraMap k[X] (FractionRing k[X]))=evalRaw :=
  RingHom.ext joint_raw

/-- Both orders of adjoining the physical coordinate and the seeds give
the same rational function field, including in positive characteristic. -/
theorem joint_surjective : Function.Surjective joint := by
  let S:=joint.fieldRange
  have raw (p:k[X]) : evalRaw p∈S :=
    ⟨algebraMap k[X] (FractionRing k[X]) p,IsFractionRing.lift_algebraMap PadeRawField.eval_injective p⟩
  have physical (p:L[X]) : algebraMap FX B (algebraMap L[X] FX p)∈S :=
    RingHom.congr_fun K1_14_1_4.evalRaw_physical p ▸ raw (p.map (algebraMap L k))
  have scalar (p:FX) : algebraMap FX B p∈S := by
    obtain ⟨n,d,_,rfl⟩:=IsFractionRing.div_surjective L[X] p
    rw [map_div₀]
    exact S.div_mem (physical n) (physical d)
  have seed (p:Seeds) : algebraMap Seeds B p∈S := by
    induction p using MvPolynomial.induction_on with
    | C x =>
      change algebraMap Seeds B (algebraMap FX Seeds x)∈S
      rw [←IsScalarTower.algebraMap_apply]
      exact scalar x
    | add p q hp hq=>rw [map_add];exact S.add_mem hp hq
    | mul_X p i hp=>
      rw [map_mul]
      exact S.mul_mem hp (K1_14_1_4.evalRaw_seed i ▸ raw _)
  intro z
  obtain ⟨p,q,_,rfl⟩:=IsFractionRing.div_surjective Seeds z
  exact S.div_mem (seed p) (seed q)

private def jointEquiv : FractionRing k[X] ≃+* B :=
  RingEquiv.ofBijective joint ⟨joint.injective,joint_surjective⟩

private theorem double_comp {R A F:Type*} [CommSemiring R] [CommSemiring A] [CommSemiring F]
    (g:A→+*F) (f:R→+*A) (P:R[X][X]) :
    doubleMap g (doubleMap f P)=doubleMap (g.comp f) P := by
  ext j i;simp only [doubleMap,coe_mapRingHom,coeff_map,RingHom.comp_apply]

private theorem double_jet {R A:Type*} [CommSemiring R] [CommSemiring A] (f:R→+*A) (c:R) :
    doubleMap f (jetConstant c)=jetConstant (f c) := by
  simp only [doubleMap,jetConstant,coe_mapRingHom,RingHom.comp_apply,Polynomial.map_C]

theorem clear_two {R:Type*} [CommRing R] [IsDomain R] (P:(FractionRing R)[X][X]) :
    ∃ (D:R[X][X]) (d:R),d≠0 ∧ doubleMap (algebraMap R (FractionRing R)) D =
      jetConstant (algebraMap R (FractionRing R) d)*P := by
  classical
  let f:=algebraMap R (FractionRing R)
  induction P using Polynomial.induction_on' with
  | add P Q hp hq =>
    obtain ⟨A,a,anz,first⟩:=hp
    obtain ⟨B,b,bnz,second⟩:=hq
    exact ⟨jetConstant b*A+jetConstant a*B,a*b,mul_ne_zero anz bnz,by
      rw [map_add,map_mul,map_mul,double_jet,double_jet,first,second,map_mul,map_mul]
      ring⟩
  | monomial n q =>
    let N:=IsLocalization.integerNormalization (nonZeroDivisors R) q
    obtain ⟨d,hd,eq⟩:=IsLocalization.integerNormalization_spec (nonZeroDivisors R) q
    have cq:N.map f=C (f d)*q := by simpa only [Algebra.smul_def,Polynomial.algebraMap_apply] using eq
    refine ⟨monomial n N,d,nonZeroDivisors.ne_zero hd,?_⟩
    change (monomial n N).map (mapRingHom f)=C (C (f d))*monomial n q
    rw [map_monomial,coe_mapRingHom,cq,C_mul_monomial]

private theorem primitive_part {R F:Type*} [CommRing R] [IsDomain R] [Field F]
    [UniqueFactorizationMonoid R[X]] (f:R→+*F) (inj:Function.Injective f)
    (P:F[X][X]) (prim:P.IsPrimitive) (D:R[X][X]) (d:R) (nd:d≠0)
    (mapped:doubleMap f D=jetConstant (f d)*P) :
    ∃ (G:R[X][X]) (c:F),G.IsPrimitive ∧ c≠0 ∧ doubleMap f G=jetConstant c*P := by
  classical
  have dn:f d≠0 := (map_ne_zero_iff _ inj).mpr nd
  let := UniqueFactorizationMonoid.strongNormalizationMonoid (α:=R[X])
  let := UniqueFactorizationMonoid.toNormalizedGCDMonoid R[X]
  have content : C (D.content.map f)*doubleMap f D.primPart=jetConstant (f d)*P := by
    calc
      _ = doubleMap f (C D.content*D.primPart) := by
        simp only [map_mul,doubleMap,coe_mapRingHom,Polynomial.map_C]
      _ = _ := D.eq_C_content_mul_primPart ▸ mapped
  have unitScalar:IsUnit (jetConstant (f d):F[X][X]) :=
    isUnit_C.mpr (isUnit_C.mpr dn.isUnit)
  have cd:C (D.content.map f)∣P :=
    (associated_unit_mul_left _ _ unitScalar).dvd_iff_dvd_right.mp ⟨_,content.symm⟩
  obtain ⟨a,ua,coeff⟩:=Polynomial.isUnit_iff.mp (prim _ cd)
  rw [←coeff] at content
  refine ⟨D.primPart,f d/a,D.isPrimitive_primPart,div_ne_zero dn ua.ne_zero,?_⟩
  apply mul_left_cancel₀ (C_ne_zero.mpr (C_ne_zero.mpr ua.ne_zero) : (jetConstant a:F[X][X])≠0)
  change C (C a)*doubleMap f D.primPart = jetConstant a*(jetConstant (f d/a)*P)
  rw [content,←mul_assoc,←map_mul]
  congr 2
  field_simp [ua.ne_zero]

/-- Clear every coefficient into the raw polynomial ring with one scalar
and then divide out all common content in the ordinate and physical variables. -/
theorem raw_model (P:B[X][X]) (prim:P.IsPrimitive) :
    ∃ (G:K1_14_1.RawSource) (c:B),G.IsPrimitive ∧ c≠0 ∧ doubleMap evalRaw G=jetConstant c*P := by
  classical
  let H:=doubleMap jointEquiv.symm.toRingHom P
  obtain ⟨D,d,nd,eq⟩:=clear_two (R:=k[X]) H
  have back:doubleMap joint H=P := by
    ext j i
    simp only [H,doubleMap,coe_mapRingHom,coeff_map]
    exact jointEquiv.apply_symm_apply _
  have mapped:doubleMap evalRaw D=jetConstant (evalRaw d)*P := by
    have test:=congrArg (doubleMap joint) eq
    rw [double_comp,map_mul,double_jet,back] at test
    rwa [restrict_joint,joint_raw] at test
  exact primitive_part evalRaw PadeRawField.eval_injective P prim D d nd mapped

/-- A primitive representative with polynomial seed coefficients in the
native bank. Its two seed degrees are shared by all rows and cutoffs. -/
theorem native_model (P:B[X][X]) (prim:P.IsPrimitive) :
    ∃ (G:K1_14.Jet) (c:B),G.IsPrimitive ∧ c≠0 ∧
      doubleMap (algebraMap Seeds B) G=jetConstant c*P := by
  obtain ⟨D,d,nd,eq⟩:=clear_two (R:=Seeds) P
  exact primitive_part (algebraMap Seeds B) (IsFractionRing.injective Seeds B) P prim D d nd eq

#print axioms native_model

#print axioms joint_surjective
#print axioms raw_model
end
end Research6966.PadeIntegralGraph

end Merged6967_R6966ProofPadeIntegralGraph

section Merged6967_R6966ProofSpreadBucket
set_option Elab.async false


set_option Elab.async false

namespace Research6966.SpreadBucket
open Finset
open K1_14 (Shape shapeSum)
open KoalaRect (rectDebit rectPower area)
open PadeCutoff (capacity excluded)

private theorem order_iff {A h W k:ℕ} {s:Shape} (hp:0<h) (hw:W<s.m*A) :
    rectPower A h s W=k+1 ↔
      s.m*A-2*h*(k+1)≤W ∧ W<s.m*A-2*h*k := by
  have a:=K1_14_4.power_threshold (s.m*A) (2*h) W 0 k hw (by omega)
  have b:=K1_14_4.power_threshold (s.m*A) (2*h) W 0 (k+1) hw (by omega)
  simp only [Nat.zero_add,Nat.sub_zero] at a b
  unfold rectPower
  omega

/-- There are at most two height units of cutoff for each Hasse order.
The cost function is indexed by positive orders. -/
theorem sum_by_order {s:Shape} {A h K scale:ℕ} (hp:0<h) (F cost:ℕ→ℕ)
    (live:∀ W<s.m*A,rectPower A h s W≤K →
      F W≤scale*cost (rectPower A h s W))
    (tail:∀ W<s.m*A,K<rectPower A h s W → F W=0) :
    ∑ W∈range (s.m*A),F W ≤ scale*(2*h)*(∑ k∈range K,cost (k+1)) := by
  let N:=s.m*A
  let power:=rectPower A h s
  have atW (W:ℕ) (hw:W<N) : F W ≤
      ∑ k∈range K, if power W=k+1 then scale*cost (k+1) else 0 := by
    by_cases high:K<power W
    · rw [tail W hw high];exact Nat.zero_le _
    · have one:0<power W:=Nat.add_pos_left Nat.one_pos _
      rw [sum_eq_single (power W-1)]
      · rw [Nat.sub_add_cancel one,if_pos rfl]
        exact live W hw (Nat.le_of_not_gt high)
      · intro j _ ne
        rw [if_neg (by omega)]
      · intro absent
        exact False.elim (absent (mem_range.mpr (by omega)))
  have count (k:ℕ) :
      (∑ W∈range N, if power W=k+1 then scale*cost (k+1) else 0) ≤
        (2*h)*(scale*cost (k+1)) := by
    rw [←sum_filter]
    have same : (range N).filter (fun W=>power W=k+1)=Ico (N-2*h*(k+1)) (N-2*h*k) := by
      ext W
      simp only [mem_filter,mem_range,mem_Ico]
      constructor
      · rintro ⟨hw,eq⟩
        exact (order_iff hp hw).mp eq
      · intro bounds
        have hw:W<N:=bounds.2.trans_le (Nat.sub_le ..)
        exact ⟨hw,(order_iff hp hw).mpr bounds⟩
    rw [same,sum_const,Nat.card_Ico,nsmul_eq_mul]
    apply Nat.mul_le_mul_right
    change N-2*h*k-(N-2*h*(k+1))≤2*h
    rw [Nat.mul_succ]
    omega
  calc
    _ ≤ ∑ W∈range N, ∑ k∈range K, if power W=k+1 then scale*cost (k+1) else 0 :=
      sum_le_sum fun W hw=>atW W (mem_range.mp hw)
    _ = _ := sum_comm
    _ ≤ ∑ k∈range K,(2*h)*(scale*cost (k+1)) := sum_le_sum fun k _=>count k
    _ = _ := by simp only [←mul_sum];ring

theorem sum_capacity {s:Shape} {A h e a n K:ℕ} {U:Fin 2→ℕ}
    (hp:0<h) (cost:ℕ→ℕ)
    (live:∀ W<s.m*A,rectPower A h s W≤K →
      capacity A h e a n s U W≤area U*cost (rectPower A h s W))
    (tail:∀ W<s.m*A,K<rectPower A h s W → capacity A h e a n s U W=0) :
    ∑ W∈range (s.m*A),capacity A h e a n s U W ≤
      area U*(2*h)*(∑ k∈range K,cost (k+1)) := sum_by_order hp _ cost live tail

def raw (s:Shape) (A h:ℕ) := shapeSum s (fun q j=>s.m*A+j-q*(131071-h))
def slope (s:Shape) := shapeSum s (fun q _=>q)

theorem raw_affine {s:Shape} {A lo h:ℕ} (left:lo≤h) (endH:h≤131071)
    (full:s.B*(131071-lo)≤s.m*A) : raw s A h=raw s A lo+(h-lo)*slope s := by
  unfold raw slope shapeSum
  simp only [mul_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro q hq
  apply sum_congr rfl
  intro j _
  have bound: q*(131071-lo)≤s.m*A:=(Nat.mul_le_mul_right _ (by have:=mem_range.mp hq;omega)).trans full
  have steps : (131071-h)+(h-lo)=131071-lo := by omega
  have e : q*(131071-h)+(h-lo)*q=q*(131071-lo) := by
    rw [Nat.mul_comm (h-lo) q,←Nat.mul_add,steps]
  omega

theorem affine_pos {C V B P lo hi h:ℕ} (left:lo≤h) (right:h≤hi)
    (first:P+lo*B<C) (last:P+hi*B<C+(hi-lo)*V) : P+h*B<C+(h-lo)*V := by
  have split1 : h*B=lo*B+(h-lo)*B := by rw [←Nat.add_mul,show lo+(h-lo)=h by omega]
  have split2 : hi*B=h*B+(hi-h)*B := by rw [←Nat.add_mul,show h+(hi-h)=hi by omega]
  have split3 : (hi-lo)*V=(h-lo)*V+(hi-h)*V := by rw [←Nat.add_mul,show (h-lo)+(hi-h)=hi-lo by omega]
  rcases le_total B V with b|v
  · have := Nat.mul_le_mul_left (h-lo) b
    omega
  · have := Nat.mul_le_mul_left (hi-h) v
    omega

/-- A capacity bound shared by a whole height interval needs two scalar
rank comparisons, since the full physical bank is affine throughout it. -/
theorem excluded_of_endpoints {s:Shape} {A e a n nodes moment lo hi h sum:ℕ} {U:Fin 2→ℕ}
    (left:lo≤h) (right:h≤hi) (lastHeight:hi≤131071) (full:s.B*(131071-lo)≤s.m*A)
    (cap:∑ W∈range (s.m*A),capacity A h e a n s U W≤area U*(2*h)*sum)
    (first:rectDebit lo nodes moment U+area U*(2*lo)*sum<area U*raw s A lo)
    (last:rectDebit hi nodes moment U+area U*(2*hi)*sum<area U*raw s A hi) :
    excluded A h e a n s U nodes moment := by
  let B:=(U 0+U 1+2)*moment+2*area U*sum
  have charge (t:ℕ) : rectDebit t nodes moment U+area U*(2*t)*sum=area U*nodes+t*B := by
    unfold rectDebit B;ring
  have supply (t:ℕ) (l:lo≤t) (r:t≤hi) : area U*raw s A t =
      area U*raw s A lo+(t-lo)*(area U*slope s) := by
    rw [raw_affine l (r.trans lastHeight) full];ring
  rw [charge] at first
  rw [charge,supply hi (left.trans right) le_rfl] at last
  have core:=affine_pos left right first last
  unfold excluded
  apply (Nat.add_le_add_left cap _).trans_lt
  change rectDebit h nodes moment U+area U*(2*h)*sum<area U*raw s A h
  rwa [charge,supply h left right]

#print axioms sum_capacity
#print axioms excluded_of_endpoints
end Research6966.SpreadBucket

end Merged6967_R6966ProofSpreadBucket

section Merged6967_R6966ProofSpreadGain
set_option Elab.async false


set_option Elab.async false

-- merged module R6966ProofSpreadStrip
section Merged_R6966ProofSpreadStrip

namespace Research6966.SpreadStrip
open Finset PadeRank

private theorem widths (b j : ℕ) :
    (positions b j).card = ∑ i ∈ range j, (b-i) := by
  classical
  unfold positions
  rw [card_filter,sum_product]
  apply sum_congr rfl
  intro i _
  change (∑ x ∈ range b, if i+x<b then 1 else 0)=b-i
  rw [← card_filter]
  have eq : (range b).filter (fun x => i+x<b)=range (b-i) := by
    ext x
    simp only [mem_filter,mem_range]
    omega
  rw [eq,card_range]

/-- Exact new symbols on restriction to a primitive slope graph. Both
shape bounds are exclusive; the last slope grades can have fewer columns. -/
theorem slice (b j a : ℕ) :
    (positions (b+1) (j+1)).card - (positions ((b+1)-(a+1)) j).card =
      (b+1) + ∑ i ∈ range (min b j), min a (b-i) := by
  rw [widths,widths,sum_range_succ']
  simp only [Nat.sub_zero,Nat.succ_sub_succ_eq_sub]
  have e : (∑ i ∈ range j, (b-i)) =
      (∑ i ∈ range j, (b-a-i)) + ∑ i ∈ range j, min a (b-i) := by
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro i _
    omega
  have f : (∑ i ∈ range j, min a (b-i))=∑ i ∈ range (min b j), min a (b-i) := by
    symm; apply sum_subset (range_mono (Nat.min_le_right ..))
    intro i hi cut
    simp only [mem_range,lt_min_iff] at *
    omega
  omega

private theorem deficits (b j a : ℕ) :
    (∑ i ∈ range (min b j), (a-(b-i))) ≤ ∑ i ∈ range a, i := by
  classical
  let s := (range (min b j)).filter (fun i => 0<a-(b-i))
  let f := fun i : ℕ => a-(b-i)
  have eq : (∑ i ∈ s, f i)=∑ i ∈ range (min b j), f i := by
    apply sum_subset (filter_subset ..)
    intro i hi outside
    simp only [mem_filter,hi,true_and,not_lt] at outside
    change a-(b-i)=0
    omega
  rw [←eq]
  have inj : Set.InjOn f ↑s := by
    intro i hi k hk same
    simp only [s,Finset.mem_coe,mem_filter,mem_range,lt_min_iff] at hi hk
    dsimp [f] at same
    omega
  have sub : s.image f⊆range a := by
    intro i hi
    obtain ⟨k,hk,rfl⟩:=mem_image.mp hi
    simp only [s,mem_filter,mem_range,lt_min_iff] at hk
    simp only [mem_range,f]
    omega
  have im : (∑ i ∈ s.image f, i)=∑ i ∈ s, f i := sum_image (f:=id) inj
  rw [← im]
  exact sum_le_sum_of_subset_of_nonneg sub (by intros; omega)

theorem slice_with_tail (b j a : ℕ) :
    b+1 + a*min b j ≤ (positions (b+1) (j+1)).card -
      (positions ((b+1)-(a+1)) j).card + ∑ i ∈ range a, i := by
  rw [slice]
  have e : (∑ i ∈ range (min b j), min a (b-i)) +
      (∑ i ∈ range (min b j), (a-(b-i)))=a*min b j := by
    rw [←sum_add_distrib]
    calc
      _ = ∑ _ ∈ range (min b j), a := sum_congr rfl fun i _ => by omega
      _ = _ := by simp [Nat.mul_comm]
  have d:=deficits b j a
  omega

theorem slice_full {b j a:ℕ} (room:j+a≤b+1) :
    (positions (b+1) (j+1)).card - (positions ((b+1)-(a+1)) j).card =
      b+1+a*min b j := by
  rw [slice]
  congr 1
  calc
    _=∑ _ ∈ range (min b j), a := by
      apply sum_congr rfl
      intro i hi
      simp only [mem_range,lt_min_iff] at hi
      omega
    _=_ := by simp [Nat.mul_comm]

#print axioms slice_with_tail
#print axioms slice_full
end Research6966.SpreadStrip

end Merged_R6966ProofSpreadStrip

-- merged module R6966ProofSpreadLines
section Merged_R6966ProofSpreadLines

namespace Research6966.SpreadLines
open Finset

def affine (b s n : ℕ) := n*b-s*(n*(n-1)/2)

private theorem affine_sum (b s n:ℕ) (last:s*(n-1)≤b) :
    (∑ i∈range n,(b-s*i))=affine b s n := by
  have e : (∑ i∈range n,(b-s*i)) + ∑ i∈range n,s*i = n*b := by
    rw [←sum_add_distrib]
    calc
      _ = ∑ _∈range n,b := by
        apply sum_congr rfl
        intro i hi
        exact Nat.sub_add_cancel ((Nat.mul_le_mul_left s (by have := mem_range.mp hi; omega)).trans last)
      _ = _ := by simp
  rw [←mul_sum,Finset.sum_range_id] at e
  unfold affine
  omega

private theorem between {b s c t i last:ℕ} (first:b≤c)
    (endPt:b+t*last≤c+s*last) (hi:i≤last) : b+t*i≤c+s*i := by
  by_cases h:t≤s
  · exact Nat.add_le_add first (Nat.mul_le_mul_right i h)
  · have eq : t=s+(t-s) := by omega
    have e (k:ℕ) : t*k=s*k+(t-s)*k := calc
      t*k = (s+(t-s))*k := congrArg (·*k) eq
      _=_ := Nat.add_mul ..
    rw [e last] at endPt
    rw [e i]
    have := Nat.mul_le_mul_left (t-s) hi
    omega

def segment (b s c t n : ℕ) : ℕ :=
  if s*(n-1)≤b ∧ t*(n-1)≤c ∧ b≤c ∧ b+t*(n-1)≤c+s*(n-1)
  then affine b s n else 0

private theorem segment_le (b s c t n:ℕ) :
    segment b s c t n≤∑ i∈range n,min (b-s*i) (c-t*i) := by
  unfold segment
  split
  · rename_i ok
    rw [←affine_sum b s n ok.1]
    apply sum_le_sum
    intro i hi
    have hh:i≤n-1:=by have := mem_range.mp hi;omega
    have ordered:=between ok.2.2.1 ok.2.2.2 hh
    have low: s*i≤b:=(Nat.mul_le_mul_left _ hh).trans ok.1
    have high:t*i≤c:=(Nat.mul_le_mul_left _ hh).trans ok.2.1
    omega
  · exact Nat.zero_le _

/-- An unchecked proposed crossing is safe because both selected lines
are tested at both ends of their own segment. -/
def splitLower (b s c t n pivot:ℕ) : ℕ :=
  let k:=min n pivot
  segment c t b s k + segment (b-s*k) s (c-t*k) t (n-k)

theorem split_le (b s c t n pivot:ℕ) :
    splitLower b s c t n pivot ≤ ∑ i∈range n,min (b-s*i) (c-t*i) := by
  let k:=min n pivot
  have add : k+(n-k)=n := by dsimp [k];omega
  calc
    _ ≤ (∑ i∈range k,min (c-t*i) (b-s*i)) +
          ∑ i∈range (n-k),min ((b-s*k)-s*i) ((c-t*k)-t*i) :=
      Nat.add_le_add (segment_le ..) (segment_le ..)
    _ = ∑ i∈range (k+(n-k)),min (b-s*i) (c-t*i) := by
      rw [sum_range_add]
      congr 1
      · exact sum_congr rfl fun _ _ => min_comm ..
      · exact sum_congr rfl fun _ _ => by simp only [Nat.mul_add,Nat.sub_sub]
    _ = _ := by rw [add]

def minSum (b s c t n:ℕ) : ℕ :=
  if s=t then segment (min b c) s (max b c) t n
  else if t<s then splitLower b s c t n ((b-c+(s-t)-1)/(s-t))
  else splitLower c t b s n ((c-b+(t-s)-1)/(t-s))

theorem minSum_le (b s c t n:ℕ) :
    minSum b s c t n ≤ ∑ i∈range n,min (b-s*i) (c-t*i) := by
  unfold minSum
  split
  · rename_i eq
    subst t
    rcases le_total b c with h|h
    · simpa [min_eq_left h,max_eq_right h] using segment_le b s c s n
    · simp only [min_eq_right h,max_eq_left h]
      simpa only [min_comm] using segment_le c s b s n
  · split
    · exact split_le ..
    · simpa only [min_comm] using split_le c t b s n ((c-b+(t-s)-1)/(t-s))

#print axioms minSum_le
end Research6966.SpreadLines

end Merged_R6966ProofSpreadLines

-- merged module R6966ProofSpreadGain
section Merged_R6966ProofSpreadGain

namespace Research6966.SpreadGain
open Finset PadeRank
set_option maxHeartbeats 1100000

def count (a B J k : ℕ) : ℕ := min k (min (J+1) (B/a+1))

def full (a B J m : ℕ) : ℕ := min m ((B-J)/(a-1))

def pivot (a B J m : ℕ) : ℕ := if J ≤ B then min m ((B-J)/(a-1)+1) else 0

def loss (a : ℕ) : ℕ := (a-1)*(a-2)/2

def lower (B J a n k : ℕ) : ℕ :=
  let m := count a B J k
  if a = 1 then SpreadLines.minSum (B+1) 1 (n*k) n m else
    let f := full a B J m
    let p := pivot a B J m
    let first := SpreadLines.minSum (B+(a-1)*J+1) (2*a-1) (n*k) n p
    let tail := SpreadLines.minSum (a*(B-a*p)+1) (a*a) (n*(k-p)) n (m-p)
    first+(tail-(m-p)*loss a)-(p-f)*loss a

private def slot (a n k b j i : ℕ) : ℕ :=
  let B := b-a*i
  let J := j-i
  if B = 0 ∨ J = 0 then 0 else
    (positions B J).card-(positions (B-a) (J-1)).card-imageAllowance B J a n (k-i)

private theorem gain_sum (a n k b j : ℕ) :
    gain a n k b j = ∑ i ∈ range k, slot a n k b j i := by
  induction k generalizing b j with
  | zero => simp [gain]
  | succ k ih =>
    rw [gain]
    by_cases zero : b=0 ∨ j=0
    · rw [ite_eq_left zero]
      symm
      apply sum_eq_zero
      intro i _
      rcases zero with zb | zj
      · simp [slot,zb]
      · simp [slot,zj]
    · rw [ite_eq_right zero, ih, sum_range_succ']
      have next (i : ℕ) : slot a n (k+1) b j (i+1) = slot a n k (b-a) (j-1) i := by
        have hb : b-a*(i+1)=(b-a)-a*i := by rw [Nat.mul_add,Nat.mul_one,Nat.sub_sub,Nat.add_comm (a*i)]
        have hj : j-(i+1)=(j-1)-i := by omega
        have hk : k+1-(i+1)=k-i := by omega
        simp only [slot,hb,hj,hk]
      rw [show (∑ i ∈ range k, slot a n (k+1) b j (i+1)) = ∑ i ∈ range k, slot a n k (b-a) (j-1) i from
        sum_congr rfl (fun i _ => next i)]
      simp only [slot,Nat.mul_zero,Nat.sub_zero,ite_eq_right zero]
      exact Nat.add_comm _ _

private def width (a b j : ℕ) : ℕ := b+1+(a-1)*min b j

private def strip (a b j : ℕ) : ℕ :=
  (positions (b+1) (j+1)).card - (positions (b+1-a) j).card

private theorem full_strip (a b j : ℕ) (ap : 0 < a)
    (room : a=1 ∨ j+(a-1)≤b+1) : strip a b j = width a b j := by
  have aa : a-1+1=a := Nat.sub_add_cancel ap
  rcases room with one | fits
  · subst a
    simpa [strip,width] using SpreadStrip.slice b j 0
  · simpa only [strip,width,aa] using (SpreadStrip.slice_full (b:=b) (j:=j) (a:=a-1) fits)

private theorem all_strips (a b j : ℕ) (ap : 0 < a) : width a b j ≤ strip a b j+loss a := by
  have aa : a-1+1=a := Nat.sub_add_cancel ap
  have estimate := SpreadStrip.slice_with_tail b j (a-1)
  rw [sum_range_id, Nat.sub_sub, show 1+1=2 by decide, aa] at estimate
  exact estimate

private theorem width_mono (a j : ℕ) {lo hi : ℕ} (le : lo ≤ hi) :
    width a lo j ≤ width a hi j :=
  Nat.add_le_add (Nat.succ_le_succ le) (Nat.mul_le_mul_left _ (min_le_min le le_rfl))

private theorem slot_at (a n k B J i : ℕ) (ib : a*i ≤ B) (ij : i ≤ J) :
    slot a n k (B+1) (J+1) i =
      strip a (B-a*i) (J-i) - (width a (B-a*i) (J-i)-n*(k-i)) := by
  have b : B+1-a*i=(B-a*i)+1 := by omega
  have j : J+1-i=(J-i)+1 := by omega
  unfold slot
  dsimp only
  rw [b,j]
  simp only [Nat.add_one_ne_zero,false_or,ite_false,imageAllowance,strip,width,Nat.add_sub_cancel]

private theorem slot_lower (a n k BL B J i L c : ℕ) (le : BL ≤ B) (valid : a*i ≤ BL) (ij : i ≤ J)
    (cap : c ≤ width a (BL-a*i) (J-i))
    (budget : width a (B-a*i) (J-i) ≤ strip a (B-a*i) (J-i)+L) :
    min c (n*(k-i)) ≤ slot a n k (B+1) (J+1) i+L := by
  have actual := cap.trans (width_mono a (J-i) (Nat.sub_le_sub_right le _))
  rw [slot_at a n k B J i (valid.trans le) ij]
  omega

private theorem counting {a B J k i : ℕ} (ap : 0 < a) (inRange : i < count a B J k) :
    i ≤ J ∧ i < k ∧ a*i ≤ B := by
  unfold count at inRange
  rw [lt_min_iff,lt_min_iff] at inRange
  obtain ⟨ik,ij,ib⟩ := inRange
  have b := (Nat.le_div_iff_mul_le ap).mp (Nat.lt_succ_iff.mp ib)
  exact ⟨Nat.lt_succ_iff.mp ij,ik,by simpa only [Nat.mul_comm i a] using b⟩

private theorem first_width {a B J m i : ℕ} (ap : 1 < a) (im : i < pivot a B J m)
    (ib : a*i≤B) (ij : i≤J) :
    width a (B-a*i) (J-i) = B+(a-1)*J+1-(2*a-1)*i := by
  have a₁ : 0<a-1 := by omega
  have ok : J≤B := by by_contra no; simp only [pivot,ite_eq_right no,Nat.not_lt_zero] at im
  have t : i≤(B-J)/(a-1) := by
    rw [pivot,ite_eq_left ok,lt_min_iff] at im
    omega
  have jfits := (Nat.le_div_iff_mul_le a₁).mp t
  have split : (a-1)*i+i=a*i := by rw [← Nat.succ_mul]; congr 1; omega
  rw [Nat.mul_comm i (a-1)] at jfits
  have jle : J-i≤B-a*i := by omega
  unfold width
  rw [min_eq_right jle]
  have cap : (a-1)*(J-i)+(a-1)*i=(a-1)*J := by rw [← Nat.mul_add,Nat.sub_add_cancel ij]
  have line : a*i+(a-1)*i=(2*a-1)*i := by rw [← Nat.add_mul]; congr 1; omega
  omega

private theorem first_room {a B J m i : ℕ} (ap : 1 < a) (im : i < full a B J m)
    (ib : a*i≤B) (ij : i≤J) : J-i+(a-1)≤B-a*i+1 := by
  have a₁ : 0<a-1 := by omega
  have ok : J≤B := by
    by_contra no
    simp only [full,Nat.sub_eq_zero_of_le (show B≤J by omega),Nat.zero_div,_root_.min_zero,Nat.not_lt_zero] at im
  have t : i+1≤(B-J)/(a-1) := by
    rw [full,lt_min_iff] at im
    omega
  have jfits := (Nat.le_div_iff_mul_le a₁).mp t
  rw [Nat.mul_comm (i+1),Nat.mul_add,Nat.mul_one] at jfits
  have split : (a-1)*i+i=a*i := by rw [← Nat.succ_mul]; congr 1; omega
  omega

private theorem tail_width {a B J m i : ℕ} (ap : 1 < a) (im : i < m)
    (ip : pivot a B J m ≤ i) :
    width a (B-a*i) (J-i) = a*(B-a*i)+1 := by
  have a₁ : 0<a-1 := by omega
  have split : (a-1)*i+i=a*i := by rw [← Nat.succ_mul]; congr 1; omega
  have ble : B-a*i ≤ J-i := by
    by_cases room : J≤B
    · rw [pivot,ite_eq_left room] at ip
      have below : (B-J)/(a-1) < i := by omega
      have cap := (Nat.div_lt_iff_lt_mul a₁).mp below
      rw [Nat.mul_comm i (a-1)] at cap
      omega
    · omega
  unfold width
  rw [min_eq_left ble]
  have eq := congrArg (fun x => x*(B-a*i)) (Nat.sub_add_cancel (show 1≤a by omega) : a-1+1=a)
  rw [Nat.add_mul,Nat.one_mul] at eq
  omega

/-- The cost of suppressing the graph in its retained descendants. The
estimate may use a smaller degree box than the one in the actual bank. -/
theorem lower_le (BL B J a n k : ℕ) (ap : 0 < a) (boxLe : BL ≤ B) :
    lower BL J a n k ≤ gain a n k (B+1) (J+1) := by
  classical
  let m := count a BL J k
  have mk : m≤k := min_le_left _ _
  let g (i : ℕ) := slot a n k (B+1) (J+1) i
  have take : (∑ i ∈ range m, g i) ≤ gain a n k (B+1) (J+1) := by
    rw [gain_sum]
    exact sum_le_sum_of_subset_of_nonneg (range_mono mk) (by intros; exact Nat.zero_le _)
  unfold lower
  dsimp only
  have boxAt (i : ℕ) (mem : i < m) := counting ap mem
  by_cases one : a=1
  · rw [ite_eq_left one]
    refine (SpreadLines.minSum_le ..).trans ((sum_le_sum (fun i mem => ?_)).trans take)
    obtain ⟨jle,ik,bfit⟩ := boxAt i (mem_range.mp mem)
    have cap : BL+1-1*i ≤ width a (BL-a*i) (J-i) := by
      rw [one]
      simp only [width,Nat.sub_self,Nat.zero_mul,Nat.add_zero,Nat.one_mul]
      omega
    have full := full_strip a (B-a*i) (J-i) ap (Or.inl one)
    have rel := slot_lower a n k BL B J i 0 _ boxLe bfit jle cap (by rw [full,Nat.add_zero])
    rwa [Nat.mul_sub_left_distrib,Nat.add_zero] at rel
  · rw [ite_eq_right one]
    have ag : 1<a := by omega
    let f := full a BL J m
    let p := pivot a BL J m
    let δ := loss a
    have pm : p≤m := by unfold p pivot; split <;> omega
    have fp : f≤p := by
      by_cases room : J≤BL
      · simpa only [p,pivot,ite_eq_left room,f,full] using
          (min_le_min (le_rfl : m≤m) (Nat.le_succ ((BL-J)/(a-1))))
      · have no : BL-J=0 := by omega
        simp only [p,pivot,ite_eq_right room,f,full,no,Nat.zero_div,_root_.min_zero]
        exact le_rfl
    have first :
        SpreadLines.minSum (BL+(a-1)*J+1) (2*a-1) (n*k) n p ≤ (∑ i ∈ range p,g i)+(p-f)*δ := by
      have penalty : (∑ i ∈ range p, if i<f then 0 else δ)=(p-f)*δ := by
        rw [← sum_range_add_sum_Ico (fun i => if i<f then 0 else δ) fp]
        rw [sum_eq_zero (fun i hi => ite_eq_left (mem_range.mp hi)),Nat.zero_add]
        calc
          _ = ∑ _i ∈ Ico f p,δ := sum_congr rfl (fun i hi => ite_eq_right (Nat.not_lt.mpr (mem_Ico.mp hi).1))
          _ = _ := by simp [Nat.card_Ico]
      refine (SpreadLines.minSum_le ..).trans ?_
      rw [← penalty,← sum_add_distrib]
      apply sum_le_sum
      intro i hi
      obtain ⟨jle,ik,bfit⟩ := boxAt i ((mem_range.mp hi).trans_le pm)
      have cap := (first_width ag (mem_range.mp hi) bfit jle).ge
      rw [← Nat.mul_sub_left_distrib]
      by_cases inside : i<f
      · rw [ite_eq_left inside]
        have room := first_room ag inside bfit jle
        have widened : J-i+(a-1)≤B-a*i+1 := room.trans (Nat.succ_le_succ (Nat.sub_le_sub_right boxLe _))
        exact slot_lower a n k BL B J i _ _ boxLe bfit jle cap (by rw [full_strip a _ _ ap (Or.inr widened),Nat.add_zero])
      · rw [ite_eq_right inside]
        exact slot_lower a n k BL B J i _ _ boxLe bfit jle cap (all_strips a _ _ ap)
    have tail :
        SpreadLines.minSum (a*(BL-a*p)+1) (a*a) (n*(k-p)) n (m-p) ≤
          (∑ i ∈ range (m-p),g (p+i))+(m-p)*δ := by
      refine (SpreadLines.minSum_le ..).trans ?_
      rw [← show (∑ _ ∈ range (m-p),δ)=(m-p)*δ by simp,← sum_add_distrib]
      apply sum_le_sum
      intro i hi
      have ind : p+i < m := by have := mem_range.mp hi; omega
      obtain ⟨jle,ik,bfit⟩ := boxAt (p+i) ind
      have cap : a*(BL-a*p)+1-a*a*i ≤ width a (BL-a*(p+i)) (J-(p+i)) := by
        rw [tail_width ag ind (Nat.le_add_right p i)]
        have eq : a*(BL-a*(p+i))=a*(BL-a*p)-a*a*i := by
          rw [Nat.mul_add,← Nat.sub_sub,Nat.mul_sub_left_distrib,Nat.mul_assoc]
        have bounded : a*a*i≤a*(BL-a*p) := by
          rw [Nat.mul_assoc]
          apply Nat.mul_le_mul_left
          rw [Nat.mul_add] at bfit
          omega
        omega
      rw [← Nat.mul_sub_left_distrib,Nat.sub_sub]
      exact slot_lower a n k BL B J (p+i) _ _ boxLe bfit jle cap (all_strips a _ _ ap)
    have combine := sum_range_add g p (m-p)
    rw [Nat.add_sub_of_le pm] at combine
    have bank := take
    change SpreadLines.minSum (BL+(a-1)*J+1) (2*a-1) (n*k) n p+
      (SpreadLines.minSum (a*(BL-a*p)+1) (a*a) (n*(k-p)) n (m-p)-(m-p)*δ)-(p-f)*δ ≤ _
    omega

#print axioms lower_le
end Research6966.SpreadGain

end Merged_R6966ProofSpreadGain

end Merged6967_R6966ProofSpreadGain
