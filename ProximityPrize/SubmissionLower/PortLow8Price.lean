import ProximityPrize.SubmissionLower.PortLow8Base
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 2400000
section PackSource_P0_9_8_3Tariff
set_option autoImplicit true
namespace P0_9_8_3

open K1_13
open K1_13_8_2 (Chamber mixed_mono)

private theorem box_refl (x : Shape) : InBox x x := ⟨le_rfl, le_rfl, le_rfl⟩

private theorem normalize_mono {x y : Shape} (h : InBox x y) :
    InBox x.chamber y.chamber := ⟨max_le_max h.1 h.2.1, h.2.1, h.2.2⟩

private theorem normalize_chamber (x : Shape) (h : 3 * x.t ≤ x.j) :
    Chamber x.chamber := ⟨le_max_right _ _, h⟩

private theorem plus_mono {x y u v : Shape} (h : InBox x y) (h' : InBox u v) :
    InBox (x.plus u) (y.plus v) :=
  ⟨Nat.add_le_add h.1 h'.1, Nat.add_le_add h.2.1 h'.2.1, Nat.add_le_add h.2.2 h'.2.2⟩

private theorem plus_chamber {x y : Shape} (hx : Chamber x) (hy : Chamber y) :
    Chamber (x.plus y) := by
  exact ⟨Nat.add_le_add hx.1 hy.1, by simp only [Shape.plus, Nat.mul_add]; exact Nat.add_le_add hx.2 hy.2⟩

private theorem scale_mono {x y : Shape} (h : InBox x y) (k : ℕ) :
    InBox (x.scale k) (y.scale k) :=
  ⟨Nat.mul_le_mul_left k h.1, Nat.mul_le_mul_left k h.2.1, Nat.mul_le_mul_left k h.2.2⟩

private theorem scale_chamber {x : Shape} (hx : Chamber x) (k : ℕ) :
    Chamber (x.scale k) :=
  ⟨Nat.mul_le_mul_left k hx.1, by simpa [Shape.scale, Nat.mul_left_comm 3 k] using Nat.mul_le_mul_left k hx.2⟩

private theorem min_fits_index (a i : ℕ) : 3 * min a (i / 3) ≤ i := by
  have h := min_le_right a (i / 3)
  omega

private theorem chart_chamber (L : ℕ) (x : Shape) : Chamber (chart L x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩

private theorem lifted_chamber (L : ℕ) (x : Shape) : Chamber (liftedChart L x) :=
  ⟨le_max_right _ _, min_fits_index _ _⟩

private theorem chart_mono (L : ℕ) {x y : Shape} (h : InBox x y) :
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
    P0_9.surfaceNumerator32 p q ≤ P0_9.surfaceNumerator32 p' q := by
  let L := P0_9.taylorLength
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

private theorem ceil_mono {a b : ℕ} (h : a ≤ b) (l : ℕ) : ceilDiv a l ≤ ceilDiv b l :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right h l) 1)

/-- Retuned shape monotonicity at a fixed order. -/
theorem physical_mono {x y : Shape} (h : InBox x y) (hx : 3 * x.t ≤ x.j)
    (hy : 3 * y.t ≤ y.j) (l : ℕ) : P0_9.physicalPrice x l ≤ P0_9.physicalPrice y l := by
  let p := x.chamber
  let p' := y.chamber
  let q : Shape := P0_9.primaryBox
  let L := P0_9.taylorLength
  let A := q.plus (p.scale 4)
  let A' := q.plus (p'.scale 4)
  have hp := normalize_mono h
  have hpc : Chamber p := normalize_chamber x hx
  have hp'c : Chamber p' := normalize_chamber y hy
  have hqc : Chamber q := ⟨by decide, by decide⟩
  have ha : InBox A A' := plus_mono (box_refl q) (scale_mono hp 4)
  have hac : Chamber A := plus_chamber hqc (scale_chamber hpc 4)
  have ha'c : Chamber A' := plus_chamber hqc (scale_chamber hp'c 4)
  have hs := surface_mono hp hp'c hqc
  have hb := (chart_mono (L+1) hp).1
  have hmain : (P0.t + 2*P0_9.incidenceGap) * x.b * q.b * (chart (L+1) p).b ≤
      (P0.t + 2*P0_9.incidenceGap) * y.b * q.b * (chart (L+1) p').b := by
    have := h.1
    gcongr
  have hcurve := mixed_mono hp (box_refl q) ha (chart_mono L hp) hp'c hqc ha'c hqc hac (chart_chamber L p)
  have hpoint := mixed_mono hp (box_refl q) ha hp hp'c hqc ha'c hqc hac hpc
  have hcurve' := mixed_mono hp hp hp (chart_mono L hp) hp'c hp'c hp'c hpc hpc (chart_chamber L p)
  have hpoint' := mixed_mono hp hp hp hp hp'c hp'c hp'c hpc hpc hpc
  have htc := Nat.mul_le_mul_left 2 h.2.2
  have hc := Nat.add_le_add hcurve (Nat.mul_le_mul htc hcurve')
  have hn := Nat.add_le_add hpoint (Nat.mul_le_mul htc hpoint')
  have hgeom := Nat.add_le_add (Nat.mul_le_mul_left P0.t hc) (Nat.mul_le_mul_left (2*P0_9.incidenceGap) hn)
  have hraw := Nat.mul_le_mul_right q.b (Nat.mul_le_mul_left (2*P0_9.physicalDegree) h.1)
  exact Nat.add_le_add
    (Nat.add_le_add (ceil_mono (Nat.add_le_add (ceil_mono hs _) (ceil_mono hmain _)) l) hraw)
    (ceil_mono hgeom _)

end P0_9_8_3
end PackSource_P0_9_8_3Tariff


namespace P0_9_8_3
open K1_13 P0_9_8
open K1_13_8_2 (orderFor)
def peak (top b j : ℕ) : Shape := ⟨b,j,min top (j/3)⟩
private theorem peak_index (top b j : ℕ) : 3*(peak top b j).t ≤ j := by
  change 3*min top (j/3) ≤ j
  have := min_le_right top (j/3)
  omega
private def Paid (top rate b j : ℕ) :=
  P0_9.physicalPrice (peak top b j) (emptyOrder (peak top b j)) ≤ indexBudget K1_13_8.zeroShape rate j
private theorem price_anti (a : Shape) {l u : ℕ} (hl : 0 < l) (h : l ≤ u) :
    P0_9.physicalPrice a u ≤ P0_9.physicalPrice a l := by
  unfold P0_9.physicalPrice
  exact Nat.add_le_add_right (Nat.add_le_add_right (K1_13_8.ceilDiv_anti _ hl h) _) _
private theorem interval {top rate lo b hi j l : ℕ} (hb : lo ≤ b) (hu : b ≤ hi) (hl : 0 < l)
    (hm : l ≤ emptyOrder (peak top lo j))
    (cost : P0_9.physicalPrice (peak top hi j) l ≤ indexBudget K1_13_8.zeroShape rate j) : Paid top rate b j := by
  have horder : emptyOrder (peak top lo j) ≤ emptyOrder (peak top b j) :=
    orderFor_mono hb (le_refl j) emptyThresholds
  calc
    P0_9.physicalPrice (peak top b j) (emptyOrder (peak top b j)) ≤ P0_9.physicalPrice (peak top b j) l :=
      price_anti (peak top b j) hl (hm.trans horder)
    _ ≤ P0_9.physicalPrice (peak top hi j) l := physical_mono (x := peak top b j) (y := peak top hi j)
      ⟨hu,le_rfl,le_rfl⟩ (peak_index top b j) (peak_index top hi j) l
    _ ≤ _ := cost
private theorem row7_3 (b : ℕ) (hb : b ≤ 120) (hv : 3 ≤ 3*b) : Paid 7 222672674688503043 b 3 := by
  exact interval (lo := 1) (hi := 120) (l := 1) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_4 (b : ℕ) (hb : b ≤ 120) (hv : 4 ≤ 3*b) : Paid 7 222672674688503043 b 4 := by
  by_cases h0 : b ≤ 66
  · exact interval (lo := 2) (hi := 66) (l := 1) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 67) (hi := 120) (l := 8) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_5 (b : ℕ) (hb : b ≤ 120) (hv : 5 ≤ 3*b) : Paid 7 222672674688503043 b 5 := by
  by_cases h0 : b ≤ 38
  · exact interval (lo := 2) (hi := 38) (l := 1) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 39) (hi := 120) (l := 8) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_6 (b : ℕ) (hb : b ≤ 120) (hv : 6 ≤ 3*b) : Paid 7 222672674688503043 b 6 := by
  by_cases h0 : b ≤ 26
  · exact interval (lo := 2) (hi := 26) (l := 1) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 27) (hi := 120) (l := 8) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_7 (b : ℕ) (hb : b ≤ 120) (hv : 7 ≤ 3*b) : Paid 7 222672674688503043 b 7 := by
  by_cases h0 : b ≤ 78
  · exact interval (lo := 3) (hi := 78) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 79) (hi := 120) (l := 9) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_8 (b : ℕ) (hb : b ≤ 120) (hv : 8 ≤ 3*b) : Paid 7 222672674688503043 b 8 := by
  by_cases h0 : b ≤ 63
  · exact interval (lo := 3) (hi := 63) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 64) (hi := 120) (l := 9) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_9 (b : ℕ) (hb : b ≤ 120) (hv : 9 ≤ 3*b) : Paid 7 222672674688503043 b 9 := by
  by_cases h0 : b ≤ 53
  · exact interval (lo := 3) (hi := 53) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 54) (hi := 120) (l := 9) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_10 (b : ℕ) (hb : b ≤ 120) (hv : 10 ≤ 3*b) : Paid 7 222672674688503043 b 10 := by
  by_cases h0 : b ≤ 46
  · exact interval (lo := 4) (hi := 46) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  by_cases h1 : b ≤ 106
  · exact interval (lo := 47) (hi := 106) (l := 9) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 107) (hi := 120) (l := 50) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_11 (b : ℕ) (hb : b ≤ 120) (hv : 11 ≤ 3*b) : Paid 7 222672674688503043 b 11 := by
  by_cases h0 : b ≤ 41
  · exact interval (lo := 4) (hi := 41) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  by_cases h1 : b ≤ 95
  · exact interval (lo := 42) (hi := 95) (l := 9) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 96) (hi := 120) (l := 49) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_12 (b : ℕ) (hb : b ≤ 120) (hv : 12 ≤ 3*b) : Paid 7 222672674688503043 b 12 := by
  by_cases h0 : b ≤ 37
  · exact interval (lo := 4) (hi := 37) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  by_cases h1 : b ≤ 86
  · exact interval (lo := 38) (hi := 86) (l := 9) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 87) (hi := 120) (l := 48) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_13 (b : ℕ) (hb : b ≤ 120) (hv : 13 ≤ 3*b) : Paid 7 222672674688503043 b 13 := by
  by_cases h0 : b ≤ 33
  · exact interval (lo := 5) (hi := 33) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 34) (hi := 120) (l := 31) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_14 (b : ℕ) (hb : b ≤ 120) (hv : 14 ≤ 3*b) : Paid 7 222672674688503043 b 14 := by
  by_cases h0 : b ≤ 30
  · exact interval (lo := 5) (hi := 30) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 31) (hi := 120) (l := 31) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_15 (b : ℕ) (hb : b ≤ 120) (hv : 15 ≤ 3*b) : Paid 7 222672674688503043 b 15 := by
  by_cases h0 : b ≤ 28
  · exact interval (lo := 5) (hi := 28) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 29) (hi := 120) (l := 31) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_16 (b : ℕ) (hb : b ≤ 120) (hv : 16 ≤ 3*b) : Paid 7 222672674688503043 b 16 := by
  by_cases h0 : b ≤ 25
  · exact interval (lo := 6) (hi := 25) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 26) (hi := 120) (l := 31) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_17 (b : ℕ) (hb : b ≤ 120) (hv : 17 ≤ 3*b) : Paid 7 222672674688503043 b 17 := by
  by_cases h0 : b ≤ 23
  · exact interval (lo := 6) (hi := 23) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 24) (hi := 120) (l := 31) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_18 (b : ℕ) (hb : b ≤ 120) (hv : 18 ≤ 3*b) : Paid 7 222672674688503043 b 18 := by
  by_cases h0 : b ≤ 22
  · exact interval (lo := 6) (hi := 22) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 23) (hi := 120) (l := 31) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_19 (b : ℕ) (hb : b ≤ 120) (hv : 19 ≤ 3*b) : Paid 7 222672674688503043 b 19 := by
  by_cases h0 : b ≤ 20
  · exact interval (lo := 7) (hi := 20) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 21) (hi := 120) (l := 31) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_20 (b : ℕ) (hb : b ≤ 120) (hv : 20 ≤ 3*b) : Paid 7 222672674688503043 b 20 := by
  exact interval (lo := 7) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_21 (b : ℕ) (hb : b ≤ 120) (hv : 21 ≤ 3*b) : Paid 7 222672674688503043 b 21 := by
  exact interval (lo := 7) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_22 (b : ℕ) (hb : b ≤ 120) (hv : 22 ≤ 3*b) : Paid 7 222672674688503043 b 22 := by
  exact interval (lo := 8) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_23 (b : ℕ) (hb : b ≤ 120) (hv : 23 ≤ 3*b) : Paid 7 222672674688503043 b 23 := by
  exact interval (lo := 8) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_24 (b : ℕ) (hb : b ≤ 120) (hv : 24 ≤ 3*b) : Paid 7 222672674688503043 b 24 := by
  exact interval (lo := 8) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_25 (b : ℕ) (hb : b ≤ 120) (hv : 25 ≤ 3*b) : Paid 7 222672674688503043 b 25 := by
  exact interval (lo := 9) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_26 (b : ℕ) (hb : b ≤ 120) (hv : 26 ≤ 3*b) : Paid 7 222672674688503043 b 26 := by
  exact interval (lo := 9) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_27 (b : ℕ) (hb : b ≤ 120) (hv : 27 ≤ 3*b) : Paid 7 222672674688503043 b 27 := by
  exact interval (lo := 9) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_28 (b : ℕ) (hb : b ≤ 120) (hv : 28 ≤ 3*b) : Paid 7 222672674688503043 b 28 := by
  exact interval (lo := 10) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_29 (b : ℕ) (hb : b ≤ 120) (hv : 29 ≤ 3*b) : Paid 7 222672674688503043 b 29 := by
  exact interval (lo := 10) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_30 (b : ℕ) (hb : b ≤ 120) (hv : 30 ≤ 3*b) : Paid 7 222672674688503043 b 30 := by
  exact interval (lo := 10) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_31 (b : ℕ) (hb : b ≤ 120) (hv : 31 ≤ 3*b) : Paid 7 222672674688503043 b 31 := by
  exact interval (lo := 11) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_32 (b : ℕ) (hb : b ≤ 120) (hv : 32 ≤ 3*b) : Paid 7 222672674688503043 b 32 := by
  exact interval (lo := 11) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_33 (b : ℕ) (hb : b ≤ 120) (hv : 33 ≤ 3*b) : Paid 7 222672674688503043 b 33 := by
  exact interval (lo := 11) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_34 (b : ℕ) (hb : b ≤ 120) (hv : 34 ≤ 3*b) : Paid 7 222672674688503043 b 34 := by
  exact interval (lo := 12) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_35 (b : ℕ) (hb : b ≤ 120) (hv : 35 ≤ 3*b) : Paid 7 222672674688503043 b 35 := by
  exact interval (lo := 12) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_36 (b : ℕ) (hb : b ≤ 120) (hv : 36 ≤ 3*b) : Paid 7 222672674688503043 b 36 := by
  exact interval (lo := 12) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_37 (b : ℕ) (hb : b ≤ 120) (hv : 37 ≤ 3*b) : Paid 7 222672674688503043 b 37 := by
  by_cases h0 : b ≤ 116
  · exact interval (lo := 13) (hi := 116) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 117) (hi := 120) (l := 51) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_38 (b : ℕ) (hb : b ≤ 120) (hv : 38 ≤ 3*b) : Paid 7 222672674688503043 b 38 := by
  by_cases h0 : b ≤ 113
  · exact interval (lo := 13) (hi := 113) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 114) (hi := 120) (l := 51) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_39 (b : ℕ) (hb : b ≤ 120) (hv : 39 ≤ 3*b) : Paid 7 222672674688503043 b 39 := by
  by_cases h0 : b ≤ 110
  · exact interval (lo := 13) (hi := 110) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 111) (hi := 120) (l := 51) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_40 (b : ℕ) (hb : b ≤ 120) (hv : 40 ≤ 3*b) : Paid 7 222672674688503043 b 40 := by
  by_cases h0 : b ≤ 107
  · exact interval (lo := 14) (hi := 107) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 108) (hi := 120) (l := 51) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_41 (b : ℕ) (hb : b ≤ 120) (hv : 41 ≤ 3*b) : Paid 7 222672674688503043 b 41 := by
  exact interval (lo := 14) (hi := 120) (l := 53) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_42 (b : ℕ) (hb : b ≤ 120) (hv : 42 ≤ 3*b) : Paid 7 222672674688503043 b 42 := by
  exact interval (lo := 14) (hi := 120) (l := 53) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_43 (b : ℕ) (hb : b ≤ 120) (hv : 43 ≤ 3*b) : Paid 7 222672674688503043 b 43 := by
  exact interval (lo := 15) (hi := 120) (l := 53) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_44 (b : ℕ) (hb : b ≤ 120) (hv : 44 ≤ 3*b) : Paid 7 222672674688503043 b 44 := by
  exact interval (lo := 15) (hi := 120) (l := 53) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_45 (b : ℕ) (hb : b ≤ 120) (hv : 45 ≤ 3*b) : Paid 7 222672674688503043 b 45 := by
  exact interval (lo := 15) (hi := 120) (l := 53) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_46 (b : ℕ) (hb : b ≤ 120) (hv : 46 ≤ 3*b) : Paid 7 222672674688503043 b 46 := by
  by_cases h0 : b ≤ 118
  · exact interval (lo := 16) (hi := 118) (l := 53) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 119) (hi := 120) (l := 55) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_47 (b : ℕ) (hb : b ≤ 120) (hv : 47 ≤ 3*b) : Paid 7 222672674688503043 b 47 := by
  by_cases h0 : b ≤ 115
  · exact interval (lo := 16) (hi := 115) (l := 53) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 116) (hi := 120) (l := 55) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row7_48 (b : ℕ) (hb : b ≤ 120) (hv : 48 ≤ 3*b) : Paid 7 222672674688503043 b 48 := by
  by_cases h0 : b ≤ 113
  · exact interval (lo := 16) (hi := 113) (l := 53) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  by_cases h1 : b ≤ 117
  · exact interval (lo := 114) (hi := 117) (l := 55) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 118) (hi := 120) (l := 56) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_3 (b : ℕ) (hb : b ≤ 120) (hv : 3 ≤ 3*b) : Paid 9 229472478411275283 b 3 := by
  exact interval (lo := 1) (hi := 120) (l := 1) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_4 (b : ℕ) (hb : b ≤ 120) (hv : 4 ≤ 3*b) : Paid 9 229472478411275283 b 4 := by
  by_cases h0 : b ≤ 68
  · exact interval (lo := 2) (hi := 68) (l := 1) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 69) (hi := 120) (l := 8) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_5 (b : ℕ) (hb : b ≤ 120) (hv : 5 ≤ 3*b) : Paid 9 229472478411275283 b 5 := by
  by_cases h0 : b ≤ 39
  · exact interval (lo := 2) (hi := 39) (l := 1) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 40) (hi := 120) (l := 8) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_6 (b : ℕ) (hb : b ≤ 120) (hv : 6 ≤ 3*b) : Paid 9 229472478411275283 b 6 := by
  by_cases h0 : b ≤ 26
  · exact interval (lo := 2) (hi := 26) (l := 1) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 27) (hi := 120) (l := 8) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_7 (b : ℕ) (hb : b ≤ 120) (hv : 7 ≤ 3*b) : Paid 9 229472478411275283 b 7 := by
  by_cases h0 : b ≤ 81
  · exact interval (lo := 3) (hi := 81) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 82) (hi := 120) (l := 9) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_8 (b : ℕ) (hb : b ≤ 120) (hv : 8 ≤ 3*b) : Paid 9 229472478411275283 b 8 := by
  by_cases h0 : b ≤ 65
  · exact interval (lo := 3) (hi := 65) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 66) (hi := 120) (l := 9) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_9 (b : ℕ) (hb : b ≤ 120) (hv : 9 ≤ 3*b) : Paid 9 229472478411275283 b 9 := by
  by_cases h0 : b ≤ 55
  · exact interval (lo := 3) (hi := 55) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 56) (hi := 120) (l := 9) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_10 (b : ℕ) (hb : b ≤ 120) (hv : 10 ≤ 3*b) : Paid 9 229472478411275283 b 10 := by
  by_cases h0 : b ≤ 48
  · exact interval (lo := 4) (hi := 48) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  by_cases h1 : b ≤ 110
  · exact interval (lo := 49) (hi := 110) (l := 9) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 111) (hi := 120) (l := 50) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_11 (b : ℕ) (hb : b ≤ 120) (hv : 11 ≤ 3*b) : Paid 9 229472478411275283 b 11 := by
  by_cases h0 : b ≤ 43
  · exact interval (lo := 4) (hi := 43) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  by_cases h1 : b ≤ 98
  · exact interval (lo := 44) (hi := 98) (l := 9) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 99) (hi := 120) (l := 49) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_12 (b : ℕ) (hb : b ≤ 120) (hv : 12 ≤ 3*b) : Paid 9 229472478411275283 b 12 := by
  by_cases h0 : b ≤ 38
  · exact interval (lo := 4) (hi := 38) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  by_cases h1 : b ≤ 88
  · exact interval (lo := 39) (hi := 88) (l := 9) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 89) (hi := 120) (l := 48) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_13 (b : ℕ) (hb : b ≤ 120) (hv : 13 ≤ 3*b) : Paid 9 229472478411275283 b 13 := by
  by_cases h0 : b ≤ 35
  · exact interval (lo := 5) (hi := 35) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 36) (hi := 120) (l := 31) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_14 (b : ℕ) (hb : b ≤ 120) (hv : 14 ≤ 3*b) : Paid 9 229472478411275283 b 14 := by
  by_cases h0 : b ≤ 31
  · exact interval (lo := 5) (hi := 31) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 32) (hi := 120) (l := 31) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_15 (b : ℕ) (hb : b ≤ 120) (hv : 15 ≤ 3*b) : Paid 9 229472478411275283 b 15 := by
  by_cases h0 : b ≤ 29
  · exact interval (lo := 5) (hi := 29) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 30) (hi := 120) (l := 31) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_16 (b : ℕ) (hb : b ≤ 120) (hv : 16 ≤ 3*b) : Paid 9 229472478411275283 b 16 := by
  by_cases h0 : b ≤ 26
  · exact interval (lo := 6) (hi := 26) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 27) (hi := 120) (l := 31) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_17 (b : ℕ) (hb : b ≤ 120) (hv : 17 ≤ 3*b) : Paid 9 229472478411275283 b 17 := by
  by_cases h0 : b ≤ 24
  · exact interval (lo := 6) (hi := 24) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 25) (hi := 120) (l := 31) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_18 (b : ℕ) (hb : b ≤ 120) (hv : 18 ≤ 3*b) : Paid 9 229472478411275283 b 18 := by
  by_cases h0 : b ≤ 22
  · exact interval (lo := 6) (hi := 22) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 23) (hi := 120) (l := 31) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_19 (b : ℕ) (hb : b ≤ 120) (hv : 19 ≤ 3*b) : Paid 9 229472478411275283 b 19 := by
  by_cases h0 : b ≤ 21
  · exact interval (lo := 7) (hi := 21) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 22) (hi := 120) (l := 31) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_20 (b : ℕ) (hb : b ≤ 120) (hv : 20 ≤ 3*b) : Paid 9 229472478411275283 b 20 := by
  exact interval (lo := 7) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_21 (b : ℕ) (hb : b ≤ 120) (hv : 21 ≤ 3*b) : Paid 9 229472478411275283 b 21 := by
  exact interval (lo := 7) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_22 (b : ℕ) (hb : b ≤ 120) (hv : 22 ≤ 3*b) : Paid 9 229472478411275283 b 22 := by
  exact interval (lo := 8) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_23 (b : ℕ) (hb : b ≤ 120) (hv : 23 ≤ 3*b) : Paid 9 229472478411275283 b 23 := by
  exact interval (lo := 8) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_24 (b : ℕ) (hb : b ≤ 120) (hv : 24 ≤ 3*b) : Paid 9 229472478411275283 b 24 := by
  exact interval (lo := 8) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_25 (b : ℕ) (hb : b ≤ 120) (hv : 25 ≤ 3*b) : Paid 9 229472478411275283 b 25 := by
  exact interval (lo := 9) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_26 (b : ℕ) (hb : b ≤ 120) (hv : 26 ≤ 3*b) : Paid 9 229472478411275283 b 26 := by
  exact interval (lo := 9) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_27 (b : ℕ) (hb : b ≤ 120) (hv : 27 ≤ 3*b) : Paid 9 229472478411275283 b 27 := by
  exact interval (lo := 9) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_28 (b : ℕ) (hb : b ≤ 120) (hv : 28 ≤ 3*b) : Paid 9 229472478411275283 b 28 := by
  exact interval (lo := 10) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_29 (b : ℕ) (hb : b ≤ 120) (hv : 29 ≤ 3*b) : Paid 9 229472478411275283 b 29 := by
  exact interval (lo := 10) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_30 (b : ℕ) (hb : b ≤ 120) (hv : 30 ≤ 3*b) : Paid 9 229472478411275283 b 30 := by
  exact interval (lo := 10) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_31 (b : ℕ) (hb : b ≤ 120) (hv : 31 ≤ 3*b) : Paid 9 229472478411275283 b 31 := by
  exact interval (lo := 11) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_32 (b : ℕ) (hb : b ≤ 120) (hv : 32 ≤ 3*b) : Paid 9 229472478411275283 b 32 := by
  exact interval (lo := 11) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_33 (b : ℕ) (hb : b ≤ 120) (hv : 33 ≤ 3*b) : Paid 9 229472478411275283 b 33 := by
  exact interval (lo := 11) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_34 (b : ℕ) (hb : b ≤ 120) (hv : 34 ≤ 3*b) : Paid 9 229472478411275283 b 34 := by
  exact interval (lo := 12) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_35 (b : ℕ) (hb : b ≤ 120) (hv : 35 ≤ 3*b) : Paid 9 229472478411275283 b 35 := by
  exact interval (lo := 12) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_36 (b : ℕ) (hb : b ≤ 120) (hv : 36 ≤ 3*b) : Paid 9 229472478411275283 b 36 := by
  exact interval (lo := 12) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_37 (b : ℕ) (hb : b ≤ 120) (hv : 37 ≤ 3*b) : Paid 9 229472478411275283 b 37 := by
  by_cases h0 : b ≤ 118
  · exact interval (lo := 13) (hi := 118) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 119) (hi := 120) (l := 51) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_38 (b : ℕ) (hb : b ≤ 120) (hv : 38 ≤ 3*b) : Paid 9 229472478411275283 b 38 := by
  by_cases h0 : b ≤ 115
  · exact interval (lo := 13) (hi := 115) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 116) (hi := 120) (l := 51) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_39 (b : ℕ) (hb : b ≤ 120) (hv : 39 ≤ 3*b) : Paid 9 229472478411275283 b 39 := by
  by_cases h0 : b ≤ 112
  · exact interval (lo := 13) (hi := 112) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 113) (hi := 120) (l := 51) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_40 (b : ℕ) (hb : b ≤ 120) (hv : 40 ≤ 3*b) : Paid 9 229472478411275283 b 40 := by
  by_cases h0 : b ≤ 109
  · exact interval (lo := 14) (hi := 109) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 110) (hi := 120) (l := 51) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_41 (b : ℕ) (hb : b ≤ 120) (hv : 41 ≤ 3*b) : Paid 9 229472478411275283 b 41 := by
  exact interval (lo := 14) (hi := 120) (l := 53) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_42 (b : ℕ) (hb : b ≤ 120) (hv : 42 ≤ 3*b) : Paid 9 229472478411275283 b 42 := by
  exact interval (lo := 14) (hi := 120) (l := 53) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_43 (b : ℕ) (hb : b ≤ 120) (hv : 43 ≤ 3*b) : Paid 9 229472478411275283 b 43 := by
  exact interval (lo := 15) (hi := 120) (l := 53) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_44 (b : ℕ) (hb : b ≤ 120) (hv : 44 ≤ 3*b) : Paid 9 229472478411275283 b 44 := by
  exact interval (lo := 15) (hi := 120) (l := 53) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_45 (b : ℕ) (hb : b ≤ 120) (hv : 45 ≤ 3*b) : Paid 9 229472478411275283 b 45 := by
  exact interval (lo := 15) (hi := 120) (l := 53) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_46 (b : ℕ) (hb : b ≤ 120) (hv : 46 ≤ 3*b) : Paid 9 229472478411275283 b 46 := by
  by_cases h0 : b ≤ 119
  · exact interval (lo := 16) (hi := 119) (l := 53) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 120) (hi := 120) (l := 55) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_47 (b : ℕ) (hb : b ≤ 120) (hv : 47 ≤ 3*b) : Paid 9 229472478411275283 b 47 := by
  by_cases h0 : b ≤ 116
  · exact interval (lo := 16) (hi := 116) (l := 53) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 117) (hi := 120) (l := 55) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row9_48 (b : ℕ) (hb : b ≤ 120) (hv : 48 ≤ 3*b) : Paid 9 229472478411275283 b 48 := by
  by_cases h0 : b ≤ 114
  · exact interval (lo := 16) (hi := 114) (l := 53) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  by_cases h1 : b ≤ 118
  · exact interval (lo := 115) (hi := 118) (l := 55) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 119) (hi := 120) (l := 56) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_3 (b : ℕ) (hb : b ≤ 120) (hv : 3 ≤ 3*b) : Paid 10 229473781150506218 b 3 := by
  exact interval (lo := 1) (hi := 120) (l := 1) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_4 (b : ℕ) (hb : b ≤ 120) (hv : 4 ≤ 3*b) : Paid 10 229473781150506218 b 4 := by
  by_cases h0 : b ≤ 68
  · exact interval (lo := 2) (hi := 68) (l := 1) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 69) (hi := 120) (l := 8) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_5 (b : ℕ) (hb : b ≤ 120) (hv : 5 ≤ 3*b) : Paid 10 229473781150506218 b 5 := by
  by_cases h0 : b ≤ 39
  · exact interval (lo := 2) (hi := 39) (l := 1) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 40) (hi := 120) (l := 8) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_6 (b : ℕ) (hb : b ≤ 120) (hv : 6 ≤ 3*b) : Paid 10 229473781150506218 b 6 := by
  by_cases h0 : b ≤ 26
  · exact interval (lo := 2) (hi := 26) (l := 1) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 27) (hi := 120) (l := 8) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_7 (b : ℕ) (hb : b ≤ 120) (hv : 7 ≤ 3*b) : Paid 10 229473781150506218 b 7 := by
  by_cases h0 : b ≤ 81
  · exact interval (lo := 3) (hi := 81) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 82) (hi := 120) (l := 9) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_8 (b : ℕ) (hb : b ≤ 120) (hv : 8 ≤ 3*b) : Paid 10 229473781150506218 b 8 := by
  by_cases h0 : b ≤ 65
  · exact interval (lo := 3) (hi := 65) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 66) (hi := 120) (l := 9) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_9 (b : ℕ) (hb : b ≤ 120) (hv : 9 ≤ 3*b) : Paid 10 229473781150506218 b 9 := by
  by_cases h0 : b ≤ 55
  · exact interval (lo := 3) (hi := 55) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 56) (hi := 120) (l := 9) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_10 (b : ℕ) (hb : b ≤ 120) (hv : 10 ≤ 3*b) : Paid 10 229473781150506218 b 10 := by
  by_cases h0 : b ≤ 48
  · exact interval (lo := 4) (hi := 48) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  by_cases h1 : b ≤ 110
  · exact interval (lo := 49) (hi := 110) (l := 9) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 111) (hi := 120) (l := 50) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_11 (b : ℕ) (hb : b ≤ 120) (hv : 11 ≤ 3*b) : Paid 10 229473781150506218 b 11 := by
  by_cases h0 : b ≤ 43
  · exact interval (lo := 4) (hi := 43) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  by_cases h1 : b ≤ 98
  · exact interval (lo := 44) (hi := 98) (l := 9) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 99) (hi := 120) (l := 49) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_12 (b : ℕ) (hb : b ≤ 120) (hv : 12 ≤ 3*b) : Paid 10 229473781150506218 b 12 := by
  by_cases h0 : b ≤ 38
  · exact interval (lo := 4) (hi := 38) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  by_cases h1 : b ≤ 88
  · exact interval (lo := 39) (hi := 88) (l := 9) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 89) (hi := 120) (l := 48) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_13 (b : ℕ) (hb : b ≤ 120) (hv : 13 ≤ 3*b) : Paid 10 229473781150506218 b 13 := by
  by_cases h0 : b ≤ 35
  · exact interval (lo := 5) (hi := 35) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 36) (hi := 120) (l := 31) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_14 (b : ℕ) (hb : b ≤ 120) (hv : 14 ≤ 3*b) : Paid 10 229473781150506218 b 14 := by
  by_cases h0 : b ≤ 31
  · exact interval (lo := 5) (hi := 31) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 32) (hi := 120) (l := 31) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_15 (b : ℕ) (hb : b ≤ 120) (hv : 15 ≤ 3*b) : Paid 10 229473781150506218 b 15 := by
  by_cases h0 : b ≤ 29
  · exact interval (lo := 5) (hi := 29) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 30) (hi := 120) (l := 31) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_16 (b : ℕ) (hb : b ≤ 120) (hv : 16 ≤ 3*b) : Paid 10 229473781150506218 b 16 := by
  by_cases h0 : b ≤ 26
  · exact interval (lo := 6) (hi := 26) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 27) (hi := 120) (l := 31) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_17 (b : ℕ) (hb : b ≤ 120) (hv : 17 ≤ 3*b) : Paid 10 229473781150506218 b 17 := by
  by_cases h0 : b ≤ 24
  · exact interval (lo := 6) (hi := 24) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 25) (hi := 120) (l := 31) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_18 (b : ℕ) (hb : b ≤ 120) (hv : 18 ≤ 3*b) : Paid 10 229473781150506218 b 18 := by
  by_cases h0 : b ≤ 22
  · exact interval (lo := 6) (hi := 22) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 23) (hi := 120) (l := 31) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_19 (b : ℕ) (hb : b ≤ 120) (hv : 19 ≤ 3*b) : Paid 10 229473781150506218 b 19 := by
  by_cases h0 : b ≤ 21
  · exact interval (lo := 7) (hi := 21) (l := 4) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 22) (hi := 120) (l := 31) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_20 (b : ℕ) (hb : b ≤ 120) (hv : 20 ≤ 3*b) : Paid 10 229473781150506218 b 20 := by
  exact interval (lo := 7) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_21 (b : ℕ) (hb : b ≤ 120) (hv : 21 ≤ 3*b) : Paid 10 229473781150506218 b 21 := by
  exact interval (lo := 7) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_22 (b : ℕ) (hb : b ≤ 120) (hv : 22 ≤ 3*b) : Paid 10 229473781150506218 b 22 := by
  exact interval (lo := 8) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_23 (b : ℕ) (hb : b ≤ 120) (hv : 23 ≤ 3*b) : Paid 10 229473781150506218 b 23 := by
  exact interval (lo := 8) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_24 (b : ℕ) (hb : b ≤ 120) (hv : 24 ≤ 3*b) : Paid 10 229473781150506218 b 24 := by
  exact interval (lo := 8) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_25 (b : ℕ) (hb : b ≤ 120) (hv : 25 ≤ 3*b) : Paid 10 229473781150506218 b 25 := by
  exact interval (lo := 9) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_26 (b : ℕ) (hb : b ≤ 120) (hv : 26 ≤ 3*b) : Paid 10 229473781150506218 b 26 := by
  exact interval (lo := 9) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_27 (b : ℕ) (hb : b ≤ 120) (hv : 27 ≤ 3*b) : Paid 10 229473781150506218 b 27 := by
  exact interval (lo := 9) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_28 (b : ℕ) (hb : b ≤ 120) (hv : 28 ≤ 3*b) : Paid 10 229473781150506218 b 28 := by
  exact interval (lo := 10) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_29 (b : ℕ) (hb : b ≤ 120) (hv : 29 ≤ 3*b) : Paid 10 229473781150506218 b 29 := by
  exact interval (lo := 10) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_30 (b : ℕ) (hb : b ≤ 120) (hv : 30 ≤ 3*b) : Paid 10 229473781150506218 b 30 := by
  exact interval (lo := 10) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_31 (b : ℕ) (hb : b ≤ 120) (hv : 31 ≤ 3*b) : Paid 10 229473781150506218 b 31 := by
  exact interval (lo := 11) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_32 (b : ℕ) (hb : b ≤ 120) (hv : 32 ≤ 3*b) : Paid 10 229473781150506218 b 32 := by
  exact interval (lo := 11) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_33 (b : ℕ) (hb : b ≤ 120) (hv : 33 ≤ 3*b) : Paid 10 229473781150506218 b 33 := by
  exact interval (lo := 11) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_34 (b : ℕ) (hb : b ≤ 120) (hv : 34 ≤ 3*b) : Paid 10 229473781150506218 b 34 := by
  exact interval (lo := 12) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_35 (b : ℕ) (hb : b ≤ 120) (hv : 35 ≤ 3*b) : Paid 10 229473781150506218 b 35 := by
  exact interval (lo := 12) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_36 (b : ℕ) (hb : b ≤ 120) (hv : 36 ≤ 3*b) : Paid 10 229473781150506218 b 36 := by
  exact interval (lo := 12) (hi := 120) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_37 (b : ℕ) (hb : b ≤ 120) (hv : 37 ≤ 3*b) : Paid 10 229473781150506218 b 37 := by
  by_cases h0 : b ≤ 118
  · exact interval (lo := 13) (hi := 118) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 119) (hi := 120) (l := 51) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_38 (b : ℕ) (hb : b ≤ 120) (hv : 38 ≤ 3*b) : Paid 10 229473781150506218 b 38 := by
  by_cases h0 : b ≤ 115
  · exact interval (lo := 13) (hi := 115) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 116) (hi := 120) (l := 51) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_39 (b : ℕ) (hb : b ≤ 120) (hv : 39 ≤ 3*b) : Paid 10 229473781150506218 b 39 := by
  by_cases h0 : b ≤ 111
  · exact interval (lo := 13) (hi := 111) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 112) (hi := 120) (l := 51) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_40 (b : ℕ) (hb : b ≤ 120) (hv : 40 ≤ 3*b) : Paid 10 229473781150506218 b 40 := by
  by_cases h0 : b ≤ 108
  · exact interval (lo := 14) (hi := 108) (l := 42) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 109) (hi := 120) (l := 51) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_41 (b : ℕ) (hb : b ≤ 120) (hv : 41 ≤ 3*b) : Paid 10 229473781150506218 b 41 := by
  exact interval (lo := 14) (hi := 120) (l := 53) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_42 (b : ℕ) (hb : b ≤ 120) (hv : 42 ≤ 3*b) : Paid 10 229473781150506218 b 42 := by
  exact interval (lo := 14) (hi := 120) (l := 53) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_43 (b : ℕ) (hb : b ≤ 120) (hv : 43 ≤ 3*b) : Paid 10 229473781150506218 b 43 := by
  exact interval (lo := 15) (hi := 120) (l := 53) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_44 (b : ℕ) (hb : b ≤ 120) (hv : 44 ≤ 3*b) : Paid 10 229473781150506218 b 44 := by
  exact interval (lo := 15) (hi := 120) (l := 53) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_45 (b : ℕ) (hb : b ≤ 120) (hv : 45 ≤ 3*b) : Paid 10 229473781150506218 b 45 := by
  exact interval (lo := 15) (hi := 120) (l := 53) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_46 (b : ℕ) (hb : b ≤ 120) (hv : 46 ≤ 3*b) : Paid 10 229473781150506218 b 46 := by
  by_cases h0 : b ≤ 118
  · exact interval (lo := 16) (hi := 118) (l := 53) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 119) (hi := 120) (l := 55) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_47 (b : ℕ) (hb : b ≤ 120) (hv : 47 ≤ 3*b) : Paid 10 229473781150506218 b 47 := by
  by_cases h0 : b ≤ 115
  · exact interval (lo := 16) (hi := 115) (l := 53) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 116) (hi := 120) (l := 55) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
private theorem row10_48 (b : ℕ) (hb : b ≤ 120) (hv : 48 ≤ 3*b) : Paid 10 229473781150506218 b 48 := by
  by_cases h0 : b ≤ 113
  · exact interval (lo := 16) (hi := 113) (l := 53) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  by_cases h1 : b ≤ 117
  · exact interval (lo := 114) (hi := 117) (l := 55) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
  exact interval (lo := 118) (hi := 120) (l := 56) (by omega) (by omega) (by decide) (by decide +kernel) (by decide +kernel)
theorem proof : P0_9_8.c3 := by
  intro a tcap ha htcap hbox
  have hz : K1_13_8.zeroShape.plus a = a := by cases a; simp [K1_13_8.zeroShape,Shape.plus]
  rw [hz] at hbox
  have hb : a.b ≤ 120 := hbox.1
  have hj : a.j ≤ 48 := hbox.2.1
  have ht : a.t ≤ 10 := hbox.2.2
  have hd := ha.2.2
  have hv := ha.2.1
  have hp := ha.1
  have paid (top rate : ℕ) (hT : a.t ≤ top)
      (hrows : ∀ j, 3 ≤ j → j ≤ 48 → j ≤ 3*a.b → Paid top rate a.b j) :
      P0_9.physicalPrice a (emptyOrder a) ≤ indexBudget K1_13_8.zeroShape rate a.j := by
    have hm : InBox a (peak top a.b a.j) := ⟨le_rfl,le_rfl,le_min hT (by omega)⟩
    apply (physical_mono hm hv (peak_index _ _ _) (emptyOrder a)).trans
    exact hrows a.j (by omega) hj hd
  unfold P0_9.factorPrice
  split_ifs with h7 h9
  · apply paid 7 _ (by omega)
    intro j hlo hhi hv
    interval_cases j
    · exact row7_3 _ hb hv
    · exact row7_4 _ hb hv
    · exact row7_5 _ hb hv
    · exact row7_6 _ hb hv
    · exact row7_7 _ hb hv
    · exact row7_8 _ hb hv
    · exact row7_9 _ hb hv
    · exact row7_10 _ hb hv
    · exact row7_11 _ hb hv
    · exact row7_12 _ hb hv
    · exact row7_13 _ hb hv
    · exact row7_14 _ hb hv
    · exact row7_15 _ hb hv
    · exact row7_16 _ hb hv
    · exact row7_17 _ hb hv
    · exact row7_18 _ hb hv
    · exact row7_19 _ hb hv
    · exact row7_20 _ hb hv
    · exact row7_21 _ hb hv
    · exact row7_22 _ hb hv
    · exact row7_23 _ hb hv
    · exact row7_24 _ hb hv
    · exact row7_25 _ hb hv
    · exact row7_26 _ hb hv
    · exact row7_27 _ hb hv
    · exact row7_28 _ hb hv
    · exact row7_29 _ hb hv
    · exact row7_30 _ hb hv
    · exact row7_31 _ hb hv
    · exact row7_32 _ hb hv
    · exact row7_33 _ hb hv
    · exact row7_34 _ hb hv
    · exact row7_35 _ hb hv
    · exact row7_36 _ hb hv
    · exact row7_37 _ hb hv
    · exact row7_38 _ hb hv
    · exact row7_39 _ hb hv
    · exact row7_40 _ hb hv
    · exact row7_41 _ hb hv
    · exact row7_42 _ hb hv
    · exact row7_43 _ hb hv
    · exact row7_44 _ hb hv
    · exact row7_45 _ hb hv
    · exact row7_46 _ hb hv
    · exact row7_47 _ hb hv
    · exact row7_48 _ hb hv
  · apply paid 9 _ (by omega)
    intro j hlo hhi hv
    interval_cases j
    · exact row9_3 _ hb hv
    · exact row9_4 _ hb hv
    · exact row9_5 _ hb hv
    · exact row9_6 _ hb hv
    · exact row9_7 _ hb hv
    · exact row9_8 _ hb hv
    · exact row9_9 _ hb hv
    · exact row9_10 _ hb hv
    · exact row9_11 _ hb hv
    · exact row9_12 _ hb hv
    · exact row9_13 _ hb hv
    · exact row9_14 _ hb hv
    · exact row9_15 _ hb hv
    · exact row9_16 _ hb hv
    · exact row9_17 _ hb hv
    · exact row9_18 _ hb hv
    · exact row9_19 _ hb hv
    · exact row9_20 _ hb hv
    · exact row9_21 _ hb hv
    · exact row9_22 _ hb hv
    · exact row9_23 _ hb hv
    · exact row9_24 _ hb hv
    · exact row9_25 _ hb hv
    · exact row9_26 _ hb hv
    · exact row9_27 _ hb hv
    · exact row9_28 _ hb hv
    · exact row9_29 _ hb hv
    · exact row9_30 _ hb hv
    · exact row9_31 _ hb hv
    · exact row9_32 _ hb hv
    · exact row9_33 _ hb hv
    · exact row9_34 _ hb hv
    · exact row9_35 _ hb hv
    · exact row9_36 _ hb hv
    · exact row9_37 _ hb hv
    · exact row9_38 _ hb hv
    · exact row9_39 _ hb hv
    · exact row9_40 _ hb hv
    · exact row9_41 _ hb hv
    · exact row9_42 _ hb hv
    · exact row9_43 _ hb hv
    · exact row9_44 _ hb hv
    · exact row9_45 _ hb hv
    · exact row9_46 _ hb hv
    · exact row9_47 _ hb hv
    · exact row9_48 _ hb hv
  · apply paid 10 _ ht
    intro j hlo hhi hv
    interval_cases j
    · exact row10_3 _ hb hv
    · exact row10_4 _ hb hv
    · exact row10_5 _ hb hv
    · exact row10_6 _ hb hv
    · exact row10_7 _ hb hv
    · exact row10_8 _ hb hv
    · exact row10_9 _ hb hv
    · exact row10_10 _ hb hv
    · exact row10_11 _ hb hv
    · exact row10_12 _ hb hv
    · exact row10_13 _ hb hv
    · exact row10_14 _ hb hv
    · exact row10_15 _ hb hv
    · exact row10_16 _ hb hv
    · exact row10_17 _ hb hv
    · exact row10_18 _ hb hv
    · exact row10_19 _ hb hv
    · exact row10_20 _ hb hv
    · exact row10_21 _ hb hv
    · exact row10_22 _ hb hv
    · exact row10_23 _ hb hv
    · exact row10_24 _ hb hv
    · exact row10_25 _ hb hv
    · exact row10_26 _ hb hv
    · exact row10_27 _ hb hv
    · exact row10_28 _ hb hv
    · exact row10_29 _ hb hv
    · exact row10_30 _ hb hv
    · exact row10_31 _ hb hv
    · exact row10_32 _ hb hv
    · exact row10_33 _ hb hv
    · exact row10_34 _ hb hv
    · exact row10_35 _ hb hv
    · exact row10_36 _ hb hv
    · exact row10_37 _ hb hv
    · exact row10_38 _ hb hv
    · exact row10_39 _ hb hv
    · exact row10_40 _ hb hv
    · exact row10_41 _ hb hv
    · exact row10_42 _ hb hv
    · exact row10_43 _ hb hv
    · exact row10_44 _ hb hv
    · exact row10_45 _ hb hv
    · exact row10_46 _ hb hv
    · exact row10_47 _ hb hv
    · exact row10_48 _ hb hv
end P0_9_8_3
