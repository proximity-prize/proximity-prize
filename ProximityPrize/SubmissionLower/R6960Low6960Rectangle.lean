import ProximityPrize.SubmissionLower.R6960Low6960AllocCore

set_option Elab.async false
set_option maxHeartbeats 4000000

namespace Low6960Rectangle
open K1_13 (Shape InBox ceilDiv)
open K1_13_8_2 (Chamber mixed_mono)
open Low6960RetainedCut (contractedPrice cutPrice fourSurface chamberHull residualBox hull_valid)
open Low6960Prices (physicalPrice physicalPriceOld)
open Low6960GeometryCut (chargedPrice)
open Low6960Monotone (box_refl normalize_mono normalize_chamber plus_mono plus_chamber scale_mono scale_chamber chart_mono chart_chamber)
open Low6960Monotone (box_refl normalize_mono normalize_chamber plus_mono plus_chamber
  scale_mono scale_chamber chart_mono chart_chamber)

/-- `physicalPriceOld` with the mixed surface numerator left free. -/
def charge (x : Shape) (l scale S : ℕ) : ℕ :=
  let p := x.chamber
  let q := Low6960Prices.primaryBox
  let h := K1_13.chart Low6960Prices.taylorLength p
  let numerator := ceilDiv S scale +
    ceilDiv ((Low6960Prices.errors + 2 * Low6960Prices.incidenceGap) * x.b * q.b *
      (K1_13.chart (Low6960Prices.taylorLength + 1) p).b) Low6960Prices.incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := K1_13.mixed32 p q auxBox h + 2 * x.t * K1_13.mixed32 p p p h
  let points := K1_13.mixed32 p q auxBox p + 2 * x.t * K1_13.mixed32 p p p p
  ceilDiv numerator l + 2 * Low6960Prices.physicalDegree * x.b * q.b +
    ceilDiv (Low6960Prices.errors * curves + 2 * Low6960Prices.incidenceGap * points)
      (32 * Low6960Prices.incidenceGap)

theorem cut_eq (x : Shape) (l scale S : ℕ) : cutPrice x l scale S = charge x l scale S := by
  simp only [cutPrice, charge, chargedPrice, Low6960GeometryCut.auxCurves32,
    Low6960GeometryCut.auxPoints32, Low6960GeometryCut.membershipDegree, Nat.mul_assoc]
  rfl

theorem charge_mono {x y : Shape} (h : InBox x y) (hx : 3 * x.t ≤ x.j)
    (hy : 3 * y.t ≤ y.j) (l scale : ℕ) {S S' : ℕ} (hS : S ≤ S') : charge x l scale S ≤ charge y l scale S' := by
  let p := x.chamber
  let p' := y.chamber
  let q : Shape := Low6960Prices.primaryBox
  let L := Low6960Prices.taylorLength
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
  have hmain : (Low6960Prices.errors + 2*Low6960Prices.incidenceGap) * x.b * q.b * (K1_13.chart (L+1) p).b ≤
      (Low6960Prices.errors + 2*Low6960Prices.incidenceGap) * y.b * q.b * (K1_13.chart (L+1) p').b := by
    have := h.1
    gcongr
  have hcurve := mixed_mono hp (box_refl q) ha (chart_mono L hp) hp'c hqc ha'c hqc hac (chart_chamber L p)
  have hpoint := mixed_mono hp (box_refl q) ha hp hp'c hqc ha'c hqc hac hpc
  have hcurve' := mixed_mono hp hp hp (chart_mono L hp) hp'c hp'c hp'c hpc hpc (chart_chamber L p)
  have hpoint' := mixed_mono hp hp hp hp hp'c hp'c hp'c hpc hpc hpc
  have htc := Nat.mul_le_mul_left 2 h.2.2
  have hc := Nat.add_le_add hcurve (Nat.mul_le_mul htc hcurve')
  have hn := Nat.add_le_add hpoint (Nat.mul_le_mul htc hpoint')
  have hgeom := Nat.add_le_add (Nat.mul_le_mul_left Low6960Prices.errors hc)
    (Nat.mul_le_mul_left (2*Low6960Prices.incidenceGap) hn)
  have hraw := Nat.mul_le_mul_right q.b (Nat.mul_le_mul_left (2*Low6960Prices.physicalDegree) h.1)
  exact Nat.add_le_add
    (Nat.add_le_add (Low6960Monotone.ceil_mono (Nat.add_le_add
      (Low6960Monotone.ceil_mono hS _) (Low6960Monotone.ceil_mono hmain _)) l) hraw)
    (Low6960Monotone.ceil_mono hgeom _)

open Low6960Allocation (Band start MassCell order allowance weight_mono order_mono)

abbrev hullOf (k : Band) (l : ℕ) : Shape := chamberHull (residualBox (start k) l)

def PaidFour {k : Band} (cells : List (MassCell k)) (t bl jl bh jh l : ℕ) : Prop :=
  0 < l ∧ l ≤ order cells ⟨bl,jl,0⟩ ∧ 0 < (hullOf k l).t ∧
    cutPrice ⟨bh,jh,t⟩ l 32 (fourSurface (Shape.chamber ⟨bh,jh,t⟩) (hullOf k l)) ≤
      allowance k ((start k).t+t) bl jl t

instance {k : Band} (cells : List (MassCell k)) (t bl jl bh jh l : ℕ) :
    Decidable (PaidFour cells t bl jl bh jh l) := inferInstanceAs (Decidable (_ ∧ _))

theorem four {k : Band} {cells : List (MassCell k)} {a : Shape} {bl jl bh jh t l : ℕ}
    (h : PaidFour cells t bl jl bh jh l)
    (hb : bl ≤ a.b) (hj : jl ≤ a.j) (hb' : a.b ≤ bh) (hj' : a.j ≤ jh)
    (ht : a.t = t) (ha : 3 * a.t ≤ a.j) :
    ∃ l, 0 < l ∧ l ≤ order cells a ∧ contractedPrice a (start k) l 165 ≤
      allowance k ((start k).t+a.t) a.b a.j a.t := by
  obtain ⟨hl, hlo, hq, hbill⟩ := h
  have hu : l ≤ order cells a := hlo.trans (order_mono cells hb hj)
  have hi : 3*t ≤ jh := by omega
  have hbox : InBox a ⟨bh,jh,t⟩ := ⟨hb', hj', ht.le⟩
  have hallow : allowance k ((start k).t+t) bl jl t ≤ allowance k ((start k).t+t) a.b a.j a.t :=
    Nat.div_le_div_right (Nat.mul_le_mul_left _ (weight_mono k hb hj ht.ge))
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
    exact charge_mono hbox ha hi l 32 hsurf
  have hc : contractedPrice a (start k) l 165 ≤ cutPrice a l 32 (fourSurface a.chamber (hullOf k l)) := by
    unfold contractedPrice
    dsimp only
    rw [if_pos hq]
    split
    · exact (min_le_left _ _).trans (min_le_right _ _)
    · exact min_le_right _ _
  exact hc.trans (hcut.trans (hbill.trans (by simpa only [ht] using hallow)))

#print axioms four
end Low6960Rectangle
