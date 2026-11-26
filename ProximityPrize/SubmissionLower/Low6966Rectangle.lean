import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Compact54Packed
import ProximityPrize.SubmissionLower.Low48BentCycleCap
import ProximityPrize.SubmissionLower.Low48BentCyclePrice
import ProximityPrize.SubmissionLower.Low6966ActiveCycleMixed

section Merged6967_Low6966Rectangle
set_option Elab.async false






set_option Elab.async false

-- merged module R6960Low6966Rectangle
section Merged_R6960Low6966Rectangle

set_option Elab.async false
set_option maxHeartbeats 4000000

namespace Low6966Rectangle
open K1_13 (Shape InBox ceilDiv)
open K1_13_8_2 (Chamber mixed_mono)
open Low6966RetainedCut (contractedPrice cutPrice fourSurface chamberHull residualBox hull_valid)
open Low6966Prices (physicalPrice physicalPriceOld)
open Low6966GeometryCut (chargedPrice)
open Low6966Monotone (box_refl normalize_mono normalize_chamber plus_mono plus_chamber scale_mono scale_chamber chart_mono chart_chamber)
open Low6966Monotone (box_refl normalize_mono normalize_chamber plus_mono plus_chamber
  scale_mono scale_chamber chart_mono chart_chamber)

/-- `physicalPriceOld` with the mixed surface numerator left free. -/
def charge (x : Shape) (l scale S : ℕ) : ℕ :=
  let p := x.chamber
  let q := Low6966Prices.primaryBox
  let h := K1_13.chart Low6966Prices.taylorLength p
  let numerator := ceilDiv S scale +
    ceilDiv ((Low6966Prices.errors + 2 * Low6966Prices.incidenceGap) * x.b * q.b *
      (K1_13.chart (Low6966Prices.taylorLength + 1) p).b) Low6966Prices.incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := K1_13.mixed32 p q auxBox h + 2 * x.t * K1_13.mixed32 p p p h
  let points := K1_13.mixed32 p q auxBox p + 2 * x.t * K1_13.mixed32 p p p p
  ceilDiv numerator l + 2 * Low6966Prices.physicalDegree * x.b * q.b +
    ceilDiv (Low6966Prices.errors * curves + 2 * Low6966Prices.incidenceGap * points)
      (32 * Low6966Prices.incidenceGap)

theorem cut_eq (x : Shape) (l scale S : ℕ) : cutPrice x l scale S = charge x l scale S := by
  simp only [cutPrice, charge, chargedPrice, Low6966GeometryCut.auxCurves32,
    Low6966GeometryCut.auxPoints32, Low6966GeometryCut.membershipDegree, Nat.mul_assoc]
  rfl

theorem charge_mono {x y : Shape} (h : InBox x y) (hx : 3 * x.t ≤ x.j)
    (hy : 3 * y.t ≤ y.j) (l scale : ℕ) {S S' : ℕ} (hS : S ≤ S') : charge x l scale S ≤ charge y l scale S' := by
  let p := x.chamber
  let p' := y.chamber
  let q : Shape := Low6966Prices.primaryBox
  let L := Low6966Prices.taylorLength
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
  have hmain : (Low6966Prices.errors + 2*Low6966Prices.incidenceGap) * x.b * q.b * (K1_13.chart (L+1) p).b ≤
      (Low6966Prices.errors + 2*Low6966Prices.incidenceGap) * y.b * q.b * (K1_13.chart (L+1) p').b := by
    have := h.1
    gcongr
  have hcurve := mixed_mono hp (box_refl q) ha (chart_mono L hp) hp'c hqc ha'c hqc hac (chart_chamber L p)
  have hpoint := mixed_mono hp (box_refl q) ha hp hp'c hqc ha'c hqc hac hpc
  have hcurve' := mixed_mono hp hp hp (chart_mono L hp) hp'c hp'c hp'c hpc hpc (chart_chamber L p)
  have hpoint' := mixed_mono hp hp hp hp hp'c hp'c hp'c hpc hpc hpc
  have htc := Nat.mul_le_mul_left 2 h.2.2
  have hc := Nat.add_le_add hcurve (Nat.mul_le_mul htc hcurve')
  have hn := Nat.add_le_add hpoint (Nat.mul_le_mul htc hpoint')
  have hgeom := Nat.add_le_add (Nat.mul_le_mul_left Low6966Prices.errors hc)
    (Nat.mul_le_mul_left (2*Low6966Prices.incidenceGap) hn)
  have hraw := Nat.mul_le_mul_right q.b (Nat.mul_le_mul_left (2*Low6966Prices.physicalDegree) h.1)
  exact Nat.add_le_add
    (Nat.add_le_add (Low6966Monotone.ceil_mono (Nat.add_le_add
      (Low6966Monotone.ceil_mono hS _) (Low6966Monotone.ceil_mono hmain _)) l) hraw)
    (Low6966Monotone.ceil_mono hgeom _)

open Low6966Allocation (Band start MassCell order allowance weight_mono order_mono)

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
    ∃ l, 0 < l ∧ l ≤ order cells a ∧ contractedPrice a (start k) l 178 ≤
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
  have hc : contractedPrice a (start k) l 178 ≤ cutPrice a l 32 (fourSurface a.chamber (hullOf k l)) := by
    unfold contractedPrice
    dsimp only
    rw [if_pos hq]
    split
    · exact (min_le_left _ _).trans (min_le_right _ _)
    · exact min_le_right _ _
  exact hc.trans (hcut.trans (hbill.trans (by simpa only [ht] using hallow)))

#print axioms four
end Low6966Rectangle

end Merged_R6960Low6966Rectangle

end Merged6967_Low6966Rectangle

section Merged6967_Low6966SharedTallyOld
set_option Elab.async false




set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000
namespace Low6966SharedTallyOld
noncomputable section

open P3 (K)
open K1_13 (Row Shape shape InBox ceilDiv mixed32 chart)
open K1_13_6 (GeoJets toGeneric intersectionIdeal cycleLength)
open K1_13_6_2_4 (oldEmbedding)
open Low6966GeometryCut (CutInput auxCurves32 auxPoints32 membershipDegree)
open Low6966GeometryCut_2 (Branch budget4 budget5)
open Low6966Prices (primaryBox taylorLength physicalPrice physicalPriceOld physicalPriceTilted
  physicalPriceActive surfaceNumerator32 tiltedSurface tiltedSurfaceActive)
open Low6966ActiveCycle (caps caps_chamber caps_active ordinary_doubled active_doubled ordinary_chart
  active_chart ordinary_budget active_budget activeRaw activeFamily old_section_active
  clip_bounds baseClip)
open Low48BentLattice (Chamber)
open Low48BentCycle (rawFamily capFamily mixedDegree)
open Low6966SharedTally (Data)
open scoped BigOperators Polynomial

open Low6966GeometryCut (le_ceil chargedPrice price_formula_old price_formula_tilted price_formula_active)

variable {Γ : Finset K} {s : K→(Polynomial K)} {f Q : Row 4} {l : ℕ} {S : Set (Ideal GeoJets)}

def orderCost (D : Data Γ s f Q l S) (weight : Ideal GeoJets → ℕ) : ℕ :=
  ∑ b∈D.branches, weight b.surface * (b.weight*(D.points b).card)

private theorem eq_surface :
    surfaceNumerator32 (shape f).chamber primaryBox =
      min (budget4 (shape f).chamber) (budget5 (shape f).chamber) := rfl

private theorem four_budget (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (weight : Ideal GeoJets→ℕ)
    (hcut : ∀ b∈D.branches, (weight b.surface : ℕ∞) ≤
      cycleLength (intersectionIdeal f Q) b.surface b.base.isPrime) :
    32*orderCost D weight ≤ budget4 (shape f).chamber := by
  have h := Low6966SharedCycleFour.bound_with_cut K1_13_6_2_3_1.proof
    (K1_13_6_2_3_2.of_children
      K1_13_6_2_3_2_1.proof K1_13_6_2_3_2_2.proof K1_13_6_2_3_2_3.proof
      K1_13_6_2_3_2_4.proof K1_13_6_2_3_2_5.proof K1_13_6_2_3_2_6.proof)
    (K1_13_6_2_3_3.of_children K1_13_6_2_3_3_1.proof
      (K1_13_6_2_3_3_2.of_children K1_13_6_2_3_3_2_1.proof K1_13_6_2_3_3_2_2.proof))
    f Q Q l input.small input.proper primaryBox ⟨by decide,by decide,by decide⟩ input.box weight
    D.branches D.points (D.four input) (fun b hb => ⟨b.base,hcut b hb⟩)
  have hh := (le_div_iff₀ (by norm_num : (0:ℚ)<32)).mp h
  apply (Nat.cast_le (α := ℚ)).mp
  simp only [orderCost,Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat,mul_comm (32:ℚ)]
  simpa only [Nat.cast_mul,budget4] using hh

private theorem legacy_budget (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (weight : Ideal GeoJets→ℕ)
    (hcut : ∀ b∈D.branches, (weight b.surface : ℕ∞) ≤
      cycleLength (intersectionIdeal f Q) b.surface b.base.isPrime) :
    32*orderCost D weight ≤ budget5 (shape f).chamber := by
  have h := Low6966SharedCycleLegacy.bound_with_weights f Q l input.small input.proper input.box
    weight D.branches D.points (D.five input) hcut
  apply (Nat.cast_le (α := ℚ)).mp
  simpa only [orderCost,Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat] using h

private theorem bent_budget (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (weight : Ideal GeoJets→ℕ)
    (hcut : ∀ b∈D.branches, (weight b.surface : ℕ∞) ≤
      cycleLength (intersectionIdeal f Q) b.surface b.base.isPrime)
    (hguard : Low6966Prices.tiltedFits (shape f)) :
    (60*32)*orderCost D weight ≤ tiltedSurface (shape f).chamber primaryBox := by
  let p := (shape f).chamber
  have ht : 1 ≤ p.t := input.small.2.1
  have hC : ∀ i, Chamber (caps p i) :=
    caps_chamber (K1_13_7_1.shape_chamber f).1 ht hguard.1
  have h := Low6966SharedCycleBound.bound_with_cut (R := rawFamily (caps p)) (B := capFamily (caps p)) (ordinary_doubled (p := p)) f Q Q l input.small input.proper weight
    (Low48BentCycle.old_section ⟨le_max_left _ _,le_rfl,le_rfl⟩)
    (Low48BentCycle.old_section input.box)
    D.branches D.points (D.bent input (ordinary_chart ht)) (fun b hb => ⟨b.base,hcut b hb⟩)
  have hh := (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℚ) ≤ 60*32)).trans (ordinary_budget hC)
  apply (Nat.cast_le (α := ℚ)).mp
  simpa only [orderCost,Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat] using hh

private theorem active_charge (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (weight : Ideal GeoJets→ℕ)
    (hcut : ∀ b∈D.branches, (weight b.surface : ℕ∞) ≤
      cycleLength (intersectionIdeal f Q) b.surface b.base.isPrime)
    (K : ℕ) (hK : Low6966Prices.ActiveFits f K) (hQ : Low6966Prices.ActiveFits Q 5164)
    (hguard : Low6966Prices.tiltedFits (shape f))
    (hactive : Low6966Prices.activeFitsPrice (shape f) K) :
    (60*32)*orderCost D weight ≤ tiltedSurfaceActive (shape f).chamber primaryBox K := by
  let p := (shape f).chamber
  have hfits := caps_active hguard hactive
  have hK' : baseClip p K ≤ p.b+p.j-K := (clip_bounds _ _ _).1
  have hsum : K+baseClip p K ≤ p.b+p.j := by
    have hc : 4 ≤ baseClip p K := hactive.2.1
    omega
  have h := Low6966SharedCycleBound.bound_with_cut (active_doubled hfits)
    f Q Q l input.small input.proper weight
    (old_section_active ⟨le_max_left _ _,le_rfl,le_rfl⟩ hK hsum)
    (old_section_active input.box hQ (by decide : 5164+498≤4012+1650))
    D.branches D.points (D.bent input (active_chart hK hactive))
    (fun b hb => ⟨b.base,hcut b hb⟩)
  have hh := (mul_le_mul_of_nonneg_left h (by norm_num : (0:ℚ)≤60*32)).trans
    (active_budget (show 3≤p.t from hactive.1) hfits)
  apply (Nat.cast_le (α := ℚ)).mp
  simpa only [orderCost,Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat] using hh

def auxiliaryCap (x : Shape) : ℕ :=
  ceilDiv (82385*auxCurves32 x + 2*46372*auxPoints32 x) (32*46372)
def continuedCap (x : Shape) : ℕ :=
  ceilDiv ((82385+2*46372)*membershipDegree x) 46372
def surfaceCap (x : Shape) : ℕ :=
  2*(133387*x.b*primaryBox.b)

private theorem charge_le {x : Shape} {l a c d n scale budget O : ℕ}
    (hl : 0<l) (hs : 0<scale)
    (ha : a ≤ auxiliaryCap x) (hc : l*c ≤ continuedCap x)
    (hd : d ≤ surfaceCap x) (hn : l*n≤O) (hO : scale*O≤budget) :
    a+c+d+n ≤ chargedPrice x l scale budget := by
  have H : l*n ≤ ceilDiv budget scale :=
    hn.trans (le_ceil hs (by simpa [Nat.mul_comm] using hO))
  have hmain : c+n ≤ ceilDiv (ceilDiv budget scale+continuedCap x) l := by
    apply le_ceil hl
    rw [Nat.add_mul,Nat.mul_comm c l,Nat.mul_comm n l]
    omega
  unfold chargedPrice auxiliaryCap continuedCap surfaceCap at *
  omega

theorem physical_bound (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (K : ℕ) (hK : Low6966Prices.ActiveFits f K) (hQ : Low6966Prices.ActiveFits Q 5164)
    (weight : Ideal GeoJets→ℕ)
    (hcut : ∀ b∈D.branches, (weight b.surface : ℕ∞) ≤
      cycleLength (intersectionIdeal f Q) b.surface b.base.isPrime)
    {a c d n : ℕ} (ha : a ≤ auxiliaryCap (shape f))
    (hc : l*c ≤ continuedCap (shape f)) (hd : d ≤ surfaceCap (shape f))
    (hn : l*n≤orderCost D weight) : a+c+d+n ≤ physicalPrice (shape f) l K := by
  have hraw : 32*orderCost D weight ≤ surfaceNumerator32 (shape f).chamber primaryBox := by
    rw [eq_surface]
    exact le_min (four_budget D input weight hcut) (legacy_budget D input weight hcut)
  have hold : a+c+d+n ≤ physicalPriceOld (shape f) l := by
    rw [price_formula_old]
    exact charge_le input.positive (by decide) ha hc hd hn hraw
  by_cases ht : Low6966Prices.tiltedFits (shape f)
  · have hbent : a+c+d+n ≤ physicalPriceTilted (shape f) l := by
      rw [price_formula_tilted]
      exact charge_le input.positive (by decide) ha hc hd hn (bent_budget D input weight hcut ht)
    rw [physicalPrice,ite_eq_left ht]
    split_ifs with haa
    · refine le_min (le_min hold hbent) ?_
      rw [price_formula_active]
      exact charge_le input.positive (by decide) ha hc hd hn (active_charge D input weight hcut K hK hQ ht haa)
    · exact le_min hold hbent
  · simpa only [physicalPrice,ite_eq_right ht] using hold

theorem additive_le {x : Shape} {l a c d : ℕ} (hl : 0<l)
    (ha : a≤auxiliaryCap x) (hc : l*c≤continuedCap x) (hd : d≤surfaceCap x) :
    a+c+d ≤ Low6966SharedPrice.additiveBase x l := by
  have hc' : c≤ceilDiv (continuedCap x) l :=
    le_ceil hl (by simpa only [Nat.mul_comm] using hc)
  calc
    a+c+d ≤ auxiliaryCap x+ceilDiv (continuedCap x) l+surfaceCap x :=
      Nat.add_le_add (Nat.add_le_add ha hc') hd
    _ = _ := by
      unfold Low6966SharedPrice.additiveBase auxiliaryCap continuedCap surfaceCap
        auxCurves32 auxPoints32 membershipDegree
      simp only [show Low6966Prices.errors = 82385 by decide, show Low6966Prices.incidenceGap = 46372 by decide, show Low6966Prices.physicalDegree = 133387 by decide,
        Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      omega

#print axioms physical_bound
#print axioms additive_le
end
end Low6966SharedTallyOld

end Merged6967_Low6966SharedTallyOld
