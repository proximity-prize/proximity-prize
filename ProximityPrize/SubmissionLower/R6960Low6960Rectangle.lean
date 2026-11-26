import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.A6966FinalAnchorSpace
import ProximityPrize.SubmissionLower.Final50PriceMass
import ProximityPrize.SubmissionLower.HighCore82258PrefixGeometry
import ProximityPrize.SubmissionLower.R6960ExceptionalStage
import ProximityPrize.SubmissionLower.R6960Front6960Rank4
import ProximityPrize.SubmissionLower.R6960Low6960AllocWeight
import ProximityPrize.SubmissionLower.R6960Low6960RetainedAssembly

section Merged6967_R6960Low6960Rectangle
set_option Elab.async false





set_option Elab.async false

-- merged module R6960Low6960AllocCore
section Merged_R6960Low6960AllocCore

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

namespace Low6960Allocation
open Finset
open K1_13 (Shape InBox)
open K1_13_8 (zeroShape Valid)
open K1_13_8_2 (Threshold orderFor)
open Final50PriceLayer (availableMass fastLayer layerTerm)
open Lower6960.Low (lowDegreeCap)
open Low6960Retained (Box)
open Lower6960.Low (retainedTariff need layerCount)
open Lower6960.Low (degree_bound)
open Final50PriceMass (check check_sum mass_eq)
open P3_6_8_1 (sumBelow)
open scoped BigOperators Classical

abbrev Band := Fin 19
abbrev empty : Band := 0

structure BandData where
  lo : ℕ
  hi : ℕ
  index : ℕ
  top : ℕ
  charge : ℕ

private def bands : List BandData :=
  [
    ⟨0,0,0,0,0⟩,
    ⟨1,1,3,1,1952879554821531⟩,
    ⟨2,2,3,1,1952879554821531⟩,
    ⟨3,3,3,1,1952879554821531⟩,
    ⟨4,4,3,1,2264030333312493⟩,
    ⟨5,5,3,1,2582480582752554⟩,
    ⟨6,14,3,1,6129519605442608⟩,
    ⟨15,26,3,1,14739727222783944⟩,
    ⟨2,17,4,1,16005524698995846⟩,
    ⟨18,24,4,1,24305329798473406⟩,
    ⟨2,21,5,1,35451803568510358⟩,
    ⟨2,17,6,1,40788674056635002⟩,
    ⟨2,11,6,2,95236959055413996⟩,
    ⟨12,17,6,2,145986486282605231⟩,
    ⟨3,12,7,1,39934370655593437⟩,
    ⟨3,10,7,2,136003299584452471⟩,
    ⟨11,12,7,2,160254426018254432⟩,
    ⟨3,4,8,1,37796815539383397⟩,
    ⟨3,4,8,2,159588895902744127⟩
  ]

def band (k : Band) : BandData := bands.get ⟨k.val,k.isLt⟩

def start (k : Band) : Shape := ⟨(band k).lo,(band k).index,(band k).top⟩

def endWidth (k : Band) : ℕ := (band k).hi

def reserve (k : Band) : ℕ := (band k).charge

def Admits (k : Band) (r : Shape) : Prop :=
  (start k).b≤r.b ∧ r.b≤endWidth k ∧ r.j=(start k).j ∧ r.t=(start k).t

instance (k : Band) (r : Shape) : Decidable (Admits k r) := by unfold Admits; infer_instance

theorem start_flat (k : Band) : start k=zeroShape ∨ 0<(start k).j := by
  fin_cases k <;> decide +kernel

theorem empty_admits : Admits empty zeroShape := by decide +kernel

theorem admits_floor {k : Band} {r : Shape} (hr : Admits k r) : InBox (start k) r :=
  ⟨hr.1,hr.2.2.1.symm.le,hr.2.2.2.symm.le⟩

private theorem checked_cover (b : Fin 27) :
    ∀ (j : Fin 9) (t : Fin 3), 1≤t.val → 3*t.val≤j.val → j.val≤3*b.val →
      b.val≤lowDegreeCap j.val → ∃ k : Band, Admits k ⟨b.val,j.val,t.val⟩ := by
  fin_cases b <;> decide +kernel

theorem choose_band (r : Shape) (v : Valid r) (box : Box r) : ∃ k : Band,Admits k r := by
  rcases r with ⟨b,j,t⟩
  have hb : b<27 := Nat.lt_succ_of_le box.1
  have hj : j<9 := Nat.lt_succ_of_le box.2.1
  have ht : t<3 := by have := v.2.1; change 3*t≤j at this; omega
  exact checked_cover ⟨b,hb⟩ ⟨j,hj⟩ ⟨t,ht⟩ v.1 v.2.1 v.2.2 (degree_bound v box)

private theorem checked_reserve (k : Band) :
    ∀ b : Fin 27,(start k).b≤b.val → b.val≤endWidth k →
      retainedTariff b.val (start k).j (start k).t≤reserve k := by
  fin_cases k <;> decide +kernel

theorem admits_fee {k : Band} {r : Shape} (hr : Admits k r) :
    retainedTariff r.b r.j r.t≤reserve k := by
  have hm : endWidth k<27 := by fin_cases k <;> decide +kernel
  rw [hr.2.2.1,hr.2.2.2]
  exact checked_reserve k ⟨r.b,hr.2.1.trans_lt hm⟩ hr.1 hr.2.1

abbrev budget : ℕ := 266228295297579504

def factorCap (top : ℕ) : ℕ := budget-Low6960Prices.lowerCap top

def pricingWeight (k : Band) (b j t : ℕ) : ℕ :=
  if k=empty then Low6960AllocWeight.weight b j t else j

def pricingDenom (k : Band) : ℕ := if k=empty then 364 else 57-(start k).j

def allowance (k : Band) (top b j t : ℕ) : ℕ :=
  (factorCap top-reserve k)*pricingWeight k b j t/pricingDenom k

theorem denom_pos (k : Band) : 0<pricingDenom k := by fin_cases k <;> decide +kernel

theorem reserve_fits (top : ℕ) (ht : top≤14) (k : Band) : reserve k≤factorCap top := by
  interval_cases top <;> fin_cases k <;> decide +kernel

theorem weight_mono (k : Band) {b j t B J T : ℕ} (hb : b≤B) (hj : j≤J) (ht : t≤T) :
    pricingWeight k b j t≤pricingWeight k B J T := by
  by_cases h : k=empty
  · simpa only [pricingWeight,ite_eq_left h] using Low6960AllocWeight.mono hb hj ht
  · simpa only [pricingWeight,ite_eq_right h] using hj

theorem allowance_mono {a b w j t : ℕ} (k : Band) (h : a≤b) (hb : b≤14) :
    allowance k a w j t≤allowance k b w j t := by
  have pos : factorCap a≤factorCap b := by
    have ha := h.trans hb
    interval_cases a <;> interval_cases b <;> decide +kernel
  exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right pos _))

def MassCell (k : Band) :=
  {q : Threshold // 0<q.j ∧ availableMass (start k) ⟨q.b,q.j,0⟩ (q.l-1)<need}

theorem mass_cell (k : Band) (b j l N : ℕ) (hj : 0<j)
    (hN : (l-1)+1650/((start k).j+j)=N) (vals : List ℕ)
    (worked : check (fastLayer (start k) ⟨b,j,0⟩ (l-1)) 0 N vals=true)
    (small : vals.sum<need) :
    0<(⟨b,j,l⟩ : Threshold).j ∧
      availableMass (start k) ⟨b,j,0⟩ (l-1)<need := by
  refine ⟨hj,?_⟩
  rw [mass_eq _ _ _ (start_flat k) (by change 0<(start k).j+j; omega),hN]
  have sum := check_sum (fastLayer (start k) ⟨b,j,0⟩ (l-1)) 0 N vals worked
  have eq : P3_6_8_1.sumBelow (fastLayer (start k) ⟨b,j,0⟩ (l-1)) N=vals.sum := by
    simpa only [Nat.zero_add,P3_6_8_1.sumBelow] using sum
  rwa [eq]

def order {k : Band} (cells : List (MassCell k)) (x : Shape) : ℕ :=
  orderFor x.b x.j (cells.map Subtype.val)

theorem order_pos {k : Band} (cells : List (MassCell k)) (x : Shape) : 0<order cells x :=
  (P0_9_8.orderFor_select x.b x.j (cells.map Subtype.val)).1

theorem order_mono {k : Band} (cells : List (MassCell k)) {x y : Shape}
    (hb : x.b≤y.b) (hj : x.j≤y.j) : order cells x≤order cells y :=
  P0_9_8.orderFor_mono hb hj _

theorem order_valid {k : Band} (cells : List (MassCell k)) (x : Shape) : order cells x=1 ∨
    availableMass (start k) x (order cells x-1)<need := by
  rcases (P0_9_8.orderFor_select x.b x.j (cells.map Subtype.val)).2 with h | ⟨q,hq,hb,hj,eq⟩
  · exact Or.inl h
  · obtain ⟨c,_,rfl⟩ := List.mem_map.mp hq
    refine Or.inr ?_
    change order cells x=c.val.l at eq
    rw [eq]
    have pos : 0<(start k).j+c.val.j := by have := c.property.1; omega
    exact (Final50PriceLayer.availableMass_anti_prefix (y:=⟨c.val.b,c.val.j,0⟩)
      (start_flat k) pos hb hj).trans_lt c.property.2

theorem layer_le_available {r y : Shape} {L : ℕ}
    (hr : r=zeroShape ∨ 0<r.j) (hj : 0<r.j+y.j) :
    (∑ k∈range layerCount,layerTerm r y L k)≤availableMass r y L := by
  apply le_trans _ (Final50PriceLayer.layerSum_le_available hr hj)
  exact sum_le_sum_of_subset (range_mono (by decide +kernel))

#print axioms choose_band
#print axioms order_valid

end Low6960Allocation

end
end Merged_R6960Low6960AllocCore

-- merged module R6960Low6960Rectangle
section Merged_R6960Low6960Rectangle

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
    ∃ l, 0 < l ∧ l ≤ order cells a ∧ contractedPrice a (start k) l 169 ≤
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
  have hc : contractedPrice a (start k) l 169 ≤ cutPrice a l 32 (fourSurface a.chamber (hullOf k l)) := by
    unfold contractedPrice
    dsimp only
    rw [if_pos hq]
    split
    · exact (min_le_left _ _).trans (min_le_right _ _)
    · exact min_le_right _ _
  exact hc.trans (hcut.trans (hbill.trans (by simpa only [ht] using hallow)))

#print axioms four
end Low6960Rectangle

end Merged_R6960Low6960Rectangle

end Merged6967_R6960Low6960Rectangle

section Merged6967_R6960Low6960SharedTallyOld
set_option Elab.async false




set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000
namespace Low6960SharedTallyOld
noncomputable section

open P3 (K)
open K1_13 (Row Shape shape InBox ceilDiv mixed32 chart)
open K1_13_6 (GeoJets toGeneric intersectionIdeal cycleLength)
open K1_13_6_2_4 (oldEmbedding)
open Low6960GeometryCut (CutInput auxCurves32 auxPoints32 membershipDegree)
open Low6960GeometryCut_2 (Branch budget4 budget5)
open Low6960Prices (primaryBox taylorLength physicalPrice physicalPriceOld physicalPriceTilted
  physicalPriceActive surfaceNumerator32 tiltedSurface tiltedSurfaceActive)
open Low6960ActiveCycle (caps caps_chamber caps_active ordinary_doubled active_doubled ordinary_chart
  active_chart ordinary_budget active_budget activeRaw activeFamily old_section_active
  clip_bounds baseClip)
open Low48BentLattice (Chamber)
open Low48BentCycle (rawFamily capFamily mixedDegree)
open Low6960SharedTally (Data)
open scoped BigOperators Polynomial

open Low6960GeometryCut (le_ceil chargedPrice price_formula_old price_formula_tilted price_formula_active)

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
  have h := Low6960SharedCycleFour.bound_with_cut K1_13_6_2_3_1.proof
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
  have h := Low6960SharedCycleLegacy.bound_with_weights f Q l input.small input.proper input.box
    weight D.branches D.points (D.five input) hcut
  apply (Nat.cast_le (α := ℚ)).mp
  simpa only [orderCost,Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat] using h

private theorem bent_budget (D : Data Γ s f Q l S) (input : CutInput Γ s f Q l)
    (weight : Ideal GeoJets→ℕ)
    (hcut : ∀ b∈D.branches, (weight b.surface : ℕ∞) ≤
      cycleLength (intersectionIdeal f Q) b.surface b.base.isPrime)
    (hguard : Low6960Prices.tiltedFits (shape f)) :
    (60*32)*orderCost D weight ≤ tiltedSurface (shape f).chamber primaryBox := by
  let p := (shape f).chamber
  have ht : 1 ≤ p.t := input.small.2.1
  have hC : ∀ i, Chamber (caps p i) :=
    caps_chamber (K1_13_7_1.shape_chamber f).1 ht hguard.1
  have h := Low6960SharedCycleBound.bound_with_cut (R := rawFamily (caps p)) (B := capFamily (caps p)) (ordinary_doubled (p := p)) f Q Q l input.small input.proper weight
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
    (K : ℕ) (hK : Low6960Prices.ActiveFits f K) (hQ : Low6960Prices.ActiveFits Q 5164)
    (hguard : Low6960Prices.tiltedFits (shape f))
    (hactive : Low6960Prices.activeFitsPrice (shape f) K) :
    (60*32)*orderCost D weight ≤ tiltedSurfaceActive (shape f).chamber primaryBox K := by
  let p := (shape f).chamber
  have hfits := caps_active hguard hactive
  have hK' : baseClip p K ≤ p.b+p.j-K := (clip_bounds _ _ _).1
  have hsum : K+baseClip p K ≤ p.b+p.j := by
    have hc : 4 ≤ baseClip p K := hactive.2.1
    omega
  have h := Low6960SharedCycleBound.bound_with_cut (active_doubled hfits)
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
  ceilDiv (82326*auxCurves32 x + 2*46389*auxPoints32 x) (32*46389)
def continuedCap (x : Shape) : ℕ :=
  ceilDiv ((82326+2*46389)*membershipDegree x) 46389
def surfaceCap (x : Shape) : ℕ :=
  2*(133429*x.b*primaryBox.b)

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
    (K : ℕ) (hK : Low6960Prices.ActiveFits f K) (hQ : Low6960Prices.ActiveFits Q 5164)
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
  by_cases ht : Low6960Prices.tiltedFits (shape f)
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
    a+c+d ≤ Low6960SharedPrice.additiveBase x l := by
  have hc' : c≤ceilDiv (continuedCap x) l :=
    le_ceil hl (by simpa only [Nat.mul_comm] using hc)
  calc
    a+c+d ≤ auxiliaryCap x+ceilDiv (continuedCap x) l+surfaceCap x :=
      Nat.add_le_add (Nat.add_le_add ha hc') hd
    _ = _ := by
      unfold Low6960SharedPrice.additiveBase auxiliaryCap continuedCap surfaceCap
        auxCurves32 auxPoints32 membershipDegree
      simp only [show Low6960Prices.errors = 82326 by decide, show Low6960Prices.incidenceGap = 46389 by decide, show Low6960Prices.physicalDegree = 133429 by decide,
        Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      omega

#print axioms physical_bound
#print axioms additive_le
end
end Low6960SharedTallyOld

end Merged6967_R6960Low6960SharedTallyOld

section Merged6967_R6960RescueGeometryInvoice
set_option Elab.async false



set_option Elab.async false

-- merged module R6960RescueGeometryRates
section Merged_R6960RescueGeometryRates

-- merged module R6960RescueGeometryTariffs
section Merged_R6960RescueGeometryTariffs

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.RescueGeometry
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

private abbrev agreement : ℕ := 179818
private abbrev blockLength : ℕ := 262144
abbrev endpointDegree : ℕ := 164650

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
private theorem rho_at_endpoint {d : ℕ} (hl : 131071 ≤ d) (hh : d ≤ 164650) :
    rho d ≤ density * d := by
  have hdA : d < agreement := hh.trans_lt (by decide)
  have hdN : d ≤ blockLength := hh.trans (by decide)
  have hrho : rho d ≤ 17 := by
    unfold rho
    have hp : (0 : ℚ) < ((agreement - d : ℕ) : ℚ) := by exact_mod_cast Nat.sub_pos_of_lt hdA
    apply (div_le_iff₀ hp).mpr
    rw [Nat.cast_sub hdN, Nat.cast_sub hdA.le]
    change (262144 : ℚ) - d ≤ 17 * ((179818 : ℚ) - d)
    have hQ : (d : ℚ) ≤ 164650 := by exact_mod_cast hh
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
    (hg : 0 < g) (hl : 131071 ≤ d) (hh : d ≤ 164650) :
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
    (hi : M.overhead.toNat≤33579) {T : Finset K} (hT : T⊆Γ) :
    FixedWord M.word T F.scalar endpointDegree where
  distinct := F.distinct.mono hT
  degree := by
    intro γ hγ
    rcases (F.mark γ (hT hγ)).scalar_degree with zero | bound
    · simp [zero]
    · change ((F.scalar γ).natDegree : ℤ)≤131071+M.overhead at bound
      change (F.scalar γ).natDegree≤164650
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
    (hi : M.overhead.toNat≤33579) : CurveTariff F := by
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
private theorem caps_weighted {d m B J : ℕ} (hl : 131071 ≤ d) (hh : d ≤ 164650)
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
    (hl : 131071 ≤ d) (hh : d ≤ 164650) (hJ : 0 < J)
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
    (hi : M.overhead.toNat≤33579) {B J : ℕ} (guard : ODEGuard B J)
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

end Lower6960.RescueGeometry

end
end Merged_R6960RescueGeometryTariffs

-- merged module R6960RescueGeometryRates
section Merged_R6960RescueGeometryRates

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.RescueGeometry
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
end Lower6960.RescueGeometry

end
end Merged_R6960RescueGeometryRates

end Merged_R6960RescueGeometryRates

-- merged module R6960RescueGeometryInvoice
section Merged_R6960RescueGeometryInvoice

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.RescueGeometry
open Finset
open K1 (p)
open P1_7_4 (Mass dotQ weightedBill)
open scoped Classical BigOperators

def degreeRates : List (List ℕ) :=
  [
    [185818626, 110433204, 89307106, 80981569, 73536324, 70050751, 70333505, 78862332, 51474031, 80824946, 107178122, 90561210, 111399090, 159856701, 155401324, 198768055, 138542104],
    [179378044, 106432694, 85817332, 77706467, 70695292, 67465905, 67744230, 75883229, 49483667, 77575308, 102814332, 87000554, 107157326, 154005122, 149641067, 191596945, 137489413],
    [181733058, 104811364, 80618367, 70841205, 66177076, 65013899, 65389313, 72436304, 46324207, 72672132, 97959228, 82217852, 103210618, 149781012, 144393038, 187541220, 147843055],
    [136033029, 79972168, 61971094, 58419873, 63658503, 67045494, 68100572, 73833280, 44860002, 62051252, 75841228, 71158176, 98079150, 149905130, 145594273, 194227079, 257834722]
  ]

def heightRates : List (List ℕ) :=
  [
    [2517532, 4393752, 5487930, 6071739, 6714662, 7056278, 7028566, 6245329, 9697201, 6083207, 4533097, 5409943, 4352404, 2963299, 3054648, 2324970, 3455218],
    [2613306, 4565008, 5717640, 6343770, 6993108, 7342509, 7311406, 6499049, 10095772, 6354940, 4730274, 5631363, 4533987, 3083274, 3172750, 2431607, 3483679],
    [2578286, 4634414, 6098334, 6978807, 7486539, 7624528, 7577076, 6822473, 10800400, 6799360, 4982963, 5981212, 4709649, 3169881, 3297026, 2491917, 3209615],
    [3523055, 6150809, 8009131, 8509917, 7795846, 7389491, 7271584, 6685557, 11161993, 7998999, 6502626, 6947741, 4976721, 3167336, 3264549, 2392496, 1733875]
  ]

def degreeRate (rect : Fin 4) (i : ℕ) : ℕ := (degreeRates.getD rect.val []).getD i 0

def heightRate (rect : Fin 4) (i : ℕ) : ℕ := (heightRates.getD rect.val []).getD i 0

private def heightTerms (a : ℕ) : List ℚ :=
  (List.range 80).map (fun i : ℕ =>
    let g := i+1
    max 0 (1-(a : ℚ)*(g : ℚ)/((p+1 : ℕ) : ℚ))*curveUnit g)

def heightBound (a : ℕ) : ℚ := (heightTerms a).foldr max 0

private theorem le_max_fold {q : ℚ} {terms : List ℚ} (mem : q∈terms) :
    q ≤ terms.foldr max 0 := by
  induction terms with
  | nil => simp at mem
  | cons a rest ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp mem with eq | h
    · exact eq.symm ▸ le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem height_spec (a g : ℕ) (pos : 0<g) (small : g≤80) :
    max 0 (1-(a : ℚ)*g/((p+1 : ℕ) : ℚ))*curveUnit g≤heightBound a := by
  apply le_max_fold
  unfold heightTerms
  apply List.mem_map.mpr
  refine ⟨g-1,List.mem_range.mpr (by omega),?_⟩
  dsimp only
  rw [Nat.sub_add_cancel (by omega : 1≤g)]

private theorem checked_rates (rect : Fin 4) (i : Fin 17) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate rect i.val : ℚ) ∧
    min (seedLimit rect) (dotQ (cutWeight rect 0 i.val) (history rect i.val)) ≤ (degreeRate rect i.val : ℚ) ∧
    heightBound (degreeRate rect i.val) ≤ (heightRate rect i.val : ℚ) := by
  fin_cases rect <;> fin_cases i <;> decide +kernel

theorem rate_spec (rect : Fin 4) {i : ℕ} (hi : i<17) :
    RateOK (degreeRate rect i) (heightRate rect i) ∧
      min (seedLimit rect) (dotQ (cutWeight rect 0 i) (history rect i)) ≤ degreeRate rect i := by
  obtain ⟨base,degree,height⟩ := checked_rates rect ⟨i,hi⟩
  exact ⟨⟨base,Nat.cast_nonneg _,fun g hp hg=>(height_spec _ g hp hg).trans height⟩,degree⟩

def lambda : ℚ := ((262144 : ℚ)/179818)*endpointDegree

def mu : ℚ := ((262144-endpointDegree : ℕ) : ℚ)/(179818-endpointDegree : ℕ)

def rankB (rect : Fin 4) : ℕ := initialCap rect 2+2

def rankJ (rect : Fin 4) : ℕ := initialCap rect 1+1

def tau : ℚ := 49/100

def pivot (rect : Fin 4) : ℚ := min (47843/5) (tau*rankB rect)

def rankWeight (rect : Fin 4) : Mass :=
  ![0,4*lambda*rankB rect*tau+mu-4*lambda*pivot rect,
    4*lambda*rankJ rect*(1-tau)+rankB rect,0]

def rankRound (rect : Fin 4) : ℚ :=
  rankWeight rect 1+2*rankWeight rect 2+2*lambda*pivot rect^2+1

def lossWeight (rect : Fin 4) (i : ℕ) : Mass :=
  fun k=>(degreeRate rect i : ℚ)*cutWeight rect 0 i k+(heightRate rect i : ℚ)*cutWeight rect 1 i k

def lossLimit (rect : Fin 4) : ℚ :=
  weightedBill 18 (beforeCuts (rankWeight rect) (lossWeight rect))
    (beforeCuts (initialMass rect) (history rect))+seedLimit rect+rankRound rect

def rescueFee (rect : Fin 4) : ℕ :=
  (lossLimit rect).ceil.toNat+(pointLimit rect).ceil.toNat+initialSeedLimit rect+initialCap rect 0

theorem rescue_fee_bound (rect : Fin 4) : rescueFee rect ≤ 118460744183568976 := by
  fin_cases rect <;> decide +kernel

theorem strict_rescue_fee (rect : Fin 4) : rescueFee rect < 118687375614631597 :=
  (rescue_fee_bound rect).trans_lt (by decide)

theorem rank_guard (rect : Fin 4) :
    rankB rect < p ∧ 0≤rankWeight rect 1 ∧ 0≤rankWeight rect 2 := by
  fin_cases rect <;> decide +kernel

#print axioms rate_spec
#print axioms strict_rescue_fee

end Lower6960.RescueGeometry

end
end Merged_R6960RescueGeometryInvoice

end Merged6967_R6960RescueGeometryInvoice

section Merged6967_R6966ProofPadeCutoff
set_option Elab.async false


set_option Elab.async false

namespace Research6966.PadeCutoff
open Polynomial Finset Module
open K1_14 (Shape Jet L FX shapeSum)
open K1_14_1 (PoleData CRTLift)
open K1_14_3 (Surface Parent ProjectedProduct SeedClosure)
open KoalaRect (area rectCapacity rectDebit rectPower)
open scoped Polynomial
noncomputable section

/-- At each physical weight the bank obeys both the old ordinate-only
capacity and the independent graph restriction. -/
def capacity (A h e a n:ℕ) (s:Shape) (U:Fin 2→ℕ) (W:ℕ) : ℕ :=
  let step:=131071-h
  let k:=rectPower A h s W
  let b:=min s.B ((s.m*A-2*h*k)/step)
  let gain:=PadeRank.gain a n k (b+1) (s.J+1)
  min (rectCapacity A h s e U (fun _=>0) W)
    (((PadeFiltered.physicalWindow s.B s.J step W).card-gain)*area U)

/-- A strict inequality here is sufficient to exclude a graph of degree
a through n actual sheets. Every term is a natural-number expression. -/
def excluded (A h e a n:ℕ) (s:Shape) (U:Fin 2→ℕ) (nodes moment:ℕ) : Prop :=
  rectDebit h nodes moment U + ∑ W∈range (s.m*A),capacity A h e a n s U W <
    area U * shapeSum s (fun q j=>s.m*A+j-q*(131071-h))

theorem not_excluded {h A e:ℕ} (hp:0<h) (hl:h≤131070) (hc:h<K1.p) {D:PoleData h}
    (Crt:CRTLift D) (word:K1.I→L) {s envelope:Shape} (U:Fin 2→ℕ)
    (fits:TerminalBanks.inside s envelope) (top:0<s.m*A) (small:s.m*A<K1.p)
    (hbox:U 0+U 1≤s.U) (bs:s.B<K1.p) (width:s.B*(131071-h)≤s.m*A)
    {nodes moment:ℕ} (nodeCap:P1_7_1.nodeRows s≤nodes) (poleCap:P1_7_1.groupedPoleMoment s.B s.J≤moment)
    {parents:Finset Surface} (geo:∀ q∈parents,Parent q)
    (pass:∀ q∈parents,TerminalBanks.Pass Crt word A envelope q)
    {f:K1_14.Equation} (prod:ProjectedProduct parents f) (ep:0<e) (deg:e≤f.natDegree)
    (ys:Finset SeedClosure) (v:SeedClosure→SeedClosure) {G:Pade.Row SeedClosure} (gp:G.primitive)
    (sheets:∀ y∈ys,(∃ q∈parents,K1_14_3.OnSeedFibre q y (v y)) ∧ G.err v y=0) :
    ¬excluded A h e G.graphDegree ys.card s U nodes moment := by
  classical
  let N:=s.m*A
  have recover:N-1+1=N:=by dsimp [N];omega
  have shapeWidth:K1_14_1.rawWidthCond h s (N-1) := by
    intro q hq j _
    rw [recover]
    exact (Nat.mul_le_mul_right _ hq).trans (width.trans (by dsimp [N];omega))
  have floor:=KoalaRect.rectRankFloor hp hl hc Crt word s (N-1) U hbox bs shapeWidth nodeCap poleCap
  rw [recover] at floor
  have bounds (W:ℕ) (win:W∈range N) :
      finrank FX (KoalaRect.rectEvaluated Crt word s W U) ≤ capacity A h e G.graphDegree ys.card s U W := by
    have inside:W<s.m*A:=mem_range.mp win
    let r:=(s.m*A-1-W)/(2*h)
    have rd:r* (2*h)≤s.m*A-1-W:=Nat.div_mul_le_self _ _
    have psmall:r+1<K1.p:=by
      have le:r≤s.m*A-1-W:=Nat.div_le_self _ _
      omega
    have enough:W+2*h*r<s.m*A:=by rw [Nat.mul_comm (2*h) r];omega
    let low:=s.m*A-2*h*(1+r)
    have low_le:low≤W := by
      have split:=Nat.mod_add_div (s.m*A-1-W) (2*h)
      have rem:=Nat.mod_lt (s.m*A-1-W) (by omega : 0<2*h)
      change (s.m*A-1-W)%(2*h)+2*h*r=s.m*A-1-W at split
      dsimp only [low]
      rw [Nat.mul_add,Nat.mul_one]
      omega
    let b:=min s.B (low/(131071-h))
    have bw:(131071-h)*b≤W := by
      rw [Nat.mul_comm]
      exact (Nat.mul_le_mul_right _ (min_le_right ..)).trans ((Nat.div_mul_le_self low _).trans low_le)
    have rank:=PadeFiltered.graph_rank hp hl Crt word U fits psmall enough (min_le_left ..) bw
      geo pass ys v gp sheets
    apply le_min
    · apply KoalaRect.rectCutoff_finrank_le _ _ _ _ _ _ _ _ prod.primitive.ne_zero deg (by omega) ep
      · intro P hP;exact K1_14_1.evaluated_shape Crt word (KoalaRect.rectEvaluated_le Crt word s W U hP)
      · intro P hP;exact KoalaRect.rectEvaluated_axis Crt word hP
      · intro P hP hn;exact P0_10_1.leading_bound hp hl Crt word s W P (KoalaRect.rectEvaluated_le Crt word s W U hP) hn
      · intro P hP hn
        exact KoalaRect.rectDivides hp Crt word A s U small geo (fun q hq=>pass q hq s fits) prod inside hP hn
      · intro z
        simpa [KoalaRect.rectSlots,KoalaRect.area] using
          KoalaRect.rectSlots_antitone U (KoalaRect.axisDegree f) (Nat.zero_le z)
    · change _≤((PadeFiltered.physicalWindow s.B s.J (131071-h) W).card-
        PadeRank.gain G.graphDegree ys.card (1+r) (b+1) (s.J+1))*area U
      rw [Nat.sub_mul,Nat.add_comm 1 r]
      exact Nat.le_sub_of_add_le rank
  have sum:=Finset.sum_le_sum (s:=range N) bounds
  unfold excluded
  exact Nat.not_lt_of_ge (floor.trans (Nat.add_le_add_left sum _))

#print axioms not_excluded

/-- Exhaustive graph classification for the production parents. Both receipt
families are tested at their minimum number of distinct ordinates. -/
theorem counted_packet {h A e c amax:ℕ} (hp:0<h) (hl:h≤131070) (hc:h<K1.p) {D:PoleData h}
    (Crt:CRTLift D) (word:K1.I→L) {s envelope:Shape} (U:Fin 2→ℕ)
    (fits:TerminalBanks.inside s envelope) (top:0<s.m*A) (small:s.m*A<K1.p)
    (hbox:U 0+U 1≤s.U) (bs:s.B<K1.p) (width:s.B*(131071-h)≤s.m*A)
    {nodes moment:ℕ} (nodeCap:P1_7_1.nodeRows s≤nodes) (poleCap:P1_7_1.groupedPoleMoment s.B s.J≤moment)
    (parents:Finset Surface) (nonempty:parents.Nonempty) (geo:∀ q∈parents,Parent q)
    (pass:∀ q∈parents,TerminalBanks.Pass Crt word A envelope q) (large:2≤e) (gap:2*c<e)
    (partialPrice:∀ a,amax<a → a≤c → excluded A h e a (e-c+a) s U nodes moment)
    (full:∀ a,e+1-(e+1)/2≤a → a≤e-c → excluded A h e a e s U nodes moment) :
    ∃ f:K1_14.Equation, ProjectedProduct parents f ∧
      (f.natDegree<e ∨ ∃ G:Pade.Row K1_14_3.SeedField,G.primitive ∧
        G.graphDegree≤amax ∧ Pade.Controls (G.map (algebraMap _ Pade.Native.Sep))
          (Pade.Native.sheets parents) c) := by
  classical
  obtain ⟨f,pf,alts⟩:=Pade.Native.packet_cases parents nonempty geo e c amax large gap
  refine ⟨f,pf,?_⟩
  by_cases low:f.natDegree<e
  · exact Or.inl low
  rcases alts with tooSmall|spread|graph
  · exact False.elim (low tooSmall)
  · obtain ⟨G,S,v,gp,onSheet,kind⟩:=spread
    have take : ∃ n,n≤S.card ∧ excluded A h e G.graphDegree n s U nodes moment := by
      rcases kind with ⟨lo,hi,count⟩|⟨lo,hi,count⟩
      · exact ⟨_,count,partialPrice _ lo hi⟩
      · exact ⟨_,count,full _ lo hi⟩
    obtain ⟨n,le,price⟩:=take
    obtain ⟨T,sub,size⟩:=exists_subset_card_eq le
    let emb:Pade.Native.Sep→+*SeedClosure:=(separableClosure K1_14_3.SeedField SeedClosure).val.toRingHom
    let pts:=T.image emb
    let slope (z:SeedClosure):=if H:∃ y∈T,emb y=z then emb (v H.choose) else 0
    have atPoint (y) (hy:y∈T) : slope (emb y)=emb (v y) := by
      have H:∃ z∈T,emb z=emb y:=⟨y,hy,rfl⟩
      simp only [slope,dite_eq_left H,emb.injective H.choose_spec.2]
    have kept:pts.card=n:=(card_image_of_injective _ emb.injective).trans size
    have prohibited:=not_excluded hp hl hc Crt word U fits top small hbox bs width nodeCap poleCap
      geo pass pf (by omega : 0<e) (by omega : e≤f.natDegree) pts slope ((G.primitive_map emb).mpr gp) (by
        intro y hy
        obtain ⟨z,hz,rfl⟩:=mem_image.mp hy
        rw [atPoint z hz]
        obtain ⟨sheet,hit⟩:=onSheet z (sub hz)
        refine ⟨(Pade.Native.sheets_iff ..).mp sheet,?_⟩
        change (G.a.map emb).eval (emb z)*slope (emb z)-(G.b.map emb).eval (emb z)=0
        rw [atPoint z hz]
        simpa only [Pade.Row.err,map_sub,map_mul,eval_map_apply,map_zero] using congrArg emb hit)
    exact False.elim (prohibited (by rwa [Pade.Row.degree_map,kept]))
  · exact Or.inr graph

#print axioms counted_packet
end
end Research6966.PadeCutoff

end Merged6967_R6966ProofPadeCutoff

section Merged6967_R6966ProofPadeRawField
set_option Elab.async false



set_option Elab.async false

namespace Research6966.PadeRawField
open Polynomial Finset Module
open K1_14 (L FX Seeds)
open K1_14_1 (SeedPoly Source RawSource centerEval jetConstant genericCoefficients)
open K1_14_1_4 (doubleMap centerBase evalRaw)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false

/-- Centering sends X to a transcendental and keeps the two seed
indeterminates. A vanishing image kills each physical coefficient. -/
theorem center_injective : Function.Injective centerBase := by
  apply (injective_iff_map_eq_zero centerBase).mpr
  intro g zero
  have z:centerEval (jetConstant g)=0 := by
    rw [K1_14_1_4.centerEval_apply]
    simp only [jetConstant,doubleMap,coe_mapRingHom,Polynomial.map_C,RingHom.comp_apply,zero,Polynomial.C_0]
  apply Polynomial.ext
  intro n
  apply MvPolynomial.ext
  intro e
  have co:=K1_14_1_8.coords_center (jetConstant g) (0,0,e)
  rw [z,map_zero] at co
  change 0=algebraMap L[X] FX (K1_14_1_8.sourceCoord (jetConstant g) (0,0,e)) at co
  have pzero : K1_14_1_8.sourceCoord (jetConstant g) (0,0,e)=0 :=
    (IsFractionRing.injective L[X] FX) (co.symm.trans (map_zero _).symm)
  have ns : ((((jetConstant g).coeff 0).coeff 0).coeff n).coeff e=0 :=
    (congrArg (fun q:L[X]=>q.coeff n) pzero).trans (coeff_zero n)
  change (g.coeff n).coeff e=0
  simpa only [jetConstant,RingHom.comp_apply,coeff_C_zero] using ns

/-- Injectivity on k(Z)[X] after moving X into the physical fraction field.
One common polynomial in the seeds reduces the assertion to the integral
source, for which all native coefficient positions remain visible. -/
theorem eval_injective : Function.Injective evalRaw := by
  apply (injective_iff_map_eq_zero evalRaw).mpr
  intro P zero
  let D:=IsLocalization.integerNormalization (nonZeroDivisors SeedPoly) P
  obtain ⟨b,hb,scaled⟩:=IsLocalization.integerNormalization_spec (nonZeroDivisors SeedPoly) P
  have eq:genericCoefficients D = C (algebraMap SeedPoly K1_14_1.SeedField b)*P := by
    change D.map (algebraMap SeedPoly K1_14_1.SeedField) = _
    simpa only [Algebra.smul_def,Polynomial.algebraMap_apply] using scaled
  have vanish:=RingHom.congr_fun K1_14_1_4.evalRaw_generic D
  change evalRaw (genericCoefficients D)=algebraMap Seeds (FractionRing Seeds) (centerBase D) at vanish
  rw [eq,map_mul,zero,mul_zero] at vanish
  have cent:centerBase D=0 := (IsFractionRing.injective Seeds (FractionRing Seeds))
    (vanish.symm.trans (map_zero _).symm)
  have dz:D=0 := center_injective (cent.trans (map_zero _).symm)
  exact (IsFractionRing.integerNormalization_eq_zero_iff (A:=SeedPoly) (p:=P)).mp dz

private abbrev k := K1_14_1.SeedField
private abbrev E := K1_14_3.SeedClosure

/-- Descend divisibility from any field extension through two polynomial
coordinates. Primitivity here is in the slope, over the full coefficient
UFD k[X,Y], so the quotient is integral also in physical X. -/
theorem primitive_divides {R F:Type*} [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]
    [Field F] (f:R→+*F) (inj:Function.Injective f) {G Q:R[X]} (primitive:G.IsPrimitive)
    (dv:G.map f ∣ Q.map f) : G∣Q := by
  let Rf:=FractionRing R
  let emb:Rf→+*F:=IsFractionRing.lift inj
  have factor:emb.comp (algebraMap R Rf)=f:=by ext x;simp [emb]
  apply primitive.dvd_of_fraction_map_dvd_fraction_map (K:=Rf)
  apply (Polynomial.map_dvd_map' emb).mp
  simpa only [Polynomial.map_map,factor] using dv

def rawField : k[X]→+*E := (algebraMap K1_14_3.SeedField E).comp evalRaw

theorem integral_power {R K:Type*} [CommRing R] [IsDomain R] [Field K] [UniqueFactorizationMonoid R[X]]
    (g:R→+*K) (inject:Function.Injective g) {G Q:R[X][X]} (gp:G.IsPrimitive) (t:ℕ)
    (dv:doubleMap g G^t ∣ doubleMap g Q) : G^t ∣ Q := by
  let F:=FractionRing K[X]
  let f:R[X]→+*F:=(algebraMap K[X] F).comp (mapRingHom g)
  have inj:Function.Injective f:=(IsFractionRing.injective K[X] F).comp (map_injective g inject)
  let := UniqueFactorizationMonoid.strongNormalizationMonoid (α:=R[X])
  let := UniqueFactorizationMonoid.toNormalizedGCDMonoid R[X]
  have prim:(G^t).IsPrimitive:=by
    clear dv
    induction t with
    | zero=>simp
    | succ t ih=>rw [pow_succ];exact ih.mul gp
  apply primitive_divides f inj prim
  obtain ⟨S,eq⟩:=dv
  refine ⟨S.map (algebraMap K[X] F),?_⟩
  have eq':=congrArg (fun p:K[X][X]=>p.map (algebraMap K[X] F)) eq
  simpa only [doubleMap,coe_mapRingHom,Polynomial.map_map,Polynomial.map_mul,Polynomial.map_pow] using eq'

theorem raw_divides {G Q:RawSource} (gp:G.IsPrimitive) (t:ℕ)
    (dv:doubleMap rawField G^t ∣ doubleMap rawField Q) : G^t ∣ Q :=
  integral_power rawField ((algebraMap K1_14_3.SeedField E).injective.comp eval_injective) gp t dv

/-- The normalized raw source pays t physical graph weights as soon as the
field-valued graph power is forced. The quotient is produced integrally. -/
theorem quotient_of_fibre_power {h:ℕ} (hp:0<h) (hl:h≤131070) {D:K1_14_1.PoleData h}
    (Crt:K1_14_1.CRTLift D) (word:K1.I→L) {s W P} (mem:P∈K1_14_1.complete Crt word s W)
    {G:RawSource} (gp:G.IsPrimitive) (t:ℕ)
    (dv:doubleMap rawField G^t ∣ doubleMap (algebraMap K1_14_3.SeedField E)
      (K1_14_1_4.specialized Crt (centerEval P))) :
    ∃ Q:RawSource, K1_14_1.forward Crt P=jetConstant ((K1_14_1.rawBlock D)^(s.B+s.J))*(G^t*Q) ∧
      K1_14_1_4.Bounded (131071-h) (131071-h-1) (W-t*RawPhysicalDegree.weight (131071-h) (131071-h-1) G) Q := by
  obtain ⟨S,eq,_⟩:=P0_10_1.complete_raw_bounded hp hl Crt word mem
  have compose (P:RawSource):doubleMap (algebraMap K1_14_3.SeedField E) (doubleMap evalRaw P)=
    doubleMap rawField P := by
      ext j i
      simp only [doubleMap,coe_mapRingHom,Polynomial.coeff_map,rawField,RingHom.comp_apply]
  rw [K1_14_1_4.specialized_center,compose,eq,map_mul] at dv
  let c:=rawField ((K1_14_1.rawBlock D)^(s.B+s.J))
  have nz:c≠0:=(map_ne_zero_iff rawField ((algebraMap K1_14_3.SeedField E).injective.comp eval_injective)).mpr
    (pow_ne_zero _ (K1_14_1_4.rawBlock_monic D).ne_zero)
  have unitC:IsUnit (jetConstant c : E[X][X]) := isUnit_C.mpr (isUnit_C.mpr nz.isUnit)
  have tr:doubleMap rawField (jetConstant ((K1_14_1.rawBlock D)^(s.B+s.J)))=jetConstant c := by
    simp only [jetConstant,doubleMap,RingHom.comp_apply,coe_mapRingHom,Polynomial.map_C];rfl
  rw [tr] at dv
  have divides:=raw_divides gp t ((associated_unit_mul_left _ _ unitC).dvd_iff_dvd_right.mp dv)
  obtain ⟨Q,id⟩:=divides
  exact ⟨Q,eq.trans (congrArg (_ * ·) id),RawPhysicalDegree.complete_graph_quotient hp hl Crt word mem G Q t
    gp.ne_zero (eq.trans (congrArg (_ * ·) id))⟩

#print axioms eval_injective
#print axioms raw_divides
#print axioms quotient_of_fibre_power
end
end Research6966.PadeRawField

end Merged6967_R6966ProofPadeRawField
