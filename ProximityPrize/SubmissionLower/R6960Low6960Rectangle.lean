import ProximityPrize.SubmissionLower.R6960Low6960Monotone
import ProximityPrize.SubmissionLower.R6960Low6960RetainedAssembly
import ProximityPrize.SubmissionLower.R6960Low6960AllocWeight
import ProximityPrize.SubmissionLower.Final50PriceMass

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

abbrev Band := Fin 24
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
    ⟨1,1,3,1,2082656172124625⟩,
    ⟨2,2,3,1,2082656172124625⟩,
    ⟨3,3,3,1,2082656172124625⟩,
    ⟨4,4,3,1,2407398541906984⟩,
    ⟨5,5,3,1,2739440492051523⟩,
    ⟨6,6,3,1,3080918482369562⟩,
    ⟨7,7,3,1,3433968972672420⟩,
    ⟨8,14,3,1,6408815028518270⟩,
    ⟨2,4,4,1,4840199963582061⟩,
    ⟨15,26,3,1,15182194834598135⟩,
    ⟨5,17,4,1,16654659875432426⟩,
    ⟨18,24,4,1,25172336815728545⟩,
    ⟨2,21,5,1,36810984112391687⟩,
    ⟨2,18,6,1,44809383679300253⟩,
    ⟨2,8,6,2,74014124830343166⟩,
    ⟨9,12,6,2,107444623972593638⟩,
    ⟨13,15,6,2,133508341055216834⟩,
    ⟨16,18,6,2,160677742451767466⟩,
    ⟨3,12,7,1,41550007179061313⟩,
    ⟨3,8,7,2,116483475873067137⟩,
    ⟨9,12,7,2,166438983552168570⟩,
    ⟨3,4,8,1,39346946759283370⟩,
    ⟨3,4,8,2,165806435271283485⟩
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

abbrev budget : ℕ := 265963255385374628

def factorCap (top : ℕ) : ℕ := budget-Low6960Prices.lowerCap top

def pricingWeight (k : Band) (b j t : ℕ) : ℕ :=
  if k=empty then Low6960AllocWeight.weight b j t else j

def pricingDenom (k : Band) : ℕ := if k=empty then 486 else 58-(start k).j

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
  let N := max layerCount (L + 1650 / (r.j + y.j))
  rw [← Final50PriceLayer.availableMass_eq_sum hr hj (N := N) (le_max_right _ _)]
  refine K1_13_8.sum_range_mono (le_max_left _ _) fun k _ => ?_
  unfold Final50PriceLayer.layerTerm Final50PriceLayer.fastLayer Final50Price.remaining
  split
  · exact min_le_left _ _
  · rw [← P0_9_8.symbol_count]
    exact min_le_right _ _

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
    ∃ l, 0 < l ∧ l ≤ order cells a ∧ contractedPrice a (start k) l 171 ≤
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
  have hc : contractedPrice a (start k) l 171 ≤ cutPrice a l 32 (fourSurface a.chamber (hullOf k l)) := by
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
