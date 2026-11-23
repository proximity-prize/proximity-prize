/- Four-surface receipt from BitWonka PR663, adapted to width-dependent reserves. -/
import ProximityPrize.SubmissionLower.Final50PriceTableBase

set_option Elab.async false
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
  let p:=x.chamber
  let q:=Final50Price.primaryBox
  let h:=K1_13.chart Final50Price.taylorLength p
  let numerator := ceilDiv S 32 +
    ceilDiv ((Final50Price.errors + 2 * Final50Price.incidenceGap) * x.b * q.b *
      (K1_13.chart (Final50Price.taylorLength+1) p).b) Final50Price.incidenceGap
  let auxBox:=q.plus (p.scale 4)
  let curves:=K1_13.mixed32 p q auxBox h+2*x.t*K1_13.mixed32 p p p h
  let points:=K1_13.mixed32 p q auxBox p+2*x.t*K1_13.mixed32 p p p p
  ceilDiv numerator l + 2 * Final50Price.physicalDegree * x.b * q.b +
    ceilDiv (Final50Price.errors * curves + 2 * Final50Price.incidenceGap * points)
      (32*Final50Price.incidenceGap)

theorem cut_eq (x : Shape) (l S : ℕ) : cutPrice x l 32 S = oldWith x l S := by
  simp only [cutPrice, oldWith, chargedPrice, Final50GeometryCut.auxCurves32,
    Final50GeometryCut.auxPoints32,Final50GeometryCut.membershipDegree,Nat.mul_assoc]
  rfl

theorem oldWith_mono {x y : Shape} (h : InBox x y) (hx : 3 * x.t ≤ x.j)
    (hy:3*y.t≤y.j) (l:ℕ) {S S' : ℕ} (hS:S≤S'):oldWith x l S≤oldWith y l S' := by
  let p:=x.chamber
  let p' := y.chamber
  let q:Shape:=Final50Price.primaryBox
  let L:=Final50Price.taylorLength
  let A:=q.plus (p.scale 4)
  let A' := q.plus (p'.scale 4)
  have hp:=normalize_mono h
  have hpc:Chamber p:=normalize_chamber x hx
  have hp'c:Chamber p' := normalize_chamber y hy
  have hqc:Chamber q:=⟨by decide,le_rfl⟩
  have ha:InBox A A' := plus_mono (box_refl q) (scale_mono hp 4)
  have hac:Chamber A:=plus_chamber hqc (scale_chamber hpc 4)
  have ha'c:Chamber A' := plus_chamber hqc (scale_chamber hp'c 4)
  have hb:=(chart_mono (L+1) hp).1
  have hmain : (Final50Price.errors + 2*Final50Price.incidenceGap) * x.b * q.b * (K1_13.chart (L+1) p).b ≤
      (Final50Price.errors+2*Final50Price.incidenceGap)*y.b*q.b*(K1_13.chart (L+1) p').b:=by
    have:=h.1
    gcongr
  have hcurve:=mixed_mono hp (box_refl q) ha (chart_mono L hp) hp'c hqc ha'c hqc hac (chart_chamber L p)
  have hpoint:=mixed_mono hp (box_refl q) ha hp hp'c hqc ha'c hqc hac hpc
  have hcurve' := mixed_mono hp hp hp (chart_mono L hp) hp'c hp'c hp'c hpc hpc (chart_chamber L p)
  have hpoint' := mixed_mono hp hp hp hp hp'c hp'c hp'c hpc hpc hpc
  have htc:=Nat.mul_le_mul_left 2 h.2.2
  have hc:=Nat.add_le_add hcurve (Nat.mul_le_mul htc hcurve')
  have hn:=Nat.add_le_add hpoint (Nat.mul_le_mul htc hpoint')
  have hgeom := Nat.add_le_add (Nat.mul_le_mul_left Final50Price.errors hc)
    (Nat.mul_le_mul_left (2*Final50Price.incidenceGap) hn)
  have hraw:=Nat.mul_le_mul_right q.b (Nat.mul_le_mul_left (2*Final50Price.physicalDegree) h.1)
  exact Nat.add_le_add
    (Nat.add_le_add (Final50PriceMonotone.ceil_mono (Nat.add_le_add
      (Final50PriceMonotone.ceil_mono hS _) (Final50PriceMonotone.ceil_mono hmain _)) l) hraw)
    (Final50PriceMonotone.ceil_mono hgeom _)

/-- The residual hull of the band start at order `l`. -/
abbrev hullOf (k:Band) (l:ℕ):Shape:=chamberHull (residualBox (start k) l)

abbrev MixReceipt (top : ℕ) (k : Band) (bl jl bh jh t l : ℕ) : Prop :=
  0 < l ∧ l ≤ order k ⟨bl,jl,0⟩ ∧ 0 < (hullOf k l).t ∧
    cutPrice ⟨bh,jh,t⟩ l 32 (fourSurface (Shape.chamber ⟨bh,jh,t⟩) (hullOf k l)) ≤
      allowance top k bl jl t

theorem mixRectangle {top : ℕ} {k : Band} {a : Shape} {bl jl bh jh t l : ℕ}
    (h:MixReceipt top k bl jl bh jh t l)
    (hb:bl≤a.b) (hj:jl≤a.j) (hb' : a.b≤bh) (hj' : a.j≤jh)
    (ht:a.t=t) (ha:3*a.t≤a.j) :
    (∃ l,0 < l ∧ l≤order k a ∧ contractedPrice a (start k) l (activeCap k)≤allowance top k a.b a.j a.t):=by
  obtain ⟨hl,hlo,hq,hbill⟩:=h
  have hu:l≤order k a:=hlo.trans (Final50PriceCaps.order_mono k hb hj)
  have hi:3*t≤jh:=by omega
  have hbox:InBox a ⟨bh,jh,t⟩:=⟨hb', hj', ht.le⟩
  have hallow : allowance top k bl jl t ≤ allowance top k a.b a.j a.t :=
    Nat.div_le_div_right (Nat.mul_le_mul
      (Nat.sub_le_sub_left (Final50PriceCaps.tileReserve_anti k hb) _)
      (Final50PriceCaps.weight_mono k hb hj ht.ge))
  refine ⟨l,hl,hu, ?_⟩
  have hqc : Chamber (hullOf k l) := by
    have:=hull_valid (residualBox (start k) l)
    exact ⟨this.1,this.2.1⟩
  have hp:=normalize_mono hbox
  have hpc' : Chamber (Shape.chamber ⟨bh,jh,t⟩):=normalize_chamber _ hi
  have hsurf : fourSurface a.chamber (hullOf k l) ≤
      fourSurface (Shape.chamber ⟨bh,jh,t⟩) (hullOf k l) :=
    mixed_mono hp (box_refl _) (chart_mono _ hp) (chart_mono _ hp) hpc' hqc
      (chart_chamber _ _) hqc (chart_chamber _ _) (chart_chamber _ _)
  have hcut : cutPrice a l 32 (fourSurface a.chamber (hullOf k l)) ≤
      cutPrice ⟨bh,jh,t⟩ l 32 (fourSurface (Shape.chamber ⟨bh,jh,t⟩) (hullOf k l)):=by
    rw [cut_eq,cut_eq]
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
