import ProximityPrize.SubmissionLower.Compact54TiltedEval
import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

/-! The same paid-tile proposition as `Compact50Cover.Tile.Paid`, decided with the Horner tilted surface.
Every price below is proved equal to its stock definition, so a batch checked here is a stock `PaidBatch`. -/
namespace Compact54FastPrice
noncomputable section
open K1_13 (Shape ceilDiv)
open K1_13_8_2 (Threshold orderFor)
open Final50Price (tiltedFits tiltedSurface physicalPrice physicalPriceOld physicalPriceTilted
  physicalPriceActive physicalPriceWith tiltedSurfaceActive activeFitsPrice activeLoss activeClips primaryBox)
open Final50SharedPrice (Surface Rate weights surface surfaceScale RateFits deficit coord slope expression
  additiveBase nonsharedFee price)
open Final50PriceCaps (Band start endWidth order thresholds activeCap allowance actualAllowance)
open Final50PriceActualOrder (raised)
open Compact50Cover (Tile PaidBatch pays)
open Final50PriceTableBase (OldReceipt PointReceipt ExactPointReceipt SharedReceipt)
open KoalaRetainedCut (contractedPrice chamberHull residualBox cutPrice fourSurface)
open KoalaWeightedRate (Pays Fits RayBounds Envelope boxFee sepBox)
open private chargedPrice from ProximityPrize.SubmissionLower.Final50GeometryCut

/-- `mixed32` in closed form: the fourth difference at the origin of the homogeneous quartic
`volume32` is its polarization, 43 monomials split into a positive and a negative part. -/
def mixedPos (p q r s : Shape) : ℕ :=
  p.b*(q.j*(r.j*(16*s.t)+r.t*(16*s.j))+q.t*(r.j*(16*s.j)+r.t*(144*s.t)))+p.j*(q.b*(r.j*(16*s.t)+r.t*(16*s.j))+q.j*(r.b*(16*s.t)+r.t*(16*s.b+56*s.t))+q.t*(r.b*(16*s.j)+r.j*(16*s.b+56*s.t)+r.t*(56*s.j)))+p.t*(q.b*(r.j*(16*s.j)+r.t*(144*s.t))+q.j*(r.b*(16*s.j)+r.j*(16*s.b+56*s.t)+r.t*(56*s.j))+q.t*(r.b*(144*s.t)+r.j*(56*s.j)+r.t*(144*s.b+216*s.t)))

def mixedNeg (p q r s : Shape) : ℕ :=
  p.b*(q.j*(r.t*(48*s.t))+q.t*(r.j*(48*s.t)+r.t*(48*s.j)))+p.j*(q.b*(r.t*(48*s.t))+q.j*(r.j*(24*s.t)+r.t*(24*s.j))+q.t*(r.b*(48*s.t)+r.j*(24*s.j)+r.t*(48*s.b+120*s.t)))+p.t*(q.b*(r.j*(48*s.t)+r.t*(48*s.j))+q.j*(r.b*(48*s.t)+r.j*(24*s.j)+r.t*(48*s.b+120*s.t))+q.t*(r.b*(48*s.j)+r.j*(48*s.b+120*s.t)+r.t*(120*s.j)))

def mixedFast (p q r s : Shape) : ℕ := mixedPos p q r s - mixedNeg p q r s

theorem mixedFast_eq (p q r s : Shape) : mixedFast p q r s = K1_13.mixed32 p q r s := by
  have h : K1_13.difference (K1_13.difference (K1_13.difference (K1_13.difference K1_13.volume32 p) q) r)
      s ⟨0,0,0⟩ = (mixedPos p q r s : ℤ) - (mixedNeg p q r s : ℤ) := by
    simp only [K1_13.difference, K1_13.volume32, K1_13.Shape.plus, mixedPos, mixedNeg]
    push_cast
    ring
  rw [mixedFast, K1_13.mixed32, h]
  first | omega | exact (Int.toNat_sub _ _).symm

/-- The stock charged price (`cutPrice`) with every mixed volume in closed form. -/
private def chargedFast (x : Shape) (l scale S : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := K1_13.chart Final50Price.taylorLength p
  let numerator := ceilDiv S scale +
    ceilDiv ((Final50Price.errors + 2 * Final50Price.incidenceGap) * x.b * q.b *
      (K1_13.chart (Final50Price.taylorLength + 1) p).b) Final50Price.incidenceGap
  let auxBox := q.plus (p.scale 4)
  let curves := mixedFast p q auxBox h + 2 * x.t * mixedFast p p p h
  let points := mixedFast p q auxBox p + 2 * x.t * mixedFast p p p p
  ceilDiv numerator l + 2 * Final50Price.physicalDegree * x.b * q.b +
    ceilDiv (Final50Price.errors * curves + 2 * Final50Price.incidenceGap * points)
      (32 * Final50Price.incidenceGap)

private theorem cut_fast (x : Shape) (l scale S : ℕ) : chargedFast x l scale S = cutPrice x l scale S := by
  simp only [chargedFast, mixedFast_eq, cutPrice, chargedPrice, Final50GeometryCut.auxCurves32,
    Final50GeometryCut.auxPoints32, Final50GeometryCut.membershipDegree, Nat.mul_assoc] <;> rfl

private theorem old_cut (x : Shape) (l : ℕ) :
    physicalPriceOld x l = cutPrice x l 32 (Final50Price.surfaceNumerator32 x.chamber primaryBox) := by
  simp only [physicalPriceOld, cutPrice, chargedPrice, Final50GeometryCut.auxCurves32,
    Final50GeometryCut.auxPoints32, Final50GeometryCut.membershipDegree, Nat.mul_assoc] <;> rfl

private theorem with_cut (x : Shape) (l s : ℕ) : physicalPriceWith x l s = cutPrice x l (60*32) s := by
  simp only [physicalPriceWith, cutPrice, chargedPrice, Final50GeometryCut.auxCurves32,
    Final50GeometryCut.auxPoints32, Final50GeometryCut.membershipDegree, Nat.mul_assoc] <;> rfl

private def surfNumFast (p q : Shape) : ℕ :=
  let L := Final50Price.taylorLength
  let g : Shape := ⟨max p.b (p.j + 1), p.j + 1, min (p.t + 1) ((p.j + 1) / 3)⟩
  let a := K1_13.liftedChart (L + 1) p
  let b := K1_13.liftedChart (L + 2) p
  min (mixedFast p q (K1_13.chart (L + 1) p) (K1_13.chart (L + 2) p))
    (mixedFast p q a b + (L + 1) * mixedFast p q g b + (L + 2) * mixedFast p q g a)

private theorem surfNumFast_eq (p q : Shape) : surfNumFast p q = Final50Price.surfaceNumerator32 p q := by
  simp only [surfNumFast, Final50Price.surfaceNumerator32, mixedFast_eq] <;> rfl

private def oldFast (x : Shape) (l : ℕ) : ℕ := chargedFast x l 32 (surfNumFast x.chamber primaryBox)

private theorem oldFast_eq (x : Shape) (l : ℕ) : oldFast x l = physicalPriceOld x l := by
  rw [oldFast, cut_fast, surfNumFast_eq, old_cut]

private def fourFast (p q : Shape) : ℕ :=
  mixedFast p q (K1_13.chart (Final50Price.taylorLength+1) p) (K1_13.chart (Final50Price.taylorLength+2) p)

private theorem fourFast_eq (p q : Shape) : fourFast p q = fourSurface p q := by
  simp only [fourFast, fourSurface, mixedFast_eq] <;> rfl

private def surfaceFast (p q : Shape) : ℕ :=
  if p.j + 1 ≤ p.b ∧ 2 ≤ p.j ∧ 2 ≤ p.t then Compact54Tilted.tiltedFast p q
  else if p.j + 1 ≤ p.b ∧ 2 ≤ p.j ∧ p.t = 1 then Compact54Tilted.tiltedFast1 p q
  else tiltedSurface p q

private theorem surfaceFast_eq (p q : Shape) : surfaceFast p q = tiltedSurface p q := by
  unfold surfaceFast
  split
  · rename_i h
    exact Compact54Tilted.tiltedFast_eq p q h.1 h.2.1 h.2.2
  · split
    · rename_i _ h
      exact Compact54Tilted.tiltedFast1_eq p q h.1 h.2.1 h.2.2
    · rfl

private def physicalFast (x : Shape) (l K : ℕ) : ℕ :=
  if tiltedFits x then
    let s := surfaceFast x.chamber primaryBox
    let base := min (oldFast x l) (chargedFast x l (60*32) s)
    if activeFitsPrice x K then
      min base (chargedFast x l (60*32) (s - activeLoss (activeClips x.chamber K)))
    else base
  else oldFast x l

private theorem physicalFast_eq (x : Shape) (l K : ℕ) : physicalFast x l K = physicalPrice x l K := by
  simp only [physicalFast,physicalPrice,physicalPriceTilted,physicalPriceActive,tiltedSurfaceActive,surfaceFast_eq,
    oldFast_eq, cut_fast, with_cut]

private def contractedFast (x h : Shape) (l active : ℕ) : ℕ :=
  let q := chamberHull (residualBox h l)
  let old := physicalFast x l active
  let four := if 0 < q.t then min old (chargedFast x l 32 (fourFast x.chamber q)) else old
  if tiltedFits x then min four (chargedFast x l (60*32) (surfaceFast x.chamber q)) else four

private theorem contractedFast_eq (x h : Shape) (l active : ℕ) :
    contractedFast x h l active = contractedPrice x h l active := by
  simp only [contractedFast,contractedPrice,physicalFast_eq,surfaceFast_eq,cut_fast,fourFast_eq]

private def weightsFast (kind : Surface) (f : Shape) : Shape :=
  match kind with
  | .ordinary =>
    let p := f.chamber
    let c1 := K1_13.chart (Final50Price.taylorLength + 1) p
    let c2 := K1_13.chart (Final50Price.taylorLength + 2) p
    let b := mixedFast p ⟨1,0,0⟩ c1 c2
    let j := mixedFast p ⟨1,1,0⟩ c1 c2 - b
    let t := mixedFast p ⟨3,3,1⟩ c1 c2 - 3*(b+j)
    ⟨b,j,t⟩
  | .tilted =>
    let s := surfaceFast f.chamber
    let b := s ⟨1,0,0⟩
    let j := s ⟨1,1,0⟩ - b
    let t := s ⟨3,3,1⟩ - 3*(b+j)
    ⟨b,j,t⟩

private theorem weightsFast_eq (kind : Surface) (f : Shape) : weightsFast kind f = weights kind f := by
  cases kind
  · simp only [weightsFast,weights,surface,mixedFast_eq] <;> rfl
  · simp only [weightsFast,surfaceFast_eq,weights,surface]

private def rateFitsFast (f : Shape) (u : Rate) : Prop :=
  let p := coord slope u.pivot
  let q := coord f u.pivot
  let w := weightsFast u.kind f
  let target := 3 * surfaceScale u.kind * u.amount
  (u.kind = .tilted → tiltedFits f) ∧
  0 < u.split ∧ u.split*p < q ∧
  (∀ i, p * coord f i ≤ q * coord slope i) ∧
  (∀ useIndex : Bool, expression w slope useIndex u.topIndex ≤ target) ∧
  (∀ useIndex : Bool, expression w (deficit q p f) useIndex u.topIndex ≤ target*(q-u.split*p))

private instance (f : Shape) (u : Rate) : Decidable (rateFitsFast f u) := by
  unfold rateFitsFast
  infer_instance

private theorem rateFitsFast_iff (f : Shape) (u : Rate) : rateFitsFast f u ↔ RateFits f u := by
  simp only [rateFitsFast,RateFits,weightsFast_eq]

private def rayBoundsFast (p : Envelope) (unit : ℕ) (x : Shape) (amount : ℕ) : Prop :=
  let w := weightsFast .tilted x
  let scale := 1920*amount
  unit*w.b ≤ scale*p.coeff.b ∧
    unit*(w.b+w.j) ≤ scale*(p.coeff.b+p.coeff.j) ∧
    unit*(3*(w.b+w.j)+w.t) ≤ scale*(3*(p.coeff.b+p.coeff.j)+p.coeff.t) ∧
    unit*boxFee w (sepBox x) ≤ scale*p.sep

private def paysRayFast (p : Envelope) (x : Shape) (u : Rate) : Prop :=
  Fits p x ∧ u.kind = .tilted ∧ u.split = KoalaWeightedRate.split ∧ 0 < u.amount ∧ tiltedFits x ∧
    rayBoundsFast p KoalaWeightedRate.unit x u.amount

private instance (p : Envelope) (x : Shape) (u : Rate) : Decidable (paysRayFast p x u) := by
  unfold paysRayFast rayBoundsFast Fits
  infer_instance

private theorem paysRayFast_iff (p : Envelope) (x : Shape) (u : Rate) : paysRayFast p x u ↔ Pays p x u := by
  simp only [paysRayFast,rayBoundsFast,Pays,RayBounds,weightsFast_eq]

private def splitPaysFast (p : Envelope) (k unit : ℕ) (x : Shape) (u : Rate) : Prop :=
  Fits p x ∧ u.kind = .tilted ∧ u.split = k ∧ 0 < k ∧ 0 < unit ∧ 0 < u.amount ∧
    tiltedFits x ∧ rayBoundsFast p unit x u.amount

private instance (p : Envelope) (k unit : ℕ) (x : Shape) (u : Rate) :
    Decidable (splitPaysFast p k unit x u) := by
  unfold splitPaysFast rayBoundsFast Fits
  infer_instance

private theorem splitPaysFast_iff (p : Envelope) (k unit : ℕ) (x : Shape) (u : Rate) :
    splitPaysFast p k unit x u ↔ KoalaSplitRate.Pays p k unit x u := by
  simp only [splitPaysFast, rayBoundsFast, KoalaSplitRate.Pays, KoalaSplitRate.RayBounds,
    weightsFast_eq]

private def allowedFast (x : Shape) (u : Rate) : Prop :=
  (rateFitsFast x u ∨ paysRayFast KoalaWeightedRate.first x u) ∨
  splitPaysFast KoalaAt2428Gate0.envelope KoalaAt2428Gate0.split KoalaAt2428Gate0.unit x u ∨
  splitPaysFast KoalaAt2428Gate1.envelope KoalaAt2428Gate1.split KoalaAt2428Gate1.unit x u ∨
  splitPaysFast KoalaAt2428Gate2.envelope KoalaAt2428Gate2.split KoalaAt2428Gate2.unit x u ∨
  splitPaysFast KoalaAt2428Gate3.envelope KoalaAt2428Gate3.split KoalaAt2428Gate3.unit x u ∨
  splitPaysFast KoalaAt2428Gate4.envelope KoalaAt2428Gate4.split KoalaAt2428Gate4.unit x u ∨
  splitPaysFast KoalaAt2428Gate5.envelope KoalaAt2428Gate5.split KoalaAt2428Gate5.unit x u ∨
  splitPaysFast KoalaAt2428Gate6.envelope KoalaAt2428Gate6.split KoalaAt2428Gate6.unit x u ∨
  splitPaysFast KoalaAt2428Gate7.envelope KoalaAt2428Gate7.split KoalaAt2428Gate7.unit x u ∨
  splitPaysFast KoalaAt2428Gate8.envelope KoalaAt2428Gate8.split KoalaAt2428Gate8.unit x u ∨
  splitPaysFast KoalaAt2428Gate9.envelope KoalaAt2428Gate9.split KoalaAt2428Gate9.unit x u ∨
  splitPaysFast KoalaAt2428Gate10.envelope KoalaAt2428Gate10.split KoalaAt2428Gate10.unit x u ∨
  splitPaysFast KoalaAt2428Gate11.envelope KoalaAt2428Gate11.split KoalaAt2428Gate11.unit x u ∨
  splitPaysFast KoalaAt2428Gate12.envelope KoalaAt2428Gate12.split KoalaAt2428Gate12.unit x u ∨
  splitPaysFast KoalaAt2428Gate13.envelope KoalaAt2428Gate13.split KoalaAt2428Gate13.unit x u ∨
  splitPaysFast KoalaAt2428Gate14.envelope KoalaAt2428Gate14.split KoalaAt2428Gate14.unit x u ∨
  splitPaysFast KoalaAt2428Gate15.envelope KoalaAt2428Gate15.split KoalaAt2428Gate15.unit x u ∨
  splitPaysFast KoalaAt2428Gate16.envelope KoalaAt2428Gate16.split KoalaAt2428Gate16.unit x u ∨
  splitPaysFast KoalaAt2428Gate17.envelope KoalaAt2428Gate17.split KoalaAt2428Gate17.unit x u ∨
  splitPaysFast KoalaAt2428Gate18.envelope KoalaAt2428Gate18.split KoalaAt2428Gate18.unit x u ∨
  splitPaysFast KoalaAt2428Gate19.envelope KoalaAt2428Gate19.split KoalaAt2428Gate19.unit x u ∨
  splitPaysFast KoalaAt2428Gate20.envelope KoalaAt2428Gate20.split KoalaAt2428Gate20.unit x u ∨
  splitPaysFast KoalaAt2428Gate21.envelope KoalaAt2428Gate21.split KoalaAt2428Gate21.unit x u ∨
  splitPaysFast KoalaAt2428Gate22.envelope KoalaAt2428Gate22.split KoalaAt2428Gate22.unit x u ∨
  splitPaysFast KoalaAt2428Gate23.envelope KoalaAt2428Gate23.split KoalaAt2428Gate23.unit x u ∨
  splitPaysFast KoalaAt2428Gate24.envelope KoalaAt2428Gate24.split KoalaAt2428Gate24.unit x u ∨
  splitPaysFast KoalaAt2428Gate25.envelope KoalaAt2428Gate25.split KoalaAt2428Gate25.unit x u ∨
  splitPaysFast KoalaAt2428Gate26.envelope KoalaAt2428Gate26.split KoalaAt2428Gate26.unit x u ∨
  splitPaysFast KoalaAt2428Gate27.envelope KoalaAt2428Gate27.split KoalaAt2428Gate27.unit x u ∨
  splitPaysFast KoalaAt2428Gate28.envelope KoalaAt2428Gate28.split KoalaAt2428Gate28.unit x u ∨
  splitPaysFast KoalaAt2428Gate29.envelope KoalaAt2428Gate29.split KoalaAt2428Gate29.unit x u ∨
  splitPaysFast KoalaAt2428Gate30.envelope KoalaAt2428Gate30.split KoalaAt2428Gate30.unit x u ∨
  splitPaysFast KoalaAt2428Gate31.envelope KoalaAt2428Gate31.split KoalaAt2428Gate31.unit x u ∨
  splitPaysFast KoalaAt2428Gate32.envelope KoalaAt2428Gate32.split KoalaAt2428Gate32.unit x u ∨
  splitPaysFast KoalaAt2428Gate33.envelope KoalaAt2428Gate33.split KoalaAt2428Gate33.unit x u ∨
  splitPaysFast KoalaAt2428Gate34.envelope KoalaAt2428Gate34.split KoalaAt2428Gate34.unit x u ∨
  splitPaysFast KoalaAt2428Gate35.envelope KoalaAt2428Gate35.split KoalaAt2428Gate35.unit x u ∨
  splitPaysFast KoalaAt2428Gate36.envelope KoalaAt2428Gate36.split KoalaAt2428Gate36.unit x u ∨
  splitPaysFast KoalaAt2428Gate37.envelope KoalaAt2428Gate37.split KoalaAt2428Gate37.unit x u ∨
  splitPaysFast KoalaAt2428Gate38.envelope KoalaAt2428Gate38.split KoalaAt2428Gate38.unit x u ∨
  splitPaysFast KoalaAt2428Gate39.envelope KoalaAt2428Gate39.split KoalaAt2428Gate39.unit x u ∨
  splitPaysFast KoalaAt2428Gate40.envelope KoalaAt2428Gate40.split KoalaAt2428Gate40.unit x u ∨
  splitPaysFast KoalaAt2428Gate41.envelope KoalaAt2428Gate41.split KoalaAt2428Gate41.unit x u ∨
  splitPaysFast KoalaAt2428Gate42.envelope KoalaAt2428Gate42.split KoalaAt2428Gate42.unit x u ∨
  splitPaysFast KoalaAt2428Gate43.envelope KoalaAt2428Gate43.split KoalaAt2428Gate43.unit x u ∨
  splitPaysFast KoalaAt2428Gate44.envelope KoalaAt2428Gate44.split KoalaAt2428Gate44.unit x u ∨
  splitPaysFast KoalaAt2428Gate45.envelope KoalaAt2428Gate45.split KoalaAt2428Gate45.unit x u ∨
  splitPaysFast KoalaAt2428Gate46.envelope KoalaAt2428Gate46.split KoalaAt2428Gate46.unit x u ∨
  splitPaysFast KoalaAt2428Gate47.envelope KoalaAt2428Gate47.split KoalaAt2428Gate47.unit x u ∨
  splitPaysFast KoalaAt2428Gate48.envelope KoalaAt2428Gate48.split KoalaAt2428Gate48.unit x u ∨
  splitPaysFast KoalaAt2428Gate49.envelope KoalaAt2428Gate49.split KoalaAt2428Gate49.unit x u ∨
  splitPaysFast KoalaAt2428Gate50.envelope KoalaAt2428Gate50.split KoalaAt2428Gate50.unit x u ∨
  splitPaysFast KoalaAt2428Gate51.envelope KoalaAt2428Gate51.split KoalaAt2428Gate51.unit x u ∨
  splitPaysFast KoalaAt2428Gate52.envelope KoalaAt2428Gate52.split KoalaAt2428Gate52.unit x u ∨
  splitPaysFast KoalaAt2428Gate53.envelope KoalaAt2428Gate53.split KoalaAt2428Gate53.unit x u ∨
  splitPaysFast KoalaAt2428Gate54.envelope KoalaAt2428Gate54.split KoalaAt2428Gate54.unit x u ∨
  splitPaysFast KoalaAt2428Gate55.envelope KoalaAt2428Gate55.split KoalaAt2428Gate55.unit x u ∨
  splitPaysFast KoalaAt2428Gate56.envelope KoalaAt2428Gate56.split KoalaAt2428Gate56.unit x u ∨
  splitPaysFast KoalaAt2428Gate57.envelope KoalaAt2428Gate57.split KoalaAt2428Gate57.unit x u ∨
  splitPaysFast KoalaAt2428Gate58.envelope KoalaAt2428Gate58.split KoalaAt2428Gate58.unit x u ∨
  splitPaysFast KoalaAt2428Gate59.envelope KoalaAt2428Gate59.split KoalaAt2428Gate59.unit x u ∨
  splitPaysFast KoalaAt2428Gate60.envelope KoalaAt2428Gate60.split KoalaAt2428Gate60.unit x u ∨
  splitPaysFast KoalaAt2428Gate61.envelope KoalaAt2428Gate61.split KoalaAt2428Gate61.unit x u ∨
  splitPaysFast KoalaAt2428Gate62.envelope KoalaAt2428Gate62.split KoalaAt2428Gate62.unit x u ∨
  splitPaysFast KoalaAt2428Gate63.envelope KoalaAt2428Gate63.split KoalaAt2428Gate63.unit x u ∨
  splitPaysFast KoalaAt2428Gate64.envelope KoalaAt2428Gate64.split KoalaAt2428Gate64.unit x u ∨
  splitPaysFast KoalaAt2428Gate65.envelope KoalaAt2428Gate65.split KoalaAt2428Gate65.unit x u ∨
  splitPaysFast KoalaAt2428Gate66.envelope KoalaAt2428Gate66.split KoalaAt2428Gate66.unit x u ∨
  splitPaysFast KoalaAt2428Gate67.envelope KoalaAt2428Gate67.split KoalaAt2428Gate67.unit x u ∨
  splitPaysFast KoalaAt2428Gate68.envelope KoalaAt2428Gate68.split KoalaAt2428Gate68.unit x u ∨
  splitPaysFast KoalaAt2428Gate69.envelope KoalaAt2428Gate69.split KoalaAt2428Gate69.unit x u ∨
  splitPaysFast KoalaAt2428Gate70.envelope KoalaAt2428Gate70.split KoalaAt2428Gate70.unit x u ∨
  splitPaysFast KoalaAt2428Gate71.envelope KoalaAt2428Gate71.split KoalaAt2428Gate71.unit x u ∨
  splitPaysFast KoalaAt2428Gate72.envelope KoalaAt2428Gate72.split KoalaAt2428Gate72.unit x u ∨
  splitPaysFast KoalaAt2428Gate73.envelope KoalaAt2428Gate73.split KoalaAt2428Gate73.unit x u

set_option synthInstance.maxSize 4096 in
private instance (x : Shape) (u : Rate) : Decidable (allowedFast x u) := by
  unfold allowedFast
  infer_instance

private theorem allowedFast_iff (x : Shape) (u : Rate) :
    allowedFast x u ↔ KoalaAt2428Rates.Allowed x u := by
  simp only [allowedFast, KoalaAt2428Rates.Allowed, KoalaWeightedRate.Allowed, rateFitsFast_iff,
    paysRayFast_iff, splitPaysFast_iff]

private def additiveFast (x : Shape) (l : ℕ) : ℕ :=
  let p := x.chamber
  let q := primaryBox
  let h := K1_13.chart Final50Price.taylorLength p
  let h1 := K1_13.chart (Final50Price.taylorLength+1) p
  let cont := ceilDiv ((Final50Price.errors+2*Final50Price.incidenceGap)*x.b*q.b*h1.b) Final50Price.incidenceGap
  let z := q.plus (p.scale 4)
  let cv := mixedFast p q z h + 2*x.t*mixedFast p p p h
  let pt := mixedFast p q z p + 2*x.t*mixedFast p p p p
  ceilDiv cont l + 2*Final50Price.physicalDegree*x.b*q.b +
    ceilDiv (Final50Price.errors*cv+2*Final50Price.incidenceGap*pt) (32*Final50Price.incidenceGap)

private theorem additiveFast_eq (x : Shape) (l : ℕ) : additiveFast x l = additiveBase x l := by
  simp only [additiveFast, additiveBase, mixedFast_eq] <;> rfl

private def sharedFast (x : Shape) (l K : ℕ) (u : Rate) : ℕ :=
  ceilDiv (physicalFast x l K + u.split*additiveFast x l + u.split*u.amount + 1)
    (u.split+1) + nonsharedFee x l

private theorem sharedFast_eq (x : Shape) (l K : ℕ) (u : Rate) : sharedFast x l K u = price x l K u := by
  simp only [sharedFast,price,physicalFast_eq,additiveFast_eq]

/-- Check the requested order using the first threshold that pays it. -/
private def supportsOrderIn (b j l : Nat) (qs : List Threshold) : Prop :=
  l ≤ 1 ∨ qs.any (fun q => decide (l ≤ q.l ∧ q.b ≤ b ∧ q.j ≤ j)) = true

private theorem supportsOrderIn_iff (b j l : Nat) (qs : List Threshold) :
    supportsOrderIn b j l qs ↔ l ≤ orderFor b j qs := by
  induction qs with
  | nil => simp [supportsOrderIn, orderFor]
  | cons q qs ih =>
    rw [orderFor, le_max_iff, ← ih]
    by_cases h : q.b ≤ b ∧ q.j ≤ j
    · simp only [supportsOrderIn, List.any_cons, Bool.or_eq_true, decide_eq_true_eq, if_pos h]
      tauto
    · simp only [supportsOrderIn, List.any_cons, Bool.or_eq_true, decide_eq_true_eq, if_neg h]
      tauto

private def supportsOrder (k : Band) (x : Shape) (l : Nat) : Prop :=
  supportsOrderIn x.b x.j l (thresholds k)

private instance (k : Band) (x : Shape) (l : Nat) : Decidable (supportsOrder k x l) := by
  unfold supportsOrder supportsOrderIn
  infer_instance

private theorem supportsOrder_iff (k : Band) (x : Shape) (l : Nat) :
    supportsOrder k x l ↔ l ≤ order k x :=
  supportsOrderIn_iff _ _ _ _

private def exactPointFast (top : ℕ) (k : Band) (b j t l : ℕ) : Prop :=
  0 < l ∧ supportsOrder k ⟨b,j,t⟩ l ∧
    ∀ w : Fin 27, (start k).b ≤ w.val → w.val ≤ endWidth k → w.val + b ≤ 137 →
      contractedFast ⟨b,j,t⟩ ⟨w.val,(start k).j,(start k).t⟩ (raised k b j t w.val l) (activeCap k) ≤
        actualAllowance top k w.val b j t

private instance (top : ℕ) (k : Band) (b j t l : ℕ) :
    Decidable (exactPointFast top k b j t l) := by
  unfold exactPointFast
  infer_instance

private theorem exactPointFast_iff (top : ℕ) (k : Band) (b j t l : ℕ) :
    exactPointFast top k b j t l ↔ ExactPointReceipt top k b j t l := by
  simp only [exactPointFast, ExactPointReceipt, contractedFast_eq, supportsOrder_iff]

private def paidFast (k : Band) (t : ℕ) : Tile → Prop
  | .rectangle b j B J l =>
    0 < l ∧ supportsOrder k ⟨b,j,0⟩ l ∧ oldFast ⟨B,J,t⟩ l ≤ allowance ((start k).t+t) k b j t
  | .mixrect b j B J l =>
    0 < l ∧ supportsOrder k ⟨b,j,0⟩ l ∧ 0 < (Final54MixReceipt.hullOf k l).t ∧
      chargedFast ⟨B,J,t⟩ l 32 (fourFast (Shape.chamber ⟨B,J,t⟩) (Final54MixReceipt.hullOf k l)) ≤
        allowance ((start k).t+t) k b j t
  | .point b j l =>
    (0 < l ∧ supportsOrder k ⟨b,j,t⟩ l ∧
      contractedFast ⟨b,j,t⟩ (start k) l (activeCap k) ≤ allowance ((start k).t+t) k b j t) ∨
    exactPointFast ((start k).t+t) k b j t l
  | .shared b j l u =>
    0 < l ∧ supportsOrder k ⟨b,j,t⟩ l ∧ allowedFast ⟨b,j,t⟩ u ∧
      sharedFast ⟨b,j,t⟩ l 172 u ≤ allowance ((start k).t+t) k b j t

private instance (k : Band) (t : ℕ) (tile : Tile) : Decidable (paidFast k t tile) := by
  cases tile <;> unfold paidFast <;> infer_instance

private theorem paidFast_iff (k : Band) (t : ℕ) (tile : Tile) : paidFast k t tile ↔ tile.Paid k t := by
  cases tile <;>
    simp only [paidFast, Tile.Paid, PointReceipt, SharedReceipt, OldReceipt, Final54MixReceipt.MixReceipt,
      contractedFast_eq, exactPointFast_iff, allowedFast_iff, sharedFast_eq, oldFast_eq, cut_fast, fourFast_eq,
      supportsOrder_iff]

def paysFast (k : Band) (t : ℕ) (tiles : List Tile) : Bool := tiles.all fun x => decide (paidFast k t x)

theorem pays_of_fast (k : Band) (t : ℕ) (tiles : List Tile)
    (h : paysFast k t tiles = true) : pays k t tiles = true := by
  unfold paysFast at h
  unfold pays
  apply List.all_eq_true.mpr
  intro tile ht
  exact decide_eq_true ((paidFast_iff k t tile).mp (of_decide_eq_true (List.all_eq_true.mp h tile ht)))

/-- A stock paid batch, checked with the Horner evaluator. -/
def fastBatch {k : Band} {t : ℕ} (tiles : List Tile) (h : paysFast k t tiles = true) : PaidBatch k t :=
  ⟨tiles, pays_of_fast k t tiles h⟩

end
end Compact54FastPrice
