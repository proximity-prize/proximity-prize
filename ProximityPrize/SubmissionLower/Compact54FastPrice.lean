import ProximityPrize.SubmissionLower.Compact54TiltedEval
import ProximityPrize.SubmissionLower.Compact50Cover

set_option maxRecDepth 16000

/-! The same paid-tile proposition as `Compact50Cover.Tile.Paid`, decided with the Horner tilted surface.
Every price below is proved equal to its stock definition, so a batch checked here is a stock `PaidBatch`. -/
namespace Compact54FastPrice
noncomputable section
open K1_13 (Shape ceilDiv)
open Final50Price (tiltedFits tiltedSurface physicalPrice physicalPriceOld physicalPriceTilted
  physicalPriceActive physicalPriceWith tiltedSurfaceActive activeFitsPrice activeLoss activeClips primaryBox)
open Final50SharedPrice (Surface Rate weights surface surfaceScale RateFits deficit coord slope expression
  additiveBase nonsharedFee price)
open Final50PriceCaps (Band start order activeCap allowance)
open Compact50Cover (Tile PaidBatch pays)
open Final50PriceTableBase (PointReceipt SharedReceipt)
open KoalaRetainedCut (contractedPrice chamberHull residualBox cutPrice fourSurface)
open KoalaWeightedRate (Allowed Pays Fits RayBounds Envelope boxFee sepBox)
open Final50PriceTableBase (OldReceipt)
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

private def rayBoundsFast (p : Envelope) (x : Shape) (amount : ℕ) : Prop :=
  let w := weightsFast .tilted x
  let scale := 1920*amount
  KoalaWeightedRate.unit*w.b ≤ scale*p.coeff.b ∧
    KoalaWeightedRate.unit*(w.b+w.j) ≤ scale*(p.coeff.b+p.coeff.j) ∧
    KoalaWeightedRate.unit*(3*(w.b+w.j)+w.t) ≤ scale*(3*(p.coeff.b+p.coeff.j)+p.coeff.t) ∧
    KoalaWeightedRate.unit*boxFee w (sepBox x) ≤ scale*p.sep

private def paysRayFast (p : Envelope) (x : Shape) (u : Rate) : Prop :=
  Fits p x ∧ u.kind = .tilted ∧ u.split = KoalaWeightedRate.split ∧ 0 < u.amount ∧ tiltedFits x ∧
    rayBoundsFast p x u.amount

private instance (p : Envelope) (x : Shape) (u : Rate) : Decidable (paysRayFast p x u) := by
  unfold paysRayFast rayBoundsFast Fits
  infer_instance

private theorem paysRayFast_iff (p : Envelope) (x : Shape) (u : Rate) : paysRayFast p x u ↔ Pays p x u := by
  simp only [paysRayFast,rayBoundsFast,Pays,RayBounds,weightsFast_eq]

private def allowedFast (x : Shape) (u : Rate) : Prop :=
  rateFitsFast x u ∨ paysRayFast KoalaWeightedRate.first x u ∨ paysRayFast KoalaWeightedRate.second x u

private instance (x : Shape) (u : Rate) : Decidable (allowedFast x u) := by
  unfold allowedFast
  infer_instance

private theorem allowedFast_iff (x : Shape) (u : Rate) : allowedFast x u ↔ Allowed x u := by
  simp only [allowedFast,Allowed,rateFitsFast_iff,paysRayFast_iff]

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

private def paidFast (k : Band) (t : ℕ) : Tile → Prop
  | .rectangle b j B J l =>
    0 < l ∧ l ≤ order k ⟨b,j,0⟩ ∧ oldFast ⟨B,J,t⟩ l ≤ allowance ((start k).t+t) k b j t
  | .mixrect b j B J l =>
    0 < l ∧ l ≤ order k ⟨b,j,0⟩ ∧ 0 < (Final54MixReceipt.hullOf k l).t ∧
      chargedFast ⟨B,J,t⟩ l 32 (fourFast (Shape.chamber ⟨B,J,t⟩) (Final54MixReceipt.hullOf k l)) ≤
        allowance ((start k).t+t) k b j t
  | .point b j l =>
    0 < l ∧ l ≤ order k ⟨b,j,t⟩ ∧
      contractedFast ⟨b,j,t⟩ (start k) l (activeCap k) ≤ allowance ((start k).t+t) k b j t
  | .shared b j l u =>
    k = .empty ∧ 0 < l ∧ l ≤ order .empty ⟨b,j,t⟩ ∧ allowedFast ⟨b,j,t⟩ u ∧
      sharedFast ⟨b,j,t⟩ l (activeCap .empty) u ≤ allowance t .empty b j t

private instance (k : Band) (t : ℕ) (tile : Tile) : Decidable (paidFast k t tile) := by
  cases tile <;> unfold paidFast <;> infer_instance

private theorem paidFast_iff (k : Band) (t : ℕ) (tile : Tile) : paidFast k t tile ↔ tile.Paid k t := by
  cases tile <;>
    simp only [paidFast, Tile.Paid, PointReceipt, SharedReceipt, OldReceipt, Final54MixReceipt.MixReceipt,
      contractedFast_eq, allowedFast_iff, sharedFast_eq, oldFast_eq, cut_fast, fourFast_eq]

def paysFast (k : Band) (t : ℕ) (tiles : List Tile) : Bool := tiles.all fun x => decide (paidFast k t x)

private theorem pays_of_fast (k : Band) (t : ℕ) (tiles : List Tile)
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
