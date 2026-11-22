import ProximityPrize.SubmissionLower.LambdaC53TiltedEval
import ProximityPrize.SubmissionLower.Compact50Cover

set_option Elab.async false
set_option maxRecDepth 16000

namespace LambdaC53TiltedPrice
open K1_13 (Shape ceilDiv)
open Final50Price (tiltedFits tiltedSurface physicalPrice physicalPriceOld physicalPriceTilted
  physicalPriceActive physicalPriceWith tiltedSurfaceActive activeFitsPrice activeLoss activeClips primaryBox)
open Final50SharedPrice (Surface Rate weights surface surfaceScale RateFits deficit coord slope expression
  additiveBase nonsharedFee price)
open Final50PriceCaps (Band start order activeCap allowance)
open Compact50Cover (Tile PaidBatch pays)
open Final50PriceTableBase (PointReceipt SharedReceipt)

private def surfaceFast (p q : Shape) : ℕ :=
  if p.j + 1 ≤ p.b ∧ 2 ≤ p.j ∧ 2 ≤ p.t then LambdaC53Tilted.tiltedFast p q
  else tiltedSurface p q

private theorem surfaceFast_eq (p q : Shape) : surfaceFast p q = tiltedSurface p q := by
  unfold surfaceFast
  split
  · rename_i h
    exact LambdaC53Tilted.tiltedFast_eq p q h.1 h.2.1 h.2.2
  · rfl

private def physicalFast (x : Shape) (l K : ℕ) : ℕ :=
  if tiltedFits x then
    let s := surfaceFast x.chamber primaryBox
    let base := min (physicalPriceOld x l) (physicalPriceWith x l s)
    if activeFitsPrice x K then
      min base (physicalPriceWith x l (s - activeLoss (activeClips x.chamber K)))
    else base
  else physicalPriceOld x l

private theorem physicalFast_eq (x : Shape) (l K : ℕ) : physicalFast x l K = physicalPrice x l K := by
  simp only [physicalFast,physicalPrice,physicalPriceTilted,physicalPriceActive,tiltedSurfaceActive,surfaceFast_eq]

private def weightsFast (kind : Surface) (f : Shape) : Shape :=
  match kind with
  | .ordinary => weights .ordinary f
  | .tilted =>
    let s := surfaceFast f.chamber
    let b := s ⟨1,0,0⟩
    let j := s ⟨1,1,0⟩ - b
    let t := s ⟨3,3,1⟩ - 3*(b+j)
    ⟨b,j,t⟩

private theorem weightsFast_eq (kind : Surface) (f : Shape) : weightsFast kind f = weights kind f := by
  cases kind
  · rfl
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

private def sharedFast (x : Shape) (l K : ℕ) (u : Rate) : ℕ :=
  ceilDiv (physicalFast x l K + u.split*additiveBase x l + u.split*u.amount + 1)
    (u.split+1) + nonsharedFee x l

private theorem sharedFast_eq (x : Shape) (l K : ℕ) (u : Rate) : sharedFast x l K u = price x l K u := by
  simp only [sharedFast,price,physicalFast_eq]

private def paidFast (k : Band) (t : ℕ) : Tile → Prop
  | .rectangle b j B J l => (Tile.rectangle b j B J l).Paid k t
  | .point b j l =>
    0 < l ∧ l ≤ order k ⟨b,j,t⟩ ∧ physicalFast ⟨b,j,t⟩ l (activeCap k) ≤ allowance ((start k).t+t) k j
  | .shared b j l u =>
    k = .empty ∧ 0 < l ∧ l ≤ order .empty ⟨b,j,t⟩ ∧ rateFitsFast ⟨b,j,t⟩ u ∧
      sharedFast ⟨b,j,t⟩ l (activeCap .empty) u ≤ allowance t .empty j

private instance (k : Band) (t : ℕ) (tile : Tile) : Decidable (paidFast k t tile) := by
  cases tile <;> unfold paidFast <;> infer_instance

private theorem paidFast_iff (k : Band) (t : ℕ) (tile : Tile) : paidFast k t tile ↔ tile.Paid k t := by
  cases tile <;>
    simp only [paidFast, Tile.Paid, PointReceipt, SharedReceipt, physicalFast_eq, rateFitsFast_iff, sharedFast_eq]

def paysFast (k : Band) (t : ℕ) (tiles : List Tile) : Bool := tiles.all fun x => decide (paidFast k t x)

private theorem pays_of_fast (k : Band) (t : ℕ) (tiles : List Tile)
    (h : paysFast k t tiles = true) : pays k t tiles = true := by
  unfold paysFast at h
  unfold pays
  apply List.all_eq_true.mpr
  intro tile ht
  exact decide_eq_true ((paidFast_iff k t tile).mp (of_decide_eq_true (List.all_eq_true.mp h tile ht)))

/-- Use the smaller evaluator without changing the geometric price proposition. -/
def fastBatch {k : Band} {t : ℕ} (tiles : List Tile) (h : paysFast k t tiles = true) : PaidBatch k t :=
  ⟨tiles, pays_of_fast k t tiles h⟩

end LambdaC53TiltedPrice
