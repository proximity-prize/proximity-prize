import ProximityPrize.SubmissionLower.Compact54Packed
import ProximityPrize.SubmissionLower.Compact54EmptyOrder
import ProximityPrize.SubmissionLower.Compact54PrimaryTiltedSurface

set_option Elab.async false
set_option maxHeartbeats 1000000

namespace Compact54EmptyTilt

open K1_13 (Shape ceilDiv)
open Final50Price (physicalPrice physicalPriceTilted physicalPriceWith primaryBox tiltedFits)
open Final50PriceCaps (Band allowance)
open Final50SharedPrice (Rate price additiveBase nonsharedFee primaryTiltedSurface primaryTiltedSurface_eq)
open KoalaWeightedRate (Allowed)
open Compact50Cover (Tile pays)
open Compact54EmptyOrder (Supported le_order)
open KoalaRetainedCut (cutPrice chamberHull residualBox)

private theorem physical_le {x : Shape} {l K : ℕ} (hf : tiltedFits x) :
    physicalPrice x l K ≤ physicalPriceTilted x l := by
  simp only [physicalPrice, if_pos hf]
  split
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact min_le_right _ _

private def sharedTilted (x : Shape) (l : ℕ) (u : Rate) : ℕ :=
  ceilDiv (physicalPriceWith x l (primaryTiltedSurface x) + u.split*additiveBase x l + u.split*u.amount + 1)
    (u.split+1) + nonsharedFee x l

private theorem shared_le {x : Shape} {l K : ℕ} {u : Rate} (hf : tiltedFits x) (ht : 0 < x.t) :
    price x l K u ≤ sharedTilted x l u := by
  have h : physicalPrice x l K ≤ physicalPriceTilted x l := physical_le hf
  unfold price sharedTilted ceilDiv
  rw [primaryTiltedSurface_eq x hf ht]
  have he : physicalPriceWith x l (Final50Price.tiltedSurface x.chamber primaryBox) =
      physicalPriceTilted x l := rfl
  rw [he]
  apply Nat.add_le_add_right
  apply Nat.div_le_div_right
  omega

private def Quick (t : ℕ) : Tile → Prop
  | .shared b j l u =>
    let x : Shape := ⟨b,j,t⟩
    0 < l ∧ Supported x l ∧ tiltedFits x ∧ 0 < t ∧
      sharedTilted x l u ≤ allowance t .empty b j t ∧ Allowed x u
  | .point b j l =>
    let x : Shape := ⟨b,j,t⟩
    0 < l ∧ Supported x l ∧ tiltedFits x ∧ 0 < t ∧
      cutPrice x l (60*32) (primaryTiltedSurface x) ≤ allowance t .empty b j t
  | _ => False

private instance (t : ℕ) (a : Tile) : Decidable (Quick t a) := by
  cases a <;> unfold Quick <;> infer_instance

private theorem quick_paid {t : ℕ} {a : Tile} (h : Quick t a) : a.Paid .empty t := by
  cases a with
  | point b j l =>
    obtain ⟨hl,ho,hfit,ht,hp⟩ := h
    have hbox : chamberHull (residualBox (Final50PriceCaps.start .empty) l) = primaryBox := by
      simp only [Final50PriceCaps.start, residualBox, Nat.mul_zero, Nat.sub_zero] <;> rfl
    rw [primaryTiltedSurface_eq _ hfit ht, ← hbox] at hp
    refine ⟨hl,le_order ho,?_⟩
    simpa only [Final50PriceCaps.start, Nat.zero_add] using
      (Compact54TiltedBatch.contracted_le_tilted ⟨b,j,t⟩ (Final50PriceCaps.start .empty)
        l (Final50PriceCaps.activeCap .empty) hfit).trans hp
  | shared b j l u =>
    obtain ⟨hl,ho,hfit,ht,hp,ha⟩ := h
    exact ⟨rfl,hl,le_order ho,ha,(shared_le hfit ht).trans hp⟩
  | rectangle => exact False.elim h
  | mixrect => exact False.elim h

def test (t : ℕ) (tiles : List Tile) : Bool :=
  tiles.all fun a => decide (Quick t a ∨ a.Paid .empty t)

theorem paid {t : ℕ} {tiles : List Tile} (h : test t tiles = true) : pays .empty t tiles = true := by
  apply List.all_eq_true.mpr
  intro a ha
  exact decide_eq_true ((of_decide_eq_true (List.all_eq_true.mp h a ha)).elim quick_paid id)

end Compact54EmptyTilt
