import ProximityPrize.SubmissionLower.Compact50Cover
import ProximityPrize.SubmissionLower.Compact54RetainedTiltedSurface

set_option Elab.async false

namespace Compact54RetainedTiltedBatch

open K1_13 (Shape)
open Final50Price (tiltedFits)
open Final50PriceCaps (Band start order allowance)
open Final50SharedPrice (tiltedSurfaceHorner tiltedSurfaceHorner_eq)
open KoalaRetainedCut (cutPrice chamberHull residualBox)
open Compact50Cover (Tile pays)

private def Sufficient (k : Band) (t : ℕ) : Tile → Prop
  | .point b j l =>
    let x : Shape := ⟨b,j,t⟩
    0 < l ∧ l ≤ order k x ∧ tiltedFits x ∧
      cutPrice x l (60*32) (tiltedSurfaceHorner x (chamberHull (residualBox (start k) l))) ≤
        allowance ((start k).t+t) k b j t
  | other => other.Paid k t

private instance (k : Band) (t : ℕ) (tile : Tile) : Decidable (Sufficient k t tile) := by
  cases tile <;> unfold Sufficient <;> infer_instance

private theorem sufficient_paid {k : Band} {t : ℕ} {tile : Tile}
    (ht : 0 < t) (h : Sufficient k t tile) : tile.Paid k t := by
  cases tile with
  | point b j l =>
    obtain ⟨hl,ho,hf,hprice⟩ := h
    let x : Shape := ⟨b,j,t⟩
    let q := chamberHull (residualBox (start k) l)
    rw [tiltedSurfaceHorner_eq x q hf ht] at hprice
    exact ⟨hl,ho,(Compact54TiltedBatch.contracted_le_tilted _ _ _ _ hf).trans hprice⟩
  | rectangle => exact h
  | mixrect => exact h
  | shared => exact h

def test (k : Band) (t : ℕ) (tiles : List Tile) : Bool :=
  if 0 < t then tiles.all (fun tile => decide (Sufficient k t tile))
  else Compact54TiltedBatch.paysTilted k t tiles

theorem paid {k : Band} {t : ℕ} {tiles : List Tile}
    (h : test k t tiles = true) : pays k t tiles = true := by
  by_cases ht : 0 < t
  · simp only [test, if_pos ht] at h
    apply List.all_eq_true.mpr
    intro tile htile
    exact decide_eq_true (sufficient_paid ht (of_decide_eq_true (List.all_eq_true.mp h tile htile)))
  · exact Compact54TiltedBatch.pays_of_tilted (by simpa only [test, if_neg ht] using h)

end Compact54RetainedTiltedBatch
