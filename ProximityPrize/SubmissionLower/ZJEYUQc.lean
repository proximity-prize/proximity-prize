import ProximityPrize.SubmissionLower.D7
import ProximityPrize.SubmissionLower.ZK3v1Id
import ProximityPrize.SubmissionLower.ZZWSERb
import ProximityPrize.SubmissionLower.ZoU8PJb
set_option Elab.async false
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
namespace TD
noncomputable section
open Polynomial

open Dt (Ls)
open cu (Jet)

open pI (oU)
open ac2
open ac3






open scoped BigOperators Classical
private theorem d1m {s :Ls} {P:Jet}
    (hb:s.free.shape.J≤ s.free.shape.B) (hc:s.moving.shape.J≤ s.moving.shape.B)
    (hP:oU P s.free.shape∨oU P s.moving.shape) :oU P (a3D s) := by
  have ha :s.free.shape.B≤(a3D s).B :=
    (Nat.sub_add_cancel hb).symm.trans_le
      (Nat.add_le_add (le_max_left _ _) (le_max_left _ _))
  have hd:s.moving.shape.B≤(a3D s).B :=
    (Nat.sub_add_cancel hc).symm.trans_le
      (Nat.add_le_add (le_max_right _ _) (le_max_right _ _))
  intro j i h
  rcases hP with hp | hp
  · obtain ⟨hg,hj,hu⟩:=hp j i h
    exact ⟨hg.trans ha,hj.trans (le_max_left _ _),hu.trans (le_max_left _ _)⟩
  · obtain ⟨hg,hj,hu⟩:=hp j i h
    exact ⟨hg.trans hd,hj.trans (le_max_right _ _),hu.trans (le_max_right _ _)⟩
end
end TD
