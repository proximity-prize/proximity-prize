import ProximityPrize.SubmissionLower.Koala6844TerminalHelper
import ProximityPrize.SubmissionLower.Koala6844TerminalRates


namespace ProximityPrize.SubmissionLower.Koala6844Terminal

open RCN095 RCN198 RCN263 RCN327 LocatorHybridCells
open Koala6831MovingPairIncidence Koala6844Receipts

set_option autoImplicit false
set_option maxRecDepth 28000
set_option maxHeartbeats 2800000

private theorem support_shape (g : Flag) (hr : 3 ≤ g.r) (hy : g.r+2 ≤ g.y) (ht : g.y ≤ g.t) :
    (cellSupport g.t g.y g.r).s = g.r ∧ (cellSupport g.t g.y g.r).ys = g.y ∧
      (cellSupport g.t g.y g.r).total = g.t := by
  simp only [cellSupport,RCN198.support,cellA,cellB,cellS]
  omega

theorem graphDirection_eq_scaled (g : Flag) (hr : 3 ≤ g.r) (hy : g.r+2 ≤ g.y) (ht : g.y ≤ g.t) :
    geometryFlag (graphDirection g) = (graphScale / geometryScale) •
      scaledPairFlag (cellSupport g.t g.y g.r) 262144 w 180961 81183 := by
  obtain ⟨hs,hys,htot⟩ := support_shape g hr hy ht
  have hs' : 2*g.r - 2 = 2*(g.r-1) := by omega
  have ha : graphScale / agreements = graphScale / geometryScale * 49890 := by decide
  have hg : graphScale / agreementGap = graphScale / geometryScale * 180961 := by decide
  have hscale : graphScale = graphScale / geometryScale * (180961 * 49890) := by decide
  have hnodes : nodes=262144 := by decide
  have hdegree : Koala6844Receipts.degree=131071 := by decide
  have hpenc : pencilLimit=81184 := by decide
  apply flag_ext <;>
    simp only [graphDirection,geometryFlag,scaledPairFlag,reducedAgreementDirection,hs,hys,htot,hs',
      unitYZFlag,unitZFlag,add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all,
      RCN327.w,ha,hg,hnodes,hdegree,hpenc,Nat.reduceSub,Nat.reduceAdd,mul_zero,add_zero,mul_one]
  · generalize graphScale / geometryScale = q at hscale ⊢
    rw [hscale]
    ring
  · ring
  · ring

theorem scaled_pair_to_receipt (g : Flag) (hr : 3 ≤ g.r) (hy : g.r+2 ≤ g.y) (ht : g.y ≤ g.t)
    (left : FlagDegree) (right : FlagIncrements) (count : ℕ)
    (hcount : count * (180961 * 49890) ≤ flagMixed left (geometryFlag right)
      (scaledPairFlag (cellSupport g.t g.y g.r) 262144 w 180961 81183)) :
    graphScale * count ≤ dot (increments left)
      (FlagIncrements.map (fun j => mixedRate j right (graphDirection g))) := by
  rw [dot_mixed_eq,geometryFlag_increments,graphDirection_eq_scaled g hr hy ht]
  let d := scaledPairFlag (cellSupport g.t g.y g.r) 262144 w 180961 81183
  have he : flagMixed left (geometryFlag right) ((graphScale/geometryScale) • d) =
      (graphScale/geometryScale) * flagMixed left (geometryFlag right) d := by
    simp only [flagMixed,nsmul_zOnly,nsmul_yz,nsmul_all]
    ring
  have hscale : graphScale = (graphScale / geometryScale) * (180961 * 49890) := by decide
  calc
    _ = (graphScale / geometryScale) * (count * (180961 * 49890)) := by rw [hscale]; ac_rfl
    _ ≤ (graphScale / geometryScale) * flagMixed left (geometryFlag right) d := Nat.mul_le_mul_left _ hcount
    _ = _ := he.symm

end ProximityPrize.SubmissionLower.Koala6844Terminal
