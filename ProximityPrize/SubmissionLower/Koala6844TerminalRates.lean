import ProximityPrize.SubmissionLower.Koala6844TerminalRaw
import ProximityPrize.SubmissionLower.Koala6844ReceiptsPrice


namespace ProximityPrize.SubmissionLower.Koala6844Terminal

open RCN095 RCN198 RCN263 RCN287 LocatorHybridCells
open Koala6844Receipts

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 12000

def geometryFlag (a : FlagIncrements) : FlagDegree := ⟨a.total,a.middle,a.slope⟩

def increments (f : FlagDegree) : FlagIncrements := ⟨f.zOnly,f.yz,f.all⟩

@[simp] theorem geometryFlag_increments (f : FlagDegree) : geometryFlag (increments f) = f := by
  cases f
  rfl

theorem dot_mixed_eq (a b c : FlagIncrements) :
    dot a (FlagIncrements.map (fun i => mixedRate i b c)) =
      flagMixed (geometryFlag a) (geometryFlag b) (geometryFlag c) := by
  simp only [dot,FlagIncrements.map,mixedRate,geometryFlag,flagMixed,
    Nat.reduceEqDiff, ite_true, ite_false]
  ring

private theorem support_shape (f : Flag) (hr : 3 ≤ f.r) (hy : f.r+2 ≤ f.y) (ht : f.y ≤ f.t) :
    (cellSupport f.t f.y f.r).s = f.r ∧ (cellSupport f.t f.y f.r).ys = f.y ∧
      (cellSupport f.t f.y f.r).total = f.t := by
  simp only [cellSupport,RCN198.support,cellA,cellB,cellS]
  omega

private theorem first_eq (f : Flag) (hr : 3 ≤ f.r) (hy : f.r+2 ≤ f.y) (ht : f.y ≤ f.t) :
    cellFirstTail f.t f.y f.r = geometryFlag (earlyCut f) := by
  obtain ⟨hs, hys, htot⟩ := support_shape f hr hy ht
  have hs' : 2 * f.r - 2 = 2 * (f.r - 1) := by omega
  apply flag_ext <;>
    simp only [cellFirstTail, reducedResidualAgreementFlag, reducedAgreementDirection,
      hs,hys,htot,hs',RCN327.w,earlyCut,geometryFlag,Koala6844Receipts.degree] <;> ring

private theorem normal_eq (f : Flag) :
    BoundaryTailProvider.cellNormal f.t f.y f.r = geometryFlag (normalCut f) := by
  simp only [BoundaryTailProvider.cellNormal, BoundaryTailAlgebra.normalFlag,
    RCN327.w, Koala6844Receipts.degree, geometryFlag, normalCut]

private theorem moving_eq (f : Flag) (hr : 3 ≤ f.r) (hy : f.r+2 ≤ f.y) :
    cellMovingFiber f.t f.y f.r = geometryFlag ⟨f.t-f.y,f.y-f.r,f.r+1⟩ := by
  apply flag_ext <;>
    simp only [cellMovingFiber,RCN206.fiberFlag,cellA,cellB,cellS,geometryFlag] <;> omega

private theorem moving_cut_eq (f : Flag) (hr : 3 ≤ f.r) (hy : f.r+2 ≤ f.y) :
    cellMovingCut f.t f.y f.r = geometryFlag (rawMovingCut f) := by
  have hrat : cellRational f.t f.y f.r =
      Lower80788.HybridIdentityC2.rationalABS (cellA f.t f.y) (cellB f.y f.r) (cellS f.r) :=
    SecondJetIdentity.cell_normal_eq f.t f.y f.r
  apply flag_ext <;>
    simp only [cellMovingCut,hrat,Lower80788.HybridIdentityC2.rationalABS,cellA,cellB,cellS,
      geometryFlag,rawMovingCut,RCN327.w,Koala6844Receipts.degree,add_zOnly,add_yz,add_all] <;> omega

private theorem safe_of_projection (f : Flag) (hr : 3 ≤ f.r) (hy : f.r + 2 ≤ f.y)
    (hearly : f.r * (earlyCut f).middle + f.y * (earlyCut f).slope < prime)
    (hsharp : f.r * ((2*(f.y-f.r)-1)*degree+1) + f.y * (2*f.r-1)*degree < prime) :
    BoundaryTailGates6808.Safe f.r f.y := by
  let g : Flag := ⟨f.r,f.y,f.y⟩
  obtain ⟨hs,hys,_⟩ := support_shape g hr hy (by rfl)
  have hfirst := first_eq g hr hy (by rfl)
  simp only [g] at hs hys
  have hmid : (sharpResidualAgreementFlag (cellSupport f.y f.y f.r) RCN327.w).yz =
      (2*(f.y-f.r)-1)*degree+1 := by
    simp only [sharpResidualAgreementFlag,sharpAgreementDirection,hs,hys,RCN327.w,degree]
    omega
  have hslope : (sharpResidualAgreementFlag (cellSupport f.y f.y f.r) RCN327.w).all =
      (2*f.r-1)*degree := by
    simp only [sharpResidualAgreementFlag,sharpAgreementDirection,hs,RCN327.w,degree]
  constructor
  · change f.r * (cellFirstTail g.t g.y g.r).yz + f.y * (cellFirstTail g.t g.y g.r).all < _
    rw [hfirst]
    exact hearly
  · rw [hmid,hslope]
    have hassoc : f.y * (2 * f.r - 1) * degree = f.y * ((2 * f.r - 1) * degree) := Nat.mul_assoc _ _ _
    simpa only [hassoc, Koala6844Receipts.prime] using hsharp

theorem graphGates_of_goodGraph (f : Flag) (hr : 3 ≤ f.r) (hy : f.r + 2 ≤ f.y)
    (h : goodGraph f = true) : GraphGates f.t f.y f.r := by
  have h' := of_decide_eq_true h
  exact ⟨h'.1,h'.2.1,safe_of_projection f hr hy h'.2.2.1 h'.2.2.2.1⟩

def rawRatesAt (f : Flag) : FlagIncrements :=
  FlagIncrements.map fun i => mixedRate i (earlyCut f) (normalCut f) +
    65539 * mixedRate i ⟨f.t-f.y,f.y-f.r,f.r+1⟩ (rawMovingCut f)

theorem rawRates_eq_bound (f : Flag) (hr : 3 ≤ f.r) (hy : f.r+2 ≤ f.y) (ht : f.y ≤ f.t)
    (left : FlagDegree) :
    dot (increments left) (rawRatesAt f) = MovingFiberOrdinaryHigh6815.bound left f.t f.y f.r := by
  rw [show dot (increments left) (rawRatesAt f) =
      dot (increments left) (FlagIncrements.map (fun i => mixedRate i (earlyCut f) (normalCut f))) +
        65539 * dot (increments left) (FlagIncrements.map (fun i =>
          mixedRate i ⟨f.t-f.y,f.y-f.r,f.r+1⟩ (rawMovingCut f))) by
    simp only [rawRatesAt,FlagIncrements.map,dot]
    ring]
  simp only [dot_mixed_eq,geometryFlag_increments, ← first_eq f hr hy ht, ← normal_eq f,
    ← moving_eq f hr hy, ← moving_cut_eq f hr hy, MovingFiberOrdinaryHigh6815.bound]

end ProximityPrize.SubmissionLower.Koala6844Terminal
