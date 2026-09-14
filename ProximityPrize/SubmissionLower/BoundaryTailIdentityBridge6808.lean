import ProximityPrize.SubmissionLower.BoundaryTailFixedStage6808
import ProximityPrize.SubmissionLower.DualCutBridge6807Arithmetic

namespace ProximityPrize.SubmissionLower.BoundaryTailIdentityBridge6808
open RCN095 RCN146 RCN327
open LocatorHybridCells LocatorHybridCellsC1
open BoundaryTailProvider BoundaryTailFixedStage6808
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def toTri (f : FlagDegree) : DualCutBridge6807Arithmetic.Tri :=
  ⟨f.zOnly, f.yz, f.all⟩

theorem mixed_toTri (f q u : FlagDegree) :
    DualCutBridge6807Arithmetic.mixed (toTri f) (toTri q) (toTri u) =
      flagMixed f q u := by
  simp only [toTri, DualCutBridge6807Arithmetic.mixed, flagMixed]
  ring

/-- Translate the subtraction-free paper certificate to the actual Stage flags. -/
theorem numerator_d6_coordinates (f : FlagDegree) (a b c : ℕ) :
    dualNumerator f (a+3+(b+2)+c) (a+3+(b+2)) (a+3) 6 ⟨1620,133,52⟩ =
      DualCutBridge6807Arithmetic.graphNumerator (toTri f) 6 1620 133 52 a b c := by
  have hy : a+3+(b+2)-(a+3) = b+2 := by omega
  have hz : a+3+(b+2)+c-(a+3+(b+2)) = c := by omega
  have hr1 : a+3-1 = a+2 := by omega
  have hr2 : a+3-2 = a+1 := by omega
  have hv1 : 131070*(b+2)-131071 = 131070*b+131069 := by
    calc
      _ = (131070*b+131069)+131071-131071 := by congr 1 <;> ring
      _ = _ := Nat.add_sub_cancel _ _
  have hv2 : 131074*(b+2)-131072 = 131074*b+131076 := by
    calc
      _ = (131074*b+131076)+131072-131072 := by congr 1 <;> ring
      _ = _ := Nat.add_sub_cancel _ _
  norm_num only [dualNumerator, ActualFirstCutPole6807.firstBaseFlag,
    cellNormal, BoundaryTailAlgebra.normalFlag, RCN327.w, hy, hz, hr1, hr2]
  simp only [hv1, hv2, add_zOnly, add_yz, add_all, nsmul_zOnly, nsmul_yz, nsmul_all,
    flagMixed, toTri, DualCutBridge6807Arithmetic.graphNumerator,
    DualCutBridge6807Arithmetic.mixed, DualCutBridge6807Arithmetic.firstFlag,
    DualCutBridge6807Arithmetic.secondFlag]
  ring

theorem identity_degree_coordinates (f : FlagDegree) (a b c : ℕ) :
    identityCurveDegree f (cellA (a+3+(b+2)+c) (a+3+(b+2)))
      (cellB (a+3+(b+2)) (a+3)) (cellS (a+3)) w =
      DualCutBridge6807Arithmetic.identityDegree (toTri f) a b c := by
  change identityCurveDegree f _ _ _ Lower80788.HybridIdentityC2.w = _
  rw [Lower80788.HybridIdentityC2.identityDegree_linear]
  have ha : cellA (a+3+(b+2)+c) (a+3+(b+2)) = c := by dsimp [cellA]; omega
  have hb : cellB (a+3+(b+2)) (a+3) = b+1 := by dsimp [cellB]; omega
  have hs : cellS (a+3) = a+1 := by dsimp [cellS]; omega
  rw [ha,hb,hs]
  simp only [DualCutBridge6807Arithmetic.identityDegree,toTri]
  ring

def newSlackZ (a b c : ℕ) : ℕ :=
    31074054019586640*a^2 +
    62148108039173280*a*b +
    1492581956935076160*a +
    497191028263698864*b +
    9841646074620153840

def newSlackV (a b c : ℕ) : ℕ :=
    31074054019586640*a^2 +
    62148108039173280*a*b +
    62148108039173280*a*c +
    13977780387554688072*a +
    497191028263698864*b +
    497191028263698864*c +
    103282985074091340660

def newSlackR (a b c : ℕ) : ℕ :=
    31074054019586640*a^2 +
    62148108039173280*a*b +
    62148108039173280*a*c +
    13977780387554688072*a +
    31074054019586640*b^2 +
    62148108039173280*b*c +
    13977780387554688072*b +
    1492581956935076160*c +
    310252507904959633793

theorem absorption_new (p : DualCutBridge6807Arithmetic.Tri) (a b c : ℕ) :
    36*131073*80831*DualCutBridge6807Arithmetic.identityDegree p a b c ≤
      50243*DualCutBridge6807Arithmetic.graphNumerator p 6 1620 133 52 a b c := by
  have h : 50243*DualCutBridge6807Arithmetic.graphNumerator p 6 1620 133 52 a b c =
      36*131073*80831*DualCutBridge6807Arithmetic.identityDegree p a b c +
      (p.z*newSlackZ a b c+p.v*newSlackV a b c+p.r*newSlackR a b c) := by
    simp only [DualCutBridge6807Arithmetic.graphNumerator, DualCutBridge6807Arithmetic.identityDegree,
      DualCutBridge6807Arithmetic.mixed, DualCutBridge6807Arithmetic.firstFlag,
      DualCutBridge6807Arithmetic.secondFlag, newSlackZ, newSlackV, newSlackR]
    ring
  rw [h]
  exact Nat.le_add_right _ _

/-- Uniform identity-branch payment for the actual sixfold-root source.
No geometric incidence or final intersection bound is assumed. -/
theorem identity_absorption_d6 (f : FlagDegree) (t y r : ℕ)
    (hr : 3 ≤ r) (hy : r+2 ≤ y) (ht : y ≤ t) :
    36 * 131073 * 80831 * identityCurveDegree f (cellA t y) (cellB y r) (cellS r) w ≤
      50243 * dualNumerator f t y r 6 ⟨1620,133,52⟩ := by
  obtain ⟨a,rfl⟩ : ∃ a, r = a+3 := ⟨r-3,by omega⟩
  obtain ⟨b,rfl⟩ : ∃ b, y = a+3+(b+2) := ⟨y-(a+3)-2,by omega⟩
  obtain ⟨c,rfl⟩ : ∃ c, t = a+3+(b+2)+c := ⟨t-(a+3+(b+2)),by omega⟩
  rw [identity_degree_coordinates,numerator_d6_coordinates]
  exact absorption_new (toTri f) a b c

end ProximityPrize.SubmissionLower.BoundaryTailIdentityBridge6808
