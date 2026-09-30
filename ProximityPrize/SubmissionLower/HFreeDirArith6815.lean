import ProximityPrize.SubmissionLower.MovingFiberArithmeticBase6815
import ProximityPrize.SubmissionLower.HFreeDir6813
namespace ProximityPrize.SubmissionLower.HFreeDirArith6815
open scoped BigOperators
open RCN095 RCN146 RCN260 RCN294 RCN327 LocatorHybridCells LocatorHybridCellsC1
open MovingFiberProfile6815 MovingFiberThreeSources6811 MovingFiberRegularData6815
open MovingFiberArithmeticBase6815
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

def numberDir (cfg : Fin 3 → Params) (scale t y r : ℕ) (f : FlagDegree) : ℕ :=
  ∑ j : Fin 3, (scale/3*weight (BoundaryTailProvider.cellNormal t y r) j*
      flagMixed f (HFreeDir6813.hfreeFirstDir t y r j) (direction j) +
    (4*(w+1)*weight (BoundaryTailProvider.cellNormal t y r) j*(scale/(3*(cfg j).d))+
      65539*weight (MovingFiberRetainedStage6811.rawFirstFlag t y r) j*(scale/(cfg j).d))*
      flagMixed f (direction j) (cfg j).flag)

def firstDir (j : Fin 3) (a b c : ℕ) : FlagDegree :=
  HFreeDir6813.hfreeFirstDir (a+3+(b+2)+c) (a+3+(b+2)) (a+3) j

def firstLo (j : Fin 3) (b c : ℕ) : FlagDegree :=
  ![⟨262144*c, 262144*b, 3⟩, ⟨262144*c, 262144*b+393216, 3⟩,
    ⟨262144*c, 262144*b+131072, 262147⟩] j

def firstHi (j : Fin 3) (a b c : ℕ) : FlagDegree :=
  ![⟨262144*c, 262144*b+131072, 262144*a+131075⟩, ⟨262144*c, 262144*b+524288, 262144*a+131075⟩,
    ⟨262144*c, 262144*b+131072, 262144*a+524291⟩] j

theorem firstDir_zero (j : Fin 3) (b c : ℕ) : firstDir j 0 b c = firstLo j b c := by
  rw [HFreeDir6813.flag_eq_iff]
  fin_cases j <;>
    simp [firstDir, firstLo, HFreeDir6813.hfreeFirstDir, HFreeDir6813.hfreeFlagDir,
      HFreeDir6813.cuspFlag, unitAllFlag, RCN326.w] <;> omega

theorem firstDir_succ (j : Fin 3) (a b c : ℕ) : firstDir j (a+1) b c = firstHi j a b c := by
  rw [HFreeDir6813.flag_eq_iff]
  fin_cases j <;>
    simp [firstDir, firstHi, HFreeDir6813.hfreeFirstDir, HFreeDir6813.hfreeFlagDir,
      HFreeDir6813.cuspFlag, unitAllFlag, RCN326.w] <;> omega

def graphDir (cfg : Fin 3 → Params) (scale : ℕ) (f : FlagDegree) (a b c : ℕ) : ℕ :=
  ∑ j : Fin 3, (scale/3*weight (normal a b c) j*flagMixed f (firstDir j a b c) (direction j) +
    (524288*weight (normal a b c) j*(scale/(3*(cfg j).d))+
      65539*weight (raw a b c) j*(scale/(cfg j).d))*
      flagMixed f (direction j) (cfg j).flag)

theorem numberDir_coordinates (cfg : Fin 3 → Params) (scale : ℕ) (f : FlagDegree) (a b c : ℕ) :
    numberDir cfg scale (a+3+(b+2)+c) (a+3+(b+2)) (a+3) f = graphDir cfg scale f a b c := by
  have hy : a+3+(b+2)-(a+3) = b+2 := by omega
  have hz : a+3+(b+2)+c-(a+3+(b+2)) = c := by omega
  have hr2 : a+3-2 = a+1 := by omega
  have hb : b+2-1 = b+1 := by omega
  have hv2 : 131074*(b+2)-131072 = 131074*b+131076 := by omega
  have hn : BoundaryTailProvider.cellNormal (a+3+(b+2)+c) (a+3+(b+2)) (a+3) = normal a b c := by
    norm_num only [BoundaryTailProvider.cellNormal,BoundaryTailAlgebra.normalFlag,normal,w,hy,hz,
      hv2,FlagDegree.mk.injEq,true_and]
    omega
  have hraw : MovingFiberRetainedStage6811.rawFirstFlag (a+3+(b+2)+c) (a+3+(b+2)) (a+3) =
      raw a b c := by
    simp only [MovingFiberRetainedStage6811.rawFirstFlag,cellA,cellB,cellS,hz,hy,hb,hr2,
      RCN198.center,RCN198.direction,raw,w,unitYZFlag]
    change FlagDegree.mk (0+2*c+131071*c) (1+(2*(b+1)+1)+131071*(b+1+1))
      (0+(2*(a+1)+3)+131071*(a+1+2)) = _
    have e0 : 0+2*c+131071*c=131073*c := by ring
    have e1 : 1+(2*(b+1)+1)+131071*(b+1+1)=131073*b+262146 := by ring
    have e2 : 0+(2*(a+1)+3)+131071*(a+1+2)=131073*a+393218 := by ring
    rw [e0,e1,e2]
  have hw4 : 4*(w+1) = 524288 := rfl
  simp only [numberDir,graphDir,firstDir,hn,hraw,hw4]

end ProximityPrize.SubmissionLower.HFreeDirArith6815
