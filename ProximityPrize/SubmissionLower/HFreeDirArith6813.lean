import ProximityPrize.SubmissionLower.MovingFiberArithmeticBase6811
import ProximityPrize.SubmissionLower.HFreeDir6813

/-!
# Per-direction H-free first cut: the arithmetic interface

The catalog form of `HFreeDir6813.numeratorDir`, for the generated receipts.  With
`r = a+3`, `v = b+2`, `z = c`:

* `numberDir` is `numeratorDir` over catalog parameters (`MovingFiberProfile6811.number`
  with the per-direction first cut), and `numberDir_coordinates` turns it into `graphDir`;
* `firstDir j a b c` is the first flag of direction `j`; it is polynomial on each of the regimes
  `r = 3` (`firstLo`) and `r ≥ 4` (`firstHi`, in `a-1`);
* `graphDir ≤ graph`, so the shipped receipts also cover `graphDir`.
-/

namespace ProximityPrize.SubmissionLower.HFreeDirArith6813
open scoped BigOperators
open RCN095 RCN146 RCN260 RCN294 RCN327 LocatorHybridCells LocatorHybridCellsC1
open MovingFiberProfile6811 MovingFiberThreeSources6811 MovingFiberRegularData6811
open MovingFiberArithmeticBase6811
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

/-- `MovingFiberProfile6811.number` with the per-direction first cut; it is
`HFreeDir6813.numeratorDir` of the catalog sources. -/
def numberDir (cfg : Fin 3 → Params) (scale t y r : ℕ) (f : FlagDegree) : ℕ :=
  ∑ j : Fin 3, (scale/3*weight (BoundaryTailProvider.cellNormal t y r) j*
      flagMixed f (HFreeDir6813.hfreeFirstDir t y r j) (direction j) +
    (4*(w+1)*weight (BoundaryTailProvider.cellNormal t y r) j*(scale/(3*(cfg j).d))+
      65539*weight (MovingFiberRetainedStage6811.rawFirstFlag t y r) j*(scale/(cfg j).d))*
      flagMixed f (direction j) (cfg j).flag)

/-- The first flag of direction `j` at `r = a+3`, `v = b+2`, `z = c`. -/
def firstDir (j : Fin 3) (a b c : ℕ) : FlagDegree :=
  HFreeDir6813.hfreeFirstDir (a+3+(b+2)+c) (a+3+(b+2)) (a+3) j

/-- `firstDir` at `r = 3`. -/
def firstLo (j : Fin 3) (b c : ℕ) : FlagDegree :=
  ![⟨262144*c, 262144*b, 3⟩, ⟨262144*c, 262144*b+393216, 3⟩,
    ⟨262144*c, 262144*b+131072, 262147⟩] j

/-- `firstDir` at `r = a+4`. -/
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

/-- `graph` with the per-direction first cut. -/
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

/-- The per-direction first cut is below the shipped one on every cell. -/
theorem numberDir_le_number (cfg : Fin 3 → Params) (scale t y r : ℕ) (hr : 3 ≤ r) (hb : r+2 ≤ y)
    (f : FlagDegree) : numberDir cfg scale t y r f ≤ number cfg scale t y r f := by
  have hmixed : flagMixed f (MovingFiberRetainedStage6811.hfreeFirst t y r)
      (BoundaryTailProvider.cellNormal t y r) =
      ∑ j : Fin 3, weight (BoundaryTailProvider.cellNormal t y r) j *
        flagMixed f (MovingFiberRetainedStage6811.hfreeFirst t y r) (direction j) := by
    simp only [Fin.sum_univ_three, weight, direction, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
      Matrix.cons_val_succ, flagMixed, unitZFlag, unitYZFlag, unitAllFlag]
    ring
  unfold numberDir number
  rw [hmixed, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => Nat.add_le_add_right ?_ _
  obtain ⟨h1, h2, h3⟩ := HFreeDir6813.hfreeFirstDir_le t y r hr hb j
  have hm := HFreeDir6813.flagMixed_mono_mid f _ _ (direction j) h1 h2 h3
  calc scale/3*weight (BoundaryTailProvider.cellNormal t y r) j*
        flagMixed f (HFreeDir6813.hfreeFirstDir t y r j) (direction j)
      ≤ scale/3*weight (BoundaryTailProvider.cellNormal t y r) j*
        flagMixed f (MovingFiberRetainedStage6811.hfreeFirst t y r) (direction j) :=
        Nat.mul_le_mul_left _ hm
    _ = _ := by ring

/-- The shipped receipts (`graph`) also bound `graphDir`. -/
theorem graphDir_le_graph (cfg : Fin 3 → Params) (scale : ℕ) (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f a b c ≤ graph cfg scale f a b c := by
  rw [← numberDir_coordinates, ← number_coordinates]
  exact numberDir_le_number cfg scale _ _ _ (by omega) (by omega) f

end ProximityPrize.SubmissionLower.HFreeDirArith6813
