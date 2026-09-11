import ProximityPrize.SubmissionLower.BoundaryTailBaseOracle

namespace ProximityPrize.SubmissionLower.BoundaryTailShape
open RCN095 RCN146 LocatorFactorAggregate LocatorPhase6800Oracle
open LocatorHybridCostC2 LocatorHybridCells BoundaryTailBaseOracle
open BoundaryTailIdentityArithmetic Lower80788.HybridIdentityC2
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
noncomputable section

/-- Subtraction-free in the varying total-degree coordinate. The remaining
natural subtractions are constant as z varies. -/
def high (r v z : ℕ) : ℕ := newCost ⟨z,v,r⟩ z (v-1) (r-2)

theorem high_mono (r v : ℕ) : Monotone (high r v) := by
  intro a b hab
  simp only [high,newCost,newNormal,reducedABS,rationalABS,mfibABS,mcutABS,
    flagMixed,unitAllFlag,add_zOnly,add_yz,add_all,
    nsmul_zOnly,nsmul_yz,nsmul_all]
  gcongr

theorem high_affine (r v z : ℕ) :
    2*high r v (z+1) = high r v z + high r v (z+2) := by
  simp only [high,newCost,newNormal,reducedABS,rationalABS,mfibABS,mcutABS,
    flagMixed,unitAllFlag,add_zOnly,add_yz,add_all,
    nsmul_zOnly,nsmul_yz,nsmul_all]
  ring

theorem hybrid_iff (r v z : ℕ) :
    HybridAppliesC2 (rawFlag r v z) ↔ 3 ≤ r ∧ 2 ≤ v := by
  unfold HybridAppliesC2 rawFlag middle
  dsimp
  omega

theorem cost_eq_high (r v z : ℕ) (hr : 3 ≤ r) (hv : 2 ≤ v) :
    cost r v z = high r v z := by
  have ha := (hybrid_iff r v z).mpr ⟨hr,hv⟩
  unfold cost BoundaryTailOrdinary.rawCost
  rw [if_pos ha]
  simp only [rawFlag_all,rawFlag_middle,rawFlag_total]
  rw [BoundaryTailOrdinaryHigh.bound_eq_abs _ _ _ _ hr (by omega)]
  unfold high
  congr 1 <;> simp only [rawFlag,total,middle,cellA,cellB,cellS] <;> omega

theorem cost_eq_old (r v z : ℕ) (h : ¬ (3 ≤ r ∧ 2 ≤ v)) :
    cost r v z = LocatorOrdinaryZConvex.rawCost r v z := by
  have ha : ¬ HybridAppliesC2 (rawFlag r v z) := by
    simpa only [hybrid_iff] using h
  change BoundaryTailOrdinary.rawCost (rawFlag r v z) =
    LocatorHybridCost.ordinaryCostOf (rawFlag r v z)
  simp only [BoundaryTailOrdinary.rawCost,LocatorHybridCost.ordinaryCostOf,if_neg ha]

theorem cost_mono (r v : ℕ) : Monotone (cost r v) := by
  intro a b hab
  by_cases h : 3 ≤ r ∧ 2 ≤ v
  · rw [cost_eq_high r v a h.1 h.2,cost_eq_high r v b h.1 h.2]
    exact high_mono r v hab
  · rw [cost_eq_old r v a h,cost_eq_old r v b h]
    exact LocatorOrdinaryZConvex.rawCost_mono_z r v hab

theorem cost_discreteConvex (r v z : ℕ) (hr : 1 ≤ r) :
    2*cost r v (z+1) ≤ cost r v z + cost r v (z+2) := by
  by_cases h : 3 ≤ r ∧ 2 ≤ v
  · rw [cost_eq_high r v (z+1) h.1 h.2,cost_eq_high r v z h.1 h.2,
      cost_eq_high r v (z+2) h.1 h.2]
    exact (high_affine r v z).le
  · rw [cost_eq_old r v (z+1) h,cost_eq_old r v z h,cost_eq_old r v (z+2) h]
    exact LocatorOrdinaryZConvex.rawCost_discreteConvex r v z hr

def shape : BoundaryTailBaseOracle.Shape := ⟨cost_mono,cost_discreteConvex⟩

end
end ProximityPrize.SubmissionLower.BoundaryTailShape
