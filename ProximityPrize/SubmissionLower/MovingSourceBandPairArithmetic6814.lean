import ProximityPrize.SubmissionLower.MovingSourceJointPairBudget6814
import ProximityPrize.SubmissionLower.MovingSourcePairStageSupplier6814

/-! Preserve the coupled U/V estimate through the actual Stage ledger.
In particular no false separate bound on U is used to spend the joint
same-source saving. -/
namespace ProximityPrize.SubmissionLower.MovingSourceBandPairArithmetic6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open scoped BigOperators
open RCN095 BoundaryTailProvider MovingFiberThreeSources6811 MovingFiberRetainedStage6811
open MovingSourcePairRetainedStage6814 MovingSourcePairStageSupplier6814 MovingSourceCoupledClearing6814

def coefficient (t y r : ℕ) (j : Fin 3) : ℕ :=
  4*(RCN326.w+1)*weight (cellNormal t y r) j+3*65539*weight (rawFirstFlag t y r) j

def fixedNumerator (t y r : ℕ) (p : FlagDegree) : ℕ :=
  ∑ j : Fin 3, weight (cellNormal t y r) j*
    flagMixed p (HFreeDir6813.hfreeFirstDir t y r j) (direction j)

theorem pairNumerator_eq (scale z u v t y r : ℕ) (p : FlagDegree) :
    pairNumerator scale z u v t y r p=
      scale*fixedNumerator t y r p+coefficient t y r 0*z+
      coefficient t y r 1*u+coefficient t y r 2*v := by
  simp only [pairNumerator,fixedNumerator,coefficient,price,weight,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,
    Function.comp_apply,Matrix.cons_val_succ]
  ring

def pricedPair {K : Type} [Field K] {F : MvPolynomial (Fin 4) K}
    (SZ : Source F) (delta u v t y r : ℕ) : ℕ :=
  pairNumerator (SZ.d*delta) (delta*flagMixed ⟨t-y,y-r,r⟩ unitZFlag SZ.flag)
    (SZ.d*u) (SZ.d*v) t y r ⟨t-y,y-r,r⟩/(3*(SZ.d*delta))

theorem pairStageCost_le_weighted {K : Type} [Field K] {F : MvPolynomial (Fin 4) K}
    (SZ SP SQ : Source F) (delta u v t y r : ℕ)
    (hprice : coefficient t y r 1*flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag+
      coefficient t y r 2*flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitAllFlag≤
      coefficient t y r 1*u+coefficient t y r 2*v) :
    pairStageCost SZ SP SQ delta t y r ⟨t-y,y-r,r⟩≤pricedPair SZ delta u v t y r := by
  unfold pairStageCost pricedPair stageScale
  apply Nat.div_le_div_right
  rw [pairNumerator_eq,pairNumerator_eq]
  have hh := Nat.mul_le_mul_left SZ.d hprice
  nlinarith

theorem pairStageCost_le_joint {K : Type} [Field K] {F : MvPolynomial (Fin 4) K}
    (SZ SP SQ : Source F) (t y r : ℕ)
    (hp : 2≤(ordinaryFlag SP.P).all) (hq : 2≤(ordinaryFlag SQ.P).all)
    (hr : (ordinaryFlag SP.P).all+(ordinaryFlag SQ.P).all≤31)
    (hy : (ordinaryFlag SP.P).yz+(ordinaryFlag SP.P).all+
      (ordinaryFlag SQ.P).yz+(ordinaryFlag SQ.P).all≤112)
    (ht : (ordinaryFlag SP.P).zOnly+(ordinaryFlag SP.P).yz+(ordinaryFlag SP.P).all+
      (ordinaryFlag SQ.P).zOnly+(ordinaryFlag SQ.P).yz+(ordinaryFlag SQ.P).all≤1009)
    (hc : coefficient t y r 1≤5*coefficient t y r 2) :
    pairStageCost SZ SP SQ 1 t y r ⟨t-y,y-r,r⟩≤pricedPair SZ 1 26233 98890 t y r := by
  have hj := MovingSourceJointPairBudget6814.joint_pair_bound _ _ hp hq hr hy ht
  have hv := (UniqueCurvatureOwner6814.small_source_pair_prices _ _ hp hq hr hy ht).2.2
  exact pairStageCost_le_weighted SZ SP SQ 1 26233 98890 t y r
    (MovingSourceJointPairBudget6814.weighted_joint_bound _ _ _ _ hj hv hc)

#print axioms pairStageCost_le_weighted
#print axioms pairStageCost_le_joint
end
end ProximityPrize.SubmissionLower.MovingSourceBandPairArithmetic6814
