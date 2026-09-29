import ProximityPrize.SubmissionLower.MovingSourceLinearTailTransport6814

/-! Proved delayed-tail envelopes and the exact arithmetic target for the
linear reduced-flow counter. This file proves NO geometric cardinality
bound: the proper-delay cycle, vertical and tangent consumers must supply
the separately named terms before this can be used in a score claim. -/
namespace ProximityPrize.SubmissionLower.MovingSourceLinearBudgetTarget6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open RCN234 RCN156
open MovingSourceLinearFlow6814 MovingSourceFlowNumerator6814 MovingSourceReducedTailWeights6814

theorem delayed_tail_weights
    {K : Type} [Field K] (J : WholeSpaceCube6814.Poly (K:=K))
    (hshape : ∀ e ∈ J.support, 2*e 1+e 3≤7 ∧ e 1+e 2+e 3≤25 ∧ e 1+e 2+e 3+e 4≤331)
    (mu delay : ℕ) (hmu : 1≤mu) (hdelay : delay≤mu) :
    wt residualSWeights (numerators (linearH J) (linearG J) (131072+delay))≤1441803*mu ∧
    wt residualYSWeights (numerators (linearH J) (linearG J) (131072+delay))≤6291505*mu ∧
    wt residualTotalWeights (numerators (linearH J) (linearG J) (131072+delay))≤86508181*mu := by
  have hh := linear_tail_weights J hshape (131072+delay)
  refine ⟨hh.1.trans ?_,hh.2.1.trans ?_,hh.2.2.trans ?_⟩ <;> nlinarith

def properRectangleTarget : ℕ :=
  57*(1441792*86508181+1441803*86507521)+
  12*(6291457*86508181+6291505*86507521)+
  3561*(6291457*1441803+6291505*1441792)

def denominatorHelperTarget : ℕ :=
  (131073*((1+2*131071*57)*21765+(131071*23)*104274+(1+2*131071*3561)*573)+50184-1)/50184+
    80890*573

def constantParameterTarget : ℕ := 12*86507521+3561*1441792
def tangentTarget : ℕ := 1802898105618360

theorem budget_target_values :
    properRectangleTarget=91885113709214910 ∧
    denominatorHelperTarget=3067534234414 ∧
    constantParameterTarget=6172311564 := by decide +kernel

theorem budget_target_fits :
    properRectangleTarget+denominatorHelperTarget+constantParameterTarget+tangentTarget=
      93691085521379248 ∧
    properRectangleTarget+denominatorHelperTarget+constantParameterTarget+tangentTarget<
      272069082261391681 := by decide +kernel

#print axioms delayed_tail_weights
#print axioms budget_target_fits
end
end ProximityPrize.SubmissionLower.MovingSourceLinearBudgetTarget6814
