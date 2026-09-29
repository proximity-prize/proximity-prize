import ProximityPrize.SubmissionLower.MovingSourceBandWiden6814

/-! Tighten a packet's total envelope using its actual carrier weight.
The code-degree bound and selected seeds are unchanged. This is needed
when the eligible Z source is selected by actual total degree. -/
namespace ProximityPrize.SubmissionLower.MovingSourceBandGeometry6814.Packet
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 20000
open RCN095 RCN135 RCN136 RCN156 RCN234 RCN275 LocatorHybridCells
variable {K I : Type} [Field K] [CharP K 2130706433]
variable {x : I → K} {t y r : ℕ}

def retotal (P : Packet x t y r) (t' : ℕ)
    (hcap : wt residualTotalWeights P.F≤t') (hyt : y≤t') (hthi : t'≤3578) : Packet x t' y r :=
  {P with yt := hyt, thigh := hthi
          box := by
            intro e he
            have hh := P.box he
            have hw : e 1+e 2+e 3≤t' := by
              simpa [RCN081.weight_fin4,residualTotalWeights] using
                (MvPolynomial.le_weightedTotalDegree residualTotalWeights he).trans hcap
            exact ⟨by omega,hh.2.1,hh.2.2⟩
          support := by
            have hr := P.rlow
            have hy := P.ylow
            have hhR := P.r_weight
            have hhY := P.y_weight
            constructor <;> dsimp [cellSupport,RCN198.support,cellA,cellB,cellS] <;> omega}

#print axioms retotal
end
end ProximityPrize.SubmissionLower.MovingSourceBandGeometry6814.Packet
