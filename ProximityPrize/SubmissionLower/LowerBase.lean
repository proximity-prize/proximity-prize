import ProximityPrize.SubmissionLower.GoldBranch6N7
set_option Elab.async false
set_option autoImplicit true
section
namespace P1_6
noncomputable section
open Polynomial
open P1 (I K k node agreement)
open K1_13 (Geom embed extend Row Shape shape InBox atJet OnFactor OrderAt indexDegree
  chart liftedChart mixed32 ceilDiv)
open scoped BigOperators
inductive Bank where
  | primary
  | secondary
  deriving DecidableEq
structure FatEquations where
  common : Row 3
  residual : Row 3
  common_ne : common ≠ 0
  residual_ne : residual ≠ 0
  common_total : common.totalDegree ≤ 3284
  common_index : indexDegree common ≤ 1120
  residual_total : residual.totalDegree ≤ 409200000
  residual_index : indexDegree residual ≤ 129000000
end
end P1_6
end
section
namespace P1_6
noncomputable section
open Polynomial
open P1 (K I k node AnchorModel AnchoredFamily)
open K1_13 (Geom embed extend atJet PoleData)
open scoped BigOperators
end
end P1_6
end
