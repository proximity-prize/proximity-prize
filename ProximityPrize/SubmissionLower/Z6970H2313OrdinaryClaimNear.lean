import ProximityPrize.SubmissionLower.Bundle6970_447c4a38913b210a
import ProximityPrize.SubmissionLower.Bundle6970_447c4a38913b210a
import ProximityPrize.SubmissionLower.Bundle6970_447c4a38913b210a
import ProximityPrize.SubmissionLower.Bundle6970_447c4a38913b210a
import ProximityPrize.SubmissionLower.Bundle6970_447c4a38913b210a
import ProximityPrize.SubmissionLower.Bundle6970_447c4a38913b210a
import ProximityPrize.SubmissionLower.Bundle6970_447c4a38913b210a
import ProximityPrize.SubmissionLower.Bundle6970_447c4a38913b210a
import ProximityPrize.SubmissionLower.Z6970H2313OrdinarySpread

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace Research6970.Height2313.OrdinaryClaimNear
open _root_.Lower6960
open Research6969
open Far6969RescueGeometry (Model Family)
open K1_14_1 (PoleData CRTLift poleProduct MarkResidues)
open K1 (K I)
open K1_14 (L)
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000
theorem catalogue:Research6970.Height2313.OrdinaryComplete.Catalogue 2308 2313 Research6970.Height2313.OrdinaryBooks.near 351:=by
  intro b a lo hi
  fin_cases b
  · exact Research6970.Height2313.OrdRouteNear0.allDegrees a lo hi
  · exact Research6970.Height2313.OrdRouteNear1.allDegrees a lo hi
  · exact Research6970.Height2313.OrdRouteNear2.allDegrees a lo hi
  · exact Research6970.Height2313.OrdRouteNear3.allDegrees a lo hi
  · exact Research6970.Height2313.OrdRouteNear4.allDegrees a lo hi
  · exact Research6970.Height2313.OrdRouteNear5.allDegrees a lo hi
  · exact Research6970.Height2313.OrdRouteNear6.allDegrees a lo hi
  · exact Research6970.Height2313.OrdRouteNear7.allDegrees a lo hi
theorem small:OrdinaryPackets.prices Research6970.Height2313.OrdinaryBooks.near 21=true:=by decide +kernel
theorem count {u del} {M:Model u del} {Γ} (F:Family M Γ) {D:PoleData M.overhead.toNat} (Crt:CRTLift D)
    (P:Prefix6969Early.Packet F Crt 237500000000000000 133994566145700 1810000000000 351 6143)
    (lo : 2308 ≤ M.overhead.toNat) (upper : M.overhead.toNat ≤ 2313)
    (noPole:∀i:I,(poleProduct D).eval (algebraMap K L (K1.node i))≠0)
    (res:∀z∈Γ,MarkResidues D (M.label z) (F.scalar z)) : Γ.card≤274779381266040419 :=
  Research6970.Height2313.OrdinaryComplete.count Spread2313.graph_above_twenty_one catalogue small (by decide) F Crt P lo upper noPole res
end Research6970.Height2313.OrdinaryClaimNear
