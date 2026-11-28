import ProximityPrize.SubmissionLower.Z6970H2307PointRowsCore
import ProximityPrize.SubmissionLower.Z6970H2307GateDispatchData

set_option autoImplicit false
namespace Height2307PointCertificates
open K1_13 (Shape)
open Height2307Bands (Band)
open Height2307PointRowsCore (Method Tile order book)

abbrev G := Height2307GateDispatch.G
abbrev Gated := Height2307GateDispatch.Gated
abbrev gates : Height2307PointRowsCore.Gates := ⟨G,Gated,fun _ _ => inferInstance⟩
abbrev paid := Height2307PointRowsCore.paid gates
abbrev Row := Height2307PointRowsCore.Row gates
abbrev Point := Height2307PointRowsCore.Point gates

theorem of_rows {k : Band} (rs : List (Row k))
    (rowKeys : rs.map (Height2307PointRowsCore.key gates) = Height2307PointRowsCore.keys k)
    (x : Shape) (hv : K1_13_8.Valid x) (strong : x.j≤2*x.b+x.t)
    (fit : K1_13.InBox ((Height2307Bands.start k).plus x) (Low6969Prices.fullCap 16)) :
    Point k x :=
  Height2307PointRowsCore.of_rows gates rs rowKeys x hv strong fit

export Height2307PointRowsCore (Method Tile order book)
end Height2307PointCertificates
