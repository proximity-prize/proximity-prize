import ProximityPrize.SubmissionLower.Z6970PlateauLines
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
namespace ExpandedPlateauSum6970
theorem priceRow500 : row 500 = 27208296914 := by decide +kernel
end ExpandedPlateauSum6970
