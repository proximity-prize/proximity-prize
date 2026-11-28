import ProximityPrize.SubmissionLower.Z6970PlateauChunk
import ProximityPrize.SubmissionLower.Z6970PlateauPriceRow500

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace ExpandedPlateauSum6970

theorem oneChunk500 : chunk 500 1 = 27208296914 := (chunk_one 500).trans priceRow500

end ExpandedPlateauSum6970
