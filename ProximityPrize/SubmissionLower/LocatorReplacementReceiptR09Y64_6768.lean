import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y64C4_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r09_y64:∀ b:Fin 160,
    Receipt ((⟨8,by decide⟩:Fin 17),(⟨64,by decide⟩:Fin 79),b):=by
  intro b
  by_cases h0:b.val<32
  · exact receipt_r09_y64_c0 b h0
  by_cases h1:b.val<64
  · exact receipt_r09_y64_c1 b (by omega) h1
  by_cases h2:b.val<96
  · exact receipt_r09_y64_c2 b (by omega) h2
  by_cases h3:b.val<128
  · exact receipt_r09_y64_c3 b (by omega) h3
  · exact receipt_r09_y64_c4 b (by omega) (by omega)
end ProximityPrize.SubmissionLower.LocatorReplacementData
