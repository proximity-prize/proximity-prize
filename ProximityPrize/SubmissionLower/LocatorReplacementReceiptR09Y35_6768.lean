import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR09Y35B07_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r09_y35:∀ b:Fin 160,
    Receipt ((⟨8,by decide⟩:Fin 17),(⟨35,by decide⟩:Fin 79),b):=by
  intro b
  by_cases h0:b.val<20
  · exact receipt_r09_y35_b00 b h0
  by_cases h1:b.val<40
  · exact receipt_r09_y35_b01 b (by omega) h1
  by_cases h2:b.val<60
  · exact receipt_r09_y35_b02 b (by omega) h2
  by_cases h3:b.val<80
  · exact receipt_r09_y35_b03 b (by omega) h3
  by_cases h4:b.val<100
  · exact receipt_r09_y35_b04 b (by omega) h4
  by_cases h5:b.val<120
  · exact receipt_r09_y35_b05 b (by omega) h5
  by_cases h6:b.val<140
  · exact receipt_r09_y35_b06 b (by omega) h6
  · exact receipt_r09_y35_b07 b (by omega) (by omega)
end ProximityPrize.SubmissionLower.LocatorReplacementData
