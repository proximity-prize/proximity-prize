import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR08Y43B07_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r08_y43:∀ b:Fin 160,
    Receipt ((⟨7,by decide⟩:Fin 17),(⟨43,by decide⟩:Fin 79),b):=by
  intro b
  by_cases h0:b.val<20
  · exact receipt_r08_y43_b00 b h0
  by_cases h1:b.val<40
  · exact receipt_r08_y43_b01 b (by omega) h1
  by_cases h2:b.val<60
  · exact receipt_r08_y43_b02 b (by omega) h2
  by_cases h3:b.val<80
  · exact receipt_r08_y43_b03 b (by omega) h3
  by_cases h4:b.val<100
  · exact receipt_r08_y43_b04 b (by omega) h4
  by_cases h5:b.val<120
  · exact receipt_r08_y43_b05 b (by omega) h5
  by_cases h6:b.val<140
  · exact receipt_r08_y43_b06 b (by omega) h6
  · exact receipt_r08_y43_b07 b (by omega) (by omega)
end ProximityPrize.SubmissionLower.LocatorReplacementData
