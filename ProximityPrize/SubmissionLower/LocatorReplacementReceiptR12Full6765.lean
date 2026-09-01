import ProximityPrize.SubmissionLower.LocatorReplacementReceiptR12G9_6768
namespace ProximityPrize.SubmissionLower.LocatorReplacementData
open LocatorReplacementGrid
set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000
theorem receipt_r12_full:
    ∀ y:Fin 79,∀ b:Fin 160,
      Receipt ((⟨11,by decide⟩:Fin 17),y,b):=by
  intro y b
  by_cases h0:y.val<8
  · exact receipt_r12_g0 y h0 b
  by_cases h1:y.val<16
  · exact receipt_r12_g1 y (by omega) h1 b
  by_cases h2:y.val<24
  · exact receipt_r12_g2 y (by omega) h2 b
  by_cases h3:y.val<32
  · exact receipt_r12_g3 y (by omega) h3 b
  by_cases h4:y.val<40
  · exact receipt_r12_g4 y (by omega) h4 b
  by_cases h5:y.val<48
  · exact receipt_r12_g5 y (by omega) h5 b
  by_cases h6:y.val<56
  · exact receipt_r12_g6 y (by omega) h6 b
  by_cases h7:y.val<64
  · exact receipt_r12_g7 y (by omega) h7 b
  by_cases h8:y.val<72
  · exact receipt_r12_g8 y (by omega) h8 b
  · exact receipt_r12_g9 y (by omega) b
end ProximityPrize.SubmissionLower.LocatorReplacementData
#print axioms ProximityPrize.SubmissionLower.LocatorReplacementData.receipt_r12_full
