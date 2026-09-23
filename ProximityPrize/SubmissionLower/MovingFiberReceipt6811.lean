import ProximityPrize.SubmissionLower.MovingFiberReceiptProof6811R36

namespace ProximityPrize.SubmissionLower.Lower80860.ReceiptProof
open ReceiptData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem receipt : Receipt := by
  intro r v hr hR hV
  interval_cases r
  · exact all1 v (by omega)
  · exact all2 v (by omega)
  · exact all3 v (by omega)
  · exact all4 v (by omega)
  · exact all5 v (by omega)
  · exact all6 v (by omega)
  · exact all7 v (by omega)
  · exact all8 v (by omega)
  · exact all9 v (by omega)
  · exact all10 v (by omega)
  · exact all11 v (by omega)
  · exact all12 v (by omega)
  · exact all13 v (by omega)
  · exact all14 v (by omega)
  · exact all15 v (by omega)
  · exact all16 v (by omega)
  · exact all17 v (by omega)
  · exact all18 v (by omega)
  · exact all19 v (by omega)
  · exact all20 v (by omega)
  · exact all21 v (by omega)
  · exact all22 v (by omega)
  · exact all23 v (by omega)
  · exact all24 v (by omega)
  · exact all25 v (by omega)
  · exact all26 v (by omega)
  · exact all27 v (by omega)
  · exact all28 v (by omega)
  · exact all29 v (by omega)
  · exact all30 v (by omega)
  · exact all31 v (by omega)
  · exact all32 v (by omega)
  · exact all33 v (by omega)
  · exact all34 v (by omega)
  · exact all35 v (by omega)
  · exact all36 v (by omega)

#print axioms receipt
end ProximityPrize.SubmissionLower.Lower80860.ReceiptProof
