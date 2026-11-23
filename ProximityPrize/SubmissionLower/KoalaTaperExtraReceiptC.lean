import ProximityPrize.SubmissionLower.KoalaTaperExtraWindows
import ProximityPrize.SubmissionLower.KoalaTaperExtraRawClip

set_option Elab.async false
set_option autoImplicit false

set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace KoalaTaperExtra
open K1_13_2_3 Low48PrimaryPivot

private theorem feeC_1329_1361 : binChunk extraC 1329 32 = 7201199403 := by decide +kernel
private theorem feeC_1361_1393 : binChunk extraC 1361 32 = 19429955649 := by decide +kernel
private theorem feeC_1393_1425 : binChunk extraC 1393 32 = 27260492106 := by decide +kernel
private theorem feeC_1425_1457 : binChunk extraC 1425 32 = 30325475781 := by decide +kernel
private theorem feeC_1457_1489 : binChunk extraC 1457 32 = 31699804500 := by decide +kernel
private theorem feeC_1489_1521 : binChunk extraC 1489 32 = 33089642040 := by decide +kernel
private theorem feeC_1521_1553 : binChunk extraC 1521 32 = 34509302100 := by decide +kernel
private theorem feeC_1553_1585 : binChunk extraC 1553 32 = 35958779220 := by decide +kernel
private theorem feeC_1585_1617 : binChunk extraC 1585 32 = 37438073400 := by decide +kernel
private theorem feeC_1617_1649 : binChunk extraC 1617 32 = 38947190100 := by decide +kernel
private theorem feeC_1649_1651 : binChunk extraC 1649 2 = 2484987960 := by decide +kernel
private theorem feeC_1329_1393 : binChunk extraC 1329 64 = 26631155052 := binChunk_join (w := extraC) (start := 1329) (left := 32) (right := 32) feeC_1329_1361 feeC_1361_1393
private theorem feeC_1425_1489 : binChunk extraC 1425 64 = 62025280281 := binChunk_join (w := extraC) (start := 1425) (left := 32) (right := 32) feeC_1425_1457 feeC_1457_1489
private theorem feeC_1393_1489 : binChunk extraC 1393 96 = 89285772387 := binChunk_join (w := extraC) (start := 1393) (left := 32) (right := 64) feeC_1393_1425 feeC_1425_1489
private theorem feeC_1329_1489 : binChunk extraC 1329 160 = 115916927439 := binChunk_join (w := extraC) (start := 1329) (left := 64) (right := 96) feeC_1329_1393 feeC_1393_1489
private theorem feeC_1521_1585 : binChunk extraC 1521 64 = 70468081320 := binChunk_join (w := extraC) (start := 1521) (left := 32) (right := 32) feeC_1521_1553 feeC_1553_1585
private theorem feeC_1489_1585 : binChunk extraC 1489 96 = 103557723360 := binChunk_join (w := extraC) (start := 1489) (left := 32) (right := 64) feeC_1489_1521 feeC_1521_1585
private theorem feeC_1617_1651 : binChunk extraC 1617 34 = 41432178060 := binChunk_join (w := extraC) (start := 1617) (left := 32) (right := 2) feeC_1617_1649 feeC_1649_1651
private theorem feeC_1585_1651 : binChunk extraC 1585 66 = 78870251460 := binChunk_join (w := extraC) (start := 1585) (left := 32) (right := 34) feeC_1585_1617 feeC_1617_1651
private theorem feeC_1489_1651 : binChunk extraC 1489 162 = 182427974820 := binChunk_join (w := extraC) (start := 1489) (left := 96) (right := 66) feeC_1489_1585 feeC_1585_1651
private theorem feeC_1329_1651 : binChunk extraC 1329 322 = 298344902259 := binChunk_join (w := extraC) (start := 1329) (left := 160) (right := 162) feeC_1329_1489 feeC_1489_1651

private theorem rawC_218 : RawReceipt.rawChunk extraC 218 64 = 105136381453 :=
  (RawClosed.rawChunk_closed extraC 218 64 (by decide) (by decide)
    (by decide) (by decide)).trans (by decide +kernel)

private theorem rawC_282 : RawReceipt.rawChunk extraC 282 40 = 193694577234 :=
  (RawClosed.rawChunk_closed extraC 282 40 (by decide) (by decide)
    (by decide) (by decide)).trans (by decide +kernel)

theorem rawC : rawWindow extraC = 298830958687 := by
  rw [raw_eq_compute extraC (by decide) (by decide), RawReceipt.rawCompute_eq]
  have part218_104 := RawReceipt.joinRaw (start := 218) (a := 64) (b := 40) rawC_218 rawC_282
  have active := part218_104
  have beforeRange := RawReceipt.rawChunk_zero extraC 0 218 (Or.inl (by decide))
  exact RawReceipt.joinRaw (start := 0) (a := 218) (b := 104) beforeRange active

theorem binC : binCompute extraC = 298344902259 :=
  (binCompute_eq_chunk extraC 1329 (by decide) (by decide)).trans feeC_1329_1651

#print axioms rawC
#print axioms binC
end KoalaTaperExtra
