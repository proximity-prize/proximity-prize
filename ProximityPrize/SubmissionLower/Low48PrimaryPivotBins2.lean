import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part588
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part652
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part716
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part780
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part844
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part908
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part972
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part1036
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part1100
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part1164
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part1228
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part1292
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part1356
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part1420
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part1484
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part1548
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part1612

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem window2_588_716 : binChunk w2 588 128 = 15940021400 :=
  binChunk_join (w:=w2) (start:=588) (left:=64) (right:=64) (x:=2275738089) (y:=13664283311) batch2_588_652 batch2_652_716
private theorem window2_716_844 : binChunk w2 716 128 = 98897485719 :=
  binChunk_join (w:=w2) (start:=716) (left:=64) (right:=64) (x:=34238929886) (y:=64658555833) batch2_716_780 batch2_780_844
private theorem window2_588_844 : binChunk w2 588 256 = 114837507119 :=
  binChunk_join (w:=w2) (start:=588) (left:=128) (right:=128) (x:=15940021400) (y:=98897485719) window2_588_716 window2_716_844
private theorem window2_844_972 : binChunk w2 844 128 = 280723506983 :=
  binChunk_join (w:=w2) (start:=844) (left:=64) (right:=64) (x:=107991005254) (y:=172732501729) batch2_844_908 batch2_908_972
private theorem window2_972_1100 : binChunk w2 972 128 = 710333537487 :=
  binChunk_join (w:=w2) (start:=972) (left:=64) (right:=64) (x:=274721008389) (y:=435612529098) batch2_972_1036 batch2_1036_1100
private theorem window2_844_1100 : binChunk w2 844 256 = 991057044470 :=
  binChunk_join (w:=w2) (start:=844) (left:=128) (right:=128) (x:=280723506983) (y:=710333537487) window2_844_972 window2_972_1100
private theorem window2_588_1100 : binChunk w2 588 512 = 1105894551589 :=
  binChunk_join (w:=w2) (start:=588) (left:=256) (right:=256) (x:=114837507119) (y:=991057044470) window2_588_844 window2_844_1100
private theorem window2_1100_1228 : binChunk w2 1100 128 = 1749172160308 :=
  binChunk_join (w:=w2) (start:=1100) (left:=64) (right:=64) (x:=683887644365) (y:=1065284515943) batch2_1100_1164 batch2_1164_1228
private theorem window2_1228_1356 : binChunk w2 1228 128 = 4035471666511 :=
  binChunk_join (w:=w2) (start:=1228) (left:=64) (right:=64) (x:=1643777913509) (y:=2391693753002) batch2_1228_1292 batch2_1292_1356
private theorem window2_1100_1356 : binChunk w2 1100 256 = 5784643826819 :=
  binChunk_join (w:=w2) (start:=1100) (left:=128) (right:=128) (x:=1749172160308) (y:=4035471666511) window2_1100_1228 window2_1228_1356
private theorem window2_1356_1484 : binChunk w2 1356 128 = 6407429970534 :=
  binChunk_join (w:=w2) (start:=1356) (left:=64) (right:=64) (x:=2990708504408) (y:=3416721466126) batch2_1356_1420 batch2_1420_1484
private theorem window2_1548_1651 : binChunk w2 1548 103 = 6720810879726 :=
  binChunk_join (w:=w2) (start:=1548) (left:=64) (right:=39) (x:=4074144621316) (y:=2646666258410) batch2_1548_1612 batch2_1612_1651
private theorem window2_1484_1651 : binChunk w2 1484 167 = 10471694717053 :=
  binChunk_join (w:=w2) (start:=1484) (left:=64) (right:=103) (x:=3750883837327) (y:=6720810879726) batch2_1484_1548 window2_1548_1651
private theorem window2_1356_1651 : binChunk w2 1356 295 = 16879124687587 :=
  binChunk_join (w:=w2) (start:=1356) (left:=128) (right:=167) (x:=6407429970534) (y:=10471694717053) window2_1356_1484 window2_1484_1651
private theorem window2_1100_1651 : binChunk w2 1100 551 = 22663768514406 :=
  binChunk_join (w:=w2) (start:=1100) (left:=256) (right:=295) (x:=5784643826819) (y:=16879124687587) window2_1100_1356 window2_1356_1651
private theorem window2_588_1651 : binChunk w2 588 1063 = 23769663065995 :=
  binChunk_join (w:=w2) (start:=588) (left:=512) (right:=551) (x:=1105894551589) (y:=22663768514406) window2_588_1100 window2_1100_1651
theorem binCompute2 : binCompute w2 = 23769663065995 := by
  exact (binCompute_eq_chunk w2 588 (by decide) (by decide)).trans window2_588_1651

end Low48PrimaryPivot
