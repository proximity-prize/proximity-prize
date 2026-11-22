import ProximityPrize.SubmissionLower.Low48PrimaryPivotBinReceipts
import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part780

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf844 : binChunk w2 844 4 = 5318025555 := by decide +kernel
private theorem leaf848 : binChunk w2 848 4 = 5488256899 := by decide +kernel
private theorem leaf852 : binChunk w2 852 4 = 5662381016 := by decide +kernel
private theorem leaf856 : binChunk w2 856 4 = 5840474787 := by decide +kernel
private theorem leaf860 : binChunk w2 860 4 = 6022769779 := by decide +kernel
private theorem leaf864 : binChunk w2 864 4 = 6209434168 := by decide +kernel
private theorem leaf868 : binChunk w2 868 4 = 6400564203 := by decide +kernel
private theorem leaf872 : binChunk w2 872 4 = 6596419867 := by decide +kernel
private theorem leaf876 : binChunk w2 876 4 = 6797193264 := by decide +kernel
private theorem leaf880 : binChunk w2 880 4 = 7002999915 := by decide +kernel
private theorem leaf884 : binChunk w2 884 4 = 7214128315 := by decide +kernel
private theorem leaf888 : binChunk w2 888 4 = 7430794496 := by decide +kernel
private theorem leaf892 : binChunk w2 892 4 = 7653133155 := by decide +kernel
private theorem leaf896 : binChunk w2 896 4 = 7881461326 := by decide +kernel
private theorem leaf900 : binChunk w2 900 4 = 8116017607 := by decide +kernel
private theorem leaf904 : binChunk w2 904 4 = 8356950902 := by decide +kernel
private theorem batch2_844_852 : binChunk w2 844 8 = 10806282454 :=
  binChunk_join (w := w2) (start := 844) (left := 4) (right := 4) (x := 5318025555) (y := 5488256899) leaf844 leaf848
private theorem batch2_852_860 : binChunk w2 852 8 = 11502855803 :=
  binChunk_join (w := w2) (start := 852) (left := 4) (right := 4) (x := 5662381016) (y := 5840474787) leaf852 leaf856
private theorem batch2_844_860 : binChunk w2 844 16 = 22309138257 :=
  binChunk_join (w := w2) (start := 844) (left := 8) (right := 8) (x := 10806282454) (y := 11502855803) batch2_844_852 batch2_852_860
private theorem batch2_860_868 : binChunk w2 860 8 = 12232203947 :=
  binChunk_join (w := w2) (start := 860) (left := 4) (right := 4) (x := 6022769779) (y := 6209434168) leaf860 leaf864
private theorem batch2_868_876 : binChunk w2 868 8 = 12996984070 :=
  binChunk_join (w := w2) (start := 868) (left := 4) (right := 4) (x := 6400564203) (y := 6596419867) leaf868 leaf872
private theorem batch2_860_876 : binChunk w2 860 16 = 25229188017 :=
  binChunk_join (w := w2) (start := 860) (left := 8) (right := 8) (x := 12232203947) (y := 12996984070) batch2_860_868 batch2_868_876
private theorem batch2_844_876 : binChunk w2 844 32 = 47538326274 :=
  binChunk_join (w := w2) (start := 844) (left := 16) (right := 16) (x := 22309138257) (y := 25229188017) batch2_844_860 batch2_860_876
private theorem batch2_876_884 : binChunk w2 876 8 = 13800193179 :=
  binChunk_join (w := w2) (start := 876) (left := 4) (right := 4) (x := 6797193264) (y := 7002999915) leaf876 leaf880
private theorem batch2_884_892 : binChunk w2 884 8 = 14644922811 :=
  binChunk_join (w := w2) (start := 884) (left := 4) (right := 4) (x := 7214128315) (y := 7430794496) leaf884 leaf888
private theorem batch2_876_892 : binChunk w2 876 16 = 28445115990 :=
  binChunk_join (w := w2) (start := 876) (left := 8) (right := 8) (x := 13800193179) (y := 14644922811) batch2_876_884 batch2_884_892
private theorem batch2_892_900 : binChunk w2 892 8 = 15534594481 :=
  binChunk_join (w := w2) (start := 892) (left := 4) (right := 4) (x := 7653133155) (y := 7881461326) leaf892 leaf896
private theorem batch2_900_908 : binChunk w2 900 8 = 16472968509 :=
  binChunk_join (w := w2) (start := 900) (left := 4) (right := 4) (x := 8116017607) (y := 8356950902) leaf900 leaf904
private theorem batch2_892_908 : binChunk w2 892 16 = 32007562990 :=
  binChunk_join (w := w2) (start := 892) (left := 8) (right := 8) (x := 15534594481) (y := 16472968509) batch2_892_900 batch2_900_908
private theorem batch2_876_908 : binChunk w2 876 32 = 60452678980 :=
  binChunk_join (w := w2) (start := 876) (left := 16) (right := 16) (x := 28445115990) (y := 32007562990) batch2_876_892 batch2_892_908
theorem batch2_844_908 : binChunk w2 844 64 = 107991005254 :=
  binChunk_join (w := w2) (start := 844) (left := 32) (right := 32) (x := 47538326274) (y := 60452678980) batch2_844_876 batch2_876_908

end Low48PrimaryPivot
