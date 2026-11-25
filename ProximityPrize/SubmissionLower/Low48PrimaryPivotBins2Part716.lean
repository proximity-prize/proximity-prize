import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins3Part1242

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf716 : binChunk w2 716 4 = 1446172140 := by decide +kernel
private theorem leaf720 : binChunk w2 720 4 = 1528012881 := by decide +kernel
private theorem leaf724 : binChunk w2 724 4 = 1612011529 := by decide +kernel
private theorem leaf728 : binChunk w2 728 4 = 1698230736 := by decide +kernel
private theorem leaf732 : binChunk w2 732 4 = 1786705069 := by decide +kernel
private theorem leaf736 : binChunk w2 736 4 = 1877434297 := by decide +kernel
private theorem leaf740 : binChunk w2 740 4 = 1970485228 := by decide +kernel
private theorem leaf744 : binChunk w2 744 4 = 2065893153 := by decide +kernel
private theorem leaf748 : binChunk w2 748 4 = 2163654945 := by decide +kernel
private theorem leaf752 : binChunk w2 752 4 = 2263841664 := by decide +kernel
private theorem leaf756 : binChunk w2 756 4 = 2366489325 := by decide +kernel
private theorem leaf760 : binChunk w2 760 4 = 2471591809 := by decide +kernel
private theorem leaf764 : binChunk w2 764 4 = 2579224524 := by decide +kernel
private theorem leaf768 : binChunk w2 768 4 = 2689424209 := by decide +kernel
private theorem leaf772 : binChunk w2 772 4 = 2802181657 := by decide +kernel
private theorem leaf776 : binChunk w2 776 4 = 2917576720 := by decide +kernel
private theorem batch2_716_724 : binChunk w2 716 8 = 2974185021 :=
  binChunk_join (w := w2) (start := 716) (left := 4) (right := 4) (x := 1446172140) (y := 1528012881) leaf716 leaf720
private theorem batch2_724_732 : binChunk w2 724 8 = 3310242265 :=
  binChunk_join (w := w2) (start := 724) (left := 4) (right := 4) (x := 1612011529) (y := 1698230736) leaf724 leaf728
private theorem batch2_716_732 : binChunk w2 716 16 = 6284427286 :=
  binChunk_join (w := w2) (start := 716) (left := 8) (right := 8) (x := 2974185021) (y := 3310242265) batch2_716_724 batch2_724_732
private theorem batch2_732_740 : binChunk w2 732 8 = 3664139366 :=
  binChunk_join (w := w2) (start := 732) (left := 4) (right := 4) (x := 1786705069) (y := 1877434297) leaf732 leaf736
private theorem batch2_740_748 : binChunk w2 740 8 = 4036378381 :=
  binChunk_join (w := w2) (start := 740) (left := 4) (right := 4) (x := 1970485228) (y := 2065893153) leaf740 leaf744
private theorem batch2_732_748 : binChunk w2 732 16 = 7700517747 :=
  binChunk_join (w := w2) (start := 732) (left := 8) (right := 8) (x := 3664139366) (y := 4036378381) batch2_732_740 batch2_740_748
private theorem batch2_716_748 : binChunk w2 716 32 = 13984945033 :=
  binChunk_join (w := w2) (start := 716) (left := 16) (right := 16) (x := 6284427286) (y := 7700517747) batch2_716_732 batch2_732_748
private theorem batch2_748_756 : binChunk w2 748 8 = 4427496609 :=
  binChunk_join (w := w2) (start := 748) (left := 4) (right := 4) (x := 2163654945) (y := 2263841664) leaf748 leaf752
private theorem batch2_756_764 : binChunk w2 756 8 = 4838081134 :=
  binChunk_join (w := w2) (start := 756) (left := 4) (right := 4) (x := 2366489325) (y := 2471591809) leaf756 leaf760
private theorem batch2_748_764 : binChunk w2 748 16 = 9265577743 :=
  binChunk_join (w := w2) (start := 748) (left := 8) (right := 8) (x := 4427496609) (y := 4838081134) batch2_748_756 batch2_756_764
private theorem batch2_764_772 : binChunk w2 764 8 = 5268648733 :=
  binChunk_join (w := w2) (start := 764) (left := 4) (right := 4) (x := 2579224524) (y := 2689424209) leaf764 leaf768
private theorem batch2_772_780 : binChunk w2 772 8 = 5719758377 :=
  binChunk_join (w := w2) (start := 772) (left := 4) (right := 4) (x := 2802181657) (y := 2917576720) leaf772 leaf776
private theorem batch2_764_780 : binChunk w2 764 16 = 10988407110 :=
  binChunk_join (w := w2) (start := 764) (left := 8) (right := 8) (x := 5268648733) (y := 5719758377) batch2_764_772 batch2_772_780
private theorem batch2_748_780 : binChunk w2 748 32 = 20253984853 :=
  binChunk_join (w := w2) (start := 748) (left := 16) (right := 16) (x := 9265577743) (y := 10988407110) batch2_748_764 batch2_764_780
theorem batch2_716_780 : binChunk w2 716 64 = 34238929886 :=
  binChunk_join (w := w2) (start := 716) (left := 32) (right := 32) (x := 13984945033) (y := 20253984853) batch2_716_748 batch2_748_780

end Low48PrimaryPivot
