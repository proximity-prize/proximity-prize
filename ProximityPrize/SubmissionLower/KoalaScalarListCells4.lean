import ProximityPrize.SubmissionLower.KoalaScalarListDefs
import ProximityPrize.SubmissionLower.KoalaScalarListCells3

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace KoalaScalarListBank
private def witness_64_2 : CJ1.Block where
  bank := .leftLow
  cap := 24
  free := [(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)]
  vectors := [
    [[0,0,0,0,0,0,0x7effc0aa,0x7efe9c39,0x7efacdb1,0x7eefd541],[0,0,0,0,1035,3915,11088,27864],[0,0,0x7effffd4,0x7effffab,0x7effff5d,0x7efffec9],[1]],
    [[0,0,0,0,0,0,0,0x7effc4b5,0x7efeb36d,0x7efb2661],[0,0,0,0,0,990,3740,10578],[0,0,0,0x7effffd5,0x7effffad,0x7effff61],[0,1]],
    [[0,0,0,0,0,0,0,0,0x7effc893,0x7efec999],[0,0,0,0,0,0,946,3569],[0,0,0,0,0x7effffd6,0x7effffaf],[0,0,1]],
    [[0,0,0,0,0,0,0,0,0,0x7effcc45],[0,0,0,0,0,0,0,903],[0,0,0,0,0,0x7effffd7],[0,0,0,1]],
    [[0,0,0,0,0,0,0,0,0x7ef92df8,0x7ecdae25],[0,0,0,0,0,0,26488,148092],[0,0,0,0,0x7efffc7a,0x7efff2b7],[],[1]],
    [[0,0,0,0,0,0,0,0,0,0x7ef9c92c],[0,0,0,0,0,0,0,24682],[0,0,0,0,0,0x7efffca4],[],[0,1]]]
theorem improved_64_2 : (CJ0.blockMatrix source 64 ((2 : ℤ)-22)).rank ≤ 24 :=
  Fast.cell (z := witness_64_2) (Fast.bands [(42,42,1),(43,43,2),(44,44,3),(45,46,3),(46,48,3),(47,50,3),(48,52,3),(49,54,3),(50,56,3),(51,58,3),(52,60,3),(53,62,2),(54,64,1)]) (by decide +kernel) (by decide +kernel)

private def witness_64_3 : CJ1.Block where
  bank := .leftLow
  cap := 24
  free := [(4,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,148995],[0,0,0,0,0,0,0x7effcc45],[0,0,0,0,903],[0,0,0x7effffd7],[1]]]
theorem improved_64_3 : (CJ0.blockMatrix source 64 ((3 : ℤ)-22)).rank ≤ 24 :=
  Fast.cell (z := witness_64_3) (Fast.bands [(42,42,1),(43,43,2),(44,44,3),(45,45,4),(46,47,4),(47,49,4),(48,51,4),(49,53,4),(50,55,4),(51,57,4),(52,59,4),(53,61,3),(54,63,2)]) (by decide +kernel) (by decide +kernel)

private def witness_65_1 : CJ1.Block where
  bank := .rightLow
  cap := 18
  free := [(1,0),(2,0),(4,0),(6,0)]
  vectors := [
    [[],[1]],
    [[],[],[1]],
    [[],[],[],[0x7f000000],[1]],
    [[],[],[],[0x7f000000],[],[0x7f000000],[1]]]
theorem improved_65_1 : (CJ0.blockMatrix source 65 ((1 : ℤ)-22)).rank ≤ 18 :=
  Fast.cell (z := witness_65_1) (Fast.bands [(0,56,10),(1,57,8),(2,58,6),(3,59,4),(4,60,2)]) (by decide +kernel) (by decide +kernel)

private def witness_65_2 : CJ1.Block where
  bank := .leftLow
  cap := 21
  free := [(3,0),(3,1),(3,2),(4,0)]
  vectors := [
    [[0,0,0,0,0,0,0x7effc0aa,0x7efe9c39,0x7efacdb1],[0,0,0,0,1035,3915,11088],[0,0,0x7effffd4,0x7effffab,0x7effff5d],[1]],
    [[0,0,0,0,0,0,0,0x7effc4b5,0x7efeb36d],[0,0,0,0,0,990,3740],[0,0,0,0x7effffd5,0x7effffad],[0,1]],
    [[0,0,0,0,0,0,0,0,0x7effc893],[0,0,0,0,0,0,946],[0,0,0,0,0x7effffd6],[0,0,1]],
    [[0,0,0,0,0,0,0,0,0x7ef92df8],[0,0,0,0,0,0,26488],[0,0,0,0,0x7efffc7a],[],[1]]]
theorem improved_65_2 : (CJ0.blockMatrix source 65 ((2 : ℤ)-22)).rank ≤ 21 :=
  Fast.cell (z := witness_65_2) (Fast.bands [(43,43,1),(44,44,2),(45,45,3),(46,47,3),(47,49,3),(48,51,3),(49,53,3),(50,55,3),(51,57,3),(52,59,3),(53,61,3),(54,63,2),(55,65,1)]) (by decide +kernel) (by decide +kernel)

private def witness_66_0 : CJ1.Block where
  bank := .rightLow
  cap := 10
  free := [(2,0)]
  vectors := [
    [[],[],[1]]]
theorem improved_66_0 : (CJ0.blockMatrix source 66 ((0 : ℤ)-22)).rank ≤ 10 :=
  Fast.cell (z := witness_66_0) (Fast.bands [(0,57,10),(1,58,8),(2,59,6),(3,60,4),(4,61,2)]) (by decide +kernel) (by decide +kernel)

private def witness_66_1 : CJ1.Block where
  bank := .rightLow
  cap := 16
  free := [(1,0),(2,0),(3,0),(4,0),(6,0),(8,0)]
  vectors := [
    [[],[1]],
    [[],[],[1]],
    [[],[],[],[1]],
    [[],[],[],[],[1]],
    [[],[],[],[],[],[0x7f000000],[1]],
    [[],[],[],[],[],[0x7f000000],[],[0x7f000000],[1]]]
theorem improved_66_1 : (CJ0.blockMatrix source 66 ((1 : ℤ)-22)).rank ≤ 16 :=
  Fast.cell (z := witness_66_1) (Fast.bands [(0,58,9),(1,59,7),(2,60,5),(3,61,3),(4,62,1)]) (by decide +kernel) (by decide +kernel)

private def witness_66_2 : CJ1.Block where
  bank := .leftLow
  cap := 18
  free := [(3,0),(3,1)]
  vectors := [
    [[0,0,0,0,0,0,0x7effc0aa,0x7efe9c39],[0,0,0,0,1035,3915],[0,0,0x7effffd4,0x7effffab],[1]],
    [[0,0,0,0,0,0,0,0x7effc4b5],[0,0,0,0,0,990],[0,0,0,0x7effffd5],[0,1]]]
theorem improved_66_2 : (CJ0.blockMatrix source 66 ((2 : ℤ)-22)).rank ≤ 18 :=
  Fast.cell (z := witness_66_2) (Fast.bands [(44,44,1),(45,45,2),(46,46,3),(47,48,3),(48,50,3),(49,52,3),(50,54,3),(51,56,3),(52,58,3),(53,60,3),(54,62,3),(55,64,2),(56,66,1)]) (by decide +kernel) (by decide +kernel)

private def witness_67_0 : CJ1.Block where
  bank := .rightLow
  cap := 9
  free := [(2,0),(4,0)]
  vectors := [
    [[],[],[1]],
    [[],[],[],[],[1]]]
theorem improved_67_0 : (CJ0.blockMatrix source 67 ((0 : ℤ)-22)).rank ≤ 9 :=
  Fast.cell (z := witness_67_0) (Fast.bands [(0,59,9),(1,60,7),(2,61,5),(3,62,3),(4,63,1)]) (by decide +kernel) (by decide +kernel)

private def witness_67_1 : CJ1.Block where
  bank := .leftLow
  cap := 14
  free := [(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)]
  vectors := [
    [[0,0,0,0,1176,4512,12972,33120],[0,0,0x7effffd1,0x7effffa4,0x7effff4d,0x7efffea5],[1]],
    [[0,0,0,0,0,1128,4324,12420],[0,0,0,0x7effffd2,0x7effffa6,0x7effff51],[0,1]],
    [[0,0,0,0,0,0,1081,4140],[0,0,0,0,0x7effffd3,0x7effffa8],[0,0,1]],
    [[0,0,0,0,0,0,0,1035],[0,0,0,0,0,0x7effffd4],[0,0,0,1]],
    [[0,0,0,0,0,0,32430,184230],[0,0,0,0,0x7efffbf6,0x7efff089],[],[1]],
    [[0,0,0,0,0,0,0,30360],[0,0,0,0,0,0x7efffc23],[],[0,1]]]
theorem improved_67_1 : (CJ0.blockMatrix source 67 ((1 : ℤ)-22)).rank ≤ 14 :=
  Fast.cell (z := witness_67_1) (Fast.bands [(45,45,1),(46,46,2),(47,48,2),(48,50,2),(49,52,2),(50,54,2),(51,56,2),(52,58,2),(53,60,2),(54,62,2),(55,64,2),(56,66,1)]) (by decide +kernel) (by decide +kernel)

private def witness_67_2 : CJ1.Block where
  bank := .leftLow
  cap := 15
  free := [(3,0)]
  vectors := [
    [[0,0,0,0,0,0,0x7effc0aa],[0,0,0,0,1035],[0,0,0x7effffd4],[1]]]
theorem improved_67_2 : (CJ0.blockMatrix source 67 ((2 : ℤ)-22)).rank ≤ 15 :=
  Fast.cell (z := witness_67_2) (Fast.bands [(45,45,1),(46,46,2),(47,47,3),(48,49,3),(49,51,3),(50,53,3),(51,55,3),(52,57,3),(53,59,3),(54,61,3),(55,63,3),(56,65,2),(57,67,1)]) (by decide +kernel) (by decide +kernel)

private def witness_68_0 : CJ1.Block where
  bank := .rightLow
  cap := 8
  free := [(2,0),(4,0),(6,0)]
  vectors := [
    [[],[],[1]],
    [[],[],[],[],[1]],
    [[],[],[],[],[],[],[1]]]
theorem improved_68_0 : (CJ0.blockMatrix source 68 ((0 : ℤ)-22)).rank ≤ 8 :=
  Fast.cell (z := witness_68_0) (Fast.bands [(0,61,8),(1,62,6),(2,63,4),(3,64,2)]) (by decide +kernel) (by decide +kernel)

private def witness_68_1 : CJ1.Block where
  bank := .leftLow
  cap := 12
  free := [(2,0),(2,1),(2,2),(3,0)]
  vectors := [
    [[0,0,0,0,1176,4512,12972],[0,0,0x7effffd1,0x7effffa4,0x7effff4d],[1]],
    [[0,0,0,0,0,1128,4324],[0,0,0,0x7effffd2,0x7effffa6],[0,1]],
    [[0,0,0,0,0,0,1081],[0,0,0,0,0x7effffd3],[0,0,1]],
    [[0,0,0,0,0,0,32430],[0,0,0,0,0x7efffbf6],[],[1]]]
theorem improved_68_1 : (CJ0.blockMatrix source 68 ((1 : ℤ)-22)).rank ≤ 12 :=
  Fast.cell (z := witness_68_1) (Fast.bands [(46,46,1),(47,47,2),(48,49,2),(49,51,2),(50,53,2),(51,55,2),(52,57,2),(53,59,2),(54,61,2),(55,63,2),(56,65,2),(57,67,1)]) (by decide +kernel) (by decide +kernel)

end KoalaScalarListBank
