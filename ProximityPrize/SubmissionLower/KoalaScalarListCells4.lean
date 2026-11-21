import ProximityPrize.SubmissionLower.KoalaScalarListDefs

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace KoalaScalarListBank
private def witness_62_2 : CJ1.Block where
  bank := .leftLow
  cap := 24
  free := [(3,0),(3,1),(3,2),(3,3),(4,0),(4,1)]
  vectors := [
    [[0,0,0,0,0,0,0x7effc4b5,0x7efeb36d,0x7efb2661,0x7ef0ef71],[0,0,0,0,990,3740,10578,26544],[0,0,0x7effffd5,0x7effffad,0x7effff61,0x7efffed1],[1]],
    [[0,0,0,0,0,0,0,0x7effc893,0x7efec999,0x7efb7b09],[0,0,0,0,0,946,3569,10080],[0,0,0,0x7effffd6,0x7effffaf,0x7effff65],[0,1]],
    [[0,0,0,0,0,0,0,0,0x7effcc45,0x7efedec3],[0,0,0,0,0,0,903,3402],[0,0,0,0,0x7effffd7,0x7effffb1],[0,0,1]],
    [[0,0,0,0,0,0,0,0,0,0x7effcfcc],[0,0,0,0,0,0,0,861],[0,0,0,0,0,0x7effffd8],[0,0,0,1]],
    [[0,0,0,0,0,0,0,0,0x7ef9c92c,0x7ed23db2],[0,0,0,0,0,0,24682,137760],[0,0,0,0,0x7efffca4,0x7efff35a],[],[1]],
    [[0,0,0,0,0,0,0,0,0,0x7efa59cb],[0,0,0,0,0,0,0,22960],[0,0,0,0,0,0x7efffccd],[],[0,1]]]
theorem improved_62_2 : (CJ0.blockMatrix source 62 ((2 : ℤ)-21)).rank ≤ 24 :=
  Fast.cell (z := witness_62_2) (Fast.bands [(41,41,1),(42,42,2),(43,43,3),(44,45,3),(45,47,3),(46,49,3),(47,51,3),(48,53,3),(49,55,3),(50,57,3),(51,59,3),(52,61,2)]) (by decide +kernel) (by decide +kernel)

private def witness_62_3 : CJ1.Block where
  bank := .leftLow
  cap := 24
  free := [(4,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,135751],[0,0,0,0,0,0,0x7effcfcc],[0,0,0,0,861],[0,0,0x7effffd8],[1]]]
theorem improved_62_3 : (CJ0.blockMatrix source 62 ((3 : ℤ)-21)).rank ≤ 24 :=
  Fast.cell (z := witness_62_3) (Fast.bands [(41,41,1),(42,42,2),(43,43,3),(44,44,4),(45,46,4),(46,48,4),(47,50,4),(48,52,4),(49,54,4),(50,56,4),(51,58,4),(52,60,3),(53,62,1)]) (by decide +kernel) (by decide +kernel)

private def witness_63_1 : CJ1.Block where
  bank := .rightLow
  cap := 18
  free := [(0,0),(1,0),(3,0),(5,0)]
  vectors := [
    [[1]],
    [[],[1]],
    [[],[],[0x7f000000],[1]],
    [[],[],[0x7f000000],[],[0x7f000000],[1]]]
theorem improved_63_1 : (CJ0.blockMatrix source 63 ((1 : ℤ)-21)).rank ≤ 18 :=
  Fast.cell (z := witness_63_1) (Fast.bands [(0,54,10),(1,55,8),(2,56,6),(3,57,4),(4,58,2)]) (by decide +kernel) (by decide +kernel)

private def witness_63_2 : CJ1.Block where
  bank := .leftLow
  cap := 21
  free := [(3,0),(3,1),(3,2),(4,0)]
  vectors := [
    [[0,0,0,0,0,0,0x7effc4b5,0x7efeb36d,0x7efb2661],[0,0,0,0,990,3740,10578],[0,0,0x7effffd5,0x7effffad,0x7effff61],[1]],
    [[0,0,0,0,0,0,0,0x7effc893,0x7efec999],[0,0,0,0,0,946,3569],[0,0,0,0x7effffd6,0x7effffaf],[0,1]],
    [[0,0,0,0,0,0,0,0,0x7effcc45],[0,0,0,0,0,0,903],[0,0,0,0,0x7effffd7],[0,0,1]],
    [[0,0,0,0,0,0,0,0,0x7ef9c92c],[0,0,0,0,0,0,24682],[0,0,0,0,0x7efffca4],[],[1]]]
theorem improved_63_2 : (CJ0.blockMatrix source 63 ((2 : ℤ)-21)).rank ≤ 21 :=
  Fast.cell (z := witness_63_2) (Fast.bands [(42,42,1),(43,43,2),(44,44,3),(45,46,3),(46,48,3),(47,50,3),(48,52,3),(49,54,3),(50,56,3),(51,58,3),(52,60,3),(53,62,2)]) (by decide +kernel) (by decide +kernel)

private def witness_64_0 : CJ1.Block where
  bank := .rightLow
  cap := 10
  free := [(1,0)]
  vectors := [
    [[],[1]]]
theorem improved_64_0 : (CJ0.blockMatrix source 64 ((0 : ℤ)-21)).rank ≤ 10 :=
  Fast.cell (z := witness_64_0) (Fast.bands [(0,55,10),(1,56,8),(2,57,6),(3,58,4),(4,59,2)]) (by decide +kernel) (by decide +kernel)

private def witness_64_1 : CJ1.Block where
  bank := .rightLow
  cap := 16
  free := [(0,0),(1,0),(2,0),(3,0),(5,0),(7,0)]
  vectors := [
    [[1]],
    [[],[1]],
    [[],[],[1]],
    [[],[],[],[1]],
    [[],[],[],[],[0x7f000000],[1]],
    [[],[],[],[],[0x7f000000],[],[0x7f000000],[1]]]
theorem improved_64_1 : (CJ0.blockMatrix source 64 ((1 : ℤ)-21)).rank ≤ 16 :=
  Fast.cell (z := witness_64_1) (Fast.bands [(0,56,9),(1,57,7),(2,58,5),(3,59,3),(4,60,1)]) (by decide +kernel) (by decide +kernel)

private def witness_64_2 : CJ1.Block where
  bank := .leftLow
  cap := 18
  free := [(3,0),(3,1)]
  vectors := [
    [[0,0,0,0,0,0,0x7effc4b5,0x7efeb36d],[0,0,0,0,990,3740],[0,0,0x7effffd5,0x7effffad],[1]],
    [[0,0,0,0,0,0,0,0x7effc893],[0,0,0,0,0,946],[0,0,0,0x7effffd6],[0,1]]]
theorem improved_64_2 : (CJ0.blockMatrix source 64 ((2 : ℤ)-21)).rank ≤ 18 :=
  Fast.cell (z := witness_64_2) (Fast.bands [(43,43,1),(44,44,2),(45,45,3),(46,47,3),(47,49,3),(48,51,3),(49,53,3),(50,55,3),(51,57,3),(52,59,3),(53,61,3),(54,63,2)]) (by decide +kernel) (by decide +kernel)

private def witness_65_0 : CJ1.Block where
  bank := .rightLow
  cap := 9
  free := [(1,0),(3,0)]
  vectors := [
    [[],[1]],
    [[],[],[],[1]]]
theorem improved_65_0 : (CJ0.blockMatrix source 65 ((0 : ℤ)-21)).rank ≤ 9 :=
  Fast.cell (z := witness_65_0) (Fast.bands [(0,57,9),(1,58,7),(2,59,5),(3,60,3),(4,61,1)]) (by decide +kernel) (by decide +kernel)

private def witness_65_1 : CJ1.Block where
  bank := .leftLow
  cap := 14
  free := [(2,0),(2,1),(2,2),(2,3),(3,0),(3,1)]
  vectors := [
    [[0,0,0,0,1128,4324,12420,31680],[0,0,0x7effffd2,0x7effffa6,0x7effff51,0x7efffead],[1]],
    [[0,0,0,0,0,1081,4140,11880],[0,0,0,0x7effffd3,0x7effffa8,0x7effff55],[0,1]],
    [[0,0,0,0,0,0,1035,3960],[0,0,0,0,0x7effffd4,0x7effffaa],[0,0,1]],
    [[0,0,0,0,0,0,0,990],[0,0,0,0,0,0x7effffd5],[0,0,0,1]],
    [[0,0,0,0,0,0,30360,172260],[0,0,0,0,0x7efffc23,0x7efff139],[],[1]],
    [[0,0,0,0,0,0,0,28380],[0,0,0,0,0,0x7efffc4f],[],[0,1]]]
theorem improved_65_1 : (CJ0.blockMatrix source 65 ((1 : ℤ)-21)).rank ≤ 14 :=
  Fast.cell (z := witness_65_1) (Fast.bands [(44,44,1),(45,45,2),(46,47,2),(47,49,2),(48,51,2),(49,53,2),(50,55,2),(51,57,2),(52,59,2),(53,61,2),(54,63,2),(55,65,1)]) (by decide +kernel) (by decide +kernel)

private def witness_65_2 : CJ1.Block where
  bank := .leftLow
  cap := 15
  free := [(3,0)]
  vectors := [
    [[0,0,0,0,0,0,0x7effc4b5],[0,0,0,0,990],[0,0,0x7effffd5],[1]]]
theorem improved_65_2 : (CJ0.blockMatrix source 65 ((2 : ℤ)-21)).rank ≤ 15 :=
  Fast.cell (z := witness_65_2) (Fast.bands [(44,44,1),(45,45,2),(46,46,3),(47,48,3),(48,50,3),(49,52,3),(50,54,3),(51,56,3),(52,58,3),(53,60,3),(54,62,3),(55,64,2)]) (by decide +kernel) (by decide +kernel)

private def witness_66_0 : CJ1.Block where
  bank := .rightLow
  cap := 8
  free := [(1,0),(3,0),(5,0)]
  vectors := [
    [[],[1]],
    [[],[],[],[1]],
    [[],[],[],[],[],[1]]]
theorem improved_66_0 : (CJ0.blockMatrix source 66 ((0 : ℤ)-21)).rank ≤ 8 :=
  Fast.cell (z := witness_66_0) (Fast.bands [(0,59,8),(1,60,6),(2,61,4),(3,62,2)]) (by decide +kernel) (by decide +kernel)

private def witness_66_1 : CJ1.Block where
  bank := .leftLow
  cap := 12
  free := [(2,0),(2,1),(2,2),(3,0)]
  vectors := [
    [[0,0,0,0,1128,4324,12420],[0,0,0x7effffd2,0x7effffa6,0x7effff51],[1]],
    [[0,0,0,0,0,1081,4140],[0,0,0,0x7effffd3,0x7effffa8],[0,1]],
    [[0,0,0,0,0,0,1035],[0,0,0,0,0x7effffd4],[0,0,1]],
    [[0,0,0,0,0,0,30360],[0,0,0,0,0x7efffc23],[],[1]]]
theorem improved_66_1 : (CJ0.blockMatrix source 66 ((1 : ℤ)-21)).rank ≤ 12 :=
  Fast.cell (z := witness_66_1) (Fast.bands [(45,45,1),(46,46,2),(47,48,2),(48,50,2),(49,52,2),(50,54,2),(51,56,2),(52,58,2),(53,60,2),(54,62,2),(55,64,2),(56,66,1)]) (by decide +kernel) (by decide +kernel)

end KoalaScalarListBank
