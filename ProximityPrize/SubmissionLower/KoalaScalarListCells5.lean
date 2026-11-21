import ProximityPrize.SubmissionLower.KoalaScalarListDefs

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace KoalaScalarListBank
private def witness_65_1 : CJ1.Block where
  bank := .rightLow
  cap := 14
  free := [(2,0),(3,0),(4,0),(5,0),(7,0),(9,0)]
  vectors := [
    [[],[],[1]],
    [[],[],[],[1]],
    [[],[],[],[],[1]],
    [[],[],[],[],[],[1]],
    [[],[],[],[],[],[],[0x7f000000],[1]],
    [[],[],[],[],[],[],[0x7f000000],[],[0x7f000000],[1]]]
theorem improved_65_1 : (CJ0.blockMatrix source 65 ((1 : ℤ)-21)).rank ≤ 14 :=
  Fast.cell (z := witness_65_1) (Fast.bands [(0,58,8),(1,59,6),(2,60,4),(3,61,2)]) (by decide +kernel) (by decide +kernel)

private def witness_65_2 : CJ1.Block where
  bank := .leftLow
  cap := 15
  free := [(3,0)]
  vectors := [
    [[0,0,0,0,0,0,0x7effc4b5],[0,0,0,0,990],[0,0,0x7effffd5],[1]]]
theorem improved_65_2 : (CJ0.blockMatrix source 65 ((2 : ℤ)-21)).rank ≤ 15 :=
  Fast.cell (z := witness_65_2) (Fast.bands [(44,44,1),(45,45,2),(46,46,3),(47,48,3),(48,50,3),(49,52,3),(50,54,3),(51,56,3),(52,58,3),(53,60,3),(54,62,2),(55,64,1)]) (by decide +kernel) (by decide +kernel)

private def witness_66_0 : CJ1.Block where
  bank := .rightLow
  cap := 8
  free := [(3,0),(5,0)]
  vectors := [
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
  Fast.cell (z := witness_66_1) (Fast.bands [(45,45,1),(46,46,2),(47,48,2),(48,50,2),(49,52,2),(50,54,2),(51,56,2),(52,58,2),(53,60,2),(54,62,2),(55,64,1)]) (by decide +kernel) (by decide +kernel)

private def witness_67_0 : CJ1.Block where
  bank := .rightLow
  cap := 7
  free := [(3,0),(5,0),(7,0)]
  vectors := [
    [[],[],[],[1]],
    [[],[],[],[],[],[1]],
    [[],[],[],[],[],[],[],[1]]]
theorem improved_67_0 : (CJ0.blockMatrix source 67 ((0 : ℤ)-21)).rank ≤ 7 :=
  Fast.cell (z := witness_67_0) (Fast.bands [(0,61,7),(1,62,5),(2,63,3),(3,64,1)]) (by decide +kernel) (by decide +kernel)

private def witness_67_1 : CJ1.Block where
  bank := .leftLow
  cap := 10
  free := [(2,0),(2,1)]
  vectors := [
    [[0,0,0,0,1128,4324],[0,0,0x7effffd2,0x7effffa6],[1]],
    [[0,0,0,0,0,1081],[0,0,0,0x7effffd3],[0,1]]]
theorem improved_67_1 : (CJ0.blockMatrix source 67 ((1 : ℤ)-21)).rank ≤ 10 :=
  Fast.cell (z := witness_67_1) (Fast.bands [(46,46,1),(47,47,2),(48,49,2),(49,51,2),(50,53,2),(51,55,2),(52,57,2),(53,59,2),(54,61,2),(55,63,2),(56,65,1)]) (by decide +kernel) (by decide +kernel)

private def witness_68_0 : CJ1.Block where
  bank := .rightLow
  cap := 6
  free := [(3,0),(5,0),(7,0),(9,0)]
  vectors := [
    [[],[],[],[1]],
    [[],[],[],[],[],[1]],
    [[],[],[],[],[],[],[],[1]],
    [[],[],[],[],[],[],[],[],[],[1]]]
theorem improved_68_0 : (CJ0.blockMatrix source 68 ((0 : ℤ)-21)).rank ≤ 6 :=
  Fast.cell (z := witness_68_0) (Fast.bands [(0,63,6),(1,64,4),(2,65,2)]) (by decide +kernel) (by decide +kernel)

private def witness_68_1 : CJ1.Block where
  bank := .leftLow
  cap := 8
  free := [(2,0)]
  vectors := [
    [[0,0,0,0,1128],[0,0,0x7effffd2],[1]]]
theorem improved_68_1 : (CJ0.blockMatrix source 68 ((1 : ℤ)-21)).rank ≤ 8 :=
  Fast.cell (z := witness_68_1) (Fast.bands [(47,47,1),(48,48,2),(49,50,2),(50,52,2),(51,54,2),(52,56,2),(53,58,2),(54,60,2),(55,62,2),(56,64,2),(57,66,1)]) (by decide +kernel) (by decide +kernel)

private def witness_69_0 : CJ1.Block where
  bank := .leftLow
  cap := 5
  free := [(1,0),(1,1),(1,2),(2,0)]
  vectors := [
    [[0,0,0x7effffcf,0x7effff9f,0x7effff41],[1]],
    [[0,0,0,0x7effffd0,0x7effffa1],[0,1]],
    [[0,0,0,0,0x7effffd1],[0,0,1]],
    [[0,0,0,0,0x7efffb99],[],[1]]]
theorem improved_69_0 : (CJ0.blockMatrix source 69 ((0 : ℤ)-21)).rank ≤ 5 :=
  Fast.cell (z := witness_69_0) (Fast.bands [(48,48,1),(49,50,1),(50,52,1),(51,54,1),(52,56,1),(53,58,1),(54,60,1),(55,62,1),(56,64,1),(57,66,1)]) (by decide +kernel) (by decide +kernel)

private def witness_70_0 : CJ1.Block where
  bank := .leftLow
  cap := 4
  free := [(1,0),(1,1)]
  vectors := [
    [[0,0,0x7effffcf,0x7effff9f],[1]],
    [[0,0,0,0x7effffd0],[0,1]]]
theorem improved_70_0 : (CJ0.blockMatrix source 70 ((0 : ℤ)-21)).rank ≤ 4 :=
  Fast.cell (z := witness_70_0) (Fast.bands [(49,49,1),(50,51,1),(51,53,1),(52,55,1),(53,57,1),(54,59,1),(55,61,1),(56,63,1),(57,65,1),(58,67,1)]) (by decide +kernel) (by decide +kernel)

private def witness_71_0 : CJ1.Block where
  bank := .leftLow
  cap := 3
  free := [(1,0)]
  vectors := [
    [[0,0,0x7effffcf],[1]]]
theorem improved_71_0 : (CJ0.blockMatrix source 71 ((0 : ℤ)-21)).rank ≤ 3 :=
  Fast.cell (z := witness_71_0) (Fast.bands [(50,50,1),(51,52,1),(52,54,1),(53,56,1),(54,58,1),(55,60,1),(56,62,1),(57,64,1),(58,66,1),(59,68,1)]) (by decide +kernel) (by decide +kernel)

end KoalaScalarListBank
