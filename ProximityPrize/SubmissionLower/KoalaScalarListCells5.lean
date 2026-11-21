import ProximityPrize.SubmissionLower.KoalaScalarListDefs

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace KoalaScalarListBank
private def witness_67_0 : CJ1.Block where
  bank := .rightLow
  cap := 7
  free := [(1,0),(3,0),(5,0),(7,0)]
  vectors := [
    [[],[1]],
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
  Fast.cell (z := witness_67_1) (Fast.bands [(46,46,1),(47,47,2),(48,49,2),(49,51,2),(50,53,2),(51,55,2),(52,57,2),(53,59,2),(54,61,2),(55,63,2),(56,65,2),(57,67,1)]) (by decide +kernel) (by decide +kernel)

private def witness_68_0 : CJ1.Block where
  bank := .rightLow
  cap := 6
  free := [(1,0),(3,0),(5,0),(7,0),(9,0)]
  vectors := [
    [[],[1]],
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
  Fast.cell (z := witness_68_1) (Fast.bands [(47,47,1),(48,48,2),(49,50,2),(50,52,2),(51,54,2),(52,56,2),(53,58,2),(54,60,2),(55,62,2),(56,64,2),(57,66,2),(58,68,1)]) (by decide +kernel) (by decide +kernel)

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
  Fast.cell (z := witness_69_0) (Fast.bands [(48,48,1),(49,50,1),(50,52,1),(51,54,1),(52,56,1),(53,58,1),(54,60,1),(55,62,1),(56,64,1),(57,66,1),(58,68,1)]) (by decide +kernel) (by decide +kernel)

private def witness_70_0 : CJ1.Block where
  bank := .leftLow
  cap := 4
  free := [(1,0),(1,1)]
  vectors := [
    [[0,0,0x7effffcf,0x7effff9f],[1]],
    [[0,0,0,0x7effffd0],[0,1]]]
theorem improved_70_0 : (CJ0.blockMatrix source 70 ((0 : ℤ)-21)).rank ≤ 4 :=
  Fast.cell (z := witness_70_0) (Fast.bands [(49,49,1),(50,51,1),(51,53,1),(52,55,1),(53,57,1),(54,59,1),(55,61,1),(56,63,1),(57,65,1),(58,67,1),(59,69,1)]) (by decide +kernel) (by decide +kernel)

private def witness_71_0 : CJ1.Block where
  bank := .leftLow
  cap := 3
  free := [(1,0)]
  vectors := [
    [[0,0,0x7effffcf],[1]]]
theorem improved_71_0 : (CJ0.blockMatrix source 71 ((0 : ℤ)-21)).rank ≤ 3 :=
  Fast.cell (z := witness_71_0) (Fast.bands [(50,50,1),(51,52,1),(52,54,1),(53,56,1),(54,58,1),(55,60,1),(56,62,1),(57,64,1),(58,66,1),(59,68,1),(60,70,1)]) (by decide +kernel) (by decide +kernel)

end KoalaScalarListBank
