import ProximityPrize.SubmissionLower.KoalaScalarListDefs

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace KoalaScalarListBank
private def witness_66_2 : CJ1.Block where
  bank := .leftLow
  cap := 15
  free := [(3,0)]
  vectors := [
    [[0,0,0,0,0,0,0x7effc4b5],[0,0,0,0,990],[0,0,0x7effffd5],[1]]]
theorem improved_66_2 : (CJ0.blockMatrix source 66 ((2 : ℤ)-22)).rank ≤ 15 :=
  Fast.cell (z := witness_66_2) (Fast.bands [(44,44,1),(45,45,2),(46,46,3),(47,48,3),(48,50,3),(49,52,3),(50,54,3),(51,56,3),(52,58,3),(53,60,3),(54,62,2),(55,64,1)]) (by decide +kernel) (by decide +kernel)

private def witness_67_0 : CJ1.Block where
  bank := .rightLow
  cap := 8
  free := [(4,0),(6,0)]
  vectors := [
    [[],[],[],[],[1]],
    [[],[],[],[],[],[],[1]]]
theorem improved_67_0 : (CJ0.blockMatrix source 67 ((0 : ℤ)-22)).rank ≤ 8 :=
  Fast.cell (z := witness_67_0) (Fast.bands [(0,60,8),(1,61,6),(2,62,4),(3,63,2)]) (by decide +kernel) (by decide +kernel)

private def witness_67_1 : CJ1.Block where
  bank := .leftLow
  cap := 12
  free := [(2,0),(2,1),(2,2),(3,0)]
  vectors := [
    [[0,0,0,0,1128,4324,12420],[0,0,0x7effffd2,0x7effffa6,0x7effff51],[1]],
    [[0,0,0,0,0,1081,4140],[0,0,0,0x7effffd3,0x7effffa8],[0,1]],
    [[0,0,0,0,0,0,1035],[0,0,0,0,0x7effffd4],[0,0,1]],
    [[0,0,0,0,0,0,30360],[0,0,0,0,0x7efffc23],[],[1]]]
theorem improved_67_1 : (CJ0.blockMatrix source 67 ((1 : ℤ)-22)).rank ≤ 12 :=
  Fast.cell (z := witness_67_1) (Fast.bands [(45,45,1),(46,46,2),(47,48,2),(48,50,2),(49,52,2),(50,54,2),(51,56,2),(52,58,2),(53,60,2),(54,62,2),(55,64,1)]) (by decide +kernel) (by decide +kernel)

private def witness_68_0 : CJ1.Block where
  bank := .rightLow
  cap := 7
  free := [(4,0),(6,0),(8,0)]
  vectors := [
    [[],[],[],[],[1]],
    [[],[],[],[],[],[],[1]],
    [[],[],[],[],[],[],[],[],[1]]]
theorem improved_68_0 : (CJ0.blockMatrix source 68 ((0 : ℤ)-22)).rank ≤ 7 :=
  Fast.cell (z := witness_68_0) (Fast.bands [(0,62,7),(1,63,5),(2,64,3),(3,65,1)]) (by decide +kernel) (by decide +kernel)

private def witness_68_1 : CJ1.Block where
  bank := .leftLow
  cap := 10
  free := [(2,0),(2,1)]
  vectors := [
    [[0,0,0,0,1128,4324],[0,0,0x7effffd2,0x7effffa6],[1]],
    [[0,0,0,0,0,1081],[0,0,0,0x7effffd3],[0,1]]]
theorem improved_68_1 : (CJ0.blockMatrix source 68 ((1 : ℤ)-22)).rank ≤ 10 :=
  Fast.cell (z := witness_68_1) (Fast.bands [(46,46,1),(47,47,2),(48,49,2),(49,51,2),(50,53,2),(51,55,2),(52,57,2),(53,59,2),(54,61,2),(55,63,2),(56,65,1)]) (by decide +kernel) (by decide +kernel)

private def witness_69_0 : CJ1.Block where
  bank := .rightLow
  cap := 6
  free := [(4,0),(6,0),(8,0),(10,0)]
  vectors := [
    [[],[],[],[],[1]],
    [[],[],[],[],[],[],[1]],
    [[],[],[],[],[],[],[],[],[1]],
    [[],[],[],[],[],[],[],[],[],[],[1]]]
theorem improved_69_0 : (CJ0.blockMatrix source 69 ((0 : ℤ)-22)).rank ≤ 6 :=
  Fast.cell (z := witness_69_0) (Fast.bands [(0,64,6),(1,65,4),(2,66,2)]) (by decide +kernel) (by decide +kernel)

private def witness_69_1 : CJ1.Block where
  bank := .leftLow
  cap := 8
  free := [(2,0)]
  vectors := [
    [[0,0,0,0,1128],[0,0,0x7effffd2],[1]]]
theorem improved_69_1 : (CJ0.blockMatrix source 69 ((1 : ℤ)-22)).rank ≤ 8 :=
  Fast.cell (z := witness_69_1) (Fast.bands [(47,47,1),(48,48,2),(49,50,2),(50,52,2),(51,54,2),(52,56,2),(53,58,2),(54,60,2),(55,62,2),(56,64,2),(57,66,1)]) (by decide +kernel) (by decide +kernel)

private def witness_70_0 : CJ1.Block where
  bank := .leftLow
  cap := 5
  free := [(1,0),(1,1),(1,2),(2,0)]
  vectors := [
    [[0,0,0x7effffcf,0x7effff9f,0x7effff41],[1]],
    [[0,0,0,0x7effffd0,0x7effffa1],[0,1]],
    [[0,0,0,0,0x7effffd1],[0,0,1]],
    [[0,0,0,0,0x7efffb99],[],[1]]]
theorem improved_70_0 : (CJ0.blockMatrix source 70 ((0 : ℤ)-22)).rank ≤ 5 :=
  Fast.cell (z := witness_70_0) (Fast.bands [(48,48,1),(49,50,1),(50,52,1),(51,54,1),(52,56,1),(53,58,1),(54,60,1),(55,62,1),(56,64,1),(57,66,1)]) (by decide +kernel) (by decide +kernel)

private def witness_71_0 : CJ1.Block where
  bank := .leftLow
  cap := 4
  free := [(1,0),(1,1)]
  vectors := [
    [[0,0,0x7effffcf,0x7effff9f],[1]],
    [[0,0,0,0x7effffd0],[0,1]]]
theorem improved_71_0 : (CJ0.blockMatrix source 71 ((0 : ℤ)-22)).rank ≤ 4 :=
  Fast.cell (z := witness_71_0) (Fast.bands [(49,49,1),(50,51,1),(51,53,1),(52,55,1),(53,57,1),(54,59,1),(55,61,1),(56,63,1),(57,65,1),(58,67,1)]) (by decide +kernel) (by decide +kernel)

private def witness_72_0 : CJ1.Block where
  bank := .leftLow
  cap := 3
  free := [(1,0)]
  vectors := [
    [[0,0,0x7effffcf],[1]]]
theorem improved_72_0 : (CJ0.blockMatrix source 72 ((0 : ℤ)-22)).rank ≤ 3 :=
  Fast.cell (z := witness_72_0) (Fast.bands [(50,50,1),(51,52,1),(52,54,1),(53,56,1),(54,58,1),(55,60,1),(56,62,1),(57,64,1),(58,66,1),(59,68,1)]) (by decide +kernel) (by decide +kernel)

end KoalaScalarListBank
