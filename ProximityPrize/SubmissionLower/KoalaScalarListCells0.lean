import ProximityPrize.SubmissionLower.KoalaScalarListDefs

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace KoalaScalarListBank
private def witness_12_41 : CJ1.Block where
  bank := .rightLow
  cap := 84
  free := [(12,0)]
  vectors := [
    [[1,9,36,84,126,126,84,36,9,1],[0x7efffff5,0x7effff9e,0x7efffe99,0x7efffd0d,0x7efffc11,0x7efffc8f,0x7efffe09,0x7effff4d,0x7effffdd,0x7efffffe],[66,495,1620,3024,3528,2646,1260,360,54,3],[0x7effff25,0x7efffa34,0x7effef21,0x7effe471,0x7effe471,0x7effeec7,0x7efff971,0x7efffe99,0x7effffdd,0x7f000000],[495,2970,7560,10584,8820,4410,1260,180,9],[0x7efffce9,0x7effefc3,0x7effdc91,0x7effd6a9,0x7effe471,0x7efff5ab,0x7efffe09,0x7effffdd],[924,4158,7560,7056,3528,882,84],[0x7efffce9,0x7efff467,0x7effef21,0x7efff431,0x7efffc11,0x7effff83],[495,1485,1620,756,126],[0x7effff25,0x7efffe12,0x7efffe99,0x7effffad],[66,99,36],[0x7efffff5,0x7efffff8],[1]]]
theorem improved_12_41 : (CJ0.blockMatrix source 12 ((41 : ℤ)-21)).rank ≤ 84 :=
  Fast.cell (z := witness_12_41) (Fast.bands [(0,0,13),(1,0,12),(2,0,11),(3,0,10),(4,0,9),(5,0,8),(6,0,7),(7,0,6),(8,0,5),(9,1,3),(10,2,1)]) (by decide +kernel) (by decide +kernel)

private def witness_13_40 : CJ1.Block where
  bank := .leftLow
  cap := 92
  free := [(10,0)]
  vectors := [
    [[0,0,0,1],[0,0,0,1],[0,0,0,1],[0,0,0,1],[0,0,0,1],[0,0,0,1],[0,0,0,1],[0,0,0,1],[0,0,1],[0,1],[1]]]
theorem improved_13_40 : (CJ0.blockMatrix source 13 ((40 : ℤ)-21)).rank ≤ 92 :=
  Fast.cell (z := witness_13_40) (Fast.bands [(0,0,9),(1,1,10),(2,2,10),(3,3,10),(4,4,10),(5,5,9),(6,6,8),(7,7,7),(8,8,6),(9,9,5),(10,10,4),(11,11,3),(12,12,2),(13,13,1)]) (by decide +kernel) (by decide +kernel)

private def witness_14_39 : CJ1.Block where
  bank := .leftLow
  cap := 99
  free := [(10,0)]
  vectors := [
    [[0,0,0,0,1],[0,0,0,0,1],[0,0,0,0,1],[0,0,0,0,1],[0,0,0,0,1],[0,0,0,0,1],[0,0,0,0,1],[0,0,0,1],[0,0,1],[0,1],[1]]]
theorem improved_14_39 : (CJ0.blockMatrix source 14 ((39 : ℤ)-21)).rank ≤ 99 :=
  Fast.cell (z := witness_14_39) (Fast.bands [(0,0,8),(1,1,9),(2,2,10),(3,3,10),(4,4,10),(5,5,10),(6,6,9),(7,7,8),(8,8,7),(9,9,6),(10,10,5),(11,11,4),(12,12,3),(13,13,2),(14,14,1)]) (by decide +kernel) (by decide +kernel)

private def witness_15_38 : CJ1.Block where
  bank := .leftLow
  cap := 105
  free := [(10,0)]
  vectors := [
    [[0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,1],[0,0,0,1],[0,0,1],[0,1],[1]]]
theorem improved_15_38 : (CJ0.blockMatrix source 15 ((38 : ℤ)-21)).rank ≤ 105 :=
  Fast.cell (z := witness_15_38) (Fast.bands [(0,0,7),(1,1,8),(2,2,9),(3,3,10),(4,4,10),(5,5,10),(6,6,10),(7,7,9),(8,8,8),(9,9,7),(10,10,6),(11,11,5),(12,12,4),(13,13,3),(14,14,2),(15,15,1)]) (by decide +kernel) (by decide +kernel)

private def witness_16_37 : CJ1.Block where
  bank := .leftLow
  cap := 110
  free := [(10,0)]
  vectors := [
    [[0,0,0,0,0,0,1],[0,0,0,0,0,0,1],[0,0,0,0,0,0,1],[0,0,0,0,0,0,1],[0,0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,1],[0,0,0,1],[0,0,1],[0,1],[1]]]
theorem improved_16_37 : (CJ0.blockMatrix source 16 ((37 : ℤ)-21)).rank ≤ 110 :=
  Fast.cell (z := witness_16_37) (Fast.bands [(0,0,6),(1,1,7),(2,2,8),(3,3,9),(4,4,10),(5,5,10),(6,6,10),(7,7,10),(8,8,9),(9,9,8),(10,10,7),(11,11,6),(12,12,5),(13,13,4),(14,14,3),(15,15,2),(16,16,1)]) (by decide +kernel) (by decide +kernel)

private def witness_17_36 : CJ1.Block where
  bank := .leftLow
  cap := 114
  free := [(10,0)]
  vectors := [
    [[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,1],[0,0,0,1],[0,0,1],[0,1],[1]]]
theorem improved_17_36 : (CJ0.blockMatrix source 17 ((36 : ℤ)-21)).rank ≤ 114 :=
  Fast.cell (z := witness_17_36) (Fast.bands [(0,0,5),(1,1,6),(2,2,7),(3,3,8),(4,4,9),(5,5,10),(6,6,10),(7,7,10),(8,8,10),(9,9,9),(10,10,8),(11,11,7),(12,12,6),(13,13,5),(14,14,4),(15,15,3),(16,16,2),(17,17,1)]) (by decide +kernel) (by decide +kernel)

private def witness_18_35 : CJ1.Block where
  bank := .leftLow
  cap := 117
  free := [(10,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,1],[0,0,0,1],[0,0,1],[0,1],[1]]]
theorem improved_18_35 : (CJ0.blockMatrix source 18 ((35 : ℤ)-21)).rank ≤ 117 :=
  Fast.cell (z := witness_18_35) (Fast.bands [(0,0,4),(1,1,5),(2,2,6),(3,3,7),(4,4,8),(5,5,9),(6,6,10),(7,7,10),(8,8,10),(9,9,10),(10,10,9),(11,11,8),(12,12,7),(13,13,6),(14,14,5),(15,15,4),(16,16,3),(17,17,2),(18,18,1)]) (by decide +kernel) (by decide +kernel)

private def witness_19_34 : CJ1.Block where
  bank := .leftLow
  cap := 119
  free := [(10,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,1],[0,0,0,1],[0,0,1],[0,1],[1]]]
theorem improved_19_34 : (CJ0.blockMatrix source 19 ((34 : ℤ)-21)).rank ≤ 119 :=
  Fast.cell (z := witness_19_34) (Fast.bands [(0,0,3),(1,1,4),(2,2,5),(3,3,6),(4,4,7),(5,5,8),(6,6,9),(7,7,10),(8,8,10),(9,9,10),(10,10,10),(11,11,9),(12,12,8),(13,13,7),(14,14,6),(15,15,5),(16,16,4),(17,17,3),(18,18,2),(19,19,1)]) (by decide +kernel) (by decide +kernel)

private def witness_20_33 : CJ1.Block where
  bank := .leftLow
  cap := 120
  free := [(10,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,1],[0,0,0,1],[0,0,1],[0,1],[1]]]
theorem improved_20_33 : (CJ0.blockMatrix source 20 ((33 : ℤ)-21)).rank ≤ 120 :=
  Fast.cell (z := witness_20_33) (Fast.bands [(0,0,2),(1,1,3),(2,2,4),(3,3,5),(4,4,6),(5,5,7),(6,6,8),(7,7,9),(8,8,10),(9,9,10),(10,10,10),(11,11,10),(12,12,9),(13,13,8),(14,14,7),(15,15,6),(16,16,5),(17,17,4),(18,18,3),(19,19,2),(20,20,1)]) (by decide +kernel) (by decide +kernel)

private def witness_21_32 : CJ1.Block where
  bank := .leftLow
  cap := 120
  free := [(10,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,1],[0,0,0,1],[0,0,1],[0,1],[1]]]
theorem improved_21_32 : (CJ0.blockMatrix source 21 ((32 : ℤ)-21)).rank ≤ 120 :=
  Fast.cell (z := witness_21_32) (Fast.bands [(0,0,1),(1,1,2),(2,2,3),(3,3,4),(4,4,5),(5,5,6),(6,6,7),(7,7,8),(8,8,9),(9,9,10),(10,10,10),(11,11,10),(12,12,10),(13,13,9),(14,14,8),(15,15,7),(16,16,6),(17,17,5),(18,18,4),(19,19,3),(20,20,2),(21,21,1)]) (by decide +kernel) (by decide +kernel)

private def witness_22_31 : CJ1.Block where
  bank := .leftLow
  cap := 120
  free := [(10,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,1],[0,0,0,1],[0,0,1],[0,1],[1]]]
theorem improved_22_31 : (CJ0.blockMatrix source 22 ((31 : ℤ)-21)).rank ≤ 120 :=
  Fast.cell (z := witness_22_31) (Fast.bands [(1,1,1),(2,2,2),(3,3,3),(4,4,4),(5,5,5),(6,6,6),(7,7,7),(8,8,8),(9,9,9),(10,10,10),(11,11,10),(12,12,10),(13,13,10),(14,14,9),(15,15,8),(16,16,7),(17,17,6),(18,18,5),(19,19,4),(20,20,3),(21,21,2),(22,22,1)]) (by decide +kernel) (by decide +kernel)

private def witness_23_30 : CJ1.Block where
  bank := .leftLow
  cap := 120
  free := [(10,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,1],[0,0,0,1],[0,0,1],[0,1],[1]]]
theorem improved_23_30 : (CJ0.blockMatrix source 23 ((30 : ℤ)-21)).rank ≤ 120 :=
  Fast.cell (z := witness_23_30) (Fast.bands [(2,2,1),(3,3,2),(4,4,3),(5,5,4),(6,6,5),(7,7,6),(8,8,7),(9,9,8),(10,10,9),(11,11,10),(12,12,10),(13,13,10),(14,14,10),(15,15,9),(16,16,8),(17,17,7),(18,18,6),(19,19,5),(20,20,4),(21,21,3),(22,22,2),(23,23,1)]) (by decide +kernel) (by decide +kernel)

end KoalaScalarListBank
