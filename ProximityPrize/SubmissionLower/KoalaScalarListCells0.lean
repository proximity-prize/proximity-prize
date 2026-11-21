import ProximityPrize.SubmissionLower.KoalaScalarListDefs

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace KoalaScalarListBank
private def witness_12_42 : CJ1.Block where
  bank := .rightLow
  cap := 84
  free := [(12,0)]
  vectors := [
    [[1,9,36,84,126,126,84,36,9,1],[0x7efffff5,0x7effff9e,0x7efffe99,0x7efffd0d,0x7efffc11,0x7efffc8f,0x7efffe09,0x7effff4d,0x7effffdd,0x7efffffe],[66,495,1620,3024,3528,2646,1260,360,54,3],[0x7effff25,0x7efffa34,0x7effef21,0x7effe471,0x7effe471,0x7effeec7,0x7efff971,0x7efffe99,0x7effffdd,0x7f000000],[495,2970,7560,10584,8820,4410,1260,180,9],[0x7efffce9,0x7effefc3,0x7effdc91,0x7effd6a9,0x7effe471,0x7efff5ab,0x7efffe09,0x7effffdd],[924,4158,7560,7056,3528,882,84],[0x7efffce9,0x7efff467,0x7effef21,0x7efff431,0x7efffc11,0x7effff83],[495,1485,1620,756,126],[0x7effff25,0x7efffe12,0x7efffe99,0x7effffad],[66,99,36],[0x7efffff5,0x7efffff8],[1]]]
theorem improved_12_42 : (CJ0.blockMatrix source 12 ((42 : ℤ)-22)).rank ≤ 84 :=
  Fast.cell (z := witness_12_42) (Fast.bands [(0,0,13),(1,0,12),(2,0,11),(3,0,10),(4,0,9),(5,0,8),(6,0,7),(7,0,6),(8,0,5),(9,1,3),(10,2,1)]) (by decide +kernel) (by decide +kernel)

private def witness_13_40 : CJ1.Block where
  bank := .rightLow
  cap := 94
  free := [(13,0)]
  vectors := [
    [[0x7f000000,0x7efffff8,0x7effffdd,0x7effffad,0x7effff83,0x7effff83,0x7effffad,0x7effffdd,0x7efffff8,0x7f000000],[13,108,396,840,1134,1008,588,216,45,4],[0x7effffb3,0x7efffdaf,0x7efff845,0x7efff13d,0x7effee49,0x7efff239,0x7efff91d,0x7efffde5,0x7effffa7,0x7efffffb],[286,1980,5940,10080,10584,7056,2940,720,90,4],[0x7efffd36,0x7effee9a,0x7effd199,0x7effbb19,0x7effc1fd,0x7effdd8d,0x7efff485,0x7efffde5,0x7effffd4,0x7f000000],[1287,7128,16632,21168,15876,7056,1764,216,9],[0x7efff94d,0x7effdf85,0x7effbf09,0x7effbb19,0x7effd6a9,0x7efff239,0x7efffdb5,0x7effffdd],[1716,7128,11880,10080,4536,1008,84],[0x7efffafa,0x7effee9a,0x7effe8cd,0x7efff13d,0x7efffb93,0x7effff83],[715,1980,1980,840,126],[0x7efffee3,0x7efffdaf,0x7efffe75,0x7effffad],[78,108,36],[0x7efffff4,0x7efffff8],[1]]]
theorem improved_13_40 : (CJ0.blockMatrix source 13 ((40 : ℤ)-22)).rank ≤ 94 :=
  Fast.cell (z := witness_13_40) (Fast.bands [(0,0,14),(1,0,13),(2,0,12),(3,0,11),(4,0,10),(5,0,9),(6,0,8),(7,0,7),(8,0,6),(9,1,4),(10,2,2)]) (by decide +kernel) (by decide +kernel)

private def witness_13_41 : CJ1.Block where
  bank := .leftLow
  cap := 92
  free := [(10,0)]
  vectors := [
    [[0,0,0,1],[0,0,0,1],[0,0,0,1],[0,0,0,1],[0,0,0,1],[0,0,0,1],[0,0,0,1],[0,0,0,1],[0,0,1],[0,1],[1]]]
theorem improved_13_41 : (CJ0.blockMatrix source 13 ((41 : ℤ)-22)).rank ≤ 92 :=
  Fast.cell (z := witness_13_41) (Fast.bands [(0,0,10),(1,1,10),(2,2,10),(3,3,10),(4,4,10),(5,5,9),(6,6,8),(7,7,7),(8,8,6),(9,9,5),(10,10,4),(11,11,3),(12,12,2),(13,13,1)]) (by decide +kernel) (by decide +kernel)

private def witness_14_39 : CJ1.Block where
  bank := .rightLow
  cap := 102
  free := [(13,0),(14,0)]
  vectors := [
    [[0x7f000000,0x7efffff8,0x7effffdd,0x7effffad,0x7effff83,0x7effff83,0x7effffad,0x7effffdd,0x7efffff8,0x7f000000],[13,108,396,840,1134,1008,588,216,45,4],[0x7effffb3,0x7efffdaf,0x7efff845,0x7efff13d,0x7effee49,0x7efff239,0x7efff91d,0x7efffde5,0x7effffa7,0x7efffffb],[286,1980,5940,10080,10584,7056,2940,720,90,4],[0x7efffd36,0x7effee9a,0x7effd199,0x7effbb19,0x7effc1fd,0x7effdd8d,0x7efff485,0x7efffde5,0x7effffd4,0x7f000000],[1287,7128,16632,21168,15876,7056,1764,216,9],[0x7efff94d,0x7effdf85,0x7effbf09,0x7effbb19,0x7effd6a9,0x7efff239,0x7efffdb5,0x7effffdd],[1716,7128,11880,10080,4536,1008,84],[0x7efffafa,0x7effee9a,0x7effe8cd,0x7efff13d,0x7efffb93,0x7effff83],[715,1980,1980,840,126],[0x7efffee3,0x7efffdaf,0x7efffe75,0x7effffad],[78,108,36],[0x7efffff4,0x7efffff8],[1]],
    [[0x7efffff4,0x7effff8b,0x7efffe25,0x7efffba1,0x7efff963,0x7efff955,0x7efffb85,0x7efffe11,0x7effff84,0x7efffff3],[168,1408,5208,11144,15176,13608,8008,2968,624,56],[0x7efffc18,0x7effe1f5,0x7eff9af1,0x7eff3d51,0x7eff143f,0x7eff46f1,0x7effa299,0x7effe321,0x7efffb24,0x7effffad],[3640,25432,77000,131880,139776,94080,39592,9800,1240,56],[0x7effdcd0,0x7eff22b7,0x7efdac75,0x7efc8381,0x7efcd535,0x7efe3939,0x7eff66e1,0x7effe391,0x7efffd9a,0x7efffff3],[16016,89496,210672,270480,204624,91728,23128,2856,120],[0x7effade4,0x7efe6ed9,0x7efcd781,0x7efca061,0x7efdf69d,0x7eff5171,0x7effe2e9,0x7efffe41,1],[20592,86064,144144,122640,55104,12096,952,0x7efffff9],[0x7effc55a,0x7eff3497,0x7efef14d,0x7eff5561,0x7effce4b,0x7efffb15,28],[8008,22000,21560,8680,1064,0x7effffc9],[0x7efff446,0x7effe875,0x7efff191,0x7efffdd1,70],[728,888,168,0x7effffc9],[0x7effffa6,0x7effffeb,28],[0,0x7efffff9],[1]]]
theorem improved_14_39 : (CJ0.blockMatrix source 14 ((39 : ℤ)-22)).rank ≤ 102 :=
  Fast.cell (z := witness_14_39) (Fast.bands [(0,0,15),(1,0,14),(2,0,13),(3,0,12),(4,0,11),(5,0,10),(6,0,9),(7,0,8),(8,1,6),(9,2,4),(10,3,2)]) (by decide +kernel) (by decide +kernel)

private def witness_14_40 : CJ1.Block where
  bank := .leftLow
  cap := 99
  free := [(10,0)]
  vectors := [
    [[0,0,0,0,1],[0,0,0,0,1],[0,0,0,0,1],[0,0,0,0,1],[0,0,0,0,1],[0,0,0,0,1],[0,0,0,0,1],[0,0,0,1],[0,0,1],[0,1],[1]]]
theorem improved_14_40 : (CJ0.blockMatrix source 14 ((40 : ℤ)-22)).rank ≤ 99 :=
  Fast.cell (z := witness_14_40) (Fast.bands [(0,0,9),(1,1,10),(2,2,10),(3,3,10),(4,4,10),(5,5,10),(6,6,9),(7,7,8),(8,8,7),(9,9,6),(10,10,5),(11,11,4),(12,12,3),(13,13,2),(14,14,1)]) (by decide +kernel) (by decide +kernel)

private def witness_15_38 : CJ1.Block where
  bank := .leftLow
  cap := 109
  free := [(10,0),(10,1)]
  vectors := [
    [[0,0,0,0,11],[0,0,0,0,10],[0,0,0,0,9],[0,0,0,0,8],[0,0,0,0,7],[0,0,0,0,6],[0,0,0,0,5],[0,0,0,4],[0,0,3],[0,2],[1]],
    [[0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,1],[0,0,0,1],[0,0,1],[0,1]]]
theorem improved_15_38 : (CJ0.blockMatrix source 15 ((38 : ℤ)-22)).rank ≤ 109 :=
  Fast.cell (z := witness_15_38) (Fast.bands [(0,0,8),(1,1,9),(2,2,10),(3,3,10),(4,4,10),(5,5,10),(6,6,10),(7,7,9),(8,8,8),(9,9,7),(10,10,6),(11,11,5),(12,12,4),(13,13,3),(14,14,2),(15,15,1)]) (by decide +kernel) (by decide +kernel)

private def witness_15_39 : CJ1.Block where
  bank := .leftLow
  cap := 105
  free := [(10,0)]
  vectors := [
    [[0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,1],[0,0,0,1],[0,0,1],[0,1],[1]]]
theorem improved_15_39 : (CJ0.blockMatrix source 15 ((39 : ℤ)-22)).rank ≤ 105 :=
  Fast.cell (z := witness_15_39) (Fast.bands [(0,0,8),(1,1,9),(2,2,10),(3,3,10),(4,4,10),(5,5,10),(6,6,10),(7,7,9),(8,8,8),(9,9,7),(10,10,6),(11,11,5),(12,12,4),(13,13,3),(14,14,2),(15,15,1)]) (by decide +kernel) (by decide +kernel)

private def witness_16_37 : CJ1.Block where
  bank := .leftLow
  cap := 115
  free := [(10,0),(10,1)]
  vectors := [
    [[0,0,0,0,0,11],[0,0,0,0,0,10],[0,0,0,0,0,9],[0,0,0,0,0,8],[0,0,0,0,0,7],[0,0,0,0,0,6],[0,0,0,0,5],[0,0,0,4],[0,0,3],[0,2],[1]],
    [[0,0,0,0,0,0,1],[0,0,0,0,0,0,1],[0,0,0,0,0,0,1],[0,0,0,0,0,0,1],[0,0,0,0,0,0,1],[0,0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,1],[0,0,0,1],[0,0,1],[0,1]]]
theorem improved_16_37 : (CJ0.blockMatrix source 16 ((37 : ℤ)-22)).rank ≤ 115 :=
  Fast.cell (z := witness_16_37) (Fast.bands [(0,0,7),(1,1,8),(2,2,9),(3,3,10),(4,4,10),(5,5,10),(6,6,10),(7,7,10),(8,8,9),(9,9,8),(10,10,7),(11,11,6),(12,12,5),(13,13,4),(14,14,3),(15,15,2),(16,16,1)]) (by decide +kernel) (by decide +kernel)

private def witness_16_38 : CJ1.Block where
  bank := .leftLow
  cap := 110
  free := [(10,0)]
  vectors := [
    [[0,0,0,0,0,0,1],[0,0,0,0,0,0,1],[0,0,0,0,0,0,1],[0,0,0,0,0,0,1],[0,0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,1],[0,0,0,1],[0,0,1],[0,1],[1]]]
theorem improved_16_38 : (CJ0.blockMatrix source 16 ((38 : ℤ)-22)).rank ≤ 110 :=
  Fast.cell (z := witness_16_38) (Fast.bands [(0,0,7),(1,1,8),(2,2,9),(3,3,10),(4,4,10),(5,5,10),(6,6,10),(7,7,10),(8,8,9),(9,9,8),(10,10,7),(11,11,6),(12,12,5),(13,13,4),(14,14,3),(15,15,2),(16,16,1)]) (by decide +kernel) (by decide +kernel)

private def witness_17_36 : CJ1.Block where
  bank := .leftLow
  cap := 120
  free := [(10,0),(10,1)]
  vectors := [
    [[0,0,0,0,0,0,11],[0,0,0,0,0,0,10],[0,0,0,0,0,0,9],[0,0,0,0,0,0,8],[0,0,0,0,0,0,7],[0,0,0,0,0,6],[0,0,0,0,5],[0,0,0,4],[0,0,3],[0,2],[1]],
    [[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,1],[0,0,0,1],[0,0,1],[0,1]]]
theorem improved_17_36 : (CJ0.blockMatrix source 17 ((36 : ℤ)-22)).rank ≤ 120 :=
  Fast.cell (z := witness_17_36) (Fast.bands [(0,0,6),(1,1,7),(2,2,8),(3,3,9),(4,4,10),(5,5,10),(6,6,10),(7,7,10),(8,8,10),(9,9,9),(10,10,8),(11,11,7),(12,12,6),(13,13,5),(14,14,4),(15,15,3),(16,16,2),(17,17,1)]) (by decide +kernel) (by decide +kernel)

private def witness_17_37 : CJ1.Block where
  bank := .leftLow
  cap := 114
  free := [(10,0)]
  vectors := [
    [[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,1],[0,0,0,1],[0,0,1],[0,1],[1]]]
theorem improved_17_37 : (CJ0.blockMatrix source 17 ((37 : ℤ)-22)).rank ≤ 114 :=
  Fast.cell (z := witness_17_37) (Fast.bands [(0,0,6),(1,1,7),(2,2,8),(3,3,9),(4,4,10),(5,5,10),(6,6,10),(7,7,10),(8,8,10),(9,9,9),(10,10,8),(11,11,7),(12,12,6),(13,13,5),(14,14,4),(15,15,3),(16,16,2),(17,17,1)]) (by decide +kernel) (by decide +kernel)

private def witness_18_35 : CJ1.Block where
  bank := .leftLow
  cap := 124
  free := [(10,0),(10,1)]
  vectors := [
    [[0,0,0,0,0,0,0,11],[0,0,0,0,0,0,0,10],[0,0,0,0,0,0,0,9],[0,0,0,0,0,0,0,8],[0,0,0,0,0,0,7],[0,0,0,0,0,6],[0,0,0,0,5],[0,0,0,4],[0,0,3],[0,2],[1]],
    [[0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,0,1],[0,0,0,0,0,0,0,1],[0,0,0,0,0,0,1],[0,0,0,0,0,1],[0,0,0,0,1],[0,0,0,1],[0,0,1],[0,1]]]
theorem improved_18_35 : (CJ0.blockMatrix source 18 ((35 : ℤ)-22)).rank ≤ 124 :=
  Fast.cell (z := witness_18_35) (Fast.bands [(0,0,5),(1,1,6),(2,2,7),(3,3,8),(4,4,9),(5,5,10),(6,6,10),(7,7,10),(8,8,10),(9,9,10),(10,10,9),(11,11,8),(12,12,7),(13,13,6),(14,14,5),(15,15,4),(16,16,3),(17,17,2),(18,18,1)]) (by decide +kernel) (by decide +kernel)

end KoalaScalarListBank
