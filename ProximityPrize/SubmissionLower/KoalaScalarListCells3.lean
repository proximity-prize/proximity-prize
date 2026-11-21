import ProximityPrize.SubmissionLower.KoalaScalarListDefs

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace KoalaScalarListBank
private def witness_56_4 : CJ1.Block where
  bank := .rightLow
  cap := 49
  free := [(7,2),(9,2)]
  vectors := [
    [[0,1],[0,3,0x7f000000],[3,0x7efffffb],[1,0x7efffff8,3],[0x7efffffd,9],[0,6,0x7efffffe],[0,0x7efffffd],[0,0,1]],
    [[0,4],[0,12,0x7efffffe],[12,0x7effffed],[4,0x7effffe3,8],[0x7efffff5,24],[1,12,0x7efffffb],[0x7efffffd,0x7efffffd],[0,6],[0,0x7efffffd],[0,0,1]]]
theorem improved_56_4 : (CJ0.blockMatrix source 56 ((4 : ℤ)-21)).rank ≤ 49 :=
  Fast.cell (z := witness_56_4) (Fast.bands [(0,43,14),(1,44,12),(2,45,10),(3,46,8),(4,47,6),(5,48,4),(6,49,2)]) (by decide +kernel) (by decide +kernel)

private def witness_56_5 : CJ1.Block where
  bank := .leftLow
  cap := 48
  free := [(6,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,0,0,0,0,0x3a91ac],[0,0,0,0,0,0,0,0,0,0,0x7ef736f4],[0,0,0,0,0,0,0,0,73815],[0,0,0,0,0,0,0x7effe1a7],[0,0,0,0,630],[0,0,0x7effffde],[1]]]
theorem improved_56_5 : (CJ0.blockMatrix source 56 ((5 : ℤ)-21)).rank ≤ 48 :=
  Fast.cell (z := witness_56_5) (Fast.bands [(35,35,1),(36,36,2),(37,37,3),(38,38,4),(39,39,5),(40,40,6),(41,42,6),(42,44,6),(43,46,6),(44,48,6),(45,50,6),(46,52,5),(47,54,3),(48,56,1)]) (by decide +kernel) (by decide +kernel)

private def witness_57_4 : CJ1.Block where
  bank := .leftLow
  cap := 45
  free := [(5,0),(5,1),(5,2),(6,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,0,0,0x7ef30515,0x7e8da6a5,0x7ca59361],[0,0,0,0,0,0,0,0,101270,721240,0x30ceba],[0,0,0,0,0,0,0x7effd969,0x7eff2f99,0x7efd14eb],[0,0,0,0,741,2698,7329],[0,0,0x7effffdb,0x7effffbb,0x7effff81],[1]],
    [[0,0,0,0,0,0,0,0,0,0,0,0x7ef490ab,0x7e9b9891],[0,0,0,0,0,0,0,0,0,91390,648869],[0,0,0,0,0,0,0,0x7effdc4e,0x7eff3fc7],[0,0,0,0,0,703,2553],[0,0,0,0x7effffdc,0x7effffbd],[0,1]],
    [[0,0,0,0,0,0,0,0,0,0,0,0,0x7ef5f5a9],[0,0,0,0,0,0,0,0,0,0,82251],[0,0,0,0,0,0,0,0,0x7effdf0d],[0,0,0,0,0,0,666],[0,0,0,0,0x7effffdd],[0,0,1]],
    [[0,0,0,0,0,0,0,0,0,0,0,0,0x7ddb27a5],[0,0,0,0,0,0,0,0,0,0,0x232434],[0,0,0,0,0,0,0,0,0x7efc9efc],[0,0,0,0,0,0,15540],[0,0,0,0,0x7efffd8b],[],[1]]]
theorem improved_57_4 : (CJ0.blockMatrix source 57 ((4 : ℤ)-21)).rank ≤ 45 :=
  Fast.cell (z := witness_57_4) (Fast.bands [(36,36,1),(37,37,2),(38,38,3),(39,39,4),(40,40,5),(41,42,5),(42,44,5),(43,46,5),(44,48,5),(45,50,5),(46,52,5),(47,54,4),(48,56,2)]) (by decide +kernel) (by decide +kernel)

private def witness_58_3 : CJ1.Block where
  bank := .rightLow
  cap := 40
  free := [(5,1),(7,1)]
  vectors := [
    [[0,0x7f000000],[0x7effffff,1],[0x7f000000,4],[3,0x7effffff],[0,0x7efffffe],[0,1]],
    [[0,0x7efffffe],[0x7efffffb,2],[0x7efffffe,9],[6,0x7efffffe],[0x7f000000,0x7efffffe],[3],[0,0x7efffffe],[0,1]]]
theorem improved_58_3 : (CJ0.blockMatrix source 58 ((3 : ℤ)-21)).rank ≤ 40 :=
  Fast.cell (z := witness_58_3) (Fast.bands [(0,46,13),(1,47,11),(2,48,9),(3,49,7),(4,50,5),(5,51,3),(6,52,1)]) (by decide +kernel) (by decide +kernel)

private def witness_58_4 : CJ1.Block where
  bank := .leftLow
  cap := 40
  free := [(5,0),(5,1)]
  vectors := [
    [[0,0,0,0,0,0,0,0,0,0,0x7ef30515,0x7e8da6a5],[0,0,0,0,0,0,0,0,101270,721240],[0,0,0,0,0,0,0x7effd969,0x7eff2f99],[0,0,0,0,741,2698],[0,0,0x7effffdb,0x7effffbb],[1]],
    [[0,0,0,0,0,0,0,0,0,0,0,0x7ef490ab],[0,0,0,0,0,0,0,0,0,91390],[0,0,0,0,0,0,0,0x7effdc4e],[0,0,0,0,0,703],[0,0,0,0x7effffdc],[0,1]]]
theorem improved_58_4 : (CJ0.blockMatrix source 58 ((4 : ℤ)-21)).rank ≤ 40 :=
  Fast.cell (z := witness_58_4) (Fast.bands [(37,37,1),(38,38,2),(39,39,3),(40,40,4),(41,41,5),(42,43,5),(43,45,5),(44,47,5),(45,49,5),(46,51,5),(47,53,5),(48,55,4),(49,57,2)]) (by decide +kernel) (by decide +kernel)

private def witness_59_3 : CJ1.Block where
  bank := .rightLow
  cap := 36
  free := [(2,1),(3,1),(4,1),(5,1),(7,1),(9,1)]
  vectors := [
    [[1,1],[0x7effffff,0x7f000000],[0,1]],
    [[2,3],[0x7efffffe,0x7efffffe],[],[0,1]],
    [[2,3],[0x7effffff,0x7effffff],[1],[0x7effffff],[0,1]],
    [[6,10],[0x7efffffb,0x7efffffa],[2],[0x7efffffe],[],[0,1]],
    [[3,6],[0x7efffffe,0x7efffffd],[],[],[0x7f000000],[3],[0,0x7efffffe],[0,1]],
    [[0x7f000000],[],[0x7efffffe],[3],[0x7efffffe],[6],[0x7f000000,0x7efffffe],[3],[0,0x7efffffe],[0,1]]]
theorem improved_59_3 : (CJ0.blockMatrix source 59 ((3 : ℤ)-21)).rank ≤ 36 :=
  Fast.cell (z := witness_59_3) (Fast.bands [(0,48,12),(1,49,10),(2,50,8),(3,51,6),(4,52,4),(5,53,2)]) (by decide +kernel) (by decide +kernel)

private def witness_59_4 : CJ1.Block where
  bank := .leftLow
  cap := 35
  free := [(5,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,0,0,0x7ef30515],[0,0,0,0,0,0,0,0,101270],[0,0,0,0,0,0,0x7effd969],[0,0,0,0,741],[0,0,0x7effffdb],[1]]]
theorem improved_59_4 : (CJ0.blockMatrix source 59 ((4 : ℤ)-21)).rank ≤ 35 :=
  Fast.cell (z := witness_59_4) (Fast.bands [(38,38,1),(39,39,2),(40,40,3),(41,41,4),(42,42,5),(43,44,5),(44,46,5),(45,48,5),(46,50,5),(47,52,5),(48,54,5),(49,56,4),(50,58,2)]) (by decide +kernel) (by decide +kernel)

private def witness_60_2 : CJ1.Block where
  bank := .rightLow
  cap := 30
  free := [(3,1),(5,1)]
  vectors := [
    [[1],[1,0x7f000000],[0x7effffff],[0,1]],
    [[2],[2,0x7f000000],[0x7effffff],[1],[0x7effffff],[0,1]]]
theorem improved_60_2 : (CJ0.blockMatrix source 60 ((2 : ℤ)-21)).rank ≤ 30 :=
  Fast.cell (z := witness_60_2) (Fast.bands [(0,49,12),(1,50,10),(2,51,8),(3,52,6),(4,53,4),(5,54,2)]) (by decide +kernel) (by decide +kernel)

private def witness_60_3 : CJ1.Block where
  bank := .leftLow
  cap := 32
  free := [(4,0),(4,1),(4,2),(5,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,135751,987280,0x445110],[0,0,0,0,0,0,0x7effcfcc,0x7efef64e,0x7efc3241],[0,0,0,0,861,3198,8881],[0,0,0x7effffd8,0x7effffb4,0x7effff71],[1]],
    [[0,0,0,0,0,0,0,0,0,123410,895440],[0,0,0,0,0,0,0,0x7effd329,0x7eff095d],[0,0,0,0,0,820,3040],[0,0,0,0x7effffd9,0x7effffb6],[0,1]],
    [[0,0,0,0,0,0,0,0,0,0,111930],[0,0,0,0,0,0,0,0,0x7effd65d],[0,0,0,0,0,0,780],[0,0,0,0,0x7effffda],[0,0,1]],
    [[0,0,0,0,0,0,0,0,0,0,0x33ebb0],[0,0,0,0,0,0,0,0,0x7efb5d3f],[0,0,0,0,0,0,19760],[0,0,0,0,0x7efffd1c],[],[1]]]
theorem improved_60_3 : (CJ0.blockMatrix source 60 ((3 : ℤ)-21)).rank ≤ 32 :=
  Fast.cell (z := witness_60_3) (Fast.bands [(39,39,1),(40,40,2),(41,41,3),(42,42,4),(43,44,4),(44,46,4),(45,48,4),(46,50,4),(47,52,4),(48,54,4),(49,56,4),(50,58,3),(51,60,1)]) (by decide +kernel) (by decide +kernel)

private def witness_61_2 : CJ1.Block where
  bank := .rightLow
  cap := 27
  free := [(1,1),(2,0),(3,1),(5,1),(7,1)]
  vectors := [
    [[0x7f000000],[0,1]],
    [[0x7f000000],[0x7f000000],[1]],
    [[0x7effffff],[0x7f000000],[],[0,1]],
    [[0x7f000000],[],[],[1],[0x7effffff],[0,1]],
    [[],[1],[],[2],[0x7effffff],[1],[0x7effffff],[0,1]]]
theorem improved_61_2 : (CJ0.blockMatrix source 61 ((2 : ℤ)-21)).rank ≤ 27 :=
  Fast.cell (z := witness_61_2) (Fast.bands [(0,51,11),(1,52,9),(2,53,7),(3,54,5),(4,55,3),(5,56,1)]) (by decide +kernel) (by decide +kernel)

private def witness_61_3 : CJ1.Block where
  bank := .leftLow
  cap := 28
  free := [(4,0),(4,1)]
  vectors := [
    [[0,0,0,0,0,0,0,0,135751,987280],[0,0,0,0,0,0,0x7effcfcc,0x7efef64e],[0,0,0,0,861,3198],[0,0,0x7effffd8,0x7effffb4],[1]],
    [[0,0,0,0,0,0,0,0,0,123410],[0,0,0,0,0,0,0,0x7effd329],[0,0,0,0,0,820],[0,0,0,0x7effffd9],[0,1]]]
theorem improved_61_3 : (CJ0.blockMatrix source 61 ((3 : ℤ)-21)).rank ≤ 28 :=
  Fast.cell (z := witness_61_3) (Fast.bands [(40,40,1),(41,41,2),(42,42,3),(43,43,4),(44,45,4),(45,47,4),(46,49,4),(47,51,4),(48,53,4),(49,55,4),(50,57,4),(51,59,3),(52,61,1)]) (by decide +kernel) (by decide +kernel)

private def witness_62_1 : CJ1.Block where
  bank := .rightLow
  cap := 20
  free := [(1,0),(3,0)]
  vectors := [
    [[0x7f000000],[1]],
    [[0x7f000000],[],[0x7f000000],[1]]]
theorem improved_62_1 : (CJ0.blockMatrix source 62 ((1 : ℤ)-21)).rank ≤ 20 :=
  Fast.cell (z := witness_62_1) (Fast.bands [(0,52,11),(1,53,9),(2,54,7),(3,55,5),(4,56,3),(5,57,1)]) (by decide +kernel) (by decide +kernel)

end KoalaScalarListBank
