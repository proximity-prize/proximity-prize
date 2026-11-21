import ProximityPrize.SubmissionLower.KoalaScalarListDefs

set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace KoalaScalarListBank
private def witness_60_4 : CJ1.Block where
  bank := .leftLow
  cap := 35
  free := [(5,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,0,0,0x7ef30515],[0,0,0,0,0,0,0,0,101270],[0,0,0,0,0,0,0x7effd969],[0,0,0,0,741],[0,0,0x7effffdb],[1]]]
theorem improved_60_4 : (CJ0.blockMatrix source 60 ((4 : ℤ)-22)).rank ≤ 35 :=
  Fast.cell (z := witness_60_4) (Fast.bands [(38,38,1),(39,39,2),(40,40,3),(41,41,4),(42,42,5),(43,44,5),(44,46,5),(45,48,5),(46,50,5),(47,52,5),(48,54,4),(49,56,3),(50,58,2),(51,60,1)]) (by decide +kernel) (by decide +kernel)

private def witness_61_3 : CJ1.Block where
  bank := .leftLow
  cap := 32
  free := [(4,0),(4,1),(4,2),(5,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,135751,987280,0x445110],[0,0,0,0,0,0,0x7effcfcc,0x7efef64e,0x7efc3241],[0,0,0,0,861,3198,8881],[0,0,0x7effffd8,0x7effffb4,0x7effff71],[1]],
    [[0,0,0,0,0,0,0,0,0,123410,895440],[0,0,0,0,0,0,0,0x7effd329,0x7eff095d],[0,0,0,0,0,820,3040],[0,0,0,0x7effffd9,0x7effffb6],[0,1]],
    [[0,0,0,0,0,0,0,0,0,0,111930],[0,0,0,0,0,0,0,0,0x7effd65d],[0,0,0,0,0,0,780],[0,0,0,0,0x7effffda],[0,0,1]],
    [[0,0,0,0,0,0,0,0,0,0,0x33ebb0],[0,0,0,0,0,0,0,0,0x7efb5d3f],[0,0,0,0,0,0,19760],[0,0,0,0,0x7efffd1c],[],[1]]]
theorem improved_61_3 : (CJ0.blockMatrix source 61 ((3 : ℤ)-22)).rank ≤ 32 :=
  Fast.cell (z := witness_61_3) (Fast.bands [(39,39,1),(40,40,2),(41,41,3),(42,42,4),(43,44,4),(44,46,4),(45,48,4),(46,50,4),(47,52,4),(48,54,4),(49,56,3),(50,58,2),(51,60,1)]) (by decide +kernel) (by decide +kernel)

private def witness_62_2 : CJ1.Block where
  bank := .rightLow
  cap := 27
  free := [(4,1),(6,1),(8,1)]
  vectors := [
    [[],[],[1],[0x7effffff],[0,1]],
    [[],[],[1],[0x7f000000],[1],[0x7effffff],[0,1]],
    [[],[],[1],[],[2],[0x7effffff],[1],[0x7effffff],[0,1]]]
theorem improved_62_2 : (CJ0.blockMatrix source 62 ((2 : ℤ)-22)).rank ≤ 27 :=
  Fast.cell (z := witness_62_2) (Fast.bands [(0,52,11),(1,53,9),(2,54,7),(3,55,5),(4,56,3),(5,57,1)]) (by decide +kernel) (by decide +kernel)

private def witness_62_3 : CJ1.Block where
  bank := .leftLow
  cap := 28
  free := [(4,0),(4,1)]
  vectors := [
    [[0,0,0,0,0,0,0,0,135751,987280],[0,0,0,0,0,0,0x7effcfcc,0x7efef64e],[0,0,0,0,861,3198],[0,0,0x7effffd8,0x7effffb4],[1]],
    [[0,0,0,0,0,0,0,0,0,123410],[0,0,0,0,0,0,0,0x7effd329],[0,0,0,0,0,820],[0,0,0,0x7effffd9],[0,1]]]
theorem improved_62_3 : (CJ0.blockMatrix source 62 ((3 : ℤ)-22)).rank ≤ 28 :=
  Fast.cell (z := witness_62_3) (Fast.bands [(40,40,1),(41,41,2),(42,42,3),(43,43,4),(44,45,4),(45,47,4),(46,49,4),(47,51,4),(48,53,4),(49,55,4),(50,57,3),(51,59,2),(52,61,1)]) (by decide +kernel) (by decide +kernel)

private def witness_63_2 : CJ1.Block where
  bank := .rightLow
  cap := 24
  free := [(3,0),(4,1),(5,0),(6,1),(8,1),(10,1)]
  vectors := [
    [[],[],[0x7f000000],[1]],
    [[],[],[0x7f000000],[],[0,1]],
    [[],[],[0x7f000000],[],[0x7f000000],[1]],
    [[],[],[0x7effffff],[],[0x7f000000],[],[0,1]],
    [[],[],[0x7f000000],[],[],[],[1],[0x7effffff],[0,1]],
    [[],[],[],[],[1],[],[2],[0x7effffff],[1],[0x7effffff],[0,1]]]
theorem improved_63_2 : (CJ0.blockMatrix source 63 ((2 : ℤ)-22)).rank ≤ 24 :=
  Fast.cell (z := witness_63_2) (Fast.bands [(0,54,10),(1,55,8),(2,56,6),(3,57,4),(4,58,2)]) (by decide +kernel) (by decide +kernel)

private def witness_63_3 : CJ1.Block where
  bank := .leftLow
  cap := 24
  free := [(4,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,135751],[0,0,0,0,0,0,0x7effcfcc],[0,0,0,0,861],[0,0,0x7effffd8],[1]]]
theorem improved_63_3 : (CJ0.blockMatrix source 63 ((3 : ℤ)-22)).rank ≤ 24 :=
  Fast.cell (z := witness_63_3) (Fast.bands [(41,41,1),(42,42,2),(43,43,3),(44,44,4),(45,46,4),(46,48,4),(47,50,4),(48,52,4),(49,54,4),(50,56,4),(51,58,3),(52,60,2),(53,62,1)]) (by decide +kernel) (by decide +kernel)

private def witness_64_1 : CJ1.Block where
  bank := .rightLow
  cap := 18
  free := [(4,0),(6,0)]
  vectors := [
    [[],[],[],[0x7f000000],[1]],
    [[],[],[],[0x7f000000],[],[0x7f000000],[1]]]
theorem improved_64_1 : (CJ0.blockMatrix source 64 ((1 : ℤ)-22)).rank ≤ 18 :=
  Fast.cell (z := witness_64_1) (Fast.bands [(0,55,10),(1,56,8),(2,57,6),(3,58,4),(4,59,2)]) (by decide +kernel) (by decide +kernel)

private def witness_64_2 : CJ1.Block where
  bank := .leftLow
  cap := 21
  free := [(3,0),(3,1),(3,2),(4,0)]
  vectors := [
    [[0,0,0,0,0,0,0x7effc4b5,0x7efeb36d,0x7efb2661],[0,0,0,0,990,3740,10578],[0,0,0x7effffd5,0x7effffad,0x7effff61],[1]],
    [[0,0,0,0,0,0,0,0x7effc893,0x7efec999],[0,0,0,0,0,946,3569],[0,0,0,0x7effffd6,0x7effffaf],[0,1]],
    [[0,0,0,0,0,0,0,0,0x7effcc45],[0,0,0,0,0,0,903],[0,0,0,0,0x7effffd7],[0,0,1]],
    [[0,0,0,0,0,0,0,0,0x7ef9c92c],[0,0,0,0,0,0,24682],[0,0,0,0,0x7efffca4],[],[1]]]
theorem improved_64_2 : (CJ0.blockMatrix source 64 ((2 : ℤ)-22)).rank ≤ 21 :=
  Fast.cell (z := witness_64_2) (Fast.bands [(42,42,1),(43,43,2),(44,44,3),(45,46,3),(46,48,3),(47,50,3),(48,52,3),(49,54,3),(50,56,3),(51,58,3),(52,60,2),(53,62,1)]) (by decide +kernel) (by decide +kernel)

private def witness_65_1 : CJ1.Block where
  bank := .rightLow
  cap := 16
  free := [(3,0),(4,0),(6,0),(8,0)]
  vectors := [
    [[],[],[],[1]],
    [[],[],[],[],[1]],
    [[],[],[],[],[],[0x7f000000],[1]],
    [[],[],[],[],[],[0x7f000000],[],[0x7f000000],[1]]]
theorem improved_65_1 : (CJ0.blockMatrix source 65 ((1 : ℤ)-22)).rank ≤ 16 :=
  Fast.cell (z := witness_65_1) (Fast.bands [(0,57,9),(1,58,7),(2,59,5),(3,60,3),(4,61,1)]) (by decide +kernel) (by decide +kernel)

private def witness_65_2 : CJ1.Block where
  bank := .leftLow
  cap := 18
  free := [(3,0),(3,1)]
  vectors := [
    [[0,0,0,0,0,0,0x7effc4b5,0x7efeb36d],[0,0,0,0,990,3740],[0,0,0x7effffd5,0x7effffad],[1]],
    [[0,0,0,0,0,0,0,0x7effc893],[0,0,0,0,0,946],[0,0,0,0x7effffd6],[0,1]]]
theorem improved_65_2 : (CJ0.blockMatrix source 65 ((2 : ℤ)-22)).rank ≤ 18 :=
  Fast.cell (z := witness_65_2) (Fast.bands [(43,43,1),(44,44,2),(45,45,3),(46,47,3),(47,49,3),(48,51,3),(49,53,3),(50,55,3),(51,57,3),(52,59,3),(53,61,2),(54,63,1)]) (by decide +kernel) (by decide +kernel)

private def witness_66_0 : CJ1.Block where
  bank := .rightLow
  cap := 9
  free := [(4,0)]
  vectors := [
    [[],[],[],[],[1]]]
theorem improved_66_0 : (CJ0.blockMatrix source 66 ((0 : ℤ)-22)).rank ≤ 9 :=
  Fast.cell (z := witness_66_0) (Fast.bands [(0,58,9),(1,59,7),(2,60,5),(3,61,3),(4,62,1)]) (by decide +kernel) (by decide +kernel)

private def witness_66_1 : CJ1.Block where
  bank := .rightLow
  cap := 14
  free := [(3,0),(4,0),(5,0),(6,0),(8,0),(10,0)]
  vectors := [
    [[],[],[],[1]],
    [[],[],[],[],[1]],
    [[],[],[],[],[],[1]],
    [[],[],[],[],[],[],[1]],
    [[],[],[],[],[],[],[],[0x7f000000],[1]],
    [[],[],[],[],[],[],[],[0x7f000000],[],[0x7f000000],[1]]]
theorem improved_66_1 : (CJ0.blockMatrix source 66 ((1 : ℤ)-22)).rank ≤ 14 :=
  Fast.cell (z := witness_66_1) (Fast.bands [(0,59,8),(1,60,6),(2,61,4),(3,62,2)]) (by decide +kernel) (by decide +kernel)

end KoalaScalarListBank
