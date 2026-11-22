import ProximityPrize.SubmissionLower.KoalaScalarListDefs
import ProximityPrize.SubmissionLower.KoalaScalarListCells2

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace KoalaScalarListBank
private def witness_58_4 : CJ1.Block where
  bank := .rightLow
  cap := 50
  free := [(6,2),(8,2),(10,2)]
  vectors := [
    [[0,1],[2,0x7effffff],[1,0x7efffffb,1],[0x7efffffd,6],[0,6,0x7effffff],[0,0x7efffffd],[0,0,1]],
    [[0,3],[6,0x7efffffc],[3,0x7efffff2,2],[0x7efffff8,12],[1,9,0x7efffffe],[0x7efffffd,0x7efffffe],[0,6],[0,0x7efffffd],[0,0,1]],
    [[0,6],[12,0x7efffff9],[6,0x7effffe9,3],[0x7efffff5,16],[4,6,0x7efffffd],[0x7efffff5],[1,12],[0x7efffffd,0x7efffffd],[0,6],[0,0x7efffffd],[0,0,1]]]
theorem improved_58_4 : (CJ0.blockMatrix source 58 ((4 : ℤ)-22)).rank ≤ 50 :=
  Fast.cell (z := witness_58_4) (Fast.bands [(0,45,14),(1,46,12),(2,47,10),(3,48,8),(4,49,6),(5,50,4),(6,51,2)]) (by decide +kernel) (by decide +kernel)

private def witness_58_5 : CJ1.Block where
  bank := .leftLow
  cap := 48
  free := [(6,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,0,0,0,0,0x449c04],[0,0,0,0,0,0,0,0,0,0,0x7ef5f5a9],[0,0,0,0,0,0,0,0,82251],[0,0,0,0,0,0,0x7effdf0d],[0,0,0,0,666],[0,0,0x7effffdd],[1]]]
theorem improved_58_5 : (CJ0.blockMatrix source 58 ((5 : ℤ)-22)).rank ≤ 48 :=
  Fast.cell (z := witness_58_5) (Fast.bands [(36,36,1),(37,37,2),(38,38,3),(39,39,4),(40,40,5),(41,41,6),(42,43,6),(43,45,6),(44,47,6),(45,49,6),(46,51,6),(47,53,5),(48,55,4),(49,57,2)]) (by decide +kernel) (by decide +kernel)

private def witness_59_4 : CJ1.Block where
  bank := .leftLow
  cap := 45
  free := [(5,0),(5,1),(5,2),(6,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,0,0,0x7ef14fdb,0x7e7e32c9,0x7c51e7d9],[0,0,0,0,0,0,0,0,111930,799500,0x3645c0],[0,0,0,0,0,0,0x7effd65d,0x7eff1e89,0x7efcd562],[0,0,0,0,780,2847,7755],[0,0,0x7effffda,0x7effffb9,0x7effff7d],[1]],
    [[0,0,0,0,0,0,0,0,0,0,0,0x7ef30515,0x7e8da6a5],[0,0,0,0,0,0,0,0,0,101270,721240],[0,0,0,0,0,0,0,0x7effd969,0x7eff2f99],[0,0,0,0,0,741,2698],[0,0,0,0x7effffdb,0x7effffbb],[0,1]],
    [[0,0,0,0,0,0,0,0,0,0,0,0,0x7ef490ab],[0,0,0,0,0,0,0,0,0,0,91390],[0,0,0,0,0,0,0,0,0x7effdc4e],[0,0,0,0,0,0,703],[0,0,0,0,0x7effffdc],[0,0,1]],
    [[0,0,0,0,0,0,0,0,0,0,0,0,0x7da8f3ed],[0,0,0,0,0,0,0,0,0,0,0x282960],[0,0,0,0,0,0,0,0,0x7efc3c20],[0,0,0,0,0,0,16872],[0,0,0,0,0x7efffd67],[],[1]]]
theorem improved_59_4 : (CJ0.blockMatrix source 59 ((4 : ℤ)-22)).rank ≤ 45 :=
  Fast.cell (z := witness_59_4) (Fast.bands [(37,37,1),(38,38,2),(39,39,3),(40,40,4),(41,41,5),(42,43,5),(43,45,5),(44,47,5),(45,49,5),(46,51,5),(47,53,5),(48,55,4),(49,57,3),(50,59,1)]) (by decide +kernel) (by decide +kernel)

private def witness_60_3 : CJ1.Block where
  bank := .rightLow
  cap := 40
  free := [(4,1),(6,1),(8,1)]
  vectors := [
    [[0x7f000000],[0x7f000000,2],[3,0x7f000000],[0,0x7efffffe],[0,1]],
    [[0x7effffff],[0x7effffff,3],[4,0x7f000000],[0x7f000000,0x7effffff],[3],[0,0x7efffffe],[0,1]],
    [[0x7efffffe],[0x7efffffe,3],[3,0x7f000000],[0x7efffffe],[6],[0x7f000000,0x7efffffe],[3],[0,0x7efffffe],[0,1]]]
theorem improved_60_3 : (CJ0.blockMatrix source 60 ((3 : ℤ)-22)).rank ≤ 40 :=
  Fast.cell (z := witness_60_3) (Fast.bands [(0,48,13),(1,49,11),(2,50,9),(3,51,7),(4,52,5),(5,53,3),(6,54,1)]) (by decide +kernel) (by decide +kernel)

private def witness_60_4 : CJ1.Block where
  bank := .leftLow
  cap := 40
  free := [(5,0),(5,1)]
  vectors := [
    [[0,0,0,0,0,0,0,0,0,0,0x7ef14fdb,0x7e7e32c9],[0,0,0,0,0,0,0,0,111930,799500],[0,0,0,0,0,0,0x7effd65d,0x7eff1e89],[0,0,0,0,780,2847],[0,0,0x7effffda,0x7effffb9],[1]],
    [[0,0,0,0,0,0,0,0,0,0,0,0x7ef30515],[0,0,0,0,0,0,0,0,0,101270],[0,0,0,0,0,0,0,0x7effd969],[0,0,0,0,0,741],[0,0,0,0x7effffdb],[0,1]]]
theorem improved_60_4 : (CJ0.blockMatrix source 60 ((4 : ℤ)-22)).rank ≤ 40 :=
  Fast.cell (z := witness_60_4) (Fast.bands [(38,38,1),(39,39,2),(40,40,3),(41,41,4),(42,42,5),(43,44,5),(44,46,5),(45,48,5),(46,50,5),(47,52,5),(48,54,5),(49,56,4),(50,58,3),(51,60,1)]) (by decide +kernel) (by decide +kernel)

private def witness_61_3 : CJ1.Block where
  bank := .leftLow
  cap := 36
  free := [(4,0),(4,1),(4,2),(4,3),(5,0),(5,1)]
  vectors := [
    [[0,0,0,0,0,0,0,0,148995,0x109238,0x4b52d0,0x1114440],[0,0,0,0,0,0,0x7effcc45,0x7efee24a,0x7efbe6a9,0x7ef37ce1],[0,0,0,0,903,3360,9349,23048],[0,0,0x7effffd7,0x7effffb2,0x7effff6d,0x7efffeed],[1]],
    [[0,0,0,0,0,0,0,0,0,135751,987280,0x445110],[0,0,0,0,0,0,0,0x7effcfcc,0x7efef64e,0x7efc3241],[0,0,0,0,0,861,3198,8881],[0,0,0,0x7effffd8,0x7effffb4,0x7effff71],[0,1]],
    [[0,0,0,0,0,0,0,0,0,0,123410,895440],[0,0,0,0,0,0,0,0,0x7effd329,0x7eff095d],[0,0,0,0,0,0,820,3040],[0,0,0,0,0x7effffd9,0x7effffb6],[0,0,1]],
    [[0,0,0,0,0,0,0,0,0,0,0,111930],[0,0,0,0,0,0,0,0,0,0x7effd65d],[0,0,0,0,0,0,0,780],[0,0,0,0,0,0x7effffda],[0,0,0,1]],
    [[0,0,0,0,0,0,0,0,0,0,0x3ac098,0x20e09c8],[0,0,0,0,0,0,0,0,0x7efae053,0x7edae9f1],[0,0,0,0,0,0,21320,117000],[0,0,0,0,0x7efffcf5,0x7efff4bb],[],[1]],
    [[0,0,0,0,0,0,0,0,0,0,0,0x33ebb0],[0,0,0,0,0,0,0,0,0,0x7efb5d3f],[0,0,0,0,0,0,0,19760],[0,0,0,0,0,0x7efffd1c],[],[0,1]]]
theorem improved_61_3 : (CJ0.blockMatrix source 61 ((3 : ℤ)-22)).rank ≤ 36 :=
  Fast.cell (z := witness_61_3) (Fast.bands [(39,39,1),(40,40,2),(41,41,3),(42,42,4),(43,44,4),(44,46,4),(45,48,4),(46,50,4),(47,52,4),(48,54,4),(49,56,4),(50,58,3),(51,60,2)]) (by decide +kernel) (by decide +kernel)

private def witness_61_4 : CJ1.Block where
  bank := .leftLow
  cap := 35
  free := [(5,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,0,0,0x7ef14fdb],[0,0,0,0,0,0,0,0,111930],[0,0,0,0,0,0,0x7effd65d],[0,0,0,0,780],[0,0,0x7effffda],[1]]]
theorem improved_61_4 : (CJ0.blockMatrix source 61 ((4 : ℤ)-22)).rank ≤ 35 :=
  Fast.cell (z := witness_61_4) (Fast.bands [(39,39,1),(40,40,2),(41,41,3),(42,42,4),(43,43,5),(44,45,5),(45,47,5),(46,49,5),(47,51,5),(48,53,5),(49,55,5),(50,57,4),(51,59,3),(52,61,1)]) (by decide +kernel) (by decide +kernel)

private def witness_62_2 : CJ1.Block where
  bank := .rightLow
  cap := 30
  free := [(2,1),(4,1),(6,1)]
  vectors := [
    [[1],[0x7effffff],[0,1]],
    [[1],[0x7f000000],[1],[0x7effffff],[0,1]],
    [[1],[],[2],[0x7effffff],[1],[0x7effffff],[0,1]]]
theorem improved_62_2 : (CJ0.blockMatrix source 62 ((2 : ℤ)-22)).rank ≤ 30 :=
  Fast.cell (z := witness_62_2) (Fast.bands [(0,51,12),(1,52,10),(2,53,8),(3,54,6),(4,55,4),(5,56,2)]) (by decide +kernel) (by decide +kernel)

private def witness_62_3 : CJ1.Block where
  bank := .leftLow
  cap := 32
  free := [(4,0),(4,1),(4,2),(5,0)]
  vectors := [
    [[0,0,0,0,0,0,0,0,148995,0x109238,0x4b52d0],[0,0,0,0,0,0,0x7effcc45,0x7efee24a,0x7efbe6a9],[0,0,0,0,903,3360,9349],[0,0,0x7effffd7,0x7effffb2,0x7effff6d],[1]],
    [[0,0,0,0,0,0,0,0,0,135751,987280],[0,0,0,0,0,0,0,0x7effcfcc,0x7efef64e],[0,0,0,0,0,861,3198],[0,0,0,0x7effffd8,0x7effffb4],[0,1]],
    [[0,0,0,0,0,0,0,0,0,0,123410],[0,0,0,0,0,0,0,0,0x7effd329],[0,0,0,0,0,0,820],[0,0,0,0,0x7effffd9],[0,0,1]],
    [[0,0,0,0,0,0,0,0,0,0,0x3ac098],[0,0,0,0,0,0,0,0,0x7efae053],[0,0,0,0,0,0,21320],[0,0,0,0,0x7efffcf5],[],[1]]]
theorem improved_62_3 : (CJ0.blockMatrix source 62 ((3 : ℤ)-22)).rank ≤ 32 :=
  Fast.cell (z := witness_62_3) (Fast.bands [(40,40,1),(41,41,2),(42,42,3),(43,43,4),(44,45,4),(45,47,4),(46,49,4),(47,51,4),(48,53,4),(49,55,4),(50,57,4),(51,59,3),(52,61,2)]) (by decide +kernel) (by decide +kernel)

private def witness_63_2 : CJ1.Block where
  bank := .rightLow
  cap := 27
  free := [(1,0),(2,1),(3,0),(4,1),(6,1),(8,1)]
  vectors := [
    [[0x7f000000],[1]],
    [[0x7f000000],[],[0,1]],
    [[0x7f000000],[],[0x7f000000],[1]],
    [[0x7effffff],[],[0x7f000000],[],[0,1]],
    [[0x7f000000],[],[],[],[1],[0x7effffff],[0,1]],
    [[],[],[1],[],[2],[0x7effffff],[1],[0x7effffff],[0,1]]]
theorem improved_63_2 : (CJ0.blockMatrix source 63 ((2 : ℤ)-22)).rank ≤ 27 :=
  Fast.cell (z := witness_63_2) (Fast.bands [(0,53,11),(1,54,9),(2,55,7),(3,56,5),(4,57,3),(5,58,1)]) (by decide +kernel) (by decide +kernel)

private def witness_63_3 : CJ1.Block where
  bank := .leftLow
  cap := 28
  free := [(4,0),(4,1)]
  vectors := [
    [[0,0,0,0,0,0,0,0,148995,0x109238],[0,0,0,0,0,0,0x7effcc45,0x7efee24a],[0,0,0,0,903,3360],[0,0,0x7effffd7,0x7effffb2],[1]],
    [[0,0,0,0,0,0,0,0,0,135751],[0,0,0,0,0,0,0,0x7effcfcc],[0,0,0,0,0,861],[0,0,0,0x7effffd8],[0,1]]]
theorem improved_63_3 : (CJ0.blockMatrix source 63 ((3 : ℤ)-22)).rank ≤ 28 :=
  Fast.cell (z := witness_63_3) (Fast.bands [(41,41,1),(42,42,2),(43,43,3),(44,44,4),(45,46,4),(46,48,4),(47,50,4),(48,52,4),(49,54,4),(50,56,4),(51,58,4),(52,60,3),(53,62,2)]) (by decide +kernel) (by decide +kernel)

private def witness_64_1 : CJ1.Block where
  bank := .rightLow
  cap := 20
  free := [(2,0),(4,0)]
  vectors := [
    [[],[0x7f000000],[1]],
    [[],[0x7f000000],[],[0x7f000000],[1]]]
theorem improved_64_1 : (CJ0.blockMatrix source 64 ((1 : ℤ)-22)).rank ≤ 20 :=
  Fast.cell (z := witness_64_1) (Fast.bands [(0,54,11),(1,55,9),(2,56,7),(3,57,5),(4,58,3),(5,59,1)]) (by decide +kernel) (by decide +kernel)

end KoalaScalarListBank
