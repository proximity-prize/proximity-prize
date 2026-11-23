import ProximityPrize.SubmissionLower.Compact54Packed

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

set_option linter.defProp false

namespace Pr657PaidOne5Top13
open Compact54Packed (paidGroup checkedWindows)
open K1_13 (Shape)
open K1_13_8 (Valid)
open Final50PriceTableBase (Covered)
open Compact50Cover (PaidBatch tilesOf checks)

private abbrev P:=PaidBatch .one5 13
private def batch0:List P:=paidGroup ["&13rB' %N46+h #Az2^O b<v$[ %A9ph $!YD%x #?p:[/ #?YeJO","$1Rax #Lu8x i9mx #?Yelp Rd]' RlDS _dv-7 `HSUC","#{[3O/ #7Ixp $ZmDf| #>4KyC %vjNCd"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 39 13 = true :=
  checkedWindows tiles 135 39 [8, 5]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 13) (hb : a.b ≤ 135) (hj : a.j ≤ 51) :
    Covered ((Final50PriceCaps.start .one5).t+13) .one5 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne5Top13
