import ProximityPrize.SubmissionLower.Compact54Packed

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

open Compact54Packed (paidGroup checkedWindows)
open K1_13 (Shape)
open K1_13_8 (Valid)
open Final50PriceTableBase (Covered)
open Compact50Cover (PaidBatch tilesOf checks)

set_option linter.defProp false

namespace Pr657PaidOne6Top5

private abbrev P:=PaidBatch .one6 5
private def batch0:List P:=paidGroup ["-7i413 ,VGETh <iFG^ &)M)Wz &)M9wU &)MJ91 &)MZWj &&`0zQ", "%<GQFv aY$1Q"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 15 36 = true :=
  checkedWindows tiles 135 15 [8, 8, 8, 8, 4]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 5) (hb : a.b ≤ 135) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .one6).t+5) .one6 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne6Top5

namespace Pr657PaidOne6Top6

private abbrev P:=PaidBatch .one6 6
private def batch0:List P:=paidGroup ["+xqN{[ +wM9[' <i>`; +qDl`; &)7}H1 &&IRjv #L9q{z %~|lR%", "%~|u,= %~}(Jv %y-ZFf #>vq2Q %vk0Tj"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 18 33 = true :=
  checkedWindows tiles 135 18 [8, 8, 8, 8, 1]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 6) (hb : a.b ≤ 135) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .one6).t+6) .one6 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne6Top6

namespace Pr657PaidOne6Top7

private abbrev P:=PaidBatch .one6 7
private def batch0:List P:=paidGroup ["4?i%%| <iFG^ &0OSY) &0Odxb &0Ou:= &,h9tp tl`V~ $]w{6U", "#@TWYr #{[z=Q %w#cqv"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 21 30 = true :=
  checkedWindows tiles 135 21 [8, 8, 8, 6]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 7) (hb : a.b ≤ 135) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .one6).t+7) .one6 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne6Top7

namespace Pr657PaidOne6Top8

private abbrev P:=PaidBatch .one6 8
private def batch0:List P:=paidGroup ["&142P= &14JWE &14S1d %Q8}@x %|r}@1 %|1Yq- %>g{^9 $!DX/b", "c!5Gz &QgAQ %w#d+1"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 24 27 = true :=
  checkedWindows tiles 135 24 [8, 8, 8, 3]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 8) (hb : a.b ≤ 135) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .one6).t+8) .one6 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne6Top8
