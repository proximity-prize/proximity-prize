import ProximityPrize.SubmissionLower.Compact54Packed

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

set_option linter.defProp false

namespace Pr657PaidOne4Top13
open Compact54Packed (paidGroup checkedWindows)
open K1_13 (Shape)
open K1_13_8 (Valid)
open Final50PriceTableBase (Covered)
open Compact50Cover (PaidBatch tilesOf checks)

private abbrev P:=PaidBatch .one4 13
private def batch0:List P:=paidGroup [")|(7wW 7C`~' &!4K'h %@.}UO #}O&P+ aWi.C #D&O:h #Ad%jd","#@=qj3 ',wK ',wN $1$+G #LE`G ~=HK <_}K ',wR","',wV ',lN '4_{ ',lR '4`! ',lV '4`& R5&W","',lZ '4`* ',l_ '4`. R4xS R4x` ',lc '4`2","aWhSW $FV1` <_r` ',lg '4`6 ',lk '4`: #bxfh","<_rh <gf6 <gf: ',ak <gf> hh,p ',ao <gfB","#@(>7O ',as <gfF ',aw <gfJ ',a{ <gfN <_gx","<gZG <gfR ~=2| <gfV ~='t <_h# R<lR _dF'h"] ++ paidGroup ["R<lV ',V& R<lZ ',V* R<l_ <_]& R<lc"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 39 14 = true :=
  checkedWindows tiles 135 39 [8, 6]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 13) (hb : a.b ≤ 135) (hj : a.j ≤ 52) :
    Covered ((Final50PriceCaps.start .one4).t+13) .one4 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne4Top13
