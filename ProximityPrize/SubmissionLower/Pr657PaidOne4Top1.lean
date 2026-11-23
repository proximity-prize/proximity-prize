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

namespace Pr657PaidOne4Top1

private abbrev P:=PaidBatch .one4 1
private def batch0:List P:=paidGroup ["9H]]1 /We|Q c1U,% &*C]E; &12'e/ &12_iW 1-oiSO 9MW_K","%Cpc[; &+)Rgj )9$6tO )9$W>K &'mvwp &!4B!/ %B#8}7 %?`tXx","$`#c)l %~N1&^ %}UIhO %}*I|h %lx[t #A!OW/ #?oj#? %<0kVh","#>ua#t %vitah"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 3 50 = true :=
  checkedWindows tiles 135 3 [8, 8, 8, 8, 8, 8, 2]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 1) (hb : a.b ≤ 135) (hj : a.j ≤ 52) :
    Covered ((Final50PriceCaps.start .one4).t+1) .one4 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne4Top1

namespace Pr657PaidOne4Top2

private abbrev P:=PaidBatch .one4 2
private def batch0:List P:=paidGroup ["%MwWH3 &11m8l &12Vj| &12wYC 0N-AC? 9MW_K &'nK%K &%ddc`", "%DBm#3 &$S:f5 %}klq/ %}*A[h %|[Aq# #|kH(` a,`t| $]vbp#", "#AMWcp #?oij' `t5Kd %xGcq[ #>uX%; _dNRt %:<I*h #={G2/"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 6 47 = true :=
  checkedWindows tiles 135 6 [8, 8, 8, 8, 8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 2) (hb : a.b ≤ 135) (hj : a.j ≤ 52) :
    Covered ((Final50PriceCaps.start .one4).t+2) .one4 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne4Top2

namespace Pr657PaidOne4Top3

private abbrev P:=PaidBatch .one4 3
private def batch0:List P:=paidGroup ["&11-yW &12?3O &12oOW &13*V[ /1}X>` 9MW_K &%8KNO &#YmQl", "k3-op (XopPW %}?tmh %|qu%# #B26.K #@izEW aWi.l %>|84G", "#~_a{x #xV/W `2O%' #?Y6Lx #bx}; #c#ph #|??At #6xXp", "%wcc=| %wcs]W _yyZ/ %w!Ig[ $Z+7N[ '4`s"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 9 44 = true :=
  checkedWindows tiles 135 9 [8, 8, 8, 8, 8, 4]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 3) (hb : a.b ≤ 135) (hj : a.j ≤ 52) :
    Covered ((Final50PriceCaps.start .one4).t+3) .one4 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne4Top3

namespace Pr657PaidOne4Top4

private abbrev P:=PaidBatch .one4 4
private def batch0:List P:=paidGroup ["&11m8l &12Vj| &12wYC .R:O3d 9!O<C &&^e,; &$>JXK %Bd}dx", "'y^_9p #@izEK aWi.` %}*As# %|[Io[ #~I.jh #A!O5G #c#{G", "_yypt aB5Xl `2Nvp %<F8Gh #c#pW ~EG[ _yyf' #{q6|h", "#|)iw[ R=%h %wcc`C %wcs~| _yyZ/ _My6` #>IOI# <gqp"] (by decide +kernel) ++ paidGroup ["<gZ[ <gfh '4`s"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 12 41 = true :=
  checkedWindows tiles 135 12 [8, 8, 8, 8, 8, 1]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 4) (hb : a.b ≤ 135) (hj : a.j ≤ 52) :
    Covered ((Final50PriceCaps.start .one4).t+4) .one4 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne4Top4
