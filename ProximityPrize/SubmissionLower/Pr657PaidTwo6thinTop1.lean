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

namespace Pr657PaidTwo6thinTop1

private abbrev P:=PaidBatch .two6thin 1
private def batch0:List P:=paidGroup ["$r8V69 &12^3f &13_zv &14*Qb 0N-HrC <iFG[ )9$Ufh &)MZz)", "$j+@>~ )8lpT) )5'5j; %~O1{n %~%J@= %{Ll?v %{L|_Q %wd|H9", "%we(!Q #{[rJ% j#EQ %:('>^"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 3 48 = true :=
  checkedWindows tiles 135 3 [8, 8, 8, 8, 8, 8]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 1) (hb : a.b ≤ 135) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6thin).t+1) .two6thin a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6thinTop1

namespace Pr657PaidTwo6thinTop2

private abbrev P:=PaidBatch .two6thin 2
private def batch0:List P:=paidGroup ["&11|!^ &13O6z &14!S% &sS<4n /o2,Rl <iFG^ &iK^./ &)d(=^", "&(i}/f &&IZtU (Xpxlf #}fiqf #@T`MI %wdsAM %wd{xf %wNQ@~", "%wNYx9 %:S/4- #{[r(^ _9V4E =x#Q #=|`?E"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 6 45 = true :=
  checkedWindows tiles 135 6 [8, 8, 8, 8, 8, 5]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 2) (hb : a.b ≤ 135) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6thin).t+2) .two6thin a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6thinTop2

namespace Pr657PaidTwo6thinTop3

private abbrev P:=PaidBatch .two6thin 3
private def batch0:List P:=paidGroup ["&12uSv &13gnI &14*]n .R;h*^ <iN/~ &)d(=^ &'olGU &%9t{A", "(Xpy1- 'yuU=M #}|?%U b=Vqr %;M?y- #?ZFEQ %wdscr %wd|=-", "%we'tE _{,ij j#/9 j#:E =x#I (DoJ (DoN"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 9 42 = true :=
  checkedWindows tiles 135 9 [8, 8, 8, 8, 8, 2]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 3) (hb : a.b ≤ 135) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6thin).t+3) .two6thin a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6thinTop3

namespace Pr657PaidTwo6thinTop4

private abbrev P:=PaidBatch .two6thin 4
private def batch0:List P:=paidGroup ["&13?[) &14!Gv &14+!9 -s@+k` 9NpUE &(itwv &%9lfQ $)s&HM", "'y_0dx '<d,cS %|]c6- $]bGl1 #@TWCQ a-xa- $2<O9 _{,^Y", "#8+F- #!U@5 SM)9 (Do: %wd{mY %we'Fr %we(8j #{rFu9", "_{,RQ (Do> (DoB $ZAzd- =wu> =wuB (<YZ SL{>"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 12 39 = true :=
  checkedWindows tiles 135 12 [8, 8, 8, 8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 4) (hb : a.b ≤ 135) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6thin).t+4) .two6thin a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6thinTop4
