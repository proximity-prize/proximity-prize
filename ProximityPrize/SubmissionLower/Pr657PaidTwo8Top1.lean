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

namespace Pr657PaidTwo8Top1

private abbrev P:=PaidBatch .two8 1
private def batch0:List P:=paidGroup ["&17yEv &19-]n &19ML5 &19fS9 &19o-^ &19wd~ $5F~<Y %~@$85", "%}[fPQ %}0nM- %|bnbE %{~;e^ $_/ueU #~$R|r atcI1 #>{|tz", "#Rjj1 #'bR9 XY;= #>fILj -Pv> #{5}0Q _>c%% -PvB", "C&|>"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 3 46 = true :=
  checkedWindows tiles 134 3 [8, 8, 8, 8, 8, 6]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 1) (hb : a.b ≤ 134) (hj : a.j ≤ 48) :
    Covered ((Final50PriceCaps.start .two8).t+1) .two8 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo8Top1

namespace Pr657PaidTwo8Top2

private abbrev P:=PaidBatch .two8 2
private def batch0:List P:=paidGroup ["&18k2n &19E7= &19UU~ &19fub &19oO) &0*405 9T'D^ %~*^v=", "%}F;I9 %|xCEr %|LCZ- #~:(wM #@D97b $_qRl- #~f1&I #Rk!z", "$L{Ev #i?zv #=7cz -Pu{ `NHoj -Pv! -Pv& C&|!", "C&|& XY%! #>{|GQ _jk0f XY%& XY%* XXkv o/+&"] (by decide +kernel) ++ paidGroup ["o/+* -P2^ -P=j o/+."]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 6 43 = true :=
  checkedWindows tiles 134 6 [8, 8, 8, 8, 8, 3]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 2) (hb : a.b ≤ 134) (hj : a.j ≤ 48) :
    Covered ((Final50PriceCaps.start .two8).t+2) .two8 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo8Top2

namespace Pr657PaidTwo8Top3

private abbrev P:=PaidBatch .two8 3
private def batch0:List P:=paidGroup ["&19-Q^ &19MA) &19^`j &19o!M &0*+x= $p8ex5 %}r;VE %}0nA~", "#@.cxE `d|OU %|bnV9 $^5dr% #A(tIE %?;2CE $#C|}9 #=7cb", "XY:b $7H4b #Rjib -Puc -Pug -Puk C&{g C&{k", "$cP5^ $7G{b #RjRb C&{o aHY5Q XY$k XY$o XY$s"] (by decide +kernel) ++ paidGroup ["o/*o o/*s o/*w #'b0s #'b0w #'b0{ #=76w #=76{"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 9 40 = true :=
  checkedWindows tiles 134 9 [8, 8, 8, 8, 8]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 3) (hb : a.b ≤ 134) (hj : a.j ≤ 48) :
    Covered ((Final50PriceCaps.start .two8).t+3) .two8 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo8Top3

namespace Pr657PaidTwo8Top4

private abbrev P:=PaidBatch .two8 4
private def batch0:List P:=paidGroup ["&19E,- &19UJr &19fjU &19oCv &-gg2^ u*IVE $!49S) cRQBE", "atc=A %}[nO- %|xC:f %|LCN~ XY:Q $_ZugU #Bdc8= #RjiQ", "o/@Q -PuR -PuV -PuZ C&{V C&{Z aHY@I $L{/U", "C&{_ #=7AQ XXvQ XY$Z XY$_ XY$c o/*_ o/*c"] (by decide +kernel) ++ paidGroup ["o/*g #'b0c #'b0g #'b0k #'b0o #'alQ o.fY #=76k", "#=76o #=76s $Z1Z|~ _>b>9 C&-E #=76w #Rj<s"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 12 37 = true :=
  checkedWindows tiles 134 12 [8, 8, 8, 8, 5]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 4) (hb : a.b ≤ 134) (hj : a.j ≤ 48) :
    Covered ((Final50PriceCaps.start .two8).t+4) .two8 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo8Top4
