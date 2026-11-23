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

namespace Pr657PaidTwo8Top5

private abbrev P:=PaidBatch .two8 5
private def batch0:List P:=paidGroup ["&19M5v &19^T^ &19ntA &/[#J% %LEo!b #B#(<) bBk`5 %G/NA", "%}FCGr $^am+r c~YCA %|bnK- #RjiE o/@E -PuB %?;289", "$#C|r- -PuF -PuJ %G.tM $L{:I #Rj^E -PuN C&{J", "C&{N C&{R XY$N XY$R XY$V o/*R o/*V o/*Z"] (by decide +kernel) ++ paidGroup ["a_/;E o/*_ #'b0Z #'b0_ #'b0c #'b0g #Rj1Q o.fQ", "#=76c #=76g #=76k #=76o #Rj<k #Rj<o #Rj<s"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 15 34 = true :=
  checkedWindows tiles 134 15 [8, 8, 8, 8, 2]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 5) (hb : a.b ≤ 134) (hj : a.j ≤ 48) :
    Covered ((Final50PriceCaps.start .two8).t+5) .two8 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo8Top5

namespace Pr657PaidTwo8Top6

private abbrev P:=PaidBatch .two8 6
private def batch0:List P:=paidGroup ["&19U?b &19f_I &19o8j &-;^bE #Qy14~ $!ut{z #A>If% $y&s=", "$7HJ= #=7n9 %}0nX9 -Pu: -Pu> %|L;[Q -PuB -PuF", "$`)}~Q #C2kO9 %G.tI $L{:E #Rj^A C&{B C&{F C&{J", "XY$F XY$J XY$N XY$R atbWE $y&FQ o/*N o/*R"] (by decide +kernel) ++ paidGroup ["o/*V o/*Z #'b0V #'b0Z #'b0_ #'b0c #=76_ #=76c", "#=76g #=76k #=76o XX>E XXIQ #Rj<k #Rj<o #Rj<s"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 18 31 = true :=
  checkedWindows tiles 134 18 [8, 8, 8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 6) (hb : a.b ≤ 134) (hj : a.j ≤ 48) :
    Covered ((Final50PriceCaps.start .two8).t+6) .two8 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo8Top6

namespace Pr657PaidTwo8Top7

private abbrev P:=PaidBatch .two8 7
private def batch0:List P:=paidGroup ["&19^IM &19g#r &0*+a~ &*c_#A #DBR#% #AjR@z &VsG5 %G/-A", "$L{P= #Rjt9 -Pu6 %|xCP~ $$(ZH- #BdcC9 -Pu: -Pu>", "-PuB %|6nT9 C&{> C&{B C&{F C&{J &+j?U $y&QM", "#i?dE XY$F XY$J XY$N XY$R o/*N o/*R o/*V"] (by decide +kernel) ++ paidGroup ["o/*Z #'b0V #'b0Z #'b0_ #'b0c #'b0g #=76c `8s1E", "#=6}Q #=76g #=76k #=76o #=76s #Rj<o #Rj<s"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 21 28 = true :=
  checkedWindows tiles 134 21 [8, 8, 8, 4]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 7) (hb : a.b ≤ 134) (hj : a.j ≤ 48) :
    Covered ((Final50PriceCaps.start .two8).t+7) .two8 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo8Top7

namespace Pr657PaidTwo8Top8

private abbrev P:=PaidBatch .two8 8
private def batch0:List P:=paidGroup ["&19fS9 &19o-^ &-gfyA $0e)Wf bBkT- %1Y25 $7HU1 $^amAn", "ci'H9 -Pu2 -Pu6 -Pu: %|bnbE -Pu> C&{: #i?oA", "o/5= C&{> %?%]=Q #~{c~1 C&{B C&{F C&{J XY$F", "b-7tI XY$J XY$N XY$R o/*N #~rjQ o.|I o/*R"] (by decide +kernel) ++ paidGroup ["o/*V o/*Z o/*_ #'b0Z #'b0_ #'b0c #'b0g #'b0k", "#=76g #>{|19 `#@+Q o.fY #=76k #=76o #=76s #=76w", "#Rj<s"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 24 25 = true :=
  checkedWindows tiles 134 24 [8, 8, 8, 1]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 8) (hb : a.b ≤ 134) (hj : a.j ≤ 48) :
    Covered ((Final50PriceCaps.start .two8).t+8) .two8 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo8Top8
