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

namespace Pr657PaidTwo6thinTop5

private abbrev P:=PaidBatch .two6thin 5
private def batch0:List P:=paidGroup ["-7ic[; ,VGu!p 9NpUE &)M)Wz &)M9wU &)MBPn &&`(C9 &#[(Sz","#~4r+5 #@?%HI #yg>- $GgV^ $2<9) j#9z =wu% (Dd)","(Dd* $]KjEQ #@TVt9 `u=:M $24:^ (Do. (Do2 (Do6","=wu2 =wu6 SL{2 =w_) SL{6 SL{: =oTF j#$6"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 15 36 = true :=
  checkedWindows tiles 135 15 [8, 8, 8, 8, 4]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 5) (hb : a.b ≤ 135) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6thin).t+5) .two6thin a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6thinTop5

namespace Pr657PaidTwo6thinTop6

private abbrev P:=PaidBatch .two6thin 6
private def batch0:List P:=paidGroup ["+xs!@t +wM9[' 9NpUE &)7[Pb &)7lp= &(=lIf &$?Zs9 $ddk'-", "b=VZE a-pxI $!Z-f- #A95a9 #8+g~ #d3s~ #!UJ~ (Do!", "(Do& (Do* #8#RQ #8+E~ =wu& =wu* =wu. `3_XE", "#8#GQ SL{* SL{. %:S&q- #{[qL~ SL{2 (<YR j#$."] (by decide +kernel) ++ paidGroup ["(<YV j#$2 (<YZ j#$6"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 18 33 = true :=
  checkedWindows tiles 135 18 [8, 8, 8, 8, 1]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 6) (hb : a.b ≤ 135) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6thin).t+6) .two6thin a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6thinTop6

namespace Pr657PaidTwo6thinTop7

private abbrev P:=PaidBatch .two6thin 7
private def batch0:List P:=paidGroup ["&14*FQ &14BMY &14Rm= &/Um+? vJNrC &_qsC7 &_ru8M #CC-65", "#A95w5 aXy=? $_*XlM j#Dv #d3sv #!UJv (Dnw $^<QM", "#y_)M #8#^M (Dn{ (Do! =wt{ =wu! =wu& SL{!", "=w^v SL{& SL{* j#$& %wNY4M %wNbkf $ZWGkE #>a5<-"] (by decide +kernel) ++ paidGroup ["_O$%A (<YN j#$* (<YR j#$. (<YV j#$2 iwlB", "j#$6"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 21 30 = true :=
  checkedWindows tiles 135 21 [8, 8, 8, 6]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 7) (hb : a.b ≤ 135) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6thin).t+7) .two6thin a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6thinTop7

namespace Pr657PaidTwo6thinTop8

private abbrev P:=PaidBatch .two6thin 8
private def batch0:List P:=paidGroup ["&14*hz &14JWE &14S1d %NvRNO #ANi+/ `I5D# _eVn3 _O,D`","%B#Gp %|s((Q %|1Yq- $!p`k~ #Ae=x1 #M^br j#9p (Dns","$^<QI #y_)I #8#^I (Dnw (Dn{ =wtw =wt{ =wu!","SLz{ =w^r SL{! SL{& j#$! _{,<9 #!M+E (<YJ","j#$& (<YN j#$* (<YR j#$. =o`N j#$2 =o`R","j#$6"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 24 27 = true :=
  checkedWindows tiles 135 24 [8, 8, 8, 3]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 8) (hb : a.b ≤ 135) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6thin).t+8) .two6thin a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6thinTop8
