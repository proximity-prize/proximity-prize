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

namespace Pr657PaidTwo6lastTop9

private abbrev P:=PaidBatch .two6last 9
private def batch0:List P:=paidGroup ["&1:@+- &1:@z1 &-h8hr #RGi;I #~P5=Q #@q#T- `e^UA #j!DM", "%y3F{= onFE Cf/I .3)N %;S5VI #|FE9v `9To9 #=v^E", ".3)R Cf/N Cf/R `$!R5 Cf$J .:o! Cf$N .:o&", "Cf$R .:o* CekA CevJ Cmu& #>%Len _)n`) CevN"] (by decide +kernel) ++ paidGroup ["Cmu*"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 120 27 24 = true :=
  checkedWindows tiles 120 27 [8, 8, 8]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 9) (hb : a.b ≤ 120) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6last).t+9) .two6last a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6lastTop9

namespace Pr657PaidTwo6lastTop10

private abbrev P:=PaidBatch .two6last 10
private def batch0:List P:=paidGroup ["&1:@LU &0@8>j &,n(E- #~%-<b #@ZMeA $!T?M #SL(Q on]Q", "$]<-?A #@Dwn) %xzyt% a3fVA $8*EM .3)R .3)V .3)Z", ".2{R .:o! .2{V .:o& Cf$R .:o* .2pR Cmu&", ".2pV Cmu*"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 120 30 21 = true :=
  checkedWindows tiles 120 30 [8, 8, 5]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 10) (hb : a.b ≤ 120) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6last).t+10) .two6last a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6lastTop10

namespace Pr657PaidTwo6lastTop11

private abbrev P:=PaidBatch .two6last 11
private def batch0:List P:=paidGroup ["&1:@n~ &.w|Uz $2XziM '&]pU #~P52Y #A?+l= a_o2I `e^aQ", "%xeG'I Cf:Y .3)Z .:o! on;M Y;5U .2{V .:o&", ".2{Z .:o* Cmu& _)nk5 .2Y> .2pV Cmu*"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 120 33 18 = true :=
  checkedWindows tiles 120 33 [8, 8, 2]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 11) (hb : a.b ≤ 120) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6last).t+11) .two6last a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6lastTop11

namespace Pr657PaidTwo6lastTop12

private abbrev P:=PaidBatch .two6last 12
private def batch0:List P:=paidGroup ["*Ybi#Y 9)^3^ &&$?mA &!;YbU #~:`Bn #@ZMYI `$!tQ #(Cc^", "Cn#) #z~,Q5 %:CNtb #{L4i5 _TwFM .:o* Cf$Y Cmu)", ".:o. .:o2"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 120 36 15 = true :=
  checkedWindows tiles 120 36 [8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 12) (hb : a.b ≤ 120) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6last).t+12) .two6last a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6lastTop12
