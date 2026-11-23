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

namespace Pr657PaidTwo6lastTop5

private abbrev P:=PaidBatch .two6last 5
private def batch0:List P:=paidGroup ["&19tx^ &1:0!f &1:@AI &.bHu= &+^A@j 6P^01 &cJrV~ &am.~)", "#ATV,= #@DpTM a3_=b #~fgs~ #@px45 #(Cc- $8*9~ #j!#%", "#=vi) .3)2 .3)6 Cf/2 `9TWj #SKWz Cf/6 Y;52", "%y3>fI Y;56 %<!=Kv on;2 on;6 #(CA2 #(B|r Y:ev"] (by decide +kernel) ++ paidGroup ["#(CA6 `9T6b #=v%n #=vG2 #(C62 .:o! %wTV5f %wTW'^", "#=v<. .:o& #=v<2 .:o* #{6^qI #=v1* Cmu& #=v1.", "Cmu*"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 120 15 36 = true :=
  checkedWindows tiles 120 15 [8, 8, 8, 8, 4]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 5) (hb : a.b ≤ 120) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6last).t+5) .two6last a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6lastTop5

namespace Pr657PaidTwo6lastTop6

private abbrev P:=PaidBatch .two6last 6
private def batch0:List P:=paidGroup ["&19}%I &1:0D1 &1$kQn &-h8QU $mJbG) au<OY a3fx) $M]x9", "#~:_s1 #@Dp3E onF- Y;@5 %ytyaj .3): .3)> #=vR)", "on;- Cf/: %y3>|b `O*iv #SKX% Y;56 %<!=c1 #@/D/U", "Y;5: Y;5> on;: `O*Rn on;> #(CA: on0: .:o!"] (by decide +kernel) ++ paidGroup ["omkz CeS~ #(C66 .:o& #(C6: .:o* #(C+2 Cmu&", "#(C+6 Cmu*"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 120 18 33 = true :=
  checkedWindows tiles 120 18 [8, 8, 8, 8, 1]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 6) (hb : a.b ≤ 120) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6last).t+6) .two6last a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6lastTop6

namespace Pr657PaidTwo6lastTop7

private abbrev P:=PaidBatch .two6last 7
private def batch0:List P:=paidGroup ["&1:/tU &1:@6= &/r'{% &,n(.n r~$YE &c5Gr- #~%-&E bCDrb", "a_o=1 &,Kg1 #(Cn= $]}h]) #@px4I onF5 Cf/9 .3)>", ".3)B `{3.~ $!S{- Cf/> %xzyhv on;5 Cf/B Y;5>", "Y;5B Y;5F on;B Y;*B .:o! %wTVyQ %wT`Rj on0>"] (by decide +kernel) ++ paidGroup [".:o& on0B .:o* CeHz CeT) on%: Cmu& #>%Len", "on%> Cmu*"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 120 21 30 = true :=
  checkedWindows tiles 120 21 [8, 8, 8, 6]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 7) (hb : a.b ≤ 120) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6last).t+7) .two6last a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6lastTop7

namespace Pr657PaidTwo6lastTop8

private abbrev P:=PaidBatch .two6last 8
private def batch0:List P:=paidGroup ["&1:08~ &1:@Wf &.w|?^ %L[su) #A)M}^ #@/EB5 &WT7= #~fh-A", "#@pxJU #j!.= #=vtA on]E %yHr%U `9To- .3)F .3)J", "%xeFn1 Cf/F Cf/J Y;5F Y;5J #(C65 Y:|9 Cf$J", ".:o! _kL*z omw) Y;*F .:o& Y;*J .:o* Y:|B"] (by decide +kernel) ++ paidGroup ["Cmu& Y:|F Cmu*"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 120 24 27 = true :=
  checkedWindows tiles 120 24 [8, 8, 8, 3]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 8) (hb : a.b ≤ 120) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6last).t+8) .two6last a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6lastTop8
