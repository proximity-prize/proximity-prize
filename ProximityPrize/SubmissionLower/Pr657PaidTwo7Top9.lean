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

namespace Pr657PaidTwo7Top9

private abbrev P:=PaidBatch .two7 9
private def batch0:List P:=paidGroup ["&15c7~ &%%PyM &%%Xcz &+C8k^ r!=[9 #D>^e% #A|46~ b>wZ-","#Nvz9 #9CR9 Tf*9 )]p: )]p> )]pB $u2L= ##n+)","Tef5 )]C9 )]C: #9CG9 ?2v> ?2vB %|HGbj $#UV!^","#AfUWb ?2vF Te|B Te|F Te|J k;%F k;%J k;%N","TeqN )eX. %C:MI $I)qE #Nv7A k:wJ )eX2 k:wN",")eX6 k:wR )eX: ##m}N )eX> ##m}R )eXB ##m}V",")eXF ##m}Z )eXJ #9C&V )eXN #9C&Z )eXR `a*89","#eK'E #9C&_ )eXV #9C&c )eXZ #9BxZ ?:_V #9Bx_"] ++ paidGroup ["?:_Z #9Bxc ?:__ #9Bxg ?:_c #Nu~c ?:_g #Nu~g","?:_k"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 27 23 = true :=
  checkedWindows tiles 134 27 [8, 8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 9) (hb : a.b ≤ 134) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7).t+9) .two7 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7Top9

namespace Pr657PaidTwo7Top10

private abbrev P:=PaidBatch .two7 10
private def batch0:List P:=paidGroup ["&15kAj &.1kRY %Jc|1n #BJ<X~ bk!}- %XnZ5 $#*M~U #Af^b%", ")]p6 #9CR9 ?2v5 )]p: )]p> ?2v: $u2L= $3T$=", "#9CG9 ?2v> ?2vB ?2vF %>~a9~ #CDD]j Te|B Te|F", "Te|J k;%F k;%J k;%N TeqN )eX. %Xm_M $I)qE"] (by decide +kernel) ++ paidGroup ["#Nv7A k:wJ )eX2 k:wN )eX6 k:wR )eX: ##m}N", ")eX> ##m}R )eXB ##m}V )eXF a/2fA ##m}Z )eXJ", "#9C&V )eXN #9C&Z )eXR #9C&_ )eXV #9C&c )eXZ", "#9BxZ ?:_V #9Bx_ ?:_Z #9Bxc ?:__ #9Bxg ?:_c"] (by decide +kernel)
private def batch1:List P:=paidGroup ["#9Bxk ?:_g %9phyE #z~-V ?:_k"]
private def batches:List P:=batch0 ++ batch1
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 30 20 = true :=
  checkedWindows tiles 134 30 [8, 8, 4]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 10) (hb : a.b ≤ 134) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7).t+10) .two7 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7Top10

namespace Pr657PaidTwo7Top11

private abbrev P:=PaidBatch .two7 11
private def batch0:List P:=paidGroup ["&15sKU &,'{{~ #P9>D- $!EplM #A:U`~ a/3b- #{!?5 )]p6","#9CR9 ?2v5 )]p: )]p> ?2v: %-e^A $3T$= #9CG9","?2v> ?2vB ?2vF Te|B $]7Ve- $['plE $ZC58Q #>6D5A","_:mtz #AfUWj Te|F `JTG~ _fvr1 _:nO9 )[t1 )]!=","$u2AE Te|J k;%F k;%J k;%N TeqN )eX. k:wJ",")eX2 k:wN )eX6 k:wR )eX: k:wV )eX> ##m}R",")eXB ##m}V )eXF ##m}Z )eXJ ##m}_ )eXN #9C&Z",")eXR #eK2Q TeDI #9C&_ )eXV #9C&c )eXZ `4~s9"] ++ paidGroup ["#9BbE ##mrc ?:_V #9Bx_ ?:_Z #9Bxc ?:__ #9Bxg","?:_c #9Bxk ?:_g #zyMKQ #=}w99 #9Bxo ?:_k"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 33 17 = true :=
  checkedWindows tiles 134 33 [8, 8, 1]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 11) (hb : a.b ≤ 134) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7).t+11) .two7 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7Top11

namespace Pr657PaidTwo7Top12

private abbrev P:=PaidBatch .two7 12
private def batch0:List P:=paidGroup [")|*pWz 66Tf5 %C5P=n $^GFL) $[S$}I $ZXq8Y #>bUFQ _fw@j","#D>_I~ $_]]9 #{!49 cN]y9 aZ;c1 $_]Q= )]p6 )]p:",")]p> )]pB ?2v> ?2vB ?2vF Te|B #~wgzb cN]cE","Te|F Te|J Te|N k:l5 ?2I= )]8A )]8B ?2T9",")]C= )]C> k;%J k;%N TeqN )eX. TeqR )eX2","k:wN )eX6 k:wR )eX: k:wV )eX> k:wZ )eXB","#eK=M k:aI ##m}V )eXF ##m}Z )eXJ ##m}_ )eXN","##m}c )eXR #9C&_ )eXV #9C&c )eXZ ##mrc ?:_V"] ++ paidGroup ["#>x*s- _|KmE ##mrg ?:_Z #9Bxc ?:__ Te9Q #9Bxg","?:_c #9Bxk ?:_g #9Bxo ?:_k"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 36 14 = true :=
  checkedWindows tiles 134 36 [8, 6]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 12) (hb : a.b ≤ 134) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7).t+12) .two7 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7Top12
