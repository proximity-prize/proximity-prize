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

namespace Pr657PaidTwo7Top5

private abbrev P:=PaidBatch .two7 5
private def batch0:List P:=paidGroup [",WovSn ,VJ8bM 7rD$Q &)8|$n &)9'[) &&a7w5 &!c'Bf %|tYeM","#B`o`5 #@lMT9 $![EPY #Af^V1 $I*@M #eKuM Tf*E ?2vM",")]eN )]pR )]pV )]pZ ?2vV ?2vZ $_]0M ##m}=","?2IE )]8I )]8J TefA ?2TI )]CJ Te|V ?2kV",")eX. ?2kZ )eX2 TeqV )eX6 TeqZ )eX: Teq_",")eX> k:wZ )eXB k:w_ )eXF %<35`9 #@@<,^ `JT=A","#Nv,M k:wc )eXJ ##m}_ )eXN ##m}c )eXR ##m}g",")eXV `JT'9 #9C&c )eXZ ##mrc ?:_V ##mrg ?:_Z"] ++ paidGroup ["k:?E ?2(I )[tM )[tN #9Bxc ?:__ #9Bxg ?:_c","#9Bxk ?:_g #9Bxo ?:_k"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 15 35 = true :=
  checkedWindows tiles 134 15 [8, 8, 8, 8, 3]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 5) (hb : a.b ≤ 134) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7).t+5) .two7 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7Top5

namespace Pr657PaidTwo7Top6

private abbrev P:=PaidBatch .two7 6
private def batch0:List P:=paidGroup ["&15Iw^ &15RQ% &15kX) &-M05f $0vX79 $![MYz #AP+g- apo-9","`a+J= ##nLE Tf5I %},jxU )]pJ %|H7{n )]pN #9CGE","Te|E ?2vJ $_mV]M #B4^of ?2vN ?2vR $_]0E #z~eE","#9C<E Te|N Te|R Te|V TeqN )eX. TeqR )eX2","aDf%= #9Bx5 TeDA )]!E )]!F TeqV )eX6 k:wR",")eX: k:wV )eX> k:wZ )eXB ##m}V )eXF ##m}Z",")eXJ ##m}_ )eXN #9C&Z )eXR #9C&_ )eXV #9C&c",")eXZ ##mrc ?:_V ##mPE Te9I #9Bx_ ?:_Z _fvE-"] ++ paidGroup ["k:49 #9Bxc ?:__ #9Bxg ?:_c #Nu~c ?:_g #zyM@E","#=}w.- #Nu~g ?:_k"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 18 32 = true :=
  checkedWindows tiles 134 18 [8, 8, 8, 8]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 6) (hb : a.b ≤ 134) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7).t+6) .two7 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7Top6

namespace Pr657PaidTwo7Top7

private abbrev P:=PaidBatch .two7 7
private def batch0:List P:=paidGroup ["&15R$I &15k+Q &/mYWY &+C8vj 6x3<A $!0EXv #A%#f) _PD;)","_:o*1 )]N) )]Y5 Tf*5 ?2v= )]e> $[RyG% $ZXh`5","#>bLn- _fvOf #A:U4) )]pB %|t?q= )]pF _|L;~ _PCw-","_%;T1 )]-) )]85 #z~p= )]pJ ##n6= ?2k= ?2vF","%?764j #}QMY- #|,4OE #{GUyQ _P;*E _PC(~ ?2vJ Te|F","Te|J Te|N k;%J k;%N TeqN )eX. k:wJ )eX2","#9C&A TeZA k:wN )eX6 k:wR )eX: k:wV )eX>","`JT=9 #Nv,E ##m}R )eXB aZ:}9 ##m}V )eXF ##m}Z"] ++ paidGroup [")eXJ #9C&V )eXN #9C&Z )eXR #9C&_ )eXV #9C&c",")eXZ #9BbE k:JI #9BxZ ?:_V #9Bx_ ?:_Z #9Bxc","?:__ #9Bxg ?:_c #Nu~c ?:_g #Nu~g ?:_k"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 21 29 = true :=
  checkedWindows tiles 134 21 [8, 8, 8, 5]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 7) (hb : a.b ≤ 134) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7).t+7) .two7 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7Top7

namespace Pr657PaidTwo7Top8

private abbrev P:=PaidBatch .two7 8
private def batch0:List P:=paidGroup ["&15REr &15kLz &-M0*Y $lbPY~ #A%#Z% aDf~1 $![EgM #Af^m%","##nL9 ?3$9 )]p: $_]F= #eKj9 ##nA9 )]p> )]pB","?2v> %|^k$b ?2vB ?2vF Te|B $`&,cE #C.oKj Te|F","Te|J k;%F %-eGE $3SkA #9C1= k;%J k;%N TeqN",")eX. k:wJ )eX2 b)CM= %-e<I k:wN )eX6 k:wR",")eX: ##m}N )eX> ##m}R )eXB ##m}V )eXF ##m}Z",")eXJ #9C&V )eXN #9C&Z )eXR #9C&_ )eXV #9C&c",")eXZ #9BxZ ?:_V #9Bx_ ?:_Z #9Bxc ?:__ #9Bxg"] ++ paidGroup ["?:_c ?1o9 ?1zE #Nu~c ?:_g #Nu~g ?:_k"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 24 26 = true :=
  checkedWindows tiles 134 24 [8, 8, 8, 2]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 8) (hb : a.b ≤ 134) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7).t+8) .two7 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7Top8
