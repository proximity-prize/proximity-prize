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

namespace Pr657PaidTwo6wideTop5

private abbrev P:=PaidBatch .two6wide 5
private def batch0:List P:=paidGroup ["&15iRY &16,B% &16DI) ,U;,)n 5~Xrf &!cf== %}CD%- '<:D;z", "#}hkT^ #@+Q&v #CE&W1 #APbL5 bU..n #{a$% #:%X% kzA)", "?r*1 `aiur #f-d~ *>v2 ?q|. ?q|2 UG%. %zT]&I", "UG%2 UG%6 $^2I0j kz+2 kz+6 #$Nwz ?qNz #$O12"] (by decide +kernel) ++ paidGroup ["#$O16 #:%72 #:%76 #:%7: `ai=j #f-,v #$Nav ?q8v", "#OW=6 #OW=: #f-C6 %wg(g9 %wg1@Q #f-C: #f-C> #{`I:", "#{`I> #=~Xl= #:%7Z"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 125 15 36 = true :=
  checkedWindows tiles 125 15 [8, 8, 8, 8, 4]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 5) (hb : a.b ≤ 125) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6wide).t+5) .two6wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6wideTop5

namespace Pr657PaidTwo6wideTop6

private abbrev P:=PaidBatch .two6wide 6
private def batch0:List P:=paidGroup ["+we=8% +v?Ljr 5i&ab &(*!/z &(**g5 &$W*=1 %~=T<n $aL)T=","#@+Pxn `ajO~ #~6kc) #@VXyb kzA% *>v& #{`uz #OW^~","UG$z *>_~ *>`! *>v* *>v. ?q|* ?q|. ?q|2","UG%. $Ihvv #f-Mv #:%6z UG%2 kz+. $^2I;v #@m&`5","kz+2 aEF|j $Ihkv #$O1. #$O12 #$O16 #:%72 #:%76","#OW=2 #OW=6 #OW=: #f-C6 #f-C: #f-C> UF(j UF3v","#{`I: #>7.D^ #{`I> #=~Xl= #:%7Z"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 125 18 33 = true :=
  checkedWindows tiles 125 18 [8, 8, 8, 8, 1]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 6) (hb : a.b ≤ 125) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6wide).t+6) .two6wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6wideTop6

namespace Pr657PaidTwo6wideTop7

private abbrev P:=PaidBatch .two6wide 7
private def batch0:List P:=paidGroup ["+:S;M~ *YHA_U 5RPO^ &(*!QA &&K;m= &!cf25 %|u;Sz g!HgU", "#}~8s1 #@A',j #:%d% ?r*) $46)z #OW^z #$OF~ $]ytKv", "#@VPp5 *>v* *>v. `w>{j #{`jv ?q|* ?q|. UG%*", "UG%. kz+* kz+. kz+2 #$O1. #$O12 #:$}v UFTv"] (by decide +kernel) ++ paidGroup ["#:%7. `aiHj #f-7v #:%72 #:%76 #|BHg) `w>Nj #OW=2", "#OW=6 %;9cgQ #|BH[% #OW=: #f-C6 #f-C: #f-C> UF3v", "#{`I: _;O(^ #{`I> #=~Xl= #:%7Z"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 125 21 30 = true :=
  checkedWindows tiles 125 21 [8, 8, 8, 6]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 7) (hb : a.b ≤ 125) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6wide).t+7) .two6wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6wideTop7

namespace Pr657PaidTwo6wideTop8

private abbrev P:=PaidBatch .two6wide 8
private def batch0:List P:=paidGroup ["&16<(~ &0}oNA &-8;qA %Jd^7f #APjwf #@+Q1r #~xI.) #A;7Db", "#{a.~ #:%c~ kzL% *>v& *>v* $45{v #f-dz #$O;z", "?q|& ?q|* ?q|. UG%* UG%. %zT]&I kz+* kz+.", "%<_}5n #A%Xq9 kz+2 $`=|z #f-Bv #$Nwv #$O1. #$O12"] (by decide +kernel) ++ paidGroup ["#:%7. `w>Yn #:%72 #:%76 #OW=2 #OW=6 #OW=: #f-C6", "#f-C: #f-C> #f-CB $Z.@hj #>7&Q1 $IhU. #zz7r% _%zO=", "#:%7Z"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 125 24 27 = true :=
  checkedWindows tiles 125 24 [8, 8, 8, 3]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 8) (hb : a.b ≤ 125) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6wide).t+8) .two6wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6wideTop8
