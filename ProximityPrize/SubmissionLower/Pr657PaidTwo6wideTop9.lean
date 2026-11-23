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

namespace Pr657PaidTwo6wideTop9

private abbrev P:=PaidBatch .two6wide 9
private def batch0:List P:=paidGroup ["&16D2j &.sx2E &+YLwM #P$J8~ #~LA-- #@m/Cf `ajDv #f.4%","#$OF~ ?q{~ *>v& $_,Z9~ #APbL9 *>v* $Ii/z #f-dz","#$O;z ?q|& ?q|* ?q|. aEG5n $Ii$z UG%* UG%.","kz+* %z?1|1 kz+. kz+2 #$O1. #$O12 #$O16 #:%72","#:%76 #:%7: #:$rz UFIz #OW=6 `K6,j #OVxv #OW=:","#OW=> #f-C: #{^k(% #>7.Ob _%ytY *=cf #f-C> #f-CB","#{`I> $Yut1% _%zO= #:%7Z"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 125 27 24 = true :=
  checkedWindows tiles 125 27 [8, 8, 8]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 9) (hb : a.b ≤ 125) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6wide).t+9) .two6wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6wideTop9

namespace Pr657PaidTwo6wideTop10

private abbrev P:=PaidBatch .two6wide 10
private def batch0:List P:=paidGroup ["&16DT5 &-yw<A &){^}Y #~b|G^ #@VYSn $46?~ #OWt~ #$O^%", "$]dAP~ #@m/!f `aj#r #f-o~ *>v& *>v* ?q|& ?q|*", "?q|. UG%* UG%. UG%2 #$O%z ?qYz kz+. %=.(Lj", "#}R/k1 kz+2 #$O1. aZz0r $`=|~ #{`S~ #$Nwz #$O12"] (by decide +kernel) ++ paidGroup ["#$O16 #:%72 #:%76 #:%7: #OW=6 #OW=: #OW=> #OW=B", "#f-C> #>LXc1 _Q%Dj #f-CB #f-CF #=~Xa1 _%zZI #$O1c"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 125 30 21 = true :=
  checkedWindows tiles 125 30 [8, 8, 5]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 10) (hb : a.b ≤ 125) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6wide).t+10) .two6wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6wideTop10

namespace Pr657PaidTwo6wideTop11

private abbrev P:=PaidBatch .two6wide 11
private def batch0:List P:=paidGroup ["&0<41M &,>+BM $/P~2v aqP2v `ajOz #~bt31 #A%bIj #$OR%", "?r*% *>v& *>v* *>v. #$O;~ ?qp~ ?q|* ?q|.", "UG%* $^t'{% #Ag7RE $Ii$~ #f-X~ #$O0~ UG%. UG%2", "kz+. aZz;v $`>+% kz+2 kz+6 #$O12 #$O16 #$O1:"] (by decide +kernel) ++ paidGroup ["#:%76 #:%7: #:%7> #OW=: #OW=> #OW=B #OW=F UF3v", "UF?% #f-CB #f-CF $Yut1% _%zO= #:%7Z"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 125 33 18 = true :=
  checkedWindows tiles 125 33 [8, 8, 2]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 11) (hb : a.b ≤ 125) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6wide).t+11) .two6wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6wideTop11

namespace Pr657PaidTwo6wideTop12

private abbrev P:=PaidBatch .two6wide 12
private def batch0:List P:=paidGroup ["*Z,}5b 5RPO^ &!cn%n %?y]8) f(8!Q #Ag?rj b*&8v `w?Uz","*>v! *>v& #$OG% ?q|% *>v* *>v. ?q|* $!FQ:=","#A;7.n ?q|. ?q|2 #:%B% UFw% UG%. UG%2 UG%6","#OW1n UFIz ?q9% *>(& #{``% #:%7% kz+2 kz+6","kz+: #$O16 #$O1: #$O1> #:%7: #:%7> #:%7B #OW=>","_}-rv #$Nb% #OW=B #OW=F #OW=J #f-CF _%zO= #:%7Z"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 125 36 15 = true :=
  checkedWindows tiles 125 36 [8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 12) (hb : a.b ≤ 125) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6wide).t+12) .two6wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6wideTop12
