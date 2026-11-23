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

namespace Pr657PaidTwo6wideTop1

private abbrev P:=PaidBatch .two6wide 1
private def batch0:List P:=paidGroup ["&08Kpn &15)}- &15y9Y &16<(~ 0L}|vf 8A&e1 &&K<1U &$AToj", "%C63@A %}-:V= #|nZ'1 a/rsM %{N[Yv %{#dVQ $]!d)= #@A&i)", "%zT]&I `5aj= #OWjM kzAQ *>vR *>vV *>vZ %;{A_v", "#|W|1A ?q|V `w>f% ky}A ?qfE ?q|Z _}.71 #$O&="] (by decide +kernel) ++ paidGroup ["UG%V kz+R kz+V #$O1R #$O1V UFJ1 ?qD9 #:%7R", "#{2jlj #:%7V #zz8Lb _%{*z *>w&"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 125 3 48 = true :=
  checkedWindows tiles 125 3 [8, 8, 8, 8, 8, 8]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 1) (hb : a.b ≤ 125) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6wide).t+1) .two6wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6wideTop1

namespace Pr657PaidTwo6wideTop2

private abbrev P:=PaidBatch .two6wide 2
private def batch0:List P:=paidGroup ["&0dTWA &15Q'= &15y[% &16D2j /n%@Yj 7]H1% &%&2vI &!M3dr", "#GXlYI #~6san #@VY3) %|He-% `K74= %{91R^ %zk1gv %z?1|1", "*>vF #~6k+% #@m&kA UG%= ?q|E *>vJ #f-Y1 #:%B5", "kz+9 *>vN ?q|J UG%F `w>ez $45f- #OW=- UG%J"] (by decide +kernel) ++ paidGroup ["kz+F kz+J #$O1F #$O1J #:%7F #:%7J #OW=F #OW=J", "#>7.Oj ?q!v ?q.% #OW=N #=~XwI _%zqb UG%s"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 125 6 45 = true :=
  checkedWindows tiles 125 6 [8, 8, 8, 8, 8, 5]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 2) (hb : a.b ≤ 125) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6wide).t+2) .two6wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6wideTop2

namespace Pr657PaidTwo6wideTop3

private abbrev P:=PaidBatch .two6wide 3
private def batch0:List P:=paidGroup ["&15)qz &15i^j &16,M1 .Q.%~j 6xjYv &&KKS1 &#1nkM %~'w{~", "#}hk`r #@+Q2- #~L@^- #A%b(j %{e1`j #f-{5 #:%d9 %{#dKE", "`aiuz _}.X) *>v: *>v> %zT[x= *>vB ?q|> ?q|B", "ky}- ?qf1 UG%> UG%B kz+> #$Nx% UFa) kz+B"] (by decide +kernel) ++ paidGroup ["#$O1> %;O91f #?rrm1 _}-}r #:$~% #$O1B #:%7> `K6,j", "#:%7B #OW=> #OW=B kyDv UF>~ #OW=F #f-CB #f-CF", "%vm)=v #=~Xl= _%zfU kz+k"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 125 9 42 = true :=
  checkedWindows tiles 125 9 [8, 8, 8, 8, 8, 2]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 3) (hb : a.b ≤ 125) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6wide).t+3) .two6wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6wideTop3

namespace Pr657PaidTwo6wideTop4

private abbrev P:=PaidBatch .two6wide 4
private def batch0:List P:=paidGroup ["&15Py- &15yOv &16<?= -r2Fbn 6Lb7n &$AT75 %~i]j~ $&/9SU", "'y5xYA #}hcK1 #@A&sn `w?K% _}.z- kzA1 *>v2 *>v6", "*>v: %zk1~1 kz+) ?qq- ?q|6 $]yt5v #@VPY5 $45p~", "#OWG~ #$O1% ?q|: %=CZR^ UG%6 a/qvn $45ez UG%:"] (by decide +kernel) ++ paidGroup ["kz+6 kz+: #$O16 #$O1: #:%76 #:%7: #:%7> #OW=:", "#OW=> %wg(Dr %wg0|- _}-[^ _Q%On UF>z #f-C: #f-C>", "#>LXW% #f-CB ?ptj ?q!v #{`I> #=~Xl= #:%7Z"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 125 12 39 = true :=
  checkedWindows tiles 125 12 [8, 8, 8, 8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 4) (hb : a.b ≤ 125) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6wide).t+4) .two6wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6wideTop4
