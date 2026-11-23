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

namespace Pr657PaidTwo7Top1

private abbrev P:=PaidBatch .two7 1
private def batch0:List P:=paidGroup ["&125s9 &14WR% &152VM &15REr 0N0$j% 9P3?n &(k/nj &&Js=z","$fozgM %~<(?r %}Wbpn %},jmI %|^k$b `a+)j _fwAz _:n}%",")]Cz )]O) `5!zz _PDG) _%<%- )]Z% )eMQ $u:mf","#}}VL1 #@lM(r k;15 kC$b %wP&%^ )eXg )eXk )]C{","?2a1 )]Z6 ?:_g _%;Ij _%;a% )]Z: ?:_k"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 3 47 = true :=
  checkedWindows tiles 134 3 [8, 8, 8, 8, 8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 1) (hb : a.b ≤ 134) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7).t+1) .two7 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7Top1

namespace Pr657PaidTwo7Top2

private abbrev P:=PaidBatch .two7 2
private def batch0:List P:=paidGroup ["+uBeC1 &s?1^b /2#;eE 9P3?n &-KiBM &-LK/1 &-Lk{M &(?'@U","&%%Q@5 %Cw7V- #}&N2^ aDf~z $]c`Vr #A%#9^ #|Ap$5 #{G_<A","_PCJ5 _PCaM `JTun #Nvdz k;;~ kC/M )]f! )eXN",")]f& )eXR ##n+v Teqz ?2l! )eXV #|AokE ?2l&",")eXZ %;#NrE #|,4fv #9C&j #9C1v )]Z& ?:_V ?2a!","?:_Z %wOzmj _fvr^ ?2a& ?:__ Teg! ?:_c Teg&","?:_g Teg* ?:_k"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 6 44 = true :=
  checkedWindows tiles 134 6 [8, 8, 8, 8, 8, 4]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 2) (hb : a.b ≤ 134) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7).t+2) .two7 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7Top2

namespace Pr657PaidTwo7Top3

private abbrev P:=PaidBatch .two7 3
private def batch0:List P:=paidGroup ["&14WFr &152KA &15R:f .R=2YI 9P3?n &'/@GE &#rkG% %BP{Kv", "'ya22r #A:UaQ apo8b %},rl% %|^s#= $!0=9n #AP+PI ##nAj", "?2vj ?:j9 $3Svb #eK_f ##n6f )]ek )eX: )]eo", ")eX> )]es )eXB ?2ko )eXF ?2ks )eXJ $]!$S^"] (by decide +kernel) ++ paidGroup ["Teqo )eXN Teqs )eXR `5!7U #9C&b Teqw )eXV", "k:ws )eXZ Tefs ?:_V %wf6XE %wfFw~ #>x+,E k:lo", "?:_Z k:ls ?:__ k:lw ?:_c ?2(Q ?23^ ##mrs", "?:_g ##mrw ?:_k"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 9 41 = true :=
  checkedWindows tiles 134 9 [8, 8, 8, 8, 8, 1]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 3) (hb : a.b ≤ 134) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7).t+3) .two7 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7Top3

namespace Pr657PaidTwo7Top4

private abbrev P:=PaidBatch .two7 4
private def batch0:List P:=paidGroup ["&14Wi= &15J%n &15c,r -60AmI 8V!W^ &%%Ppf %~~Q$I #GB`+%","'ya:<Y #~b<~- #@lM>A %|t?|I `5!zQ %?LiPv ##nAY ?2vY",")]eZ )]p_ )]pc #~b4^b #@lLd9 $I**U #eK_U TeqM","?2`U )]NV )]pg )]e_ )eX. )]ec )eX2 ?2k_",")eX6 `JTSI ?2kc )eX: ?2kg )eX> Teqc )eXB","Teqg )eXF k:wc )eXJ k:wg )eXN k:wk )eXR","#9BxU TeOU ##m}g )eXV ##m}k )eXZ `4~~E #9BmQ","k:lk ?:_V %wf>c- %wfG<E ##mrg ?:_Z ##mrk ?:__"] ++ paidGroup ["##mro ?:_c #>6DK^ _:n.9 #9Bxk ?:_g #9Bxo ?:_k"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 12 38 = true :=
  checkedWindows tiles 134 12 [8, 8, 8, 8, 6]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 4) (hb : a.b ≤ 134) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7).t+4) .two7 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7Top4
