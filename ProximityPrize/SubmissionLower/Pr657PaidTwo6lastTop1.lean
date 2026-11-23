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

namespace Pr657PaidTwo6lastTop1

private abbrev P:=PaidBatch .two6last 1
private def batch0:List P:=paidGroup ["&17iv5 &19LZ5 &19|w= &1:08~ &.wsf= &,WQM5 %K6Yjn #?vh'1", "`{+~I $8*fz #}V$3b #?vgbz `$!]Y #(CKf onEn Y;?v", ".3({ .3)! %{'V&M $]h4{= #@ZDR^ Cf.{ #iv`% #=nH)", "#=v;U Y;4w Y:pY Cejb on:s %zC$)f on:w `O!Sr"] (by decide +kernel) ++ paidGroup ["#SCB~ #(C@s %ytyU^ #=vFo #=vFs %<M5ZI #}V#7= CeHQ", "#SKLo #SKLs Ce=M #i~Ro #(BZE #i~Rs #=uaA $8)_g", "`O)x1 #SJg= $8)_k #>|]f~ $8)_o $!SMo .:o! $8)Sk", ".:o& $8)So .:o* $8)Hg Cmu& _)mVv $8)Hk Cmu*"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 120 3 48 = true :=
  checkedWindows tiles 120 3 [8, 8, 8, 8, 8, 8]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 1) (hb : a.b ≤ 120) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6last).t+1) .two6last a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6lastTop1

namespace Pr657PaidTwo6lastTop2

private abbrev P:=PaidBatch .two6last 2
private def batch0:List P:=paidGroup ["&18rx1 &19e4b &1:/iI &1:@+- &-}cBU &+^A*M #P=qZ% #}V$Tz", "#?vh'5 `9U2r #=v~~ #~fg]Y #@pwzn `$!]^ #(CKj Y;4r", "Cf.z .3)! .3)& %zo$6r `eT|% #ivk1 #i~^^ Cf/!", "Y;4{ on$b Cejf on:w %z-N:- on:{ #(C@w %y_Fg%"] (by decide +kernel) ++ paidGroup ["#(C@{ #=vFw %<7hS1 #@Dn}U #SK+Q #=vF{ om`U #i~Ro", "`O*1A #SJ}M #i~Rs #i~Rw #i~R{ $!SXw `#~U1 #i~Gw", ".:o! $!SMs .:o& $!SMw .:o* Cdn= CdyI $!SBo", "Cmu& $!SBs Cmu*"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 120 6 45 = true :=
  checkedWindows tiles 120 6 [8, 8, 8, 8, 8, 5]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 2) (hb : a.b ≤ 120) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6last).t+2) .two6last a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6lastTop2

namespace Pr657PaidTwo6lastTop3

private abbrev P:=PaidBatch .two6last 3
private def batch0:List P:=paidGroup ["&19LO% &19u&n &1:0-r &0@/eE &-</v5 &*ycuj &ca7TQ &caH!9", "#A)Mr5 #@/=NI $yf=% #~%,Jj #@Doz% #j!!r #=vhv #(Cb~", ".3)& $8*#f #i~ij #=vQn .3)* Cf/& Y;5! Y;5&", "$]}h$I #A)Ljn $8)j^ on;! `9TAQ #SKAb on;& %yHr0b"] (by decide +kernel) ++ paidGroup ["#(CA! #(CA& a3eeI $8)SU #=vG! #=vG& #SKM! #(BfY", "#SKM& #i~S! #SKB! .:o! %wTUNz %wTV@r %wT_x- #i~G{", ".:o& #i~H! .:o* #i~<w Cmu& #i~<{ Cmu*"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 120 9 42 = true :=
  checkedWindows tiles 120 9 [8, 8, 8, 8, 8, 2]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 3) (hb : a.b ≤ 120) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6last).t+3) .two6last a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6lastTop3

namespace Pr657PaidTwo6lastTop4

private abbrev P:=PaidBatch .two6last 4
private def batch0:List P:=paidGroup ["&19e)Q &19}0Y &1:0O= &/E|A^ &,A|RM $09Ow% #~%,m% #@Dp>=", "`eUbM `O+O% Y;@% Cf:- #=v]z onE~ $]}hEb #@pw{%", ".3). %zC$?~ $d2:j $8*#n #i~ir #=vQv Cf/* Cf/.", "Y;5* %y_FZv `{2u^ Y;5. on;* %y3?*n on;. #(CA*"] (by decide +kernel) ++ paidGroup ["#(CA. #=vG* #=vG. #SKM* #=v<* .:o! #>%LNI omTb", "Ce=f #SKB& .:o& #{L3a% #>PTfI Y:8U #SKB* .:o*", "#SK7! Cmu& #SK7& Cmu*"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 120 12 39 = true :=
  checkedWindows tiles 120 12 [8, 8, 8, 8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 4) (hb : a.b ≤ 120) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6last).t+4) .two6last a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6lastTop4
