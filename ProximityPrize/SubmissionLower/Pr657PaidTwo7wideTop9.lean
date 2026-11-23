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

namespace Pr657PaidTwo7wideTop9

private abbrev P:=PaidBatch .two7wide 9
private def batch0:List P:=paidGroup ["&16s]r &-N@!v &):Y:M ov_+) $(O40M #~LpVj #@W+]A #:T%U", "lKkY $J:YU #f]1U #$~fU *u|{ *u}! *n,V *u}&", "*n,Z *u}* #B5o6z b@!I% `wfU% $4e=U *n,_ *u}.", "@C2Z *u}2 @C2_ *u}6 @C2c *u}: Uv8_ *u}>"] (by decide +kernel) ++ paidGroup ["Uv8c *u}B Uv8g *u}F Uv-_ @K&B Uv-c @K&F", "#f[bY lK(U Uv-g @K&J lK3c @K&N lK3g @K&R", "lK3k @K&V %>>5g= #$~9g @K&Z #$~9k @K&_ $4dnb", "#:S4^ #$~9o @K&c #$~9s @K&g #AgfE) b?~z9 #:S?o"] (by decide +kernel)
private def batch1:List P:=paidGroup ["@K&k #:S?s @K&o %.u?j $4dcf #$~.s U~,k #$~.w", "U~,o #:S4s U~,s #:S4w U~,w #:S4{ U~,{ #:S5!", "U~-! #P):{ U~-& #P);! U~-* #P);& U~-. #P);*", "U~-2 #f[A& U~-6 #P)0& lS32 #P)0* lS36 $Z.xV)"] (by decide +kernel) ++ paidGroup ["#>7^?M @BoY *mi_ lS3: %vmWFn #zzh&- *u~V"]
private def batches:List P:=batch0 ++ batch1
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 130 27 23 = true :=
  checkedWindows tiles 130 27 [8, 8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 9) (hb : a.b ≤ 130) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7wide).t+9) .two7wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7wideTop9

namespace Pr657PaidTwo7wideTop10

private abbrev P:=PaidBatch .two7wide 10
private def batch0:List P:=paidGroup ["&0hsDU &+DHcz %HZ?^^ #A;_?v b*TnM %.v]Y $!]V#n cf;_)", "b*LY% #$~fU @C=U *u|{ $4eHU #P)}U *u}! *n,V", "*u}& *n,Z *u}* *n,_ *u}. @C2Z *u}2 @C2_", "*u}6 @C2c *u}: Uv8_ *u}> Uv8c *u}B #f[mY"] (by decide +kernel) ++ paidGroup ["#$~DY Uv8g *u}F Uv-_ @K&B Uv-c @K&F Uv-g", "@K&J Uv-k @K&N lK3g @K&R $_-$OM #Agf[- lK3k", "@K&V aEnK1 $vBDf #|1hb #$~.^ lK3o @K&Z #$~9k", "@K&_ #$~9o @K&c #$~9s @K&g #$~9w @K&k #:S?s"] (by decide +kernel)
private def batch1:List P:=paidGroup ["@K&o $J9tj #$~.s U~,k #$~.w U~,o #$~.{ U~,s", "#:S4w U~,w #:S4{ U~,{ $4dWn #:S5! U~-! #:S5&", "U~-& #P);! U~-* #P);& U~-. #P);* U~-2 _}[eU", "#$}Sb #P);. U~-6 #P)0& lS32 $ZDE;z #P)0* lS36"] (by decide +kernel) ++ paidGroup ["#{3<PA _<!.Y @Bzf lS3: #zzovY"]
private def batches:List P:=batch0 ++ batch1
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 130 30 20 = true :=
  checkedWindows tiles 130 30 [8, 8, 4]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 10) (hb : a.b ≤ 130) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7wide).t+10) .two7wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7wideTop10

namespace Pr657PaidTwo7wideTop11

private abbrev P:=PaidBatch .two7wide 11
private def batch0:List P:=paidGroup ["&.tX~~ &)|7cM #N0_pz #CEUP~ #A&,#z a[L@M $4ejY #P*AY", "*u|{ *u}! *u}& #:SlY UvCY *n,Z *u}* *n,_", "*u}. `b;7Q #P)rY *n,c *u}2 @C2_ *u}6 @C2c", "*u}: @C2g *u}> $#m<M) #Agfr) Uv8c *u}B Uv8g"] (by decide +kernel) ++ paidGroup ["*u}F @C'g @K&B Uv-c @K&F #:SJ^ Uv!^ Uv-g", "@K&J Uv-k @K&N `wn'Y #f[bb Uv-o @K&R lK3k", "@K&V lK3o @K&Z lK3s @K&_ #$~9o @K&c #$~9s", "@K&g #$~9w @K&k #$~9{ @K&o #$~.s U~,k #P):j"] (by decide +kernel)
private def batch1:List P:=paidGroup ["Uu^f #$~.w U~,o #$~.{ U~,s aEv(j $4dcr #$~/!", "U~,w #:S4{ U~,{ #:S5! U~-! #:S5& U~-& #:S5*", "U~-* #P);& U~-. #P);* U~-2 #P);. U~-6 #:S*.", "lS32 #>M*l) _QSMb #:S*2 lS36 #{3<PA _<!.Y @Bzf"] (by decide +kernel) ++ paidGroup ["lS3: %vmaMY #zzovY"]
private def batches:List P:=batch0 ++ batch1
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 130 33 17 = true :=
  checkedWindows tiles 130 33 [8, 8, 1]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 11) (hb : a.b ≤ 130) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7wide).t+11) .two7wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7wideTop11

namespace Pr657PaidTwo7wideTop12

private abbrev P:=PaidBatch .two7wide 12
private def batch0:List P:=paidGroup ["&,jbc% &(*sWU #~Lpmr bl3DQ %Z!!Y a[D7- `Kf<Q @K1%","#E$D@5 #A}<<% b*LN- #$~fY @C=Y *u}& *n,Z *u}*","*n,_ *u}. *n,c *u}2 @C2_ *u}6 #:Sa^ Uv8^","@C2c *u}: @C2g *u}> @C2k *u}B Uv8g *u}F","@C'g @K&B #$~Db @C'k @K&F Uv-g @K&J Uv-k","@K&N #|1sf #$~9b Uv-o @K&R Uv-s @K&V lK3o","@K&Z lK3s @K&_ a0C-b #|1hj lK3w @K&c #$~9s","@K&g #$~9w @K&k #$~9{ @K&o lK({ U~,k #$~.w"] ++ paidGroup ["U~,o #$~.{ U~,s #$~/! U~,w #$~/& U~,{ #:S5!","U~-! #f[@v lJdr #:S5& U~-& #:S5* U~-* #:S5.","U~-. `62$b #:Rpn #:S52 U~-2 #P);. U~-6 #:S*.","lS32 #:S*2 lS36 _&KX1 _&KoI @BoV @Jn5 U~-B","%vmaXf #>!3YY"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 130 36 14 = true :=
  checkedWindows tiles 130 36 [8, 6]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 12) (hb : a.b ≤ 130) (hj : a.j ≤ 49) :
    Covered ((Final50PriceCaps.start .two7wide).t+12) .two7wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo7wideTop12
