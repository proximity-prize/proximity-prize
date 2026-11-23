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

namespace Pr657PaidTwo6thinwideTop9

private abbrev P:=PaidBatch .two6thinwide 9
private def batch0:List P:=paidGroup ["&/Uk<1 &+,Y+) &'p'*l #LO_Bd #}g#cA #@)g4W #dCAl #8;*p","j2pt (]%: (]%> #dB}b #8:fd j2Nh (T1s (]%B","(T1w (]%F #A#nsQ #?E!Wn #>aD$~ #>5;`) _$*&~ (Js-","#AeLl% b=n+U >*7s (]%J ``!&U #dBrb >*7w (]%N","S]=s (]%R S]=w (]%V j2Cs (]%Z S]2s >2+V","j28o >2+Z j28s >2+_ j28w >2+c #8:9b S[nb","#!e>s >2+g #!e>w >2+k #!e>{ >2+o #8:Dw >2+s","#8:D{ >2+w #8:E! >2+{ #Mm4f S[Wb #8:9w Se1w"] ++ paidGroup ["$$z^rn #CC;D9 #8:9{ Se1{ %,SFE $^Rtj #dB:f #8::!","Se2! #Mm?{ Se2& #Mm@! Se2* #Mm@& Se2. #Mm@*","Se22 #dBF& Se26 #dBF* Se2: #dBF. Se2> #dB;&","j:8: #dB;* j:8> #dB;. j:8B %W[GU #81a9 SS-E","=}yM (ROr #Md}I #dB;2 j:8F #yuA. j:8J #yuA2","j:8N >(wn #yuA6 j:8R #yuA: j:8V $2JG6 j:8Z","#yu66 #!m>V >(lr #yu6: #!m>Z #yu6> #!m>_ $2J<:","#!m>c $2J<> #!m>g $2J<B #!m>k #?E!7U `3uq9 S[,9"] ++ paidGroup ["S[,E #dB0V #!m>o _empY S[Mb #!d{s #!m>s #!d{z","#!e*) (SM% (SM) >)j2 #!m>w (SX2 ([K_ >1hr","j:9& %w9GUM #>JwbM _$;-- >2-: _9n3) >2!5 >2->",">2-B"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 133 27 24 = true :=
  checkedWindows tiles 133 27 [8, 8, 8]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 9) (hb : a.b ≤ 133) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6thinwide).t+9) .two6thinwide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6thinwideTop9

namespace Pr657PaidTwo6thinwideTop10

private abbrev P:=PaidBatch .two6thinwide 10
private def batch0:List P:=paidGroup ["&#qY-h %{cY(f %{M.]~ &)Mk13 &&`@S# #AO#3S #@)gJ` $^T?t","#~a,5v #@kD;M #dC6h #8:|l j2ep (]%: (]%> (T1s","(]%B (T1w (]%F #yv&b #8:Zb j2Cd >*7s (]%J",">*7w (]%N S]=s (]%R S]=w (]%V j2Cs (]%Z","S]2s >2+V j28o >2+Z $^S8f #dB[b #!e3b j28s",">2+_ j28w >2+c #!e>s >2+g #Ec^Bz #@TfEf #?/L;~","#>Jnf- _9]-) =}y5 c!CJ9 #!e>w >2+k _{;:~ _{C#U","$G}yf #!e>{ >2+o #8:Dw >2+s #8:D{ >2+w #8:E!"] ++ paidGroup [">2+{ #8:9w Se1w #8:9{ Se1{ #8::! Se2! #8::&","Se2& #Mm@! Se2* #Mm@& Se2. #yu@n #!ddj #Mm@*","Se22 #dBF& Se26 #dBF* Se2: #dBF. Se2> #Mm5.","j:8: #dB;* j:8> #dB;. j:8B #d:1M #89_r #dB;2","j:8F #dB;6 j:8J #yuA2 j:8N #yuA6 j:8R #yuA:","j:8V `_v7I #d:&U #yuA> j:8Z #yu66 #!m>V #yu6:","#!m>Z >(lv #yu6> #!m>_ #yu6B #!m>c $2J<> #!m>g","$2J<B #!m>k _9e75 >)&A #Mm*_ #!m>o #|++dz (R}J"] ++ paidGroup ["j1_f #!d{s #!m>s #>w!@b _9eoz >)_) >)j2 #!m>w","(SX2 j:!n >1hr j:9& %w9G(z #{FUsA ([b{ Se35",">2-: #{1#V5 _9n3) >2-> >2-B"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 133 30 21 = true :=
  checkedWindows tiles 133 30 [8, 8, 5]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 10) (hb : a.b ≤ 133) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6thinwide).t+10) .two6thinwide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6thinwideTop10

namespace Pr657PaidTwo6thinwideTop11

private abbrev P:=PaidBatch .two6thinwide 11
private def batch0:List P:=paidGroup ["&!asU| &!a{@% &(>/Ah $+}5<[ #}fxox #@)g)S ``!^d #dCLp","#8;5t (]%: (]%> j2Nh >*7l (T1s (]%B (T1w","(]%F #yv&b j28W >)s` (Sbc j2Cd >*7s (]%J",">*7w (]%N #E7^*9 #BI+7- bS;I5 S]=s (]%R a.*=Y","#!e3Q S[n^ (SKb (SKc S]=w (]%V j2Cs (]%Z","S]2s >2+V S]2w >2+Z j28s >2+_ j28w >2+c","#!e>s >2+g #!e>w >2+k #!e>{ >2+o #!e?! >2+s","#8:.f S[cf #8:D{ >2+w #8:E! >2+{ #!e4! Se1w"] ++ paidGroup ["#8:9{ Se1{ #8::! Se2! #yuKn #!doj #8::& Se2&","#Mm@! Se2* #Mm@& Se2. #Mm@* Se22 %B)LQ $GupM","#yu@r #Mm@. Se26 #dBF* Se2: #dBF. Se2> #Mm5.","j:8: #Mm52 j:8> #dB;. j:8B #dB;2 j:8F #dB;6","j:8J #dB;: j:8N #yuA6 j:8R #yuA: j:8V >(wv","#yuA> j:8Z `_v7M #d:&Y #dB0> #!m>V #yu6: #!m>Z","#yu6> #!m>_ >(lz #yu6B #!m>c #yu6F #!m>g $2J<B","#!m>k _O:H9 S[7E #Mm*_ #!m>o #89vb #!dpj #!d{s"] ++ paidGroup ["#!m>s $Zn4{) _9eoz _$2^~ >)_) >)j2 #!m>w #{]+bz","(SX2 ([K_ >1hr j:9& #>JwbM ([b{ Se35 >2-:","#>5DEA _9n3) >2-> >2-B"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 133 33 18 = true :=
  checkedWindows tiles 133 33 [8, 8, 2]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 11) (hb : a.b ≤ 133) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6thinwide).t+11) .two6thinwide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6thinwideTop11

namespace Pr657PaidTwo6thinwideTop12

private abbrev P:=PaidBatch .two6thinwide 12
private def batch0:List P:=paidGroup ["&*G{k3 &&usXx 1=!=t #}g#yK #?q49` #dC6h #8:|l j2ep","(]%: #}%<lY #{rUsn #{0x?v _9]Mf _9eLA #A#wAQ (]%>","`uTBY #yv1d j2C[ >)~d (Smg (T1s (]%B (T1w","(]%F >*7s (]%J >*7w (]%N S]=s (]%R S]=w","(]%V S]={ (]%Z S]2s >2+V S]2w >2+Z #8:Df","S[yf j28s >2+_ j28w >2+c j28{ >2+g #!e>w",">2+k #Mm4U S[Lb >);j (S*k #yubj #!e(f #!e>{",">2+o #!e?! >2+s #8:D{ >2+w #8:E! >2+{ #!e4!"] ++ paidGroup ["Se1w b(2cA #dB/U j1Gf >)%n (Rqr (Rqs $G}nn","#8:9{ Se1{ #8::! Se2! #8::& Se2& #8::* Se2*","#Mm@& Se2. #Mm@* Se22 #Mm@. Se26 #Mm@2 Se2:","#dBF. Se2> #Mm5. j:8: #Mm52 j:8> #dB;. j:8B","#dB;2 j:8F #dB;6 j:8J #d:1U #89_z #dB;: j:8N","#dB;> j:8R #yuA: j:8V #yuA> j:8Z #dB0> #!m>V","#dB0B #!m>Z #yu6> #!m>_ #yu6B #!m>c >(l~ #yu6F","#!m>g #yu6J #!m>k _emY= j1HI #Mm*_ #!m>o _9eX^"] ++ paidGroup ["#!d{s #!m>s _O;#~ S[p- >)j2 #!m>w #{]+n) j2/A","j:!n >1hr j:9& %:=q,z ([b{ Se35 >2-: #>5DPM","_9n3) >2-> >2-B"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 133 36 15 = true :=
  checkedWindows tiles 133 36 [8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 12) (hb : a.b ≤ 133) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6thinwide).t+12) .two6thinwide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6thinwideTop12
