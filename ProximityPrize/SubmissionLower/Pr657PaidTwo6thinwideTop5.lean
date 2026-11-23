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

namespace Pr657PaidTwo6thinwideTop5

private abbrev P:=PaidBatch .two6thinwide 5
private def batch0:List P:=paidGroup ["&13~x= &14IO) &-w|71 &*t'0= &((YR1 2Lf7- #AO#(b #@?<Pr","`uU)% #~JUvz #@kD0U j2f) j2Cj >)~r (Smv (Smw","S]=r >*,z (Sx{ j2Z% >26U (T2* (]%V (T2.","(]%Z (T'& >2+V #yuxn #Mmar #!eIv (T'* >2+Z",">*-& >2+_ >*-* >2+c S]3& >2+g $^[_yA #AeLJ)","S]3* >2+k j29& >2+o `3vJb #8:9n j29* >2+s","#!e?& >2+w #!e?* >2+{ `uKu5 $G}nj #!e4! Se1w","#!e4& Se1{ #!e4* Se2! #!doj >)Fj #8::& Se2&"] ++ paidGroup ["%}+avY #8::* Se2* #Mm@& Se2. #Mm@* Se22 $`Oq*Y","$!pg4b #Mm@. Se26 #dBF* Se2: #yu5n #!dXj #dBF.","Se2> #Mm5. j:8: #dB;* j:8> cMK5I aCSk= $GuYI","#Md}E #dB;. j:8B #dB;2 j:8F #yuA. j:8J #yuA2","j:8N #yuA6 j:8R #yuA: j:8V $2JG6 j:8Z >(ln","(RZo #yu66 #!m>V #yu6: #!m>Z #yu6> #!m>_ $2J<:","#!m>c #yl~U j)3M (JhJ $2J<> #!m>g $G}B: #!m>k","_{B`5 #!dNA (Rr= (RrA #Mm*_ #!m>o _$2GY _$2G^"] ++ paidGroup [">)Gj j1u{ #!m>s #{rU_) #>w!Kn _$2j% _$2j) >)j5","(Sd: #!m>w #>aL]5 _$:sn j:9) Se3. %w9FdU #>JwmY","_OCZA SeIM"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 133 15 36 = true :=
  checkedWindows tiles 133 15 [8, 8, 8, 8, 4]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 5) (hb : a.b ≤ 133) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6thinwide).t+5) .two6thinwide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6thinwideTop5

namespace Pr657PaidTwo6thinwideTop6

private abbrev P:=PaidBatch .two6thinwide 6
private def batch0:List P:=paidGroup ["&141jI &0:@qb &,<8%^ &)!c%E $i1Fj` aC^)j _eo$f _9f_n","_$3Mr (T&j (T1v #dCX% #|V4kb #{]$&r #{FUZA #@To@Y","S]Hv (T1z (T1{ (]%F (]%J (T2! (]%N S]2j","(Smn (Smo >*,r >*7{ (]%R >*8! (]%V #DiTY-","#B3Tx% bS;>1 $2K,j #Mmaj #!eIn S]={ (]%Z >*,{",">2+V >*-! >2+Z `uS~Y #yumf S]2{ >2+_ S]3!",">2+c j28{ >2+g j29! >2+k #!e>{ >2+o #!e?!",">2+s #!e?& >2+w #8:E! >2+{ #!e4! Se1w #8:#f"] ++ paidGroup ["S[Wf #8:9{ Se1{ #8::! Se2! #8::& Se2& $$8x@5","#@k3B= #@k;+5 #Mm@! Se2* %|s6oA #!dXY >)%b (Rqf","(Rqg #!ddf #Mm@& Se2. #Mm@* Se22 #dBF& Se26","%B)AI $GueE #yu5j #dBF* Se2: #dBF. Se2> #dB;&","j:8: #dB;* j:8> #dB;. j:8B #dB;2 j:8F #yuA.","j:8J #yuA2 j:8N #yuA6 j:8R $2JG2 j:8V $2JG6","j:8Z `_v,A #d9xM >(ln #yu66 #!m>V #yu6: #!m>Z","$2J<6 #!m>_ $2J<: #!m>c (JhJ $2J<> #!m>g $G}B:"] ++ paidGroup ["#!m>k _{B`5 #!dNA #dB0V #!m>o _empY j1_f #!d{s","#!m>s $Zn4oz _O;#~ S[p- >)j2 #!m>w _O;EI j:-z",">1s~ Se3. _$;89 ([n1 ([y= >28I %w#qin %:(>')","#>5DPM _9n>5 >2-B"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 133 18 33 = true :=
  checkedWindows tiles 133 18 [8, 8, 8, 8, 1]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 6) (hb : a.b ≤ 133) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6thinwide).t+6) .two6thinwide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6thinwideTop6

namespace Pr657PaidTwo6thinwideTop7

private abbrev P:=PaidBatch .two6thinwide 7
private def batch0:List P:=paidGroup ["&14A[U &.F'N- &*^Pq- &'p'5x n#+Hp #AeU.Q #@?<E^ `uTzl","SeGA j2Yr >*Bv #~v_0r #@k<=% (]%B #!eIY >)sb","(Sbf (Sbg #8:fj j2Nn (T1w (]%F (T1{ (]%J",">*7w (]%N >*7{ (]%R S]=w (]%V S]={ (]%Z","$2J~b #dBgf #!e>f S]2s >2+V S]2w >2+Z S]2{",">2+_ j28w >2+c j28{ >2+g #!e>w >2+k %,[Df","$2Jhb #Mm?b #!e>{ >2+o $_*h3E #A{!P) #!e?! >2+s","#8:D{ >2+w #8:E! >2+{ #8:9w Se1w a-~{1 $^Rtf"] ++ paidGroup ["#8:9{ Se1{ #8::! Se2! #Mm?{ Se2& #Mm@! Se2*","#Mm@& Se2. %?b%WY $#>oVf #dBF! Se22 #dBF& Se26","#dBF* Se2: #dBF. Se2> #dB;& j:8: #d:1E #89_j","#dB;* j:8> #dB;. j:8B #yuA* j:8F #yuA. j:8J","`_v7= #d:&I #yuA2 j:8N bS:MI #yuA6 j:8R $2JG2","j:8V $2JG6 j:8Z >(ln #yu66 #!m>V #yu6: #!m>Z","$2J<6 #!m>_ $2J<: #!m>c #yl~U j)3M (JhJ $2J<>","#!m>g $G}B: #!m>k _{B`5 S[,9 >(xA #dB0V #!m>o"] ++ paidGroup ["#89kU #89vb S[Mb #!d{s #!m>s #{rU_) _9eoz >)_)",">)j2 #!m>w _$3#A #!m>{ #>Jw@) _O;:A #>K!a) Se35","Se>A (]'B %w#qRU (]'F (]'J"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 133 21 30 = true :=
  checkedWindows tiles 133 21 [8, 8, 8, 6]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 7) (hb : a.b ≤ 133) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6thinwide).t+7) .two6thinwide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6thinwideTop7

namespace Pr657PaidTwo6thinwideTop8

private abbrev P:=PaidBatch .two6thinwide 8
private def batch0:List P:=paidGroup ["&14IfA &#/{bl &#0&Kz &)!bw7 %@[PGt %@F%}O #@?<EW `uTzh","#yvit #~JV/v #@To5M j2Yl >*Bp (]%; (]%> #yv1f","#8:ff j2Nj (T1s (]%B (T1w (]%F >*7s (]%J",">*7w (]%N S]=s (]%R S]=w (]%V $G~2b #dBgb","#!e>b j2Cs (]%Z S]2s >2+V #}P<o) #}:oEv #AeLU%","S]2w >2+Z j28s >2+_ aY*V1 `IK[U j28w >2+c","#!e>s >2+g #!e>w >2+k #!e>{ >2+o #8:Dw >2+s","#8:D{ >2+w #8:E! >2+{ #8:#b S[Wb #8:9w Se1w"] ++ paidGroup ["#8:9{ Se1{ #8::! Se2! #Mm?{ Se2& #Mm@! Se2*","#!dXY >)%b (Rqf (Rqg #!ddf #Mm@& Se2. #dBF!","Se22 $`Oy)5 #@k3BI #@Tew= #dBF& Se26 %W[RM $GueE","#yu5j #dBF* Se2: #dBF. Se2> #dB;& j:8: #dB;*","j:8> #dB;. j:8B #dB;2 j:8F b=eGI %,S%Q #yuA.","j:8J #yuA2 j:8N #yuA6 j:8R $2JG2 j:8V $2JG6","j:8Z >(ln (RZo #yu66 #!m>V #yu6: #!m>Z #yu6>","#!m>_ $2J<: #!m>c $2J<> #!m>g >(av $2J<B #!m>k"] ++ paidGroup ["_$2&1 #dB0V #!m>o #?/T;I _O:_U S[Mb #!d{s #!m>s","_9eoz >)_) >)j2 #!m>w %:S>?A j2/A j:!n Sdyv","j:9& %w9G?5 #{FUh5 _$;-- ([c% ([n1 >2-: >2->","_$;!) Se3:"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 133 24 27 = true :=
  checkedWindows tiles 133 24 [8, 8, 8, 3]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 8) (hb : a.b ≤ 133) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6thinwide).t+8) .two6thinwide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6thinwideTop8
