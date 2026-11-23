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

namespace Pr657PaidTwo6thinwideTop1

private abbrev P:=PaidBatch .two6thinwide 1
private def batch0:List P:=paidGroup ["$eCv!9 $e1EWf $m@s[5 &13gK~ &149i) &14YWM &.r@'j &,hP}f","#Q^_Ib $^F6I% &%NlXz &#DlWz #A9L_5 #@)g*E ``!_Y #8Bq1","#!mk9 #~JUaI #A#w,) j2O^ j:C- %}+avY #dBsM #8:[Q","j2DU (]&: >2,6 %?b%cf >2,: (Sy_ Se26 $#>obz","#B_]yU >*!Z Se2: _O;#5 _$2^9 (S61 (SA= #!e4I",">*!_ Se2> >)tV j:8: >)tZ j:8> S[zV j:8B","S[zZ j:8F j1jA >)RE j2#V j:8J _{C$1 S[M5",">)<= (S+> j2#Z j:8N #!e)V j:8R `uK_b `3v*1"] ++ paidGroup ["#!e)Z j:8V #8:/V j:8Z #!d{V #!m>V S[B= #!d{Z","#!m>Z #8:$V #!m>_ #8:$Z #!m>c S[,1 S[,= S[7=","#Mm*V #!m>g #Mm*Z #!m>k _em{b j1jn >)Rr S[p!","#!m>o $[&p-b _enK9 (Sd6 j:-r >1sv Se3& #{r_CM","_evl= >*O~ #{]4RM %w9G?5 %w9P$Y"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 133 3 48 = true :=
  checkedWindows tiles 133 3 [8, 8, 8, 8, 8, 8]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 1) (hb : a.b ≤ 133) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6thinwide).t+1) .two6thinwide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6thinwideTop1

namespace Pr657PaidTwo6thinwideTop2

private abbrev P:=PaidBatch .two6thinwide 2
private def batch0:List P:=paidGroup ["$pF^^I &13N}^ &141jI &14QXr &.F/d% &+n89v $lK%D= #}fxeI","#@ToA- a.*vA `ILXM #y~R% &!a9.b S]IM Se<z $]x,O)","#@k<'I (]&& >*!= (SnA (SnB >*-I >1}v >2,!","_enJ1 j29= >2,& `uT!% _{CP- (SyJ Se2! %}A/+~","(SyN Se2& >*!J Se2* %?wW^M >)i9 S](F Se2.","S](J Se22 j1u1 >)^5 j2.F Se26 $[}p<5 $Zn,CI","$ZB#~U $Z,Mm^ #BI*]E j2.J Se2: #!e4F Se2> j2#F","j:8: `IK:z #dB;- #!dp- S[X1 #!e)B j:8> ao];Q"] ++ paidGroup ["`ICGQ #!e)F j:8B #!e)J j:8F #8:/F j:8J #8:/J","j:8N #Mm5F j:8R #Mm5J j:8V S[7) #Mm5N j:8Z","#yu+- #!dN) #Mm*F #!m>V #Mm*J #!m>Z #dB0F #!m>_","#dB0J #!m>c #dB0N #!m>g #yu6J #!m>k #?/LGv _{BvM","S[BQ >)<Y (S+^ #!d{o #!m>o _en4~ j2$- >)j1","(Sd6 #!m>s _O;PQ #!mJ) Se3- >2-2 %wNr%) %wNz[A","$ZWhCA _evwM $Z,hAA"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 133 6 45 = true :=
  checkedWindows tiles 133 6 [8, 8, 8, 8, 8, 5]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 2) (hb : a.b ≤ 133) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6thinwide).t+2) .two6thinwide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6thinwideTop2

namespace Pr657PaidTwo6thinwideTop3

private abbrev P:=PaidBatch .two6thinwide 3
private def batch0:List P:=paidGroup ["&13/iz &14!&M &14IZ5 &.[b^j &+WboY &)MshU #|+4ij #{FV5v","_9f2f _9fH~ #?Z_49 #}|M`1 #?E+1Y #>JwIf #>5D8n _$2]f","(SKr #Mn1= #!ewA #!mjn `IL,% _enl1 >2+j (]%o","(]%s $^F,sM S]31 >*-9 (T'> >2+o (T'B >2+s","#A9D39 >*-> >2+w j2.) >)t- S]3: >2+{ >*!:","Se1w #yub~ #MmK% j2#% S](6 Se1{ %}VY(- a.)yn","$G}y~ S](: Se2! j2.6 Se2& j2.: Se2* %|s.pf","#!e46 Se2. #!e4: Se22 $`Oq5f $!/+ib #!e4> Se26"] ++ paidGroup ["#8::: Se2: #8::> Se2> #8:/6 j:8: #8:/: j:8>","#@)]v9 #89jz S[Az #8:/> j:8B $s}|U #![ZA #!dBv","#dB$z #Mm5: j:8F #Mm5> j:8J #dB;: j:8N #dB;>","j:8R #dB;B j:8V #yuA> j:8Z #dB0> #!m>V #dB0B","#!m>Z #yu6> #!m>_ `_v,M #d9xY #yu6B #!m>c >(l~","#yu6F #!m>g #yu6J #!m>k _{BkA (Rr: >)1M #8:$g","#!m>o %;!E{U #{r^QQ _O:un j1u{ #!m>s #{FU[~ _enK=","j2:I j:-v j:9! _eva5 j:OA SeII %w#rDM %:(>SY"] ++ paidGroup ["(]'J"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 133 9 42 = true :=
  checkedWindows tiles 133 9 [8, 8, 8, 8, 8, 2]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 3) (hb : a.b ≤ 133) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6thinwide).t+3) .two6thinwide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6thinwideTop3

namespace Pr657PaidTwo6thinwideTop4

private abbrev P:=PaidBatch .two6thinwide 4
private def batch0:List P:=paidGroup ["&13_XM &149]z &/l8Yf &,QkAn &)y{^) $.*,{% #A{+)b #?/U6U","#>Jw`b #>5DNj _$2sb (Sbn a.*u~ _{D6- #Mv/b S]I-",">*C5 $!Dg<~ #A9DI1 >2+Z j2D% >*-) (T'. >2+_","(T'2 >2+c #dBgv #8:Oz j28~ >*-. >2+g >*-2",">2+k S]3. >2+o S]32 >2+s j29. >2+w j292",">2+{ $2Jhr #Mm?r #!e(v j2.* Se1w j2.. Se1{","$_lEPM #Bu3!5 #!e4* Se2! %}A.}r #!e4. Se2& #!e42","Se2* $^K$I $G}cr #dB:r #8::. Se2. %?b%AA $#jo{5"] ++ paidGroup ["#8::2 Se22 #Mm@. Se26 #Mm@2 Se2: #Mm@6 Se2>","a-~e= #81l9 #!dBn #Mm5. j:8: #Mm52 j:8> #Mm56","j:8B #dB;2 j:8F #dB;6 j:8J #dB;: j:8N #yuA6","j:8R >(wr #yuA: j:8V #yuA> j:8Z #yu66 #!m>V","#d9xQ j)>M #yu6: #!m>Z >(lv #yu6> #!m>_ #yu6B","#!m>c $2J<> #!m>g #?ZT2= #d9bI #d9mU >(av $2J<B","#!m>k _O:H9 #dB0V #!m>o _O:=1 _O:SI _O:jb j1jr","j1u{ #!m>s _en@1 j2/= (Sd: #!m>w %:S>?A _evIz"] ++ paidGroup ["j:9) j:D5 ([y5 ([y9 (]'> $ZB52A (]'B _9nTM"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 133 12 39 = true :=
  checkedWindows tiles 133 12 [8, 8, 8, 8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 4) (hb : a.b ≤ 133) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6thinwide).t+4) .two6thinwide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6thinwideTop4
