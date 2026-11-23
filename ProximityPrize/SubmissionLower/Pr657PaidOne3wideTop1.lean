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

namespace Pr657PaidOne3wideTop1

private abbrev P:=PaidBatch .one3wide 1
private def batch0:List P:=paidGroup ["9H]]1 0&nAY c1U,% &![D-[ &10|'[ &12(V/ 1jk@6; 9M8m3", "&)3NPp &/Rfg+ %HSK_A )u|KXt )9$(|O &$iNI? &!4#$h %A>;Kd", "%?4L9K %=@+Ot %AQXKb %}U#0t %}*+-O #@R}O# #?oJ%[ $0bf|", "#}e1Dh #@=J(' `Gc8l #bY8| %x]DWt `skDh <@:' }{Kt"] (by decide +kernel) ++ paidGroup ["hHE| &k)* %wM3:C <@/' &k). &k)2 #>3Z/O <@/.", "Qs5*"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 3 51 = true :=
  checkedWindows tiles 135 3 [8, 8, 8, 8, 8, 8, 3]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 1) (hb : a.b ≤ 135) (hj : a.j ≤ 53) :
    Covered ((Final50PriceCaps.start .one3wide).t+1) .one3wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne3wideTop1

namespace Pr657PaidOne3wideTop2

private abbrev P:=PaidBatch .one3wide 2
private def batch0:List P:=paidGroup ["#U@Yk^ %I7Hpd &10|2h &12(b? &129$# 0N,h<# 9M8m3 &%d4i'", "(Xo|6p &(|Sz' $_T2QK $]vCnl %~9=1l %}Tx'/ %|qLoh %?In[t", "#@'|}? `skfS $^Yv3t #}e1DW #6P~l b&I3x aWHmK #L&yd", "}{bh `2/yW &k(o &k(s <@.p &k(w &k({ #6PQd"] (by decide +kernel) ++ paidGroup ["hH:h <@#l <@.w <@.{ Qs4w #{Z9dh _MQ/W Qs4{", "hH:w _7{eC hH:{ _!Hj[ }{@w"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 6 48 = true :=
  checkedWindows tiles 135 6 [8, 8, 8, 8, 8, 8]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 2) (hb : a.b ≤ 135) (hj : a.j ≤ 53) :
    Covered ((Final50PriceCaps.start .one3wide).t+2) .one3wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne3wideTop2

namespace Pr657PaidOne3wideTop3

private abbrev P:=PaidBatch .one3wide 3
private def batch0:List P:=paidGroup ["%I7Hpd &10|2h &12(b? &129$# /nxf;d 8iZ9' &%!V4x &!uh-l","$'gS~l &(|Sz' %}Tx'/ #B1l=K #@iRTW #@'}+3 %|qLoh `20=G","%?In[t $!Bu?h #BGA-O #6PsS hH[W `Gc-C #L&yO `scEp","`Gc!C <@9` <@.[ 7{F<f%6}h#D?J] 80Viy@|;PX53[D hH:S <@#W &jo[","7XcL*_>Z4lDdOX 8Bh9/]dV:1&'m, 7k3lT@KP4<3k_H 8TxfByKr#fsx}q","a,85h `GYut 7|b/!!XF4H{Q8D 8h,5V84/j>dm1X","#L&WS hH/S 7E|!Q+0sad.x_@ 812NKaf<3vjXG4 8z<bjSyJRsZOZ0 <?u[","7VkH6:_wt2Ea*$ 8B`nvBs24&T>~0","9/M1}paf<KKCku #L&LO 7hYnxJ0|)^]HQe 8T11C%#(3SCF/}","9A^_4/I$&$<7|] 700-Fn/>S3!)_, 7yI7]Y`#<,t0zH 8f_Pmd/{3a.,fy","9So.GK1>lY-,0D 6TD/sS/brU{!0( 7@>mDX|'v'2>6@ 8-8^Aj1'NX-vE,","8x/q:E<q30z3ui 9g!ZZgvYU1z}A, 6dt?.&9dBYYs=@ 7PMOBDkn:;FtCH"] ++ paidGroup ["8>('&y`+b'D^mm 9,^3e'Ig3=dwNe 9y3*o&^u>gkqQq _MPvC","6tFNEUCep^9gJX 7a]2@0ZV]/W+x] 8NtLi,1/tR[F8P 9>.S1fV]2kR~^T",":.CW%BF3(?[ecX 6:)&!B6;UTs,^i 7&v^^(Mg@avZWq 7qkr=yJ?~Clb(e","8`csM;`4)~s.a4 9O[s[GdR2x=e7P :@T'8_.MnuLXt@ 6HzuTdW,.2OK7e","76HmuWWhneUNf, 8$zT;e:)C7|v]y 8qR<2K18<M,t+u 9b-6))qH2H,lF@",":ReSKzsiWM=M(("]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 9 45 = true :=
  checkedWindows tiles 135 9 [8, 8, 8, 8, 8, 5]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 3) (hb : a.b ≤ 135) (hj : a.j ≤ 53) :
    Covered ((Final50PriceCaps.start .one3wide).t+3) .one3wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne3wideTop3

namespace Pr657PaidOne3wideTop4

private abbrev P:=PaidBatch .one3wide 4
private def batch0:List P:=paidGroup ["&10{n? &.,t9l &12)1t .R:0AK 8'|bx &%8$<; &!`,p' %~:$'G","&#-xKS &]{^KG #}9)eO #@'}A3 $]`ma' #@iRIK %|[!hO _d'm7","`skD+ _yYs3 QsJG hHPG 8+3XFl|uKQoUMP #6P]? hHEC 8=i-hmEp=(N@y0","$^pK#O #~HlV; 8P@`,mlk/;)hny 7xRFrn=nyd+',X 8cv4Mn5e}nfS<X","#@=IcS `sc:d `2/c3","8-Fy2,;|[zZ8^q 8vMfon[`p$@{2D #6PQC <@#K 8?;MNG:-?4-J3,","9,&;3o%ZaV}f^$ 8Q0!kc8;!J][eD 9>ZmToKURjX0Rm","Qs)K 7vlow9h[mCx/(X 8d$T*~6Hbb/n9] 9Q3AvorPD@7x~L 8*~W2{:S=(pw,}","8uv)G<4VDweo&e 9dht:p;K6RpBt8 8<3?K_jJkIe@XP","9*jZdW2e(18#W} 9w@H[pbF()O.Au #L&LC }{5G 7`+OY~wZv+^?58","8ME'eC<B;.^+]u 9<_0#s0rhGh5-8 :,uz}q+@w<*U7a","<?jK 7p[^q6wp0AI.'T 8_Vl~'l9iOQR,H 9NRb@1/#J_:F_P :?MOAqQ;hnm/{0","8$/m*Kx'GW4yvq 8piT9i>194J=0m 9aG6]L-1-ujX3i"] ++ paidGroup [":R&$cqx6Z$GVpy #K{Mt #L&AC 7EJWt)si$1yg|m 84`{@ax;_m}hi0","9${<RLn(gU>d]@ 9s;hyh+>n/<jf$ :eZV'rA1KW'B>X","<?_K 7U>C+{@q!C)HOa 8E4,VvxOw&iVZL 960$l1?}7:7Nae :(0=9&)LPEl|:<",":x3+Hrh,=j_j4D _yQ1[ _MI%l","7f2.@okx|u:JXH 8Ue:n.xe1<TELi 9GAj'rote[+v08 ::$oUA'Z3]?0lT",";-h]js1'/@>T`$ %wLv9? 7(zjC:fs8~-#?y 7v%vUd9#{)G,,<","8g8I'CxyHR@4?( 9XSQ@VAl5@$a4] :KvCr]%hssoB@m ;@@2.sV~~Rv|Tm <?SK","782DWvZDvu0czu 8(vakWd+xZX.5$ 8wiW=Xy0`i,#1D","9jf9Y:qccav*a0 :^jv1x#vV-ASs( ;RudOs}yp)Uh#L #{/0}C <7Ih","7GF|mTNtVl4FWq 88jL#L13vleleu 9+<fSnyDw~to#a","9{w~r|CZ3EnreT :p_JN6!'9CqfG@ ;fM8qtFtb<11v8 &jBN 7V[W%3CF7c8*5m","8H^78@[;t@vnn] 9;mtk&yY27`]r} :0,g.`sQagc<4(",";%R|kP}4yZCwyX ;y%k5tmoRomzCu"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 12 42 = true :=
  checkedWindows tiles 135 12 [8, 8, 8, 8, 8, 2]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 4) (hb : a.b ≤ 135) (hj : a.j ≤ 53) :
    Covered ((Final50PriceCaps.start .one3wide).t+4) .one3wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne3wideTop4
