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

namespace Pr657PaidOne3Top1

private abbrev P:=PaidBatch .one3 1
private def batch0:List P:=paidGroup ["9H]]1 16T:n c]^N- &!04#3 &10lVx &11}nl 1k$-]C 9M1'p", ".H)wb &%`{t# &,M|Pl )u|,[S )9#ngO &!Fw:S &(%3{` )5%2ZS", "&!3x<K %~$<zO %?v#3G %>:<C7 %~e&5) %}k=$d (UT{SW '9^qPK", "#~HmH+ #?oB2C `^0xW #|jv#S h@i[ <8Q` _c|oG }soW"] (by decide +kernel) ++ paidGroup ["&c@c &c@g %:h!G' _yQ_3 _MIRC <8Fc QkAS &c5c", "&k)2 %w7Cl/ %w7LEG %:;vvx <8;_ &k)6 <7w? <8%K", "<8;c &k): #zv[;x QkA_ &k)>"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 136 3 51 = true :=
  checkedWindows tiles 136 3 [8, 8, 8, 8, 8, 8, 3]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 1) (hb : a.b ≤ 136) (hj : a.j ≤ 53) :
    Covered ((Final50PriceCaps.start .one3).t+1) .one3 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne3Top1

namespace Pr657PaidOne3Top2

private abbrev P:=PaidBatch .one3 2
private def batch0:List P:=paidGroup ["#T0l-) &&pRa' &11^8d &11~(+ 0N,P&| 9M1'p &*YYTl &ewi<x", "&'ma}x &',M~K &%!_w? #JYJw? %}Tx'3 %})x;K #}NSmK #@=JI/", "#bQEG #6I.K }t(S $]J2F' #@Ru/K _yQu7 }sdC &c@V", "%x]g+' `sc;' `2'{3 <8FR <8FV QkLR QkLV <8%?"] (by decide +kernel) ++ paidGroup ["h@RR %wLf%t %wLn]/ QkAR &k)2 Qj}3 <7w; h@GN", "&k)6 h@GR &k): }sMN &k)>"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 136 6 48 = true :=
  checkedWindows tiles 136 6 [8, 8, 8, 8, 8, 8]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 2) (hb : a.b ≤ 136) (hj : a.j ≤ 53) :
    Covered ((Final50PriceCaps.start .one3).t+2) .one3 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne3Top2

namespace Pr657PaidOne3Top3

private abbrev P:=PaidBatch .one3 3
private def batch0:List P:=paidGroup ["%H~kw? &11^-S &11}y| &12P9' /o1+}' 7-d5G &&25Ep &$>$8+","$(a]~` &)JLoG %}kM83 %})x;K %|[#8' #}e)s; #@R}N| `scs/","`2(U; h@i? <8QC $]`eV| #@Ru/? 80Viy@|;PX5+t$ }sd7 QkL;","8Bh9/]dV:1%}'i 7k3lT@KP4<3cw( 8TxfByKr#fsq8P #x'*+ #K{p/ }sX3","7|b/!!XF4H{IP$ 8h,5V84/j>deI8","`^0)| 7E|!Q+0sad.pv} 812NKaf<3vjP_q 8z<bjSyJRsZGrm","7VkH6:_wt2EXAa 8B`nvBs24&T78m 9/M1}paf<KK<&T 6|~JI%?U1{jHia","7hYnxJ0|)^]@jD 8T11C%#(3SC>G] 9A^_4/I$&$<07< 700-Fn/>S2~~vi","7yI7]Y`#<,t)5( 8f_Pmd/{3a.$~X 9So.GK1>lY-$H$ 6TD/sS/brUzwGe","7@>mDX|'v'26M} 8-8^Aj1'NX-n]i 8x/q:E<q30z,0H 9g!ZZgvYU1zuXi","6dt?.&9dBYYkT} 7PMOBDkn:;Fl[( 8>('&y`+b'DV(L 9,^3e'Ig3=dogD","9y3*o&^u>gkijP 6+43K}rJ};=&u@ 6tFNEUCep^9_c8 7a]2@0ZV]/W$3<","8NtLi,1/tR[>P0 9>.S1fV]2kRvv4 :.CW%BF3(?[ecX #>I(6l"] ++ paidGroup ["6:)&!B6;UTs$vH 7&v^^(Mg@avRpP 7qkr=yJ?~ClY@D 8`csM;`4)~s&xq","9O[s[GdR2x=]O0 :@T'8_.MnuLXt@ #{/),x #>3Qw`","<7Tx <7a' 5]VYhka{e9X{W4 6HzuTdW,.2OCOD 76HmuWWhneUF}i","8$zT;e:)C7|nuX 8qR<2K18<M,lCT 9b-6))qH2H,d^}",":ReSKzsiWM=M(( 5koBZ-91AS^5u] 6Woh+(xydL(APL 7Ex}0*bj>i5;.$","85,79P)oeL4G%a 9%AbtZ`<NyCSl8 9sZURh~>2TtJ7y :ev#`9['A&.A8m"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 136 9 45 = true :=
  checkedWindows tiles 136 9 [8, 8, 8, 8, 8, 5]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 3) (hb : a.b ≤ 136) (hj : a.j ≤ 53) :
    Covered ((Final50PriceCaps.start .one3).t+3) .one3 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne3Top3

namespace Pr657PaidOne3Top4

private abbrev P:=PaidBatch .one3 4
private def batch0:List P:=paidGroup ["&10l@[ &11}WS &11~IS .R9f[d 97Zsl &',Ei[ &$=y.C &!4-'7","(XoI0; &^4{_# #}ze;l #@=Jk' %|/w~' #~tmJ+ #@iJV; #bQE/","#6I.3 <8Q7 `scPx _yR## 8vMfon[`p$@sJ$ 9,&;3o%ZaV}^ua","8Q0!kc8;!J]S}$ 9>ZmToKURjX(kL","8d$T*~6Hbb/fQ< 9Q3AvorPD@7q9, h@G' <80+ 8*~W2{:S=(poD]","8uv)G<4VDweg>D 9dht:p;K6Rp;.u 8<3?K_jJkIe8q0","9*jZdW2e(17xp] 9w@H[pbF()O&YT #}8}v' 7`+OY~wZv+^7Lu","8ME'eC<B;.^#uT 9<_0#s0rhGh-Du :,uz}q+@w<*MO@ `^/{p","#bPj| 7p[^q6wp0AI&?4 8_Vl~'l9iOQJD( 9NRb@1/#J_:>w0",":?MOAqQ;hnm(5m }sB# Qk+' 75Vm_5Ha&]h^.e","8$/m*Kx'GW4r1P 8piT9i>194J5HL 9aG6]L-1-ujPKH :R&$cqx6Z$GO+X","7EJWt)si$1y`7L 84`{@ax;_m}a#m 9${<RLn(gU>[t} 9s;hyh+>n/<b}a",":eZV'rA1KW':V8 7U>C+{@q!C)@h@ 8E4,VvxOw&iNs, 960$l1?}7:7FyD",":(0=9&)LPEltQy :x3+Hrh,=j_bL$ 6vf2.[rCX*)7z] 7f2.@okx|u:Bq("] ++ paidGroup ["8Ue:n.xe1<T=eH 9GAj'rote[+nGu ::$oUA'Z3]?)'4 ;-h]js1'/@>Lwa","%wcCc# %wcL<; _yQ1` 7(zjC:fs8~,xWX","7v%vUd9#{)G$Cy 8g8I'CxyHR@,Ve 9XSQ@VAl5@$XL< :KvCr]%hsso:XL",";@@2.sV~~RvtmL %wM!bS 6HXM59*m(4Op+m 782DWvZDvu0[5T","8(vakWd+xZX&La 8wiW=Xy0`i+xI$ 9jf9Y:qccav!xm :^jv1x#vV-AL-e",";RudOs}yp)Uh#L %:;v`` 6W3+JjB<D7yCdP 7GF|mTNtVl4>pP","88jL#L13vled}T 9+<fSnyDw~tg;@ 9{w~r|CZ3Enj}4 :p_JN6!'9Cq^_}",";fM8qtFtb<11v8 <7Il <7Tx 5w-QbAl7_$&z[T","6fjfa=Yiax@Sg@ 7V[W%3CF7c8!ML 8H^78@[;t@vg)< 9;mtk&yY27`U-]",":0,g.`sQagc4Ke ;%R|kP}4yZCp48 ;y%k5tmoRomzCu 6(+EysF8V:AjOi","6uDCvnr8}{j(B$ 7fq29o7uuY;c+H 8XQ!M5)CrR&GY0 9LA&$;ynIMKC|y",":A>NGDEI1KZ|P, ;7GQ*l{B[qt$fP <.Z?Vu6jE%HD9a"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 136 12 42 = true :=
  checkedWindows tiles 136 12 [8, 8, 8, 8, 8, 2]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 4) (hb : a.b ≤ 136) (hj : a.j ≤ 53) :
    Covered ((Final50PriceCaps.start .one3).t+4) .one3 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne3Top4
