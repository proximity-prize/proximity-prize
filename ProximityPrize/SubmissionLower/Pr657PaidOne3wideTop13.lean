import ProximityPrize.SubmissionLower.Compact54Packed

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

set_option linter.defProp false

namespace Pr657PaidOne3wideTop13
open Compact54Packed (paidGroup checkedWindows)
open K1_13 (Shape)
open K1_13_8 (Valid)
open Final50PriceTableBase (Covered)
open Compact50Cover (PaidBatch tilesOf checks)

private abbrev P:=PaidBatch .one3wide 13
private def batch0:List P:=paidGroup ["*[#L[| 5{($S %~OMS7 $a_*S' #D;dwC `201p #?oAm3 `GZDC","#x/=x <@8| #CAI~h #Accm3 b&I3? <@-x &k(! &k(&","<@.! #L&bt hH9t <@.& <@.* #x')K #6H^K Qs4&","<?tx Qs4* Qs4. ;?dw]&)3vu-(km Qs42 ;?dw]&)3vu-(kq Qs46 Qr{#",";?dw]&)3vu-(ku <sNi)Lc=yU+>^@ <@.B }{5# ;?dw]&)3vu-(ky","<sNi)Lc=yU+>^D <@.F ;?dw]&)3vu-(k}","<sNi)Lc=yU+>^H >N(RP:&VlO{d=8 &k(R :JDqb*b${%@h0( ;?dw]&)3vu-(l$","<sNi)Lc=yU+>^L >N(RP:&VlO{d=< &k(V","$0Y$[ #K{X[ #6P;' :`g95R9|C309e] ;NUxK>X#5X]?B4 <sNi)Lc=yU+>^P",">N(RP:&VlO{d=@ @.M5uJ.!OD_w1a",":v+^fzovi@|i=4 ;eb.33B?e=7$!( <sNi)Lc=yU+>^T >N(RP:&VlO{d=D","@.M5uJ.!OD_w1e <?_+ ;.M&:EGq1Nl:ri ;{m@x(,]6~ne^y"] ++ paidGroup ["<sNi)Lc=yU+>^X >N(RP:&VlO{d=H @.M5uJ.!OD_w1i aW@LW $[b;d",";CoJkm}kV]ZjJ@ <4xS_ysyfcHI=m =%^fIB2Gq>m=p4",">N(RP:&VlO{d=L @.M5uJ.!OD_w1m :g{%-ytQ_(P#>u ;Y3p?8Ue|.N]Wi","<K&gFn^98G#-za =<RgDa.*Kw6U/8 >N(RP:&VlO{d=P @.M5uJ.!OD_w1q",":|U[Jx;)z#XaE$ ;oU7pa.`D<>/0@ <b1z.cGUgK_32H =SGh@!)j(1XKsH",">N(RP:&VlO{d=T @.M5uJ.!OD_w1u <?S/ ;415hv__8Z]}s<","<'w]D+dYjJ-^eu <x=/sW1s908to< =k<i;@%KaH{BYX >]vMVB>B&X>F[a","@.M5uJ.!OD_w1y }z|3 ;Him(u&6T5b=CT <=<$uS<T2Wz0=L","=1HBZKy2hqpXN0 >%1j6^~.<a@9@i >uT<f-KFiFKOJ0 @@9E6!<l?XX+pe &jB2",";^DFEsIkpmfYqm <R^IH{rNWfi_s$ =GSUB@cO:UJ=.$","><&k1|ymuxc0'y ?03+tuXKN4XX8] @[F'%F}i+kaC(m &jB6 ;r|}cqnC/GjwB(","<i!nzFJH}7]R#L =^_i*5Llj:$~ju >Rxl-=uOPS,GC}","?Gnx&`fP4!fb', @wReqlaet}iZ=u #?-cHC Qjfh &jB: <*WW#p4xK!o6p@","<~D6Mo#CEEL$X$ =tj{o*7,;{[cIi",">jmm([q2,kN>+0 ?`Lg5JsTv0x.JL A5`Fa4Dba2qrR} &jB> <?31@nXOfzwtvL","=6f[!9X=kS;S0X >-v1U{~Hk#:h_P ?$bn#zlqf%q4o@"] ++ paidGroup ["?x+UD6#YZ|(78y APm(OY(_LDz,i( <?H: <Skh^l}(%T|4Fe =L+#Rb183b+%f0",">D$D=phf<drL>D ?;Vn|;hSA=6+UP @2gEMbc[vuS#0]","Alyg>~i[8W%C~0 QrN7 <?H> <iFA{kC]A0#Pt} =bLH',g2XowT=e",">Z/W%eR%lHL0{8 ?RKowYd5zTX!<a @LEGD>k[>Kqy0P","B+)H.FLX$j-[68 QrYF =wnmWT?,~}g&s< >q:jjY<B>-&rZ, ?j@prx_uU0!9Xe","@g$I:xsZd#2r0D B[NHxfZ;>]y`/@ _!@I[","&b8g QrYJ >035+|u'FNYw#e ?*E}QN&_mn^V9} @$5qn9ZW1GD0?u","A#`K1T{Z+VPk08 B[NHxgJO./B~Oe"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 39 15 = true :=
  checkedWindows tiles 135 39 [8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 13) (hb : a.b ≤ 135) (hj : a.j ≤ 53) :
    Covered ((Final50PriceCaps.start .one3wide).t+13) .one3wide a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne3wideTop13
