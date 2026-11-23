import ProximityPrize.SubmissionLower.Compact54Packed

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

set_option linter.defProp false

namespace Pr657PaidOne3Top13
open Compact54Packed (paidGroup checkedWindows)
open K1_13 (Shape)
open K1_13_8 (Valid)
open Final50PriceTableBase (Covered)
open Compact50Cover (PaidBatch tilesOf checks)

private abbrev P:=PaidBatch .one3 13
private def batch0:List P:=paidGroup ["*[8hW| 7-d5G &!IVS+ %@D,$p g4J*h #A7S2+ b&I`` `sc}d","<8Pp $!XJr| cb0P7 bh'g` }snl QkVp &c?s &c?w","&c?{ <8Ew >N(RP:&VlO{[Ti &c@& #6Hil Qk@l <sNi)Lc=yU+6u}",">N(RP:&VlO{[Tm","&c@* $F/Kl #bQ#l <sNi)Lc=yU+6v$ >N(RP:&VlO{[Tq @.M5uJ.!OD_oI4","<sNi)Lc=yU+6v( >N(RP:&VlO{[Tu","@.M5uJ.!OD_oI8 ;?dw]&)3vu,~&a <sNi)Lc=yU+6v, >N(RP:&VlO{[Ty","@.M5uJ.!OD_oI< ;NUxK>X#5X]7Yq <sNi)Lc=yU+6v0 >N(RP:&VlO{[T}","@.M5uJ.!OD_oI@ ;eb.33B?e=6y9e <sNi)Lc=yU+6v4 >N(RP:&VlO{[U$","@.M5uJ.!OD_oID ;.M&:EGq1Nl3-H ;{m@x(,]6~n]vX <sNi)Lc=yU+6v8",">N(RP:&VlO{[U( @.M5uJ.!OD_oIH ;CoJkm}kV]Zbb} <4xS_ysyfcHAUL","=%^fIB2Gq>m6*q >N(RP:&VlO{[U, @.M5uJ.!OD_oIL ;Y3p?8Ue|.NTpH","<K&gFn^98G#&5@ =<RgDa.*Kw6MFu >N(RP:&VlO{[U0 @.M5uJ.!OD_oIP","#x&pl :|U[Jx;)z#XX]a ;oU7pa.`D<>'G} <b1z.cGUgK_+J("] ++ paidGroup ["=SGh@!)j(1XD.( >N(RP:&VlO{[U4 @.M5uJ.!OD_oIT ;415hv__8Z]v-y","<'w]D+dYjJ-U}T <x=/sW1s908m)y =k<i;@%KaH{:r8 >]vMVB>B&X>>t@","@.M5uJ.!OD_oIX ;Him(u&6T5b5[4 <=<$uS<T2Wz(U, =1HBZKy2hqpPfm",">%1j6^~.<a@1XH >uT<f-KFiFKGbm @@9E6!<l?XX$+D Qjql","&bYo ;^DFEsIkpmfR,L <R^IH{rNWfiW-a =GSUB@cO:UJ5Ea ><&k1|ymuxc(?X","?03+tuXKN4XPP< @[F'%F}i+ka;@L &bYs",";r|}cqnC/GjoYe <i!nzFJH}7]J;, =^_i*5Llj:$w%T >Rxl-=uOPS,?[]","?Gnx&`fP4!fY>i @wReqlaet}iRUT &bYw <*WW#p4xK!o/*}","<~D6Mo#CEEKypa =tj{o*7,;{[ZbH >jmm([q2,kN6Bm ?`Lg5JsTv0x&c,","A5`Fa4Dba2qjk] <7`s <?31@nXOfzwm1, =6f[!9X=kS;KH8",">-v1U{~Hk#:`w0 ?$bn#zlqf%q-)} ?x+UD6#YZ|(/PX APm(OY(_LDz%#e","#>u(O' _yQ1` }r}l <7`w","<Skh^l}(%T|,_D =L+#Rb183b*z}m >D$D=phf<drDV$ ?;Vn|;hSA=6#n0","@2gEMbc[vuRxH< Alyg>~i[8W%<8m <7`{ <iFA{kC]A0#I/]","=bLH',g2XowLUD >Z/W%eR%lHL)5u ?RKowYd5zTWwT@ @LEGD>k[>KqqH0","B+)H.FLX$j-[68 Qjfw <}~y;ih4]h'f]u =wnmWT?,~}f|-y"] ++ paidGroup [">q:jjY<B>-&jri ?j@prx_uU0!1qD @g$I:xsZd#2jH$ B[NHxfZ;>]y`/@ Qjf{","=5YRXh.iyB,&.0 >035+|u'FNYo;D ?*E}QN&_mn^NQ]","@$5qn9ZW1GD(WT A#`K1T{Z+VPcGu B[NHxgJO./B~Oe Qjg! =J5,vfRA7z0B[H",">ETY]GL~l]I@py ?@Q39Bm|>s<SgD @;*riWV9j_f|>e","A=>M(2&YPjk:ou BXPFATBFH(NccD"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 136 39 15 = true :=
  checkedWindows tiles 136 39 [8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 13) (hb : a.b ≤ 136) (hj : a.j ≤ 53) :
    Covered ((Final50PriceCaps.start .one3).t+13) .one3 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidOne3Top13
