/-
Nine-factor witness construction adapted from public Proximity Prize peer
submission 657, commit e07f14a81dfe2cf1bda985e67040ad4d31fe81ab.
-/
import ProximityPrize.SubmissionLower.Final50RankReceiptFast
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 20000000

namespace Final50RankReceipt
open K1_13_1_1 (bandCount)
open Final50RankReceipt renaming witnessFinal50Fast → w



private def r30_0 : List (Chunk 30) := [
  w 30 56 0 340026 340903 92 9102 [],
  w 30 55 0 350025 350902 97 9348 ["vnfP{$/q<4SkR'*Vk-vO7#Xm${4GC6NH3P'RTVFlE6Ex0Ag0WcMgS@3>[4l;;D$R","**.V-W!6(p{#^-3zLfOd0=2fKZ*;9aw*taSKV46]#qrx32/iy3#uTErAC?Z<CbIT","#6o^W313*i9wduhd[&{C"],
  w 30 54 0 360024 360899 100 9451 ["j#iRW?X,HC^!t+r:Q.U'L*WM.pD(On0Q0Ona-j-E%;=:Vm+EU@Fds+<TxIwVehZ:","AVz$/]Jytv;k%br9sN5&c,LIL^RobbY;9#DzSX5YAYz0LZ;NR>7N*btBXT2r(y9;","*k)Z_nf}EU{`1Q1G)57bX=l<JZ~gLT(zpbcmjQD3%gPrS&/1V_>?(4FYv*13_@mV"],
  w 30 54 100 360900 360902 3 269 ["1'%IG"]]

private def r30_1 : List (Chunk 30) := [
  w 30 53 0 370023 370838 100 9296 ["n9>B9s(>#WUK&q)Ln%+f%2&&pWd1,h$agM*R-y7Sna}L]iT)T5%a<]ky*>g!9i'>","zRA.tR:+gv:/2:1kBJO^Z+w#BoQB,>@?sf>kW-T%.oM-!`(qV(%_%vL|CTV%ypMU","flr)$^ib-TX1HAW}>CBbfLYKrt{H#M;GF-Q.$'@I7A8RU1atdptPeQ0R'mmh?r~k","XIzK)R_qr/e.6%8~ioQ&)-gCdUJz2lem$z%OTI#Bz~32_Pbs8s/"],
  w 30 53 100 370839 370901 7 621 ["7sIt-|FKvQe-xi"],
  w 30 52 0 380022 380832 100 9183 ["n5DW;xLv/QgM@.=nqB4RkCF!!4,b|4-q~V/~J4N.7Ak2$)J|}`RigyA:'=bJ48S.","=w]n[yu}IG|@H$SC)Q`>94f0`et@G3Ko9ZQjudT8e6c@4MjxBYcn;@2#zQ,CwC*]",".m|IMpL69+GwQwoZ{6530hcl5KI%sU-dfKnC3>{?+TB{7B>K`K-$%e5{hw-Yb6j]","c,O`tm;Om+n#};NI?k<tWV8`(WC5/Z9Dd@|Oxw?ifZxxS4PKL{v>VPF)7ZK4WIQ}",".0FWd~]zD5g/|`BFP{"],
  w 30 52 100 380833 380901 12 1037 ["qX[9^adRRRRX=UM}9Wrudhy^a2_Ol%X"]]

private def r30_2 : List (Chunk 30) := [
  w 30 51 0 390021 390772 100 9073 ["54$TSaM7'%7p{<tk@m:.9V<'vNXt%,gTw{IC@U[xKP>4^$+G)L3+dhKIH359:5AV","z}fugbBYNA]]*|?u2$tt,sGj~o;CLwnUy{:nyzU=;V+||8aMS4(&F-v^2,^DJ(/g","jKUnuen]1RQDw-cRdq)ImmSr(3l<2e+v/zK09C5e]jg<E9(@S2(bXRAqqE{`Z;vR","B(m>iE?sz{3#Y~9RY+$$z9O-oGMaU#Ew3.RZ<N[8bS*8-}S=BMGlhPtsYO'k>d*N","QC10a0'/%;@lI=%z_85NdCLL4b]cY>'Iy8:T%*[XH"],
  w 30 51 100 390773 390900 15 1263 ["/'+7?#O5:=h7[TKB{G[a{cUyL^<1v3/XYNnKMF`RJV8g_V"],
  w 30 50 0 400020 400712 100 8973 ["f-6Bd7ci8PPr9o2nw:KuJ:5TTj-Q|>HXv&=A'5^^yVFH-PSP$A$&:UUAbi2]wZq!","5iW_bt0]Ceeuitz#yDAXdiru={-]LE'}F--&2FkGR7M7')CSp)$|InM){dg9EhKK",":hfr1p0'}%T;.#Y&f,&85@&gF><@Su|bwG:.@r0~][#(jM|)UX.e!Oa+x{nTwmq~","-ejMB/JMqx2Lgu;DOIJ2ZR^W&a<LJSrTp1[Os.bq'=y6u<#t4xsDkkN.0~K(m~]m","wj6,$Jp_R--.n!^4K9=R[ls@k#z>n;h1pjj(Nvi=(Q&slP:yG`Gp<JMmB"],
  w 30 50 100 400768 400900 19 1570 ["#-got;kD~$g{]&kJfA6xm]X>&Tlue$JV_T~b]Q%#5wYS/kv#{cYc,PO!QFai$"]]

private def r30_3 : List (Chunk 30) := [
  w 30 49 0 410019 410708 100 8873 ["cBem=p<^-?Yu`e2/X%o[}pYAfl#au/-$i&cj6T:,'g$Zx+K7`{o$tfx7~G|zRUc{","`Apt;cs`i$9J.=a'(w77RV-f'Pu?Vl}v|6Qge@UDYIY4JwpGhPAPL1/rvdy&?5_5","iW8A.qZ6@0;fJdFqoYMP:gd)0XIz*y5{Y[n}nld1.qCl#)Nh?Y)$kpPQ3dV)G6rI","KRd+%.^1.0Lr_d0<kyyjQP4{iPT*_%*;@bDl7vTBC2kw0hW*Bn1G09(Gx$Y=P|OW","9o8`+RF9y#Bh8)j;:jw,f}otEyTV(@;I[1m/JQ}0,(v$*VoS5U:iW>.z_d/M!."],
  w 30 49 100 410709 410899 21 1692 ["abuvi7}d7&dE!-,1iEUWU-2O=xOE)dsEu?rvS54.$B1S]q4MW+bSJTVlq6K4n#~8","Qo&|1Bt1H"],
  w 30 48 0 420018 420649 100 8770 ["x'QO.z{WE#GPct{)Fg8r=o+y~Gk`x+*j}5lps=^<:G~zZ.{m6gdI/6j;p6ob(|Dc","iSq<v'kg2^r6~txIO,?y^mqiZ{J#!0`^jnA-C+P'x8ts!Y-pFy$9E5+(sLw3rq,%","hf'j3?CWMfzT)'r9Jzp,(g$1TkJ#eNYI[ael4|Ch$s1$L>5nDNYuf$zil3.4Zt}h","J&5?=(ZS$d_Wa%D4t#9SV0hkv(Jx]>so(Fu/F@3CV]PSaZ6dZQ'[OY$CA}29$5UU","$UxGIZ{b$RSKBq_H#IjEe'$a5C[ctr8PCB/Doi1p=,wAoq_X{lL=!GeQdW%"],
  w 30 48 100 420704 420899 24 1908 ["ee+U)'8k0o`Ac)wWp`x0j%&^%Z_Imc*vj;YLk$SgAiT9<V%NWU.q@^8M;IW6v*4w","#8)CTxfnN/<:wld,M.B49=1-+TLzW`"]]

private def r30_4 : List (Chunk 30) := [
  w 30 47 0 430017 430645 100 8670 ["5/0q3-L5:Z,^(^Nbayeg3WWCx;<!vSSkXgEniG~o:F)@b<6N`knY)BXIUU2nS:l.","$Zp8yL|kbGE&6FyABggj?gtbJ;_2%NRaF[b2j?:F,^Sp(`{aYKG@lQjWN;paeV'X","zfW[9$xv4pFU6a|%h=x7~Ux2`_'8|r=AX!2S|RW]J*LtdoXZntwjG}n/YP]:=*S'","b.fANk0w;:K4bo,D<:JHdB2S|w%5Eu[34K2Ot%$+%@.-`G`P7IrQ9):9QgCiX_Mu","UYSzn>q7U}kvnvzsG0T|$W%Z>3MNhJOyN_eKG7iG+a-b<H<lUIH~"],
  w 30 47 100 430646 430898 25 1939 ["R3D-1tBV,j)0]0eXKzF5oo?a-n*=Q|q(NL1{b~-bhUZ3eP|mY:yUa7Qpc2[Y4e{g","74%JxA5&u1`aumBd)0[O>qC/L'K^2uTnPUM~o="],
  w 30 46 0 440016 440641 100 8577 ["lu-qg+{=J$~8C'Jesvdt9RUzXh4{iyu.LYN67bn|^uj{;]DPMFh2w01AF{?c<>F{","]T8DW>%/g_B.:bzrsz{Bsn>wZXY-uuj/%I7*Y,C{bto4n-1;w)tp?RtkuaD%Pyhu","UyH:)u7]qEvi`GIGqeC'=2C(GIb>Sc2~dr*{.pwb^t-@G_#~.ZCN!!r(kTpu%^<:","BoqMBk4)H'>$ejOyOjAwpu;4cc5gHD([*>^auB#2r@;9|Qsk|e?V((3W%ycOVHpy","8&Dd7GTttO4=Pt9z_cm]P*L)tHqtIt6CYX08<o=%e^UK8=!gKRZ;j'.p"],
  w 30 46 100 440642 440898 27 2052 ["/5LPrZu:dgF1,U0h$;t`Mc^:dLW*,j?;PnTka0#Fj::ND#1pdD(U!@V[=p}FJJ[1","#U)^d~)4fw%$j~y}bMQ8)hR!xE3_ri*]}Y_/nP4R:&HV8-YjO-X"]]

private def r30_5 : List (Chunk 30) := [
  w 30 45 0 450015 450584 100 8454 ["Jqi#}jY}rVd4LswBl-GWSWemA83FE@b)jo`1lRP}E}eg4WnDk3jCXO:]HdifuE]!","4yTRzUa*%yJG2_*9:d:7pACZ_z0M9*J'RG+R]w{09oV'XbuUZ::[f&Fzta@(Gp+=","/F2MzRa:?T8!J%}Rj(rV58Kv3#mnG[,&1W`5m>QF2n^gDnwhH+C=ndgC}3(=(^Dz","B@eT8[#~Xwwb@mRMGfFN|61Gbj{,4~@_(^S'.?gRxL*~}|FS%$s]RpI1cmtv^Q-}","TbP`>fv<[[]6R9'}}P]^##SL_9]}rC/$zcQvDPx-2MZtrv"],
  w 30 45 100 450585 450897 27 2019 ["6F(]<lCny.ZilW$CMpcu|I|Z=FRoA6&lrIK#FSK+N*+Re}A2L&^)Tl)k)U;ILJ*E","-I=))4~C~pEX0CSLmu@2cfr_q+jztl`5<yOycBfd~>1J7(NS('!#yn4"],
  w 30 44 0 460014 460580 100 8365 ["krvB[P@15DFjFv[Z3jK7HZjxOC$^5o4b2Qw8RO,:,5bUuMQn@Ck,@ZEg5!s-`*3N","pm*ab:T#ELeVdF|b2T:__xMd.GJ_jIaJ:u:<!dnC>g0bnKJ1-r95}PlPqJEn^:w,","$UE.Qv{50|P@fN'wx5XdDjiWWjPe,$gK82lgsHdCf.]E1Lw&J%qtOhT1wqtTw}rd","wb7N2tN[^-ha5yh-91;>n]Z#o|bDYp#rW&&KzQLGx**`K]iKd+lv`,}cR.V[k{n7",".0yDquD5A3}<m{UkR,o%=~F&_IiD9dqXLKDSQqi(vdvVr`c];3"],
  w 30 44 100 460581 460897 28 2041 ["[YazIQI]pv$,LIm;r{l`Evk/n0|!;gH4vT]7W-l6?b~I_`<{VyI)/W#Ey/{#=:xZ","3]tt,xzw~l4^j6=M7*r1|iY>-N^Nmy37vdVYt|g27C{UJ/)~%n$Ihy;4I>{Eg="]]

private def r30_6 : List (Chunk 30) := [
  w 30 43 0 470013 470578 100 8246 ["b_V?;zgHD6TZcJ5HJ-!13:_]F1-OH!eTce=%j$wk$9qOx1-/5Jn`mp3szV@J.+`.","e1B21v|X4iU+.{hCu9I0cm$k3=mVTZ3u?w51'~N$0R4Fy!$xZ$4ZHq>GE1QR`/kE",">/z>>.?g$*LL&D>0;;J`;_CdS1Z]kVJwcfu1cYZCZ/~-vU$U^wYW7_LQO@5t@R?5","x7][YU6ePnSH-%W$:dX7^/.vuf6q0#7L{9TinTp;Ma-?3GBMa{:Z7_29+Sxl]W<v","$5S@hW^#:GR=P.!8{Tu)aK44Jg%:;*.7yoK@PwxP{mE*xP;1"],
  w 30 43 100 470579 470896 27 1924 ["fiUG4^5lk_{(eoz[^_4>&rmMZ|ORoayQ?yM%P{]y]z;jVBPeK615[imMc|<ul(%{","]$@@i._Ts!VEkDy9n$M3;3<u?egcM_utNQ0UNd5Ov*=V$B#UtsWz@@/>loKnC:"],
  w 30 42 0 480012 480521 100 8122 ["o}}TOsD~dkhD_3:=!5Bxgk^w?!vuBV%/t%yUoqR}79|1wjI(UUwn$OOgcbQ=bwI&","<GLbrT3HMHS8+JR#y'XFS!gswdao.''{YvDE[wxB/FK^Sz4(Fdy'=RCSUWx<j%?7","D};&0P9FtYs.#kBw#lz.zdljS3*(ehz?ab$|O%V2R+`K-PVK:2'kL`*VO~95c'iO","=>-Vjmc,.bp/i27G]@7Earu;!EeyiN(WMNgcN4/*DS#*_LIB?w3CnP/:0L^4M~`U","Tj3QtwIvrUUj:@7gNFNcRHN7.Vc3CP>foe|3yQ_<;FJP4}"],
  w 30 42 100 480576 480896 27 1899 ["cNRus1F;N#hbk;'Cy.EF*[{OfF^&zNck8VY{~*hKOY%wPCJ_fwJ=O0J}lh^f&M]&","JV?e;|;CNf'CXh7gJGV,g0*x?fgWGR)Z6zP~=6p!$&?O+[7#3e!GZYKDEIxRz$NR","&`+@"]]

private def r30_7 : List (Chunk 30) := [
  w 30 41 0 490011 490519 100 7995 ["Y40Kt5Hx1Khw|:60H2:-oD[OLjAL^%a6rzu2wd=yx6Ck.3x(hKphM].bJ*z613!Z","QJKAqk6uZo<,rq}M3<W*t!*M'n.dmJJEBf}JMld=yIC{r3W%Qe6nKMyi23nECoDN","WPFhKWnriZ2%dDR}7*66E7Devz$]5pO`cJ{r%>Uqpf5E+~sZ%kYk~z!-Uu$k+9V9","IIBz8wQ<]hxgepgbm[nyksO))EHY1&#7C>.Jo_cZ5dO%.~Qx3v0d[E8}k]p#t=0p","$OH8CTKCl*QA'kM/y~eXGXT2QmA:!s4$vol6URm|`JIhsFioT"],
  w 30 41 100 490520 490833 25 1716 ["|hDPLFKN=E~jfv,6akO;n5]b_p-GmC?2o#&C.k?j%cBoCA:16v}3a+=33l?%l]uN","De-w58q!NHF@H!BNxV)V6KY8B~%l(WUt?+(,Lk+Rm:dReMP(Q]@4ZH.;3}V^"],
  w 30 40 0 500010 500517 100 7881 ["[P6FBsB:8[<]{KV'(Dxb6ssSQULp0}:;jz5}y|48>NGfb>~|0|B);L-<8;]`vc>Z","(*S&v!HbRFR~WBz`aw8l9?~gbrmY8WYsiOeJvD~OXDi:O>Er&P>4d}74G]|e>3^I","{*J`h$}bbG;?$2W:%byM:uwq5?cY!CRm!~$53S0i)^Y0c`PfJ_1=-U6P5)Z;~G%6","r#ME5hziFD%y-vsmqna8~sl'?XaW@nL_UA-j~1pthNq!J0FQTK^81L&+vvt(/KH$","lne+JY3b3/?ObWbtt5P*(H#|B@[Ri2thF`iqL6O09!V01fhRx#$"],
  w 30 40 100 500518 500832 24 1606 ["!8G`pogt^Uq<S=u{^Y&])~Yx1A,Tm?b#AQPF.h*!_LM_etXCN$6W1pP[BJUjQyN6","?<P@(sF9{K0!Z((B:3z-{I~?}K>RaD&pxCquln&d[eO)_;Zn[bCp$2me88sJSe"]]

private def r30_8 : List (Chunk 30) := [
  w 30 39 0 510009 510516 100 7737 ["(pf6zeEOA#M,cl10)-}AA6dH~M>|JSkcgKxv*RP$N>|&/o:+r@v}D8H%+?<0x6.Z","50[&2&I220jJ9EEMtn{6,Ox4/,[Lk1Qx:aw0iGYalp|VxX'/=Wuq*De/bh>m0#AP",";D(}5P/{%q}f{Z^Go8Z^->B,JJ:#Q;c(5/1h^X(KTkET)n.enc0MGxVFX)87)KFM","tM6!f_RTQx!Ja$zF6{<B:-Yduc:<{!%ghTn~W`[P-+OGl0u!/P#7[{)66&ch|7aj","#/s`EB!pZ(Mvv+k*~[VWcKc&q;IX]=CrVf:km0qwCI-xW60`t9[lQUs9@>_"],
  w 30 39 100 510517 510832 22 1439 ["}}!w%VsY4>(JwiC,r3Ocw8Xsh>@utu.cC|y;n.>=4DtJK<OIV|*<}_jB+4FE6}+I","%w{9qBdf{H?5~dk2|-@p^;${0E@u}r<b#8N%-Cpwq_snN<,+"],
  w 30 38 0 520008 520515 100 7602 ["%Y=79+k*bb+-)obf-&*W'-VkuPH)9R{}1{SaU<fs_Y^0XMed9E/w4Y+<vMtLCJ>Z","C8G,2%w)Fpy>X1?`@ZO(+!KBCDHcNyr_o?/,8]Z]K0;@(,)_.!nm2A[v3S$P8sy{","n$N~q%9X!2*]O:4B!>AdYKR]gSoTs2|3KtF<^ag@8G90oe{B3/)Pq}XvR{*qcw}C","2*ax_vfUrsU<0u6x+%1#i9n_!PN|x;`qAQ_QD55}|U$@i*-XQD_m&1zLk@%F6?{k","*pe)7P'n//i3QT[V@/Y=W}5xKHn*x2e<JmMStrtj,E(SyQ}en]o?;V{9E?TP8"],
  w 30 38 100 520516 520769 20 1279 ["UN8;^FC$yU8}`_4rtH02LuC%L@sDt<1bUl>D['0G3{!=9]YKz?HCc{w[o]t,Af1S","6yW04'M)VG<w2g]lgGbkh)?ozT51&r@`(l@dsR${`/Y%"]]

private def r30_9 : List (Chunk 30) := [
  w 30 37 0 530007 530515 100 7437 ["~5A_FOsP5~LqW1Wchbn$#cjEWkEbt]=[qA_T<eHrF[`P7cf{O*:0B,9VWT$43cg{","|#Gt*y^/>b.5@dQSYjaxD1bm4=;bO1OZYtkIa;g?4GQ.3>Ewpb[STx2tp;v|n!$>","[x.ZnBzs%zO+hsv|+hS/!'wfX/';.xot3.-an@ZiYARxkJg+S0WNj{DCqagsv_ui","h=7;Sv|uE:n'S0}0BLS?eK<Vb%f*Ry`,_dsbdfd0,dsXb>?JeW?N$2p;XgqQ8b-m","${BL1HU;.P]>|1e-`zo`Y`9LjPNzB{i{Z@D:XVYfC:-N=T0U[|Cv!iWj?Hb{#*kX","t?2~D)B%X!"],
  w 30 37 100 530516 530768 17 1066 ["sT[Q$hc/a1Sbtu<ws@6A|+2,q)~E>cFI_.Hf_>4>??&@3-aH(m1j9<Q0FIR)UHRG","(]C@)&4>H>Kkhg=V(K!O(iXN0_"],
  w 30 36 0 540006 540515 100 7283 ["@%w|BX!@,6{0rS(Ty%6Te}yZ#CMxdDvY<t8f`(h'{yD?tnPyqKoci~9j{KQV1<4R","7zGyXh'4sT`dZI5G7HpAhF!<mcDtc._p))W,L$6*q}tmDVhGY.sbD#0Hal]/Yv?w","#/4w.lFe0W-y]]g|-QbGUF7|`_[Wm0d5~O>Ck`s1[b8K]LD`{cZ=5H-=Qk-,g$Mp","y=R?Za6cngGP*4oit|8Cm~~y:srPLH3PsLYNai:l>wQ?xAnSKyPGoN7=gr_FBg~T","wzs6e(zCbodGziJNU3ZtqlJ}&jj@u{$(C12ec1}Q=V4]EdIK/2@h'>4WPuw<-#C8","V~3!AWb|AiSpM'^"],
  w 30 36 100 540516 540768 15 923 ["V3:j-|4.dT}jg)tv:u{Yoma@/P<W''qG5r(ENYx.U*k<?*ulR@9vdiWhy'1vu?_G","_dQj{F?0e[4("]]

private def r30_10 : List (Chunk 30) := [
  w 30 35 0 550005 550516 100 7099 ["n,^GG]Sh.?{9JyA24X1T,R4tY#0LAdsN~hLu?];aN7pY::?ynjrnr&r'=/SX2a.{","{sQ:aE-xJO8Kk$>:QzLq8^vJx)Nj+P|%EqYx(|9ACe`!}PI^g,)~1?E3I~WAk.m,","W_r|,`j#~(lmea+tL%2u%H</GJ9&IWB%eI'!)5x3yC6jD6*g`n4#IzA,fME|K;=F","4>l[>9<+Pv,LARF_!5yaFaZ&L_!tpT`LA8!Ts)cns@KC^Ru$n0=Id[o`9thU0`.^","J@$ke~udvQ3:U3L/M?W~%5$]^qC9%V74mkCb{!9yG`qh~FDY'it}~K)m4HD}4nR6","#7p.?g]WGLylCM9cinG/bzs?/?'Y>YLe2"],
  w 30 35 100 550517 550705 11 666 [":;/?-K>NpKd]@.|#^7aUc{0ZAr#A@NK7IU4[fnk>=Y&6'2E;DQIBX`<~"],
  w 30 34 0 560004 560517 100 6928 [",#ycvam@ec({&8.x!#nLQHku@(FGH~:m0ex80[d0R(+>kID5jf_-/D'jW^V]Nw-w","%5GI8clTlw4v)(bN;!P&4hrbN<=o$~2TX'4C8N*;*x9ge,q2O?&$!v2;#|%2=uVY","^b?N1CGy&{+6aK-=HsRe&=H;P19KCj~F>Vfc'ud~K^u5HGxH2.El-Y+Qw@cHm$P,","3HaW|EGdq`;yR6lsr$Tjhd~+t}loE<TT|>k5$4PZ9^Xjx-sL#yPX,},fA;f0HfL1","mi[@R[p5Hh<jX2s$NpFulfYiuPxP<?LuTLJT.L8NI%%_owuP]H)D00-eq90HDI^/",")xB*2z|73LrXTv9F:,[*S;$V4woDYRLEo2#a|pW"],
  w 30 34 100 560576 560704 8 477 ["I.1&MSlkF,an`O4zuec3x>=F;}{i@YAO7Q~A/,eaxp_4."]]

private def r30_11 : List (Chunk 30) := [
  w 30 33 0 570003 570578 100 6728 ["~ftv;MR:1D@NP,@R*;p<~TK90IXc%O6*2^j2Kp5aEB[CJA~Fo1Xr-;L?)ZNz(#T!","^u^SU|@z>nX*Igtw0]$*JcR|8'C-z*_l)K!oVO4!rrX~}FlcD1[3f)c^bd{Erhx}","Fy<I[R#RP&czh/@M!^b|<'A:u%jD~%zjA~|/aM]f`hUFSpvXM%p,ZO[hc^]uE6#i",",Q[wRum_Ke'76,fefvxO-.3yTQ,{q5lFMY!:7)-'_FmpS>JZ+zH[.b?az$cC-(R)","0W8thIY,,<}H`BaMvm]a/[|._g|rnf7B?w,Mw-V8+LVF}yImjS8BrBS50QuvlU]?","-<d50'oUz@?0`$ymlTQVk,jD0b8<+9TJ#%<?jU6NzQ.t(EOh[$w"],
  w 30 33 100 570579 570704 4 236 ["*t5|Gu`gC!X+zJ[IZ{[)"],
  w 30 32 0 580002 580641 100 6546 ["SM_nS>8hG>HV@2&*@1A^>EK:@Ewxu:%0:T7gc7~Qz/>}MKUZ=!&nNtdq!do)G4<s","?F5^qHMgPy1OB6{>g9!JH5ge}XL(%x,o3>3rb>?`cg:t$$r^#tcV}jRN1)(sN^[4","?.mBAK[)u?Ew6|pgv=+J'B6o0sMOe+zK%])NDM8NiNiwnet[!k)7_g<Vp,$cK}Wg","iT=CEjx%>[+2wSZBKB){r$ya;JlVONW>KF~[yLm8`Z'+o~bH0}Z0y9rjo{Ga1=ty","mf8T%Q)L'p>2O:)lXJ2:>Ym<Lg>~H^#%:a@2UayEun&NWUZg`<h`{'7lZgO=/O=5","o,}sosB_hSPOa6TUj'l?/`c,Lk1P<%zch5aD/PN04S;nd`/ikrobieKWoZ[d.[7u","%JZ/"],
  w 30 31 0 590001 590640 95 6049 ["'9r5@X_?Y|nOj6CW/Lpk7mngCq{&ejaJvJk|YLL!>Qu{&)m+z=&kR<B;c](5`Bs*","zdMHA,HcO+0)Y;q7A,}[BD6!p+@*p]/wiBvrs0O+$r7p9%:UduUMZaPv+x@p5P_]","`tT.rm-Nwq^Bbsq|OncZGTo4ZRy%b{MIV^8AsBtlL@oc=4$+&V3~UgW!~Z]fBHor","taJ@%Q$7kXv+o(R&a`<+;a<G??I:M#TdEk1p;?+Wo_'?Na:f.nKD<O~$BwzSY9<c","5?VB4#M1$|+8>6+hz}&749rgbXQ>s+>u>Jl[cn%vy*'+g9Em}z6UP%b*sI9'wXC4","0La~wphu>Xp}J-u5FnFzA<lcv4vzxOhYv51(X(;#Qx9y*mQQI:l(i4n*0D~Yys"]]

private def r30_12 : List (Chunk 30) := [
  w 30 30 0 600000 600640 91 5630 ["[^Gaflxo714i<]#VA-a:hqu!mTRn>fS-QzlB=[mRsfe8LRwwp-,[V2hlq%]o+Hfw","JE2&yHHPa2-LzJg+`'~9@;:+sX:%O|@pl}6BH^zLFV~//6bNp=m4y%7a0xE5=^0#","[(@iJ3Vg?*Pjy)}1!E.1Z4QzZ#BbNXf;DI-W3,^7$rC]{*UadDj<[da)g;iP=rxA","fvnte=qhIr3JUF;)hNL[RYJ<p[@vX@.M@WS5o}#OD1=gtazCW<y${PvTVJaPBGv2","R%Ww/bQjAn6f8k'h(Ai@F%mcSw-t?A#6!F%.jmNi))H3*Kch6xqKOh9!`f`ZpBSN","'`|=6Gja8=,1ZB(}O@(%m7z4H?KM54qMR_-;8Ep>jSH_NEc$"],
  w 30 29 0 610000 610577 85 5083 ["{V|.aK('Gn&>${%vSibPVkle(R=%Cv74T|+/>5*^C%yXVxil&B%d'+v.b+uC=bG7","$b4M5?v:Hf*K%ygK>d[1v6tuD^]-!a!oluum|Uas#pP1cVHcF|=Wpl71fbH`<'-I","AGJ#)jh~5z}=&<V2y{AvpR7yqs[d<p<kQ&pZM{+,Gpj`A3#.?;+:e{u$eeZoy1-_","?nG^~I_]2~9QgT8iRa$A79o/KV%2Jg*x=R-#5{zz6T9z>Xkr6n<,%B3[dw]%o&cF","2a0Mz<(pon.g:34;t|+cJ'0@C+-pFZi7byCy(1Xjkz3]BoJ)E;^mL5X6}=WrH-!-","wJWVXv=;K8G{5Rt`m=)*AfqWc*KR$pOs_CU7cRGEX@"],
  w 30 28 0 620000 620576 80 4612 ["k1!V3+hE|w1c24>O-#p}1[jL,~*:>=B4HN9;>wu<#1=]$RQSv<D>,N=qXigtQ,A/","K]&Vjnk=Y.$G|RSbNQ|hk?1AFb{=O)#D='BSR:as]e@|5^s2VR,%U2ak<S?YW^/!","@j%Ad.psDRZ+-OhT*$:Rg81O5b]Vbu9fi]pmO!LK<r=p<6[M:{pvkFn^/gqveF9e","'OwrYm)f]u&|4OsHtIAz7V1@Y~c=HX0}iJ[ZGVZ~(h@y1GD,xU5kFJjALrvmX>+}","''[KaO_Mt,R'x#kwe/Qz9w98F[Qo]B5`!V>u;#u;?h`H*7</InC4lkk:H7cc>wd_",",fb>A_96<C6R(uoAxAq={q@uiU<!w]JOu7a|7N"],
  w 30 27 0 630000 630576 75 4169 [",iArToPjG)g(u6v|%@,Xchp1.<<$'R[uR6&mE{(awJMnZLUJU`)P,Y8[J!QlZcal","P^oz0f1}czuJr*tVO-0t`dF`xada;0)4/5qOzdCVVfp/6C!!wA@qwb@fzedw[xpM","ky'wE_VUpeGyL=*rn<`NX.C),}9|-4z#5PJ$:OmMnjRb}GC2jbBCcAz19wWfs%a?","zgafwZBl6bk=hS9RM.Lcs/R:d7n>pu=}=3?^K@ams}cCuSOpF@Z)+!VwEQaW5#FW","NC|Z_TfBX'ih$'!uO?USAv/PS!{9XqOLP}}ocE^oTL1{)}U6g]AMevE<<t'-Uc.6",".ZMGXV.J:!eM<lyd"]]

private def r30_13 : List (Chunk 30) := [
  w 30 26 0 640000 640513 70 3749 ["D&{DfC2`tO;#t]o;Uikt8}}TRHK=l`UeO*t~m8N3b^t;|It:l%gN8SN>:=1G=[0[","8.Qyao.C;!CTMk!I#X$C@c@3%hI,/1DT>FL~Fop!_G%mfH/qjc1(o;MvpIB0NDf)","y{Xy}lfkQ@1$#nyNzy|7[imid98bS-I_>uI|PeC`>un|.4`c*@pD+B9v_C`!ruZ(","I$Zo-;ht=]=[5cR13xlB'O}N[p2BJ{kl3%*lV1|c1Pq[#B{4wN0$E$|b>+`RFIJd","?KTnx?=zn^$Us.6jh?E#2Q_vk8!DQnZ+*@eV7-REQZISbi}]vmA66K*@Fsye31R_","#&1&51YZ6u`GnQ"],
  w 30 25 0 650000 650512 65 3354 ["VWVVd@{6y:<jo=v6+1w[A3/'iUi.CpP=OoDsm|Eqa0&UM1zU3_^MS3m!JWJHm}X+","vw,U|{W^41F?'eVXA[Vu$X|&N.}jt80KhrO{**Lu^XZPRO.*Acj)/NFq.d4OP#pl","iJo_<mbEsd&XS%')&WdDEMm1Yv.g;A>H<O(&ieX(9=iEpF+`sr8}Y5#oG47%8o3o","P;r2agh/,c}#8.567&fPm4WOwxE<)|^OD,~BnT>Oz(y/;/(HP)z@L<SCJJhf2X%b","lYj}yZbKrj,-:46un~B(K>EuUZhoz7ls@6P/tf3Xuq)gJ{=Y`WP*y$Y=-)alx_M'","4i>T"],
  w 30 24 0 660000 660512 61 3023 ["b4)=B3aNZ:DlH~1-/#.)U,hK{r.w-9s7J&mQE^/0wQ#0io!hrsT'Qp0&+OZr}CB#","S2@GQj`E-K%:Qj@!Z~TLbEIP`YCIhoPmUEE_mJt})4MjB<qG=|b+5/Sn3I1?sQ1$","^-4qkk6lD7Fb3[zb>CJfpH2%IH*'p$WiuYn2Lin}^5W)E|p69L)M~~_RKmF{:@$#","3{=ozgqQhCMvGDO:M]>)/Xe].a9+*uL{_z&I>R(;CJp:.D,eX5G_~ep!ugK9LsLp","qK&LKjL=SZK9NESFFS^,2Jn)gC598R!|l[5A^:vRlwomC"],
  w 30 23 0 670000 670449 56 2672 ["WWbbOUlK2IR}C|QhXFIX9*U<_ZyB@.U-oi;D'7CsVk6&#:ui^^g{=1)6B,pm1X'G","`2I#nO^?3Bx;:Av>PGYB-a%J2PO#ppK%?2h{}yAT>c`nI0qk/[)FY[x6)J.#|!ry","~.M%ksua8O2g6sL'l#|%mpIm]P#=L9z0{Bv^_pa;IEj~d}z[MC#4j~'~NY]fD]al","B:xWaic0oX-pGN_oi|AkvV~Uf=@imZ,0^:#8YQ=81:~mqS?Wabg+SiVM725{JpF|","$uJxr)9z+Q=eStI:9f_npd#PzA'w_:UrIUoeA"]]

private def r30_14 : List (Chunk 30) := [
  w 30 22 0 680000 680448 52 2381 [";L%05*x/w')``<</Cn7jmC~S.^')rhlub,`4vUHtK!HZ1?'y>z>4X@NRn+^`uW+'","[5;4l@7HA%yKxICO-mw-u-{PE_{CI~mO((7-qZA0ZK5i,&'d1}AdP2U]_Y~_-'Y3","@&#KJSf?TLF9NWL03.luaeECA(tcQ'HoeZZx{szs0-ZiQ~p/AApxkOL!U&~la`8!","bJc=,-$j3g+4udT1{)*eW%G/'5;0<4|&cNWfd+Ux-ktl~lU0mRck4XYskXQWBwiP","(yBE&v7(Z8rIb+#^m@QB@$p"],
  w 30 21 0 690000 690448 48 2110 ["{WrK;4fagrX!#wwV2o5)Yq)F1~~=K3I]Zf_v|sknJ>R3A~`a'L==qd?.U7ThP.(K","OMd,&Vr!#d!mb1w^!YZ%<AW)Uo@[b|8eg$Y:5(hmVotIh'#Zx-=Mi(G}4~&c_b[,","mmAO1wdv+zj:MCv_mYN0Jn~EaQyG75=E%J[g]a]]~h_2@zo+!xVqxNk:pUc!xtxZ","DSyw-k|cH=NdY*pxyk,u~$Lu'ts9/P'Txw@vCia=6US;.y5_KUUcGd=0hU${swFX"],
  w 30 20 0 700000 700385 44 1855 ["Og*2nfa<s^#<zBbhsR2'q+~^^Cnn*PQaJWx(t<I!3P((G~uY/9aH&d4#@jbhYXlW","j_Cr`]gZeNgegJ*%Q=:DeS|9yfORch-y5J8rV3JBE;cJvWG6&K3)c%:f?5Dq/j,v","OE5JPK0k*ou#I<AQX7*+I2bRDgj4/Bn14JKL[:L@=LpEL+jU9^Hgfa`l:)CDXiVw","%)6!TPO^!t@(pyBcGX>alV>v:^Mz;}Tl+9,F,,n%t8Z&mYyrWM4JVMq"],
  w 30 19 0 710000 710384 40 1618 ["Z&|EVM_Z[gkq.p3])wKQhE_OZWe1vC]w3zZY#Fz|5/@8CVCftVFxWa:3U{|b$skS","*w$B)I@`1N2EL[JhlMu*g9,T>NFi!pK#8B{qv`AK{8]Ix6B<NKZqb>:llV^/A~eb","-Y4>}.j{-}LCaUx61g.G,tOX!Q~{n1oiR{(WN`2<N>F&mNK;z7Ebeb>*v.#K?SFG","z^GqH1LA~=zQDT](Z>dFB=ZvZ{wd>9|_uxQ(ZF"]]

private def r30_15 : List (Chunk 30) := [
  w 30 18 0 720000 720384 37 1432 ["yEz2~v@LHD+wAEHMSo)Num}Q7|)ziR5AFm_FTdR9ZK%c$.w</i<AUfPtq.'ln-TK","de!NvH!nru-BMj6r>f*}|9T$&OM;,[O2~]LXNGR}?b>=!gm1.fJQc]T,A1}?i6tq","L+ZV|1y|Y5WBAfL&t'9,tKw`Xnp:A}h9qBRWq}L9>oxXI`JW;tHT%~(;LuSG,iUV","#@F$aoi&urFfbYl~i;"],
  w 30 17 0 730000 730321 33 1225 ["5*EoEN]oiPG-WO1!+ZWC/SOZ>%GoYfcB{Ue<N1A%~-1kC}AymN#xLp/GRyi]a@O'","=}Ha{ZfXOK3DL!jLUBuKk:W'M&,zcDqg#iJOrxtd0@o-G;em{$?igPB`UY?f=JZu","2C/$hO}YNm{+<9[?sk9=m#JYl`exP!eHJ^O,-yXbUr9%[HAsq4b9BY.sY~g`Eg!S","#5je=O"],
  w 30 16 0 740000 740320 30 1065 ["g=ghD7Z0V-K@C'K24G0=j1I?~1}%*]2pMYt>]#X94YFCH>E`+-#lEu*]Rur%yLZu","5*[]yJ@$2Nr.Qn3%yA?F.uA.`ZbH/>@L/:MQKQiNq)TPD7,L[)gmQq,9'KY'RfVC","%!j6M4aMWDSFQIto)dzcKv'9u|bETg9f#TbdYU+OgVS$a3hqm18]eK"],
  w 30 15 0 750000 750320 27 918 ["62%^D]k/ix(`uK>f({>7eX}yut8ECG`eihXFDx/Nq<U<E?4;vXG7Uy7UQEpA:c7!","XJ{.:IVxtgb>4Ar*Ay6!I(#beN5fjX{v557xrBBaiTc%&?tB%bque41_.4,S=6&j","/<>x|$+^JllQHP#sR*{>.;Ra?z6&1u(3E5"]]

private def r30_16 : List (Chunk 30) := [
  w 30 14 0 760000 760257 24 780 ["oC*n]@e(Atq-/SDF~/=,!'iD)NGo}Bk/Wl~njuy<{&EE#jQ{zcs^oG:xhp#]=s4v","X+WTn(8.j(oS1`S#v3#YNJ.oen0v,sX7su^y_Oae[l$NUD)l*`8A(uSl8e|7kD1s","%{^q<kwMWpc:T)'j!cw"],
  w 30 13 0 770000 770256 21 653 ["VR:V|dY_9jcA&PQ(M4NLKR&3n6:K]SeM/89{in*1[<O&pizBl1Ab:Mt}~~i2c)TF","y=<u:uMg56)0<ML4rC)i5h8_||0ra$jE&u^}UFF_g~g'j[HxjTN8twd,^,o6JTdI","o!(lZ"],
  w 30 12 0 780000 780256 19 564 ["qmDm(*R;GZ9%~&ev[%g0m8q:PYl[8RqdcgXO7^;/gp=HW2|$P<fut0{YPi{|x.dQ","-g3Qw1R#j^n[,&+2DnwLpt47'qXs1IsV%8Qw&PvbY8H9fNBjg"],
  w 30 11 0 790000 790193 16 454 ["8VQo;)kb-cK!n[T(qDJ33<-S#G8T{kI#y{A`}`e[`-pntPuZ+K$H<>vBSWp71OdB",":6`qRmToW}7k[=BDg|/5yigYl`@yyHC:7Z:_"]]

private def r30_17 : List (Chunk 30) := [
  w 30 10 0 800000 800192 14 379 ["{}x:j^uiIdg~em;(^w2i~r&x0X<%kX$9:&GO,?f5umILyZElLOiZYy%~H)tIqr,'","JFShR7W}:L%|E@f%+K#iqo8"],
  w 30 9 0 810000 810192 12 311 ["Js]5,/tr0&5mY/J/@KugN_~;=KS!^x2NaD85x+99?s2>St?ASh),xZ//G^JGV},v","&OnuC7TH"],
  w 30 8 0 820000 820129 10 247 ["f,o(h!3`X^t7<%E8#mhA&6cA(doPw6'[%D;bh&-aouZ{&?F0<8=_}U:bw^t"],
  w 30 7 0 830000 830128 8 189 ["+Hh4`+#^lyp'DCng|X6`va~'`=4^~_7-7NQ@L0bF/|hz-~*++"]]

private def r30_18 : List (Chunk 30) := [
  w 30 6 0 840000 840128 7 158 ["'~(Lg3,?O@tw]m3p34-BDPeTmT?Cv;26!ngmm*&"],
  w 30 5 0 850000 850065 5 107 ["(rggJUT)iGy|Tzf7X7{%e9LVN./Fh"],
  w 30 4 0 860000 860064 4 81 ["^dgMa.w&4y~-Q<f'>ONdK"],
  w 30 3 0 870000 870064 3 58 ["<szgp]=#AkM7e8kg"]]

private def r30_19 : List (Chunk 30) := [
  w 30 2 0 880000 880001 2 36 ["5*[g2$ROz"],
  w 30 1 0 890000 890000 1 17 ["Hty}."],
  w 30 0 0 900000 900000 1 16 ["EF.T"]]
private def chunks30:List (Chunk 30):=r30_0 ++ r30_1 ++ r30_2 ++ r30_3 ++ r30_4 ++ r30_5 ++ r30_6 ++ r30_7 ++ r30_8 ++ r30_9 ++ r30_10 ++ r30_11 ++ r30_12 ++ r30_13 ++ r30_14 ++ r30_15 ++ r30_16 ++ r30_17 ++ r30_18 ++ r30_19
def rows30:=rowsFrom chunks30

theorem good30 : ∀ r ∈ rows30,good 30 r=true:=rowsFrom_good chunks30

theorem sorted30 : rows30.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks30 0 (by decide +kernel)).1

theorem mass30 (i : Fin 57) :
    bandCount 30 (i.val:ℤ) 56 14≤(rows30.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks30).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 30 (j:ℤ) 56 14≤mass j chunks30))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total30 : (rows30.map (price 30)).sum = 290376 :=
  (total_eq chunks30).trans (by decide +kernel)



private def r31_0 : List (Chunk 31) := [
  w 31 56 0 370025 370898 100 9866 [],
  w 31 56 100 370899 370903 5 470 [],
  w 31 55 0 380024 380837 100 9615 ["JjtK]yBX4]]>aM78)O4M4<U_Th3ge'kaPW}F4xv@-Xd!28ur|VK_}a2mt2fVECu!","tB9b(>^(>VGH{abXs&,FTa?0X`Fq')yEqn:,WuxQD[~R#aG$h7wKj/3aq|I'.hwV","#xmzS[1Oqx%+XrIr*yca=kw^y"],
  w 31 55 100 380838 380902 10 923 ["%at_lBE6UTN1;1y`O"]]

private def r31_1 : List (Chunk 31) := [
  w 31 54 0 390023 390777 100 9405 ["+sj1ktq$g0:#@xH}L8>Wt,!o'`oQc[7mNO7js]r]IEsFg'1=;zu[~)pOv`KFlyk*","S#FzYJi=V,x14ua!/5z<m89{?pQQ8utmXv([ec=3-L`,mpmMs?q@$MtKXNcK?qnR","#tnf:D.@)jZi#'2}xl|ovulTXKYcL7M;qe-%/3JlZNiq-+MZK2g=$n#9N"],
  w 31 54 100 390832 390902 15 1358 ["4K*Y|^gspi{RvTuu1h;E_%P4Dl1+T;*XN6L"],
  w 31 53 0 400022 400771 100 9260 ["1Rk=0xJ;Z0!.hVa2*BAkc.:ljG`qB}qM,s>q!jq`rH@T@p$oBc(}6iI:#>V8bWec","lTZl`]S;(,/<Gcj@}.<:}zmZ)EiMnO`,)!RnKc~~@*p{V#!3Rw_u:eIczq[9B4N1","zC>CWPv@}~fgg~YTOA}|CGO@.I3)='s^KTcyqe~$/Qm,&(`mU%-.oMZEp0#O.b]h","(pWKO~5|6t^z8*6C|>sE&dWw<:_bB6{4%G0o%F!.6b="],
  w 31 53 100 400772 400901 19 1667 ["#M8#ieOp=694b-n~MyRvV'Y(V<wIF<Bb|RZj&}4;SwrGi+G$Y]ry"]]

private def r31_2 : List (Chunk 31) := [
  w 31 52 0 410021 410712 100 9125 ["c0OC.#%0H+O510X2p3=~rk96>+I-}JKT(dPq7)9gkuk}w06(#2q47qZz-tZUV6R*","CwDckm.<T$2_JA$^NOl2=1~&Q%XpoUL3VQ9DJH>Y`!zePbJ+#Up+zPNCo0ElPaW5","fGxGuvDWHlhw|&@cpquxB=!v@tbW+$VUfDKbG*!5:N,h[&&t&5W&>_v>KMy[+S}p","0E^Vsb5t2<m?5!Hs1Dg.3@2;<KW^gsU|U.x-9csXphKmfX?)g5`ZZ.I&}a88si,,","#V-(fR1LCR-h$.q["],
  w 31 52 100 410713 410901 23 1973 ["bN~ejI2s/Si@rX>ED5V,mfp;N3ePic3SOi_[Bn>_|S2iMaL@e*!nOY}h7@?m1sAX",")p"],
  w 31 51 0 420020 420707 100 9026 ["=3NUw#3j87?W?}1Q_c*KE{~ZA0a4U+dxefAm|m0)cIFPA0A`}K+'zyDTq[,AryeR","iD|^.J@&a,/'42ce,l2.#h_|OEYfGpC<FP,@l#5%-6V$M;:mo']l4bZ:52:}m(e`","f|7;[1,QhDfg.W[5xUo'4$eH:h>H>yu0<r[wcIGC='8O?r~$lHuQG)4MSn:YJ/#b","O'.uTh[@wc!L$V,!OBO`cl`$wVQMh<JN~x74M*#6}2Y=1P6.%'[G!=|K,nXX[j>S","JAHJp[.K)li|)u9|v:Ly(z2b,i~A%L|R:Zo1m:_p"],
  w 31 51 100 420708 420900 26 2169 ["kc/bM.s;}N/)=iD8YO2v@z*2'cpl-&aoPftDXsY1RrO?Y$D?'_~h^2s14.AZVeo5","q-98<ms<OIWy[2,[>7G}5"]]

private def r31_3 : List (Chunk 31) := [
  w 31 50 0 430019 430649 100 8905 ["F|dQ'Hfmt8rv=UBL@-3Aq/2mq`O)%Fn]x'A{yd~[i]Ylz*X.(D@N<](enU`h#MYw","oU>zYrTf;`xC*9;4uHdU}:?k5OXu!''Z7ap$}s!*A8OsLLnh^o-pS[jD})a{5;f0","*JB7P#JYlY]wGOU,K86uMTHxQdMUoCbt-75*5,,^P;,M,:^zI[j?^#y{S(d<#`i)","n-hy,|-8cFtI*>2Tr/~T_~8nx/uJ,E3]1Yvdjd3k9o_Iv#,WzV14oX7R/1Rcv<NS","+9E9NyIH5e8t0S?R`vGY}:qISjf+ekZ}|0I[U^:-!@;@.E+{CC&ZHt,5!~~-"],
  w 31 50 100 430650 430900 29 2375 ["k&3hYjNK^oh.&oS&SYj&N5J_6|5#fHApF3ibz.Ng-Ca)z-.2[Jbe%KQq7?8Gyq?X","$Ay1|U1>+ae@Ojn,'7j.<@2yb[sJ,-r>e`**c"],
  w 31 49 0 440018 440644 100 8816 ["AnRZ~D/>7X:.mO?Qe=uyNp-M0[mNj6MFiSc(%Tt$YT)6CjOL!2_/4-,zb?trBbJZ","IC5u!U_z/,}EW1Vzg7ne9eMY<MvjKYV'dW(p@D~A$vlv?B=#lNGdh3jE/wDzMZ,7","{^G?G.xvjenD@=ls%|zrV9P,b_>nKwA}Ojp`GC[EaDiY^0vCPU9Ti`k*1CJKa_'4","ka.RQ5,~Br=oE%[L7[q_8u8+`i@z1rw@:#xrq<=hx4.QLU}.&vYl|2l._f,>PE0#","qg!l6J{[P8VClq]8zlDRIwb.^_+;}%q;RVJ/IVF0dF:Qf%*Oz4{5_an*OV%$Vj,%","eO_k&2/gi"],
  w 31 49 100 440645 440899 31 2474 ["Y^~BWZ#8tvYQ2TaAY&xQpmXwr;Q<]t4~~iuKfbGT@4X24e<oq&{!^F&RkYn%:$84","Ej2UnM6Mx;]U=XV}2w+V{Fa>(&~eDlt{]/i*2p|cKb/LZG$^"]]

private def r31_4 : List (Chunk 31) := [
  w 31 48 0 450017 450640 100 8697 ["&VsBzy--<k#0o*RCX]|N7g>`w`|2~]/~(.GFN*Q1aoa6^T.hqd;2lS,r~91E9GvF","p~m7B)_2Y`W1I^c`|&cAS@^j_`2Q+D?SeADWKf?}-{qj>a;oB<AFEzgy^'K=*-JM","i0gTebO@V(Xj14,e)U.d2y:y.ml;kOu4-Z88Y9-UOAPN*'w8BK(|l%,B?QbEx]u$","V$1D,?mu9miuyJ8?xKSTqQx*{_rQr'a=!RrdL,XM+U0SAV{t3Fjf~CbC}cH]g)L~","f:KKiw*i2t$,V{8)hbXDtJTQQ#Ds?=yPN<S,w+$o[.LZ>l3arrGsUWDzR*vV12(o","#"],
  w 31 48 100 450641 450899 33 2588 ["83Xj/}~^YbTMx9r5;(bXQ6hX@&-,v]-mvq[!TvP^HT*s>}?'7*aTEyr,,{}V3BG(","2CplNwUL9dLU.z4'96f}v6zbf+#-%<gY6-;:}T6Yyiye%7Nh*8td>r^uY&|9N}2"],
  w 31 47 0 460016 460583 100 8599 ["W^UbU)1,'4fD`nW4Kr+uL!(6:hY-3H:<xDnb[ShnR_Oa!Z`JF1KCs2Z_HSy5HV{J",":([`]#s-i;$9D0o5c@fmVLhp@hF-gg*eU@pYm:APDJU/XsW1^hu^S{8!w}#qm;]C","b<FTdzcT'q*?YdMQfMTWF`F)!Wof8)4jeQ]>te;rc_iBE(jWe_ju9YcH~S}'GiB<","$5<D'7KqEm7ip(tg5W,B?>68vq#eqJ,s[;?Rq*;HKA9YrcX((w{ewzktlb,4Z=@,","ub<YJ>`ro2c2V0Q17Iq--se?h[>0ZCFhwh#d'J1$Dl3;S_#96WsE{^$DnQE9aczV","#"],
  w 31 47 100 460584 460898 34 2610 ["d[sM`HU?T3$)d+uwUOQ,#-r|?6dM0k?'-Vho3GXFzKd#7F]f%X}.=5zG-R[P|L3*","nC0/{D~P'|_!yb!_Zyz*Rfyg9BsF$;+(zW#9!+j[i=Pcg_`U(uVd$?Gq-}RJ=ad)","'QA8*_~s]Q1!C:"]]

private def r31_5 : List (Chunk 31) := [
  w 31 46 0 470015 470579 100 8492 ["%`}m3~^^:i>h+_TMa49@=Xi(j=QUE{0-gOb}=y{z`?'/?YyB>Sdt>8OR9&83-HN:","(U.XK)HPAK]<L&gq(l?Yl;iB_'?n?-b8O20EsSLcN!<v>X^3r-.T|{vB>djz#qR8","RLeknxx58a&,3SVmDHX<}{H4K@IvfrxQFO.OvB-x$mUd~9|'=Z!j?!^3o;(Blb~O","W#bazaFm%re-w(F%=P):rD5uzYqhC^nJ<GHR{(PWS<_?8)6fRH(S+U@<6l~sG;RU","):WSO+v[9_Z{;&G5'a'F&aWHXu5G)t{]7D<S6'wsL?hBQ!oa/3m,8%]_,J[4"],
  w 31 46 100 470580 470898 35 2623 ["<vm9e@dufl48T'Lc)D'=pwqb&:>3@On02@y$b#yV'NGp)V0GBn{Vt.oX2W1LzJe7","(N#(nr@HI=8:s3KY5gUP'2-G_B=q_|:_j@*#tY4bo2V<hZ4s1;s|<Y][}?;}lzoe","5r}{B-qd_Y+p.A&Oe]H.yB"],
  w 31 45 0 480014 480576 100 8377 ["OcpW|Y|h0Z.u_(wIyCMR;G{[-v,;cfG[%<ed_-ueRNFmOfwT7;iMs*5T0;xV=.g:","u!GF[sNTWia.7h6S9}3m;n?&Z}eU<6Gy]0*l8Xn8Qcg`$01K]y?f8sRh6_bm;(CQ","?8wz0n;^)JecmOO[1>TY?~IhR[O4Jm',|AvO%_/+?-[=$Xkc.#$shi@F/6In<hr)","{~sP|bRCdh7M?2CFYgM@h01gKrQmk_>4kLZk+p!mUdFc'mf6t,^G(+jO,l)>n;Ti","$`0X?1va/l*@c,I77x,/+Q#vpIikIj5Cv~yCOM9SA:m<^.fOy`wUR7>O,i!s"],
  w 31 45 100 480577 480897 35 2579 ["2je*lI2zARN-IZz`a&?9p-&,*y`E?XCJ)H}_GJ9%tK1b4v$Q$VW#8EQ9F6-`N_pH","4`Ei]E!rLVqQV}1ka${Gr#H@hFrzvyM,]s&3M.~ErF/K7G514&s=(gHqJhX4(:y+","#W~$qb{2xA2naBGknsZ~&=I[58/"]]

private def r31_6 : List (Chunk 31) := [
  w 31 44 0 490013 490520 100 8254 [".34.q7|ebV7Vs4xR[[|eRsT|b>HFZ/k`!;v3|5<(Mvj&1a*k1>DDZEqE#'Aemv]!","=UnS_i1{;b~Qjk`V^H#PxGG&Cr-2EM?Jn;f~*W]Qq8Higg<=`TymJ=wu!zYl0ryi","Y[fzcluaZZd6OxR5]L.$L[KdA|r0g*0!L3:BBru[eHW.*PPB,]dzW_69X>55F.Im","zj_<'kQ:%RKSY1TZ)p~FurN-@T`mRh;sG}<r%`T*=^!key$(F1kPfowW?A`JV7u-","^ui@C5.$v*/rm:O!K<V7p<>e12X1]a'E>;J9MeCrRP-ADA0Z&T7m5D2Jb"],
  w 31 44 100 490521 490897 35 2525 ["logTdb#jnPSukOqqrDFn,VPh3O8x{;!c,&6'6UX?KmmXuAmZ.CW,|Ob?!dp;948_","EXTBkO8w}X$2HbGVI5_EVFmi!$WG>h%^EJIm-En(VXf.lOz;le`Vg^ApX]7|5Mqr",",-E{j2a%H,L0:;UE79@|?Mcf|E0$,Cje"],
  w 31 43 0 500012 500517 100 8152 ["2'=36goYuxr;M%>Xh?_.Xunp'Svga@67[y%$AVQQBO+$/^>kC$gUgo0}CGR5Ffo*","z,M679O!I&fR:UatW>_$9ug.rNZvI>wBxN+`mP`Tqm4~PNNK'HW.8B0pKsf?>$OA","OIrwnr&T>[HXC,j67&JHM|}Dj.P*2bds[M.oZNG5C6Fiz>vR3>B,m3Jm%@dst<J}","Ul6rx|NuxllEaB$IUz.,sEE*&M@i~X+SiJ2lD7hmCwoi?*QKD1#2Y_=4Pq-yeqi|","#r>[C~2N$@b|>G|BG9=U2i,(=1x#2q|20i8bC,&,7vg<&^T^y`:;a%EX-oy"],
  w 31 43 100 500518 500896 34 2389 ["0VD]U^%a28FI=fy7s7McojreCGA^b5;qoJ>D{2UaMFZ<700CS-MI<h~]=k''y*om","gMH.WbQ_C/$qgh`;qrwXp1:[:4*o.0v%x;>2~lZWa|.u9!b}iIEM-O;nF._Aj2Y%","4CV1x><O[P(?jCI-l`u@yg@)_3"]]

private def r31_7 : List (Chunk 31) := [
  w 31 42 0 510011 510515 100 8024 ["1!=Z5lr]G}x7KjhIoCgNh)O-zC'J#06&R,`~AjiZ.xUk0[D6:/d=1}5oVt_Z3%B:","G@NvuL^P7*{Rh,iroU&V|z.>r]A/(JowT>U!!Hl?</9n4E=a$}5I(~]nz((qlex{","Gx{f7i4bG)zE~tV<J&6id{udbIxc(CEPi8eW;&nl;~9&^J60RyfQ4h~<=V!C].Af","D~'$!~xuL0yG}g#b*@Oj'EiQeCiy({fo9~h~OV,f)=^i=LoF2QGzwR!+Pg.mt}]b","%D>Hi,O+NG(?G/np6K43C_ZHG.7+v2YWaNNtg9]YNG?H[.QSocf{Y]|~+bn"],
  w 31 42 100 510516 510896 33 2264 ["/pe*90`|KwV,*qiK;s3Fi>cK_uCyk0ZyCBvVo$cUkrE9$JYbwj1xuhcn&Y#p%^q6","O_nn5/~NC=jLW%A.9?_FtS3tvw<VTGzWfoBb_f,XanR'JRT4Q6m},`.2s4vTkSuz","(+;=azzf0J([qAG7@oZ3f&|dTQ?9bg"],
  w 31 41 0 520010 520513 100 7896 ["8XJ(IVM&PJhg>M{1X$AG<ZA-J<}>YNLe7[Z2f,3v`[^;0>+}qq7bn[8BXvre**es","3-LllpOO/T:}%LER2Z2OX~F&4'C;=M2MTR2aZz]E|w_QwIg9g26OX#!%W|ZxdRl$","xc~;Nlrm0h:r}$ob4Fj,>i0.kXAZR#xC'~d^cYO7Zq`s)x.[5zZ]96OiYz)D-l<K","6u&(*t}?3Qvbe?]Y?aV>eYaZg.qs#qRGrT~m,4'`Wl+'hL-ar!oUnWHZku-0MbT$","#qMl@.u}~*b)OScn~Lp&,DC*C?Vnny['*f%k~h(aa@_-7KcDEOE<i(JN(Hh"],
  w 31 41 100 520514 520833 31 2083 ["cz`@ryx?lY)0U*#5O8%eb%rR&&[O1Fc%iqr4Xqvr@lBY>}$nZaMmw%40Yph63b#!","|&?o04/]Vc}lmg>&S&b%EwaaTEQ_g!QuopTx.PpM2^-+;|)J{13k7.~Q{H<k&`g1","%n[s+s/LV`m6[crS$y!8g`UIs"]]

private def r31_8 : List (Chunk 31) := [
  w 31 40 0 530009 530512 100 7745 ["H&Qn<1lk*(O>)U.&[y`e}<C{t~L.qM{dVMDI>L>~*sr8V2yIg=NS]*4;|.r!<h=&","REPy+^xW`G3{=1-IkOK^^(-;X=fWvV9j<tw[s&BVjB7yi>NY0^rPHbJ_q:xKho^A","2b0=_Nn=NI_GTQSFCfX[m)5}zp-^eX.{i}CBiSZlU%..vwyb^OII%uJ/FL6#Mt@X","*mly_Pa&1B$@|SwU9p3FggVHgm/#Gm]ZDC_-_p0K/Atq@xoAGj/p>8vxyiskH=M(","-9,W`v^$<Y(4&nT*XukL`M!S:E<AFoA;eV<($J`X6wH;I[O`xIUm!du/.Htf(x'n","+F"],
  w 31 40 100 530513 530832 29 1907 ["E*#;=f+Q,F]BR'i*7H`9J$2ON{jc+VYv#.j<6H?Xuzn_A?v*VZH<S&Ta=Mus.z71","p|&fa%]b.?b%Ke$D=BNW_tWm.48UU{'r<?)5O$YrhxO|IG*h@{6I&TwrF<*hE~t;","-;JOxkkxeb26a9"],
  w 31 39 0 540008 540457 100 7602 ["$m*ZHQo4.r_x$'d@?RMn@H#?1%XS.:q@c^}sUO_!&&(]<J=3'^)EH(P~')[eDE_k","wg:#}DFgZ@d<2{>@b]EteP9q,w+Y7V6*XK;8<J;|Oq%w:M]F]>2pDf8(y1k:.Mem","r*K.G;8jQi8B=fG<-2i@oN2<PqYfaovx@{R0@0!:,hoU`{[8r{wc39+H3~`F.imz","xaNS:aFv_vp^/Idhh&j)F~AD^lcp1wtAgieJIT1_bmdrH{ua'GHWLe@eww$S/M0t","=7!Vm*)37&~,jrimU>PknL2V;QY=d.b+`b6(0,LH]<v:G[zR7VCb!0t&'o@ds^9^","%"],
  w 31 39 100 540512 540832 27 1745 ["'1/KYmcleG33t@v|Aq7o=x+7;90F$hBn0ou]2&Oi^s_,}a#R5R!|/~KIfydj}.,V","{EIQ(*)M#>sXP[[l``kloa}5[0^Y+!Ul[puJ2y!D#b~#+M?:s*PL3aeFr2QWP$TM","&{|=fKf@{Ub_"]]

private def r31_9 : List (Chunk 31) := [
  w 31 38 0 550007 550456 100 7438 ["ej8>Z`p{J+2p?*l{)S0J1#?FQ{RHB/y^>B&LvDx1thkN]Hk]LF$']t{K&GcoBo{J","[zApWSL/L*y`y(:5w:%d=)sDC~@PbW;+H`0}?+.R?AN+8T}lZGp^&#;722GjVj$f","5gC53N)?#,bidbWF8q+m`Sg_eUy&1H*'=:8'X<pK2O]vE#Y^eM=:(ep3%pTGJN!o","Oo/JytUt+Cczco:U2sGN>D<aU>j>F'SzZD<xMOoG9:N#7#XlVm[lTR1}{]>5(%C|","U=;I';=gqR0fvynd=:ClKv_@?2?T9Nbz%sGE]$BOX21A#Y`n|'GOD#vQKn2m2=}s","#FiL'b?I>)>"],
  w 31 38 100 550512 550769 24 1515 ["/:L%;)~R0u)s]%by~M~e].<hKlh/WLr!]K]>2E}ub+N3tBk?Gs'6p~JmJqN#axjY","7dfCW|uN6]H+9VVZB,Kh]!9h8C]2?][_<J6Bu^?_Hu[BzavMz1%8ej(?gfl>Z,Y"],
  w 31 37 0 560006 560456 100 7285 ["uZt.b7Hzy}!e5XOwU*_g2&%Dd@7>N%Mpb&y&chb24dcL`NnJbxityh$da)'IG4H!","[`<|@I$+p{NoF:2FhqD+[kS6usf$bbt(]k2/<)Z,&)z.71Onnh0FM~L6U)Ee(.RT","ejphJndUg)PK>MZZ/iUOUF>-%`&oBhwP.]o*t+wlI`le2G6!k>:*&)BxD~09l5'z","1fl:%kYL`[|l(]vz'Z?&|cf~s{V4%Ky#C@MA-/G;-Zq,_lI(U].HEISNd3L@#p>1","I[E<[VNgL@rs7dy{-?&)/E@+0q%SY#)5+C*?P8/n:J0',jUA^CiwyD?T@p'pYu7f","vw/*0oQ-UCvgD0'"],
  w 31 37 100 560512 560768 21 1296 ["Oo*NU&9L!4qsFH?#AWBK[_P&]^%]U|^bipZe.qFNP_-,cY6VNV<n[2Qi8:E/rUP6","/K(EERd<N-N!g0qP(5:hxL*+Nmu7hQr5<UJW>;Y-44O|%e-"]]

private def r31_10 : List (Chunk 31) := [
  w 31 36 0 570005 570512 100 7104 ["W6]BbcweoT?bk;Cck@8g0uuN<A/Di5~HH52:bAOA+^OUBGk-xoWEELgrP`ctvk2*","ne)E3-d%|n.9IuOi&u}0=8H!$e}L}%TMs(4w/<qZrs|'E?P<0O(LpFPz=.{]w~?4","bK,RW%:.Z9okgtb[esKK5?^:2,~KgAL7*A/:-n(:AZNV:Cb_:rU]9LsLURj7,Qj~","Z+Qqj-uiF>yVO9~WObZsm;fNnsV+-67)`G4_G9.Qf{|>dlh)s>6iU)lB0(xb9+Rg","x'}jl??Bm9%kTT?pAPJ6o<I~40Dc#}jp[=qe9m)c?jLrZLG.J(L(0^=k}7@4NfOO","'V#%4E:.ZHV@h,AcU3,%}+FK5F}4"],
  w 31 36 100 570513 570768 18 1086 ["oXj7x1G8c<^tzs`Zn8T_s=Thn!?sK/~f,p5]kIpKYN#_[}--6QRPyz,-u&.Z#%Gt","'2OH,;:<f5Ol}!3Lu+!0C[/.>Arn=1{&"],
  w 31 35 0 580004 580513 100 6931 ["mNx][oY.d2NJ:WrZS<qzdsh_rqtIdY/+@09=3tV$iNZ>h2v;$otFs|6~e5s-b0DR","r;RCm%g=Soe~Bdy[ZRhg|+M.i[V84m~W+xeB~S!(+EW}J3aA/p*V6rgl1@m9DI$`","w8S&Tc~]$/cFO.QP/w!%2d<M[B-4l<crypJVs25I2CF$m0mM!.=<6guck=|:L]f{","-)(<8$>C;wF]lPHg%OQzuJ@+1ci't;Iaw2k8m6QmlW$2`23K*#+QBTQzg8B|%LN[","):oyBA7&53iKF[2}Lw;c[Qsryzp|&51+BUp@!sSuzJt6e[E15$.kvtq(K18$9dkN","$H0t,Tmhglr;d9yo..P0WplwA.nG}7qZ<e$16SE)mu%g"],
  w 31 35 100 580514 580705 14 829 ["i<$myD0=(1OZ4t&yS9[f[6r?*dwD3/U<#l[<xza{fV6eHf@c^>X/|XQF3(jfC}<p","#.!<.'hFih"]]

private def r31_11 : List (Chunk 31) := [
  w 31 34 0 590003 590515 100 6721 ["TDu&fRpo$?B8qHjls=ur=MN1l4-9g,lYu<>v9,ZKD:,px2~MQe=T6n%W-FM7zsIg","Z&3HI.*:!4CG}^d7/7%P/+:Ni@wGvAI9O(so10:Yig~XE*5M6yzSK&cb!tu&gox{","g-#<#ieZaZ$:;+@n0E_bI][JhnYhRPy!Y}ii5g6V.Sy4zR0S;lD3dmzzDft=(!|{","/wOT'6SaNm*vQ.vR`.{DRZU7Qk)ZlRQ!9{DyBw86Y*H[dS3TYYwuC6)_Ntb@F,$,","rvLk}zB8MF|1}>bE[-$m#E}?!unhHq)Fm[-.fXHfumO>m|r]ETA<Rzl2ULS!QG|G",")B~ym}K&O(/,;o&ptn86,n6@}-Tj9w}/XC%ZRZDoTjEoNK;v+u~"],
  w 31 34 100 590516 590704 10 583 ["%)pu.w(rkKSz1YM&7Z:CVc~hFc-KdwZY1pADGu=c#YeXO|[mY3^!"],
  w 31 33 0 600002 600576 100 6535 ["/_]T(/5cizF4Gsn[c{)/80!Q(qNau~DkY{=5I2&t}anQ&)i7a1d)zeQJ[^aX/*ck","qri!7D8wUWpZ#X%0C,TcIo'0:XO39E<[m$nSFK6?#$%roL}+FO}hB<toPgb];<Gt","zQr*=+^qj'^XDpQ@+O5FY>x.yk88t%2/i/J,{Qmtab7EL$_fzD(MdEt7GO<[w6q0","6QoRF<;u-~U+<dT<JOG7Pq#Z[htD<LB'CCmZ`|7b2ATt{VsdsHJ}C|~#zE*+fMKH","p2U7`<gWX~)<5YmW6m_1On!sJ`/qtfH;$2CY<upfVX0WsgfbG+]m)K.<8z5-OVS{","{fR[RP6Ew)Cnv)Cdw<FwBvQ:pv-nq>_/!u]ni4_R]RTBc,K=GZazV,HCOc5t,&E_","<+9["],
  w 31 33 100 600577 600704 6 346 ["$aGRS:A$+[BbzQ3M4Rw=H,ga4(e@d$)j4"]]

private def r31_12 : List (Chunk 31) := [
  w 31 32 0 610001 610640 100 6314 ["Fn;hZ}.b4(H@?ZIg#!nIP'$ji}4Q$YDG(G3hJtM[mqA{?U?m&b4!Z_/XUSi)FIs{","#;8Q:3w^u_3JW#xU_5Lm`[+*Iw@~#w3;/4l(,t/9=T4`yeBdBSc:Bz:f|lBI''}A","_l'3@zO'DVg[r5J)KDr~30`x=PWe<araMqOqEuG5Gz[eFGr,+&RG^pG+`]-)4[-t","ct,#_%2,@?P)qg(o68hs/k!f6UU7TD,`F5j99xk]9]ZeD.U%:Rzv]pmQjKSRL49&","'oNT+<7qXu6-9T-Npd>H,bHhG-6z.NAn[0vW1Kmrj{~AkSK2_U?lFuep[DR?QG,l","ukp8%d8OEEN#'_wx)?CMJyzh4p<b^f||4cxAjGOH`:O[rH=}C,.,MS.!OrEpO=*,","(P1Jj$RS&^t'ApNsd<~"],
  w 31 32 100 610641 610641 1 57 ["=LM`vB"],
  w 31 31 0 620000 620640 96 5890 [";q1oxc(7&Yk[-_R4|NM9/rM2u}eO{MOp.sg{qIYhv%(:(Lh~ig}{5/ck__LZJW`o","QT?u!EZ/kYhKZ@(,5lHUS}h:b#<3ktkK~f~8gcV>6tCRFUuF.O|'AE<1l5mPN?F?",":4W.V5aa:hCTRsg#|oK}o67T|!dNlcrtD.!E#./wk]z2j~Ate>hbt6]:'WsT/[Dc","h<c,$mq?@ixI`K0K]8ckncu+l]l4f5uNOYvN$fWx'{)2u/,OT('QM[+Cx<hbdB;G",",8uE/14gT>(NZ>#x9xRZj=2,MW2$Qo8|:<mc|Roafp+q;hZZe9HS8c$)*#RfsT1h","u-SQ#KoSE|/W$6I%oTEV4n-QqbdeS1Ko9K:S(Id(iV0iw;Eth<)xKdJce[Kd2'@q","'VC4aphO[};-qB"],
  w 31 30 0 630000 630640 91 5387 ["3vxsX5J,3MKD@&|ZegE/LTTld<%D;x%yTL0+K(Zd5'DMhp_|uO'U}h^MV?RN9lb?","tJ?'8M+mikw6:]m4{v0=XL*{jSEWM,;}7z>@{xq>+bz0*~L&7cf_D]eSl.yx_R8]","1*:FD:bZFE>9P&&mS6ei[>e,S.@DAJI`h+UZ1XiZUal&9C(x<vzisJp<wVI~&QAf","..bpSAKoeOO&qj[O84HT+Ws/6NE's/g4VBUO-v!S`V`WVBmI-Rl_dG'2}|k}MGM8","}=eGL1r]g1sFfnUW?hyBVH^aimhK=Vxe|z$Qht9uhwr9Y*C1mPR'^QcD/kd'UsLE","<3wZ~1.}lhXLr}P&IvdQ;?hcCX18i&(x7D_|nusw;hdVF`^aOIQ]ug9T]pY6x@vR","%f]5*aW"]]

private def r31_13 : List (Chunk 31) := [
  w 31 29 0 640000 640577 85 4859 ["@+kZoyh$75ad}G1$W[@UBzKW#|vrcf&o}Z~XnK8^_u>0n(NRrz?%dNc0;btC.KoS","AP.zp80~Ja1(@](duDdAiTnex/LPN6gPOe2Bg|I*lB13l-sn(}l5mkb+mW7^%*$8","3%sc6QtVS4&j0#?/p8sN&$~;{)T@A(lGh#P|=TUnScXRw2)$K*lJ3z#jZ5mxrOxZ","5kOKYH~}@DERUC]t%v('e>7#5{7eN!JF22IvW,p>B+?ucDF4CDM1I1-iZQ4J0;Pn","&Jte1NbcCL%@`)E;fJd3q-UQ'gjR8hyyVhfpfIo;v3,us8ZR9ptKCEs7V[JsYX~g","L8b=bg37FG[(jGVzTqi;P.-foWcA;(e!~9>$Jqe)Gs8cu-e3S3*hXBrgAxNpoaV"],
  w 31 28 0 650000 650576 80 4404 [",0u.r0JfJb:3l`>jG*5a&|+p0To#RZV(iKytk%b|'wIJGOW{cg!0'=4}27QcLLzO","=I'4`'8TC&O:I`V4e^tDm;8WGhBJ&NqBpKb;~FPEn|bkr`5lvQ6f;ZXrN]R)+K34","=UO}|f<;S;'J,*+2}L?&=E?}w']yh&C(v[EYrAa=#,Uu<9W(qVm)=&NoI4ysSjRM","6n7vV%DO`i.!6/5&.;uHgli7`e{R.Q#Gzp{d<&&caAzEN}GBa9:lY@:qH-Yj_vb-","I%PYZczLIa23fF^L]Ig~rpK^jcQW._P@$@fxX+7C)NI#<@z]l]_@gt!4DCy6j|PM","+Hgwd[9E[pzHBab?tu2rh^uPfYQOHE=Cpxj)1$,|y4}3aS"],
  w 31 27 0 660000 660576 75 3984 ["DRi'Z=s[GN}1<W6c0h.@J1tC6w4=Y?>t]6:xRu8h;#:#Q]Y:nw%wK8-4k+g3TJc3","tFrN0~5Z1q.tVfAhTByA;Bv)o5YE4t:Mm9<CXgz~r>3^K*WhLbKA(C[}EksC[E:8","zqp-Pe5#}>b4*5q]OD|/u+cOf7H'iO,I~`.UX38=/>n!&.:$K!1@LqiYCq6!qP8F","x91$H9rLR.@oqKyKqaGn'v&^mt,>:W44w%u8]*2`F|<fI:jO5!%;[,JG]X|1Qr(t","~`O2KA,kxz_4X32ni4yL9(5FAOLB)|h'}{jX$sk,qWvKRqYh&($<MK6+U4SC%Dx+","(%#)^mtKR!tHb,D5Fa(.UjXeGFH*2[Nsc[<iUrRPqc.Z"],
  w 31 26 0 670000 670513 70 3579 ["yR{#xOE+(k5-:(H<z]Fi3RVlWF2v~o,|QHP5Hf'-9#1rzI&[,P1==UNP3CDD|E{#","XD9rYjwtYI&agl<0acgn?l7OM+Lwr4PnGD-smKakdUd1CyJ!z;G2R2I}xM/SV&wh","Vw?UZg&nB@}R-<G:aH6oSJ;8Fr]/N5=j2`)kyPVth<PJehUikw!bs<xkl*U)HWG;","vWg7HXND=6(t<=7XZ-Fgi9U!*|4)qhR@'Fe9NH0EUJLf4${R?gW_p~q_V&KNqgmw","+F518x$EWiZler*Bsg@pz$h$[;1RkAG8hfJik[38pfYms.5C$`Sf2eS,E*5K(V+B","3<c:!nL{$XRxp|r!/*`1Lc}ppntA=W6k)"]]

private def r31_14 : List (Chunk 31) := [
  w 31 25 0 680000 680512 65 3199 ["g@cD[qwCg~T_-LB-T=B2InXu{}_uWdZK=Krk_8j$!6%|Q1k69mewozH0+>L&myT[","s5757IqF!R+M`$pcD!-L'ycL'lPW3jqha5ssY33C`R&/2^~O-TDa`!q;34qv>$N_","{7h9Vcw496;7pd|Px4ZxRiCAEPhGQ7^O$|+xQr?@'8F:h}WwBgDvtO'+BnmrqjE&","h}GyB*DFDha;8=pym3Iy>^2(UASzRgWaMZ`ZxRm&!}[4])SlIsHX&f:vm.Z7f#VM","`~p,@#F1]2Oy6ZNHegmNzA8C&Jy5e-}DgmV4W.NDc)tJreI}UH/?fX8z}G<.f~?K","2LxPp?Oy0`Sp"],
  w 31 24 0 690000 690512 61 2887 ["Lf,k::1/Brt<{jZX{Pq)rNM#~wPQfs>bjv*j,#U=~O;U,6d0[9{{^{p7+Dn_7HJ3","T,!&9fr.tz%*%,OWDC`]mYQP^82Hw9>%t:|_zz~?y&.i.u>2gLaUG$@|>tm9-)]`","]kRnJ1`Lk1<>Cf3@9rk~vzI'([27:#KnjOz+&`dnq)j:D9}(gl<(Ga)LR.U0e?4h","fkz61CPi%gMDs<5V_wq[[/DD_T4frBs%-37~&Lj?Dtf%Mtj>S]hH5W5'_7=K^jkf","c+67Yocne)7Q7:*]>T$mlSD<Yw62@~KMTDr?NO72(JcjXyNZnZgzEvwR?y6vtM~Y","0@O,5k)l"],
  w 31 23 0 700000 700449 56 2549 ["`Pg%H-*.?F?{DF''EUfM1aB^o^^#`.1;BpT:B67R~@BTe7`VL+tScEt+o>pc`ty|","vm[QnO*f%SL%wX0o{(A0DtWOB+j`[o>g}MXAb*wkk7`5R%#ob#V9)r@}V&VHlCTs","h'.t1gk'kbLK=^9Y$sx!2b!+Z0d!o>EoWH:,yocc%8ue*]N-GA$FCv.I^1NNHw,h","RAn{5?p14C0%/aAJBx@wi>72BNdexBjR:?:Kun)GJK(sD_JyL&7Pnli@qPwfIS'8","(36h55%]LW;~b4cCn}J3Gy:}V-6)-J_8|1M>myc8jmD#=vpzBNriu`"],
  w 31 22 0 710000 710448 52 2270 ["0V%PKu+ql($}dIN75641fnR<r[!)h({^0rU5JAA*Ni&-3LSjOpN/XG-)3FN~#*ct","(vLbX%~v6Fn]K?#mi[{1%<`[|PGqQEo)`W4r'zEm%?sG8(^7vD,h1t[ihm7>o&2a","Yv*0J^>?rI1]VRw:R7M;:ps{6,X!7=^qW*[3~+{4(A]GL-SNYy#g>?1;x<c9m<!_","j+IGC3+?W_fw'U$CsZpNWT>2[*+j&K)v'eh)Sk2li#[T'@|P2*!Qq^vvGlX3C(ne","Q/NXqj(A#F-gr8=oZZT.c%S7(ibNzwRYT"]]

private def r31_15 : List (Chunk 31) := [
  w 31 21 0 720000 720448 48 2015 ["m;0;%KAbNS0r{fvcxp`0k+x:r3g^2^@]7iLz:C]vJx*^K[ivZ?_N1o59]U,5_WP[","iU1n2C1jt0Sc8-arg|q]2d`U8m|{5hn}o1IuN4yd_<D#4Yb(`k)z/^K^!P(uEq,!","sND)vbd$L:N&yd$S{,QdG!GrM,O^yY()nD?}mKK3&87$P4wa{FcA9@au5$;T)7o:",";Co6ya:cXzKX|fd1A)eUDgAXF}.:LlQe.6}7Cbh4W7I_A|TAYj%%[4?wJ7O'+2D3","#=_LHf+*ZaEQxmg*y|,0"],
  w 31 20 0 730000 730385 44 1770 ["&R4l4aff_$=<Vw^'a<Zs_hj7-GlTuq*A2HT[s!^%XX@n(2s*h^}|P1s@N&,>l^nO","Qf.1Rye%YcG[2q+8!@-Pox+2}@)fY0z2$w^P/yoI}tk@g>juii;jc4orr~^R7%oi","()RVw&Z@ew@ze2ldk`ff`|Ju6.$NK~XF.@<eCYk&iDK#.{`z)xO;Q9`/FL7Q.{YS","P?oI6R;^G8%PpX.'}qW(rVOb%$C5ae6?+FteKR`DTH[5o,t>7W9e5a15]cz/BZfY",">)]{"],
  w 31 19 0 740000 740384 40 1543 ["X!ME5NoTHS6L4:RJ@Lv7slzbzbIvdzWvZ@''|)z#1ND>Y$nIwi@h;)>ftDvGRzE/","8?>oL1YX-QC6;ztG8c&K8<wWPcrFCipU,ZHx-^fc=a^GWN.i!Wch>ZBz9*Dj2'(z","8;j,v8c~(Z&2FGG63mI_%?GVTA])w-.k-#@c(Ve$.8lppH2gBLplPA_gYQv+KN,`","+xsf$&&]<cwwlnC>o|2pe8,%1RG5-yii.A]n)-x5PgBm"],
  w 31 18 0 750000 750384 37 1369 ["ph_Sd3?+z2GS*##FpH*)wzwj[o$!)p/)]0^A(uzf8EI)bq%V,aWi*`SAF<7`o25a","FN#*XeDy'8j-:YAC~o:v4I4<sYp;*'=N^q~v6J#JWNn.A+uhTQfp&nml.|A*CD9*","Md^Y~jlj>W!Kdq=i*s.QtD'@z2s'}CswU6@5)lIV*W[$4.l(1gtge.Zzz97Z9IrJ","):W&7CkA,_?drWtzxD4K*i?8R0ZSXm)M"]]

private def r31_16 : List (Chunk 31) := [
  w 31 17 0 760000 760321 33 1170 ["!s}jdKr7.#5'USQ)'LvnglFe.rVo82~B56w'>,?c7-9v~3m&&d~VzDl:=%FJ|uA1","LPj=wdbXq}UQAe1vwQp)zJ+UcE(^7?nrIE?Wnj9d+{;Xt^[,)24heYLd*E-J~2-E","@qF5z%M[hPh(k['|;Yl5y!eASi=12Gk$I2>24>_/Cc[fX[-6Kx]ZNak'9:U[ei`*","3!l3TM'/v{|Nyp"],
  w 31 16 0 770000 770320 30 1017 ["(TZ-hS89c!K?e840JVqM2n.v8U0m]^[Td+P1G~?w0<R.IwN~Gw$f>_E,$4Ci/&XE",")d=&iSxN${DbLPA}*[C4N7+0S6m*BE`'zvgawGW<yT<x>FXW5]ArB+'|Ep+s.Eak","&&dtE0H>pR([}~J${!<3YZ^P4%/~#exq,A'<`[bzi5_-#v-$1l2rYXk@,"],
  w 31 15 0 780000 780320 27 879 ["fh/Wx'd!D56Y.R&+>RW38D8?Uw,{'Y^hIYL[v$~R$9F[`O>lFE6RNr&#q%fgO(YJ","n46|#.%17k!{!#+#3hM2vM^o/uI!QkD/c`?Hk|.UF{WgH.z;?FSHH!]+5li-ygm3","0a/7E*C*WjzO~u.i`I;OlffDbpot!wEw`5&FICykI"],
  w 31 14 0 790000 790257 24 746 ["R#n%wyK~6x1sn/RMk7m?>4cDrtWb*2TQh)!eK)tmoyxyo57K]?lw]PbG<33b{F3Q","/'p(aMS<7p.7_[:;Mh~>O,_S9drRV.OK4{~Mg<=SjU^N6+?ak.[OosR~fy=<Ug|%","$VxR<R,V2^wx|N[fe(-[{Q>u"]]

private def r31_17 : List (Chunk 31) := [
  w 31 13 0 800000 800256 21 624 ["aUP>k6N,UnD}oVy0<kPN<,O+$9RB}O%Va]{zL#WQ;5LYFa%W@n-#/&`&7a5g453c","ZUq<;>GK(K+'EsXyWjx$qP]oFf/M9Up<RBnDQfot2m3l96=z`ja&7L``Bh}*gEw/","&h#wt"],
  w 31 12 0 810000 810256 19 541 ["cHRDwh4F>?0:D:f71}#E`lJm#dX50E*5hTN-H|W<0y}4zb5o)^|u%1bAO#*oV/H5","&fKR`1CM:`dJzbd.t?A=L_.1mkL_0$I:;SmMtEn45AL-M.<mb3fJEa7"],
  w 31 11 0 820000 820193 16 435 ["FV$FpT2FFLz6V<+z?DN?H55<n(et'pAv/?eO@$nA$E@4M>~i8m34(t94XL0-K,H'","f5B3%*}9&,|xkm^f!Ul9f7u=G@aHlq>8OrBum"],
  w 31 10 0 830000 830192 14 363 [")XbeEuGzB-!O)JJ|=NAc]e)7>c%@:<s,SsX?vVK1N}Iu>?s/IAe06G+Zh%BkMozk","5T[!UwN'72n073dBinmGP?ie0"]]

private def r31_18 : List (Chunk 31) := [
  w 31 9 0 840000 840192 12 299 ["J#q|Qj&Q^Be]>We&p]'{Lm?o5m92l)hzUa#8/-u&?b:tCZU4aEbP7O%]DinHziDN","$n.{&:Q7j"],
  w 31 8 0 850000 850129 10 237 ["']1IsOciUc@B%/_M'zag'n|^L>i5}>~%3XZ%3tICko:sr2]N$x)S{y&-n8l2z#"],
  w 31 7 0 860000 860128 8 181 ["#]gTNa4;J1{%ih0[v^|)|,W^-;4J@w)WUu<KuEs)ah#;18o)[;"],
  w 31 6 0 870000 870128 7 151 [",Sl'kE1qI(UX!XrKT*VGgRx,`z^4@-n3f=B9]pb.&"]]

private def r31_19 : List (Chunk 31) := [
  w 31 5 0 880000 880065 5 102 ["(pvGDj]mv7TNii0G5B358cI02ZQQS"],
  w 31 4 0 890000 890064 4 77 ["sH,>6*thT@tR=!</a?MdATuO"],
  w 31 3 0 900000 900064 3 55 ["(0bD^@3aUQdU4&ZE"],
  w 31 2 0 910000 910001 2 34 ["#YGuRRb@Zj!6"]]

private def r31_20 : List (Chunk 31) := [
  w 31 1 0 920000 920000 1 16 ["+eQj1"],
  w 31 0 0 930000 930000 1 15 ["}uUOI"]]
private def chunks31:List (Chunk 31):=r31_0 ++ r31_1 ++ r31_2 ++ r31_3 ++ r31_4 ++ r31_5 ++ r31_6 ++ r31_7 ++ r31_8 ++ r31_9 ++ r31_10 ++ r31_11 ++ r31_12 ++ r31_13 ++ r31_14 ++ r31_15 ++ r31_16 ++ r31_17 ++ r31_18 ++ r31_19 ++ r31_20
def rows31:=rowsFrom chunks31

theorem good31 : ∀ r ∈ rows31,good 31 r=true:=rowsFrom_good chunks31

theorem sorted31 : rows31.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks31 0 (by decide +kernel)).1

theorem mass31 (i : Fin 57) :
    bandCount 31 (i.val:ℤ) 56 14≤(rows31.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks31).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 31 (j:ℤ) 56 14≤mass j chunks31))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total31 : (rows31.map (price 31)).sum = 299265 :=
  (total_eq chunks31).trans (by decide +kernel)



private def r32_0 : List (Chunk 32) := [
  w 32 56 0 400024 400777 100 9845 [],
  w 32 56 100 400778 400903 18 1712 [],
  w 32 55 0 410023 410771 100 9589 ["F2!t%m:}7b:27c[xL+9D!yaz)7=hBe*(3'huc^e02Q:X.=oDa]6m3/NQP-eOZQs:","ll59T6Q9xTIfXLbq&jqrLL{^mO)3VH<{._%2zSi2.NLs5ZN|B0:Yc?]U&7t9q)K#","'DkUX)),r`RF2_Or18YHG3G^/T"],
  w 32 55 100 410772 410902 22 2024 [",[nD,9FE?G>D}O%jf]'E2m7%<'Re=A,91*Iw;"]]

private def r32_1 : List (Chunk 32) := [
  w 32 54 0 420022 420712 100 9378 ["zE/;i&RJ@-VSK8,I{d-*Xp~DTgg<t/rru_ixO|.gV<|E{$}v5j*wl#[!aZkT52~6","<@?cw}l~R&0eIqE-Egx0yRPD$^tCB5^I?_#c}H,,+.:jME-Uui4fecEJ'=&C<-n0","&t%9wsf=L*3CD|bTU_DrWl&{+0ZJCk'jBX>7T2{%N({$hT|0U[PJN"],
  w 32 54 100 420713 420902 27 2419 [".Lj(,CRY?,v*l;Dp!<~_MKIAY{[|mlTldhs_sd4j=f>GR's2>(R44w,C5P]"],
  w 32 53 0 430021 430707 100 9210 ["Xx{/>d9@N2'Y1+nPORJ<X8G,kcR*K]vO`L}?MaLPIH-vyb)rArHeo'7pJc$@;8Ag","kqX}Jf;5%$wX+07cMl0`7Yf#1pYkQ}s!2(},*nrRJZ6jREb-UM5>elH62)F7&lm{","P4hG@B&MYTbW>o}E/ItA-rtT<KP[a.8~JvM^<AAiomr/3f'.7IV/[w&t_${rNTab","'@&<cg+DdQtg6V9#-cvw`:Rv`J4K7smQBq>ZK"],
  w 32 53 100 430708 430901 30 2611 [".@s7TVXtD{dDw%`A?bv8|JVfhn.dJqrT8xo8z!yLc0Sd%la'd<{DDCu#V6/{I>,C","6d_]SaJ#IyRd*:'.m"]]

private def r32_2 : List (Chunk 32) := [
  w 32 52 0 440020 440649 100 9070 ["y*5K$zA*@SD$SH*H!qyXDv6FL5pf~Si+.jqb_hXu_=zEJG$*OSZ-bv`n-I!bbyC.","p%x-#.V^#)/Rs$,lI1:aIfIz<aMiy_J{*a9W`bW-gA8byE%xl7*%:|WS-AOG&'w@","HU+r.5v]O:@-Cb+0o}Pp~&le/;;'s!-eEr^;y7+'&41}SOV(uU1/H^@G;7qk@`Z&","b9c@-O~6V@(xG]waIYUwBU{dmSeyca&G]n=pM=]:DU04vR14[<>vY0^qq~WGUc<U",">Ujj80ju"],
  w 32 52 100 440650 440901 34 2894 ["Sk/<U_>Rj~21{lFTQn;VIS%(%'A%#T-sX6wI|9)gGxt'_{pl@%@0}`27z$$8kNa4","k$z@(>K[06eINMIG8C/^/h+I+InZ#z?m+j%}"],
  w 32 51 0 450019 450644 100 8957 ["*XDt70b@LL/#Dd*A<nC*$bn=74y#MQ6e}]kuZDoKv]B%O1CbfUl09E-xG%ujqqkk","Uctl=cyz7>&LQ:CK'LZbD-UCBB&BQtO-+t1@dw'wuWwN1E23+qbL',|]f4NZxS(4","v&`1{X&.FT#y~vs)yAX6,q3K}(IB0(tVEtIqz$x/sv[t/aeo9:e-Hw++Xrl6`8^T","8HAK2|IvlV|+wC2nKq.42Zf3&ffWL?7Y*zU>|KFKOog!5GlY7UyN{w27W^PAd9lb","$H&bTtWLo;/5##nX]VT&mD`MQ-`<Iy*T&2}hz"],
  w 32 51 100 450645 450900 36 2978 ["ISLh=qf{2p8^}y:'Ov7'2DCgs^Si&^]MQILJ8Yr.o$X';qB18T8=y$E9j#<^hec]","B6e7wav`YTk*Hn=qA{Khxjl6,b%iB0hD26'AB~Nr!6O}kL(py3b7C$"]]

private def r32_3 : List (Chunk 32) := [
  w 32 50 0 460018 460587 100 8834 ["T?ky^Id,ELLl,[e:3>@XOoL$O3`<8&#@Iu_WrE(,0#b%=mULvs{<SdowfBFzpHJ*","1gW<;fa?=eNvpGpOzLTTZNqiEZ;$ed$G]`'TiRPJ%>J%zJA|5J<T(6/ajCKHNdCM","77^`D@'IR,{9hH5'-(Kpe(qf'0e2_x|*{#jtM.3E{.2p'>y!b-F,UQl=9oIHFhNE","x}t.%TFRnu[1X4=&jV?pV_6SHEBlbG8Ji13%%y)no;r#^js[|/C>e<RP?JGKo;G7","zy.Rf#uu(JHID?vv)LYn^;gG(0%U@0g*~uW'S0N|YUt[uf$MeZu(66K|P,KN%)"],
  w 32 50 100 460640 460900 39 3172 ["nl-$_&N!>LdmO/t?%!`q=wOa~AjK{~X{hEHQ2K6#2V`iFr_A-R~+sU8uBjw-SS-p","J%UPm2%G@D/mm@|{N2'o!=vU?ne|]nAzabOah#}]:9l{%I/L41h^0b}';6F}6C8(","$bqgUCA"],
  w 32 49 0 470017 470583 100 8733 ["28*>&U:flUUejvcaK0v*xvmb0b%nX:qMr~Q3Ga{iWA{m7;!u/]Z43+YXwjkqmey!","9jP/Y.c3OobjYqL(NL:yuu!9*Tjv/S%R262rHqTsp(P;sNg<T$yq8rsLGW^via84","eKY9C1;}Z>gHld>~mzVQDckV1`~[E5r<G-yj2^x-QU#^INw~Z-I_Utg{3q]qb<?]","&R@W=B^T8V`R*=;%VF*)bbFn{=&_h_>~k(3+50rQDwU<`)fe1<&u4OcR#vXM7cis","BtJI^I+!%lkD#Y3Bjq2iKfey1TMnByxcFQAU]JPYyIUqrQO5w9H^$B*N]uZN^4A<","40zCaQJS!l(%if"],
  w 32 49 100 470584 470899 40 3164 ["tP0.f(DD1<lA`eS[f~:)^C!${#iF[rdH_pPqpZtnB<eT;Oi'Og;r^w1BB,`-H|}>",".m&E__Wzg9u9AW)%:R@o_a`{^i>~~{i5?D@^Q)rNIL$@p+cU<B*O.mmC4xNpY*gX","0;|X'PO54iW@lZ+H*s$"]]

private def r32_4 : List (Chunk 32) := [
  w 32 48 0 480016 480578 100 8635 ["_s&!P;JU@u(_y)S(!bd<IBScO<F'w!)0Va#d&w`*_=O%+t?Wg*}Ij$u/,Wum8PnV","L.X*9G$B_Jkhl9bL9.kY~VCOB4#6iVy^JP3Y@:Ny~45K9L(bv#}]|4-%QQwTRV.%",".s}yKSf$4aJ%DjNgc>504}EK+V')HmfPP#%rcCh]Iw![DdG_Hav1uYi<`]0NORDy","YpKI9Fzf+Qp$/7;kQ5bzqYg}V=$HxnA*=T6*VY#8cF))?-,aX*4,85KyHpo3gp-y","X{{%1nB[8Kw$I&CK_5LWxUQGtM:*q*5T4$8QE1TyxwQ8n%t8:5=xh2-C5DhH,,Y1","Q8A+POO1%"],
  w 32 48 100 480579 480899 42 3248 ["_pw%L:+~9qzw96fQ;q4lT#|7sN84DRHp>7aW1L[nChdbj[qO[mG^XA/~Sa'%Q(hI","z4'p!vcK-TfFch^f'h4=MSV8=#0]rJr36N$rzZMZIG[z]w`=TEHfW1~`'ShaqkGj","#Rl&<Kb9f)Aa@Bp+TUp$6-h(#t]K]XpIJ):Uc_"],
  w 32 47 0 490015 490523 100 8494 ["T@yp&(vQq_|AahbN@%$vz0$%O$s4Uxp%ZI5*q+odMUo~i{mK7d*=C$xF-X|V<e$R","R~lW?H7k86T.U?v:JN{B^lji(=~cpFJ#kwLg^2B7)7lspN|?b)R?t!e~Qv::L=gI",",3~nZ*|ZDNaN)YWxeTpdk~:;3n3rBgh]W.K=U&^_C82)UA1+7F{C`MM@GlF>aVsu","mF%k-^euBtkIt+`Go7^A$ulN!q5fQt;$$$Ux/%SFI_#4|Kj%3ImsH7Bsv6*-*ro~","KpD6M&Ly*mCU[l3B547,~?2&</m1O3M>8I!AKE262$-]Jkmx}Uc-+q48t+*|U.R,",")-`Bs4e3L)dM"],
  w 32 47 100 490576 490898 42 3200 ["XQOeOW.dTYCw_]4R$(MWW]#G#:U;whWta/ePF0Qq+~HBA5$W]1.QJM8w+d!?=blG","*D]!tQYXv%Mo-JyG8OKj$(4:F+S'2lVv3HCFo=j<};`,4#z;O'TlOBwSl/vMAjv?","%:ohTCCrT#a;&o|*45/&Z<.qln?3wQ<>GnZElD:5nR'Vz{"]]

private def r32_5 : List (Chunk 32) := [
  w 32 46 0 500014 500519 100 8406 ["$-fTs'M}%Q8MPv:$@3+6=$YZ7DanGD,/d?63{LR@Q=sf7O)3&MB;V<}AOy@{rKJ{","Du:vQoqPALirI|.3f_'8^=!Je+Q@:g=z;{-o1UdENzBCoeg|o9yaAB)5]PxA[QU_","u3xp$gq6+VRSX]d<!V|RhKZp6,N|Cp@RD$K+OKoV%64H4SZ,lMxN;NHv}dBOBHEu",";q&5Zk58fxVOJ(sEqv!SaD+&bi8>-],Bwu$>?]HLem3A~U73.7MHzuWE;pagu?<:","n>l<55wrGt7K,=<3nEAcxF>F90*2C1c;xh;Bl@{By!ozIz-'&.7Nn]>71k`D?T/q","kGWG"],
  w 32 46 100 500520 500898 43 3189 ["L>uhf@R{U3AU0m%B_JYr4R:05y@|QX?wbw{qd8g<((a(y-o/]pYW=rqX9/,k?6S!","0W9X|b^0WD;_H0Ix9!#wdQ7H;X%N2~@SBUMLV/9*RTT*DS2##>Rg<ibH^HR?M23F","~6kiV7ai<+tS>G<{4Hz]9W;CE3+U+`gT4s>L>;Guy1Y_WX%e,QM@LWi4"],
  w 32 45 0 510013 510516 100 8289 ["FFi(R.;##7W{ro4hyiC#Cq8bpwqQa=ZJ9Js0l8Fc>&Lysxi6zlhx+yHu$_vL|nnF","i#=BXl-Y{U.F%%r'{<$ObD,X*%E[@l)D,r(S~}=AAA(vX)E{AOCwj)H92&DaQ8PM","2Rx|LjQ.u,&=iVy@1nCgRhRa{}i-^10`.qbDW=U)K4`IL9Xo1zwtrp*PB9z$+=Ky","}x.k-pF&Rh2Ez@/z.~6kvl0,}QA8oq%z]Uv@}Axd.r$(%;l*?W+84aMF|iN<-9:j",".vqis~Gvz_~dn.F=1tkvi`D0hFdWV/L$-dv#]puM;W&X5xP`l}N~J1CXRG[#p;sI","-)Sg/Gj"],
  w 32 45 100 510517 510897 42 3038 [")>2$e@`j%F/{d3$=z(Tw-!Ph!Vw^-*RuHpbsAE1J?h9ipKHZB@=d<t3mc4lTlx$v","$D6lVlGbXEEVM6q`k$3$cA?hCL@2wYbq9wMh;0!TW@tT}2[[`&cVF$3jY~h$=jF%",",nQHLZ`hvfoX+[ilp?&r?p3Lcu#uk2^mD$G2B*IVPgCX4]/#8@f!a<to=}"]]

private def r32_6 : List (Chunk 32) := [
  w 32 44 0 520012 520513 100 8170 ["8f^n$RTsCHHRr!:/eF'9i%<-(J(Wul!`MT|druR1xt'ebmu#=ax-,7p{_b/N?Ok:","C*_QXM1|8hRdus{hiLM^1gIo{@G=sKdlu,TS&QN86r]tm6,T]PUG*74Y{]`q)/>&","7/66p(wF/<SD:3bm!@@'kSFUBES:Uzw;3r2=/hc|6z!NzOf~AZSS{O=dpeH'9[%>","9.V>Gtg[>MbWS5at)@[>u+P,/1[+;<F@*xdm7V14#|I-;H6*8xpA,QPe'%uYoSw,","dYy7zcV*`;5C(w4d+5!yKa4M;'nm9HcQ%GMdMJblPAPO-g`)gUMO`B)=+SjzSiT"],
  w 32 44 100 520514 520897 42 2977 ["eq(MY>o7D_(J%U&cH;k|~o^Uey`fI.wn'l%0?X[-_U0}yyX#1}==U>T@bpRu>YCi","'Wb%#SUs)5Yb/gTjI!'Zj9j&Cc~b/|'LI@:<37umr!=;B}`;F;-79qcw{8ZJ>qd<","%4k#+yfV3h>i5uLh:$j2t1g*B5fpw8@3bn;N)JYfCGi:'VtbichT8='1(DvA"],
  w 32 43 0 530011 530459 100 8019 ["$kVnYv/qgCQ{%s$+_s<QEukhs$C[8IXG|lVM_]m75,`75bI<}Y&;`gWFp=*1'|w*","'EcR9B|q&N^'itH|Yp#.NG7,=](6Ecs{+lYiS_9@ErL|1uO4lhP/<:rX7O(/c>wo","|3@wGSl#H@#U^>V=pn`@zt{AjRt67.7n`.XJ#n:Kk~MfwB&Ev8_ZBUv}?+eBJ]WY","8AVmw]bd^#(%:o-tQxWu86|0zh)6dgNQ.G37@F=8GkqpjI%6$D3MM]<;mnN5*swn","K;$r/7a$3%yCmzjXW#2/POC3n0Ap{7>R^LIE3lWM3%eBFsnseHpqiM^`Ly_g*G!.",",z&ngMe"],
  w 32 43 100 530512 530896 40 2786 ["#$#=[u^x=k~aMSFdB}n!2EaaB&/N<1=R5.j?eRWi@A%ncZ:6O,kVA^r,_{ob8SOy","D>c=hV1j*}_?oEdTpg7bUfJ*d5)WqN~!j0ZcrO-}F#I>EDk`L=VDI%L]Nvhwj$>C","1_1)8g{?s#&E^;HfY:|#JV3`e9(R%7)jF;I.U!p$N%}HUJ8s_w1xOo^P5"]]

private def r32_7 : List (Chunk 32) := [
  w 32 42 0 540010 540456 100 7908 ["QECry[f;qq7VCy5Hqdig5&VU&Ur8_V,x0K!L=iNovfA6#C=-UbY)>7vClFc;i3y2","jp[E?H,/aj)jHxkY<gjf3B:DeJZYnC$7~8)ikq$o{vq+_,^jKWASYTy{'xgB{[yT","g6NidO6/-f]ThkO;8_EHaD!$5T,|^}-hGg-NXtQl<h|z^gSp,o,E4qD>5&qO!Nu2","e=-dXx05}9WU_T0jc`7MU@@20rAE?-dtQWm%/fK*=~$L}mtA;TdgpgR|<q7T3lCe","1>]F1[.%3S9rbsj,zE9$xew3OUbJZ1+kh47cmg[@Z>hJ%sy>of~^xE&+45^!p`rF",",%|hbVS0"],
  w 32 42 100 540457 540896 39 2644 ["`9vKnTF|Q7B3/)k3|a=@X+n33tlR:.GdZy[t-|I1!SZIULEhOS'1RQ2f7S2,3,6-","xXf2d*i=IdLUjFG.<PaIwI]oMU3'wpwzlS,#76QY+rRxQn-71D}ExRNc%8H]`K?Y","&Fs=@uaW/a$D7-QcK;%>*~8}HdeeSIa-SBCwnx{&l0*|V:|a@3"],
  w 32 41 0 550009 550455 100 7763 ["MBg*hhN<Im;Q>L1im&8(67lGzB>#n2xqz;YLW:DJpB>^xK{_:6rF-urE)I~eFauR","2?9+57sAsZMb!f*[cQ{kzq;$>7!R,5p{OXf7/5%1qNNY3!lnFHx4N|L=B#[eR9Hy","iOVPN=?Tap9$5/&dlMJ~=.Jq=}HwQ~tmXL5O&2-m|<D^q5#8NVHxQ<WCt5Tmyr5t","nZC@Eh*~}@iS0pO>~CO5#&CG6:4CN@v^wyyc|H959mg-:[f5j3q/b5g/-jhuG2vG","U~/txCeQAx!6=I,_z&qSwA6wji=*N2/K+x7'1%{Sg3VyRr_-)c.#]4)T3p]-]pD5","#8lxL^"],
  w 32 41 100 550456 550833 36 2378 ["D,tPw667eSMb8t<`JoXv=_fHBio&mD2V/WCk2zMPKr-*P76xwdKQl_-5?8~X=@zB","nf&W=bP]YVhoT*61m%Nw?]iO2'J>J_T5Sur^XcJF(t,)-evq@kb=iPrVlS+#Xa+j","$`OP*.?g4KNH8?3QP{)KKTO/X$}A-AEq^a8w4BSB9]B`.sV"]]

private def r32_8 : List (Chunk 32) := [
  w 32 40 0 560008 560453 100 7631 ["N6?-ltIpQg|<OYCE`9d4H`9m-cBX=He7?7w@9;>XWfc%^z+H}I7!F@n`HRpg^V`>","c:]m4.|?DDgyW=2}QexI-^>2V`etX6af~*]rR<>g].Y-;.k].@>3uU]HUk8Ey1vG","YsxYIPCMQLDBRwq-T,i<$y'zu4=#BZ~Idn}7Iz8t[{*jAmR19|CYfM7Q&{z+$K+=","'rd9O4<uV~Oth.a]3WpyYl8xBR(jeI-vt'dqBVV+w-TzEF*j2k9v,,)Uqf$.rQ[A","@/]6D_EUJ!c`[e@V8us&O0BFU+a?:#,LnWn81pOV_T6~Am@rbU~k9S{Go?7xq}j3","--&/$G4rnFeHh"],
  w 32 40 100 560454 560832 34 2189 ["`idH#c6'kv*3W={#LV''O.X#IwQaVPv:F.MC4A|-]^y49T+xUUC@/Vo5_)t!}Z06","58GV/,uD{o.Nip4nl5/xY*`uf[-~y`w:,YD[H6^q9wJ%j#L|+G#mDf)R&2o%:R,c","7vKqP}PEIZ!Ws,yxCb7hz$O<:{P_Ox#*$TGj9"],
  w 32 39 0 570007 570453 100 7463 ["`k(N|Q9;ao^f`(WPPufRkY'<AtT1u6n`+OM$ivb%=Kx8^`!X]5'k%C|TqMd:b=_*","b*Tdfzq^/k!jKfQ`&[?Q23EbVMG/@JP}+*{vvP0LruCo@v]xl+WU*uD7$,vLT[,0","|?'g+I0@xQShh,W0J.P4jH!vLCZ0Ev`yPD:&O.4?Rhrm,UDGxEv1y2]MN^TPPg:%","G]eG;cU%31`$5Aq)v~RL8:d9O2^$W/-Hd}rl5I^Nx4OwD@twEStHL>q2j,b|W<-]",":q@oWq(12U'MLPW}}#-`mUaiorieW'=S$~Y;b0nqgPkOv*lx%gxn.Qi1~;vkXlEt","(Xu^%WolIIxa,"],
  w 32 39 100 570454 570832 31 1951 ["@m+{ghBC?r?1`V<oOT%NK}KG]gmU2;|-Il,wJKD^'C*O:`[weTX2P'C(,LI_^z6^","Lc(?In;2&PRt)RUO0GDtD+OHvlVu>Dx[Hx$;vS<()PJL18g>&2F-Z8o}'MD*B.:A","#q<YCdRUY{V%e~;Pa_2o5mg_vF;Pjk"]]

private def r32_9 : List (Chunk 32) := [
  w 32 38 0 580006 580452 100 7308 ["^=/yR]W[k&|3d4c<LI2oh`e3L2@Ld$7Y7Ti1i0V+&3QnkeHW'Sl.[5+57;K?EI]!","FMN@~8lI*KDu=$Hb<p9_1?*kF)aHfW-@yLL)W'a,florLT_}(TE*J%08KZn{@a57","$TL(]ZF1A{XgDg*i0%lO.8(k;fn%-QFQ>%%3@4s4*UmMOW@Bb}V?}@lA0^,bBu(j","CK~Cx87cW1m^LN[mk9ZA^x!pZ/}NKxnh29:<@:V*~JK<AeghB|RRTLf)bFQU+t,l","`RoO%j%j#,7n^U?Rg}1;C8J`f*!-{]>/M;SOt:+o{yP*`[7P_o`&hKI?a4ooSnK;","*+xvgaIFUPJ_^kft*ridOl-*"],
  w 32 38 100 580453 580769 28 1720 ["O`{qlMYNi!A;1?-e?x;Et&x[M%/Z%R4Q|$igTXec!e(Kbo]JIMbvf!mt'm9#`&.U","y]gXx!){>mK@1G1BA+O2SqN<7hN02O6um'x;8ub4[-)Jmu!UJL8]l7A_$+)<<msl",";3&XSVi]rS'aoI"],
  w 32 37 0 590005 590453 100 7115 ["e:kUk7W}6A!iG02#Du|WaSAFukMim-N%vqlxQWB'tFo!!WSiQ75G`&6'45U/zcck","2b72L[SUC5,$kcvgL0w3c3]O>yLf}o@_7$+G,=41[`G+C@QEi6j]dhnk)=|0=ptj","X2KX}y7A;l]O66wYwbj.Y:*kcj7Ej*)s:<NMLF4XWiW!NC_uGw0=fJUy0(;5.lAT","Q1(S=v!z`gqvCLJirE07sd:THww]b--,D+Ev&wTP$`goK[bz:hn-^^_E/1%-9n:^","=`bmZ!X9sc)1g>D)9p1kX+N/d?6!*_bkOCy]aCa#PwL't&GR<{7W8N9bWx_<2=xr","UeoLkN9w6qntq:!~3^z9:;>u`z'dIT"],
  w 32 37 100 590454 590768 24 1446 ["-T,}{fnbTs%*vGN3,6Q'`Gs4I?um34Rx3+2uKyy{$YW+6N-IxvQGRKLTLVv#+wp{","&x0vx%g&l&^A8if~%n|~1ns?yK&5)?m#6&H&Jq%+L5e`1O+VgQR!UL)e9?,3QO0"]]

private def r32_10 : List (Chunk 32) := [
  w 32 36 0 600004 600453 100 6939 ["TC[f]$jyl/xwMj_'_!:DKsu@5pk!YN(H~|Gh{|ADN&lbz33PC_P|=,Q{fbjv1#(2","&C]yvft$n7a*h2W)w2.qU>6T,B#QQ9`9CAPL?dMt>$ab>qu(AFpb#`F>vZLjq|dD","n2~}@f8gYWjaK>Q4A83]{UcRkL$3#M50RY2LqgUWNQ=:@8~E80{*nnQ3NDw`A`Y&","Sw[.1pPc-ln/Y52<L(TdbrLpMN6_o2u}Z=oeQO%_k<PWd;Yt*zo1wWM?k{b;%7!D","xU}`OA|>a6nB.4pYS.-9|pk`.R:qBofGJ)8<D[';9M[8{L`?.manRnTeF#g23LVg","#p{2%Oh%PW;@S&1YJJDMIR@[EdP1}:hu;3Qh.N&c+Vn"],
  w 32 36 100 600454 600768 21 1241 ["!`|R>lmGQJ&D4>a*^TBQiAN`LA!B2dJck=.R)m%0za,552BS,$~VZ{m{L^tW7L:&","#daC}k|1umR9w)D-x3@j?kuR[b;V_vVi_v9qh$*MrCCHu"],
  w 32 35 0 610003 610455 100 6726 ["5[UnzBS$Slu)<'H?_HQO~QCwy>tQL)w,[ALnUL6H{dP}_sz.],Hk+F)dw:%(4T_{","L}K'DaLrlPW6vUZO-qkfFybj9o%D`Ehdy-4Ki]8MmKUu{1h~d}Qw@2@I|d+USg7)","G_fZ/V:F%}/8_(Bgbpy:%H{Ixr9>:Dh<EZc~xaqAsn_o.zr;_@-xN*~]8L!%s4Mt","ym7xsb+Y&y$ccM?D|Kk+ej,/pb'W%|He?9_v.v{I7knSC*)1dken:vuJ$ON%6a.{","G,<22!/56^V{}nrvU6njZy88~H!a1nKslb`69j1`9<]3S>zWrD};J*6hzj^R9{vp","&3;df-3$0(nIx!Zb6@+-1O^,z}i?(ttx}ABzNllg+^xq?cX+wo"],
  w 32 35 100 610512 610705 16 929 ["th<!@mt6URT9'B+I*7Lqgi3e`Pdk1bYWHoSFofR)~s!?4L`@7'YaYJBaha(pp]%9","#yX*#d-t&t^{,hGg-g_T"]]

private def r32_11 : List (Chunk 32) := [
  w 32 34 0 620002 620513 100 6532 ["mIH0~y~u{!!3>{QJdj5?@{<&B^Q87y;v.(8LB#j3tewmfx`fYp8cAE3.pBg*j%FJ","PTGI`eC!7]6B]KX]ObJ-3l5x`@%'w55'[P)+a1yrfN^OcZO,kx_NM4H_1t`=@7xN",":J+']I;x(N%w4r[aF.Y)Vs@L5ML3G-{L@WW4^t9tx!P$Lx]Vb^]|sJmBYu/D!i^L","M5GgCcKWREXKs8~}Hrp&6[r64t21u4+w~q`w_`|~Ayk:8*IXwdK;.>P#u<yOr+Yt",":vg3Um>Re;0K6[<|p9CiuX~R:[sHRi{N<v3}c>NU98`)L$`ic68('.F_p'pqQ}jR","ixA~K[IRXOl)%7@NwHCq#2?l^jNiE4VV%3E`GmXgLqgfp]~M:qN|(ZRTV39y#kxG","QAKxA6`2Kg"],
  w 32 34 100 620514 620704 12 685 ["$d%)D8I}zA;ZZ**7CH5<fAOA)V6Lj<x#g#pPe=SxfV-u8Pw[b%'NXy%nZlt{"],
  w 32 33 0 630001 630516 100 6305 ["YNSuj3OF)~BFTi,q=L]LBY]$YH;C9)7cM6q%j,o-Qd#/qI1}Tz&h'plP@k=gHG)V","OP2:f1AdM`,7:zgP|Yi@)WmbW)cGgKz1j/LQ#'_+zgyY)_F8N5LnW&gM[9b];YN.","v!!%hG$PR*'O:Co]|Ft_G0[,LG|>`-(PYk+?Py<sAs:8BM|[V-YwiNNK3b,0~)Y8","[wwN8<b7%(>OD=XZ(5N:gtGt-q5IIl}`d5VC?6C''a#^!6Z2u];^C]O&n9~U0INh","zwrYfqONn3hefX=uNMj&iE'T7cw_dPD0qm}'o(+C,{3<&m+m$.G>OdO0[l8b,Xj.","pix4p'+^YDIua]%V3t)@<9Ln#NcBukQizeHiLi{[J]Kz77v3DczjBbscOW_TkprN","D^V=FfdJO&xLAHc.t}m8"],
  w 32 33 100 630576 630704 7 396 ["L%VurKRPOlU'#Ss&3tlwtKFaXqwOE)M+Ehk"]]

private def r32_12 : List (Chunk 32) := [
  w 32 32 0 640000 640578 100 6095 ["2gVU/u'9bVsV0.i'1>VGz@Y>qQL+)dtarA|dBgML&FMZ!&AJ@8Ae')(bm*m+C[Fk","bI+|oug~?=da{vvwRU+K{Jnt-1B`bD%^wJOmxK-HPfUbQXq}CRQy4aJC[+#mz$gp","tkF?d@Q:w}Ym'k68J0(qM^JxyOq74FlC;lCz4[gw7E0Pq[%At}KZQ&NK{Ny~7Cyw","?,Nl!YikMpnA)/p_s!;}H~#ev8R0Gj^fEx(nDD{Pp(.cy?:k@->Odq:%Ge7T>,Wo","GBQbv&61~8JB@E;ERJrzQMa%6zmhv5]pGk7m9M<||!Z;8ut`-4qdKMpCYAd(iLEZ","rZz,7honYZ}`j4s%8~`neI(X0d(fg2)nA#r|?aEd2HYN|<9dJB/y`0Os-]@o:@3-","%nZ`]NO_%&x,P*HtEl)sOpyB<(s$7]!}"],
  w 32 32 100 640640 640641 2 112 [".rFvs_3OJ5"],
  w 32 31 0 650000 650640 96 5643 ["<0`[<#&fnDeijLw]Qk@BkrzuprC}I%{6^qrQ_(=><K_SEw=>}^{(U-md},7bh[8|",",+)A!R4H?{A'k52#jFiX-R}'fz<w7@NK~?VXUvX=`vzF(1u~AVz$atzb{g0C'9A(","s<Tm>Q:K##*2H,d)!3Va9N<gah4a5B/;[+{GXZr8x)d6n)2jUtJIzZa~yt^V4zHa","PxDuwBx>=Pd.?w81gk)G9Bi08CvK):OG=nN{t(ex-`a?&_8i&q;-+PT@*UjB_)Pa","gLkR8d01j{d#G.uph68Nagc4*qBB?p>]7&KPFj&TzhRi$!nO$Ml<+HO[YFQJ=LOv","S+xKaKiL|'PLWNh?[nzF)C$bW7v:jwc!j0VE}k'Z1B'c4lTM?-h&zRE;Oq4u)a=i","c(p)H)U$m8yDk2^v/VMdX4c!/QzoYzP}l]"],
  w 32 30 0 660000 660640 91 5157 [">`5Gz4%cV;J?uw<Xf6*F%.JpS2RS&Vimlw3KL/#$cD=s^2M}^z]U$SH?df<t|;j`","<lGtn43&-+icO%`>X<LZAdnt;(`='|LW}++[*%zZlr3Vh[]n7P#Oy%w>YuFK6Ki@","c8ryBHu?_WIo<U+XHb=lD9WL_qZ@83@6*z:F&g1P,L/Iy!5BUa|H<FeJ+9Z%fn^j","LAp85kKo;y~}DeD@zTZDgW1#.67vupaL~z%aE*B1,'l*hzrN9)4vPT)1JUiaG&Sh","je%FO<[GL]{1hhO_)d{6+G^EVpTBWl15j9*%?v!MPvy8GRT0sZ8ff3nOB)LGrB:W","$sA6W?fO>S&!$Q)KYd,1;}/$m{`msn3KctS.t3~5O7}Q:C$I60VgbT{^<x-T.4b(","$#Fy#Fj/?F)]{A+;`6utY(&$"]]

private def r32_13 : List (Chunk 32) := [
  w 32 29 0 670000 670577 85 4646 ["Y>BW.I_7`!.%SsADY4H?6JQqk8uhyP!N$tBk?H$.BT]jHvA4vwU38#,v=q/xl0k3","v0nrq](Z##6$iX?5ZX[]I}uO.R]OmNB5bjY)>Zk15dY&XdH'A7fR1Rivqkbiuvz=","Aqng2NF0v3D:<q$Z~;u&I3A:,;<+3##F=z>u@7op<nN<frl$%oc765J1Z~o=*7z|","l~=<:DBF)tP|/LyQdLbFgYvLIFZ%A>zBnhB(?nd!16QMs@V0fJd]k>z}k+Sr4H>0","}sW83O5{VqVAR;Z'2BrElVmP.Y#2,8^N;]LTq'F-mo].,e8F_'=1+Y/RI5caF;^|","f}#I|o)PJ0A0]oM@<$PQ5s-91XcM.d,A0HW~2FfkG>|ajrSw&;rp@?QlB83^YCW{","%@J@<^"],
  w 32 28 0 680000 680576 80 4214 ["[Dkg=o}r*lcNx=6x),H>0$v$F,=i3:o7dhz=_;^VLT&wf(DEn8MZ.dqZex^3Fq*t",">AI<bvJU7uh!CGg[OX)Zk>B'W>=5_>jcN(havip!IR?oQ.)j}KK8/L=/EQli5D|}","CPN!4I2)Ett:w!;Rco<^vOq*u'=!yz!/%vfrCbyJB?vnq,W+GRii_:;q]NB/*g2h","Jg/N;UPv/EtEl)g@}5Mk%{]Mw;N{mPjf}w!RwgpSv0|qyvfx19PQ;ONG+/kJotSl","9R[W94RmSLDY[l#:J@;u?rE$^cL-a`p3<GD*#YlLOIy=uw@fV<#T$A4|fp22nme7","9lNBD2Qc5;q[<cN^%^5m&4~oloQd,Lp.BHj3/(V$5-CMm<bm/Pd9Xs;f<FPc,o4s","#2F"],
  w 32 27 0 690000 690576 75 3809 ["[DF=$/0jyVp:0JYik&NsCaa%<OCjUh;S2%}2/Jz1%E)AcLKcVHGIOOeZ[elvWLT[",">oS:K)PPTViM63>/x1d{/P>F.+Ho+co[E)rd#4'zMLAv-L}[e~},{B8H)FaLW/Xy","6M^q>yPq<HHTRbm(p,dfywLL%7Ep2|s4hE[s}']]IgA&S1:}.ftO*JFK&cuR8opZ","(}VA1+@O$h!4kgVsl$'L1]OU0Oiebh[UHKLw`4)T|@Cp}]XC{g=2=Ze@ER;]A75A","r5:UK3Yb%VWU)IRE,&fgF>NnHSU>V)R+<+t@a&uT!S^f%r)IJ])(9sFK>Koeu:J<","&}L{*i}8<Tq!pmcuWgiXx_8?q'7EmtA}X9`BqB_[<wxo)nMudXPfT.Ql"],
  w 32 26 0 700000 700513 70 3419 ["C[n&4p}y:kjpeq]ij+8[^OF'[6;Tc_e?yuY{5}75r89oP+84=)J>j&cXiP9PkX&d","+AxNp=ki~g4vq.FyY;7N7[wh,*`2^7E'|MB7_<A|b$bEvtMAp1kYu]m;{-m(/GR(","%rL%=}.v$B_JjKS/ksW-8YKh-7-i^e#S?(EZMOa]5gA}+Fok..v,`4|R8pTgy5DH",":0T*^;_[buAy:,DSuL>tE[7Kb2.(F)_c_0K)$vu4D,qLG*DE)JKAr}qYUdA;c9Bx","@>j3M=8hB$2X=b8T,]PyN'f%0!$d}&Y;PW`qaHY;7)Yp;M?f<mjF^}1*?J)so3>9","$*Kw.<s$zd:mz;z5TfjVA2=bSR:uoPldO.!"]]

private def r32_14 : List (Chunk 32) := [
  w 32 25 0 710000 710512 65 3059 ["R58.8i.]`^.w:azkr=X6sc$0;;m`cWZt&`5ruyU,dD,u+f1;1qiYks6LkM<7xw#W","(>^!CZgeWQzYC]<Q,.Z'U<7nmxemyz6kez(h'4)GW<gWSn1LgO.:](=`+!cdAyuJ","m+$6{(In|CPQ|Z;Stf<!fL0]W7%1!)8]${eE:MMUJ@-ZLE{9X5$%q%|Qt#@I6U0-","(&[]Qt41R5C^BG;Om*}b'~iiyYvH=1&xI._'QGRkQCS5/k,_Yj8!{Y$):un:UGD2","tSYy2uUuu[,Q4t~vMlhJ#c&4Zj7!'&2THr;J%j,g^yL2qa+V@~@9uuDY;xPorEI[","g)uPt/l__[NIW`*io5/=@v5STnQufe("],
  w 32 24 0 720000 720512 61 2759 ["mG<udQdQl&g:<{`o')$Xo*@d<?MlbJV[{Fsn&yV~{[~]9}|qx5`qHkC&YIv:`eyl","d>[ugQ2.uJTwwn|jY+qASfDHSH[`%>sz{mr1Beq/y=g1?94)c*lPxoH'u,7,l5A@","~v5%fp3&e.zQf{IZd>LR%U:-=fE4A)|_cP-cQu47ct0cARu(FYOKW-J%@m1rq+km","{*Up!U#Y-%TPcPf)*eQ|V{9=aiwGy[D6R&M{(5[Xz$-f2KX+]3`}e1)6U`i:<~q<","a0nXeYo!vk:|-7gw6{%]q8(Y]i>EF4qNW`,tOY9)4me&sU~hx5]z&y+6&Y|xN{RE","TO1eWqI=9gnD]&zM"],
  w 32 23 0 730000 730449 56 2434 ["N2F6=C*zPsscCw(.uBV7Z*m'c2;>;5Cz5VHdE(irQ<}SUdn/dIg^}:y<Zll@[asS","yJ;F>VUI?+`)TRl6a^#2Ev|fno0ptNHnpo{pEI9|xW;)h%K$P.e6lF#wLT*>uMrw","`E~%|[wZ]E6S|qolFC~jS&})wH1jFG,DFELbmzMC#1$bSVWKR^||z6vacHDa$<6&","yRF,L[U/qKV&Elqo~P:WX@#,aAD=VU[KPRx/ODmmoZi:|OVCDa:LO1@Lia%l%0?e","2-o.9`{F@jqOEE,t|.HmkEMDV!-5Tf{o:U4Ug!xMk[M3)>m>qG!#zQUb:.F"],
  w 32 22 0 740000 740448 52 2171 ["8bc+n(aq*v**tok3{DIx%)@/Nd[H{xvy[<+iY},<@:e@:gAse5Y6-+b:9w#,^W6t",">EoM1~sEb`T`:+!WiAWR!GV{UqkL2m=u@F^=P>c+sJyi'Lqm(bSH.5r07q^L|y9~","y{4|*cnLHmt}<1qO?TcK.ue6p^r$mW8in#h]5j$!CYfr6E9-+G9>L$'@?zDIs<0j","mCT#e$d_jy!8y;HN(Mi0Q:s-E2A67TMNf2}#h[C/EIe,M['20sD9a^(^N|'Drv]O","%9/XlXS5^D9Cjz#pW.W)S0=&>D~&2a<FA7'%q3K.Z)8?X10u"]]

private def r32_15 : List (Chunk 32) := [
  w 32 21 0 750000 750448 48 1926 ["G,f(:LICaVI%|c)ZGvS]Lt:CE`r2z})R`kWeZ':L92bTEn=0M86/cDG:f|+p|^'x","]NWFX~(=}}%`w'^m9PeQ03bngF&^ha$yy#*zD#VYiGGz6wE?z@DYmef/$C{>QnvW","(>ZJJ`VLc6-hzg<2j1^2o?&qNL/1*pg<wh2v:PWO9j,B&7mW:X]b()McuCkp`$y2","f3#wboN?B.a.7iNg+=g^0p[[:;JA05@=HCo&~m_^zkuM$TlV7mHEsgX'hdfIzlx!",".g4^ZRI$<zIW>`ODZ-ZeTpF9FOdVT"],
  w 32 20 0 760000 760385 44 1691 ["vUyZ8bI;Pkm$Hd7SPsn4{tYL#&x~b[>RFUA%aRx!CLFCm&xUUeurU-5.8mMO]m:t","a,fRRAKf#X+Kv9^2MN<qu^ztc>9(GM56G8L%Bv5ycy>e6HV/oX&;}p2cyg,a;M#W","MO0Wd{kd)|@|H)v8?.9H=s3fyF9vZIQ9CgbXIQ+k$&TR:g3D_71a`0F6`H::_`{y","<pE'<t%^rO5Pf<eP:T~2*)Pzwx~:}yUltuXi#mt{+gxuc+9IP36r5ykFzhy;DTcQ","#6@~n"],
  w 32 19 0 770000 770384 40 1477 ["vUDpwa161d{3p&`B-Lk'@<bSLZID5Cl=i}r8kC:DBWT&e>=hmg1XUI~rDSZ<uc}]","H=D9Y9!Iq'a'49-h%Cf$Wp?e_AFv8`8i@}Q@nx;,Z2pC0j*Pdxn=&USe]!9o+4Zd","C{jjujZD,,.3<n0l7m_IY6WStx9MF[sIoz._zYJq6dq)<|!Y2Eg5^=g_LKv_ZLZv","*.ugx&ROZo)G?Lq(o~H?&OTu5PIl@`+RR[vSXMk03kUzf8JZ}lz0ZsLL"],
  w 32 18 0 780000 780384 37 1310 ["yJD3qO4)%Kfdj;a-Ef!eB/T[gJH87rL3@xxrDmze!6~n1^9]yK:@v+|'lkKNkeSy","<mt&^I]uU>'$COXfwR>>?U86Z;^;`2h2?83VyBS<em<CiBqm53=RO#Bg[-[$_4!!",".J3mb1zOym5(|p405d@*MF+<kpmabc[z7&c{VkP1{i*jo6Dp;klyB9lWB%zY1%Z!","0+H8(-uI}v3Q]w?8+&F*kyU$ybw+>3J8c>"]]

private def r32_16 : List (Chunk 32) := [
  w 32 17 0 790000 790321 33 1119 ["MQ5}l(vxnHj*wFf6m>Z/oLk'2Z|80+TFkIzdAE<T=O]=*'j}7-YoB'V%p(/l'l0V","#ca884aSOEGBvIF;hYj3yj0uY|9eM&Kim{Vg1$v9vx@,@?uCOg:3iyN=z]gR(,`*","Om%eHfoGZq%amZ?Vxf<HW4RS-1QN'j$+IrCp^01gJsx'.lD$Cf0!n/XC7o2qE>th","g%Jupw=1Wl,^%y"],
  w 32 16 0 800000 800320 30 975 ["B:}(|(40~uo%i=${WhpEFn+tkK<{Vm/)X$N:NbiSOE]!{HTLTskHfebAGutp;Q>n","!>pVFY?#g-3$T5$3JIWkyxWB.dU-q1gd4m4`x0oH<c$!uW,$,gtS_#=7gp.<;=Xx","7hDS1)!YSNswm),Scsh5:t1cj$[c+6axxu?XR~GREd6#,npx21Ngrm;m>y<v"],
  w 32 15 0 810000 810320 27 842 ["`(]p?aeT%Vc,Rnl-U}.=@&P`Sp8Mng=t'RiehN<giBrWUw,RHZZKo*9+9z@s:qE:","s%y(va#r9nB`-VB#=V@~20B=>n][%6_L%qoZ}0Y!0gxA29#SQ?HO0+Ju,a&?o/;D",">M-LeTO=:JB&#FVGIcQcKqqa?lmIpW:!rqXtSdD*VR]"],
  w 32 14 0 820000 820257 24 714 ["W@5)oxAL,L++^/D]/gY}xr=#,9@h6/vN_A$^(ap!uDsgY/R)h7jXXVZ&<9QzvziU","8[O61_@`Fa{{j1R]c{05e3qOdm@g;rn$QW/JNZ55#_mYe3~:GHfPp{^4O0#//$+J","#@G+hS*7!?=9#W!7o=OQ8K"]]

private def r32_17 : List (Chunk 32) := [
  w 32 13 0 830000 830256 21 599 ["h|{[`0j&M3E!3u76j$fCls%7CN1BO|}!E<m@drHcv6z)Y%{n9;v4<TV^J5M%k&;s","CfP2nVp9ri|3xGu=)D5qtjHWbHJR58rkt7qa8Sc.F[*EcW:ieH;<;Ipv)|u$z{X0",";PbzN9&e"],
  w 32 12 0 840000 840256 19 519 ["=bOnnJ$f;B/n|aTLJDu%(.S!o`m1Ki:'rYX<-NK^QEPVgx`[M]s8[R~up2y{cUEk","I4'A0Zs'8Jfj4Z<<efy8h}'8W{oNXA(wid97uZ8xOiEZcgg&M-f6f"],
  w 32 11 0 850000 850193 16 417 ["&2#F+rW1]3Dti6dWdaaQcS2wJ3g[]/2Ohz.|^2lO01+dz!kZIR`ufYV:e<#yBvR>","$wqIV.&ayh^wKD8ZG5&8leDt6_rV>LR+]Dh|O:"],
  w 32 10 0 860000 860192 14 349 ["9A0ZI)Yr};M4tS{Q_:srhs6!p~/SbrIwOr;?zEDa{j?%=@Qv)Po$/%ahK,)Og0TO","#h*}tNl,OMj0^,i's7lz.$0O"]]

private def r32_18 : List (Chunk 32) := [
  w 32 9 0 870000 870192 12 287 ["E2~@qK]ssr4DgFnCP2Mj]L+k8<51bDJliM>{7zj+k1Z}%t|7,&coO6<h5pJWt?g&","#{Vo]>L_gr"],
  w 32 8 0 880000 880129 10 227 ["**uS%YG6^sif7wiGxMi0X_p34w{n%fS[1zQ(2qmQ=EsBGUBMhXeg2%^'k`72W"],
  w 32 7 0 890000 890128 8 173 ["#.T+?Xf(3dJf:u+N&RvQE6V0bVQ@>xEtEI_'(i[8<~HT_al9k3K"],
  w 32 6 0 900000 900128 7 144 ["z:(g$a85L@/dsPa7<u&4jw)K-?3KW>1`32:BQnB"]]

private def r32_19 : List (Chunk 32) := [
  w 32 5 0 910000 910065 5 97 ["%>pc<t58&4q!9g3i-mMBAYo<AUX-}%3"],
  w 32 4 0 920000 920064 4 73 [")4^(>]8`R~c.LP0CqI1:452"],
  w 32 3 0 930000 930064 3 52 ["31%{_7QeH;w$XG+cV"],
  w 32 2 0 940000 940001 2 32 ["/8P3.fMiLn"]]

private def r32_20 : List (Chunk 32) := [
  w 32 1 0 950000 950000 1 15 ["<|PyW:"],
  w 32 0 0 960000 960000 1 14 ["Bd*4"]]
private def chunks32:List (Chunk 32):=r32_0 ++ r32_1 ++ r32_2 ++ r32_3 ++ r32_4 ++ r32_5 ++ r32_6 ++ r32_7 ++ r32_8 ++ r32_9 ++ r32_10 ++ r32_11 ++ r32_12 ++ r32_13 ++ r32_14 ++ r32_15 ++ r32_16 ++ r32_17 ++ r32_18 ++ r32_19 ++ r32_20
def rows32:=rowsFrom chunks32

theorem good32 : ∀ r ∈ rows32,good 32 r=true:=rowsFrom_good chunks32

theorem sorted32 : rows32.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks32 0 (by decide +kernel)).1

theorem mass32 (i : Fin 57) :
    bandCount 32 (i.val:ℤ) 56 14≤(rows32.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks32).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 32 (j:ℤ) 56 14≤mass j chunks32))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total32 : (rows32.map (price 32)).sum = 306880 :=
  (total_eq chunks32).trans (by decide +kernel)



private def r33_0 : List (Chunk 33) := [
  w 33 56 0 430023 430713 100 9819 [],
  w 33 56 100 430714 430903 30 2844 [],
  w 33 55 0 440022 440707 100 9561 ["jF+X&#1+2*kPsZcK<0!NnKE8OCazo$YW%cy8m>63m}k2@re`XIv+YWI(u>!QCOFk",";s9_.B!+Z(CJhhP!0&t>~i;Ua$3/8/yV(@JJe[l14Bx9IW4*LhP3S$lfAAf{:&eP","'DkUX%Df}nz)?H~'ejR^s1?eQd"],
  w 33 55 100 440708 440902 34 3118 ["@`Dt`[0,DJ|86ju~2!?qX:`[qQFPd1ja3&S}PojpM7Ah@!]9<)9;qW7o|"]]

private def r33_1 : List (Chunk 33) := [
  w 33 54 0 450021 450650 100 9330 [":W8%edm[|hj;^IR$=m')IaA5E?a;-x-v)},jV6n+p%`iIV|DQq$aq#5!5y<.Q,-V","/6XL]8U{wB2<!#U[!3GLhwM|Jtd|(~zrr6w%bH'C2.sm7W4D=aQ]OZ)*-*+&yE$X","&t%9wsf=L*3CE#4{,&olKUIbS%bO<TLTcj0|?*fY8)v0;4%fKTP1C"],
  w 33 54 100 450651 450902 38 3390 ["7ZyS<I9TY5psV`^.ITZpi[iyOx)8/Je.r_;5c'A[Rj2|au'Rey_-d>w)Ib&L2$~h","&OZ%y(olV((^XA*"],
  w 33 53 0 460020 460644 100 9163 ["e:5C439etB8(XaeHjNww]UAy#n^C)QlJ8.GBa+B-O_JWvOy~A*J:eFfUpcB0k@gZ","<Om+kd4D[zs2dUz)`.@3K|Tw_q`9-9J5K$HFj+x<vzWlD1'KP>gY9Gd7d>9$bJgp","Rjq;mlhWqaW|e+}w+mH!(H)LUYuCEz@83+l#g'*eXs@7j~CLhw]&tP]_/|^cvDu>","*1~n(:}@p=50pd0^s;%H2!Aba#<*Xm1Z"],
  w 33 53 100 460645 460901 41 3545 ["'fxqX4Cve($j^fY8vg[MP1Yzfal@(Z_o4+>f4a/>QQlN60dc#`5rW<7#@kesL}gK","&ruX+_]tF[PAPy~dP!LvR6P}68<1p)u%{u2fZE5V~L"]]

private def r33_2 : List (Chunk 33) := [
  w 33 52 0 470019 470588 100 8990 ["(;X3FlG--HWh;TYb9x8AdV0|&Fl+`IHO4w$CO3T'3D0x),KhO2D~6/#m3'03A@1&","ERjY][_@E?owoZGO@~2?9]8@+;5B0QkC7sj;l<FlN+.Z`v:2'yD$in[{v0}{B'qS","jiejh0nLbe#.PJR{{CBG.UD>Xiq)gh~m(R#.gH:D7H?xeP$DSi&,IWf-vT6ID%Rj","<1U/}5BvLB!xZGpayuy?$Jxz!0jDgd$`$yv@?fJ]84fB5E>}@lmK3{3wCF_5<THl","eeME2-a9"],
  w 33 52 100 470640 470901 44 3726 ["VL>==%mAk>d&hcjT0#68z;)qrn`Wq&+Xyf4QWZ{Yc~UTEc!hyit9EV4]Pf5-m_|x","'ti4iZ*/CvKv&|{Zk_LoIlx(W;KfzxGxwS}]NX<ba*I>{&=5:M1>RrOdoqLNWC"],
  w 33 51 0 480018 480583 100 8888 ["ow6$,k}TGDv9W<&aMcUj8V(R(x>a92wpoYi@<0`Wl($xoyZSz<.t4X5|rCVu1'Vk","TUm|904!hyS3>,*AC=SF/hWQj/aq~!%/8T8s2o%h*~FN@{t/~DKo5>Bv7|bdtyip","cyYLuD;ajn*`'@Q?pZ(U_Q02@^l`u+d(u0cJ2q:2V$)=ZZU7g3/rl>!b6?QSaf]Z","x|iH6lwHuD![LCW{]!`g#i,AN:`jcav2yq5:'n/}piKgn,aY50?,@9@e|qCDGc80","$s*RHi5*Hz[d$mG`eU6+$c/B:VEU;cK<"],
  w 33 51 100 480584 480900 46 3778 ["`37Cm$6]{&p#]oYS+0Vb6^w.Hzv~ktOEu_magK57PFw|2u[N_x:H(O~pOe.R*;9j","|%1oexbxsS!q&5Lt!oZ'uo)->Q01`DH|M`qdx6K/]peiOhdzWE52_/Np,W7U:JkG","#dygvaaMo>Wb,DKs7]R~v"]]

private def r33_3 : List (Chunk 33) := [
  w 33 50 0 490017 490578 100 8773 ["(`8TsLR_J~$Ke7RAs@z`dHNZ6;z9R3plJewdVwLHVIgMYu~QZ9}0O0DEf_Cu{V0c","Cd,l~,_2`J8kH~)1xbW5M|N;JGZFD!,r;Q}`2r`b+KuBq-:-ZD*Pea=e2,+.Yob^","'G;@')~O/K3}JR6BaGVBH)]l`$2ZH>8g%Yl~e:?}]@A`Z-9i(YvagyTC*E??[S`:","C?yqu;kVG:#0AHRu*61]j/JVXca5P`]oNwU98`,`:>Q@4ZMlftw3u6p/dkip71W6","%&/,iQ%9ELjUaAQu+jv3F7Lq^m69gSgg1ip{#`9~{*SoB^09'(!8E'T@U~Il"],
  w 33 50 100 490579 490900 48 3843 [">0D8HR'=CIvc'*A}.'|167eZFLYj%%H,sV02CSy`rI<fXfDE_M6})feX2?q>p[%P","?q`Rx7jle!3)7=#RLAD>aY!Hbf9bgywJpr<kPQ>ebO_5wr!q=7Pnn4f.Wqm1cOR+","EUa$lj#E@^%iEs^p/%'c}gkfMsyme}Vq*QARgiL5"],
  w 33 49 0 500016 500523 100 8644 ["Y<Z]_yPP4@!Ie2%/$h|a*?F`sH0kZg4{f:<_+fO*r|x|xFE]E7sY;7L50`+x3+qR","$_vJGBJnD!8oJFpS}WML#PdW-E6IE`N=2dUl$2L^0qnhrNVmF>dX.jY'qq{~4L5K","H-hfA>8kyHv4Cm1O;r4xvV9edvN^N;;'_#6)?eHV$:]F7K1?iq.9ZKACFAV+pX:=","%k'dW]{Z~lA2Vodc'8$PIMf<?s?,NGwY2OmBQ+_y>~[Ka$GwNdc(]ooyFWk~NWef","==)-0_Hp1_hh!J.mb;4M)!Km#YkN@BLSMfB'x+Rxjb]eRxRt)=h?LtkTZzJLgrsa","Y6jsVl,ae;n$(9"],
  w 33 49 100 500524 500899 49 3852 ["t#N}yJt*N0*T8{h`@CO('a~5b,7;7D6T7CKS@}j/kV]yW2T9lawBAo)oc`gjJ`?j","(W-^?&o;ejo,3pq1/+KNG?M](F}n%Yy3fk6@Mtu77dg1sg~qw8sT|AcZvw%C[_jP","'cXM^Sz}On,&AayA{*=LY~/$|w-A2.`g1Yjc-^<-2$-&(]XQr|yRS9"]]

private def r33_4 : List (Chunk 33) := [
  w 33 48 0 510015 510519 100 8543 ["j)YFQzRCNe68nTR~'ImQc_1IL#r{apM&O6L/)G8@2_:{cx/4zLLqMbZRe%Fe]hXs","&,1of>e-=R^F}ybf&fR5s;Dmb?]$%Y5NV[!sr;?l`}9{pk$x[u!Y's;!tP'nWuoA","Q/*!3L$KRyA(,|xjvCT(]nzl/sPQ8aTIFem_l9w<0gL0?j23)`9+g)0H,[G'>Ja]","*:>99[J^Bh1;7v?x_jRG2k%RzDH>Fv}Et|y=r+{YQ$OwC-[YZQ'Y1?9#r{hR87ds","&qiG6^k}i`[$eLRRa&SHS[bqqo|284#k3m467D4t/(j!{M@7(]['^2/6t;Sg-x14","#TOAPSm.O<%Qs*o3*$aWb65cEjN"],
  w 33 48 100 510520 510899 50 3825 ["78S_R2y:19.QptR9LVnpP?0(+_dS;v@9GR`~'0eAA%<W0#Su_=>zWB6|1{<%DbMZ","qC0?l3D3][-q>HfLASO{jvy;Uc5q[}Uj[1T)_/g{D'toraw1?ab'uO8`1X,Kq5,g","bcY8qsk=jkB;Cx,[pkrL:H$SVE[,?k5I+A(sdbYE]L3E#uGoChnE^%5k8Pme,<EV","vNb~3"],
  w 33 47 0 520014 520515 100 8439 ["2>KOE(W5r]YJUhBxm@51(dKP.e>IW09.!ayF#8j'[$fkMNK1YVyV!iFc-MkUg0o{","Vp3H*-`.%#PaDkF,F%|claqrsd'd]E=-?3/?}:yZ^8p6S'_TY`Ct?vRDlg^m!j$)","4gl}|R@!}{>//):W(?I]{8)u0'NoP972*5:P*Jp{LctBh@[7*&T]W8'&uwI`N=6S","80{7h)ML'GKIsU4hJ=d,&d9*,OCDBGv'+j3JrYA`G72;(7%o*1Fi(5!^Y)HBG)K[","]kreI69-OC!5@RsPE_4WKt*8X<JzI*;=ur;y$MBI#)Q;RWY6?9nKhN|>C1-O3<:l","$#4uZ{/GoM,"],
  w 33 47 100 520516 520898 50 3733 ["%S|520i_1o}n.hu61xzFC:!oQVA|A(/)0Z]zZEBytrUEC<A)SUiC=v.?,LmdBrov","0TiFg-QNN'-z=Jr`DKLq-'X[,5~Uv4'>e4/-8J;EaopMT):oX0O}}>jMb3{,XiE|","{Vd'96Zi.UR'YOtJ)sBN$x1{'Cpz~'fB]d]z,Iq%.6cK3Ar@,(*&rqXd&KA)>'Ui","#:8Y1Op*CO:8*hO5s+7"]]

private def r33_5 : List (Chunk 33) := [
  w 33 46 0 530013 530512 100 8297 ["'M:uNQUI90aR2{GT#O3ul23q/oxd6v3Z]*g3IIyzYooj6<y`@38L=|CTFH3S5#^&",">_bilhW]^aK<'Z05=;.HjEvVao}3H6fA5c2V]!7wea6SYU5-p8e%1aSS;h3{?v_a","5=};@YJ12tgn][th6T17kn&9/NaqF]oq}Opu)7<}z_izutj0Qo&uJC>qU!3*x<c;","/9/0z1)]@<jHLnNpOpsA]{qBE{1$7Fp{H!ah.5;inDZ+PClIgKdSi=pVRK8,<l:}","D34W:=;'gT1)2`BHoA*>O{fL-M[9FGw}i.0:Vf&<r9b*'p_jW]QT&*B/t@6#L,Sj","jUv+859T2mqQAN~H}e%_"],
  w 33 46 100 530513 530898 50 3667 ["oz1)<u{:JK}$WTHQphk!l`wb_%C-8c=B_K2<bw*BB,5Up:47KC!nmww6pCss9&FD","M(Q^8{&]XmvGk>Rt%,6]zHMG3`Vt%f{[d#|7]9MiG.#OI!-+VHK<DEc|(''[QCk(","niuS+W|^lNKv=T{=znED,3(WLcv_~DpWm*q16xUjB/w?3YinX:*k~HJyY;Yb2g(n",",DYk,7.ZD7gY@Z,IPiu"],
  w 33 45 0 540012 540458 100 8181 ["T27/brCzeO$B<}_{UT>:xNH,OmXHC)x}atsHY}pnXMXGw`.u17yjfRlsCZZfwJ-6","7YXh5xTFK_Itg0!-@kFqTx}s3{C7`!z7Dng|wv38sTD~??H?Jv329CPFG..dgc:t","U_g8RH%PqoO_nex+E*o3<O)**$E0JDol~yum%WbX0k{sd-[{:j6W%zI~Oxq[2aF.","r(~{N8|66$7lW>|<3Xj:]_MQ3cA,3:a8u(KFn_2E)60U~P^S#GRpRE1]JJp$O{UM","U[nZp7S>~cTv5&){o{$1&$LrHpMriY(U`TDMLnj}r/cyN<J'C|V>hTzpK=9>vZWY","%Wn%:B9zG4w]$Enm`"],
  w 33 45 100 540459 540897 49 3512 ["bIS#,1NR:N5Fu'ep~Yk/<mvWzw7YI>aRVSBc9jmrk/Vvr;EC6.0||tD75.+KeGgg","qTOWl4hFO~~:iYr5@XY@t7K>j4}4IC8G*fbQl2m+CTt3C#6D1Pk(a8qQ|'j5:8{o","zRYiNMDxrdf.{I,_d12:X$*bJLG9k=X)j{`1d%Yu7(LY8qNf]MR8Ct%CO;i`?dO?","$7?iQr*YH:*Os|9l@VOy2Fu@ZO@"]]

private def r33_6 : List (Chunk 33) := [
  w 33 44 0 550011 550455 100 8058 ["wNJFQ_[z]<QY;QkSC3f|AWjW^b01fPDuTZ'*8[w**YB&^w&k#&7RVe'X8THSwU(R","12mX4+4h'hRV^%3v/)M%@*!oFXJ5]m5U(p,!8MCk[{+i/,1)=Ew>UV[n%{5BQ=Dq","Xr}pj%haP5&ByRYmBs0BxM5y|sMsZa.-cNedRhL#oEJ8_z+03QHYx}E{(af-myo!","YZjMz_WK2^<jp=]6&'x|xc^tG^AR^T2u/%-?~/pmflxx:OeMu)EFtsp-7U0Q<U9s","V7|;L7w^6W6l^{05vesUBhdswJi:D:d})c3o6-]90>!X<tY6X1+r~G#`CAR,vU$S","@gx,LX.T9S[mUY"],
  w 33 44 100 550456 550897 48 3350 ["/='?(n])je*M;X.7Yrd!Zk2@jo*Ypfx-nha5fEA1Tu#h*2vn*P:qLWvjU~e3#~sx","1xlgx(2Df)eX[M%FL[C*S*zxgmLsXpa7f0Y%gmAh}FfXlC@_]G<MH%-Bd+!8Ixex",":>6JbkxGzi0N.%QSvI9is-dMa]S@LD[9}-2:KwV*~yw4,@jWl+PlJgT>)%}nLXHZ","}=Vm#xl4Tie!i5+o*nNp6Y4@`"],
  w 33 43 0 560010 560453 100 7940 ["NQH.aNZ9>Zo(ljEb&u~/[}OuTD:n.rWVDT]vYq`vXVM2a.|!Du5=lS`h2PXNoj|>","CT.s&+UO-$}}DAvMP:SL[EgQ8#;O12{s:6-t9=q)8rCYpvh%Jhm2PIP;&kmTlx!w","XFsLqfe@f_kBIt/|YK8N;i7Ds)G19RK]/Q{QI5AFg9nJyM%RkCy6Z,;[iJ^p}v7&","[cWr>NG6+:}$X%[^,.-gRA~xN9J,EWL9Sr6Qv~fsp0~5y=vt8]*fM<Zz(C,DMrLT","tBII~$I)$hKu>JXN+Q5tbRy|rJX=<|^KP0`nhr/Q^=PHErf_F9WJBD)H1TJ_B%71","'Z%lAC:WRoo{"],
  w 33 43 100 560454 560896 46 3127 ["5$uLg<ICd`SBMECNxzEj@#a)kGiMa0r03NtRfaC|I`<SEtm[rl5~2?d!&#fk.M=B","o>RW6O=''LX42z<5E<40-_azo^W:,#Yb6^xn2%]FZok9rB~(c+mdQ(/+y@5ZC)k&","k|H@dG'uuxd&[KMC#[chYrWXZ]*so+(sy)g(Ja=+y<[,NWLxwlUZ5eA4xmNm<}ca","%-Nf*;J${>&&MD5G[O[{M8veIm/-"]]

private def r33_7 : List (Chunk 33) := [
  w 33 42 0 570009 570451 100 7793 ["B+O1Rq4d(*V`INy(U8-[)Fb@-!,GwXFrM}MB;`0Q/yHmg4<5~BrH)Sv{`[I|~7'N","y.%)LFhHHW~eGbw(L!(lu;i5p>(y9.hr~TKV^=q]z+Zk.iY@=#R#44@&F$P_5XC:","9/6WHy+mn6dTJM|L;nM3hJ?{6hwbx#c^[Zs%A~NQU,>|6@'}qm3O+gJf7iiI^U(>","qg`[PPlNIg+,`f4M7Y=DZ_B$Br(_Xsx#bIFSkm@?lS;vX`W,|-l+mN:LQ#3t,ZQP","Lf*lY<7Yr&7)Nd5k#au9`:Uv3%P@LTJg-zuo+]PW6k:U'>X]6]F''^:L=q-ytJnn","/*hb9bEDpx,E+ZfhJN"],
  w 33 42 100 570452 570896 44 2917 ["1`.*xiw58aqO}~Ll@27?AfgN9|7~-OkH%H9rq-0++M/U^k8IuS`c.jz_XL0FqAB>","MB)2KbE[748e06Ocs`g#+7%QVFjh<!=049JQfh~]ImT3|I28xJt2+%C|qf+-wN&I","7]mvQ}O%8fSv8S[5T'4'}/lwk%+D1j&|w~bXe4@fHC?RPb#G^9Z887I{kcuA%qJe","#>%L'?*NJG}Vvk}d3K"],
  w 33 41 0 580008 580450 100 7654 ["'?M=LC9>1uZMSCpRp'Zfr|]gjK_~}J5=g;Y6N+tx~;Hfiu^'cScsv.wNza;z]Rh_","2xXN8`JP='ga`.wgaJE&c6ACF#x|1b^bIVR|$/fPB5Zh:YbQE,W,{%'xK:kT+o>M","=m6w^*-=;C8xtKbKDQt]mJ)d3miG^{&%PYm{^LPO<2bcAn+DuwRO/;i3^KbMj+a6","f*|s;yJB0gn#@[S9%==KYZ/2RHdyqTcW*Q8CRN:ey'tIBZ9Am[WCK0z-Vb[gl)DX","G%hI@('?Cm$[9F;Y;-^fSP,0-8w{+-%T|?7aBYNi:6[,mv-S{V:scGYVw7a_sqO'","&d`ne5U3gHwps*pHz"],
  w 33 41 100 580451 580833 41 2652 ["7Ce*x$q)bf[I}4lS`Mi#%vkcG{PX[P%u)[Ip!=j!R)g?erzQRoQE6]iF+2Ka8Qx2","XrIOa^n'a[N'Y.:=G+,z_=G)UXvW%0Nb0bY)T:Xs>$f>K[}Re-^7Ge3dPT77@^vw","5o`#b}+!ThJ`m=;//sy{#*ph2-Cz*WewpRfu|r<D_tia%jL.lGTw?omoi[9+]J*K","kk4>mNy8&5$dqM"]]

private def r33_8 : List (Chunk 33) := [
  w 33 40 0 590007 590449 100 7482 ["H5[BFEBzu+o@`T]u'F#qI,XqH0|_NN@#?#7r6oOrhrJDxC@1/__%JAj[t3VLW]|N",":$~ufTGdQk.66-f{MrgTn2r6'Ve:(De>J|LVI_QjV%6xucpy]4h}>4TR3a&9@*[N","lK}nh$](;ri8G6{a=t=_,](ivV+sV$smg|vpjb9u7HpH#NSSXabn;0NY%K}r&eH7","I1;rnR*p%0(JN+PFR:6zO3NV=oZrrlx:`Y]}HA03mUrf9cu}TR@&u{Q_*~Dbn.>$","5sFTjB7e=E$0.YSz$8H&NQNkSc9~cN0s3#I}OzIXd[gX%~e(3aU{7*c,V`702O<T","$D]1Li^s?vKb%AE>BI^k|M"],
  w 33 40 100 590450 590832 38 2402 ["&s.yY$||yWB'$R3k>8ju)KAt9(pFaJ|[:J$-`]1AUI[Mn-9Q!^iX9/y`VW&H4TaF","[?Q`m#l{[!ck)+`R8EY)U(LP5t37Oj9y-.=$SnW$0B!6@fg%mAN&0,1TqS98.!z(","OHfZKhqen[:}*}!%dLa9ee3CM'pTp%CxNlfUqc7++MQGialX3Ht|7n!L~n]f8&57","+^"],
  w 33 39 0 600006 600449 100 7327 ["aaIlRm~P:a]$mfJ:*}I`|A<cM<5`'q(VoI}2.mysE|>4N2zYjZ!1!.k{)OUS=+b6","RtV8T%516Fd^dq?5C,l:ilcj^cgtLANC&ag;5sD[;o?IS%>uAn^Lz7c^dJm3'7RK","_@[l>zzWBRLwWWBf&/x{qKhR!bLp3R~#ws:%C-,/{igl2~BTndaJ{`Q1J>v9?C,/","s'5#YKnkr:Q9?C=g~-?UdX'f~|1abcDX@Ni%@W4+0Jb-jODg_B0L_o+1>'@n^mH_","-qK$.mw^eH)|DH;cT+dOoW&?4UJZp%uZ-db}^L8}dU2w+T.m[:me.!bcuC>CInX@","1O{b~f7zr9Z|ncmyb2|qXMGfo{_L4"],
  w 33 39 100 600450 600832 35 2158 ["@b/rKpSAHdZSmvqL@H-Su5l:j[3VSjBIq05-ev=0SApK<}%m@:KTfw8_`h&[&:ew","lk=d'Vx|t-e-Ytey'4;T3svTOkas:?6b=2-Z/ahD1+yl&S:Cb8(H3J+Jk&:I7EvN","+a|1oGb%rA@Y=<#H;s,F,+^hTHw7'&f&EXA4My;=VlDZ10Sv!:XoiAwd"]]

private def r33_9 : List (Chunk 33) := [
  w 33 38 0 610005 610449 100 7137 [":cq_om`nnOq%rUIT<bK|.=jzLA2gBP2OLr?{QTQVS5<0>C,B<O|rT(j^c=5:Vc<R","3D_xs5f4o@P/!7~Ei(C<Q0X<l0wUnYm&yjO+EHFwjq]r'e~,SR]1dh/.Mzp6t>)p","|UJz{5q{K@DX52)Ee&6oL[-jW=!qM{*mg*Xw*mb>JSIi-|[R#VGr@B&q6[:orgGi","hIO0b%%[`+DFAttkb&:8*!g/h5pzE|MAc{nTl6NP`5nVn<dVjz#MgfMs%1>`3}!3","nrvf[$RKYDCU~0M?Me3s:~QhAR>~KpK_R+aHg<:S7*gxka.$46iSP`a[fs9w8HHZ",">'Lc1L2;a0$p.*}[a+a2C3#+Py/`:F3I>X0"],
  w 33 38 100 610450 610769 31 1867 ["37mQzA=Y61uxtx#nE(W6={>Bd/+h_x,1L<Ms~f+9p><X0<0EG{8K1t@qHJ+CmSM*","P=rv[o%nDltF@:Wo/06.<~!W'HSF^1>:&M>u-[$,<y:JVRdRB)fbV=](H3Hq889A","OocwUx6eBva36+Wt@JRi`'EwM:;`>2pvU?^=~^]7_"],
  w 33 37 0 620004 620450 100 6958 ["[R:}N}UAD9CL8RT8:nFsY4M~ViScLJ.Gq)Tc'oTGb;+meZ$HqnmGSW<7uRZom]ic","})+(P%*2L:#,kPUct%S!0w<#(8G=>,<(~`7/SE#C-nXnsWOc]0<DX[R~S{tjU8!x","0?qK!sH9y=bHF0Q$LWK}4N0k+XPYe/nxa$dK=@K9G4ws`:y.62n?70p=y!,h^$6e","^O^v`IY`k6#J93CH)^))N]uA(h%z)aeNyDS`]8hCk(<&-aEN9/[,,t@[plE~[)sa","^~oow8GmG=pNy5+[aIH+]99#IZ}&[xdc6Jp,{dZgNw@h[#/o}%-Vc-+>%NXP-i+:","-:TS^H=Ej+t=0DNS*!S8zVXF?r1]*x!|TXYIW/zm2sJHWX"],
  w 33 37 100 620451 620768 27 1590 ["c]%wl|8}{JTN1t*.t$tj<exO]Nc<[gDf+Mc!LRN`l`AmZ'_'4Z3/3MgCPRN.tr@/","LITJK&_`o2bBy:PHq8ya/4x&iN)4^Xb@B~aya6531uBpvmHT6k#A?V@.Mvk*DI[9","/hR=sh-'dr1L_+Qu;mUP9"]]

private def r33_10 : List (Chunk 33) := [
  w 33 36 0 630003 630451 100 6741 ["%Y'rc!NttUU-/Ho*(o4weL4q+$dnEs>V-Xj}`3HT}25fR8hX9zH7pMaPV%a*Al$!","r3RjsKmpz]CngCdTe4UK~%d~ywN|L]-3E3=|O}Tc1/?RM7UDSS&*I#P2%I%HxAc!","`ul[+:R2gM.eD3OsrHHjdk[Bw24w:Cdm._~NhIhF7X%flN([[_}LkSM&T_hm(e&z","&I>v^^W-leOL7eYd/kY1oj*T.$Yl`?6@IVr$>3Fn{O>C:qsEVe`B?GayLvdeH;Ql","7_%3)[,Q`V7CDzeN^_lECW~ezW.cfys<`U?N7Q'Yuyx~8#66#ps;EqUE,q:G-eWE","2cbo)]k!B=r8-%HG~`Gjn5M:$|EdoUO]]MRn&7'k]i;2yJTH:ZS>zYdHi&u^Y6+0","%E"],
  w 33 36 100 630452 630768 23 1330 ["~U]_X*.l/VZw}_Bs`o'LB*;;;i,$=%uU&m*.G-@ceq2c3gSRj@6Pq(^*!4N'Rj2w","}1ESD+D`JpYjC.E%7/}TrMlOzt.1g)UZ!brxWEE+8Q?&InbpT7.2P#l,D"],
  w 33 35 0 640002 640453 100 6540 ["e'<'{2>XV$v.nqTIDZ/J,eQQ.CD<s9n>~|dio+b#'#5}y=*s&*j[QHs+V3ZDQZ/>",",(`A/4}oZmBVC'D=Ix%l<7m.S'[l`k7(VqdCXhcsc'hwX&W>J4K{9Jt44!-X<Z5*","*{sPffD>OTr9Srvw<D{0?'*&No8!9c!F&$(+c=jvGw9`EO|D8a5*Csi:|i%jkeFZ","IvQd^;yz,mY#<{}_K9s^}x?10K~=p^(PyS+L&.SAyJ/kFD87Kw'J#Ix@2mi#EOT`","SzqZYY${pp$PK-]T.7+#Ew#y@YVo+ePAw{sW:#aJ8s+dg|%q[M$abSqImF+;n:^.","Q'v1FIglENp>jEAv1/q5dDi`y{qo!{x`5T-)/{B95RwsO**)d4Qa.f9`h8f=sAut","$F;|9B;V{n`M-"],
  w 33 35 100 640454 640705 18 1023 [";tSNK?qZ7U3<V@,]|`]^iM<NxRY?a1Z=u$a:N^^>`k}pYC;Eg=X%`ZJS^lv5)c[k","/3I7W.VlZ~:c7mFUPNdDT#rE_23ZG@"]]

private def r33_11 : List (Chunk 33) := [
  w 33 34 0 650001 650512 100 6306 ["5DW:.ruuh+z5p7^5VnUjj,M3x{X}FjI*(Xin[6&Eie)OLPK:#FYJ@#c=Ha[9/d_J",">5$uF8P'_^_Pw]z#%ru:~B@O_Aug8rCB_0uXgs8?T?aI$t+H3.(QB^{g&xKk<oFQ","-W{~>)vWXcr#Rf%o*=$5zK8d)ZPB#E^}SE(#!H'W`+3wmeFt!aBv1*EH`CcE{wN1","4Nu=yQOsVx3A@C*4@%i&y2*DQXQs['7CC`0.YAhFij_?*30pX6/$MX?AL91*m3+f","!8;E|X4CV&d?CS4*pYBtlA)7sf(sGN8Qix7t2,@Gajr1OWQ-NE-l7RG)E8VXxWsl","dokVef).8_pRpH:cY]Hi4&4F-s<lHp]O@11$Keew-'Q0X&~U++i+quOWdfZ,_fp4","$lA&1&:B?I_jNo!(Du(&-3w;sr)YI,+'vR"],
  w 33 34 100 650513 650704 13 728 ["<.*=6>]y))z(g9W0f%)OBH>;2Eh*`sBe0[lk11ai]~?*'4,DK6&mahx+DQwZNsRi","0"],
  w 33 33 0 660000 660515 100 6089 [";-`5&lN$p`PYtT2n1O.:,%H~;)5SzXe+*6A>@T,SRl@A1~5qGtJm$tl1CO`p-'*:","<#%wVerY'c^8~eP#vLnF*0TsB-Jg`wkSf%Nz0ZfzRoDd548(G0'vhGR)<c~&8iXU","Se[s},.V*?9i'<m.e-#C&u#d1EFUtYgt#+Nx]RmCaJI9fq>_71^/+~qiv'ucZ`F:","_sH(_jwKtJ,wVO`p@aMpu2_!F>n9_jSf?y,V!,@SL,9^u>x;RPq5tMqTRn#X}!Bd","A9r5e=gD2P~]H8UiEiZwF_pGv.n7~!V-7)e2FW0!.j{D.2+1}/.,QLbi&l@9i8(c",":~J:kT3;2NG`Ry7y0Q4s2{>;f:+LE^8@ot;FNs`oVlK4`)w:}jo#3G7I!&j3K,h(","kG'mj>V#8dQ%tZ7CSWN?@+-#oRQ@(c`:zqjBiM"],
  w 33 33 100 660516 660704 8 443 [".{Ib|}$[W$wbmJ/t.OyrmJY}@^Ih3L]%7L>esy1b"]]

private def r33_12 : List (Chunk 33) := [
  w 33 32 0 670000 670578 100 5845 ["h|g6;IuhE`8Qv{7L8]q:Tz8br3$v0>P]E#/Xaq9r&hnl6I>MxsDQkZX-]/g;rWF3","u?]{SoGr$EPqAxl`EFG[u:e]~V&:V<o.uh22Mkn&h=P!4a^fhoY<-YN;@rqa:Kl1","i+GM^7*@j=_kH3Xcr7aPEDGVHt'1dQFnfkO;pkhM{{2h!pG0!*'W!npXFd3r~N9y","gLj.NEl-4*7^jugS!/x$O-tHlG~UG#XC-G|ip'Imo?<uEq4'z<Sa`<)H_C'p_y1G","AMKm6,v[4iwYZv_iO@.4iy-kl#8wOIsTx%d8vR#VQ+geKx`cw9:lzQkvr7Ap2Mot","GXPvXF>7zQ:k>(^}f}c:CZ8Lk,}89'I/+h'm$_0?V>Iyut$o]i;<&YyNqK0Shz|Z","4fEV)O>lhd*[:%9L_(J}Vb?3p`|J,e!J;=M6L*Jw#1^x}){q.o#qqVH@8eACo/"],
  w 33 32 100 670640 670641 2 110 [".r3&'6l$IA"],
  w 33 31 0 680000 680640 96 5409 ["muz!B?x_XO+U_@f2KYaw,2`]a&nRgZ6;bpy8cQr,r!A-=CB?O[D`<Ynwg|M4cRNd","'pf6tz,.|q:Fp;+zvT9K*nNk||6~)hwj&f3`S0c}<$LQ7XP4-=maZ`UI1]|C;QE?","fdOosja0^9kMjTGh9ZZ#&{)RbnO]k*<)qVMCU!rWR4}~>)J8j(rs?E7WH^o%eUF1","8jcBeUj}8'~&5OU<op0}+)f^jU&c':lCyR<M)&V~Cdpk2_L]:1c[t7Di2N9}z*j]","&d',Yy`DG6|)sc4Rb}zovi'AO7VD8?k<Z%*jQgFs`n!h,-c$l+/(+/?mHaH?~sM~","Is_fR/@5f|YM<*IJKOl(9@)NdA3yH.um90<U%x9_Dk_)D%=Ju:VhYL4RlRCL.Vk'","$tjDYBLlZRKt>&/t1QYP78CVjFDn}ZARAO5NGhF^[fsIf,Fhs-pf>E"],
  w 33 30 0 690000 690640 91 4939 [";X>S23n+~Eoq9Hn~P11|v9ZFk9rW?*~Gu&7/}WwljEV]w~Uo|o(@2.Xyktq_p(9O","y>#n|7HMpcib9FT3zujU]fO~<4Q/z7j8y?PZx.Fg/VPfLian:LX&t~RH0?WCjdRi","x0^_TkcpjjP/B9tWh/[D?Nmy%]F|)(M5C}){&z|{DtgrO_(<6?86Uy9Vx,.sJE>P","7-(>;y6Y^j#[N5+u?{Gv_'tGffj@.aOzmYp9dHSDhDhQv]eFup-qa2}8~1}JtBj~","f,9ggw9s0n0Mc2>{1;T};M=%b9lA.N~vQ{ZGviiz:&{+#EmoG:*-P969qxXNsie$","`RGg!],HO{<0LZcveeijTp#]0]mWLtJ}<'f<j1V@qq/=pAUJrGNg`oZ>1r$-#bTb","iHka_hc@'Z}^,[kDD2-0m()c'I6xnL>0+&_z>46W.MV"]]

private def r33_13 : List (Chunk 33) := [
  w 33 29 0 700000 700577 85 4451 ["#@ba(l!B~5X.Vd<c?EbBcGX-udi%DBtu0CJ-<4<S0G_?5Uu2F,H/Ki>@-z{QSP.C","jz8SM[t[|5SC>f1OUkxg(:Ij%l@gS&,lo%8f~@8`)`eFUjBt_e;s>F5/Ff4V4,#s","chj,vf+c->>,uj.5RFeJHp!'k#?Cf}9di8g!==uh|DEhU1Tf#eo**[sUe-1l{rmz","#gJ*7<$_{x@[%@eurR6jH]etZ0I&@%d-Dg^2F6F{}rlM.Q::(rwgavsn%d6^WJTK","K|8)kMr2B.rRR#[9R/*u?2BL#1KO|alIInxR<}{Wk[NP:7ae>?&a|k>NwbJ&a_(U","Qn(gCb?q>,tR|QU``W%e1x!_x*'|E^7f#i**o|Jd&(k<FG|1wB21H^!Z#|Mu.qH9","#0^vL-PNU(1tL$*dmawo0|FHqk_Y"],
  w 33 28 0 710000 710576 80 4034 ["g}2Q.(9qt{Jj0`1%gXA%8U<|}MYQDgzIuMH$!{/%$;3}X0~/xVTG*foXiXO4H+#G","N%sJs!79ZSZUM(h@yzCM.sqCR/1h^>E&[w8^7Xg9r%9(/bfaca]JIvSc`D0o@Rv)","7ex34imq}ZzA`jz,-o/?~IJ[/Fs}LtSS2?Sw9jzxzN|Ju#Rx1%1M|>%1E1m#ogZC","x}]UaUaPJ+N4hKi[we_<?0.i/[U.62Z;;)}]?X5,y<ym#%B:(PMfFLB|;O7p5Mg/","1cY*B.MR8i%N0p!#L}:$l9vt0|>h;N,neV03,djb-=PU2;sjbLp:@~<)'jR2xtYT","&_/6uUDNS-#hb,3~V:3K^a*%HkKGVh>5u#x:GfwppJva'g|COV)Ey!*bAc6UkTXp","#6G'6m)Q=bvlOd>j%#^T-("],
  w 33 27 0 720000 720576 75 3644 ["kXRaW*^)qY]z1sq^oskpgecp~L`4f,NQ-+a)L`5l5.$K3a;RnT/Z-DKBlBh%qr{#","0aRprcPh/:kuGOt@8f$*~K+2XC3B@d?-=Ob3kQnp{75|N1&g}3Qsw~-`!ZIzUVq8","'PhB3HkAu4Y[YT^')?&NQZ!q_*F7S<*_%.&RSL-('BI?&{d4X!iZT#ua@<W%ZixU","#^_HCmLF?grv?.,2sVZ*@tsV%A/W=rR0w~=OL_$evt*K9+8.LlaM|yK&{!C`l7|S","U|>q}!(@vW:FsF1uMPZ,&#=a4|Oa<!H&%UgLwc}-|2vVlV<yy2rz_9QHR6!$1Q`R","g+U22!06bN%{dd3SUbpxE!K3&H>!UdQO'=U~w^rBg@XLt`-e&/6tPEf-k4._!(="],
  w 33 26 0 730000 730513 70 3274 ["J+o=pr0aUu%jF7-(wB9^v-!!6~a$IQDPZ4gI1)43&PZxRW;dn-,]KSwPlQ!?2a#x","l:^.*j*-4C-GYS%]N!*Wq5woUFKW([v9lryA4fSO?%nRngJ^=:Ce,$VE:z)+hsf3",")5{-pJ($jQi@8V]MO6}n-O<xNb_3j1a5[Gk,v`2}O>#12XTvlQS<o@w'53(ek=+x","-l+`!RM(`>^}TiZcvDfxLWucEdP0t{C(VTlV3q-.xNH<UXMmad57h@ZLVF{-y2@>","gu&eMh%wI<]]Be=Pn^Y>f!I4eVA9e(t#f>j`swop|-Xak[vHmy<P4@4%+<mXZ^Sd","e}@#?H1L8k8:*xVBlgj%Df]M3BET>>JZFURCB=Q@V$O)q}3_]8&,h~]."]]

private def r33_14 : List (Chunk 33) := [
  w 33 25 0 740000 740512 65 2927 ["y!)'.#kAYXooA7y3PNJF+joHgI,3k#%Mo%CUCV7ZU_8`G6jg@:l%}@u^SBIX!rvp",",/8j!J#Fr/tviX<85@Yi}U(1|~r*TkJ]:6>Wqj>T)_I_=^})kg!|L!q`Ctq-m<(!",":NJ@:XmKA}m#8{J76<A]M=2>M|dT$-BeWEB7LH({1'`d5_ydVbMoL`GnwWYJND3{",")+gm%(y^,UP~EDdl>]ibq$01Vog:5w^__WENzs(|5#8d+)SRjALrnsV?1[by]eHd","ZfF>kxhe8ZlslJ@:nOX^w:9[LVA,-,;;PU(.rTg5=Ifrer_0fJT7S]wuToqx$p>>","#2Acv)z$oTE4shBMo$E6{&jdzb%3MxKbvI!ip.yDGwIn>k"],
  w 33 24 0 750000 750512 61 2639 ["vVh%3sJYLp<fzFXF34dh~_lqs7~_:#N.,s&sH.kU/|%jSYV69T-1[OgCm=HVs[el","FrtaoT7uoDpG/*++)RAhxM)g8zl`8399s:Ruv6p@3J7yxEs<N2hNp-74@(s'a{wj","r2i*WVxiWhtm?9>.Yk[u|Yh@k8pFxO-D6YXd7LLziLhXB~>h%a@a;*OvDBH9WciS","eh[~Dl~Z%AKgab3OjF00E[.|5E,E=#aHdH?SXiS3^k5v~RSh}N)k:|{kk_x'P=us","k:sP]c?-M*@+uJwReunpsgW:2fPJ^c)(Dq]M!a5,C^D)w.u{''hj!B]|*MBF)vSc","9:}BAZxTdbW(MG^I'y(K7tJR="],
  w 33 23 0 760000 760449 56 2331 ["*^TRS2P2.T0o:.]wdkk`RcAoL^7y86sh/LdCrL#=;l1XZ!0D40WR?gEAt[wdmD3x",",pLXmOEdPauy_!gjhCBXu2&wt]#PYssYGRRob->;2bM](aRzXW5y)$iy5(?I=GT=","%c{C/]*|P#J)Mp&d]b]z}Z@V3)[0{8m2qry:a>ZWo_!2v2M+hH;8QE|zG|RKJb2t","P8'I&8RB_y:X&c%ozzVg|n-sO5W1K-WhbzFCLNG<s9]S5K:X7PLE_=!1^($#Yxkd","k_I.d^(9g{|}BJ$(}:LYU$~wYm(r)7U!%i]00tfQXh1bc|H.Wun>{;-<W/tY-Gt'","9|3!=,*I5&wiK"],
  w 33 22 0 770000 770448 52 2078 ["{nx)[;Rdxj@_c&c_p+OHzTyhj}7Wk=V?0Y96J`>)YGG]6+^wOJ-R@26c>#MkvxvO","|#Y$s5h_|>Ty&xrV13AO[VRUgBo<ya</~Jqw$dNY;U*gW|Cl6vB)Sql>Qxd/f#l$","*sh`9)Ab~E?0;1~Eo6*Y]K'2#Z%Rm$Ht;d1~~(+^:Ny)E5?^<J5'@Q_f)!]Gi{,@","rPed7z;D6'NS@q?*N@K-E1z)bofz2@xWh.>b[tmZ1nMcJd{xN_p;>Sy?U#CX|v.3","0FZ8(iVp*C83j=B-?m[EmtXQ4bvc3lc=lo5*?P=;rL*p^ia/5LDX6P7:@YO[OM)"]]

private def r33_15 : List (Chunk 33) := [
  w 33 21 0 780000 780448 48 1843 ["R'i!@j8j16>[!)!om>.DFHP<.%u_f0@ttwj>`A3y*RsLM^GkQZLP!yB}ti0;gC?8","pJR35cP<q;!U'9OxV')!-(jGXe*.w1=SJ.9eny<5pQEGXG{b'=={sQ[q3]kl>v_s","hAKTt'q']Hql$!Sr'dE{1]&NKX{kKHy4R0KTqUxzaThnwQWEBaS7u2;]2O|N;FFX","8)8f.r?vDRt}i%l>=;<@k6fj~q1ABD-f3#+VC-vhT~l$#0z@G;Rhm+lUXUS?j:9U","$8GEW{8.6qtQs2'0@ba(zbU$`4Vf57~k(^9V4"],
  w 33 20 0 790000 790385 44 1621 ["'i@2<PTE`7<dqFOBs8BnIsAbCO0AB~f%`Q@T.qI@0ndN5JqX_ZU&4G4Y&MOn%hNU","s7jGUf^[eykQx^H+YMEw[ES>n`xj@W.]ljdM,af]]L^_!^~%|H4^mc?1&?Wuo})R","{3-4P};H_rr5u;N(DJFcCY@Om3TN`9bkXz{]9SeylIL^w;ia|*[*.^afx!EP'%7W","PthQj9g8k{ZUkWntfIY6ysZco?-11aWO/w?{d2UWv[&*+[Dh,[E`(<^aVO+/L0/~","^~lyhd4B9]$b-Dx&hpLUq"],
  w 33 19 0 800000 800384 40 1415 ["?JkBA8pT+PvoF&](-B!EyGm{rK^5On78%TQ?5oQ9$D*McMP,+|7ID:|)A'z0eCF5","idUKS>sCIfRg4UQnj!K0z?o0RUXf[[&^OUjrsf-^Nlr&~')C]6i7%27;znx37ZW=","fTmy);ep/_/O1P`8+O4>L'-$Bf9BP0xL6T`g2ekNg)qnmblDCNGwBJ9Fna}8:Oad","sgWO{Q{*Q0~3k$1l!t$JTnrgK)zp?m1#2u0P2~9@f.h-]#eM4EX0Nfl!YajD~A<8","5"],
  w 33 18 0 810000 810384 37 1255 ["/uDw[]Q2&#d90T+ti-Ew(:!hyQ(xiF{OwAH2_Anh|>_$j{9k.9hCm%|EFSCE:L@E","7=DQiIX-Ta$'6iWUZ,AmA{/[N>,@F}$W=KQuKL{S~NRCrbBzA-T&@A;i%rjn+GHk","6>F$;fy>K8NSI<M<P`(uS3Z2K{tVpA+#hU%2$874$}r]-)KWjtAOi',-sL1ro1^y","$WXr/%d>&&*>p9h/J.xg'yDk>-0b}4>jm}cSJ%N0u*"]]

private def r33_16 : List (Chunk 33) := [
  w 33 17 0 820000 820321 33 1074 ["d1E57]^+4LPe~IV`oX@0$vLQ03WGkq|{.PVoeF~?V}K%>(X{Ehp5t}4tKRrvGxy6",")'(P|H'LZiURbXk:0t7Vh02$3]UQge`L^>2?Zz=cmz0=TWJ`hF[Zk|!e9u|AER.,","%*;!Do+s~<qKN<k4d_D:BZ>U?Q.#3~0m#4ppyhl33c(!VaK*]A]7bYQ)[9k4p^3a","xVMox0;`&Nt:7R{9RF<V7"],
  w 33 16 0 830000 830320 30 935 ["VWV>:7$T]akK<f6{-VggAm'Pey;e?Wavx#.H]?E,>~>BS;]Z.X6}NX)c=hb}9%f)","1l=JZa|DJL5oScvms:2f:YBxGv7fWSai@bQtWugW#TQkPutqSSuEXoXRov9S&^{k","J(nepTQxdvO&z(EY|#U{b*n?/;n]@q'a.tqE.)mxedytY`]Tun2r;]&rdw<,,V&c","5*@B"],
  w 33 15 0 840000 840320 27 807 ["niXsfIae!w{W|UUK6~y1t(s}=dDBgCp<.g$2E;a8yq{8y1ZsvvdT:-(3<&*dH1x2","u/y-jXg7>Azh.uT^t!t^p(K&kMp8Y6~|1}=Lhfn9Fs$F!BQbrjkX#u^:N|n5O)9N","$zp7n@own;J-h-R](I]5W0BO|mL9C{A',q)q?#5O6$;O1"],
  w 33 14 0 850000 850257 24 686 ["`5W-{_3-h#PdiHWEtWfF~x-@PgY(1=l8yI,{F?sWz28akf,8P!;$@}F?]x0p6UZ_","4!)w]z=%C/-R]t(k-tGJH=BVfRXS&rWH[Ryp[=jf$^'].YT$YKi8F&?4dvzjr|S5","#`z1F#C~zWCx-/b(zcuz-:i+J8KE&"]]

private def r33_17 : List (Chunk 33) := [
  w 33 13 0 860000 860256 21 575 ["&zouV.BBL_O6vH03h?A:BqQ6%u{$aG)a)fT[r~'rUb<oo9.DXlrS38@Zq5.N=!e7","W7{a:OM.5YtIE3(*70B%OER5`cXx[`QVFq8@DY'a(l1Nw</~89g2h:mOd!;%>++t",".Abp1I.tYB"],
  w 33 12 0 870000 870256 19 498 ["H:yFM>qj6NKx?@1K;YO*fVj6FzMxgGLA(=1)lqqmQfT[Z&PU|ux'7-?%Ecp<PNIj","B.vRSA`Fqp'`eAU?D5E$hL*;L2A?@C>ERd,qj8?TxbF;_U39:mHcUs%f0"],
  w 33 11 0 880000 880193 16 401 ["(sPBGSgR|,ND[PMoAyfmBYT<Kh]xa`Jy0/2x'TRT4!s}OJhN&KMWVc;1B]hk:.w7","$$MpjI{pPLd@c^r{B05))&$g2:C++<kHc7BS'i|"],
  w 33 10 0 890000 890192 14 335 ["ptRqIOp=)f^3)6Ol1%hN8uGLel0o$XIG/@:rQc}*6VV`Uf_PvoXM3?C*1c^'Wj:W","(U`L%PTPvvrp+upH]qXP%/v!i9_a"]]

private def r33_18 : List (Chunk 33) := [
  w 33 9 0 900000 900192 12 275 ["ld])Ec1/[-a$Lq'.SF(s+^dtB83sp~RehEo|F-7dh.CRc}K<HxgY[*R~(VhkJ4v2","5He$fs8.s~c"],
  w 33 8 0 910000 910129 10 217 ["MNP3*}JMg_p^_yvW=OnS0J9/7XT%T3SdI1rl^^Tu(Iee^)'e&/q]8C'F`P@>@2)#"],
  w 33 7 0 920000 920128 8 165 ["<.][@A(:lI%>H#XLwIA{Du0J!kZnA&+hUvKg:{`NS<DJgBL[bt"],
  w 33 6 0 930000 930128 7 137 ["%48r'7/v#5Mtxos6VC_an~bKk3b80PosvUMT#'?j$mh:"]]

private def r33_19 : List (Chunk 33) := [
  w 33 5 0 940000 940065 5 92 ["n}so_Wet[NW_TfMV~-9ImI0.GS1dm>"],
  w 33 4 0 950000 950064 4 69 ["Yj#QoJjLG}t^*y9e[Xc_PQy,p"],
  w 33 3 0 960000 960064 3 49 ["%ul>D!t!>-nMoM)0n"],
  w 33 2 0 970000 970001 2 30 ["#,93%e04X?qr!"]]

private def r33_20 : List (Chunk 33) := [
  w 33 1 0 980000 980000 1 14 ["+boen"],
  w 33 0 0 990000 990000 1 13 ["vG,<n"]]
private def chunks33:List (Chunk 33):=r33_0 ++ r33_1 ++ r33_2 ++ r33_3 ++ r33_4 ++ r33_5 ++ r33_6 ++ r33_7 ++ r33_8 ++ r33_9 ++ r33_10 ++ r33_11 ++ r33_12 ++ r33_13 ++ r33_14 ++ r33_15 ++ r33_16 ++ r33_17 ++ r33_18 ++ r33_19 ++ r33_20
def rows33:=rowsFrom chunks33

theorem good33 : ∀ r ∈ rows33,good 33 r=true:=rowsFrom_good chunks33

theorem sorted33 : rows33.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks33 0 (by decide +kernel)).1

theorem mass33 (i : Fin 57) :
    bandCount 33 (i.val:ℤ) 56 14≤(rows33.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks33).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 33 (j:ℤ) 56 14≤mass j chunks33))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total33 : (rows33.map (price 33)).sum = 313260 :=
  (total_eq chunks33).trans (by decide +kernel)



private def r34_0 : List (Chunk 34) := [
  w 34 56 0 460022 460651 100 9785 [],
  w 34 56 100 460652 460903 42 3972 [],
  w 34 55 0 470021 470645 100 9523 ["NtUC+Z6>R^`k*=T2%fW|1'CifL'@]u-FPp(xk%Dp7+]t5'#9L$3R?ZhU@3l.{O-&","<~+C#28-(h/>;0CTxWE,,j5C-hwGDMp`45;=%oz~P2O'9;)6m,NaWNn`i}[:Hxj:","0{lvTMbDQ#tNoP9{|x;xvziRq{I"],
  w 34 55 100 470646 470902 45 4108 ["[x4+LON[^`zB9&FToMB:ROp`5b=C$=jK=<:pnuHm:nEHuzXZMY~kAk1uD^(LO4/O","%|c39[X>@CYS"]]

private def r34_1 : List (Chunk 34) := [
  w 34 54 0 480020 480589 100 9275 ["nv$'CQC8(gq=gtIY}BV5],b]ve-yW?jq^Sb9XHB$ZMw#}ktNIek@lfsG&N63eWfF","`UvL.#=QV0>TGe%@,I0w@jN5h~BoEY0-9NkENtkZgn7C[nZXU{1F?Pe*FY~FM%On","&`VwqjD+|Q'G*U|V.~')BW2WxJQH+}L(X^`5qDQ3FN)qTtneob+P,"],
  w 34 54 100 480640 480902 49 4360 ["!avwcy9mS*ypxP/d;c9dphqL*jLvv'9,q1hgs-|L*_:K&ru3*~0ef{)~<$o'R4:k","WZ2C`QEEPYb]:EqMx(V[Chl2`|>v(;D2M"],
  w 34 53 0 490019 490584 100 9100 ["}n~f2=8-E3=Rvd!e.,}q$aIdZhQV2Y)SqCf+D=U_chl-l`Hd`!NLDeaeP1n(JeJ*","u5w}jkxi8B.[3(!)7)pvY{S`'WYQwk~DQvGIrf?xC4!_u`%Y0j3V{HXkk8gz(eS6","&BO@gz.y,?=`2k^zCnV![7{Pz6~8zHqAoRKH/$oUiNx[rqqB_gd1<CHiAqdjTn!B","&Pd:E{,#3>Cxq-Io}lF}jB<Q50"],
  w 34 53 100 490585 490901 51 4385 [")^,e/%fL;v1LE-F(v!]B##,_vg5AX`kv,w:K.f`_zi^Q$DbzbO(jqH~!WacaYag,","f(B+HJbL63MMQq6Yt?+}O-.oN>&37BdJsmHL}Mihrv!Ent3R3B+jemh.vP:.NhNM","&"]]

private def r34_2 : List (Chunk 34) := [
  w 34 52 0 500018 500578 100 8948 ["sR}nx|H(x;#+*pI{eZEQ2B%^rS6B6@=RsyM#k?wM/kA$V<V]vpuDrJuAgQ=L$:j&","VuQf+DiaSL@q&qSX].:K=FBw7=9*ynA^!uOcpomazGl-htSo`ybz]IFvR:#h?MH6","7AhxS+-7'IH,aYS[.-::dQ[hExknR|t-J5=mqh<7|Bs1%+3]MU.*4_PE{x4.K]'C","f%:cb:'fB;rR^&3P&Up!GHImdaw?|;|HojmBUl6?#E3f1T3rF6i;y}KD-(y'}K"],
  w 34 52 100 500579 500901 54 4513 ["c>BzT&i#j[iP|b>1oU;]*+Pk2b+KLD:/Z1r&`_EyDu}:OKEsB2NM,n+%/;k:cLYa","=npP7a(0-L(b:wY:{W_-oF,2qsM<c!8-r=[fne@xvT_FQ/t,`PyAb/FBd'iFmMrw","%exq+!PRHLA~y'/*A-'2XMINhk"],
  w 34 51 0 510017 510524 100 8788 ["uRWMyU%rB$PuVN2ws0?1nm<+rGAQc|]<)Jx+>(`EF5~pNbd[H{J.`*mpdyo>*s^w","3*o^<SV?TW@v%4F%i/:lo6PZZp9^Ux9l1r|-}]R&jDBF/rlZn1IHU}Woqv3(K+6n","G0#Y5aGK~`2TI,mCLZ:*7+,VzolS3!8_j+w:+i=DUgQky;Xd4)90r~QBlV~'(f?C","oR?(CBm55W|E^$<H%@;$PY`;BGp#bgl:3zRh8yD$I7V#4/5Koudo|e4+#a01)^.q","#5WQ9}a^VqQUZ:V>M`]7-CE9.186bR}/"],
  w 34 51 100 510525 510900 55 4496 ["h9:G;tW8r9C&`ecGC#9jHw~`e2{jrW8AVc1JX;Gw,gqomQr},Hg)gP#o2#jWEKxa","9T7x=9AoQgr:'r`8t81dC}:;('92ee6z_,](F>WX21tS@]>P3d)G&}(eNMYK%qqY","#ZN|K]P5=ML9.dzgq$m?;&8%68l.}!zF0Ytf$M$?A)>xGS"]]

private def r34_3 : List (Chunk 34) := [
  w 34 50 0 520016 520519 100 8696 ["ouAe6puC@G0OI;OFS:Tj,DT6&f?Kc]W0kJ}1~#bs>NF:zQ}Y9WJP1E-8Y4,G2%96",":Bs+i?Io!%sWTaS*kM0GfKXPqw'Xc*2NI58<29<`zPQTn,Db8x@nU:!~=#`+$t=G","!`r9JP=}}J}y|`<LR8o.k<BPO/)Y?LVXZ%>n|IA*ygZnU>EMi*}tF>RF6^<4~mfR","s7vi1*V7QpMA!y~{<d,rI$wtwgb3y.b6JAT<S~DD2Md0B0rebusj`H9D5Pu-@%d<","#r#BgcH(y1ib{Mhr.wh.n^EC-a)]^Yy&wT0Z[?yMQs>hkpo^q/b7R"],
  w 34 50 100 520520 520900 57 4520 ["F9F01-rvp*d]@JQU<^RB;oO';7d:qD5.?5b:]M7)K4ATGdsRWh.{Q0A*){wv0Ym5","'W)?}6-{~3'H0w6/4RH'~1wAmz,zo/8U%c;xuf/a,..@z}23y@B~KWu=uf.z^(P8","qv%NyxVAtk1Gk(BTO`<!*PZO]d}o,071]u$JIa+Q/?r&b(kp{0W4*e<9[<B'r/oK","##$"],
  w 34 49 0 530015 530515 100 8580 ["Hh:AY{k(N^`&bO-/WTx.)}dy#YM/ab1IR=Y{t;`kvfh$XS,Q.cpw&Th~&:aJb~1V","v9TP:Q:Z~j@z#w`%}PhS2xA(KnkIm:oZ$~9##p#rt*y(L}r`!|@y26gS>qLtaG#*","CF5D(y@dB0,(Y1Ofr5H_WF5?*bB='1+;tKe9U^Z,o'W^Q,^GRMc|#oW(82LOwqW[","mFy~mOrQ){kDSB7EuKu8@{Um$KC|'c{K@U-Wk+KO@}b(dM]ZlI}yb%t(=^1px,bd","GL}Anf,jJt^>|%qnUYA,z*FFu4racbKTmpO|3CoRClxwIzR:LtZ;yPNh?=?PrZxK","$X%JPSk~`@%`4$W|p"],
  w 34 49 100 530516 530899 57 4403 ["<;p=K0LTZ`J6b>3{pd3U>{b&6GB+2?D@+%^H)-*XW'{z~SyeiJW)AU/UG6}bl<38","wm=ws,AEBeiy-oWbInGyr>[mMQsOHlq3cYjY^FM}I6<U:yJ?pf4)TF%kdM:@fS[b","6;vK$jW!6Dvj9y7F_tF}['+-uPcp&o*8PLvwtY/L<]).@[ZOe{Oa[8ltjjEf<xv2","J2#Sou~NowgqG:6%0W9"]]

private def r34_4 : List (Chunk 34) := [
  w 34 48 0 540014 540461 100 8432 ["r6]>%(pp}bQLQYl{s=QZu_eZgmc/ri(IUu8'(Q(Ue2)a/f,@*AY`@:_n9(PH.}'>","{qK[vY$4xLvqf`SR3ZBjrbv]1PhKVHb2Rq-J:%j&!2qOl+S-'JgG&w1ZS5UM{B7l","7~9Q{Fn|3?GJO9moMtuEXRjHy@oAI4vbqG}]t5'm,%<ZagKj$Ku3^|Fy.t<J?`el","H9.b3!R#-j*`1p[cB_CoxGWwvc0xbE?bBddei+Oi$S8e5@YN(._=&=)-HbDTzpIr","bdy6&8JuGj&H8j?FK&Rx6EU=2WFja!h>uD2Q]c|@{z@X]_{6|4]Jd=Y[~ZnW]Na6","&Ej'qRtJ*.ZADAkBZk}VWTXUwT6]`ud4e"],
  w 34 48 100 540512 540899 58 4412 ["T|xNM+v+1ClyMI2klBNWnOQ*|'=A{6/4;49fx2A6LyBxwCX4BWb,JY,u?mD%Bs;7","|?:j_]vsC+0PD/Kj8oqs;d({~k%m[icRl~b5<-+|.<2YIu0quO%'{`VZF5Q~H]pW","A%`Q%ke(005$&i81sE;chW_<75rhP;VFXU:[N!O}6&eV0*7R148eAR[poX_|f@4#","%RDnLZ2u/ngNzN04PqaJV`6P&Zy5z"],
  w 34 47 0 550013 550458 100 8325 ["dV@G(8V)Ju75/L,`R8<~w0T~#-[a&aHe-hmglTK.S-ZN!{bVH:]N&TVCOO4m2|ec","|[rF-TZqMIiOai~)a(#rAuf),O69-VQ0xGtOLCf8CV/[1p6b|dcqz7b32-:d%;`&","tJ%,mAa:7*+3C|%.LsVRbgNG`Fd<LWrw/!9DM`m@w}%3+TOG<aRnR9Q%Sk|-FW=H","XN3+v==ypCbO6#l~3ev)RO)>&og4*{9!y50XyD3e6M~kR0zj,QbVkF=^g~CM#WRm","hZvoqCUg~#gg;RYXG@MwZ+hqn6sSDiNRUw8*#?RTTU!g^~lP)Lt92k=6=:_Aij=)","I-[C};MjzB'uui&S6d-+=g!3(G*diGo"],
  w 34 47 100 550459 550898 57 4215 ["@X^p8}K|CxbBI)HPq;bRG/n{2!%z|,]9'&|hAe'sby'Oe~*S=RU$EY6GR25wq}9C","@wxgQm;#_z/QhY44%:lv|&YgKgz!(M3.r/$*|`TT*o^cT}j`3U1%OlXNbw5Zm`T)","je?m@NO0p8dP*''R'!LTLu$I5Tnp2idi,qco~q}VK1PNY(~WWNb.*/Z?QkmZEpUP","ZL/+ixK)M%Bu|33.%xM/:3KL}6iU-w>tZ8mKi:xSY"]]

private def r34_5 : List (Chunk 34) := [
  w 34 46 0 560012 560454 100 8222 ["S)D%e#p{z@s/qXQ:tWT|=b(=GHtQ8-,X^C)3@t@UOD]^`@8~96!E7}NKs14X<p6*","=EayNo++u#UqU0.yxGkkaISiD*]4'[!Rd7srwO32OH4@H=OatI6qa^p3$6}XS>1N","CtA$rcuHcGu+t/}mhY$',!~rfb_Dk1(ea3~5>pv+>lN;WP([PNO^j3.jL71)yP+k","Tp,<^4<Jxi;*k}_.9JSmj/jYBZ/m]j*qge#;%^Pb[-zCV/m-+ogPn<H@J<e2>v4'","SW/_QeN2Fl#gr+n|-9+?b~iFKxdh5E!#o&yd%sS''FZF^DEL&u,3x4DRB:eW'/rp","*SnaKX=nFYiSjCNm!SS2B^J"],
  w 34 46 100 560455 560898 57 4105 ["VwK^N.?q@EK7S^I!Yhf@X$(b3Ywg/]`*I#Nfdl9-$q2Bx[Esa|W+(=LMuPJf,hAJ","q(Yz*Ah0DXl)6[,nf5.8<gCrEnp(azM*M<1A>`3faSI1|&V?x@?&+|76!ay%3jXb","*@-$@$7q$O/&pC[m^>i*,eM_~i0aoY0!VhV4b}!6grfcmfb+Dm[iKv:$KdOpPfNS","$.tR)b0f^Olz)>nn}L8[S<{^AjhKHU>OD%RfoG^eC]r*HAe<`|:R"],
  w 34 45 0 570011 570452 100 8093 ["rJ{7wd(>-@W|Sa>!~B*2iSL*;^o3WqSm9DQI72q4)Zg.]78(j/*&?r'/C-mA>Td.","6.e&jBNg1eNC9rvDG(=}JaSFS?{B}dUFZ2sj+QWWw=%WcfR?~R~A!?j<ulz$*]sL","gyNn+`Od8*TO:q2q!tc9R,=f[WI3&=_G$uJW`vF&,huAZCJ=c>?E0VpR<,cJVumb","I>d2Oylrpdms+/1(:cUliIi5nqXjHH6mT[1Weh';l4XF>:wq@U.vULld;3dRsT@%","Uo?0'^NWlBnTnGa0)px7S+?.#@qJ`Umis<~[/4Q?G2e$_*-5|T297C-)7*O)X@Rs",",LIF9H4w!9*ggp[()-mni~}"],
  w 34 45 100 570453 570897 55 3859 ["}~51[C6k,fGj{F={HoF$Kc%hV],H*rvK=ttFwF[j@g&jyreDr0X$x*an1svS[-Cs","-H'Xj/RSGKFa'@rC=pbcl6GjV.RG?F6t2T_r1Yk7`,xfdbK-u3Zfc6bW]!'u&TIK","ZH#)X257HWF~<f^fXb='A]1ZtQ9qyJUA]V]`Z]QB(+@G/Y:'lS{x&,5@pQaPlz]F","*-?K1l^3Lg$yP|vF4{s)Vy]wPSUK;SZ[Bv9P!16jVFa'G.uLM0jCPv"]]

private def r34_6 : List (Chunk 34) := [
  w 34 44 0 580010 580449 100 7956 ["t~4597TM.;p'hznDDtTj?oL/7'XCFB*:lcO';pMMy>^_nQfqO7@{/g;=^XPF]K6k","FbV!D(nk)!Rv/'{1wG0glc<-EdITlsbJm)9>.3`/N--KW[S18'K)I;hH{hgsrZyO","a5bCe=w*;KXXWp7bIpsL7{Ca{xn]zhjM^PR_;(qJ&~M*7]94h%q?@8:6IOLNtS-`","O.V6E:=MMD}*O.{f^`FA9V=Svx*x0~Qr>nF/pGV~&Rw]`WZ!}]6G3,;P,Ou$#D,3","m7_qg%i'yY}HL>0^E8MadKEaW<FYTPGbQ7v!L-b!`f=o8+w9l{;a9nGl&+d@zV4}",")d@CF8v*`Tk@CZEuBU'@_|?t"],
  w 34 44 100 580450 580897 54 3710 ["|jnF^FNq{{YP#O/_Y}4E-9!NMrujVq|6_|]mLU1oY-s2kIWi)w0J<dz)pDuj[150","[(Jgt=wO)^5[MH-[}{b#Z'dg[rp'VeZwa'K[0:6zBh0io6B;GXvLx%AcEl5TX0Bu","K;)ier.wL&d`LT~-S1]/y$fL^h59WY;(as{uylb5CC+ct&}3h(mx{nJ^zHKI7bR&","#<,P_0ajt?8_w#*F8.Q7>>N_HV91.!S:~-wZ{5jR]^y*V3o3mUp^"],
  w 34 43 0 590009 590448 100 7802 ["2R0VR<RlE{VJATx;c5Y(m[<[)eC:V0S!BeK-PdwO{|-e^(ZGi}tuq4BI(?3L38ic","pf>r,Y[4o|oiH*ViX)THy'b5*2^qD3~tT*ivbI8Ta3i<ks)|a'v:V:=SR/#L'=4B","4Pl~>}4y/m9~yUI8v!F,<^'Wo4caU_mJ<v$L$K;4vDMAt6gHFH,0e#yN$W#<X@&W","K@9kw;oMz3ZY|H/ibI%[lf|jMxX#iC@pqT4_|/H0GB<lwug-YL}~:@)@pj}N2B1Z","6EmN9gA~vy,DWnMo$U}ujaA7`hknb0^;Eyp'dD0chYgB*HF4@3D[NBqGzdsHe'0{","7[36^6t4DJX*FcVW:<Bxpx!ow"],
  w 34 43 100 590449 590896 51 3421 ["u~jmX2_ySO'z?SIgMV>Yv$}_0vK6oZ26ZwG)W3LHg%_*HSG+5s>8(IC|qf}-:HqM","eF}3%i30p3sB&+]U.jZkl~I$xj6)lp<L3EIEbK$kHyW{ncCiUQZ[hwjOnTm#Cs<{","$Le||A:U[@Ri);nMTFfN6gr?Kakz<])AQyl9,jv!=+,JsOtUuf6Ix$FyTX5XrmOD","'.^+WgK3!yYv'WRb5;PUaegm2D&)pAVLZqj=U5K7"]]

private def r34_7 : List (Chunk 34) := [
  w 34 42 0 600008 600395 100 7657 ["OXv!=!2I#/4moaZ9;*'ix*WjBfRiZRFJ)V:ZM5Log(V'L7@`{sE`rhpsY(P0wR9g","2GB#~KePT$*/kq_F()><)rn:9x{r7GJUW73{z@aUbL~2g(lvZNO%c7V$L2%S</4e","fd*/ldOV;9^vZyh3AqBZFU~E4}j!o!GjE~K&[OnN01(P$MLC2UgM=1@%!@,lrB_}","HryvV@My2>wn[g,Lioqugf23?=~qx*WKmsY)L2wpBg?$)6YcZjiZ6~,Yfz&I0H2-","^4iUbFG+mMIP@P7HVsN0mmI.N,c{6sY/k.%&}-Zmk!7NlyF}JLT5V/4C+2^/Ep?(","'Okv5nKZo?jZsqG6<PFhq%f*dJkA"],
  w 34 42 100 600396 600896 49 3213 ["x/Pf:.`;fk^VrewXQzDdm9R1,rV%~;vp'63vuA1O'F7j!5&t!3fZ#NGP;5B|!NSI",";k#JuQ'@&g(V:A'qwBMc&z^c)9;q2'{uTn5;~6iRv0aECT(#a[kOM&-7QZfFu02E","6d:*q,6b-WT^2:.:sub1<g|/Hh*s73$)L{!&q#k<;WAx'JC0md&hv=vRrC]=F|4/","#FYT9,&Kua.zhk1s6Qm`{/XeQSU&H]z.FZ8"],
  w 34 41 0 610007 610394 100 7495 [">sDmwc'$wmL,wA_=8Z~pE0|^Pk2IG!+/P5t.Gl{8?!/.u&H?cBILm;@X(#*x>j*Z","l]!#2Jq#$*PhPeq^>TWM$IaaGS&#fX>=q`;vI(}qBoDZy}.^a'6rQ{ncNyu?q`lm","k@zA6|BV='ZY!8?BiB}%w2~Gy:#V%fL{7X{d*X^N_S])(r1cKU4A%A/uiU%~(sy*","B,0.i>tam|iAvm;Pz3Lt*na~<jJJ=kyRS]T7HVH[qKNwKK?~]p}Was(87y2$*t%F","nfPQJ+e2R4o%1_Js!R>'vO06A.g^|)8%%Vm.d-6wZCI4TlVrO_oz5oNRcGsj6@>o","p3Q@|hi,5W_HU(`}(z%BMAE&'GxUIMT,Y:A+"],
  w 34 41 100 610395 610833 45 2872 ["'kKP'_@+8F3RZdUq`#'W{-FWx=,PrUxvN1'HH3me_)s{Qw*Y+>o;_36{Q&$1-v4>","@g2QDb4F^hK`Y9fsqn%*7?$-$Ar<h2beHl+}t)7VZBoGKcr/Y(ovqCC!EcyprP8!","81g']IN^cTY{ch4LP@W247lZ~tEuQZ<4XDK*|9NuB;YNttw%M)~+=~drpO7yC<t%","${eyJTxh~+=91>Ni$m3"]]

private def r34_8 : List (Chunk 34) := [
  w 34 40 0 620006 620393 100 7341 ["2B7P,e_n`<rSQQb]X}vAW*9>v~jw8MO(D+a1GFT'!?1GtdHF3'+K5by%gds/Rl2Z","&/DRBPKH`fIV$Paw/uu,&I|E6-IX[R]uj9~,DZRe:Zl%i-(,THXZ{W(pz?0LK$5|","(dCJ~py*TxtN$$twOB43O;e2E8]E<{[aYH;K8<pE~3*q1yaTq7`4d<}X^&UY0?.Q","bL^rxub%0sdNJ3]%eDd9Shpi-Xd>gnX4xZ-V%&IU8*l%iy2CRRNgA*WQu@>b6(=0","}dttL]bl<NsD,j-u>k05k:N5{%t:eEe}sP&P%)_oLsW0yy~Ijz^$g<@iZXnVs+FN","BsZnA2Z8Xv$%Za1?~q)g.$HG|,l;:M"],
  w 34 40 100 620394 620832 42 2610 ["uCu0%[8H=Qu<cQfwEKA_F!OJHRCZe'9[r@oHaJ=mIq)6.p2^sj&G%[Lln%uOw3y.",".61!4_p]tu4zMP|4CL)u=*1RQmb>5g4'SVwD@BD?9{fE.h,.A}T#HC}4^&]k_q,7","|E$:j|D29.O?L]EygA5e7v#k$K+.Wt89$x5P(R2q>8#bKa~S(W[ehEopEz-}O(oX","%%srj{c]<"],
  w 34 39 0 630005 630393 100 7151 ["uJ5:xkQ7Gkk&jr!$G)PJgneY|v_@1.X!p^*d4XPA5NvtsI$h/<vvt[sVRPli=o)&","vNRo&!&UbSTvbL(ex?OT4x6rOp~?nE)lN:7>oM.^4lw6'B8M[Ws=5{,-_m8X;PIJ","w1sN&l0Gc@.)wZ#XsP;`,!#|buAt#?w;j/Icl2'l0%7EQTC>/5'}[7_2@R2oju?m","7{0K]TB~~_o$6sd.hP,C_;4TL~WH|;o<+YOkB&(e42`F#/?8R?ywqpq%x=YAfb9e","/$k)y$=4G8de!4I(i?E.C'Z{.;~PxqS~)KPzqX17GZ[//XRkBkb!O.Ms@3~pcy<O","iRB|w^V)I$$(OHhjqO[2]Y-}h]q6.]kEidW_iy7Nr@s+ZOX"],
  w 34 39 100 630394 630832 38 2307 ["6pA6(JM*=;|QK-,kW34.>=V?*b!9id(w<oa#0w@*t.A(u6!&4e=TPz,K-s]EoHS*","*WWw]ofkgBmNXMSvPo/VS34HC%pw][5QRD0I.5TM2g@'F}KL9lDv}M:e-nFg[[#F","({EAP=)y/u}LbQpcjjwQ/L[KQ`[b1,VpK&iZs=DhAV.#mr2w!%b8QUL"]]

private def r34_9 : List (Chunk 34) := [
  w 34 38 0 640004 640393 100 6970 ["PXwRXM~3!k5b@y:r|J#94yR-}vg'{GPY_)cnkW&}tTZ]F8L{(p=3;!}kVqT8GhDc","cNHKH-B%i.B&^|F9?1LlUk[7r^xDO|IqlnEK$t<W'w>,Z[1O#CP8dg'@XYKA4mpw","X8&Rn|M(Er`<aMo`Q$Xc1R39<vXmG2K4jLt.iFyzF[g{tNu_;rI<$c6kHjll9Xxn",";cu$rGWU$EJcs@.Y(E9e:/Vkp,TV&$eoN(pp_^`FHsE=`DvwLb>8os-_16s<;`;u","+C,9=)JVkB'^y/iws$LN4E>k%2xTscSWaKk,-j9)$|AwjVTD.)X^D;/ShrArWF,}","%;/F.W}pvo8#j'o7.<PiI^)$vQ%Wv{Iv0hoM..Eb}B|E"],
  w 34 38 100 640394 640769 34 2015 ["*U8WInr16;^PC-SCvUjsgi,Z'W1hJy[(Xn;pdVX+ura{XT[raw6}^Rfw+gKNU$79","2,c^kUs$|PylDxcU/1v)|f~y.NCPw|OvZjV==CC/kyE3Oyd0Sz#VN,pf}v+ia#sR","$j(t<Z}=HDIq]]My5%:9MfVhM(j}Kf0/#4l5C+(,u:7"],
  w 34 37 0 650003 650448 100 6761 ["[gJspsv4/.E_CsYiEUV('{{Qm&?UBddg-ET6yLM`myp%'99F%5niLoS<s[;c[/5F","anl*Xr5|I>ws0xU%}uBnF&hNzz)Nm,FC5<9>&z;0~Z>0?f72cz<~*{Yio#]?*A|H","|%qo(7TLk*)dtXzRz&i@I%?@V{eW#'1)PaMKQ*~L^Sh2U[;1%YY#7yM,ZD83^O+U","Ao%({K5PY<`tp@Th5xZe+V:L:JS]#.=;e_t?X,FbMh3I85=e6a~w')9SMQ^Ia`bd","{ivQ?`OZTK11m*G}35{-00/ig'XF!4[OZ7={z3:)A>.JDoJyZlQjd@~kEZ%/0h,e","A=ReEe_{6HU?jF:hMuI1QsfT2qT7'76?4j>:k']hS%n9CgTs8hlFK'K?ibvCG{"],
  w 34 37 100 650449 650768 29 1676 ["OegznX>GH^>(Q%]L1q2R&KY}x@G<cGMuJ)==3e1@+v0SirNVe;w0T?I>,H,'#U08","I'y/4R6Q7448#Q]('x:sx'P`0R|AN'Sej.F7{@U5Ge&Gs9[{D7Xs;B-&YfL$kPvO",">I*2MP9t8%@)=AkrM*9"]]

private def r34_10 : List (Chunk 34) := [
  w 34 36 0 660002 660449 100 6556 ["yLV}h(CuM3WnP;I*@vNu@Sd)Y^8<;Tu}eJxU`|ZQ4@Nkbn1D~.lZs]o{gyL3GHU6","r0QslkuSr5n{ahFsP`T4evZ){X`N;n@>~VCot#$q]2w/r_mpqZ'T<B!=hR9f=^+T","C,mnI<#IGU:=P9$EWL7SO@x-{x}]<HWEGc[%+jy2m=maYy0iCLMq!D3B!aP4SCB#",":Z-*KVBD&h@br9-@wL7a@jA)S;zZ4gu![uNY{bxg:S%J@~-FXv((Y$p=M?#9cJ'o","G+3mIgU`]^/qDx?:6`-9R*_u;*Rxfx4^.!y`IBT1`/P|ye-:Mtu)fa}FWs)LbEQo",":y:s`*&A-cs$q';#;5,!*2C<)?cL<JAk>6(Qq'`bw,s6hX+Imr|s7/X1<F.'Uu`k","%D"],
  w 34 36 100 660450 660768 25 1417 ["*c>Mk'xaa$k^*k'6M<Y+A./iA$5G6)K@>yFs1[etauXMo=)'.tZX6LFk7XiV>(_8",",6.<'WBGf1>;s1]zLMyh=C(5m.?<TnOiN1.Yo.5(7fJf~IH=5WF9dndz0#C@kh5"],
  w 34 35 0 670001 670452 100 6317 ["Jz4R[AP+V`yHhY)?VJ[_iav8`BD&tq$x!$<v%<Pi,@#?(qR,9/^Z@y}7:6zob0d.","QabJ$[p6t4t#JC&~RE4*bnam[WnxN.azL}`#KHW2ZX^Iuge9Zht9^i!hJx:!`@<i","vOYKBMt]{#'vhEe'/!E6CROC5/@dV|^{HKK..(&o|YKgUmyO1z08|,pL03t#m`u-","49Jvwgjy_nw>~&?7BM.4j<!l^T%w/}W6k{VA^HJbqwe2>!p,QOhLeE{4PB?caS+{","ayct&x_*j&,dI0,ACMgAqk;ov>e)Cr0ZTN;[P)z$~TP)#!Z.gpAEZkHTDl'h@XK5","1^O%';YgRH35cx(9i=UYyrZz!D6Q,5XT^UKN?n1:WHqwP`HN<)J.a#LPJl5.ghj6","'>^qGB#1SrtJa+=~i4M]jjfJqBd~s"],
  w 34 35 100 670453 670705 19 1059 ["D+i<bUWftd,Qr,WiT_G<0lXeV~>E873[(vYy(1W:2jes's&x<rL?[vm[R%/z%@,o","+={*|FyCr;*yQ`Z&dq,lI1eZ4}!6FGjIS"]]

private def r34_11 : List (Chunk 34) := [
  w 34 34 0 680000 680454 100 6091 ["8V.=DL6AvM_GH1O{gmXQ3|}7~}rxY:ozml[{Gss:LdIw6>!$qSAQ/2DBV14mP_(B","/=4:w5bm`J:8AC}-3EV5Qk<xsinU#WGkf=ylBYs:v+!59lxwH*zlI>5py*GTqcD1","2Nl|sWR_@tmhJ]#4$SLC-%<<]l[e.sgd~'P66v^|!0Pd%Op6>qhi&thEaES5s.Qn","Z(Dn[u<vtlq8dZ`bNjC3BRqdWE^y[(djdICUk3Y?2q/j}{R:cy(^kZQ?Z1?'2T~h","(eH3Zr0W$=R1mU*{ox~TI^)if|n{w)<&qIJ[>i=)})2N)PS[+RC~,aEl5s.WG>uf","b{%8DW3I)WD-.a$pby0%KF;qp}=XiFHHbn+oV<xT}zw[t(#v!ICYe.u[uFw,[*jI","8ahi?=W,b+AVuiHAoM6X$Gf1L=VZ`-J"],
  w 34 34 100 680512 680704 14 769 ["gmZ-%AlKzz?e:D4g5:q=onU^A4qXM$,w!jxMF]~Opx.w|/Rp$FPSxiv3ue0nDbj2","D<dlECLX"],
  w 34 33 0 690000 690515 100 5841 ["6g-e,dPC'}<Q3m>i]o.'Ky4'}qa|$D?gyFHLjetPM2$Q-*iKiptY-XjQM+0fopb?","PbcHPM9Zmoex.[5u{90cw,L+x*esk_zUtlL.O865'VLdp4Mv-)B%RE=7^$!BgLci","u$bTa)s'0`H|mDlkx(XIYro0xjCj/1bKXm7%OlPyakI%j''^EBcQ>|Bz}C-t,8!A","l_AZ{6HU&Cj>JOeEY$)XI{#!LO#e:vr<r|@zN?::7l(O4;W1VqVmAA!S>9{wCm]x","}hn[y}>HN=qpHTAG(uM,<v%n;e@uxv<y`&Vj;JE`.[WSx>_}RZ/5i=V-^/8QAABK","?m*^v?dypNRHO];o*V|L^X|Pxdi(+OI*!rgROA($a?fk,i411ql2HhfG9#LZ?*K>",">bdXCb:c9$t0rpnM8[Grr!wpLT^Y^Bw);kgo$W))=-#bW:b$x|d]r^Z3dE"],
  w 34 33 100 690516 690704 8 435 ["(2mPt$pUiw?}C*dz@*Y/SXv00.Fx/}]$?-I`XOZ"]]

private def r34_12 : List (Chunk 34) := [
  w 34 32 0 700000 700578 100 5607 ["';kj6~UMYNiE-6Ds*dZDMacB}GMHf7|51^N#I~QG7cz,}J'+b&:n{<}wb/m='X,|","<0lm@.`%&~]6KE;!=NrwxwBO:woeO&]Bs1mB:R%ax104Hdw'}Ov'XH(y]Db[Eh1Q","j*VO:BG}&dv31g:=zHax}2T)$U7nUco4|OtblHjQHgE?sj*I8q}2ZwMLl,$PPI_x","Fw=0kjZBtCTvO~0dfaVpi'1KI*&#,!MCrdO`U}|FKR:nzAtk_[>XBIN;%EayDdK!","3C^$Ig:]+2BQ('h};'i>.L[5r;uQx2XaX3Lst_rq1S[LtFZ*o~prz=[+fLe:e.SA","w',Id`a=qil:}aoT$8POGCE._*Tm~Qp2-g6ON4%T0w8fLy]8jJX_n`g,j-@]VY#t","/H`1&vuPEQ|$V#D6Uys}9M6:L2F4nhF.!QQmd!8M'Vq:AdKW]/HF1F:pl+[Tuf5c","dgY.Zc"],
  w 34 32 100 700640 700641 2 108 ["#ama[b+8"],
  w 34 31 0 710000 710640 96 5187 ["]Ca}bBIo:9BV/@C7?-sFuhv/v*icmc3R.-MDpfn4pKBPK*XNkntf9e$,<6L+R+@[","YM%7<zmu2a&?9Fk`gP{7;gM3!+9|GT-eBX:S}7jwNTNg|zcKP_r1qOt?p(4Dh+'A",",HBWIFdza^Aec_([pl{5@8ot*Ya$K:qqmFwn8e34f2#B&sU0PyL/79rY|`*aQm3=","S*YeKU27QhvJ&C&>7ep_<vG|OQ5K!]fa2/MtH1gp=y&ttwI!?f1:2!2E~60Dz%:~","ld?m%:N2mf7Rub5MkDuhVh-Cu`1NJ+<b1[y'ftQwNT^.H#MmL%8-kQscb5BZXCRr","qoA_r&3R]h`Dbo{EdDy.-o[D*zgHN=b#u?`W8t#Q/9zsLjlPWm@M3IjMN<G,wl/K","#i5KwsP2*j=z-q=~kH<+3/Rnx.wYiI]8/,Tyw)Uq.)VF&9,D0T3]|7II%T>A_-m"],
  w 34 30 0 720000 720640 91 4738 ["yJYd6*JCoKn-Q>!#1TeybD3z>;}L}bOkef93fJ47(0=k[vJk7?z8[OjH$`0ToV,[","0Z1F*TW-_m=iyI>OEhSTTyzN;.)A8X4LkZo5?O^J'%iW|13-^oo=0{:Tl(o^yRM8","BU0X!]4Edr~hq:$YRj)2s%q&&lUfYb(SXfTX;K[Pv%HE@O8W}Y2I-<3HX-JL|1u>",")4D.sb*!*'p9YERTB@)*C1;@d2+J>|cjU2GW@I[w,ozep$Eq=ujd&N::Os#f#Ih%","3bnw2y5Jg{[<Qh|+]WnIx5Yr32EK`&g@,*GhtQ/?4'N8i;D}zxe1vpNu*L~xSbRc","<=:a5(KE&|?Ww!2j|Ze7l`7ZZm>N-3W3WSBKMceBPvRk[cW/Z4xz'_'t.n;)8=V'","BJJ7>F=$|92Zf[DajsiDqP,PHazQM%)(t.@[fZ.[cvWAfj%-E"]]

private def r34_13 : List (Chunk 34) := [
  w 34 29 0 730000 730577 85 4266 ["6nYT3FuTR?2r/BOH{Zj_ey/adMfBD8hH<r8uLD~NTII9Iw<&LB-6Pd,)v>T+P(V#","BjXjQtjPgvCc%P5#$VP^+u]7ZkPRRM[G;@Xr*$/|ZF*epP#Y5+D#p/ua,[#uh,d=","fuwh9mC'|c/Oio32ow7BGr4RnIPn@+4Ou@dL:]oVAwE_hs!|u;Jf+1ZDW=LU9wSf","JZ~!z|D/fYH&/>iq}N#P|yg)V,0JoZ%lvN1bmlSd)vzsksRtt,Q1?2#>,4P2yUD<","vqv)z^/d[{-[~y3QbsU^X+69YbhJt;2^1yTkX}!13.Lp~tO`P#g=_HxdK4I~h~b*","{/h=<~jZ{Q&Bu]`~Z<fh<h#`76wA[t!`]m%V#YhwUTr:]vbaeW5.64|&K4=&!P_4","7wQBx1g8<4krkp~oY&GJ8H{cdE2[H}j.2lC`d]|"],
  w 34 28 0 740000 740576 80 3864 ["&-z~{Ax;9QH:uNvMOytE~n}RCB&T+&s{]jVzg[}BprASieYHFfV587l%LjM8`9H[","$qXgQ<-+SzEQ9_u{q#aH,VL*;4u!lsr7y6G[~[qg>/v/DBY:{WNjqt{m{Bhqk}^m","s6UUE1>v$vKzUSNJfe+]}I1y(DD_>72G@hR@5Q+7vqx5ow%!A!DZEVQnNG-*^@BC","jEFr[s}fYf9rM4/O3$0&EGt[#DX;O)u~*0>[Es.y_TlB?`kEYd]Jq10gpHmo%kOK","/YR$c-f=vqJp]i<F,[m]:wRSz,DN{@pGsS|TlvYj|/.{9=t-HACPJuUJYdz)x>oG","vZ50n0_-*sL?#G*q_AG*$*H+vtgkQZ;`N>NGs/Ny3XV(Q)vr<RA1F;|IKRA9Kz0W","&s3r*=Re-%`@vAi$%%uN?l"],
  w 34 27 0 750000 750576 75 3494 ["C@W,4k}0hs)eg5M%,HDVzeN@IFp`*uU8jl{2cCK,`za2=PVD>vh$N'T#^-}ioJI/","Lhn7g(Y'5?bQr|$J|w{{s<4;&8*[2bdQrc/)-rs(rPsf=,wYtrk39^hPmeA4Bnvl","+`gt79v%}Suavsz8j6zlEST'otAi8s^)SV>s[ziln&47[1d1OkT9g~3jp`rM~y(Q","J#mQEf'`/M#Z}8^&rcmKu.GO2@a*^8V!uxdFK)[of<5~^o44X[@HiA.TWU&X,hQ9",";NW~3*>[m've!)n&kd:.ku8{*HF-v(TnNRsM-kM/M?G?#lg_Y]knBAm*5[`:]M/1",">zBeAhZ1GAQM/_THlBkQ%oxWUYdF!PQUz-b?IuZhi-10?'3b,yowL;~w{x[QDnOF","#ne4ymruE"],
  w 34 26 0 760000 760513 70 3137 ["}cg&4')+In}U2`.Xx}(<oX3j,GW$cc:NgA9j0Hm+Cb;ZY((U:yZXfDC<XN8lNyV#","7I=oRCgMb?#w{;@}Qs)6-/){X[3_4$UxUO$L(d>?Y@X_<{vOqp|~YI?p'XsMZW<'","2KlVCF~=n-y-QMq6JM-x;qOx{:NUnf9F1`~@++=dk!EB8A<egCCC]A[WFCtMOx-/","[)nPB%Uji|Q~wmGlhr:l3MzYh=wu/{88^y7uz=lDT~7L={qT^)dN]SdhL'x){6jE","E81|n{Z8xjQ`S|Z0zSc&]Ne|xd58n2N%,@VD0#j^cq;T},-HyfRFE?bB9|L$14*h","t|unPiV>1B1~|.T=H?LEs5)ltXq<8Z&*fo|Q8%a.+tu.hE:}fSUMv$`2%#x/P8+[","J"]]

private def r34_14 : List (Chunk 34) := [
  w 34 25 0 770000 770512 65 2803 ["jh$wPo>tj|0Ba}$cL~He{H'VdY]jEPI9U2U8@387JD;AR?+s7?9pHul!yU'oZ<5?",":*&;T@Y,&g/ZI^PpX~6W8Fz/hGw79ffZ-oksERsddajI-'|!*o.*Onr2Ok]1Cjwq","1&SjB!|{gXbfoy;(.TV(AC0;ysuwkG?jxf04tap9g(6p%{`*8&0+aJ.1+V%89I6F","hQHy[gK_XtT}I+;E<U`6&<aN+8#M{~db1hdq2j*BbaI}$&y=-D@H'M1C1}bIQ1n(","Yec[qso^qF$[&CQ^B6&^7uxhWzD1^v%N`X-d.)Qyk]Z[q`8RW},~l6vd_!5M4i3S","&c#TXpm.~3WZKW|UQOg0#z12&y~mW+mPu73E;tQhF4{-~o"],
  w 34 24 0 780000 780512 61 2531 [";p/'rF/cB7}^oaatCU*iuBSsj8zjy6K/mG[U`*#p05-`#A;y->8l~PI0AyA5+)5/","x)sfvk[/7*UIJa8j1fb>)k<FyzpM!?'Wv.(CXH7RdzIW-C^v>*>!*lePwBhBMNUy","^Gxnd'(V=pmOM:W?qw|T^5k6|T#g>+9u}`E%btW;4(F)L|t6NCX+eBj$y8whTjSS","BG6L-vnU<j@,!ICbyuWc@m0+l|Zc*fOKi=0yV]wqw~-uY}M&?j!AsU6yjE'%=*uV","nY^^G}rCom5yg?EB}d5?98BMS}M]EJ)2}=%;N;kWJz|KYZYD{9)j:Uj;)CC]GIN+","6ScP7$wN/'2g68%kg-GUkJ@Z@8bkePaf_"],
  w 34 23 0 790000 790449 56 2234 ["fG{chH<nKM94!it~?k4%`u2$R9s[ALfujVAU4pz9:^5-bM}LmjPqjKn/p%-4GJql","~&dV]!z6vmn@1elr.as_T?5+ImmJ^q3tYk#=K7w#RMVzOuBd0qUt;ev#FArMz@RS","~sEvS4R0%l:<7IP1b#Hp!7C90!rNW@r+JOn(I&Vc~9j|i&;o;vg=<yCVAH0CC^<;","KM9)bfS<&Vc)CXuX;s5g~<Ly(D,PsR&7,bS;u/kGr*dZcP!sqN}Tr-Zp@q2n^7u#","D*U|Wcsr>AGZ_%B`]0K&xfyTtJL^B~+l*h{SOMy{j=.|P~NJ|G'jC-H2Z+iaFPZ!","aNGm_}WWf|pH%5M1yE"],
  w 34 22 0 800000 800448 52 1991 ["Q&v;(%kTIwfaMB5yoQ:67Uu=whdBCoTjj=YqwZpC&mz<DR@>ElPLV)JU0|F#|y10","HPECV(bI(##%wbQX$bivf:{(o|U'b~vFHmwdxR^5o'7o'e{#lBFn0Sg&:6V^^n=-","2[#0wxk*m}LiV:~QtcBE48L&]'t6:6/+%Db0Y0SXb1@'xyaF]MhCUK2.8Nst}6QJ","5OIv{LlJ.*7ccV&!j+mOg=1OZYQ!cPl/_vM9t>hpq5H-CHM@xoUP2=(O_~~E4{Jz","[Gq-5IAq|DHu-.<*~brgf@%x.s:CmXa$yX,N!QF0!z`%$c7KzRgeunDG')Bz1Pd"]]

private def r34_15 : List (Chunk 34) := [
  w 34 21 0 810000 810448 48 1769 ["yO3r0OriCN]{/XgYWHZD'&Qsx!5<!Xc]B2n+4Yc42kTD^h#KP[v!5vq.xADN+/CH","X3<7ij}!t&e*YvaqY#lo:x.:GFPle7v~rGJgU{NKpnz?yOdGRmoQVPJ>`x6mR=cP",",AXV(3bs//)isOGUABq-*lH^~>EuXIHi_8z'e,Hz:9A(mP~])N/joP:B`QA#Md:s",">|p*{N.>:x&.R$+*fPIj7,Ve?X@'/Bm(,nY>_1cbyj1&RO*-b||p+x<,wfBmpDa>","#|x/A,ch/O7WG_B+#CPUO=pUj@x/gmx)2:4=4mWJVtG/!"],
  w 34 20 0 820000 820385 44 1555 ["w+Y=i?n`h*CHbss2B:;?yAHhDEI]A~#U7*x(epU1[oqEqFJ3~SfU4.?8Ec,bOQ2D","_yuT4EpdWAn@{|K16Ru5+qy%jvv?>,X!xu79t|3F})+(^M>&Qzj9jq{%**tr*O/_","@$,Zq:.$2f%P0V*@l`y.i#B,38*TT4hf.mO=2~J>:0cTwl{H|x`[U@.^M,Y:mYe;","31I#CP?4Uj^DCUI0DNgn!47%G3B]fE~8w<!-%-:ka&?VX!V1{tidIxVha-:]6Obf",")9oxoP[xGr5w?}PTWkPY?}/"],
  w 34 19 0 830000 830384 40 1357 ["X])$'fATYi%&DTliuZiImTi^Wbm)^Mu*:iLP-Y;.q+'w?0rowRwi-tNX^w&T,_tR","t(+MRG$I!DC@:Up+S*G=PW.MS&%>}^gi^jgRJ;;f#iU#,^7?zEcC%#cidn{PQ#]P","]yQIiPjppSM2rIYzK<FcFCH~]RJ#@kR74x6NZARcVYu/Jk'>PB;@R<1g$^.P{sbP","#,f7{:srMjqch!5isvI9KUF.6vJk7].uhTJNvX]|,G={#NG't>#Rp.P:z@)0fL4l","(`eF"],
  w 34 18 0 840000 840384 37 1206 ["ID}Ibo~C[w;!EXNa;><_Pk'|Po!0v|9UE?t)ikV{p(BI)C4oK>0ht`]GG84w,(F^","SImD]c&KZ-kgx'uE@VQM@>%13`p1#MbmdU05:0fRDpt%qDRHFN='hL$o0q<AM<3I","fJnmJS)bU,%YicEBJEZZ:Axkzieqs(!fSlPEgA8Okt`ZJr]p[P$h=KBkc't/2W!V","KM&u'Fs+vBY><m%;fjq{P]10fy~ahM)Orb(]<!@+wD"]]

private def r34_16 : List (Chunk 34) := [
  w 34 17 0 850000 850321 33 1031 ["Z37WG=08*;L!6|^&}&lmhyj2Ui5iTXtoZY>Y)CzH8[&u&lOrl+TnH2!nH8*cOOVo","_YEtS#*L=hiX0-L/G5qR{7kKm$*60I=hmC.8P;0c~)z:,e9yghilgK%ExW|6'1_/",":ovg2'Et%*z7Yyz.:lE6QE5P$$^3bu!+ttF1el>dUH>+,;ZsT<qL=Pn-Jv,l.rSt","s0~p7`d/H@?va8I#3l:44%V[0"],
  w 34 16 0 860000 860320 30 897 ["b1E#LILn0iCZQmXV3-~*azO=a.$HR[>$Bx7`Ae._p|!W#Yh>_mT?sDX-|vc!e%AY","#CG'uBW.usA97/xBUX?yJZDp?MgP[w'35z*OcK{.&-[C<#.y~iS6KXU)`@/k|h>h","Op/<}N[y1e~PyBfQk+fiLj{2`LqQxB[_C5+g?$2SH/~4<y<<7iF|LMA[GTL2.P5D","+o"],
  w 34 15 0 870000 870320 27 776 ["qb!'%GXsZQ'QIN4uK)~Z=ZLW@*m25%U3^pm/qUiAtGMK6V8C+`Gni7NdD]X*|xDg","sF^g!uGO<Q7+0Y=ni}@EQK_G0ALo,_'y,S.q1p]h~opk=QBc?y&nXjN^P#:^-1g|","%~/JhT[%b!#z[E(<dr~i`I5Eyyvw{JZy0l:g*9X'CIJ)_)4M"],
  w 34 14 0 880000 880257 24 659 ["5/GA!LP[9SV(>ud|fhM[;%A~Yvzrh*?Z7kRu8$}`$gC';bS-e[`zgb<O&R5wGc3S","/?B[[O03.nzYx98U(hM^`p:K,V$gVZk</%2bwE=RxM{c@0S[@$Li?2}+u]5@QHOl","$G>WCYg8vvfP)-`!.Ppg2{L/s>Mc"]]

private def r34_17 : List (Chunk 34) := [
  w 34 13 0 890000 890256 21 552 ["Cq5w=W5}ui@{Kc!]7=>AU)#y?c?W76Hmh$`f6k%A[aR[(i]q:V)NH0=EMOQ?^zxs","UZ+(-'@0!+7/}/Jex-yuP;k[S&<h~R1F5[:#ziiCE69?AdFccBmp/,n5t)U9NkS?","#N|S=y:&uL4`"],
  w 34 12 0 900000 900256 19 479 ["v4LG.iVHUTX/Vdb5wX$:V,;2KF2Lj|QdWUtp8)#UtJ$jYX(N3OaE99)oD,dGf#S:","eWlKZ.L{u4?y/)o+Q1=U`ut3%OT:(]Yqw{GBxLX5sDf]].(cwHU{,Dj"],
  w 34 11 0 910000 910193 16 385 ["{^;A>8}R7,_%jy%_Sq/cN}#QWw,7GZ?xP?F:psX?&A&&FlMmfVtP`J,imUVryy;K","}8aO==9J.|-!mhw0}8$t4T<5g&^1q~V]!nYzy=.5"],
  w 34 10 0 920000 920192 14 321 ["k!Vq04j}W)qMf&w]|P3L0|0AQJHI3wWe|Grmt$2_v~wMSX?SAlR3Ja<g15Lh?I'+","+G*)::-.%g_71pI]G-hI!7saC;N"]]

private def r34_18 : List (Chunk 34) := [
  w 34 9 0 930000 930192 12 263 ["rc`cBD%%Ivx$pk$:=1a?x,OYqbJv?M,zOJ;8j)jN)W(+1^Vw*`<dKj{_a>#*;kMs","/SeET#/&?-?v"],
  w 34 8 0 940000 940129 10 207 ["#G1wxW2X(@-{lAxIR2aFd?9=:^O`@gZSRm?r1_Ewy_DY2^^_5t/%7&#mu{j+cW"],
  w 34 7 0 950000 950128 8 157 ["E*)Ao!vcAgu@+scSY[}t$Y:H`pmwiVu0ZZh1Pc~8:Z&yNq)O-x5vd"],
  w 34 6 0 960000 960128 7 130 ["+QlLigT*O>Ms][,luW{w2_`-j'/&icdaQG?'812jb"]]

private def r34_19 : List (Chunk 34) := [
  w 34 5 0 970000 970065 5 87 ["$=KqI(0e=AWlh)?n9E,!1(SMW|Y1^pX/"],
  w 34 4 0 980000 980064 4 65 ["&~V]#37)}BLW''k`9ndoJ.tJ"],
  w 34 3 0 990000 990064 3 46 [",s3>]hU'`hln(:*vjs"],
  w 34 2 0 1000000 1000001 2 28 ["/5!4q?3v0-"]]

private def r34_20 : List (Chunk 34) := [
  w 34 1 0 1010000 1010000 1 13 ["<u#OD_"],
  w 34 0 0 1020000 1020000 1 12 ["@$%q"]]
private def chunks34:List (Chunk 34):=r34_0 ++ r34_1 ++ r34_2 ++ r34_3 ++ r34_4 ++ r34_5 ++ r34_6 ++ r34_7 ++ r34_8 ++ r34_9 ++ r34_10 ++ r34_11 ++ r34_12 ++ r34_13 ++ r34_14 ++ r34_15 ++ r34_16 ++ r34_17 ++ r34_18 ++ r34_19 ++ r34_20
def rows34:=rowsFrom chunks34

theorem good34 : ∀ r ∈ rows34,good 34 r=true:=rowsFrom_good chunks34

theorem sorted34 : rows34.Pairwise (fun a b => a.tag < b.tag) :=
  (rowsFrom_sorted_aux chunks34 0 (by decide +kernel)).1

theorem mass34 (i : Fin 57) :
    bandCount 34 (i.val:ℤ) 56 14≤(rows34.filter (fun r => decide (i.val≤r.index))).length:=by
  change _≤((rowsFrom chunks34).filter _).length
  rw [mass_eq]
  have h : (List.range 57).all
      (fun j => decide (bandCount 34 (j:ℤ) 56 14≤mass j chunks34))=true:=by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

theorem total34 : (rows34.map (price 34)).sum = 318512 :=
  (total_eq chunks34).trans (by decide +kernel)


end Final50RankReceipt
