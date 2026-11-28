import ProximityPrize.SubmissionLower.Z6970H2307OrderPackedTools
import ProximityPrize.SubmissionLower.Bundle6970_27eec3c217f82fce

section Pack_Z6970H2307PackedPre01Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre1_4_40_data : List (Nat × Nat) :=
  [(40,15388832648660), (45,17088601900869), (46,17422861664195), (47,17755237912696), (49,18414364418504),
    (50,18741127261847), (51,19066031581204), (52,19389083540835), (53,19710289490107)]

def pre1_4_40 : List PrefixEntry := pre1_4_40_data.map fun (l,v) => (4,l,v)

theorem pre1_4_40_good : prefixGood ⟨1,3,1⟩ pre1_4_40=true :=
  prefixGood_chain ⟨1,3,1⟩ 4 32 12569018017134 pre1_4_40_data (prefixFind_sound ⟨1,3,1⟩ pre1_4_8 pre1_4_8_good (by decide)) (by decide +kernel)

private def pre1_2_4_data : List (Nat × Nat) :=
  [(4,1687745984996), (8,3341447105232)]

def pre1_2_4 : List PrefixEntry := pre1_2_4_data.map fun (l,v) => (2,l,v)

theorem pre1_2_4_good : prefixGood ⟨1,3,1⟩ pre1_2_4=true :=
  prefixGood_chain ⟨1,3,1⟩ 2 0 0 pre1_2_4_data rfl (by decide +kernel)

private def pre1_2_12_data : List (Nat × Nat) :=
  [(12,4961451705902), (16,6548112638694), (20,8101788808110), (24,9622844529566), (28,11111649191822)]

def pre1_2_12 : List PrefixEntry := pre1_2_12_data.map fun (l,v) => (2,l,v)

theorem pre1_2_12_good : prefixGood ⟨1,3,1⟩ pre1_2_12=true :=
  prefixGood_chain ⟨1,3,1⟩ 2 8 3341447105232 pre1_2_12_data (prefixFind_sound ⟨1,3,1⟩ pre1_2_4 pre1_2_4_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre01Part001

section Pack_Z6970H2307PackedPre02Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre2_4_38_data : List (Nat × Nat) :=
  [(38,14617965807115), (41,15643127727616), (42,15980846193368), (43,16316575284787), (44,16650322022779),
    (45,16982093452609), (46,17311896677348), (47,17639738822070), (48,17965627029996), (49,18289568465767),
    (50,18611570311502), (51,18931639770161), (52,19249784061513)]

def pre2_4_38 : List PrefixEntry := pre2_4_38_data.map fun (l,v) => (4,l,v)

theorem pre2_4_38_good : prefixGood ⟨2,3,1⟩ pre2_4_38=true :=
  prefixGood_chain ⟨2,3,1⟩ 4 34 13222807517078 pre2_4_38_data (prefixFind_sound ⟨2,3,1⟩ pre2_4_8 pre2_4_8_good (by decide)) (by decide +kernel)

private def pre2_2_4_data : List (Nat × Nat) :=
  [(4,1686625401144), (8,3337440727313), (12,4952832771762)]

def pre2_2_4 : List PrefixEntry := pre2_2_4_data.map fun (l,v) => (2,l,v)

theorem pre2_2_4_good : prefixGood ⟨2,3,1⟩ pre2_2_4=true :=
  prefixGood_chain ⟨2,3,1⟩ 2 0 0 pre2_2_4_data rfl (by decide +kernel)

private def pre2_2_16_data : List (Nat × Nat) :=
  [(16,6533198214783), (20,8078941271736), (24,9590472368174), (28,11068210552580), (32,12512581807346)]

def pre2_2_16 : List PrefixEntry := pre2_2_16_data.map fun (l,v) => (2,l,v)

theorem pre2_2_16_good : prefixGood ⟨2,3,1⟩ pre2_2_16=true :=
  prefixGood_chain ⟨2,3,1⟩ 2 12 4952832771762 pre2_2_16_data (prefixFind_sound ⟨2,3,1⟩ pre2_2_4 pre2_2_4_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre02Part001

section Pack_Z6970H2307PackedPre03Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre3_4_46_data : List (Nat × Nat) :=
  [(46,17199263575150), (47,17522491263507), (48,17843687238684), (49,18162859696446), (51,18795166664620),
    (52,19108317681492), (53,19419478090760), (54,19728656051674)]

def pre3_4_46 : List PrefixEntry := pre3_4_46_data.map fun (l,v) => (4,l,v)

theorem pre3_4_46_good : prefixGood ⟨3,3,1⟩ pre3_4_46=true :=
  prefixGood_chain ⟨3,3,1⟩ 4 38 14539329621506 pre3_4_46_data (prefixFind_sound ⟨3,3,1⟩ pre3_4_8 pre3_4_8_good (by decide)) (by decide +kernel)

private def pre3_2_4_data : List (Nat × Nat) :=
  [(4,1685502240963), (8,3333416030552), (12,4944160603993), (16,6518167416650)]

def pre3_2_4 : List PrefixEntry := pre3_2_4_data.map fun (l,v) => (2,l,v)

theorem pre3_2_4_good : prefixGood ⟨3,3,1⟩ pre3_2_4=true :=
  prefixGood_chain ⟨3,3,1⟩ 2 0 0 pre3_2_4_data rfl (by decide +kernel)

private def pre3_2_20_data : List (Nat × Nat) :=
  [(20,8055880553959), (24,9557755680816), (28,11024259745189), (30,11744396627261), (35,13506971980478),
    (40,15216368248870)]

def pre3_2_20 : List PrefixEntry := pre3_2_20_data.map fun (l,v) => (2,l,v)

theorem pre3_2_20_good : prefixGood ⟨3,3,1⟩ pre3_2_20=true :=
  prefixGood_chain ⟨3,3,1⟩ 2 16 6518167416650 pre3_2_20_data (prefixFind_sound ⟨3,3,1⟩ pre3_2_4 pre3_2_4_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre03Part001

section Pack_Z6970H2307PackedPre04Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre4_4_50_data : List (Nat × Nat) :=
  [(50,18346801197126), (51,18656970262846), (52,18965066805373), (53,19271100192113), (54,19575079786152)]

def pre4_4_50 : List PrefixEntry := pre4_4_50_data.map fun (l,v) => (4,l,v)

theorem pre4_4_50_good : prefixGood ⟨4,3,1⟩ pre4_4_50=true :=
  prefixGood_chain ⟨4,3,1⟩ 4 49 18034550255345 pre4_4_50_data (prefixFind_sound ⟨4,3,1⟩ pre4_4_8 pre4_4_8_good (by decide)) (by decide +kernel)

private def pre4_2_4_data : List (Nat × Nat) :=
  [(4,1684375912389), (8,3329373715005), (12,4935435651850), (16,6503023228963), (20,8032617168325)]

def pre4_2_4 : List PrefixEntry := pre4_2_4_data.map fun (l,v) => (2,l,v)

theorem pre4_2_4_good : prefixGood ⟨4,3,1⟩ pre4_2_4=true :=
  prefixGood_chain ⟨4,3,1⟩ 2 0 0 pre4_2_4_data rfl (by decide +kernel)

private def pre4_2_24_data : List (Nat × Nat) :=
  [(24,9524717104346), (29,11337902680546), (31,12047230922669), (36,13781283495575), (41,15460111796952),
    (44,16441363925148), (45,16764161451949), (46,17084830970741)]

def pre4_2_24 : List PrefixEntry := pre4_2_24_data.map fun (l,v) => (2,l,v)

theorem pre4_2_24_good : prefixGood ⟨4,3,1⟩ pre4_2_24=true :=
  prefixGood_chain ⟨4,3,1⟩ 2 20 8032617168325 pre4_2_24_data (prefixFind_sound ⟨4,3,1⟩ pre4_2_4 pre4_2_4_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre04Part001

section Pack_Z6970H2307PackedPre05Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre5_1_24_data : List (Nat × Nat) :=
  [(24,9491243689154), (26,10217831667486), (28,10934840582432), (30,11642344326687), (32,12340418499522),
    (35,13370016884863)]

def pre5_1_24 : List PrefixEntry := pre5_1_24_data.map fun (l,v) => (1,l,v)

theorem pre5_1_24_good : prefixGood ⟨5,3,1⟩ pre5_1_24=true :=
  prefixGood_chain ⟨5,3,1⟩ 1 22 8755003586647 pre5_1_24_data (prefixFind_sound ⟨5,3,1⟩ pre5_1_12 pre5_1_12_good (by decide)) (by decide +kernel)

private def pre5_1_38_data : List (Nat × Nat) :=
  [(38,14378834049171), (41,15367137801311), (44,16335200712210), (46,16969467338336), (48,17594943580457),
    (49,17904411302351), (53,19120724401760)]

def pre5_1_38 : List PrefixEntry := pre5_1_38_data.map fun (l,v) => (1,l,v)

theorem pre5_1_38_good : prefixGood ⟨5,3,1⟩ pre5_1_38=true :=
  prefixGood_chain ⟨5,3,1⟩ 1 35 13370016884863 pre5_1_38_data (prefixFind_sound ⟨5,3,1⟩ pre5_1_24 pre5_1_24_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre05Part003

section Pack_Z6970H2307PackedPre06Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre6_1_24_data : List (Nat × Nat) :=
  [(24,9457641976601), (26,10178619119956), (29,11241390514498), (32,12281976779127), (35,13300664372737),
    (38,14297747007742)]

def pre6_1_24 : List PrefixEntry := pre6_1_24_data.map fun (l,v) => (1,l,v)

theorem pre6_1_24_good : prefixGood ⟨6,3,1⟩ pre6_1_24=true :=
  prefixGood_chain ⟨6,3,1⟩ 1 22 8726600371906 pre6_1_24_data (prefixFind_sound ⟨6,3,1⟩ pre6_1_12 pre6_1_12_good (by decide)) (by decide +kernel)

private def pre6_1_41_data : List (Nat × Nat) :=
  [(41,15273524723048), (45,16541949257554), (47,17162391717627), (51,18376202796807), (52,18674083673060),
    (53,18969759367838), (55,19554542570174)]

def pre6_1_41 : List PrefixEntry := pre6_1_41_data.map fun (l,v) => (1,l,v)

theorem pre6_1_41_good : prefixGood ⟨6,3,1⟩ pre6_1_41=true :=
  prefixGood_chain ⟨6,3,1⟩ 1 38 14297747007742 pre6_1_41_data (prefixFind_sound ⟨6,3,1⟩ pre6_1_24 pre6_1_24_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre06Part003

section Pack_Z6970H2307PackedPre07Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre7_2_8_data : List (Nat × Nat) :=
  [(8,3317146648400), (12,4908965612539), (14,5688408325521), (19,7589563403072), (24,9423907410240),
    (30,11538786977245)]

def pre7_2_8 : List PrefixEntry := pre7_2_8_data.map fun (l,v) => (2,l,v)

theorem pre7_2_8_good : prefixGood ⟨7,3,1⟩ pre7_2_8=true :=
  prefixGood_chain ⟨7,3,1⟩ 2 4 1680980977493 pre7_2_8_data (prefixFind_sound ⟨7,3,1⟩ pre7_2_4 pre7_2_4_good (by decide)) (by decide +kernel)

private def pre7_2_37_data : List (Nat × Nat) :=
  [(37,13890223652710), (43,15809366561493), (49,17642426675503), (52,18527547751756), (53,18818021838868),
    (54,19106234567242), (55,19392199004495), (56,19675928201244)]

def pre7_2_37 : List PrefixEntry := pre7_2_37_data.map fun (l,v) => (2,l,v)

theorem pre7_2_37_good : prefixGood ⟨7,3,1⟩ pre7_2_37=true :=
  prefixGood_chain ⟨7,3,1⟩ 2 30 11538786977245 pre7_2_37_data (prefixFind_sound ⟨7,3,1⟩ pre7_2_8 pre7_2_8_good (by decide)) (by decide +kernel)

private def pre7_1_2_data : List (Nat × Nat) :=
  [(2,846101553820), (4,1680947210950)]

def pre7_1_2 : List PrefixEntry := pre7_1_2_data.map fun (l,v) => (1,l,v)

theorem pre7_1_2_good : prefixGood ⟨7,3,1⟩ pre7_1_2=true :=
  prefixGood_chain ⟨7,3,1⟩ 1 0 0 pre7_1_2_data rfl (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre07Part001

section Pack_Z6970H2307PackedPre08Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre8_2_12_data : List (Nat × Nat) :=
  [(12,4900049066547), (17,6819707985191), (23,9030919696219), (30,11486367665153), (38,14133928661563),
    (41,15084453468873)]

def pre8_2_12 : List PrefixEntry := pre8_2_12_data.map fun (l,v) => (2,l,v)

theorem pre8_2_12_good : prefixGood ⟨8,3,1⟩ pre8_2_12=true :=
  prefixGood_chain ⟨8,3,1⟩ 2 8 3313038343836 pre8_2_12_data (prefixFind_sound ⟨8,3,1⟩ pre8_2_4 pre8_2_4_good (by decide)) (by decide +kernel)

private def pre8_2_52_data : List (Nat × Nat) :=
  [(52,18380170142677), (53,18665438735870), (54,18948378801724), (57,19783369466594)]

def pre8_2_52 : List PrefixEntry := pre8_2_52_data.map fun (l,v) => (2,l,v)

theorem pre8_2_52_good : prefixGood ⟨8,3,1⟩ pre8_2_52=true :=
  prefixGood_chain ⟨8,3,1⟩ 2 41 15084453468873 pre8_2_52_data (prefixFind_sound ⟨8,3,1⟩ pre8_2_12 pre8_2_12_good (by decide)) (by decide +kernel)

private def pre8_1_2_data : List (Nat × Nat) :=
  [(2,845761517481), (4,1679810797055), (6,2502198068567), (8,3312978914348)]

def pre8_1_2 : List PrefixEntry := pre8_1_2_data.map fun (l,v) => (1,l,v)

theorem pre8_1_2_good : prefixGood ⟨8,3,1⟩ pre8_1_2=true :=
  prefixGood_chain ⟨8,3,1⟩ 1 0 0 pre8_1_2_data rfl (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre08Part001

section Pack_Z6970H2307PackedPre09Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre9_2_13_data : List (Nat × Nat) :=
  [(13,5279191508328), (18,7175545395960), (24,9355500638182), (32,12104217004193), (42,15296509773947),
    (43,15601374582738), (49,17377556926146), (54,18790000578495), (56,19338209290368), (57,19608781117818),
    (58,19877018031324)]

def pre9_2_13 : List PrefixEntry := pre9_2_13_data.map fun (l,v) => (2,l,v)

theorem pre9_2_13_good : prefixGood ⟨9,3,1⟩ pre9_2_13=true :=
  prefixGood_chain ⟨9,3,1⟩ 2 8 3308914747128 pre9_2_13_data (prefixFind_sound ⟨9,3,1⟩ pre9_2_4 pre9_2_4_good (by decide)) (by decide +kernel)

private def pre9_1_2_data : List (Nat × Nat) :=
  [(2,845421040959), (4,1678671891023), (6,2499799008688), (8,3308856571348), (10,4105905225405),
    (12,4891012298375)]

def pre9_1_2 : List PrefixEntry := pre9_1_2_data.map fun (l,v) => (1,l,v)

theorem pre9_1_2_good : prefixGood ⟨9,3,1⟩ pre9_1_2=true :=
  prefixGood_chain ⟨9,3,1⟩ 1 0 0 pre9_1_2_data rfl (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre09Part001

section Pack_Z6970H2307PackedPre10Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre10_4_33_data : List (Nat × Nat) :=
  [(33,12514780031495), (42,15423309688706), (43,15733962494743), (46,16651215142677), (48,17250584421646),
    (49,17546666055041), (51,18131684521301), (52,18420645828106), (53,18707258159348), (54,18991533739539),
    (55,19273484788439), (56,19553123500901), (57,19830462063977)]

def pre10_4_33 : List PrefixEntry := pre10_4_33_data.map fun (l,v) => (4,l,v)

theorem pre10_4_33_good : prefixGood ⟨2,4,1⟩ pre10_4_33=true :=
  prefixGood_chain ⟨2,4,1⟩ 4 24 9397371688855 pre10_4_33_data (prefixFind_sound ⟨2,4,1⟩ pre10_4_8 pre10_4_8_good (by decide)) (by decide +kernel)

private def pre10_2_4_data : List (Nat × Nat) :=
  [(4,1679890736048)]

def pre10_2_4 : List PrefixEntry := pre10_2_4_data.map fun (l,v) => (2,l,v)

theorem pre10_2_4_good : prefixGood ⟨2,4,1⟩ pre10_2_4=true :=
  prefixGood_chain ⟨2,4,1⟩ 2 0 0 pre10_2_4_data rfl (by decide +kernel)

private def pre10_2_8_data : List (Nat × Nat) :=
  [(8,3313397599152), (12,4901182175396), (16,6443922907168), (20,7942312516205), (24,9397056524747)]

def pre10_2_8 : List PrefixEntry := pre10_2_8_data.map fun (l,v) => (2,l,v)

theorem pre10_2_8_good : prefixGood ⟨2,4,1⟩ pre10_2_8=true :=
  prefixGood_chain ⟨2,4,1⟩ 2 4 1679890736048 pre10_2_8_data (prefixFind_sound ⟨2,4,1⟩ pre10_2_4 pre10_2_4_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre10Part001

section Pack_Z6970H2307PackedPre11Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre11_4_41_data : List (Nat × Nat) :=
  [(41,15023249879025), (44,15943255501187), (50,17715791726070), (51,18002625667992), (52,18287041830935),
    (53,18569053769343), (55,19125918875960), (56,19400799122689), (57,19673329194233), (58,19943522557642)]

def pre11_4_41 : List PrefixEntry := pre11_4_41_data.map fun (l,v) => (4,l,v)

theorem pre11_4_41_good : prefixGood ⟨3,4,1⟩ pre11_4_41=true :=
  prefixGood_chain ⟨3,4,1⟩ 4 38 14080266967577 pre11_4_41_data (prefixFind_sound ⟨3,4,1⟩ pre11_4_8 pre11_4_8_good (by decide)) (by decide +kernel)

private def pre11_2_3_data : List (Nat × Nat) :=
  [(3,1263619401930), (7,2906219461267), (11,4501211479796)]

def pre11_2_3 : List PrefixEntry := pre11_2_3_data.map fun (l,v) => (2,l,v)

theorem pre11_2_3_good : prefixGood ⟨3,4,1⟩ pre11_2_3=true :=
  prefixGood_chain ⟨3,4,1⟩ 2 0 0 pre11_2_3_data rfl (by decide +kernel)

private def pre11_2_15_data : List (Nat × Nat) :=
  [(15,6049325346268), (19,7551309936392), (23,9007934335708), (27,10419984641928), (31,11788264805062)]

def pre11_2_15 : List PrefixEntry := pre11_2_15_data.map fun (l,v) => (2,l,v)

theorem pre11_2_15_good : prefixGood ⟨3,4,1⟩ pre11_2_15=true :=
  prefixGood_chain ⟨3,4,1⟩ 2 11 4501211479796 pre11_2_15_data (prefixFind_sound ⟨3,4,1⟩ pre11_2_3 pre11_2_3_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre11Part001

section Pack_Z6970H2307PackedPre12Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre12_4_51_data : List (Nat × Nat) :=
  [(51,17872154393934), (52,18151983823494), (53,18429354579238), (54,18704281560939), (57,19514548913577),
    (58,19779849760057)]

def pre12_4_51 : List PrefixEntry := pre12_4_51_data.map fun (l,v) => (4,l,v)

theorem pre12_4_51_good : prefixGood ⟨4,4,1⟩ pre12_4_51=true :=
  prefixGood_chain ⟨4,4,1⟩ 4 42 15240583465592 pre12_4_51_data (prefixFind_sound ⟨4,4,1⟩ pre12_4_8 pre12_4_8_good (by decide)) (by decide +kernel)

private def pre12_2_4_data : List (Nat × Nat) :=
  [(4,1677649817102), (8,3305390160396), (12,4883978619274), (16,6414201467262)]

def pre12_2_4 : List PrefixEntry := pre12_2_4_data.map fun (l,v) => (2,l,v)

theorem pre12_2_4_good : prefixGood ⟨4,4,1⟩ pre12_2_4=true :=
  prefixGood_chain ⟨4,4,1⟩ 2 0 0 pre12_2_4_data rfl (by decide +kernel)

private def pre12_2_20_data : List (Nat × Nat) :=
  [(20,7896872817552), (24,9332833416545), (29,11063414746464), (34,12724095027356), (36,13369192159363),
    (41,14935009922940)]

def pre12_2_20 : List PrefixEntry := pre12_2_20_data.map fun (l,v) => (2,l,v)

theorem pre12_2_20_good : prefixGood ⟨4,4,1⟩ pre12_2_20=true :=
  prefixGood_chain ⟨4,4,1⟩ 2 16 6414201467262 pre12_2_20_data (prefixFind_sound ⟨4,4,1⟩ pre12_2_4 pre12_2_4_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre12Part001

section Pack_Z6970H2307PackedPre13Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre13_4_53_data : List (Nat × Nat) :=
  [(53,18288479796342), (54,18558689808781), (55,18826420608973), (57,19354509732125), (58,19614900561772)]

def pre13_4_53 : List PrefixEntry := pre13_4_53_data.map fun (l,v) => (4,l,v)

theorem pre13_4_53_good : prefixGood ⟨5,4,1⟩ pre13_4_53=true :=
  prefixGood_chain ⟨5,4,1⟩ 4 52 18015774234542 pre13_4_53_data (prefixFind_sound ⟨5,4,1⟩ pre13_4_8 pre13_4_8_good (by decide)) (by decide +kernel)

private def pre13_2_4_data : List (Nat × Nat) :=
  [(4,1676525218743), (8,3301361664302), (12,4875303035594), (16,6399184440474), (21,8234973989041)]

def pre13_2_4 : List PrefixEntry := pre13_2_4_data.map fun (l,v) => (2,l,v)

theorem pre13_2_4_good : prefixGood ⟨5,4,1⟩ pre13_2_4=true :=
  prefixGood_chain ⟨5,4,1⟩ 2 0 0 pre13_2_4_data rfl (by decide +kernel)

private def pre13_2_26_data : List (Nat × Nat) :=
  [(26,9995694371174), (31,11683202270393), (37,13614279069145), (41,14846315499836), (45,16035277863241),
    (52,18015465739306), (54,18558381034769)]

def pre13_2_26 : List PrefixEntry := pre13_2_26_data.map fun (l,v) => (2,l,v)

theorem pre13_2_26_good : prefixGood ⟨5,4,1⟩ pre13_2_26=true :=
  prefixGood_chain ⟨5,4,1⟩ 2 21 8234973989041 pre13_2_26_data (prefixFind_sound ⟨5,4,1⟩ pre13_2_4 pre13_2_4_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre13Part001

section Pack_Z6970H2307PackedPre14Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre14_2_19_data : List (Nat × Nat) :=
  [(19,7524121790544), (26,10019109973456), (36,13337892815228), (49,17244460789963), (55,18901168068133),
    (56,19168686159557), (57,19433790395957)]

def pre14_2_19 : List PrefixEntry := pre14_2_19_data.map fun (l,v) => (2,l,v)

theorem pre14_2_19_good : prefixGood ⟨10,3,1⟩ pre14_2_19=true :=
  prefixGood_chain ⟨10,3,1⟩ 2 13 5268683351245 pre14_2_19_data (prefixFind_sound ⟨10,3,1⟩ pre14_2_4 pre14_2_4_good (by decide)) (by decide +kernel)

private def pre14_1_2_data : List (Nat × Nat) :=
  [(2,845080126915), (4,1677530284586)]

def pre14_1_2 : List PrefixEntry := pre14_1_2_data.map fun (l,v) => (1,l,v)

theorem pre14_1_2_good : prefixGood ⟨10,3,1⟩ pre14_1_2=true :=
  prefixGood_chain ⟨10,3,1⟩ 1 0 0 pre14_1_2_data rfl (by decide +kernel)

private def pre14_1_6_data : List (Nat × Nat) :=
  [(6,2497392719534), (8,3304718929299), (10,4099569420353), (12,4882012873007), (14,5652125752252),
    (16,6409991923358)]

def pre14_1_6 : List PrefixEntry := pre14_1_6_data.map fun (l,v) => (1,l,v)

theorem pre14_1_6_good : prefixGood ⟨10,3,1⟩ pre14_1_6=true :=
  prefixGood_chain ⟨10,3,1⟩ 1 4 1677530284586 pre14_1_6_data (prefixFind_sound ⟨10,3,1⟩ pre14_1_2 pre14_1_2_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre14Part001

section Pack_Z6970H2307PackedPre15Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre15_1_12_data : List (Nat × Nat) :=
  [(12,4780672400452), (17,6585091591225), (68,19553333688031), (71,20053983750821), (74,20530130881413)]

def pre15_1_12 : List PrefixEntry := pre15_1_12_data.map fun (l,v) => (1,l,v)

theorem pre15_1_12_good : prefixGood ⟨21,3,1⟩ pre15_1_12=true :=
  prefixGood_chain ⟨21,3,1⟩ 1 9 3645537067894 pre15_1_12_data (prefixFind_sound ⟨21,3,1⟩ pre15_1_2 pre15_1_2_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre15Part001

section Pack_Z6970H2307PackedPre17Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre17_4_33_data : List (Nat × Nat) :=
  [(33,12167780008818), (40,14298626539536), (44,15451258300253), (52,17620281010466), (53,17878992163814),
    (55,18388336705719), (56,18639006317674), (57,18887031590702), (58,19132430580236), (59,19375221311792),
    (60,19615421781626), (61,19853049957177), (62,20088123770671)]

def pre17_4_33 : List PrefixEntry := pre17_4_33_data.map fun (l,v) => (4,l,v)

theorem pre17_4_33_good : prefixGood ⟨2,5,1⟩ pre17_4_33=true :=
  prefixGood_chain ⟨2,5,1⟩ 4 24 9206650402168 pre17_4_33_data (prefixFind_sound ⟨2,5,1⟩ pre17_4_8 pre17_4_8_good (by decide)) (by decide +kernel)

private def pre17_2_4_data : List (Nat × Nat) :=
  [(4,1673171552714)]

def pre17_2_4 : List PrefixEntry := pre17_2_4_data.map fun (l,v) => (2,l,v)

theorem pre17_2_4_good : prefixGood ⟨2,5,1⟩ pre17_2_4=true :=
  prefixGood_chain ⟨2,5,1⟩ 2 0 0 pre17_2_4_data rfl (by decide +kernel)

private def pre17_2_8_data : List (Nat × Nat) :=
  [(8,3289461323678), (12,4849877019471), (16,6355453960820), (20,7807252154509), (24,9206354462981)]

def pre17_2_8 : List PrefixEntry := pre17_2_8_data.map fun (l,v) => (2,l,v)

theorem pre17_2_8_good : prefixGood ⟨2,5,1⟩ pre17_2_8=true :=
  prefixGood_chain ⟨2,5,1⟩ 2 4 1673171552714 pre17_2_8_data (prefixFind_sound ⟨2,5,1⟩ pre17_2_4 pre17_2_4_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre17Part001

section Pack_Z6970H2307PackedPre18Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre18_2_19_data : List (Nat × Nat) :=
  [(19,7284162505966), (26,9588922250084), (36,12558044653716), (63,18910151150702), (67,19670509994313),
    (69,20035085258377), (70,20213566008079)]

def pre18_2_19 : List PrefixEntry := pre18_2_19_data.map fun (l,v) => (2,l,v)

theorem pre18_2_19_good : prefixGood ⟨10,5,1⟩ pre18_2_19=true :=
  prefixGood_chain ⟨10,5,1⟩ 2 13 5150929483480 pre18_2_19_data (prefixFind_sound ⟨10,5,1⟩ pre18_2_4 pre18_2_4_good (by decide)) (by decide +kernel)

private def pre18_1_2_data : List (Nat × Nat) :=
  [(2,841036942777), (4,1664147284625)]

def pre18_1_2 : List PrefixEntry := pre18_1_2_data.map fun (l,v) => (1,l,v)

theorem pre18_1_2_good : prefixGood ⟨10,5,1⟩ pre18_1_2=true :=
  prefixGood_chain ⟨10,5,1⟩ 1 0 0 pre18_1_2_data rfl (by decide +kernel)

private def pre18_1_6_data : List (Nat × Nat) :=
  [(6,2469489912257), (8,3257236643674), (10,4027571609286), (12,4780690074074), (14,5516797687488),
    (16,6236109728338)]

def pre18_1_6 : List PrefixEntry := pre18_1_6_data.map fun (l,v) => (1,l,v)

theorem pre18_1_6_good : prefixGood ⟨10,5,1⟩ pre18_1_6=true :=
  prefixGood_chain ⟨10,5,1⟩ 1 4 1664147284625 pre18_1_6_data (prefixFind_sound ⟨10,5,1⟩ pre18_1_2 pre18_1_2_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre18Part001

section Pack_Z6970H2307PackedPre19Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre19_1_6_data : List (Nat × Nat) :=
  [(6,2452655011970), (8,3228346610175), (11,4353362169156), (14,5432959268100), (18,6803573495256),
    (36,12071751571748)]

def pre19_1_6 : List PrefixEntry := pre19_1_6_data.map fun (l,v) => (1,l,v)

theorem pre19_1_6_good : prefixGood ⟨17,5,1⟩ pre19_1_6=true :=
  prefixGood_chain ⟨17,5,1⟩ 1 4 1656151338312 pre19_1_6_data (prefixFind_sound ⟨17,5,1⟩ pre19_1_2 pre19_1_2_good (by decide)) (by decide +kernel)

private def pre19_1_83_data : List (Nat × Nat) :=
  [(83,20418095810307), (85,20641755957507), (86,20750393078440)]

def pre19_1_83 : List PrefixEntry := pre19_1_83_data.map fun (l,v) => (1,l,v)

theorem pre19_1_83_good : prefixGood ⟨17,5,1⟩ pre19_1_83=true :=
  prefixGood_chain ⟨17,5,1⟩ 1 36 12071751571748 pre19_1_83_data (prefixFind_sound ⟨17,5,1⟩ pre19_1_6 pre19_1_6_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre19Part001

section Pack_Z6970H2307PackedPre20Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre20_4_24_data : List (Nat × Nat) :=
  [(24,9018698563046), (26,9668513366020), (30,10924118703006), (39,13542096758223), (48,15888494971307),
    (55,17537584268325), (60,18626558877830), (62,19042205554183), (64,19446750942055), (65,19644921618087),
    (66,19840389976146)]

def pre20_4_24 : List PrefixEntry := pre20_4_24_data.map fun (l,v) => (4,l,v)

theorem pre20_4_24_good : prefixGood ⟨2,6,1⟩ pre20_4_24=true :=
  prefixGood_chain ⟨2,6,1⟩ 4 16 6268020827778 pre20_4_24_data (prefixFind_sound ⟨2,6,1⟩ pre20_4_8 pre20_4_8_good (by decide)) (by decide +kernel)

private def pre20_4_67_data : List (Nat × Nat) :=
  [(67,20033180186294), (68,20223316335275), (69,20410822425283)]

def pre20_4_67 : List PrefixEntry := pre20_4_67_data.map fun (l,v) => (4,l,v)

theorem pre20_4_67_good : prefixGood ⟨2,6,1⟩ pre20_4_67=true :=
  prefixGood_chain ⟨2,6,1⟩ 4 66 19840389976146 pre20_4_67_data (prefixFind_sound ⟨2,6,1⟩ pre20_4_24 pre20_4_24_good (by decide)) (by decide +kernel)

private def pre20_2_4_data : List (Nat × Nat) :=
  [(4,1666467907278), (8,3265632696942), (12,4798921063888), (16,6267802780214), (20,7673787202678)]

def pre20_2_4 : List PrefixEntry := pre20_2_4_data.map fun (l,v) => (2,l,v)

theorem pre20_2_4_good : prefixGood ⟨2,6,1⟩ pre20_2_4=true :=
  prefixGood_chain ⟨2,6,1⟩ 2 0 0 pre20_2_4_data rfl (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre20Part001

section Pack_Z6970H2307PackedPre20Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre20_1_22_data : List (Nat × Nat) :=
  [(22,8353542116174), (24,9018281791823), (26,9668079749926), (28,10303137103014), (30,10923657008048)]

def pre20_1_22 : List PrefixEntry := pre20_1_22_data.map fun (l,v) => (1,l,v)

theorem pre20_1_22_good : prefixGood ⟨2,6,1⟩ pre20_1_22=true :=
  prefixGood_chain ⟨2,6,1⟩ 1 20 7673661719617 pre20_1_22_data (prefixFind_sound ⟨2,6,1⟩ pre20_1_12 pre20_1_12_good (by decide)) (by decide +kernel)

private def pre20_1_32_data : List (Nat × Nat) :=
  [(32,11529844330173), (34,12121904354305), (36,12700042437639), (38,13264463716232), (40,13815373037057),
    (42,14352974889546)]

def pre20_1_32 : List PrefixEntry := pre20_1_32_data.map fun (l,v) => (1,l,v)

theorem pre20_1_32_good : prefixGood ⟨2,6,1⟩ pre20_1_32=true :=
  prefixGood_chain ⟨2,6,1⟩ 1 30 10923657008048 pre20_1_32_data (prefixFind_sound ⟨2,6,1⟩ pre20_1_22 pre20_1_22_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre20Part004

section Pack_Z6970H2307PackedPre21Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre21_4_24_data : List (Nat × Nat) :=
  [(24,9018698563046), (26,9668513366020), (30,10924118703006), (39,13542096758223), (48,15888494971307),
    (55,17537584268325), (60,18626558877830), (62,19042205554183), (64,19446750942055), (65,19644921618087),
    (66,19840389976146)]

def pre21_4_24 : List PrefixEntry := pre21_4_24_data.map fun (l,v) => (4,l,v)

theorem pre21_4_24_good : prefixGood ⟨2,6,2⟩ pre21_4_24=true :=
  prefixGood_chain ⟨2,6,2⟩ 4 16 6268020827778 pre21_4_24_data (prefixFind_sound ⟨2,6,2⟩ pre21_4_8 pre21_4_8_good (by decide)) (by decide +kernel)

private def pre21_4_67_data : List (Nat × Nat) :=
  [(67,20033180186294), (68,20223316335275), (69,20410822425283)]

def pre21_4_67 : List PrefixEntry := pre21_4_67_data.map fun (l,v) => (4,l,v)

theorem pre21_4_67_good : prefixGood ⟨2,6,2⟩ pre21_4_67=true :=
  prefixGood_chain ⟨2,6,2⟩ 4 66 19840389976146 pre21_4_67_data (prefixFind_sound ⟨2,6,2⟩ pre21_4_24 pre21_4_24_good (by decide)) (by decide +kernel)

private def pre21_2_4_data : List (Nat × Nat) :=
  [(4,1666467907278), (8,3265632696942), (12,4798921063888), (16,6267802780214), (20,7673787202678)]

def pre21_2_4 : List PrefixEntry := pre21_2_4_data.map fun (l,v) => (2,l,v)

theorem pre21_2_4_good : prefixGood ⟨2,6,2⟩ pre21_2_4=true :=
  prefixGood_chain ⟨2,6,2⟩ 2 0 0 pre21_2_4_data rfl (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre21Part001

section Pack_Z6970H2307PackedPre21Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre21_1_22_data : List (Nat × Nat) :=
  [(22,8353542116174), (24,9018281791823), (26,9668079749926), (28,10303137103014), (30,10923657008048)]

def pre21_1_22 : List PrefixEntry := pre21_1_22_data.map fun (l,v) => (1,l,v)

theorem pre21_1_22_good : prefixGood ⟨2,6,2⟩ pre21_1_22=true :=
  prefixGood_chain ⟨2,6,2⟩ 1 20 7673661719617 pre21_1_22_data (prefixFind_sound ⟨2,6,2⟩ pre21_1_12 pre21_1_12_good (by decide)) (by decide +kernel)

private def pre21_1_32_data : List (Nat × Nat) :=
  [(32,11529844330173), (34,12121904354305), (36,12700042437639), (38,13264463716232), (40,13815373037057),
    (42,14352974889546)]

def pre21_1_32 : List PrefixEntry := pre21_1_32_data.map fun (l,v) => (1,l,v)

theorem pre21_1_32_good : prefixGood ⟨2,6,2⟩ pre21_1_32=true :=
  prefixGood_chain ⟨2,6,2⟩ 1 30 10923657008048 pre21_1_32_data (prefixFind_sound ⟨2,6,2⟩ pre21_1_22 pre21_1_22_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre21Part004

section Pack_Z6970H2307PackedPre22Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre22_4_57_data : List (Nat × Nat) :=
  [(57,17567594829616), (63,18762172333139), (66,19321628885713), (67,19502696805829), (68,19681101967083),
    (69,19856871747990), (71,20200613867447), (72,20368640148623), (73,20534138935352)]

def pre22_4_57 : List PrefixEntry := pre22_4_57_data.map fun (l,v) => (4,l,v)

theorem pre22_4_57_good : prefixGood ⟨5,6,2⟩ pre22_4_57=true :=
  prefixGood_chain ⟨5,6,2⟩ 4 46 15097472107235 pre22_4_57_data (prefixFind_sound ⟨5,6,2⟩ pre22_4_8 pre22_4_8_good (by decide)) (by decide +kernel)

private def pre22_2_4_data : List (Nat × Nat) :=
  [(4,1663128232174), (8,3253776938182), (12,4773628633137), (16,6224440512462), (21,7943654774555)]

def pre22_2_4 : List PrefixEntry := pre22_2_4_data.map fun (l,v) => (2,l,v)

theorem pre22_2_4_good : prefixGood ⟨5,6,2⟩ pre22_2_4=true :=
  prefixGood_chain ⟨5,6,2⟩ 2 0 0 pre22_2_4_data rfl (by decide +kernel)

private def pre22_2_26_data : List (Nat × Nat) :=
  [(26,9561545518137), (31,11081931249225), (37,12783193608943), (43,14356468690116), (50,16039176511409),
    (64,18951142126969), (67,19502444495607), (68,19680849656861), (70,20029781053703), (72,20368387838401),
    (73,20533886625130)]

def pre22_2_26 : List PrefixEntry := pre22_2_26_data.map fun (l,v) => (2,l,v)

theorem pre22_2_26_good : prefixGood ⟨5,6,2⟩ pre22_2_26=true :=
  prefixGood_chain ⟨5,6,2⟩ 2 21 7943654774555 pre22_2_26_data (prefixFind_sound ⟨5,6,2⟩ pre22_2_4 pre22_2_4_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre22Part001

section Pack_Z6970H2307PackedPre22Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre22_1_24_data : List (Nat × Nat) :=
  [(24,8926191553956), (26,9561427952036), (28,10181063074972), (30,10785345851475), (32,11374527614293),
    (35,12230536863502)]

def pre22_1_24 : List PrefixEntry := pre22_1_24_data.map fun (l,v) => (1,l,v)

theorem pre22_1_24_good : prefixGood ⟨5,6,2⟩ pre22_1_24=true :=
  prefixGood_chain ⟨5,6,2⟩ 1 22 8275107214273 pre22_1_24_data (prefixFind_sound ⟨5,6,2⟩ pre22_1_12 pre22_1_12_good (by decide)) (by decide +kernel)

private def pre22_1_38_data : List (Nat × Nat) :=
  [(38,13053985314861), (41,13845720384044), (44,14606585584882), (47,15337418588423), (50,16039049588954),
    (68,19680722729258), (70,20029654126100), (73,20533759697527)]

def pre22_1_38 : List PrefixEntry := pre22_1_38_data.map fun (l,v) => (1,l,v)

theorem pre22_1_38_good : prefixGood ⟨5,6,2⟩ pre22_1_38=true :=
  prefixGood_chain ⟨5,6,2⟩ 1 35 12230536863502 pre22_1_38_data (prefixFind_sound ⟨5,6,2⟩ pre22_1_24 pre22_1_24_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre22Part003

section Pack_Z6970H2307PackedPre23Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre23_2_17_data : List (Nat × Nat) :=
  [(17,6527084275492), (23,8515804664544), (30,10644182096508), (38,12839471516162), (41,13601242417779),
    (61,17909603193217), (72,19774100008398), (73,19927873460010), (74,20079156449165), (76,20374368246365),
    (78,20659967618386)]

def pre23_2_17 : List PrefixEntry := pre23_2_17_data.map fun (l,v) => (2,l,v)

theorem pre23_2_17_good : prefixGood ⟨8,6,2⟩ pre23_2_17=true :=
  prefixGood_chain ⟨8,6,2⟩ 2 12 4747940779157 pre23_2_17_data (prefixFind_sound ⟨8,6,2⟩ pre23_2_4 pre23_2_4_good (by decide)) (by decide +kernel)

private def pre23_1_2_data : List (Nat × Nat) :=
  [(2,839696255413)]

def pre23_1_2 : List PrefixEntry := pre23_1_2_data.map fun (l,v) => (1,l,v)

theorem pre23_1_2_good : prefixGood ⟨8,6,2⟩ pre23_1_2=true :=
  prefixGood_chain ⟨8,6,2⟩ 1 0 0 pre23_1_2_data rfl (by decide +kernel)

private def pre23_1_4_data : List (Nat × Nat) :=
  [(4,1659732828263), (6,2460331736162), (8,3241724938525), (10,4004153712981), (12,4747868710359),
    (14,5473128483671)]

def pre23_1_4 : List PrefixEntry := pre23_1_4_data.map fun (l,v) => (1,l,v)

theorem pre23_1_4_good : prefixGood ⟨8,6,2⟩ pre23_1_4=true :=
  prefixGood_chain ⟨8,6,2⟩ 1 2 839696255413 pre23_1_4_data (prefixFind_sound ⟨8,6,2⟩ pre23_1_2 pre23_1_2_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre23Part001

section Pack_Z6970H2307PackedPre24Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre24_2_19_data : List (Nat × Nat) :=
  [(19,7145479114476), (27,9638092318922), (79,20120768147415), (80,20246125060115), (81,20369222328278),
    (82,20490090335615), (83,20608759195615)]

def pre24_2_19 : List PrefixEntry := pre24_2_19_data.map fun (l,v) => (2,l,v)

theorem pre24_2_19_good : prefixGood ⟨11,6,2⟩ pre24_2_19=true :=
  prefixGood_chain ⟨11,6,2⟩ 2 13 5082571422338 pre24_2_19_data (prefixFind_sound ⟨11,6,2⟩ pre24_2_4 pre24_2_4_good (by decide)) (by decide +kernel)

private def pre24_1_2_data : List (Nat × Nat) :=
  [(2,838680029250), (4,1656348513695)]

def pre24_1_2 : List PrefixEntry := pre24_1_2_data.map fun (l,v) => (1,l,v)

theorem pre24_1_2_good : prefixGood ⟨11,6,2⟩ pre24_1_2=true :=
  prefixGood_chain ⟨11,6,2⟩ 1 0 0 pre24_1_2_data rfl (by decide +kernel)

private def pre24_1_6_data : List (Nat × Nat) :=
  [(6,2453238667812), (8,3229601980295), (10,3985706717424), (12,4721836705134), (14,5438289892517),
    (17,6476758301252)]

def pre24_1_6 : List PrefixEntry := pre24_1_6_data.map fun (l,v) => (1,l,v)

theorem pre24_1_6_good : prefixGood ⟨11,6,2⟩ pre24_1_6=true :=
  prefixGood_chain ⟨11,6,2⟩ 1 4 1656348513695 pre24_1_6_data (prefixFind_sound ⟨11,6,2⟩ pre24_1_2 pre24_1_2_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre24Part001

section Pack_Z6970H2307PackedPre26Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre26_1_4_data : List (Nat × Nat) :=
  [(4,1651802369303), (6,2443688671845), (8,3213250792542), (10,3960793271998), (13,5041554369196),
    (16,6074748671539)]

def pre26_1_4 : List PrefixEntry := pre26_1_4_data.map fun (l,v) => (1,l,v)

theorem pre26_1_4_good : prefixGood ⟨15,6,2⟩ pre26_1_4=true :=
  prefixGood_chain ⟨15,6,2⟩ 1 2 837318867684 pre26_1_4_data (prefixFind_sound ⟨15,6,2⟩ pre26_1_2 pre26_1_2_good (by decide)) (by decide +kernel)

private def pre26_1_20_data : List (Nat × Nat) :=
  [(20,7380647222055), (26,9192695575534), (91,20393696571136), (94,20644471710518), (95,20724469093428),
    (96,20802718117560), (97,20879247586071), (98,20954085984160)]

def pre26_1_20 : List PrefixEntry := pre26_1_20_data.map fun (l,v) => (1,l,v)

theorem pre26_1_20_good : prefixGood ⟨15,6,2⟩ pre26_1_20=true :=
  prefixGood_chain ⟨15,6,2⟩ 1 16 6074748671539 pre26_1_20_data (prefixFind_sound ⟨15,6,2⟩ pre26_1_4 pre26_1_4_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre26Part001

section Pack_Z6970H2307PackedPre27Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre27_1_4_data : List (Nat × Nat) :=
  [(4,1649515336418), (6,2438876230262), (8,3205001247699), (11,4311339563319), (14,5367373563930),
    (18,6699578868967)]

def pre27_1_4 : List PrefixEntry := pre27_1_4_data.map fun (l,v) => (1,l,v)

theorem pre27_1_4_good : prefixGood ⟨17,6,2⟩ pre27_1_4=true :=
  prefixGood_chain ⟨17,6,2⟩ 1 2 836635750191 pre27_1_4_data (prefixFind_sound ⟨17,6,2⟩ pre27_1_2 pre27_1_2_good (by decide)) (by decide +kernel)

private def pre27_1_100_data : List (Nat × Nat) :=
  [(100,20488956671098), (104,20731608067130), (108,20951063386378), (109,21002502684517), (110,21052623815712)]

def pre27_1_100 : List PrefixEntry := pre27_1_100_data.map fun (l,v) => (1,l,v)

theorem pre27_1_100_good : prefixGood ⟨17,6,2⟩ pre27_1_100=true :=
  prefixGood_chain ⟨17,6,2⟩ 1 18 6699578868967 pre27_1_100_data (prefixFind_sound ⟨17,6,2⟩ pre27_1_4 pre27_1_4_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre27Part001

section Pack_Z6970H2307PackedPre28Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre28_1_8_data : List (Nat × Nat) :=
  [(8,3196705713722), (11,4296179026857), (15,5681173554053), (21,7592730653927), (135,21124154274478),
    (136,21143045693734), (137,21161259778909), (138,21178813875922), (139,21195725043118)]

def pre28_1_8 : List PrefixEntry := pre28_1_8_data.map fun (l,v) => (1,l,v)

theorem pre28_1_8_good : prefixGood ⟨19,6,2⟩ pre28_1_8=true :=
  prefixGood_chain ⟨19,6,2⟩ 1 6 2434040216023 pre28_1_8_data (prefixFind_sound ⟨19,6,2⟩ pre28_1_2 pre28_1_2_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre28Part001

section Pack_Z6970H2307PackedPre29Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre29_4_34_data : List (Nat × Nat) :=
  [(34,11716622000735), (44,14237383413125), (55,16600165163077), (64,18245141576439), (68,18899964730471),
    (69,19056715228471), (70,19210747242052), (71,19362092271481), (72,19510781633407), (74,19800317729524),
    (75,19941226194992), (76,20079602458832), (77,20215476935386), (78,20348879855092), (79,20479841271074),
    (80,20608391052456), (81,20734558887540)]

def pre29_4_34 : List PrefixEntry := pre29_4_34_data.map fun (l,v) => (4,l,v)

theorem pre29_4_34_good : prefixGood ⟨3,7,1⟩ pre29_4_34=true :=
  prefixGood_chain ⟨3,7,1⟩ 4 25 9113798439236 pre29_4_34_data (prefixFind_sound ⟨3,7,1⟩ pre29_4_8 pre29_4_8_good (by decide)) (by decide +kernel)

private def pre29_2_4_data : List (Nat × Nat) :=
  [(4,1658673804467), (8,3238006479396)]

def pre29_2_4 : List PrefixEntry := pre29_2_4_data.map fun (l,v) => (2,l,v)

theorem pre29_2_4_good : prefixGood ⟨3,7,1⟩ pre29_2_4=true :=
  prefixGood_chain ⟨3,7,1⟩ 2 0 0 pre29_2_4_data rfl (by decide +kernel)

private def pre29_2_12_data : List (Nat × Nat) :=
  [(12,4740030308097), (16,6166847856288), (20,7520628514879), (24,8803603253658), (28,10018059143905),
    (32,11166318845406)]

def pre29_2_12 : List PrefixEntry := pre29_2_12_data.map fun (l,v) => (2,l,v)

theorem pre29_2_12_good : prefixGood ⟨3,7,1⟩ pre29_2_12=true :=
  prefixGood_chain ⟨3,7,1⟩ 2 8 3238006479396 pre29_2_12_data (prefixFind_sound ⟨3,7,1⟩ pre29_2_4 pre29_2_4_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre29Part001

section Pack_Z6970H2307PackedPre30Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre30_4_34_data : List (Nat × Nat) :=
  [(34,11716622000735), (44,14237383413125), (55,16600165163077), (64,18245141576439), (68,18899964730471),
    (69,19056715228471), (70,19210747242052), (71,19362092271481), (72,19510781633407), (74,19800317729524),
    (75,19941226194992), (76,20079602458832), (77,20215476935386), (78,20348879855092), (79,20479841271074),
    (80,20608391052456), (81,20734558887540)]

def pre30_4_34 : List PrefixEntry := pre30_4_34_data.map fun (l,v) => (4,l,v)

theorem pre30_4_34_good : prefixGood ⟨3,7,2⟩ pre30_4_34=true :=
  prefixGood_chain ⟨3,7,2⟩ 4 25 9113798439236 pre30_4_34_data (prefixFind_sound ⟨3,7,2⟩ pre30_4_8 pre30_4_8_good (by decide)) (by decide +kernel)

private def pre30_2_4_data : List (Nat × Nat) :=
  [(4,1658673804467), (8,3238006479396)]

def pre30_2_4 : List PrefixEntry := pre30_2_4_data.map fun (l,v) => (2,l,v)

theorem pre30_2_4_good : prefixGood ⟨3,7,2⟩ pre30_2_4=true :=
  prefixGood_chain ⟨3,7,2⟩ 2 0 0 pre30_2_4_data rfl (by decide +kernel)

private def pre30_2_12_data : List (Nat × Nat) :=
  [(12,4740030308097), (16,6166847856288), (20,7520628514879), (24,8803603253658), (28,10018059143905),
    (32,11166318845406)]

def pre30_2_12 : List PrefixEntry := pre30_2_12_data.map fun (l,v) => (2,l,v)

theorem pre30_2_12_good : prefixGood ⟨3,7,2⟩ pre30_2_12=true :=
  prefixGood_chain ⟨3,7,2⟩ 2 8 3238006479396 pre30_2_12_data (prefixFind_sound ⟨3,7,2⟩ pre30_2_4 pre30_2_4_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre30Part001

section Pack_Z6970H2307PackedPre31Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre31_2_8_data : List (Nat × Nat) :=
  [(8,3226193983090), (12,4714899284140), (16,6123907167598), (21,7776996151409), (26,9314744767414)]

def pre31_2_8 : List PrefixEntry := pre31_2_8_data.map fun (l,v) => (2,l,v)

theorem pre31_2_8_good : prefixGood ⟨6,7,2⟩ pre31_2_8=true :=
  prefixGood_chain ⟨6,7,2⟩ 2 4 1655338835381 pre31_2_8_data (prefixFind_sound ⟨6,7,2⟩ pre31_2_4 pre31_2_4_good (by decide)) (by decide +kernel)

private def pre31_2_32_data : List (Nat × Nat) :=
  [(32,11015328639158), (39,12811593576437), (79,19875489137695), (80,19994609900357), (82,20225916130459),
    (84,20448185048578), (85,20556008238932), (86,20661664873832), (87,20765185362440), (88,20866599868577)]

def pre31_2_32 : List PrefixEntry := pre31_2_32_data.map fun (l,v) => (2,l,v)

theorem pre31_2_32_good : prefixGood ⟨6,7,2⟩ pre31_2_32=true :=
  prefixGood_chain ⟨6,7,2⟩ 2 26 9314744767414 pre31_2_32_data (prefixFind_sound ⟨6,7,2⟩ pre31_2_8 pre31_2_8_good (by decide)) (by decide +kernel)

private def pre31_1_2_data : List (Nat × Nat) :=
  [(2,838353532387), (4,1655306382422)]

def pre31_1_2 : List PrefixEntry := pre31_1_2_data.map fun (l,v) => (1,l,v)

theorem pre31_1_2_good : prefixGood ⟨6,7,2⟩ pre31_1_2=true :=
  prefixGood_chain ⟨6,7,2⟩ 1 0 0 pre31_1_2_data rfl (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre31Part001

section Pack_Z6970H2307PackedPre32Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre32_2_18_data : List (Nat × Nat) :=
  [(18,6744985888312), (24,8621066836828), (32,10861862141517), (68,17902395188130), (87,20084375661347),
    (88,20176894417412), (90,20355959744474), (91,20442568593605), (93,20610092068380), (94,20691067146237),
    (95,20770224250742), (96,20847592854530), (97,20923202135091), (98,20997080970607)]

def pre32_2_18 : List PrefixEntry := pre32_2_18_data.map fun (l,v) => (2,l,v)

theorem pre32_2_18_good : prefixGood ⟨9,7,2⟩ pre32_2_18=true :=
  prefixGood_chain ⟨9,7,2⟩ 2 13 5044904747152 pre32_2_18_data (prefixFind_sound ⟨9,7,2⟩ pre32_2_4 pre32_2_4_good (by decide)) (by decide +kernel)

private def pre32_1_2_data : List (Nat × Nat) :=
  [(2,837342049269), (4,1651950230703)]

def pre32_1_2 : List PrefixEntry := pre32_1_2_data.map fun (l,v) => (1,l,v)

theorem pre32_1_2_good : prefixGood ⟨9,7,2⟩ pre32_1_2=true :=
  prefixGood_chain ⟨9,7,2⟩ 1 0 0 pre32_1_2_data rfl (by decide +kernel)

private def pre32_1_6_data : List (Nat × Nat) :=
  [(6,2444128151426), (8,3214194640762), (10,3962481864999), (12,4689334800621), (14,5395110152522),
    (16,6080175174736)]

def pre32_1_6 : List PrefixEntry := pre32_1_6_data.map fun (l,v) => (1,l,v)

theorem pre32_1_6_good : prefixGood ⟨9,7,2⟩ pre32_1_6=true :=
  prefixGood_chain ⟨9,7,2⟩ 1 4 1651950230703 pre32_1_6_data (prefixFind_sound ⟨9,7,2⟩ pre32_1_2 pre32_1_2_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre32Part001

section Pack_Z6970H2307PackedPre33Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre33_2_19_data : List (Nat × Nat) :=
  [(19,7029340197306), (27,9418477583485), (91,19964334600300), (96,20341285661423), (98,20479940669980),
    (101,20675672686034), (103,20798327883564), (105,20914977308892), (106,20971118009609), (107,21025838410487)]

def pre33_2_19 : List PrefixEntry := pre33_2_19_data.map fun (l,v) => (2,l,v)

theorem pre33_2_19_good : prefixGood ⟨11,7,2⟩ pre33_2_19=true :=
  prefixGood_chain ⟨11,7,2⟩ 2 13 5024938940344 pre33_2_19_data (prefixFind_sound ⟨11,7,2⟩ pre33_2_4 pre33_2_4_good (by decide)) (by decide +kernel)

private def pre33_1_2_data : List (Nat × Nat) :=
  [(2,836665587988), (4,1649700477363), (6,2439420689315)]

def pre33_1_2 : List PrefixEntry := pre33_1_2_data.map fun (l,v) => (1,l,v)

theorem pre33_1_2_good : prefixGood ⟨11,7,2⟩ pre33_1_2=true :=
  prefixGood_chain ⟨11,7,2⟩ 1 0 0 pre33_1_2_data rfl (by decide +kernel)

private def pre33_1_8_data : List (Nat × Nat) :=
  [(8,3206163281213), (10,3950284516038), (12,4672158300719), (14,5372174408814), (17,6382102254967),
    (20,7345174593044)]

def pre33_1_8 : List PrefixEntry := pre33_1_8_data.map fun (l,v) => (1,l,v)

theorem pre33_1_8_good : prefixGood ⟨11,7,2⟩ pre33_1_8=true :=
  prefixGood_chain ⟨11,7,2⟩ 1 6 2439420689315 pre33_1_8_data (prefixFind_sound ⟨11,7,2⟩ pre33_1_2 pre33_1_2_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre33Part001

section Pack_Z6970H2307PackedPre34Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre34_2_97_data : List (Nat × Nat) :=
  [(97,20155380402374), (102,20468525170712), (106,20691892486362), (109,20844740432169), (110,20893035372561),
    (111,20940046054279), (112,20985797744254), (113,21030315385389), (114,21073623596349), (115,21115746678163)]

def pre34_2_97 : List PrefixEntry := pre34_2_97_data.map fun (l,v) => (2,l,v)

theorem pre34_2_97_good : prefixGood ⟨12,7,2⟩ pre34_2_97=true :=
  prefixGood_chain ⟨12,7,2⟩ 2 28 9654530403119 pre34_2_97_data (prefixFind_sound ⟨12,7,2⟩ pre34_2_4 pre34_2_4_good (by decide)) (by decide +kernel)

private def pre34_1_2_data : List (Nat × Nat) :=
  [(2,836326723443), (4,1648572112557), (6,2437057194508), (8,3202127778176), (10,3944152276113)]

def pre34_1_2 : List PrefixEntry := pre34_1_2_data.map fun (l,v) => (1,l,v)

theorem pre34_1_2_good : prefixGood ⟨12,7,2⟩ pre34_1_2=true :=
  prefixGood_chain ⟨12,7,2⟩ 1 0 0 pre34_1_2_data rfl (by decide +kernel)

private def pre34_1_12_data : List (Nat × Nat) :=
  [(12,4663519526503), (15,5700983004109), (18,6689826693920), (21,7631554334819), (25,8816585819011),
    (50,14617717295903)]

def pre34_1_12 : List PrefixEntry := pre34_1_12_data.map fun (l,v) => (1,l,v)

theorem pre34_1_12_good : prefixGood ⟨12,7,2⟩ pre34_1_12=true :=
  prefixGood_chain ⟨12,7,2⟩ 1 10 3944152276113 pre34_1_12_data (prefixFind_sound ⟨12,7,2⟩ pre34_1_2 pre34_1_2_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre34Part001

section Pack_Z6970H2307PackedPre35Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre35_512_106_data : List (Nat × Nat) :=
  [(106,20428082133034), (110,20619745850568), (116,20870174038942)]

def pre35_512_106 : List PrefixEntry := pre35_512_106_data.map fun (l,v) => (512,l,v)

theorem pre35_512_106_good : prefixGood ⟨13,7,2⟩ pre35_512_106=true :=
  prefixGood_chain ⟨13,7,2⟩ 512 0 0 pre35_512_106_data rfl (by decide +kernel)

private def pre35_256_92_data : List (Nat × Nat) :=
  [(92,19568819421967), (93,19640301371699), (95,19778083085169), (96,19844445522429), (99,20033787312116)]

def pre35_256_92 : List PrefixEntry := pre35_256_92_data.map fun (l,v) => (256,l,v)

theorem pre35_256_92_good : prefixGood ⟨13,7,2⟩ pre35_256_92=true :=
  prefixGood_chain ⟨13,7,2⟩ 256 0 0 pre35_256_92_data rfl (by decide +kernel)

private def pre35_128_96_data : List (Nat × Nat) :=
  [(96,19840815888612), (98,19968637789649), (103,20260984581585), (104,20315021874477), (105,20367647623515),
    (106,20418889318840), (109,20564579693062), (113,20741063164016), (114,20782180115654), (117,20898713161564),
    (118,20935363990493)]

def pre35_128_96 : List PrefixEntry := pre35_128_96_data.map fun (l,v) => (128,l,v)

theorem pre35_128_96_good : prefixGood ⟨13,7,2⟩ pre35_128_96=true :=
  prefixGood_chain ⟨13,7,2⟩ 128 0 0 pre35_128_96_data rfl (by decide +kernel)

private def pre35_64_90_data : List (Nat × Nat) :=
  [(90,19414163961896), (94,19703695578911), (97,19902813664281), (98,19965917585213), (99,20027437473863),
    (100,20087402988429), (101,20145843420483), (102,20202787694989), (103,20258264377149), (104,20312301670041),
    (105,20364927419079), (107,20466053892958), (108,20514608538559), (110,20607832831938), (111,20652554313037),
    (112,20696049334612), (113,20738342959580), (114,20779459911218), (115,20819424579767), (119,20968236576596),
    (120,21002794072086)]

def pre35_64_90 : List PrefixEntry := pre35_64_90_data.map fun (l,v) => (64,l,v)

theorem pre35_64_90_good : prefixGood ⟨13,7,2⟩ pre35_64_90=true :=
  prefixGood_chain ⟨13,7,2⟩ 64 0 0 pre35_64_90_data rfl (by decide +kernel)

private def pre35_32_101_data : List (Nat × Nat) :=
  [(101,20144110826556), (105,20363194825152), (107,20464321299031), (108,20512875944632), (109,20560126894699),
    (111,20650821719110), (112,20694316740685), (113,20736610365653), (114,20777727317291), (115,20817691985840),
    (116,20856528426385), (117,20894260363201), (118,20930911192130), (122,21067159956992)]

def pre35_32_101 : List PrefixEntry := pre35_32_101_data.map fun (l,v) => (32,l,v)

theorem pre35_32_101_good : prefixGood ⟨13,7,2⟩ pre35_32_101=true :=
  prefixGood_chain ⟨13,7,2⟩ 32 0 0 pre35_32_101_data rfl (by decide +kernel)

private def pre35_16_91_data : List (Nat × Nat) :=
  [(91,19486520558941), (100,20084705724515), (102,20200090431075), (106,20413471850490), (108,20511911274645),
    (109,20559162224712), (110,20605135568024), (111,20649857049123), (112,20693352070698), (113,20735645695666),
    (114,20776762647304), (115,20816727315853), (116,20855563756398), (117,20893295693214), (118,20929946522143),
    (119,20965539312682), (120,21000096808172), (121,21033641432281)]

def pre35_16_91 : List PrefixEntry := pre35_16_91_data.map fun (l,v) => (16,l,v)

theorem pre35_16_91_good : prefixGood ⟨13,7,2⟩ pre35_16_91=true :=
  prefixGood_chain ⟨13,7,2⟩ 16 0 0 pre35_16_91_data rfl (by decide +kernel)

private def pre35_8_22_data : List (Nat × Nat) :=
  [(22,7908981928840), (97,19899605353042), (104,20309093358802), (105,20361719107840), (109,20558651177387),
    (111,20649346001798), (114,20776251599979), (115,20816216268528), (116,20855052709073), (117,20892784645889),
    (118,20929435474818), (119,20965028265357), (120,20999585760847), (121,21033130384956), (122,21065684239680),
    (124,21127906464412)]

def pre35_8_22 : List PrefixEntry := pre35_8_22_data.map fun (l,v) => (8,l,v)

theorem pre35_8_22_good : prefixGood ⟨13,7,2⟩ pre35_8_22=true :=
  prefixGood_chain ⟨13,7,2⟩ 8 0 0 pre35_8_22_data rfl (by decide +kernel)

private def pre35_4_9_data : List (Nat × Nat) :=
  [(9,3571102223128), (22,7908720550159)]

def pre35_4_9 : List PrefixEntry := pre35_4_9_data.map fun (l,v) => (4,l,v)

theorem pre35_4_9_good : prefixGood ⟨13,7,2⟩ pre35_4_9=true :=
  prefixGood_chain ⟨13,7,2⟩ 4 0 0 pre35_4_9_data rfl (by decide +kernel)

private def pre35_4_111_data : List (Nat × Nat) :=
  [(111,20649083683441), (113,20734872329984), (114,20775989281622), (115,20815953950171), (116,20854790390716),
    (118,20929173156461), (119,20964765947000), (120,20999323442490), (121,21032868066599), (122,21065421921323),
    (123,21097006791275)]

def pre35_4_111 : List PrefixEntry := pre35_4_111_data.map fun (l,v) => (4,l,v)

theorem pre35_4_111_good : prefixGood ⟨13,7,2⟩ pre35_4_111=true :=
  prefixGood_chain ⟨13,7,2⟩ 4 22 7908720550159 pre35_4_111_data (prefixFind_sound ⟨13,7,2⟩ pre35_4_9 pre35_4_9_good (by decide)) (by decide +kernel)

private def pre35_2_4_data : List (Nat × Nat) :=
  [(4,1647470919522), (8,3198127521009), (13,5004815632627), (20,7300383809192), (114,20775855971054),
    (117,20892389016964), (118,20929039845893), (119,20964632636432), (120,20999190131922), (121,21032734756031),
    (122,21065288610755), (123,21096873480707), (124,21127510835487), (125,21157221831777)]

def pre35_2_4 : List PrefixEntry := pre35_2_4_data.map fun (l,v) => (2,l,v)

theorem pre35_2_4_good : prefixGood ⟨13,7,2⟩ pre35_2_4=true :=
  prefixGood_chain ⟨13,7,2⟩ 2 0 0 pre35_2_4_data rfl (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre35Part000

section Pack_Z6970H2307PackedPre35Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre35_1_2_data : List (Nat × Nat) :=
  [(2,835987351558), (4,1647441242480), (6,2434687103346), (8,3198079300122), (10,3937998443798),
    (12,4654848700028)]

def pre35_1_2 : List PrefixEntry := pre35_1_2_data.map fun (l,v) => (1,l,v)

theorem pre35_1_2_good : prefixGood ⟨13,7,2⟩ pre35_1_2=true :=
  prefixGood_chain ⟨13,7,2⟩ 1 0 0 pre35_1_2_data rfl (by decide +kernel)

private def pre35_1_15_data : List (Nat × Nat) :=
  [(15,5687804700561), (18,6671324497031), (22,7908520973263), (27,9341292622441), (117,20892321957869),
    (120,20999123072827), (121,21032667696936), (122,21065221551660), (123,21096806421612), (124,21127443776392),
    (125,21157154772682)]

def pre35_1_15 : List PrefixEntry := pre35_1_15_data.map fun (l,v) => (1,l,v)

theorem pre35_1_15_good : prefixGood ⟨13,7,2⟩ pre35_1_15=true :=
  prefixGood_chain ⟨13,7,2⟩ 1 12 4654848700028 pre35_1_15_data (prefixFind_sound ⟨13,7,2⟩ pre35_1_2 pre35_1_2_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre35Part001

section Pack_Z6970H2307PackedPre36Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre36_256_124_data : List (Nat × Nat) :=
  [(124,20818971372124), (128,20925348161714)]

def pre36_256_124 : List PrefixEntry := pre36_256_124_data.map fun (l,v) => (256,l,v)

theorem pre36_256_124_good : prefixGood ⟨14,7,2⟩ pre36_256_124=true :=
  prefixGood_chain ⟨14,7,2⟩ 256 0 0 pre36_256_124_data rfl (by decide +kernel)

private def pre36_64_114_data : List (Nat × Nat) :=
  [(114,20481416690871), (116,20555933893760), (118,20626164657755), (119,20659731014787), (120,20692295148277),
    (121,20723879484298), (122,20754506113684), (130,20967584537936), (131,20990532096848), (132,21012725057267),
    (133,21034182005017), (135,21074960682493), (136,21094318071682)]

def pre36_64_114 : List PrefixEntry := pre36_64_114_data.map fun (l,v) => (64,l,v)

theorem pre36_64_114_good : prefixGood ⟨14,7,2⟩ pre36_64_114=true :=
  prefixGood_chain ⟨14,7,2⟩ 64 0 0 pre36_64_114_data rfl (by decide +kernel)

private def pre36_32_118_data : List (Nat × Nat) :=
  [(118,20624523952771), (120,20690654443293), (122,20752865408700), (123,20782556091444), (125,20839215018086),
    (126,20866225148324), (128,20917709048886), (129,20942222785471), (130,20965943832952)]

def pre36_32_118 : List PrefixEntry := pre36_32_118_data.map fun (l,v) => (32,l,v)

theorem pre36_32_118_good : prefixGood ⟨14,7,2⟩ pre36_32_118=true :=
  prefixGood_chain ⟨14,7,2⟩ 32 0 0 pre36_32_118_data rfl (by decide +kernel)

private def pre36_16_115_data : List (Nat × Nat) :=
  [(115,20516667220063), (121,20721323758206), (123,20781641070336), (124,20810417238188), (125,20838299996978),
    (126,20865310127216), (127,20891468090432), (128,20916794027778), (129,20941307764363), (130,20965028811844),
    (131,20987976370756), (132,21010169331175), (133,21031626278925), (134,21052365494313), (137,21110455045957),
    (138,21128500145981), (140,21162714450164)]

def pre36_16_115 : List PrefixEntry := pre36_16_115_data.map fun (l,v) => (16,l,v)

theorem pre36_16_115_good : prefixGood ⟨14,7,2⟩ pre36_16_115=true :=
  prefixGood_chain ⟨14,7,2⟩ 16 0 0 pre36_16_115_data rfl (by decide +kernel)

private def pre36_8_24_data : List (Nat × Nat) :=
  [(24,8465484847504), (117,20588532627456), (123,20781156106484), (124,20809932274336), (126,20864825163364),
    (127,20890983126580), (128,20916309063926), (130,20964543847992), (131,20987491406904), (132,21009684367323),
    (133,21031141315073), (134,21051880530461), (135,21071919992549), (136,21091277381738), (137,21109970082105),
    (138,21128015182129), (139,21145429480765)]

def pre36_8_24 : List PrefixEntry := pre36_8_24_data.map fun (l,v) => (8,l,v)

theorem pre36_8_24_good : prefixGood ⟨14,7,2⟩ pre36_8_24=true :=
  prefixGood_chain ⟨14,7,2⟩ 8 0 0 pre36_8_24_data rfl (by decide +kernel)

private def pre36_4_9_data : List (Nat × Nat) :=
  [(9,3566033198940), (24,8465236073949), (126,20864576304673), (128,20916060205235), (129,20940573941820),
    (130,20964294989301), (131,20987242548213), (132,21009435508632), (133,21030892456382), (134,21051631671770),
    (135,21071671133858), (136,21091028523047), (137,21109721223414), (138,21127766323438), (139,21145180622074),
    (140,21161980627621)]

def pre36_4_9 : List PrefixEntry := pre36_4_9_data.map fun (l,v) => (4,l,v)

theorem pre36_4_9_good : prefixGood ⟨14,7,2⟩ pre36_4_9=true :=
  prefixGood_chain ⟨14,7,2⟩ 4 0 0 pre36_4_9_data rfl (by decide +kernel)

private def pre36_2_4_data : List (Nat × Nat) :=
  [(4,1646337278211), (9,3565933290662), (15,5674640273592), (23,8175978372748), (113,20439074954739),
    (131,20987116053032), (132,21009309013451), (133,21030765961201), (134,21051505176589), (135,21071544638677),
    (136,21090902027866), (137,21109594728233), (138,21127639828257), (139,21145054126893), (140,21161854132440),
    (141,21178056066750)]

def pre36_2_4 : List PrefixEntry := pre36_2_4_data.map fun (l,v) => (2,l,v)

theorem pre36_2_4_good : prefixGood ⟨14,7,2⟩ pre36_2_4=true :=
  prefixGood_chain ⟨14,7,2⟩ 2 0 0 pre36_2_4_data rfl (by decide +kernel)

private def pre36_1_2_data : List (Nat × Nat) :=
  [(2,835647563432)]

def pre36_1_2 : List PrefixEntry := pre36_1_2_data.map fun (l,v) => (1,l,v)

theorem pre36_1_2_good : prefixGood ⟨14,7,2⟩ pre36_1_2=true :=
  prefixGood_chain ⟨14,7,2⟩ 1 0 0 pre36_1_2_data rfl (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre36Part000

section Pack_Z6970H2307PackedPre37Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre37_512_66_data : List (Nat × Nat) :=
  [(66,17574518000223), (73,18483154683818), (84,19656916889012), (86,19840117639097), (88,20014722417127)]

def pre37_512_66 : List PrefixEntry := pre37_512_66_data.map fun (l,v) => (512,l,v)

theorem pre37_512_66_good : prefixGood ⟨3,8,1⟩ pre37_512_66=true :=
  prefixGood_chain ⟨3,8,1⟩ 512 0 0 pre37_512_66_data rfl (by decide +kernel)

private def pre37_256_78_data : List (Nat × Nat) :=
  [(78,19044550119179), (92,20330807271300), (95,20553603503844)]

def pre37_256_78 : List PrefixEntry := pre37_256_78_data.map fun (l,v) => (256,l,v)

theorem pre37_256_78_good : prefixGood ⟨3,8,1⟩ pre37_256_78=true :=
  prefixGood_chain ⟨3,8,1⟩ 256 0 0 pre37_256_78_data rfl (by decide +kernel)

private def pre37_128_67_data : List (Nat × Nat) :=
  [(67,17695032055967), (74,18584566665555), (76,18814957818921), (91,20243472767715), (93,20397763868186),
    (98,20750512305295)]

def pre37_128_67 : List PrefixEntry := pre37_128_67_data.map fun (l,v) => (128,l,v)

theorem pre37_128_67_good : prefixGood ⟨3,8,1⟩ pre37_128_67=true :=
  prefixGood_chain ⟨3,8,1⟩ 128 0 0 pre37_128_67_data rfl (by decide +kernel)

private def pre37_64_70_data : List (Nat × Nat) :=
  [(70,18087233873030), (71,18214233929588), (75,18695709928429), (76,18809635433215), (77,18921057658183),
    (81,19342441985322), (82,19441891706700), (83,19539053885630), (85,19726655537234), (86,19817164317407),
    (87,19905524169675), (90,20158048855753), (94,20466696172770), (96,20609584645036), (97,20678281963364),
    (99,20810339621561), (100,20873761913963)]

def pre37_64_70 : List PrefixEntry := pre37_64_70_data.map fun (l,v) => (64,l,v)

theorem pre37_64_70_good : prefixGood ⟨3,8,1⟩ pre37_64_70=true :=
  prefixGood_chain ⟨3,8,1⟩ 64 0 0 pre37_64_70_data rfl (by decide +kernel)

private def pre37_32_69_data : List (Nat × Nat) :=
  [(69,17954190055607), (72,18335228383515), (74,18575928871148), (75,18692394519728), (78,19026697800450),
    (79,19133223024850), (80,19237354008061), (82,19438576297999), (83,19535738476929), (84,19630648158621),
    (86,19813848908706), (87,19902208760974), (88,19988453686736), (89,20072617423292), (90,20154733447052),
    (91,20234834973308), (93,20389126073779), (94,20463380764069), (95,20535751185115), (101,20932171965950)]

def pre37_32_69 : List PrefixEntry := pre37_32_69_data.map fun (l,v) => (32,l,v)

theorem pre37_32_69_good : prefixGood ⟨3,8,1⟩ pre37_32_69=true :=
  prefixGood_chain ⟨3,8,1⟩ 32 0 0 pre37_32_69_data rfl (by decide +kernel)

private def pre37_16_34_data : List (Nat × Nat) :=
  [(34,11377767596231), (73,18455037362701), (77,18915893658756), (79,19131374434124), (80,19235505417335),
    (82,19436727707273), (84,19628799567895), (85,19721491537807), (86,19812000317980), (87,19900360170248),
    (88,19986605096010), (89,20070768832566), (90,20152884856326), (91,20232986382582), (92,20311106361845),
    (93,20387277483053), (94,20461532173343), (95,20533902594389), (96,20604420645609), (97,20673117963937)]

def pre37_16_34 : List PrefixEntry := pre37_16_34_data.map fun (l,v) => (16,l,v)

theorem pre37_16_34_good : prefixGood ⟨3,8,1⟩ pre37_16_34=true :=
  prefixGood_chain ⟨3,8,1⟩ 16 0 0 pre37_16_34_data rfl (by decide +kernel)

private def pre37_8_16_data : List (Nat × Nat) :=
  [(16,6081658908575)]

def pre37_8_16 : List PrefixEntry := pre37_8_16_data.map fun (l,v) => (8,l,v)

theorem pre37_8_16_good : prefixGood ⟨3,8,1⟩ pre37_8_16=true :=
  prefixGood_chain ⟨3,8,1⟩ 8 0 0 pre37_8_16_data rfl (by decide +kernel)

private def pre37_8_34_data : List (Nat × Nat) :=
  [(34,11376809795829), (79,19130398149983), (81,19336301701754), (88,19985628811869), (89,20069792548425),
    (90,20151908572185), (92,20310130077704), (93,20386301198912), (94,20460555889202), (95,20532926310248),
    (96,20603444361468), (97,20672141679796), (98,20739049636021), (99,20804199337993), (100,20867621630395)]

def pre37_8_34 : List PrefixEntry := pre37_8_34_data.map fun (l,v) => (8,l,v)

theorem pre37_8_34_good : prefixGood ⟨3,8,1⟩ pre37_8_34=true :=
  prefixGood_chain ⟨3,8,1⟩ 8 16 6081658908575 pre37_8_34_data (prefixFind_sound ⟨3,8,1⟩ pre37_8_16 pre37_8_16_good (by decide)) (by decide +kernel)

private def pre37_4_8_data : List (Nat × Nat) :=
  [(8,3214544919010), (16,6081282042721), (25,8918231783662)]

def pre37_4_8 : List PrefixEntry := pre37_4_8_data.map fun (l,v) => (4,l,v)

theorem pre37_4_8_good : prefixGood ⟨3,8,1⟩ pre37_4_8=true :=
  prefixGood_chain ⟨3,8,1⟩ 4 0 0 pre37_4_8_data rfl (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre37Part000

section Pack_Z6970H2307PackedPre38Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre38_512_66_data : List (Nat × Nat) :=
  [(66,17574518000223), (73,18483154683818), (84,19656916889012), (86,19840117639097), (88,20014722417127)]

def pre38_512_66 : List PrefixEntry := pre38_512_66_data.map fun (l,v) => (512,l,v)

theorem pre38_512_66_good : prefixGood ⟨3,8,2⟩ pre38_512_66=true :=
  prefixGood_chain ⟨3,8,2⟩ 512 0 0 pre38_512_66_data rfl (by decide +kernel)

private def pre38_256_78_data : List (Nat × Nat) :=
  [(78,19044550119179), (92,20330807271300), (95,20553603503844)]

def pre38_256_78 : List PrefixEntry := pre38_256_78_data.map fun (l,v) => (256,l,v)

theorem pre38_256_78_good : prefixGood ⟨3,8,2⟩ pre38_256_78=true :=
  prefixGood_chain ⟨3,8,2⟩ 256 0 0 pre38_256_78_data rfl (by decide +kernel)

private def pre38_128_67_data : List (Nat × Nat) :=
  [(67,17695032055967), (74,18584566665555), (76,18814957818921), (91,20243472767715), (93,20397763868186),
    (98,20750512305295)]

def pre38_128_67 : List PrefixEntry := pre38_128_67_data.map fun (l,v) => (128,l,v)

theorem pre38_128_67_good : prefixGood ⟨3,8,2⟩ pre38_128_67=true :=
  prefixGood_chain ⟨3,8,2⟩ 128 0 0 pre38_128_67_data rfl (by decide +kernel)

private def pre38_64_70_data : List (Nat × Nat) :=
  [(70,18087233873030), (71,18214233929588), (75,18695709928429), (76,18809635433215), (77,18921057658183),
    (81,19342441985322), (82,19441891706700), (83,19539053885630), (85,19726655537234), (86,19817164317407),
    (87,19905524169675), (90,20158048855753), (94,20466696172770), (96,20609584645036), (97,20678281963364),
    (99,20810339621561), (100,20873761913963)]

def pre38_64_70 : List PrefixEntry := pre38_64_70_data.map fun (l,v) => (64,l,v)

theorem pre38_64_70_good : prefixGood ⟨3,8,2⟩ pre38_64_70=true :=
  prefixGood_chain ⟨3,8,2⟩ 64 0 0 pre38_64_70_data rfl (by decide +kernel)

private def pre38_32_69_data : List (Nat × Nat) :=
  [(69,17954190055607), (72,18335228383515), (74,18575928871148), (75,18692394519728), (78,19026697800450),
    (79,19133223024850), (80,19237354008061), (82,19438576297999), (83,19535738476929), (84,19630648158621),
    (86,19813848908706), (87,19902208760974), (88,19988453686736), (89,20072617423292), (90,20154733447052),
    (91,20234834973308), (93,20389126073779), (94,20463380764069), (95,20535751185115), (101,20932171965950)]

def pre38_32_69 : List PrefixEntry := pre38_32_69_data.map fun (l,v) => (32,l,v)

theorem pre38_32_69_good : prefixGood ⟨3,8,2⟩ pre38_32_69=true :=
  prefixGood_chain ⟨3,8,2⟩ 32 0 0 pre38_32_69_data rfl (by decide +kernel)

private def pre38_16_34_data : List (Nat × Nat) :=
  [(34,11377767596231), (73,18455037362701), (77,18915893658756), (79,19131374434124), (80,19235505417335),
    (82,19436727707273), (84,19628799567895), (85,19721491537807), (86,19812000317980), (87,19900360170248),
    (88,19986605096010), (89,20070768832566), (90,20152884856326), (91,20232986382582), (92,20311106361845),
    (93,20387277483053), (94,20461532173343), (95,20533902594389), (96,20604420645609), (97,20673117963937)]

def pre38_16_34 : List PrefixEntry := pre38_16_34_data.map fun (l,v) => (16,l,v)

theorem pre38_16_34_good : prefixGood ⟨3,8,2⟩ pre38_16_34=true :=
  prefixGood_chain ⟨3,8,2⟩ 16 0 0 pre38_16_34_data rfl (by decide +kernel)

private def pre38_8_16_data : List (Nat × Nat) :=
  [(16,6081658908575)]

def pre38_8_16 : List PrefixEntry := pre38_8_16_data.map fun (l,v) => (8,l,v)

theorem pre38_8_16_good : prefixGood ⟨3,8,2⟩ pre38_8_16=true :=
  prefixGood_chain ⟨3,8,2⟩ 8 0 0 pre38_8_16_data rfl (by decide +kernel)

private def pre38_8_34_data : List (Nat × Nat) :=
  [(34,11376809795829), (79,19130398149983), (81,19336301701754), (88,19985628811869), (89,20069792548425),
    (90,20151908572185), (92,20310130077704), (93,20386301198912), (94,20460555889202), (95,20532926310248),
    (96,20603444361468), (97,20672141679796), (98,20739049636021), (99,20804199337993), (100,20867621630395)]

def pre38_8_34 : List PrefixEntry := pre38_8_34_data.map fun (l,v) => (8,l,v)

theorem pre38_8_34_good : prefixGood ⟨3,8,2⟩ pre38_8_34=true :=
  prefixGood_chain ⟨3,8,2⟩ 8 16 6081658908575 pre38_8_34_data (prefixFind_sound ⟨3,8,2⟩ pre38_8_16 pre38_8_16_good (by decide)) (by decide +kernel)

private def pre38_4_8_data : List (Nat × Nat) :=
  [(8,3214544919010), (16,6081282042721), (25,8918231783662)]

def pre38_4_8 : List PrefixEntry := pre38_4_8_data.map fun (l,v) => (4,l,v)

theorem pre38_4_8_good : prefixGood ⟨3,8,2⟩ pre38_4_8=true :=
  prefixGood_chain ⟨3,8,2⟩ 4 0 0 pre38_4_8_data rfl (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre38Part000

section Pack_Z6970H2307PackedPre39Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre39_512_73_data : List (Nat × Nat) :=
  [(73,18316220715083), (90,19972289116063), (92,20126145500830)]

def pre39_512_73 : List PrefixEntry := pre39_512_73_data.map fun (l,v) => (512,l,v)

theorem pre39_512_73_good : prefixGood ⟨4,8,2⟩ pre39_512_73=true :=
  prefixGood_chain ⟨4,8,2⟩ 512 0 0 pre39_512_73_data rfl (by decide +kernel)

private def pre39_256_94_data : List (Nat × Nat) :=
  [(94,20264254775299), (100,20659376619367)]

def pre39_256_94 : List PrefixEntry := pre39_256_94_data.map fun (l,v) => (256,l,v)

theorem pre39_256_94_good : prefixGood ⟨4,8,2⟩ pre39_256_94=true :=
  prefixGood_chain ⟨4,8,2⟩ 256 0 0 pre39_256_94_data rfl (by decide +kernel)

private def pre39_128_74_data : List (Nat × Nat) :=
  [(74,18416520348373), (79,18960844736750), (80,19062457960841), (81,19161739536563), (88,19794420700389)]

def pre39_128_74 : List PrefixEntry := pre39_128_74_data.map fun (l,v) => (128,l,v)

theorem pre39_128_74_good : prefixGood ⟨4,8,2⟩ pre39_128_74=true :=
  prefixGood_chain ⟨4,8,2⟩ 128 0 0 pre39_128_74_data rfl (by decide +kernel)

private def pre39_64_81_data : List (Nat × Nat) :=
  [(81,19156922281533), (82,19253908309467), (83,19348634601492), (84,19441136684256), (86,19619608899759),
    (87,19705648653949), (88,19789603445359), (91,20029297575136), (97,20456904927920), (98,20521838299295),
    (101,20706408408092), (102,20764624029332), (105,20929769157549)]

def pre39_64_81 : List PrefixEntry := pre39_64_81_data.map fun (l,v) => (64,l,v)

theorem pre39_64_81_good : prefixGood ⟨4,8,2⟩ pre39_64_81=true :=
  prefixGood_chain ⟨4,8,2⟩ 64 0 0 pre39_64_81_data rfl (by decide +kernel)

private def pre39_32_80_data : List (Nat × Nat) :=
  [(80,19054622417988), (82,19250890021644), (83,19345616313669), (85,19528431511465), (87,19702630366126),
    (88,19786585157536), (89,19868489081653), (90,19948375949413), (91,20026279287313), (92,20102232334180),
    (93,20176268044630), (94,20248419089180), (95,20318717851021), (96,20387196429473), (97,20453886640097),
    (99,20582027788646), (103,20818217905689), (104,20873256435236), (106,20978730465996), (107,21029224194933)]

def pre39_32_80 : List PrefixEntry := pre39_32_80_data.map fun (l,v) => (32,l,v)

theorem pre39_32_80_good : prefixGood ⟨4,8,2⟩ pre39_32_80=true :=
  prefixGood_chain ⟨4,8,2⟩ 32 0 0 pre39_32_80_data rfl (by decide +kernel)

private def pre39_16_36_data : List (Nat × Nat) :=
  [(36,11817082948953), (76,18632130940450), (77,18740958571647), (86,19614907212706), (88,19784901758306),
    (89,19866805682423), (90,19946692550183), (91,20024595888083), (92,20100548934950), (94,20246735689950),
    (95,20317034451791), (96,20385513030243), (97,20452203240867), (98,20517136612242), (99,20580344389416),
    (100,20641857534018), (101,20701706721039), (102,20759922342279)]

def pre39_16_36 : List PrefixEntry := pre39_16_36_data.map fun (l,v) => (16,l,v)

theorem pre39_16_36_good : prefixGood ⟨4,8,2⟩ pre39_16_36=true :=
  prefixGood_chain ⟨4,8,2⟩ 16 0 0 pre39_16_36_data rfl (by decide +kernel)

private def pre39_8_17_data : List (Nat × Nat) :=
  [(17,6400973739252)]

def pre39_8_17 : List PrefixEntry := pre39_8_17_data.map fun (l,v) => (8,l,v)

theorem pre39_8_17_good : prefixGood ⟨4,8,2⟩ pre39_8_17=true :=
  prefixGood_chain ⟨4,8,2⟩ 8 0 0 pre39_8_17_data rfl (by decide +kernel)

private def pre39_8_37_data : List (Nat × Nat) :=
  [(37,12056292831975), (75,18519935189608), (84,19435545790691), (85,19525858905723), (91,20023706681571),
    (93,20173695438888), (94,20245846483438), (95,20316145245279), (96,20384623823731), (97,20451314034355),
    (98,20516247405730), (99,20579455182904), (100,20640968327506), (101,20700817514527), (102,20759033135767),
    (103,20815645299947), (104,20870683829494)]

def pre39_8_37 : List PrefixEntry := pre39_8_37_data.map fun (l,v) => (8,l,v)

theorem pre39_8_37_good : prefixGood ⟨4,8,2⟩ pre39_8_37=true :=
  prefixGood_chain ⟨4,8,2⟩ 8 17 6400973739252 pre39_8_37_data (prefixFind_sound ⟨4,8,2⟩ pre39_8_17 pre39_8_17_good (by decide)) (by decide +kernel)

private def pre39_4_8_data : List (Nat × Nat) :=
  [(8,3210650132438), (17,6400603425999), (26,9175808144187)]

def pre39_4_8 : List PrefixEntry := pre39_4_8_data.map fun (l,v) => (4,l,v)

theorem pre39_4_8_good : prefixGood ⟨4,8,2⟩ pre39_4_8=true :=
  prefixGood_chain ⟨4,8,2⟩ 4 0 0 pre39_4_8_data rfl (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre39Part000

section Pack_Z6970H2307PackedPre40Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre40_64_121_data : List (Nat × Nat) :=
  [(121,20817874755187), (124,20898705503122), (128,20993669032753)]

def pre40_64_121 : List PrefixEntry := pre40_64_121_data.map fun (l,v) => (64,l,v)

theorem pre40_64_121_good : prefixGood ⟨7,8,1⟩ pre40_64_121=true :=
  prefixGood_chain ⟨7,8,1⟩ 64 0 0 pre40_64_121_data rfl (by decide +kernel)

private def pre40_32_131_data : List (Nat × Nat) :=
  [(131,21053688710094), (134,21109152660679), (135,21126195890779)]

def pre40_32_131 : List PrefixEntry := pre40_32_131_data.map fun (l,v) => (32,l,v)

theorem pre40_32_131_good : prefixGood ⟨7,8,1⟩ pre40_32_131=true :=
  prefixGood_chain ⟨7,8,1⟩ 32 0 0 pre40_32_131_data rfl (by decide +kernel)

private def pre40_16_80_data : List (Nat × Nat) :=
  [(80,18503181859374), (117,20692392626272), (119,20755366803916), (120,20785280353936), (121,20814177420008),
    (123,20869017799253), (124,20895008167943), (126,20944244520587), (130,21032365316976), (132,21071596021002)]

def pre40_16_80 : List PrefixEntry := pre40_16_80_data.map fun (l,v) => (16,l,v)

theorem pre40_16_80_good : prefixGood ⟨7,8,1⟩ pre40_16_80=true :=
  prefixGood_chain ⟨7,8,1⟩ 16 0 0 pre40_16_80_data rfl (by decide +kernel)

private def pre40_8_18_data : List (Nat × Nat) :=
  [(18,6676385595498), (118,20723713238501), (122,20841382801292), (124,20894308962858), (126,20943545315502),
    (128,20989272492489), (129,21010875215169), (130,21031666111891), (131,21051666356721), (132,21070896815917),
    (136,21140527382848), (138,21171243972688), (139,21185644492208)]

def pre40_8_18 : List PrefixEntry := pre40_8_18_data.map fun (l,v) => (8,l,v)

theorem pre40_8_18_good : prefixGood ⟨7,8,1⟩ pre40_8_18=true :=
  prefixGood_chain ⟨7,8,1⟩ 8 0 0 pre40_8_18_data rfl (by decide +kernel)

private def pre40_4_8_data : List (Nat × Nat) :=
  [(8,3198876538556)]

def pre40_4_8 : List PrefixEntry := pre40_4_8_data.map fun (l,v) => (4,l,v)

theorem pre40_4_8_good : prefixGood ⟨7,8,1⟩ pre40_4_8=true :=
  prefixGood_chain ⟨7,8,1⟩ 4 0 0 pre40_4_8_data rfl (by decide +kernel)

private def pre40_4_17_data : List (Nat × Nat) :=
  [(17,6353094658099), (28,9623388361275), (123,20867959705795), (125,20919018069601), (127,20966477569561),
    (128,20988913604116), (129,21010516326796), (130,21031307223518), (131,21051307468348), (132,21070537927544),
    (133,21089019160688), (134,21106771418933), (135,21123814649033)]

def pre40_4_17 : List PrefixEntry := pre40_4_17_data.map fun (l,v) => (4,l,v)

theorem pre40_4_17_good : prefixGood ⟨7,8,1⟩ pre40_4_17=true :=
  prefixGood_chain ⟨7,8,1⟩ 4 8 3198876538556 pre40_4_17_data (prefixFind_sound ⟨7,8,1⟩ pre40_4_8 pre40_4_8_good (by decide)) (by decide +kernel)

private def pre40_2_4_data : List (Nat × Nat) :=
  [(4,1647571551270), (8,3198767788393)]

def pre40_2_4 : List PrefixEntry := pre40_2_4_data.map fun (l,v) => (2,l,v)

theorem pre40_2_4_good : prefixGood ⟨7,8,1⟩ pre40_2_4=true :=
  prefixGood_chain ⟨7,8,1⟩ 2 0 0 pre40_2_4_data rfl (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre40Part000
