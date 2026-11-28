import ProximityPrize.SubmissionLower.Z6970H2307OrderPackedTools
import ProximityPrize.SubmissionLower.Bundle6970_d00f88131f2f793d

section Pack_Z6970H2307PackedPre01Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre1_2_32_data : List (Nat × Nat) :=
  [(32,12568577166404), (34,13285205724291), (38,14695031198758), (39,15042641095547), (43,16413877009520),
    (44,16751915705374), (47,17754681843457), (48,18085174554584), (50,18740553419953), (51,19065452097670)]

def pre1_2_32 : List PrefixEntry := pre1_2_32_data.map fun (l,v) => (2,l,v)

theorem pre1_2_32_good : prefixGood ⟨1,3,1⟩ pre1_2_32=true :=
  prefixGood_chain ⟨1,3,1⟩ 2 28 11111649191822 pre1_2_32_data (prefixFind_sound ⟨1,3,1⟩ pre1_2_12 pre1_2_12_good (by decide)) (by decide +kernel)

private def pre1_2_52_data : List (Nat × Nat) :=
  [(52,19388498620290)]

def pre1_2_52 : List PrefixEntry := pre1_2_52_data.map fun (l,v) => (2,l,v)

theorem pre1_2_52_good : prefixGood ⟨1,3,1⟩ pre1_2_52=true :=
  prefixGood_chain ⟨1,3,1⟩ 2 51 19065452097670 pre1_2_52_data (prefixFind_sound ⟨1,3,1⟩ pre1_2_32 pre1_2_32_good (by decide)) (by decide +kernel)

private def pre1_1_2_data : List (Nat × Nat) :=
  [(2,848131476387), (4,1687709326753), (6,2518776578774), (8,3341376600054), (10,4155553095325)]

def pre1_1_2 : List PrefixEntry := pre1_1_2_data.map fun (l,v) => (1,l,v)

theorem pre1_1_2_good : prefixGood ⟨1,3,1⟩ pre1_1_2=true :=
  prefixGood_chain ⟨1,3,1⟩ 1 0 0 pre1_1_2_data rfl (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre01Part002

section Pack_Z6970H2307PackedPre02Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre2_2_36_data : List (Nat × Nat) :=
  [(36,13924017744679), (40,15302957386710), (43,16316104004358), (45,16981612590746), (47,17639249104492),
    (48,17965133144732), (50,18611068588917), (51,18931134368906), (53,19565498124168)]

def pre2_2_36 : List PrefixEntry := pre2_2_36_data.map fun (l,v) => (2,l,v)

theorem pre2_2_36_good : prefixGood ⟨2,3,1⟩ pre2_2_36=true :=
  prefixGood_chain ⟨2,3,1⟩ 2 32 12512581807346 pre2_2_36_data (prefixFind_sound ⟨2,3,1⟩ pre2_2_16 pre2_2_16_good (by decide)) (by decide +kernel)

private def pre2_1_2_data : List (Nat × Nat) :=
  [(2,847794320219), (4,1686589283838), (6,2516432652222), (8,3337372205685), (10,4149456597186)]

def pre2_1_2 : List PrefixEntry := pre2_1_2_data.map fun (l,v) => (1,l,v)

theorem pre2_1_2_good : prefixGood ⟨2,3,1⟩ pre2_1_2=true :=
  prefixGood_chain ⟨2,3,1⟩ 1 0 0 pre2_1_2_data rfl (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre02Part002

section Pack_Z6970H2307PackedPre03Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre3_2_45_data : List (Nat × Nat) :=
  [(45,16873568687315), (46,17198833249783), (49,18162421283500), (51,18794723609492), (53,19419030880929),
    (54,19728207001123)]

def pre3_2_45 : List PrefixEntry := pre3_2_45_data.map fun (l,v) => (2,l,v)

theorem pre3_2_45_good : prefixGood ⟨3,3,1⟩ pre3_2_45=true :=
  prefixGood_chain ⟨3,3,1⟩ 2 40 15216368248870 pre3_2_45_data (prefixFind_sound ⟨3,3,1⟩ pre3_2_20 pre3_2_20_good (by decide)) (by decide +kernel)

private def pre3_1_2_data : List (Nat × Nat) :=
  [(2,847456706515), (4,1685466564731)]

def pre3_1_2 : List PrefixEntry := pre3_1_2_data.map fun (l,v) => (1,l,v)

theorem pre3_1_2_good : prefixGood ⟨3,3,1⟩ pre3_1_2=true :=
  prefixGood_chain ⟨3,3,1⟩ 1 0 0 pre3_1_2_data rfl (by decide +kernel)

private def pre3_1_6_data : List (Nat × Nat) :=
  [(6,2514080049505), (8,3333349028422), (10,4143326445422), (12,4944066036733), (14,5735621815598)]

def pre3_1_6 : List PrefixEntry := pre3_1_6_data.map fun (l,v) => (1,l,v)

theorem pre3_1_6_good : prefixGood ⟨3,3,1⟩ pre3_1_6=true :=
  prefixGood_chain ⟨3,3,1⟩ 1 4 1685466564731 pre3_1_6_data (prefixFind_sound ⟨3,3,1⟩ pre3_1_2 pre3_1_2_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre03Part002

section Pack_Z6970H2307PackedPre04Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre4_2_51_data : List (Nat × Nat) :=
  [(51,18656580738829), (52,18964676123622), (53,19270708450662), (54,19574687077096)]

def pre4_2_51 : List PrefixEntry := pre4_2_51_data.map fun (l,v) => (2,l,v)

theorem pre4_2_51_good : prefixGood ⟨4,3,1⟩ pre4_2_51=true :=
  prefixGood_chain ⟨4,3,1⟩ 2 46 17084830970741 pre4_2_51_data (prefixFind_sound ⟨4,3,1⟩ pre4_2_24 pre4_2_24_good (by decide)) (by decide +kernel)

private def pre4_1_2_data : List (Nat × Nat) :=
  [(2,847118637991), (4,1684340854001), (6,2511719161850), (8,3329308464367)]

def pre4_1_2 : List PrefixEntry := pre4_1_2_data.map fun (l,v) => (1,l,v)

theorem pre4_1_2_good : prefixGood ⟨4,3,1⟩ pre4_1_2=true :=
  prefixGood_chain ⟨4,3,1⟩ 1 0 0 pre4_1_2_data rfl (by decide +kernel)

private def pre4_1_10_data : List (Nat × Nat) :=
  [(10,4137164711289), (12,4935344457326), (14,5723906309973), (16,6502909981797), (18,7272415709188),
    (20,8032485478734)]

def pre4_1_10 : List PrefixEntry := pre4_1_10_data.map fun (l,v) => (1,l,v)

theorem pre4_1_10_good : prefixGood ⟨4,3,1⟩ pre4_1_10=true :=
  prefixGood_chain ⟨4,3,1⟩ 1 8 3329308464367 pre4_1_10_data (prefixFind_sound ⟨4,3,1⟩ pre4_1_2 pre4_1_2_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre04Part002

section Pack_Z6970H2307PackedPre07Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre7_1_6_data : List (Nat × Nat) :=
  [(6,2504589856498), (8,3317085613760), (10,4118495342908), (12,4908883104467), (14,5688316890308),
    (16,6456868207182)]

def pre7_1_6 : List PrefixEntry := pre7_1_6_data.map fun (l,v) => (1,l,v)

theorem pre7_1_6_good : prefixGood ⟨7,3,1⟩ pre7_1_6=true :=
  prefixGood_chain ⟨7,3,1⟩ 1 4 1680947210950 pre7_1_6_data (prefixFind_sound ⟨7,3,1⟩ pre7_1_2 pre7_1_2_good (by decide)) (by decide +kernel)

private def pre7_1_18_data : List (Nat × Nat) :=
  [(18,7214611457465), (20,7961624675824), (22,8697988349689), (25,9782749614421), (28,10844030635570),
    (31,11882135820221)]

def pre7_1_18 : List PrefixEntry := pre7_1_18_data.map fun (l,v) => (1,l,v)

theorem pre7_1_18_good : prefixGood ⟨7,3,1⟩ pre7_1_18=true :=
  prefixGood_chain ⟨7,3,1⟩ 1 16 6456868207182 pre7_1_18_data (prefixFind_sound ⟨7,3,1⟩ pre7_1_6 pre7_1_6_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre07Part002

section Pack_Z6970H2307PackedPre08Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre8_1_10_data : List (Nat × Nat) :=
  [(10,4112213988775), (12,4899969532752), (14,5676316185500), (16,6441329103546), (18,7195088175504),
    (20,7937676914295)]

def pre8_1_10 : List PrefixEntry := pre8_1_10_data.map fun (l,v) => (1,l,v)

theorem pre8_1_10_good : prefixGood ⟨8,3,1⟩ pre8_1_10=true :=
  prefixGood_chain ⟨8,3,1⟩ 1 8 3312978914348 pre8_1_10_data (prefixFind_sound ⟨8,3,1⟩ pre8_1_2 pre8_1_2_good (by decide)) (by decide +kernel)

private def pre8_1_23_data : List (Nat × Nat) :=
  [(23,9030808069244), (26,10099313758707), (29,11143520067492), (33,12498586020406), (35,13160407811221),
    (40,14770005657747)]

def pre8_1_23 : List PrefixEntry := pre8_1_23_data.map fun (l,v) => (1,l,v)

theorem pre8_1_23_good : prefixGood ⟨8,3,1⟩ pre8_1_23=true :=
  prefixGood_chain ⟨8,3,1⟩ 1 20 7937676914295 pre8_1_23_data (prefixFind_sound ⟨8,3,1⟩ pre8_1_10 pre8_1_10_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre08Part002

section Pack_Z6970H2307PackedPre09Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre9_1_14_data : List (Nat × Nat) :=
  [(14,5664251448166), (16,6425702201828), (19,7545962128980), (22,8640198244816), (25,9708741828099),
    (28,10751944718436)]

def pre9_1_14 : List PrefixEntry := pre9_1_14_data.map fun (l,v) => (1,l,v)

theorem pre9_1_14_good : prefixGood ⟨9,3,1⟩ pre9_1_14=true :=
  prefixGood_chain ⟨9,3,1⟩ 1 12 4891012298375 pre9_1_14_data (prefixFind_sound ⟨9,3,1⟩ pre9_1_2 pre9_1_2_good (by decide)) (by decide +kernel)

private def pre9_1_32_data : List (Nat × Nat) :=
  [(32,12104104266886), (37,13733279022717), (44,15903574935897), (54,18789886145475), (57,19608666684798),
    (58,19876903598304)]

def pre9_1_32 : List PrefixEntry := pre9_1_32_data.map fun (l,v) => (1,l,v)

theorem pre9_1_32_good : prefixGood ⟨9,3,1⟩ pre9_1_32=true :=
  prefixGood_chain ⟨9,3,1⟩ 1 28 10751944718436 pre9_1_32_data (prefixFind_sound ⟨9,3,1⟩ pre9_1_14 pre9_1_14_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre09Part002

section Pack_Z6970H2307PackedPre10Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre10_2_28_data : List (Nat × Nat) :=
  [(28,10808875194043), (31,11840010012270), (35,13178479887714), (39,14476068192398), (43,15733539899262),
    (46,16650782850656), (49,17546225533170)]

def pre10_2_28 : List PrefixEntry := pre10_2_28_data.map fun (l,v) => (2,l,v)

theorem pre10_2_28_good : prefixGood ⟨2,4,1⟩ pre10_2_28=true :=
  prefixGood_chain ⟨2,4,1⟩ 2 24 9397056524747 pre10_2_28_data (prefixFind_sound ⟨2,4,1⟩ pre10_2_8 pre10_2_8_good (by decide)) (by decide +kernel)

private def pre10_2_50_data : List (Nat × Nat) :=
  [(50,17839919042517), (52,18420198386703), (54,18991082340380), (55,19273031591386), (56,19552668619240),
    (57,19830005606634)]

def pre10_2_50 : List PrefixEntry := pre10_2_50_data.map fun (l,v) => (2,l,v)

theorem pre10_2_50_good : prefixGood ⟨2,4,1⟩ pre10_2_50=true :=
  prefixGood_chain ⟨2,4,1⟩ 2 49 17546225533170 pre10_2_50_data (prefixFind_sound ⟨2,4,1⟩ pre10_2_28 pre10_2_28_good (by decide)) (by decide +kernel)

private def pre10_1_2_data : List (Nat × Nat) :=
  [(2,845765739098), (4,1679855057608), (6,2502349370986)]

def pre10_1_2 : List PrefixEntry := pre10_1_2_data.map fun (l,v) => (1,l,v)

theorem pre10_1_2_good : prefixGood ⟨2,4,1⟩ pre10_1_2=true :=
  prefixGood_chain ⟨2,4,1⟩ 1 0 0 pre10_1_2_data rfl (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre10Part002

section Pack_Z6970H2307PackedPre11Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre11_2_36_data : List (Nat × Nat) :=
  [(36,13438311313802), (37,13760410268746), (39,14396802885992), (44,15942875442338), (47,16840261753566),
    (50,17715401250054), (54,18848279915949), (55,19125522986269), (56,19400402432753), (57,19672931770317),
    (58,19943124482162)]

def pre11_2_36 : List PrefixEntry := pre11_2_36_data.map fun (l,v) => (2,l,v)

theorem pre11_2_36_good : prefixGood ⟨3,4,1⟩ pre11_2_36=true :=
  prefixGood_chain ⟨3,4,1⟩ 2 31 11788264805062 pre11_2_36_data (prefixFind_sound ⟨3,4,1⟩ pre11_2_15 pre11_2_15_good (by decide)) (by decide +kernel)

private def pre11_1_2_data : List (Nat × Nat) :=
  [(2,845428828761), (4,1678736600826), (6,2500009834107), (8,3309336970022), (10,4106808037874)]

def pre11_1_2 : List PrefixEntry := pre11_1_2_data.map fun (l,v) => (1,l,v)

theorem pre11_1_2_good : prefixGood ⟨3,4,1⟩ pre11_1_2=true :=
  prefixGood_chain ⟨3,4,1⟩ 1 0 0 pre11_1_2_data rfl (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre11Part002

section Pack_Z6970H2307PackedPre12Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre12_2_47_data : List (Nat × Nat) :=
  [(47,16727607965431), (52,18151637021396), (55,18976431594076), (56,19246515433157), (57,19514200232689),
    (58,19779500847593)]

def pre12_2_47 : List PrefixEntry := pre12_2_47_data.map fun (l,v) => (2,l,v)

theorem pre12_2_47_good : prefixGood ⟨4,4,1⟩ pre12_2_47=true :=
  prefixGood_chain ⟨4,4,1⟩ 2 41 14935009922940 pre12_2_47_data (prefixFind_sound ⟨4,4,1⟩ pre12_2_20 pre12_2_20_good (by decide)) (by decide +kernel)

private def pre12_1_2_data : List (Nat × Nat) :=
  [(2,845091466312), (4,1677615186655)]

def pre12_1_2 : List PrefixEntry := pre12_1_2_data.map fun (l,v) => (1,l,v)

theorem pre12_1_2_good : prefixGood ⟨4,4,1⟩ pre12_1_2=true :=
  prefixGood_chain ⟨4,4,1⟩ 1 0 0 pre12_1_2_data rfl (by decide +kernel)

private def pre12_1_6_data : List (Nat × Nat) :=
  [(6,2497662147722), (8,3305326350057), (10,4100703454513), (12,4883890339045), (14,5654986468865)]

def pre12_1_6 : List PrefixEntry := pre12_1_6_data.map fun (l,v) => (1,l,v)

theorem pre12_1_6_good : prefixGood ⟨4,4,1⟩ pre12_1_6=true :=
  prefixGood_chain ⟨4,4,1⟩ 1 4 1677615186655 pre12_1_6_data (prefixFind_sound ⟨4,4,1⟩ pre12_1_2 pre12_1_2_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre12Part002

section Pack_Z6970H2307PackedPre13Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre13_2_56_data : List (Nat × Nat) :=
  [(56,19091379543220), (58,19614591519691)]

def pre13_2_56 : List PrefixEntry := pre13_2_56_data.map fun (l,v) => (2,l,v)

theorem pre13_2_56_good : prefixGood ⟨5,4,1⟩ pre13_2_56=true :=
  prefixGood_chain ⟨5,4,1⟩ 2 54 18558381034769 pre13_2_56_data (prefixFind_sound ⟨5,4,1⟩ pre13_2_26 pre13_2_26_good (by decide)) (by decide +kernel)

private def pre13_1_2_data : List (Nat × Nat) :=
  [(2,844753654450), (4,1676490930284), (6,2495306693986), (8,3301299119200), (10,4094568175262)]

def pre13_1_2 : List PrefixEntry := pre13_1_2_data.map fun (l,v) => (1,l,v)

theorem pre13_1_2_good : prefixGood ⟨5,4,1⟩ pre13_1_2=true :=
  prefixGood_chain ⟨5,4,1⟩ 1 0 0 pre13_1_2_data rfl (by decide +kernel)

private def pre13_1_12_data : List (Nat × Nat) :=
  [(12,4875217376741), (14,5643352135590), (16,6399080384721), (18,7142512688442), (20,7873761155339),
    (22,8592940614416)]

def pre13_1_12 : List PrefixEntry := pre13_1_12_data.map fun (l,v) => (1,l,v)

theorem pre13_1_12_good : prefixGood ⟨5,4,1⟩ pre13_1_12=true :=
  prefixGood_chain ⟨5,4,1⟩ 1 10 4094568175262 pre13_1_12_data (prefixFind_sound ⟨5,4,1⟩ pre13_1_2 pre13_1_2_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre13Part002

section Pack_Z6970H2307PackedPre14Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre14_1_19_data : List (Nat × Nat) :=
  [(19,7524028763399), (22,8611048453098), (25,9671411717225), (29,11044432955105), (34,12696516758097)]

def pre14_1_19 : List PrefixEntry := pre14_1_19_data.map fun (l,v) => (1,l,v)

theorem pre14_1_19_good : prefixGood ⟨10,3,1⟩ pre14_1_19=true :=
  prefixGood_chain ⟨10,3,1⟩ 1 16 6409991923358 pre14_1_19_data (prefixFind_sound ⟨10,3,1⟩ pre14_1_6 pre14_1_6_good (by decide)) (by decide +kernel)

private def pre14_1_42_data : List (Nat × Nat) :=
  [(42,15196245817574), (52,18083864059097), (55,18901063137494), (59,19956716635114)]

def pre14_1_42 : List PrefixEntry := pre14_1_42_data.map fun (l,v) => (1,l,v)

theorem pre14_1_42_good : prefixGood ⟨10,3,1⟩ pre14_1_42=true :=
  prefixGood_chain ⟨10,3,1⟩ 1 34 12696516758097 pre14_1_42_data (prefixFind_sound ⟨10,3,1⟩ pre14_1_19 pre14_1_19_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre14Part002

section Pack_Z6970H2307PackedPre17Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre17_2_28_data : List (Nat × Nat) :=
  [(28,10553867763125), (32,11850920471998), (36,13098660592245), (40,14298254766621), (44,15450876488868),
    (46,16009938886554)]

def pre17_2_28 : List PrefixEntry := pre17_2_28_data.map fun (l,v) => (2,l,v)

theorem pre17_2_28_good : prefixGood ⟨2,5,1⟩ pre17_2_28=true :=
  prefixGood_chain ⟨2,5,1⟩ 2 24 9206354462981 pre17_2_28_data (prefixFind_sound ⟨2,5,1⟩ pre17_2_8 pre17_2_8_good (by decide)) (by decide +kernel)

private def pre17_2_51_data : List (Nat × Nat) :=
  [(51,17358459376849), (54,18134607639341), (55,18387938731117), (57,18886632006348), (58,19132030304569),
    (59,19374820414139), (60,19615020326147), (61,19852648003800)]

def pre17_2_51 : List PrefixEntry := pre17_2_51_data.map fun (l,v) => (2,l,v)

theorem pre17_2_51_good : prefixGood ⟨2,5,1⟩ pre17_2_51=true :=
  prefixGood_chain ⟨2,5,1⟩ 2 46 16009938886554 pre17_2_51_data (prefixFind_sound ⟨2,5,1⟩ pre17_2_28 pre17_2_28_good (by decide)) (by decide +kernel)

private def pre17_1_2_data : List (Nat × Nat) :=
  [(2,843739718709), (4,1673136309218)]

def pre17_1_2 : List PrefixEntry := pre17_1_2_data.map fun (l,v) => (1,l,v)

theorem pre17_1_2_good : prefixGood ⟨2,5,1⟩ pre17_1_2=true :=
  prefixGood_chain ⟨2,5,1⟩ 1 0 0 pre17_1_2_data rfl (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre17Part002

section Pack_Z6970H2307PackedPre18Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre18_1_19_data : List (Nat × Nat) :=
  [(19,7284078236747), (22,8295550708432), (25,9271348518532), (29,10518387060603), (34,11993267731409),
    (67,19670419252182), (70,20213475265948)]

def pre18_1_19 : List PrefixEntry := pre18_1_19_data.map fun (l,v) => (1,l,v)

theorem pre18_1_19_good : prefixGood ⟨10,5,1⟩ pre18_1_19=true :=
  prefixGood_chain ⟨10,5,1⟩ 1 16 6236109728338 pre18_1_19_data (prefixFind_sound ⟨10,5,1⟩ pre18_1_6 pre18_1_6_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre18Part002

section Pack_Z6970H2307PackedPre20Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre20_2_24_data : List (Nat × Nat) :=
  [(24,9018420681442), (28,10303286635964), (32,11530002087465), (36,12700206391004), (40,13815541569657),
    (44,14877645125053)]

def pre20_2_24 : List PrefixEntry := pre20_2_24_data.map fun (l,v) => (2,l,v)

theorem pre20_2_24_good : prefixGood ⟨2,6,1⟩ pre20_2_24=true :=
  prefixGood_chain ⟨2,6,1⟩ 2 20 7673787202678 pre20_2_24_data (prefixFind_sound ⟨2,6,1⟩ pre20_2_4 pre20_2_4_good (by decide)) (by decide +kernel)

private def pre20_2_49_data : List (Nat × Nat) :=
  [(49,16132900570166), (54,17310693002542), (59,18414158429737), (60,18626205817965), (62,19041852229970),
    (64,19446397447494), (65,19644568065524), (67,20032826557879), (68,20222962685123), (69,20410468761413)]

def pre20_2_49 : List PrefixEntry := pre20_2_49_data.map fun (l,v) => (2,l,v)

theorem pre20_2_49_good : prefixGood ⟨2,6,1⟩ pre20_2_49=true :=
  prefixGood_chain ⟨2,6,1⟩ 2 44 14877645125053 pre20_2_49_data (prefixFind_sound ⟨2,6,1⟩ pre20_2_24 pre20_2_24_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre20Part002

section Pack_Z6970H2307PackedPre20Part005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre20_1_44_data : List (Nat × Nat) :=
  [(44,14877473320888), (46,15389071812005), (48,15887973380393), (50,16374380428606), (52,16848494658498),
    (54,17310517002964)]

def pre20_1_44 : List PrefixEntry := pre20_1_44_data.map fun (l,v) => (1,l,v)

theorem pre20_1_44_good : prefixGood ⟨2,6,1⟩ pre20_1_44=true :=
  prefixGood_chain ⟨2,6,1⟩ 1 42 14352974889546 pre20_1_44_data (prefixFind_sound ⟨2,6,1⟩ pre20_1_32 pre20_1_32_good (by decide)) (by decide +kernel)

private def pre20_1_56_data : List (Nat × Nat) :=
  [(56,17760647557745), (58,18199085479607), (59,18413981685710), (60,18626028987520), (62,19041675270663),
    (64,19446220405813), (66,19839859289399), (67,20032649452373), (68,20222785569045)]

def pre20_1_56 : List PrefixEntry := pre20_1_56_data.map fun (l,v) => (1,l,v)

theorem pre20_1_56_good : prefixGood ⟨2,6,1⟩ pre20_1_56=true :=
  prefixGood_chain ⟨2,6,1⟩ 1 54 17310517002964 pre20_1_56_data (prefixFind_sound ⟨2,6,1⟩ pre20_1_44 pre20_1_44_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre20Part005

section Pack_Z6970H2307PackedPre21Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre21_2_24_data : List (Nat × Nat) :=
  [(24,9018420681442), (28,10303286635964), (32,11530002087465), (36,12700206391004), (40,13815541569657),
    (44,14877645125053)]

def pre21_2_24 : List PrefixEntry := pre21_2_24_data.map fun (l,v) => (2,l,v)

theorem pre21_2_24_good : prefixGood ⟨2,6,2⟩ pre21_2_24=true :=
  prefixGood_chain ⟨2,6,2⟩ 2 20 7673787202678 pre21_2_24_data (prefixFind_sound ⟨2,6,2⟩ pre21_2_4 pre21_2_4_good (by decide)) (by decide +kernel)

private def pre21_2_49_data : List (Nat × Nat) :=
  [(49,16132900570166), (54,17310693002542), (59,18414158429737), (60,18626205817965), (62,19041852229970),
    (64,19446397447494), (65,19644568065524), (67,20032826557879), (68,20222962685123), (69,20410468761413)]

def pre21_2_49 : List PrefixEntry := pre21_2_49_data.map fun (l,v) => (2,l,v)

theorem pre21_2_49_good : prefixGood ⟨2,6,2⟩ pre21_2_49=true :=
  prefixGood_chain ⟨2,6,2⟩ 2 44 14877645125053 pre21_2_49_data (prefixFind_sound ⟨2,6,2⟩ pre21_2_24 pre21_2_24_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre21Part002

section Pack_Z6970H2307PackedPre21Part005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre21_1_44_data : List (Nat × Nat) :=
  [(44,14877473320888), (46,15389071812005), (48,15887973380393), (50,16374380428606), (52,16848494658498),
    (54,17310517002964)]

def pre21_1_44 : List PrefixEntry := pre21_1_44_data.map fun (l,v) => (1,l,v)

theorem pre21_1_44_good : prefixGood ⟨2,6,2⟩ pre21_1_44=true :=
  prefixGood_chain ⟨2,6,2⟩ 1 42 14352974889546 pre21_1_44_data (prefixFind_sound ⟨2,6,2⟩ pre21_1_32 pre21_1_32_good (by decide)) (by decide +kernel)

private def pre21_1_56_data : List (Nat × Nat) :=
  [(56,17760647557745), (58,18199085479607), (59,18413981685710), (60,18626028987520), (62,19041675270663),
    (64,19446220405813), (66,19839859289399), (67,20032649452373), (68,20222785569045)]

def pre21_1_56 : List PrefixEntry := pre21_1_56_data.map fun (l,v) => (1,l,v)

theorem pre21_1_56_good : prefixGood ⟨2,6,2⟩ pre21_1_56=true :=
  prefixGood_chain ⟨2,6,2⟩ 1 54 17310517002964 pre21_1_56_data (prefixFind_sound ⟨2,6,2⟩ pre21_1_44 pre21_1_44_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre21Part005

section Pack_Z6970H2307PackedPre23Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre23_1_16_data : List (Nat × Nat) :=
  [(16,6180199218508), (18,6869354450017), (20,7540873735872), (23,8515711067125), (26,9452494966405),
    (29,10352230196750)]

def pre23_1_16 : List PrefixEntry := pre23_1_16_data.map fun (l,v) => (1,l,v)

theorem pre23_1_16_good : prefixGood ⟨8,6,2⟩ pre23_1_16=true :=
  prefixGood_chain ⟨8,6,2⟩ 1 14 5473128483671 pre23_1_16_data (prefixFind_sound ⟨8,6,2⟩ pre23_1_4 pre23_1_4_good (by decide)) (by decide +kernel)

private def pre23_1_33_data : List (Nat × Nat) :=
  [(33,11496010854099), (37,12578175734706), (62,18092675057306), (72,19774002164018), (74,20079058604785),
    (76,20374270401985), (78,20659869774006)]

def pre23_1_33 : List PrefixEntry := pre23_1_33_data.map fun (l,v) => (1,l,v)

theorem pre23_1_33_good : prefixGood ⟨8,6,2⟩ pre23_1_33=true :=
  prefixGood_chain ⟨8,6,2⟩ 1 29 10352230196750 pre23_1_33_data (prefixFind_sound ⟨8,6,2⟩ pre23_1_16 pre23_1_16_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre23Part002

section Pack_Z6970H2307PackedPre24Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre24_1_20_data : List (Nat × Nat) :=
  [(20,7472749606093), (23,8427404429094), (27,9638012683348), (32,11055222132702), (76,19730751800870),
    (81,20369142502443), (83,20608679369780), (84,20725178926898)]

def pre24_1_20 : List PrefixEntry := pre24_1_20_data.map fun (l,v) => (1,l,v)

theorem pre24_1_20_good : prefixGood ⟨11,6,2⟩ pre24_1_20=true :=
  prefixGood_chain ⟨11,6,2⟩ 1 17 6476758301252 pre24_1_20_data (prefixFind_sound ⟨11,6,2⟩ pre24_1_6 pre24_1_6_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre24Part002

section Pack_Z6970H2307PackedPre29Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre29_2_37_data : List (Nat × Nat) :=
  [(37,12512094087956), (42,13762583862348), (47,14922265233203), (52,15995560007647), (58,17175603536856),
    (62,17900306357874), (64,18244861112546), (70,19210466778159), (71,19361811807588), (74,19800037265631),
    (75,19940945731099), (76,20079321994939), (78,20348599391199), (79,20479560807181), (80,20608110588563),
    (81,20734278423647)]

def pre29_2_37 : List PrefixEntry := pre29_2_37_data.map fun (l,v) => (2,l,v)

theorem pre29_2_37_good : prefixGood ⟨3,7,1⟩ pre29_2_37=true :=
  prefixGood_chain ⟨3,7,1⟩ 2 32 11166318845406 pre29_2_37_data (prefixFind_sound ⟨3,7,1⟩ pre29_2_12 pre29_2_12_good (by decide)) (by decide +kernel)

private def pre29_1_2_data : List (Nat × Nat) :=
  [(2,839360578593), (4,1658639840241), (6,2458084181219), (8,3237945211164), (10,3998479317308)]

def pre29_1_2 : List PrefixEntry := pre29_1_2_data.map fun (l,v) => (1,l,v)

theorem pre29_1_2_good : prefixGood ⟨3,7,1⟩ pre29_1_2=true :=
  prefixGood_chain ⟨3,7,1⟩ 1 0 0 pre29_1_2_data rfl (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre29Part002

section Pack_Z6970H2307PackedPre30Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre30_2_37_data : List (Nat × Nat) :=
  [(37,12512094087956), (42,13762583862348), (47,14922265233203), (52,15995560007647), (58,17175603536856),
    (62,17900306357874), (64,18244861112546), (70,19210466778159), (71,19361811807588), (74,19800037265631),
    (75,19940945731099), (76,20079321994939), (78,20348599391199), (79,20479560807181), (80,20608110588563),
    (81,20734278423647)]

def pre30_2_37 : List PrefixEntry := pre30_2_37_data.map fun (l,v) => (2,l,v)

theorem pre30_2_37_good : prefixGood ⟨3,7,2⟩ pre30_2_37=true :=
  prefixGood_chain ⟨3,7,2⟩ 2 32 11166318845406 pre30_2_37_data (prefixFind_sound ⟨3,7,2⟩ pre30_2_12 pre30_2_12_good (by decide)) (by decide +kernel)

private def pre30_1_2_data : List (Nat × Nat) :=
  [(2,839360578593), (4,1658639840241), (6,2458084181219), (8,3237945211164), (10,3998479317308)]

def pre30_1_2 : List PrefixEntry := pre30_1_2_data.map fun (l,v) => (1,l,v)

theorem pre30_1_2_good : prefixGood ⟨3,7,2⟩ pre30_1_2=true :=
  prefixGood_chain ⟨3,7,2⟩ 1 0 0 pre30_1_2_data rfl (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre30Part002

section Pack_Z6970H2307PackedPre31Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre31_1_6_data : List (Nat × Nat) :=
  [(6,2451138428221), (8,3226137093126), (10,3980598187655), (12,4714824587516), (14,5429126351588),
    (16,6123819991685)]

def pre31_1_6 : List PrefixEntry := pre31_1_6_data.map fun (l,v) => (1,l,v)

theorem pre31_1_6_good : prefixGood ⟨6,7,2⟩ pre31_1_6=true :=
  prefixGood_chain ⟨6,7,2⟩ 1 4 1655306382422 pre31_1_6_data (prefixFind_sound ⟨6,7,2⟩ pre31_1_2 pre31_1_2_good (by decide)) (by decide +kernel)

private def pre31_1_18_data : List (Nat × Nat) :=
  [(18,6799228058342), (20,7455678789326), (22,8093505382184), (24,8713045871067), (26,9314642244106),
    (29,10184147377511)]

def pre31_1_18 : List PrefixEntry := pre31_1_18_data.map fun (l,v) => (1,l,v)

theorem pre31_1_18_good : prefixGood ⟨6,7,2⟩ pre31_1_18=true :=
  prefixGood_chain ⟨6,7,2⟩ 1 16 6123819991685 pre31_1_18_data (prefixFind_sound ⟨6,7,2⟩ pre31_1_6 pre31_1_6_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre31Part002

section Pack_Z6970H2307PackedPre32Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre32_1_19_data : List (Nat × Nat) :=
  [(19,7069766924471), (22,8014914917115), (25,8916958289268), (28,9777261207859), (32,10861776805705)]

def pre32_1_19 : List PrefixEntry := pre32_1_19_data.map fun (l,v) => (1,l,v)

theorem pre32_1_19_good : prefixGood ⟨9,7,2⟩ pre32_1_19=true :=
  prefixGood_chain ⟨9,7,2⟩ 1 16 6080175174736 pre32_1_19_data (prefixFind_sound ⟨9,7,2⟩ pre32_1_6 pre32_1_6_good (by decide)) (by decide +kernel)

private def pre32_1_83_data : List (Nat × Nat) :=
  [(83,19693567040933), (88,20176809053053), (92,20527183878217), (94,20690981781878), (96,20847507490171),
    (97,20923116770732), (98,20996995606248)]

def pre32_1_83 : List PrefixEntry := pre32_1_83_data.map fun (l,v) => (1,l,v)

theorem pre32_1_83_good : prefixGood ⟨9,7,2⟩ pre32_1_83=true :=
  prefixGood_chain ⟨9,7,2⟩ 1 32 10861776805705 pre32_1_83_data (prefixFind_sound ⟨9,7,2⟩ pre32_1_19 pre32_1_19_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre32Part002

section Pack_Z6970H2307PackedPre33Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre33_1_23_data : List (Nat × Nat) :=
  [(23,8262853118828), (27,9418402400988), (32,10758573101551), (96,20341210407585), (102,20737689543886),
    (104,20857314353146), (105,20914902055054), (106,20971042755771), (107,21025763156649), (108,21079089639474)]

def pre33_1_23 : List PrefixEntry := pre33_1_23_data.map fun (l,v) => (1,l,v)

theorem pre33_1_23_good : prefixGood ⟨11,7,2⟩ pre33_1_23=true :=
  prefixGood_chain ⟨11,7,2⟩ 1 20 7345174593044 pre33_1_23_data (prefixFind_sound ⟨11,7,2⟩ pre33_1_8 pre33_1_8_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre33Part002

section Pack_Z6970H2307PackedPre34Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre34_1_106_data : List (Nat × Nat) :=
  [(106,20691821806205), (108,20795064960134), (110,20892964692404), (111,20939975374122), (112,20985727064097),
    (113,21030244705232)]

def pre34_1_106 : List PrefixEntry := pre34_1_106_data.map fun (l,v) => (1,l,v)

theorem pre34_1_106_good : prefixGood ⟨12,7,2⟩ pre34_1_106=true :=
  prefixGood_chain ⟨12,7,2⟩ 1 50 14617717295903 pre34_1_106_data (prefixFind_sound ⟨12,7,2⟩ pre34_1_12 pre34_1_12_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre34Part002

section Pack_Z6970H2307PackedPre36Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre36_1_4_data : List (Nat × Nat) :=
  [(4,1646308061466), (6,2432310766572), (8,3194018460247), (10,3931824029614), (13,4994641212818),
    (16,6006142908816)]

def pre36_1_4 : List PrefixEntry := pre36_1_4_data.map fun (l,v) => (1,l,v)

theorem pre36_1_4_good : prefixGood ⟨14,7,2⟩ pre36_1_4=true :=
  prefixGood_chain ⟨14,7,2⟩ 1 2 835647563432 pre36_1_4_data (prefixFind_sound ⟨14,7,2⟩ pre36_1_2 pre36_1_2_good (by decide)) (by decide +kernel)

private def pre36_1_20_data : List (Nat × Nat) :=
  [(20,7277778198189), (25,8749161135467), (134,21051441798491), (136,21090838649768), (137,21109531350135),
    (138,21127576450159), (139,21144990748795), (140,21161790754342), (141,21177992688652), (142,21193612489707)]

def pre36_1_20 : List PrefixEntry := pre36_1_20_data.map fun (l,v) => (1,l,v)

theorem pre36_1_20_good : prefixGood ⟨14,7,2⟩ pre36_1_20=true :=
  prefixGood_chain ⟨14,7,2⟩ 1 16 6006142908816 pre36_1_20_data (prefixFind_sound ⟨14,7,2⟩ pre36_1_4 pre36_1_4_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre36Part001

section Pack_Z6970H2307PackedPre37Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre37_4_34_data : List (Nat × Nat) :=
  [(34,11376320076039), (44,13704077430088), (83,19532414146379), (89,20069293092742), (90,20151409116502),
    (91,20231510642758), (92,20309630622021), (93,20385801743229), (94,20460056433519), (95,20532426854565),
    (96,20602944905785), (97,20671642224113), (98,20738550180338), (99,20803699882310), (100,20867122174712),
    (101,20928847635400), (102,20988906578608)]

def pre37_4_34 : List PrefixEntry := pre37_4_34_data.map fun (l,v) => (4,l,v)

theorem pre37_4_34_good : prefixGood ⟨3,8,1⟩ pre37_4_34=true :=
  prefixGood_chain ⟨3,8,1⟩ 4 25 8918231783662 pre37_4_34_data (prefixFind_sound ⟨3,8,1⟩ pre37_4_8 pre37_4_8_good (by decide)) (by decide +kernel)

private def pre37_2_4_data : List (Nat × Nat) :=
  [(4,1652005713938), (8,3214425337668)]

def pre37_2_4 : List PrefixEntry := pre37_2_4_data.map fun (l,v) => (2,l,v)

theorem pre37_2_4_good : prefixGood ⟨3,8,1⟩ pre37_2_4=true :=
  prefixGood_chain ⟨3,8,1⟩ 2 0 0 pre37_2_4_data rfl (by decide +kernel)

private def pre37_2_12_data : List (Nat × Nat) :=
  [(12,4689880406978), (16,6081090846339), (20,7390869242090), (24,8622113003860), (28,9777781595678),
    (32,10860843390033)]

def pre37_2_12 : List PrefixEntry := pre37_2_12_data.map fun (l,v) => (2,l,v)

theorem pre37_2_12_good : prefixGood ⟨3,8,1⟩ pre37_2_12=true :=
  prefixGood_chain ⟨3,8,1⟩ 2 8 3214425337668 pre37_2_12_data (prefixFind_sound ⟨3,8,1⟩ pre37_2_4 pre37_2_4_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre37Part001

section Pack_Z6970H2307PackedPre38Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre38_4_34_data : List (Nat × Nat) :=
  [(34,11376320076039), (44,13704077430088), (83,19532414146379), (89,20069293092742), (90,20151409116502),
    (91,20231510642758), (92,20309630622021), (93,20385801743229), (94,20460056433519), (95,20532426854565),
    (96,20602944905785), (97,20671642224113), (98,20738550180338), (99,20803699882310), (100,20867122174712),
    (101,20928847635400), (102,20988906578608)]

def pre38_4_34 : List PrefixEntry := pre38_4_34_data.map fun (l,v) => (4,l,v)

theorem pre38_4_34_good : prefixGood ⟨3,8,2⟩ pre38_4_34=true :=
  prefixGood_chain ⟨3,8,2⟩ 4 25 8918231783662 pre38_4_34_data (prefixFind_sound ⟨3,8,2⟩ pre38_4_8 pre38_4_8_good (by decide)) (by decide +kernel)

private def pre38_2_4_data : List (Nat × Nat) :=
  [(4,1652005713938), (8,3214425337668)]

def pre38_2_4 : List PrefixEntry := pre38_2_4_data.map fun (l,v) => (2,l,v)

theorem pre38_2_4_good : prefixGood ⟨3,8,2⟩ pre38_2_4=true :=
  prefixGood_chain ⟨3,8,2⟩ 2 0 0 pre38_2_4_data rfl (by decide +kernel)

private def pre38_2_12_data : List (Nat × Nat) :=
  [(12,4689880406978), (16,6081090846339), (20,7390869242090), (24,8622113003860), (28,9777781595678),
    (32,10860843390033)]

def pre38_2_12 : List PrefixEntry := pre38_2_12_data.map fun (l,v) => (2,l,v)

theorem pre38_2_12_good : prefixGood ⟨3,8,2⟩ pre38_2_12=true :=
  prefixGood_chain ⟨3,8,2⟩ 2 8 3214425337668 pre38_2_12_data (prefixFind_sound ⟨3,8,2⟩ pre38_2_4 pre38_2_4_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre38Part001

section Pack_Z6970H2307PackedPre39Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre39_4_36_data : List (Nat × Nat) :=
  [(36,11815746084726), (48,14433193543730), (91,20023251643381), (95,20315690207089), (96,20384168785541),
    (97,20450858996165), (98,20515792367540), (99,20579000144714), (100,20640513289316), (101,20700362476337),
    (102,20758578097577), (103,20815190261757), (104,20870228791304), (105,20923723225794), (106,20975702822064)]

def pre39_4_36 : List PrefixEntry := pre39_4_36_data.map fun (l,v) => (4,l,v)

theorem pre39_4_36_good : prefixGood ⟨4,8,2⟩ pre39_4_36=true :=
  prefixGood_chain ⟨4,8,2⟩ 4 26 9175808144187 pre39_4_36_data (prefixFind_sound ⟨4,8,2⟩ pre39_4_8 pre39_4_8_good (by decide)) (by decide +kernel)

private def pre39_2_4_data : List (Nat × Nat) :=
  [(4,1650900938476), (8,3210533252930), (12,4681644524996)]

def pre39_2_4 : List PrefixEntry := pre39_2_4_data.map fun (l,v) => (2,l,v)

theorem pre39_2_4_good : prefixGood ⟨4,8,2⟩ pre39_2_4=true :=
  prefixGood_chain ⟨4,8,2⟩ 2 0 0 pre39_2_4_data rfl (by decide +kernel)

private def pre39_2_16_data : List (Nat × Nat) :=
  [(16,6067093101114), (20,7369839479848), (24,8592935951004), (29,10014548431525), (34,11322679225324)]

def pre39_2_16 : List PrefixEntry := pre39_2_16_data.map fun (l,v) => (2,l,v)

theorem pre39_2_16_good : prefixGood ⟨4,8,2⟩ pre39_2_16=true :=
  prefixGood_chain ⟨4,8,2⟩ 2 12 4681644524996 pre39_2_16_data (prefixFind_sound ⟨4,8,2⟩ pre39_2_4 pre39_2_4_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre39Part001

section Pack_Z6970H2307PackedPre40Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre40_2_12_data : List (Nat × Nat) :=
  [(12,4656690024254), (17,6352931454417), (22,7915278699094), (28,9623207201961), (35,11401172178315)]

def pre40_2_12 : List PrefixEntry := pre40_2_12_data.map fun (l,v) => (2,l,v)

theorem pre40_2_12_good : prefixGood ⟨7,8,1⟩ pre40_2_12=true :=
  prefixGood_chain ⟨7,8,1⟩ 2 8 3198767788393 pre40_2_12_data (prefixFind_sound ⟨7,8,1⟩ pre40_2_4 pre40_2_4_good (by decide)) (by decide +kernel)

private def pre40_2_122_data : List (Nat × Nat) :=
  [(122,20840841403253), (125,20918835559935), (126,20943003917463), (127,20966295059895), (130,21031124713852),
    (131,21051124958682), (132,21070355417878), (133,21088836651022), (134,21106588909267), (135,21123632139367),
    (136,21139985984809), (137,21155669784073), (138,21170702574649), (140,21198889778680)]

def pre40_2_122 : List PrefixEntry := pre40_2_122_data.map fun (l,v) => (2,l,v)

theorem pre40_2_122_good : prefixGood ⟨7,8,1⟩ pre40_2_122=true :=
  prefixGood_chain ⟨7,8,1⟩ 2 35 11401172178315 pre40_2_122_data (prefixFind_sound ⟨7,8,1⟩ pre40_2_12 pre40_2_12_good (by decide)) (by decide +kernel)

private def pre40_1_2_data : List (Nat × Nat) :=
  [(2,836002045315), (4,1647539821028), (6,2434983099623), (8,3198713292521), (10,3939124199253)]

def pre40_1_2 : List PrefixEntry := pre40_1_2_data.map fun (l,v) => (1,l,v)

theorem pre40_1_2_good : prefixGood ⟨7,8,1⟩ pre40_1_2=true :=
  prefixGood_chain ⟨7,8,1⟩ 1 0 0 pre40_1_2_data rfl (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre40Part001

section Pack_Z6970H2307PackedPre41Part000

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre41_64_121_data : List (Nat × Nat) :=
  [(121,20817874755187), (124,20898705503122), (128,20993669032753)]

def pre41_64_121 : List PrefixEntry := pre41_64_121_data.map fun (l,v) => (64,l,v)

theorem pre41_64_121_good : prefixGood ⟨7,8,2⟩ pre41_64_121=true :=
  prefixGood_chain ⟨7,8,2⟩ 64 0 0 pre41_64_121_data rfl (by decide +kernel)

private def pre41_32_131_data : List (Nat × Nat) :=
  [(131,21053688710094), (134,21109152660679), (135,21126195890779)]

def pre41_32_131 : List PrefixEntry := pre41_32_131_data.map fun (l,v) => (32,l,v)

theorem pre41_32_131_good : prefixGood ⟨7,8,2⟩ pre41_32_131=true :=
  prefixGood_chain ⟨7,8,2⟩ 32 0 0 pre41_32_131_data rfl (by decide +kernel)

private def pre41_16_80_data : List (Nat × Nat) :=
  [(80,18503181859374), (117,20692392626272), (119,20755366803916), (120,20785280353936), (121,20814177420008),
    (123,20869017799253), (124,20895008167943), (126,20944244520587), (130,21032365316976), (132,21071596021002)]

def pre41_16_80 : List PrefixEntry := pre41_16_80_data.map fun (l,v) => (16,l,v)

theorem pre41_16_80_good : prefixGood ⟨7,8,2⟩ pre41_16_80=true :=
  prefixGood_chain ⟨7,8,2⟩ 16 0 0 pre41_16_80_data rfl (by decide +kernel)

private def pre41_8_18_data : List (Nat × Nat) :=
  [(18,6676385595498), (118,20723713238501), (122,20841382801292), (124,20894308962858), (126,20943545315502),
    (128,20989272492489), (129,21010875215169), (130,21031666111891), (131,21051666356721), (132,21070896815917),
    (136,21140527382848), (138,21171243972688), (139,21185644492208)]

def pre41_8_18 : List PrefixEntry := pre41_8_18_data.map fun (l,v) => (8,l,v)

theorem pre41_8_18_good : prefixGood ⟨7,8,2⟩ pre41_8_18=true :=
  prefixGood_chain ⟨7,8,2⟩ 8 0 0 pre41_8_18_data rfl (by decide +kernel)

private def pre41_4_8_data : List (Nat × Nat) :=
  [(8,3198876538556)]

def pre41_4_8 : List PrefixEntry := pre41_4_8_data.map fun (l,v) => (4,l,v)

theorem pre41_4_8_good : prefixGood ⟨7,8,2⟩ pre41_4_8=true :=
  prefixGood_chain ⟨7,8,2⟩ 4 0 0 pre41_4_8_data rfl (by decide +kernel)

private def pre41_4_17_data : List (Nat × Nat) :=
  [(17,6353094658099), (28,9623388361275), (123,20867959705795), (125,20919018069601), (127,20966477569561),
    (128,20988913604116), (129,21010516326796), (130,21031307223518), (131,21051307468348), (132,21070537927544),
    (133,21089019160688), (134,21106771418933), (135,21123814649033)]

def pre41_4_17 : List PrefixEntry := pre41_4_17_data.map fun (l,v) => (4,l,v)

theorem pre41_4_17_good : prefixGood ⟨7,8,2⟩ pre41_4_17=true :=
  prefixGood_chain ⟨7,8,2⟩ 4 8 3198876538556 pre41_4_17_data (prefixFind_sound ⟨7,8,2⟩ pre41_4_8 pre41_4_8_good (by decide)) (by decide +kernel)

private def pre41_2_4_data : List (Nat × Nat) :=
  [(4,1647571551270), (8,3198767788393)]

def pre41_2_4 : List PrefixEntry := pre41_2_4_data.map fun (l,v) => (2,l,v)

theorem pre41_2_4_good : prefixGood ⟨7,8,2⟩ pre41_2_4=true :=
  prefixGood_chain ⟨7,8,2⟩ 2 0 0 pre41_2_4_data rfl (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre41Part000
