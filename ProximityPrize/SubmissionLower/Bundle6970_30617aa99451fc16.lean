import ProximityPrize.SubmissionLower.Z6970H2307OrderPackedTools
import ProximityPrize.SubmissionLower.Bundle6970_c8568d4b10f524f8

section Pack_Z6970H2307PackedPre01Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre1_1_12_data : List (Nat × Nat) :=
  [(12,4961350103647), (14,5758811760686), (16,6547982700430), (18,7328907963439), (20,8101632913105)]

def pre1_1_12 : List PrefixEntry := pre1_1_12_data.map fun (l,v) => (1,l,v)

theorem pre1_1_12_good : prefixGood ⟨1,3,1⟩ pre1_1_12=true :=
  prefixGood_chain ⟨1,3,1⟩ 1 10 4155553095325 pre1_1_12_data (prefixFind_sound ⟨1,3,1⟩ pre1_1_2 pre1_1_2_good (by decide)) (by decide +kernel)

private def pre1_1_22_data : List (Nat × Nat) :=
  [(22,8866203232852), (24,9622664923336), (26,10371064299645), (28,11111447988499), (30,11843862925400)]

def pre1_1_22 : List PrefixEntry := pre1_1_22_data.map fun (l,v) => (1,l,v)

theorem pre1_1_22_good : prefixGood ⟨1,3,1⟩ pre1_1_22=true :=
  prefixGood_chain ⟨1,3,1⟩ 1 20 8101632913105 pre1_1_22_data (prefixFind_sound ⟨1,3,1⟩ pre1_1_12 pre1_1_12_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre01Part003

section Pack_Z6970H2307PackedPre02Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre2_1_12_data : List (Nat × Nat) :=
  [(12,4952735152130), (14,5747257687086), (16,6533074501083), (18,7310236366906), (20,8078794257164)]

def pre2_1_12 : List PrefixEntry := pre2_1_12_data.map fun (l,v) => (1,l,v)

theorem pre2_1_12_good : prefixGood ⟨2,3,1⟩ pre2_1_12=true :=
  prefixGood_chain ⟨2,3,1⟩ 1 10 4149456597186 pre2_1_12_data (prefixFind_sound ⟨2,3,1⟩ pre2_1_2 pre2_1_2_good (by decide)) (by decide +kernel)

private def pre2_1_22_data : List (Nat × Nat) :=
  [(22,8838799623302), (24,9590304639253), (26,10333361917106), (28,11068024498402), (30,11794345845380)]

def pre2_1_22 : List PrefixEntry := pre2_1_22_data.map fun (l,v) => (1,l,v)

theorem pre2_1_22_good : prefixGood ⟨2,3,1⟩ pre2_1_22=true :=
  prefixGood_chain ⟨2,3,1⟩ 1 20 8078794257164 pre2_1_22_data (prefixFind_sound ⟨2,3,1⟩ pre2_1_12 pre2_1_12_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre02Part003

section Pack_Z6970H2307PackedPre03Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre3_1_16_data : List (Nat × Nat) :=
  [(16,6518048732396), (18,7291402839343), (20,8055740901671), (22,8811120087296), (24,9557598154604),
    (26,10295233941743)]

def pre3_1_16 : List PrefixEntry := pre3_1_16_data.map fun (l,v) => (1,l,v)

theorem pre3_1_16_good : prefixGood ⟨3,3,1⟩ pre3_1_16=true :=
  prefixGood_chain ⟨3,3,1⟩ 1 14 5735621815598 pre3_1_16_data (prefixFind_sound ⟨3,3,1⟩ pre3_1_6 pre3_1_6_good (by decide)) (by decide +kernel)

private def pre3_1_28_data : List (Nat × Nat) :=
  [(28,11024086920605), (30,11744217037368), (32,12455684575605), (34,13158550834535), (36,13852877664717),
    (38,14538727374186)]

def pre3_1_28 : List PrefixEntry := pre3_1_28_data.map fun (l,v) => (1,l,v)

theorem pre3_1_28_good : prefixGood ⟨3,3,1⟩ pre3_1_28=true :=
  prefixGood_chain ⟨3,3,1⟩ 1 26 10295233941743 pre3_1_28_data (prefixFind_sound ⟨3,3,1⟩ pre3_1_16 pre3_1_16_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre03Part003

section Pack_Z6970H2307PackedPre04Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre4_1_22_data : List (Nat × Nat) :=
  [(22,8783182393660), (24,9524570012825), (26,10256713373499), (28,10979678600231), (30,11693532215089),
    (32,12398341974094)]

def pre4_1_22 : List PrefixEntry := pre4_1_22_data.map fun (l,v) => (1,l,v)

theorem pre4_1_22_good : prefixGood ⟨4,3,1⟩ pre4_1_22=true :=
  prefixGood_chain ⟨4,3,1⟩ 1 20 8032485478734 pre4_1_22_data (prefixFind_sound ⟨4,3,1⟩ pre4_1_10 pre4_1_10_good (by decide)) (by decide +kernel)

private def pre4_1_34_data : List (Nat × Nat) :=
  [(34,13094176619882), (36,13781105341420), (37,14121251845873), (39,14794953411431), (42,15789161007216),
    (45,16763970950310), (47,17403189332734)]

def pre4_1_34 : List PrefixEntry := pre4_1_34_data.map fun (l,v) => (1,l,v)

theorem pre4_1_34_good : prefixGood ⟨4,3,1⟩ pre4_1_34=true :=
  prefixGood_chain ⟨4,3,1⟩ 1 32 12398341974094 pre4_1_34_data (prefixFind_sound ⟨4,3,1⟩ pre4_1_22 pre4_1_22_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre04Part003

section Pack_Z6970H2307PackedPre07Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre7_1_34_data : List (Nat × Nat) :=
  [(34,12897380140546), (38,14216039468359), (39,14539536362215), (43,15809228779217), (48,17342638139366),
    (50,17939624756660), (51,18234660733035), (52,18527409227418), (54,19106096021593), (56,19675789648771)]

def pre7_1_34 : List PrefixEntry := pre7_1_34_data.map fun (l,v) => (1,l,v)

theorem pre7_1_34_good : prefixGood ⟨7,3,1⟩ pre7_1_34=true :=
  prefixGood_chain ⟨7,3,1⟩ 1 31 11882135820221 pre7_1_34_data (prefixFind_sound ⟨7,3,1⟩ pre7_1_18 pre7_1_18_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre07Part003

section Pack_Z6970H2307PackedPre08Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre8_1_46_data : List (Nat × Nat) :=
  [(46,16618736456111), (53,18665313779844), (57,19783244510568)]

def pre8_1_46 : List PrefixEntry := pre8_1_46_data.map fun (l,v) => (1,l,v)

theorem pre8_1_46_good : prefixGood ⟨8,3,1⟩ pre8_1_46=true :=
  prefixGood_chain ⟨8,3,1⟩ 1 40 14770005657747 pre8_1_46_data (prefixFind_sound ⟨8,3,1⟩ pre8_1_23 pre8_1_23_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre08Part003

section Pack_Z6970H2307PackedPre10Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre10_1_8_data : List (Nat × Nat) :=
  [(8,3313330579569), (10,4112881899440), (12,4901087652655), (14,5678033080950), (16,6443804329101)]

def pre10_1_8 : List PrefixEntry := pre10_1_8_data.map fun (l,v) => (1,l,v)

theorem pre10_1_8_good : prefixGood ⟨2,4,1⟩ pre10_1_8=true :=
  prefixGood_chain ⟨2,4,1⟩ 1 6 2502349370986 pre10_1_8_data (prefixFind_sound ⟨2,4,1⟩ pre10_1_2 pre10_1_2_good (by decide)) (by decide +kernel)

private def pre10_1_18_data : List (Nat × Nat) :=
  [(18,7198488428284), (20,7942173034158), (22,8674946682465), (24,9396899001348), (26,10108120433943)]

def pre10_1_18 : List PrefixEntry := pre10_1_18_data.map fun (l,v) => (1,l,v)

theorem pre10_1_18_good : prefixGood ⟨2,4,1⟩ pre10_1_18=true :=
  prefixGood_chain ⟨2,4,1⟩ 1 16 6443804329101 pre10_1_18_data (prefixFind_sound ⟨2,4,1⟩ pre10_1_8 pre10_1_8_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre10Part003

section Pack_Z6970H2307PackedPre11Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre11_1_12_data : List (Nat × Nat) :=
  [(12,4892514358570), (14,5666548039685), (16,6429002596207), (18,7179973083855), (20,7919555710440)]

def pre11_1_12 : List PrefixEntry := pre11_1_12_data.map fun (l,v) => (1,l,v)

theorem pre11_1_12_good : prefixGood ⟨3,4,1⟩ pre11_1_12=true :=
  prefixGood_chain ⟨3,4,1⟩ 1 10 4106808037874 pre11_1_12_data (prefixFind_sound ⟨3,4,1⟩ pre11_1_2 pre11_1_2_good (by decide)) (by decide +kernel)

private def pre11_1_22_data : List (Nat × Nat) :=
  [(22,8647847536337), (24,9364946636677), (26,10070952523767), (28,10765965714821), (30,11450087572524),
    (32,12123420171895)]

def pre11_1_22 : List PrefixEntry := pre11_1_22_data.map fun (l,v) => (1,l,v)

theorem pre11_1_22_good : prefixGood ⟨3,4,1⟩ pre11_1_22=true :=
  prefixGood_chain ⟨3,4,1⟩ 1 20 7919555710440 pre11_1_22_data (prefixFind_sound ⟨3,4,1⟩ pre11_1_12 pre11_1_12_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre11Part003

section Pack_Z6970H2307PackedPre12Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre12_1_16_data : List (Nat × Nat) :=
  [(16,6414092950987), (18,7161311967760), (20,7896747901513), (22,8620506705921), (24,9332695280170),
    (26,10033422368159)]

def pre12_1_16 : List PrefixEntry := pre12_1_16_data.map fun (l,v) => (1,l,v)

theorem pre12_1_16_good : prefixGood ⟨4,4,1⟩ pre12_1_16=true :=
  prefixGood_chain ⟨4,4,1⟩ 1 14 5654986468865 pre12_1_16_data (prefixFind_sound ⟨4,4,1⟩ pre12_1_6 pre12_1_6_good (by decide)) (by decide +kernel)

private def pre12_1_28_data : List (Nat × Nat) :=
  [(28,10722798162439), (30,11400933669964), (32,12067941410965), (34,12723935162051), (36,13369029472124),
    (38,14003340015489), (40,14626983544306)]

def pre12_1_28 : List PrefixEntry := pre12_1_28_data.map fun (l,v) => (1,l,v)

theorem pre12_1_28_good : prefixGood ⟨4,4,1⟩ pre12_1_28=true :=
  prefixGood_chain ⟨4,4,1⟩ 1 26 10033422368159 pre12_1_28_data (prefixFind_sound ⟨4,4,1⟩ pre12_1_16 pre12_1_16_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre12Part003

section Pack_Z6970H2307PackedPre13Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre13_1_24_data : List (Nat × Nat) :=
  [(24,9300167455421), (26,9995560012246), (28,10679238592134), (30,11351324732822), (32,12011941907291),
    (35,12981636373449)]

def pre13_1_24 : List PrefixEntry := pre13_1_24_data.map fun (l,v) => (1,l,v)

theorem pre13_1_24_good : prefixGood ⟨5,4,1⟩ pre13_1_24=true :=
  prefixGood_chain ⟨5,4,1⟩ 1 22 8592940614416 pre13_1_24_data (prefixFind_sound ⟨5,4,1⟩ pre13_1_12 pre13_1_12_good (by decide)) (by decide +kernel)

private def pre13_1_38_data : List (Nat × Nat) :=
  [(38,13926232809657), (41,14846163235339), (44,15741864834113), (47,16613778667919), (50,17462347999136),
    (51,17740093373806)]

def pre13_1_38 : List PrefixEntry := pre13_1_38_data.map fun (l,v) => (1,l,v)

theorem pre13_1_38_good : prefixGood ⟨5,4,1⟩ pre13_1_38=true :=
  prefixGood_chain ⟨5,4,1⟩ 1 35 12981636373449 pre13_1_38_data (prefixFind_sound ⟨5,4,1⟩ pre13_1_24 pre13_1_24_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre13Part003

section Pack_Z6970H2307PackedPre17Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre17_1_6_data : List (Nat × Nat) :=
  [(6,2488313391266), (8,3289395779836), (10,4076510289414), (12,4849785510843), (14,5609351616154)]

def pre17_1_6 : List PrefixEntry := pre17_1_6_data.map fun (l,v) => (1,l,v)

theorem pre17_1_6_good : prefixGood ⟨2,5,1⟩ pre17_1_6=true :=
  prefixGood_chain ⟨2,5,1⟩ 1 4 1673136309218 pre17_1_6_data (prefixFind_sound ⟨2,5,1⟩ pre17_1_2 pre17_1_2_good (by decide)) (by decide +kernel)

private def pre17_1_16_data : List (Nat × Nat) :=
  [(16,6355340330150), (18,7087884901944), (20,7807119848484), (22,8513181175668), (24,9206206548047)]

def pre17_1_16 : List PrefixEntry := pre17_1_16_data.map fun (l,v) => (1,l,v)

theorem pre17_1_16_good : prefixGood ⟨2,5,1⟩ pre17_1_16=true :=
  prefixGood_chain ⟨2,5,1⟩ 1 14 5609351616154 pre17_1_16_data (prefixFind_sound ⟨2,5,1⟩ pre17_1_6 pre17_1_6_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre17Part003

section Pack_Z6970H2307PackedPre29Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre29_1_12_data : List (Nat × Nat) :=
  [(12,4739947288851), (14,5462613795342), (16,6166747833606), (18,6852622693286), (20,7520515487548)]

def pre29_1_12 : List PrefixEntry := pre29_1_12_data.map fun (l,v) => (1,l,v)

theorem pre29_1_12_good : prefixGood ⟨3,7,1⟩ pre29_1_12=true :=
  prefixGood_chain ⟨3,7,1⟩ 1 10 3998479317308 pre29_1_12_data (prefixFind_sound ⟨3,7,1⟩ pre29_1_2 pre29_1_2_good (by decide)) (by decide +kernel)

private def pre29_1_22_data : List (Nat × Nat) :=
  [(22,8170706799105), (24,8803480689050), (26,9419124864716), (28,10017929713976), (30,10600186145236),
    (32,11166184668202)]

def pre29_1_22 : List PrefixEntry := pre29_1_22_data.map fun (l,v) => (1,l,v)

theorem pre29_1_22_good : prefixGood ⟨3,7,1⟩ pre29_1_22=true :=
  prefixGood_chain ⟨3,7,1⟩ 1 20 7520515487548 pre29_1_22_data (prefixFind_sound ⟨3,7,1⟩ pre29_1_12 pre29_1_12_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre29Part003

section Pack_Z6970H2307PackedPre30Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre30_1_12_data : List (Nat × Nat) :=
  [(12,4739947288851), (14,5462613795342), (16,6166747833606), (18,6852622693286), (20,7520515487548)]

def pre30_1_12 : List PrefixEntry := pre30_1_12_data.map fun (l,v) => (1,l,v)

theorem pre30_1_12_good : prefixGood ⟨3,7,2⟩ pre30_1_12=true :=
  prefixGood_chain ⟨3,7,2⟩ 1 10 3998479317308 pre30_1_12_data (prefixFind_sound ⟨3,7,2⟩ pre30_1_2 pre30_1_2_good (by decide)) (by decide +kernel)

private def pre30_1_22_data : List (Nat × Nat) :=
  [(22,8170706799105), (24,8803480689050), (26,9419124864716), (28,10017929713976), (30,10600186145236),
    (32,11166184668202)]

def pre30_1_22 : List PrefixEntry := pre30_1_22_data.map fun (l,v) => (1,l,v)

theorem pre30_1_22_good : prefixGood ⟨3,7,2⟩ pre30_1_22=true :=
  prefixGood_chain ⟨3,7,2⟩ 1 20 7520515487548 pre30_1_22_data (prefixFind_sound ⟨3,7,2⟩ pre30_1_12 pre30_1_12_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre30Part003

section Pack_Z6970H2307PackedPre31Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre31_1_32_data : List (Nat × Nat) :=
  [(32,11015223298794), (35,11809035290294), (38,12566742551451), (41,13289494718927), (45,14200751951644),
    (83,20338058429599), (87,20765079144588)]

def pre31_1_32 : List PrefixEntry := pre31_1_32_data.map fun (l,v) => (1,l,v)

theorem pre31_1_32_good : prefixGood ⟨6,7,2⟩ pre31_1_32=true :=
  prefixGood_chain ⟨6,7,2⟩ 1 29 10184147377511 pre31_1_32_data (prefixFind_sound ⟨6,7,2⟩ pre31_1_18 pre31_1_18_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre31Part003

section Pack_Z6970H2307PackedPre37Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre37_2_37_data : List (Nat × Nat) :=
  [(37,12117066937921), (42,13270180570945), (47,14325831798888), (52,15289569017138), (68,17818116115920),
    (91,20231256209533), (94,20459802000294), (98,20738295747113), (99,20803445449085), (100,20866867741487),
    (101,20928593202175), (102,20988652145383), (103,21047074621495)]

def pre37_2_37 : List PrefixEntry := pre37_2_37_data.map fun (l,v) => (2,l,v)

theorem pre37_2_37_good : prefixGood ⟨3,8,1⟩ pre37_2_37=true :=
  prefixGood_chain ⟨3,8,1⟩ 2 32 10860843390033 pre37_2_37_data (prefixFind_sound ⟨3,8,1⟩ pre37_2_12 pre37_2_12_good (by decide)) (by decide +kernel)

private def pre37_1_2_data : List (Nat × Nat) :=
  [(2,837342972874)]

def pre37_1_2 : List PrefixEntry := pre37_1_2_data.map fun (l,v) => (1,l,v)

theorem pre37_1_2_good : prefixGood ⟨3,8,1⟩ pre37_1_2=true :=
  prefixGood_chain ⟨3,8,1⟩ 1 0 0 pre37_1_2_data rfl (by decide +kernel)

private def pre37_1_4_data : List (Nat × Nat) :=
  [(4,1651972167976), (6,2444204871282), (8,3214365437948), (10,3962784805189), (12,4689800071536)]

def pre37_1_4 : List PrefixEntry := pre37_1_4_data.map fun (l,v) => (1,l,v)

theorem pre37_1_4_good : prefixGood ⟨3,8,1⟩ pre37_1_4=true :=
  prefixGood_chain ⟨3,8,1⟩ 1 2 837342972874 pre37_1_4_data (prefixFind_sound ⟨3,8,1⟩ pre37_1_2 pre37_1_2_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre37Part002

section Pack_Z6970H2307PackedPre38Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre38_2_37_data : List (Nat × Nat) :=
  [(37,12117066937921), (42,13270180570945), (47,14325831798888), (52,15289569017138), (68,17818116115920),
    (91,20231256209533), (94,20459802000294), (98,20738295747113), (99,20803445449085), (100,20866867741487),
    (101,20928593202175), (102,20988652145383), (103,21047074621495)]

def pre38_2_37 : List PrefixEntry := pre38_2_37_data.map fun (l,v) => (2,l,v)

theorem pre38_2_37_good : prefixGood ⟨3,8,2⟩ pre38_2_37=true :=
  prefixGood_chain ⟨3,8,2⟩ 2 32 10860843390033 pre38_2_37_data (prefixFind_sound ⟨3,8,2⟩ pre38_2_12 pre38_2_12_good (by decide)) (by decide +kernel)

private def pre38_1_2_data : List (Nat × Nat) :=
  [(2,837342972874)]

def pre38_1_2 : List PrefixEntry := pre38_1_2_data.map fun (l,v) => (1,l,v)

theorem pre38_1_2_good : prefixGood ⟨3,8,2⟩ pre38_1_2=true :=
  prefixGood_chain ⟨3,8,2⟩ 1 0 0 pre38_1_2_data rfl (by decide +kernel)

private def pre38_1_4_data : List (Nat × Nat) :=
  [(4,1651972167976), (6,2444204871282), (8,3214365437948), (10,3962784805189), (12,4689800071536)]

def pre38_1_4 : List PrefixEntry := pre38_1_4_data.map fun (l,v) => (1,l,v)

theorem pre38_1_4_good : prefixGood ⟨3,8,2⟩ pre38_1_4=true :=
  prefixGood_chain ⟨3,8,2⟩ 1 2 837342972874 pre38_1_4_data (prefixFind_sound ⟨3,8,2⟩ pre38_1_2 pre38_1_2_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre38Part002

section Pack_Z6970H2307PackedPre39Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre39_2_39_data : List (Nat × Nat) :=
  [(39,12523385237287), (45,13830843071656), (78,18845768522741), (92,20098972921524), (98,20515560598816),
    (101,20700130707613), (102,20758346328853), (104,20869997022580), (105,20923491457070), (106,20975471053340),
    (107,21025964782277), (108,21075001332257)]

def pre39_2_39 : List PrefixEntry := pre39_2_39_data.map fun (l,v) => (2,l,v)

theorem pre39_2_39_good : prefixGood ⟨4,8,2⟩ pre39_2_39=true :=
  prefixGood_chain ⟨4,8,2⟩ 2 34 11322679225324 pre39_2_39_data (prefixFind_sound ⟨4,8,2⟩ pre39_2_16 pre39_2_16_good (by decide)) (by decide +kernel)

private def pre39_1_2_data : List (Nat × Nat) :=
  [(2,837008439086), (4,1650867981171)]

def pre39_1_2 : List PrefixEntry := pre39_1_2_data.map fun (l,v) => (1,l,v)

theorem pre39_1_2_good : prefixGood ⟨4,8,2⟩ pre39_1_2=true :=
  prefixGood_chain ⟨4,8,2⟩ 1 0 0 pre39_1_2_data rfl (by decide +kernel)

private def pre39_1_6_data : List (Nat × Nat) :=
  [(6,2441910140420), (8,3210474947457), (10,3956909440919), (12,4681567104893), (14,5384808812946)]

def pre39_1_6 : List PrefixEntry := pre39_1_6_data.map fun (l,v) => (1,l,v)

theorem pre39_1_6_good : prefixGood ⟨4,8,2⟩ pre39_1_6=true :=
  prefixGood_chain ⟨4,8,2⟩ 1 4 1650867981171 pre39_1_6_data (prefixFind_sound ⟨4,8,2⟩ pre39_1_2 pre39_1_2_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre39Part002

section Pack_Z6970H2307PackedPre40Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre40_1_12_data : List (Nat × Nat) :=
  [(12,4656620021058), (14,5351615355498), (16,6024534122267), (18,6675808446461), (20,7305878411642),
    (22,7915190587542)]

def pre40_1_12 : List PrefixEntry := pre40_1_12_data.map fun (l,v) => (1,l,v)

theorem pre40_1_12_good : prefixGood ⟨7,8,1⟩ pre40_1_12=true :=
  prefixGood_chain ⟨7,8,1⟩ 1 10 3939124199253 pre40_1_12_data (prefixFind_sound ⟨7,8,1⟩ pre40_1_2 pre40_1_2_good (by decide)) (by decide +kernel)

private def pre40_1_25_data : List (Nat × Nat) :=
  [(25,8791228769026), (28,9623116170984), (31,10412385551328), (34,11160560056880), (38,12096803138144),
    (129,21010242100601), (133,21088744934493), (134,21106497192738), (135,21123540422838), (136,21139894268280),
    (137,21155578067544), (138,21170610858120), (139,21185011377640), (140,21198798062151)]

def pre40_1_25 : List PrefixEntry := pre40_1_25_data.map fun (l,v) => (1,l,v)

theorem pre40_1_25_good : prefixGood ⟨7,8,1⟩ pre40_1_25=true :=
  prefixGood_chain ⟨7,8,1⟩ 1 22 7915190587542 pre40_1_25_data (prefixFind_sound ⟨7,8,1⟩ pre40_1_12 pre40_1_12_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre40Part002

section Pack_Z6970H2307PackedPre41Part001

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre41_2_12_data : List (Nat × Nat) :=
  [(12,4656690024254), (17,6352931454417), (22,7915278699094), (28,9623207201961), (35,11401172178315)]

def pre41_2_12 : List PrefixEntry := pre41_2_12_data.map fun (l,v) => (2,l,v)

theorem pre41_2_12_good : prefixGood ⟨7,8,2⟩ pre41_2_12=true :=
  prefixGood_chain ⟨7,8,2⟩ 2 8 3198767788393 pre41_2_12_data (prefixFind_sound ⟨7,8,2⟩ pre41_2_4 pre41_2_4_good (by decide)) (by decide +kernel)

private def pre41_2_122_data : List (Nat × Nat) :=
  [(122,20840841403253), (125,20918835559935), (126,20943003917463), (127,20966295059895), (130,21031124713852),
    (131,21051124958682), (132,21070355417878), (133,21088836651022), (134,21106588909267), (135,21123632139367),
    (136,21139985984809), (137,21155669784073), (138,21170702574649), (140,21198889778680)]

def pre41_2_122 : List PrefixEntry := pre41_2_122_data.map fun (l,v) => (2,l,v)

theorem pre41_2_122_good : prefixGood ⟨7,8,2⟩ pre41_2_122=true :=
  prefixGood_chain ⟨7,8,2⟩ 2 35 11401172178315 pre41_2_122_data (prefixFind_sound ⟨7,8,2⟩ pre41_2_12 pre41_2_12_good (by decide)) (by decide +kernel)

private def pre41_1_2_data : List (Nat × Nat) :=
  [(2,836002045315), (4,1647539821028), (6,2434983099623), (8,3198713292521), (10,3939124199253)]

def pre41_1_2 : List PrefixEntry := pre41_1_2_data.map fun (l,v) => (1,l,v)

theorem pre41_1_2_good : prefixGood ⟨7,8,2⟩ pre41_1_2=true :=
  prefixGood_chain ⟨7,8,2⟩ 1 0 0 pre41_1_2_data rfl (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre41Part001
