import ProximityPrize.SubmissionLower.Z6970H2307OrderPackedTools
import ProximityPrize.SubmissionLower.Bundle6970_30617aa99451fc16

section Pack_Z6970H2307PackedPre01Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre1_1_32_data : List (Nat × Nat) :=
  [(32,12568356351251), (34,13284975808351), (36,13993769136299), (38,14694784414793), (40,15388069912945),
    (41,15731829208778)]

def pre1_1_32 : List PrefixEntry := pre1_1_32_data.map fun (l,v) => (1,l,v)

theorem pre1_1_32_good : prefixGood ⟨1,3,1⟩ pre1_1_32=true :=
  prefixGood_chain ⟨1,3,1⟩ 1 30 11843862925400 pre1_1_32_data (prefixFind_sound ⟨1,3,1⟩ pre1_1_22 pre1_1_22_good (by decide)) (by decide +kernel)

private def pre1_1_43_data : List (Nat × Nat) :=
  [(43,16413611474254), (45,17087786284563), (47,17754403054111), (49,18413511468075), (50,18740265640955),
    (51,19065161478348), (52,19388205263571)]

def pre1_1_43 : List PrefixEntry := pre1_1_43_data.map fun (l,v) => (1,l,v)

theorem pre1_1_43_good : prefixGood ⟨1,3,1⟩ pre1_1_43=true :=
  prefixGood_chain ⟨1,3,1⟩ 1 41 15731829208778 pre1_1_43_data (prefixFind_sound ⟨1,3,1⟩ pre1_1_32 pre1_1_32_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre01Part004

section Pack_Z6970H2307PackedPre02Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre2_1_32_data : List (Nat × Nat) :=
  [(32,12512379729314), (34,13222180132589), (35,13574009856558), (37,14271562711143), (39,14961019533123),
    (41,15642435950732)]

def pre2_1_32 : List PrefixEntry := pre2_1_32_data.map fun (l,v) => (1,l,v)

theorem pre2_1_32_good : prefixGood ⟨2,3,1⟩ pre2_1_32=true :=
  prefixGood_chain ⟨2,3,1⟩ 1 30 11794345845380 pre2_1_32_data (prefixFind_sound ⟨2,3,1⟩ pre2_1_22 pre2_1_22_good (by decide)) (by decide +kernel)

private def pre2_1_43_data : List (Nat × Nat) :=
  [(43,16315867948140), (45,16981371704906), (46,17311168136298), (48,17964885691874), (50,18610817182387),
    (51,18930881106016), (52,19249020093309), (53,19565241378450)]

def pre2_1_43 : List PrefixEntry := pre2_1_43_data.map fun (l,v) => (1,l,v)

theorem pre2_1_43_good : prefixGood ⟨2,3,1⟩ pre2_1_43=true :=
  prefixGood_chain ⟨2,3,1⟩ 1 41 15642435950732 pre2_1_43_data (prefixFind_sound ⟨2,3,1⟩ pre2_1_32 pre2_1_32_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre02Part004

section Pack_Z6970H2307PackedPre03Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre3_1_40_data : List (Nat × Nat) :=
  [(40,15216162542839), (42,15885246553789), (44,16546043294691), (46,17198617071849), (48,17843032408842),
    (50,18479354448320), (51,18794500962027)]

def pre3_1_40 : List PrefixEntry := pre3_1_40_data.map fun (l,v) => (1,l,v)

theorem pre3_1_40_good : prefixGood ⟨3,3,1⟩ pre3_1_40=true :=
  prefixGood_chain ⟨3,3,1⟩ 1 38 14538727374186 pre3_1_40_data (prefixFind_sound ⟨3,3,1⟩ pre3_1_28 pre3_1_28_good (by decide)) (by decide +kernel)

private def pre3_1_53_data : List (Nat × Nat) :=
  [(53,19418806136324)]

def pre3_1_53 : List PrefixEntry := pre3_1_53_data.map fun (l,v) => (1,l,v)

theorem pre3_1_53_good : prefixGood ⟨3,3,1⟩ pre3_1_53=true :=
  prefixGood_chain ⟨3,3,1⟩ 1 51 18794500962027 pre3_1_53_data (prefixFind_sound ⟨3,3,1⟩ pre3_1_40 pre3_1_40_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre03Part004

section Pack_Z6970H2307PackedPre04Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre4_1_50_data : List (Nat × Nat) :=
  [(50,18346218340122), (51,18656385504420)]

def pre4_1_50 : List PrefixEntry := pre4_1_50_data.map fun (l,v) => (1,l,v)

theorem pre4_1_50_good : prefixGood ⟨4,3,1⟩ pre4_1_50=true :=
  prefixGood_chain ⟨4,3,1⟩ 1 47 17403189332734 pre4_1_50_data (prefixFind_sound ⟨4,3,1⟩ pre4_1_34 pre4_1_34_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre04Part004

section Pack_Z6970H2307PackedPre10Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre10_1_28_data : List (Nat × Nat) :=
  [(28,10808702217697), (30,11498736363815), (32,12178315548399), (34,12847533019980), (36,13506483020185),
    (38,14155260480990)]

def pre10_1_28 : List PrefixEntry := pre10_1_28_data.map fun (l,v) => (1,l,v)

theorem pre10_1_28_good : prefixGood ⟨2,4,1⟩ pre10_1_28=true :=
  prefixGood_chain ⟨2,4,1⟩ 1 26 10108120433943 pre10_1_28_data (prefixFind_sound ⟨2,4,1⟩ pre10_1_18 pre10_1_18_good (by decide)) (by decide +kernel)

private def pre10_1_40_data : List (Nat × Nat) :=
  [(40,14793961004067), (42,15422680840105), (44,16041516838277), (46,16650566309502), (48,17249927100817),
    (50,17839697109729)]

def pre10_1_40 : List PrefixEntry := pre10_1_40_data.map fun (l,v) => (1,l,v)

theorem pre10_1_40_good : prefixGood ⟨2,4,1⟩ pre10_1_40=true :=
  prefixGood_chain ⟨2,4,1⟩ 1 38 14155260480990 pre10_1_40_data (prefixFind_sound ⟨2,4,1⟩ pre10_1_28 pre10_1_28_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre10Part004

section Pack_Z6970H2307PackedPre11Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre11_1_34_data : List (Nat × Nat) :=
  [(34,12786066866530), (36,13438131859655), (38,14079720106685), (40,14710937148144), (42,15331889519735),
    (44,15942684482280)]

def pre11_1_34 : List PrefixEntry := pre11_1_34_data.map fun (l,v) => (1,l,v)

theorem pre11_1_34_good : prefixGood ⟨3,4,1⟩ pre11_1_34=true :=
  prefixGood_chain ⟨3,4,1⟩ 1 32 12123420171895 pre11_1_34_data (prefixFind_sound ⟨3,4,1⟩ pre11_1_22 pre11_1_22_good (by decide)) (by decide +kernel)

private def pre11_1_46_data : List (Nat × Nat) :=
  [(46,16543429925455), (48,17134233992591), (50,17715205033537), (52,18286451403219), (53,18568461679388),
    (54,18848081385439), (55,19125324002727), (57,19672732008847)]

def pre11_1_46 : List PrefixEntry := pre11_1_46_data.map fun (l,v) => (1,l,v)

theorem pre11_1_46_good : prefixGood ⟨3,4,1⟩ pre11_1_46=true :=
  prefixGood_chain ⟨3,4,1⟩ 1 44 15942684482280 pre11_1_46_data (prefixFind_sound ⟨3,4,1⟩ pre11_1_34 pre11_1_34_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre11Part004

section Pack_Z6970H2307PackedPre12Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre12_1_43_data : List (Nat × Nat) :=
  [(43,15542705294065), (46,16435090520638), (49,17304542041011), (52,18151463211965), (55,18976257150954),
    (56,19246340833398)]

def pre12_1_43 : List PrefixEntry := pre12_1_43_data.map fun (l,v) => (1,l,v)

theorem pre12_1_43_good : prefixGood ⟨4,4,1⟩ pre12_1_43=true :=
  prefixGood_chain ⟨4,4,1⟩ 1 40 14626983544306 pre12_1_43_data (prefixFind_sound ⟨4,4,1⟩ pre12_1_28 pre12_1_28_good (by decide)) (by decide +kernel)

private def pre12_1_58_data : List (Nat × Nat) :=
  [(58,19779326001282)]

def pre12_1_58 : List PrefixEntry := pre12_1_58_data.map fun (l,v) => (1,l,v)

theorem pre12_1_58_good : prefixGood ⟨4,4,1⟩ pre12_1_58=true :=
  prefixGood_chain ⟨4,4,1⟩ 1 56 19246340833398 pre12_1_58_data (prefixFind_sound ⟨4,4,1⟩ pre12_1_43 pre12_1_43_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre12Part004

section Pack_Z6970H2307PackedPre13Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre13_1_55_data : List (Nat × Nat) :=
  [(55,18825956341314), (58,19614436037499), (59,19872412608931)]

def pre13_1_55 : List PrefixEntry := pre13_1_55_data.map fun (l,v) => (1,l,v)

theorem pre13_1_55_good : prefixGood ⟨5,4,1⟩ pre13_1_55=true :=
  prefixGood_chain ⟨5,4,1⟩ 1 51 17740093373806 pre13_1_55_data (prefixFind_sound ⟨5,4,1⟩ pre13_1_38 pre13_1_38_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre13Part004

section Pack_Z6970H2307PackedPre17Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre17_1_26_data : List (Nat × Nat) :=
  [(26,9886335010428), (28,10553706949671), (30,11208464056683), (32,11850749213052), (34,12480706395717),
    (36,13098481015383)]

def pre17_1_26 : List PrefixEntry := pre17_1_26_data.map fun (l,v) => (1,l,v)

theorem pre17_1_26_good : prefixGood ⟨2,5,1⟩ pre17_1_26=true :=
  prefixGood_chain ⟨2,5,1⟩ 1 24 9206206548047 pre17_1_26_data (prefixFind_sound ⟨2,5,1⟩ pre17_1_16 pre17_1_16_good (by decide)) (by decide +kernel)

private def pre17_1_38_data : List (Nat × Nat) :=
  [(38,13704219512064), (40,14298068629388), (42,14880175041065), (44,15450685281994), (46,16009745625932),
    (48,16557502283184)]

def pre17_1_38 : List PrefixEntry := pre17_1_38_data.map fun (l,v) => (1,l,v)

theorem pre17_1_38_good : prefixGood ⟨2,5,1⟩ pre17_1_38=true :=
  prefixGood_chain ⟨2,5,1⟩ 1 36 13098481015383 pre17_1_38_data (prefixFind_sound ⟨2,5,1⟩ pre17_1_26 pre17_1_26_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre17Part004

section Pack_Z6970H2307PackedPre29Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre29_1_34_data : List (Nat × Nat) :=
  [(34,11716215588781), (36,12250568600296), (38,12769532593609), (40,13273395450346), (42,13762444087458),
    (44,14236964174669)]

def pre29_1_34 : List PrefixEntry := pre29_1_34_data.map fun (l,v) => (1,l,v)

theorem pre29_1_34_good : prefixGood ⟨3,7,1⟩ pre29_1_34=true :=
  prefixGood_chain ⟨3,7,1⟩ 1 32 11166184668202 pre29_1_34_data (prefixFind_sound ⟨3,7,1⟩ pre29_1_22 pre29_1_22_good (by decide)) (by decide +kernel)

private def pre29_1_46_data : List (Nat × Nat) :=
  [(46,14697239954829), (48,15143554059054), (50,15576187429903), (52,15995419115451), (55,16599743780622),
    (58,17175462598356)]

def pre29_1_46 : List PrefixEntry := pre29_1_46_data.map fun (l,v) => (1,l,v)

theorem pre29_1_46_good : prefixGood ⟨3,7,1⟩ pre29_1_46=true :=
  prefixGood_chain ⟨3,7,1⟩ 1 44 14236964174669 pre29_1_46_data (prefixFind_sound ⟨3,7,1⟩ pre29_1_34 pre29_1_34_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre29Part004

section Pack_Z6970H2307PackedPre30Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre30_1_34_data : List (Nat × Nat) :=
  [(34,11716215588781), (36,12250568600296), (38,12769532593609), (40,13273395450346), (42,13762444087458),
    (44,14236964174669)]

def pre30_1_34 : List PrefixEntry := pre30_1_34_data.map fun (l,v) => (1,l,v)

theorem pre30_1_34_good : prefixGood ⟨3,7,2⟩ pre30_1_34=true :=
  prefixGood_chain ⟨3,7,2⟩ 1 32 11166184668202 pre30_1_34_data (prefixFind_sound ⟨3,7,2⟩ pre30_1_22 pre30_1_22_good (by decide)) (by decide +kernel)

private def pre30_1_46_data : List (Nat × Nat) :=
  [(46,14697239954829), (48,15143554059054), (50,15576187429903), (52,15995419115451), (55,16599743780622),
    (58,17175462598356)]

def pre30_1_46 : List PrefixEntry := pre30_1_46_data.map fun (l,v) => (1,l,v)

theorem pre30_1_46_good : prefixGood ⟨3,7,2⟩ pre30_1_46=true :=
  prefixGood_chain ⟨3,7,2⟩ 1 44 14236964174669 pre30_1_46_data (prefixFind_sound ⟨3,7,2⟩ pre30_1_34 pre30_1_34_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre30Part004

section Pack_Z6970H2307PackedPre37Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre37_1_14_data : List (Nat × Nat) :=
  [(14,5395753935473), (16,6080995034902), (18,6745877822425), (20,7390762036293), (22,8016012294368),
    (24,8621997829459)]

def pre37_1_14 : List PrefixEntry := pre37_1_14_data.map fun (l,v) => (1,l,v)

theorem pre37_1_14_good : prefixGood ⟨3,8,1⟩ pre37_1_14=true :=
  prefixGood_chain ⟨3,8,1⟩ 1 12 4689800071536 pre37_1_14_data (prefixFind_sound ⟨3,8,1⟩ pre37_1_4 pre37_1_4_good (by decide)) (by decide +kernel)

private def pre37_1_26_data : List (Nat × Nat) :=
  [(26,9209090270477), (28,9777661012379), (30,10328080775723), (32,10860719339117), (34,11375945591015),
    (36,11874127081435)]

def pre37_1_26 : List PrefixEntry := pre37_1_26_data.map fun (l,v) => (1,l,v)

theorem pre37_1_26_good : prefixGood ⟨3,8,1⟩ pre37_1_26=true :=
  prefixGood_chain ⟨3,8,1⟩ 1 24 8621997829459 pre37_1_26_data (prefixFind_sound ⟨3,8,1⟩ pre37_1_14 pre37_1_14_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre37Part003

section Pack_Z6970H2307PackedPre38Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre38_1_14_data : List (Nat × Nat) :=
  [(14,5395753935473), (16,6080995034902), (18,6745877822425), (20,7390762036293), (22,8016012294368),
    (24,8621997829459)]

def pre38_1_14 : List PrefixEntry := pre38_1_14_data.map fun (l,v) => (1,l,v)

theorem pre38_1_14_good : prefixGood ⟨3,8,2⟩ pre38_1_14=true :=
  prefixGood_chain ⟨3,8,2⟩ 1 12 4689800071536 pre38_1_14_data (prefixFind_sound ⟨3,8,2⟩ pre38_1_4 pre38_1_4_good (by decide)) (by decide +kernel)

private def pre38_1_26_data : List (Nat × Nat) :=
  [(26,9209090270477), (28,9777661012379), (30,10328080775723), (32,10860719339117), (34,11375945591015),
    (36,11874127081435)]

def pre38_1_26 : List PrefixEntry := pre38_1_26_data.map fun (l,v) => (1,l,v)

theorem pre38_1_26_good : prefixGood ⟨3,8,2⟩ pre38_1_26=true :=
  prefixGood_chain ⟨3,8,2⟩ 1 24 8621997829459 pre38_1_26_data (prefixFind_sound ⟨3,8,2⟩ pre38_1_14 pre38_1_14_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre38Part003

section Pack_Z6970H2307PackedPre39Part003

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre39_1_16_data : List (Nat × Nat) :=
  [(16,6067001727258), (18,6728518606095), (20,7369738373744), (22,7991045333357), (24,8592828294042),
    (26,9175478607377)]

def pre39_1_16 : List PrefixEntry := pre39_1_16_data.map fun (l,v) => (1,l,v)

theorem pre39_1_16_good : prefixGood ⟨4,8,2⟩ pre39_1_16=true :=
  prefixGood_chain ⟨4,8,2⟩ 1 14 5384808812946 pre39_1_16_data (prefixFind_sound ⟨4,8,2⟩ pre39_1_6 pre39_1_6_good (by decide)) (by decide +kernel)

private def pre39_1_28_data : List (Nat × Nat) :=
  [(28,9739387494257), (30,10284945284800), (32,10812541488440), (34,11322564337863), (36,11815400302514),
    (38,12291433922609), (40,12751047459768)]

def pre39_1_28 : List PrefixEntry := pre39_1_28_data.map fun (l,v) => (1,l,v)

theorem pre39_1_28_good : prefixGood ⟨4,8,2⟩ pre39_1_28=true :=
  prefixGood_chain ⟨4,8,2⟩ 1 26 9175478607377 pre39_1_28_data (prefixFind_sound ⟨4,8,2⟩ pre39_1_16 pre39_1_16_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre39Part003

section Pack_Z6970H2307PackedPre41Part002

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre41_1_12_data : List (Nat × Nat) :=
  [(12,4656620021058), (14,5351615355498), (16,6024534122267), (18,6675808446461), (20,7305878411642),
    (22,7915190587542)]

def pre41_1_12 : List PrefixEntry := pre41_1_12_data.map fun (l,v) => (1,l,v)

theorem pre41_1_12_good : prefixGood ⟨7,8,2⟩ pre41_1_12=true :=
  prefixGood_chain ⟨7,8,2⟩ 1 10 3939124199253 pre41_1_12_data (prefixFind_sound ⟨7,8,2⟩ pre41_1_2 pre41_1_2_good (by decide)) (by decide +kernel)

private def pre41_1_25_data : List (Nat × Nat) :=
  [(25,8791228769026), (28,9623116170984), (31,10412385551328), (34,11160560056880), (38,12096803138144),
    (129,21010242100601), (133,21088744934493), (134,21106497192738), (135,21123540422838), (136,21139894268280),
    (137,21155578067544), (138,21170610858120), (139,21185011377640), (140,21198798062151)]

def pre41_1_25 : List PrefixEntry := pre41_1_25_data.map fun (l,v) => (1,l,v)

theorem pre41_1_25_good : prefixGood ⟨7,8,2⟩ pre41_1_25=true :=
  prefixGood_chain ⟨7,8,2⟩ 1 22 7915190587542 pre41_1_25_data (prefixFind_sound ⟨7,8,2⟩ pre41_1_12 pre41_1_12_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre41Part002
