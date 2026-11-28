import ProximityPrize.SubmissionLower.Z6970H2307OrderPackedTools
import ProximityPrize.SubmissionLower.Bundle6970_94cd5bdb3c76dc56

section Pack_Z6970H2307PackedPre10Part005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre10_1_52_data : List (Nat × Nat) :=
  [(52,18419974191721), (54,18990856143195), (56,19552440677714)]

def pre10_1_52 : List PrefixEntry := pre10_1_52_data.map fun (l,v) => (1,l,v)

theorem pre10_1_52_good : prefixGood ⟨2,4,1⟩ pre10_1_52=true :=
  prefixGood_chain ⟨2,4,1⟩ 1 50 17839697109729 pre10_1_52_data (prefixFind_sound ⟨2,4,1⟩ pre10_1_40 pre10_1_40_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre10Part005

section Pack_Z6970H2307PackedPre17Part005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre17_1_50_data : List (Nat × Nat) :=
  [(50,17094101253879), (52,17619688262073), (54,18134408720218), (56,18638407690377), (58,19131829777502),
    (59,19374619580366), (61,19852446650231)]

def pre17_1_50 : List PrefixEntry := pre17_1_50_data.map fun (l,v) => (1,l,v)

theorem pre17_1_50_good : prefixGood ⟨2,5,1⟩ pre17_1_50=true :=
  prefixGood_chain ⟨2,5,1⟩ 1 48 16557502283184 pre17_1_50_data (prefixFind_sound ⟨2,5,1⟩ pre17_1_38 pre17_1_38_good (by decide)) (by decide +kernel)

private def pre17_1_62_data : List (Nat × Nat) :=
  [(62,20087519803363)]

def pre17_1_62 : List PrefixEntry := pre17_1_62_data.map fun (l,v) => (1,l,v)

theorem pre17_1_62_good : prefixGood ⟨2,5,1⟩ pre17_1_62=true :=
  prefixGood_chain ⟨2,5,1⟩ 1 61 19852446650231 pre17_1_62_data (prefixFind_sound ⟨2,5,1⟩ pre17_1_50 pre17_1_50_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre17Part005

section Pack_Z6970H2307PackedPre29Part005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre29_1_69_data : List (Nat × Nat) :=
  [(69,19056293825872), (72,19510360230808), (73,19656425064853), (74,19799896326925), (77,20215055532787),
    (79,20479419868475), (81,20734137484941)]

def pre29_1_69 : List PrefixEntry := pre29_1_69_data.map fun (l,v) => (1,l,v)

theorem pre29_1_69_good : prefixGood ⟨3,7,1⟩ pre29_1_69=true :=
  prefixGood_chain ⟨3,7,1⟩ 1 58 17175462598356 pre29_1_69_data (prefixFind_sound ⟨3,7,1⟩ pre29_1_46 pre29_1_46_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre29Part005

section Pack_Z6970H2307PackedPre30Part005

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre30_1_69_data : List (Nat × Nat) :=
  [(69,19056293825872), (72,19510360230808), (73,19656425064853), (74,19799896326925), (77,20215055532787),
    (79,20479419868475), (81,20734137484941)]

def pre30_1_69 : List PrefixEntry := pre30_1_69_data.map fun (l,v) => (1,l,v)

theorem pre30_1_69_good : prefixGood ⟨3,7,2⟩ pre30_1_69=true :=
  prefixGood_chain ⟨3,7,2⟩ 1 58 17175462598356 pre30_1_69_data (prefixFind_sound ⟨3,7,2⟩ pre30_1_46 pre30_1_46_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre30Part005

section Pack_Z6970H2307PackedPre37Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre37_1_38_data : List (Nat × Nat) :=
  [(38,12355629764489), (40,12820817727986), (42,13270053097287), (44,13703695707035), (46,14122102845729),
    (48,14525629009670), (50,14914625704856)]

def pre37_1_38 : List PrefixEntry := pre37_1_38_data.map fun (l,v) => (1,l,v)

theorem pre37_1_38_good : prefixGood ⟨3,8,1⟩ pre37_1_38=true :=
  prefixGood_chain ⟨3,8,1⟩ 1 36 11874127081435 pre37_1_38_data (prefixFind_sound ⟨3,8,1⟩ pre37_1_26 pre37_1_26_good (by decide)) (by decide +kernel)

private def pre37_1_52_data : List (Nat × Nat) :=
  [(52,15289441176466), (86,19810142303484), (94,20459674158847), (95,20532044579893), (98,20738167905666),
    (100,20866739900040), (101,20928465360728), (102,20988524303936), (103,21046946780048)]

def pre37_1_52 : List PrefixEntry := pre37_1_52_data.map fun (l,v) => (1,l,v)

theorem pre37_1_52_good : prefixGood ⟨3,8,1⟩ pre37_1_52=true :=
  prefixGood_chain ⟨3,8,1⟩ 1 50 14914625704856 pre37_1_52_data (prefixFind_sound ⟨3,8,1⟩ pre37_1_38 pre37_1_38_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre37Part004

section Pack_Z6970H2307PackedPre38Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre38_1_38_data : List (Nat × Nat) :=
  [(38,12355629764489), (40,12820817727986), (42,13270053097287), (44,13703695707035), (46,14122102845729),
    (48,14525629009670), (50,14914625704856)]

def pre38_1_38 : List PrefixEntry := pre38_1_38_data.map fun (l,v) => (1,l,v)

theorem pre38_1_38_good : prefixGood ⟨3,8,2⟩ pre38_1_38=true :=
  prefixGood_chain ⟨3,8,2⟩ 1 36 11874127081435 pre38_1_38_data (prefixFind_sound ⟨3,8,2⟩ pre38_1_26 pre38_1_26_good (by decide)) (by decide +kernel)

private def pre38_1_52_data : List (Nat × Nat) :=
  [(52,15289441176466), (86,19810142303484), (94,20459674158847), (95,20532044579893), (98,20738167905666),
    (100,20866739900040), (101,20928465360728), (102,20988524303936), (103,21046946780048)]

def pre38_1_52 : List PrefixEntry := pre38_1_52_data.map fun (l,v) => (1,l,v)

theorem pre38_1_52_good : prefixGood ⟨3,8,2⟩ pre38_1_52=true :=
  prefixGood_chain ⟨3,8,2⟩ 1 50 14914625704856 pre38_1_52_data (prefixFind_sound ⟨3,8,2⟩ pre38_1_38 pre38_1_38_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre38Part004

section Pack_Z6970H2307PackedPre39Part004

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 50000
set_option maxHeartbeats 0

namespace Height2307Orders

private def pre39_1_43_data : List (Nat × Nat) :=
  [(43,13410509619534), (46,14035148118291), (49,14626213553282), (93,20172892542207), (94,20245043586757),
    (98,20515444509049), (99,20578652286223), (100,20640165430825), (101,20700014617846), (104,20869880932813),
    (105,20923375367303), (106,20975354963573), (107,21025848692510), (108,21074885242490)]

def pre39_1_43 : List PrefixEntry := pre39_1_43_data.map fun (l,v) => (1,l,v)

theorem pre39_1_43_good : prefixGood ⟨4,8,2⟩ pre39_1_43=true :=
  prefixGood_chain ⟨4,8,2⟩ 1 40 12751047459768 pre39_1_43_data (prefixFind_sound ⟨4,8,2⟩ pre39_1_28 pre39_1_28_good (by decide)) (by decide +kernel)

end Height2307Orders
end Pack_Z6970H2307PackedPre39Part004
