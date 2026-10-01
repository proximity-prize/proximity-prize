import ProximityPrize.SubmissionLower.RelativeWideBlocks6815
set_option Elab.async false
section MergedPart0
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R144
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨16,41,3670,3956,17619782869255014⟩
private def profiles_RelativeWidePack6815_P24 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨24414,146,5079⟩
  | 4 => ⟨29843,173,5971⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P24 : WideCovered band 5373895 7789007 := wide_block_sound band profiles_RelativeWidePack6815_P24 5373895 7789007 (wideData 16 0x11f68073cf6002abbf8000000001397406ac36002abbf80000000006f3907fc7c002abbf82080082008e29075e60002abbf8000000000f9b406e86c002abbf8000000001083c066bf8002abbf80000000001970077da4002abc80208008200ca3d072cb0002abbf8000000000be700608e4002abbf8000000000ef3006cc26002abbf80000000005928071b68002abbf871c01c7010bf3903ee08ae082abbf82080082001df4620e020aaefe0820041006f4320b02135dfe0630630019419402e806100196dfe40f20f20f20f20f20f207fe13aaa00ccbbeb4) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P24 : WideCovered band 7789008 8402369 := wide_block_sound band profiles_RelativeWidePack6815_P24 7789008 8402369 (wideData 16 0x67f740b5a78002abbf80000000001fa7f42fb2e000aaefe0820020804b7c0293f8800aaefe0000000006bec02a37e800aaefe000000000770b01e35f000aaefe0000000001b3d42eebb800aaefe082002080567e42ba38000aaf200000000004f8a01b308000aaefe0000000006a29028ebc000aaefe000000000522d02b2ec000aaefe0820020800678690adfaa002abbf80000000010cbc068bf2002abbf80000000015b7007ac60002abbf80000000019d600a1bfe002abbf80000000018b3d077db8002abc802d02d03c82d02d03c92f7da04bbf8ee18ef77e3c) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P24 : WideCovered band 8402370 9015731 := wide_block_sound band profiles_RelativeWidePack6815_P24 8402370 9015731 (wideData 16 0x63dac0bac6a002abbf80000000001c26c04b64e000aaefe000000000065a6813f82c002abbf8208008200293d843cfab000aaefe000000000060aa80e6f30002abbf80000000001970f03bb0f000aaefe0000000000698a80b9e32002abc80000000001f92c0fef72002abbf82080082001ffdc4486aa000aaefe00000000077e902e76a800aaefe0000000007e8f028a58000aaefe00000000006adb80ea8b4002abbf8000000001dc610fbbfa002abbf8208008200ae790a3ffa002abbf8000000001c8bc0aed74002abc802e82e83c82e82e83c96eb2e05c7ff3e1908e5e20) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P24 : WideCovered band 9015732 9629093 := wide_block_sound band profiles_RelativeWidePack6815_P24 9015732 9629093 (wideData 16 0x7a824222c26002abbf80000000001fe9908b319000aaefe00000000007cc301abea0002abbf80000000010f6c26fb34002abbf82080082017e651bfe7c002abbf80000000001bf99068ffd000aaefe00000000006d9e8131afe002abc800000000001f24f06e21e800aaefe0000000000619a81edaac002abbf82080082001dbbd44d339000aaefe000000000068d6c1389e8002abbf80000000001b7bd05837e800aaefe00000000006eaec0f6db4002abbf80000000001ff4c05f208000aaefe0820020800b4d31177be2002abc803803803c83803803c9ef32e079faab4191a33de4) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P24 : WideCovered band 9629094 10242455 := wide_block_sound band profiles_RelativeWidePack6815_P24 9629094 10242455 (wideData 16 0x130f706a8924002abbf80000000004c63f19dfbf000aaefe0000000000fbd384fdce8002abbf82080082007d355ecc7a002abbf80000000002feb810ca2d000aaefe0000000000b08ec332fa4002abbf800000000038f6f10b37f800aaf200000000000e8ae4433f20002abbf80000000002fa7b0cfb58800aaefe082002080076c653748b2002abbf800000000029ab90b8b3a000aaefe0000000000a9fa42e7dec002abbf800000000028b3908caec000aaefe0000000000b6b702ffcf0002abbf82080082001d7594bba2d800aaf200e60e60f20e60e60f206db2690aaf2af6192ba1da8) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P24 : WideCovered band 10242456 10280790 := wide_block_sound band profiles_RelativeWidePack6815_P24 10242456 10280790 (wideData 1 0xee0ee0f20ee0ee0f20a7ae0d11afbe7e213cefd6c) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 5373895 7789007 10280790 c0_RelativeWidePack6815_P24 (wide_covered_join band 7789008 8402369 10280790 c1_RelativeWidePack6815_P24 (wide_covered_join band 8402370 9015731 10280790 c2_RelativeWidePack6815_P24 (wide_covered_join band 9015732 9629093 10280790 c3_RelativeWidePack6815_P24 (wide_covered_join band 9629094 10242455 10280790 c4_RelativeWidePack6815_P24 c5_RelativeWidePack6815_P24)))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 16)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 16≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤41)
    (hT0 : 3670≤T) (hT1 : T≤3956) (hnu : 5373895≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤17619782869255014 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R144

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R145
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨16,42,3589,3930,17946072568172132⟩
private def profiles_RelativeWidePack6815_P24 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨24504,145,5079⟩
  | 4 => ⟨29904,171,5971⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P24 : WideCovered band 5504966 7634957 := wide_block_sound band profiles_RelativeWidePack6815_P24 5504966 7634957 (wideData 16 0x119a8066e7a002af4b8000000001483006ab74002af4b80000000006af006fb7a002af4b82080082014dad072a34002af4b8000000000ef6c063d72002af4b8000000000fd2476ee000abd2e0000000002fec01aa7f800abd300820020805abc41bee9800abd2e000000000360c0182fc800abd2e0000000003b9e018e4b000abd2e0000000001feb019b5f800abd2e0000000003a2d418a19800abd2e2490092404b89f80eefabf820abd2e1450051400a3917da8084de8f8f3c03cf0019342fae824bd8f20e60e60f40e60e60f40b1f12ff000cef4ab2) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P24 : WideCovered band 7634958 8254590 := wide_block_sound band profiles_RelativeWidePack6815_P24 7634958 8254590 (wideData 16 0x63b380a0974002af4b8000000000bf7c0a9b60002af4b8000000000186fb41eeea800abd2e0820020802e7c01e35a000abd2e000000000738a01db8b800abd2e000000000063a6407dc66002af4b800000000019769429fed000abd300820020804ec07787e002af4b80000000015d3c062bbc002af4b8000000001cd2407586a002af4b80000000007ee107ce68002af4b82080082012df907a9f8002af4b8000000001493c06baa0002af4b80000000017ea006fde6002af4b80000000005ea8067e20002af4b82c82c83d02c82c83d148f4904867f2618ed2bd68) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P24 : WideCovered band 8254591 8874224 := wide_block_sound band profiles_RelativeWidePack6815_P24 8254591 8874224 (wideData 16 0x2080082001da3d43ef9e000abd2e000000000066eec0b4e30002af4b80000000001bb0b02effb000abd2e000000000079fa00e79a2002af4b800000000028a9f43e6d8800abd2e0820020800a7801ee7a000abd2e000000000064f740a9fb2002af4c00000000001b3eb02c68c000abd2e000000000062e2c0bcde2002af4b82080082002aada43b78f800abd2e0000000007a5c01febf800abd2e000000000060a7406cdee002af4b80000000001b27e02aacd800abd2e0000000002a6a42db3d000abd2e0820020800639b50b4834002af4c02e02e03d02e02e03d18face04f64aa418fea5f2a) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P24 : WideCovered band 8874225 9493858 := wide_block_sound band profiles_RelativeWidePack6815_P24 8874225 9493858 (wideData 16 0x2bf2847ca4e800abd2e08200208006dca4134a2c002af4b80000000001b27f03a37a000abd2e00000000007ade413ec30002af4b8000000000293cc05ae7b000abd2e0000000004f1e45fe4d800abd2e082002080533b44cf2c800abd3000000000006df740fa87c002af4b80000000001ba8c02d64b000abd2e00000000007f9ac129e2a002af4b80000000003ffc13be2c002af4b82080082001ca5e44ab5b000abd2e000000000069dfc0e49f0002af4b80000000001c64a03af4c800abd2e00000000007bd640f4ea0002af4c03803803d03803803d1cebc906a2dc3c1918208ee) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P24 : WideCovered band 9493859 10113492 := wide_block_sound band profiles_RelativeWidePack6815_P24 9493859 10113492 (wideData 16 0x20800820019a1b509e58800abd2e0000000000b5fe02ece70002af4b80000000002e60d0bb6fe800abd2e0000000000bdd682f2baa002af4b8000000000392e90bf3ef000abd2e000000000076b3c265ffa002af4b82080082001affb49d75e800abd300000000000a4c38221ff6002af4b80000000002a6ee089f9e000abd2e0000000000b0bb4232922002af4b80000000002eadd098b7c000abd2e0820020800b68e11f283e002af4b80000000001c76804ef6b800abd2e00000000007cb681a3de6002af4b800000000028ef806b639800abd300e60e60f40e60e60f406ab7a908c78e2019297aab2) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P24 : WideCovered band 10113493 10462035 := wide_block_sound band profiles_RelativeWidePack6815_P24 10113493 10462035 (wideData 9 0x13daf44309fa002af4b820800820038e2c55ff7a800abd2e0000000000bf8b42adeb0002af4b80000000005d75856862ec20abd2e08200208006ba644bdae2002af4b80000000003e73c11ab18000abd2e0000000000fba284648ac002af4b80000000003fb88118f7e800abd2e0ec0ec0f40ec0ec0f40a59e3c0dae8da8193af4c76) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 5504966 7634957 10462035 c0_RelativeWidePack6815_P24 (wide_covered_join band 7634958 8254590 10462035 c1_RelativeWidePack6815_P24 (wide_covered_join band 8254591 8874224 10462035 c2_RelativeWidePack6815_P24 (wide_covered_join band 8874225 9493858 10462035 c3_RelativeWidePack6815_P24 (wide_covered_join band 9493859 10113492 10462035 c4_RelativeWidePack6815_P24 c5_RelativeWidePack6815_P24)))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 16)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 16≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤42)
    (hT0 : 3589≤T) (hT1 : T≤3930) (hnu : 5504966≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤17946072568172132 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R145

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R146
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨16,43,3474,3903,30411606095906251⟩
private def profiles_RelativeWidePack6815_P24 : ℕ → Profile
  | 0 => ⟨16536,4,5080⟩
  | 1 => ⟨24535,143,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P24 : WideCovered band 5636037 7474634 := wide_block_sound band profiles_RelativeWidePack6815_P24 5636037 7474634 (wideData 16 0x2080082001cf87b09800acb3e00000000053d8018388000acb3e0000000002f790192bf000acb3e00000000023f95fb62002b2cf82080082002da1065a78002b2cf800000000129b47abb800acb3e000000000364d19ea0002b2d80000000000cd2906593c002b2cf820800820019e0060ce0002b2cf8000000000eda05a4d000acb3e0000000002b6c1eca4002b2cf8000000000b8a10629b2002b2cf82080082003be05f18800acb3e0000000003a491a872002b2cf871c01c7014f2ae0383cd64082b2d802b82b83d82b82b83d879ec075af400d92ceae) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P24 : WideCovered band 7474635 8100539 := wide_block_sound band profiles_RelativeWidePack6815_P24 7474635 8100539 (wideData 16 0x7bce1deb8002b2cf80000000001a72901c2fd800acb3e00000000016eb41e27c000acb3e0000000004a9d41ba0c000acb3e082002080166801cbdf000acb3e0000000000629f406bcb6002b2cf8000000000ad3c066e60002b2cf80000000017bfd074d24002b2cf82080082001ce406f9f8002b2cf8000000001cda0067cb4002b2cf8000000000e9e87fde000acb3e0000000005a2941cbd8800acb3e082002080074a01ab5f000acb3e0000000005acf1ac72002b2cf8000000000ebfc067d62002b2d802c02c03d82c02c03d96ef2d03c6ec6008eab3a72) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P24 : WideCovered band 8100540 8726445 := wide_block_sound band profiles_RelativeWidePack6815_P24 8100540 8726445 (wideData 16 0x3f2a02deaa000acb3e0000000006a7d4283f8000acb3e082002080438c42dbbe800acb3e000000000072c2807efbc002b2cf80000000001ee3d01ae4a000acb3e0000000003a2d42bfc9000acb3e08200208007bb250e0e74002b2d800000000001964c018a68000acb3e000000000072cbc079da2002b2cf80000000015b7c0a2baa002b2cf80000000010931072a76002b2cf8208008201b9350acb6a002b2cf80000000001a60a01cac9000acb3e00000000006ff6c064ab2002b2cf800000000169a50a0d6c002b2d802e02e03d82e02e03d99f7a9049fdfac08fc39e34) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P24 : WideCovered band 8726446 9352350 := wide_block_sound band profiles_RelativeWidePack6815_P24 8726446 9352350 (wideData 16 0xa6ea40fbcf8002b2cf80000000002b69e02e318800acb3e000000000079c3513792e002b2cf82080082010f690fba6c002b2cf80000000001c67901f7df800acb3e0000000000a2c640e4cb6002b2cf80000000002b74e03c249800acb3e0000000007bbd42c66a000acb3e082002080076a710fcdec002b2cf80000000001d3ba02bff8800acb3e00000000007a8bc075bbc002b2cf800000000029fae02fb5f000acb3e00000000007fe390f0e38002b2cf82080082015e6d0b9b24002b2cf80000000001bf7801d24e000acb600be0be0f60be0be0f6060ab5a05a27ff2090de09f8) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P24 : WideCovered band 9352351 9978256 := wide_block_sound band profiles_RelativeWidePack6815_P24 9352351 9978256 (wideData 16 0x2f2bf07ea0b000acb3e0000000000b99a41a68ac002b2cf80000000006ef122d962002b2cf82080082017d46cbdd800acb3e0000000000a6c38176a2a002b2cf800000000028b3b049f1d000acb3e0000000000b78b81a5870002b2d80000000001e8781b58ee002b2cf82080082001eb3944dbfb800acb3e00000000007c9a812bdba002b2cf800000000028ece04c7f8800acb3e0000000000a3e780ea9ec002b2cf80000000002d7bc0597ad800acb3e0000000000eefa117bce6002b2cf82080082001aa3a02ba8a000acb600e40e40f60e40e40f606cb7db06e64ef0091f66dba) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P24 : WideCovered band 9978257 10604161 := wide_block_sound band profiles_RelativeWidePack6815_P24 9978257 10604161 (wideData 16 0x1b5d206299b2002b2cf80000000006db9d17f3e9000acb3e082002080069be13f8b68002b2cf80000000004bb5a0feb18000acb3e00000000012fdb43f2f64002b2cf80000000003ef3f0c925a800acb3e000000000137fb03f2aa8002b2cf80000000005eb53fbeb6002b2cf8208008200292ae08bafb800acb3e0000000000e8bf02b0c3a002b2cf80000000003b3c80ace48000acb3e0000000000e1f70226972002b2cf80000000003f2b80b8f48800acb3e0820020800aa9392a9c3e002b2cf800000000028fda05d27a800acb600ea0ea0f60ea0ea0f60a1a6fe09cbeaa20938ed97e) (by decide +kernel)
private theorem c6 : WideCovered band 10604162 10643280 := wide_block_sound band profiles_RelativeWidePack6815_P24 10604162 10643280 (wideData 1 0xf00f00f60f00f00f60f3fb5d10cb58b2094a73d60) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 5636037 7474634 10643280 c0_RelativeWidePack6815_P24 (wide_covered_join band 7474635 8100539 10643280 c1_RelativeWidePack6815_P24 (wide_covered_join band 8100540 8726445 10643280 c2_RelativeWidePack6815_P24 (wide_covered_join band 8726446 9352350 10643280 c3_RelativeWidePack6815_P24 (wide_covered_join band 9352351 9978256 10643280 c4_RelativeWidePack6815_P24 (wide_covered_join band 9978257 10604161 10643280 c5_RelativeWidePack6815_P24 c6))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 16)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 16≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤43)
    (hT0 : 3474≤T) (hT1 : T≤3903) (hnu : 5636037≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤30411606095906251 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R146

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R147
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨16,44,3402,3815,30005041600743961⟩
private def profiles_RelativeWidePack6815_P24 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨24620,142,5079⟩
  | 3 => ⟨30072,168,5971⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P24 : WideCovered band 5767108 7268529 := wide_block_sound band profiles_RelativeWidePack6815_P24 5767108 7268529 (wideData 16 0x8200208046e81a8b2002b65b80000000011a2c738c800ad96e00000000027ce41830c800ad96e0820020801aeb4183ed800ad96e0000000003b0914bb0002b65b8000000000df2866bd800ad970000000000238d5e8e0002b65b82080082003aa1769f800ad96e000000000376817a78002b65b800000000079f466ec800ad96e000000000161a56c3a002b65b8208008200ad59ff8002b65b8000000000c9f057dd800ad96e1450030c04bde700b9b20d020ad96e2cb00d3400fab018adb824e9af20b40b40f80b40b40f80e3c129e400c9b2cea) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P24 : WideCovered band 7268530 7900706 := wide_block_sound band profiles_RelativeWidePack6815_P24 7268530 7900706 (wideData 16 0x778e16ea8002b65b800000000018a2c019b88000ad96e000000000429941b779800ad96e08200208072fa41dece800ad96e0000000006e49018339000ad96e0000000007e9918bee002b65c0000000000d9350698a4002b65b80000000019eb9072aee002b65b82080082016d787aab800ad96e0000000005a7a018728000ad96e000000000133f5b8f8002b65b800000000158b106cee4002b65b82080082012ebc730a000ad96e000000000523c1efe2002b65b8000000000ba75063aa4002b65b82b82b83e02b82b83e14e29a039b892610dfa1c30) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P24 : WideCovered band 7900707 8532883 := wide_block_sound band profiles_RelativeWidePack6815_P24 7900707 8532883 (wideData 16 0x7d928063cfa002b65b80000000011cfd07acf2002b65b80000000001f33e42e3ff800ad96e08200208072ab01d2b9800ad96e00000000007bef8070f24002b65b8000000000b86d0798be002b65c00000000007ca5068c6e002b65b82080082019cfd0a5f2c002b65b80000000001bf4801aade800ad96e000000000464d01c64a800ad96e000000000768a41f3eb000ad96e082002080470c41b658000ad96e000000000066de4065eea002b65b8000000001dfb806b962002b65b80000000014ff1073ff8002b65b82d82d83e02d82d83e16cebe03e70efe10f9349f2) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P24 : WideCovered band 8532884 9165061 := wide_block_sound band profiles_RelativeWidePack6815_P24 8532884 9165061 (wideData 16 0x1e2cb02aeed000ad96e00000000007fd7006daa0002b65b80000000002af0a02defd000ad96e000000000077c350e8c78002b65b82080082001b69c43a6ae800ad96e000000000077b7407ff38002b65c0000000000283dc0192d8000ad96e000000000077d680ab9e4002b65b80000000001c2fc42f2ba800ad96e08200208006bea50e0a30002b65b80000000001df7d01e219800ad96e0000000000a3e747e2b000ad96e000000000566b028ffc000ad96e000000000071b790b7824002b65c0208008201496d0af9aa002b65b82f02f03e02f02f03e1ba64804cf2d3c110ae6fb4) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P24 : WideCovered band 9165062 9797238 := wide_block_sound band profiles_RelativeWidePack6815_P24 9165062 9797238 (wideData 16 0x7dd6812bc36002b65b80000000002931904b34d000ad96e0000000000a7f700ecdfa002b65b8000000000187b805970b000ad96e0820020800acfa9168ae0002b65b80000000001db8b03b3af800ad97000000000007efe40f29ba002b65b800000000028abb02b65b800ad96e0000000000a4968122d32002b65b80000000002e6e844dbb8800ad96e0820020804ee9039ad8000ad96e00000000007ae680bbd7c002b65b80000000002822901ead9000ad96e0000000000b0bac0e9b34002b65b80000000002963c43ef28800ad96e0e40e40f80e40e40f8062b6ed05e6ddf6111c79d78) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P24 : WideCovered band 9797239 10429415 := wide_block_sound band profiles_RelativeWidePack6815_P24 9797239 10429415 (wideData 16 0xea9b02bab68002b65b80000000003bb880af3dd800ad96e0000000000e487422dda8002b65b800000000099282edea4002b65b82080082017fe022de20002b65b80000000002c7cb07d278800ad9700000000000b78e41f8b66002b65b80000000002c35e05ef1a800ad96e0000000000e8ab0229878002b65b82080082002ea6c488a0a000ad96e0000000000a2aac1738ae002b65b800000000029fab05debc800ad96e0000000000a6a60130a2c002b65b80000000002df6d05ef3a800ad96e0000000007bc846daae000ad96e0ea0ea0f80ea0ea0f807197ce07dacea4112e2cb3a) (by decide +kernel)
private theorem c6 : WideCovered band 10429416 10824525 := wide_block_sound band profiles_RelativeWidePack6815_P24 10429416 10824525 (wideData 10 0x820020802a6ff11ebb67082b65b80000000006eb6919b61c000ad96e08200208007b953df2d000ad96e000000000132da443d8e0002b65b80000000004c7e810bf19000ad96e000000000132e74426cbc002b65b80000000004d72e108ba8000ad96e000000000123d3c333e36002b65b82080082001abaa4e93af000ad96e0ee0ee0f80ee0ee0f80aff2bf0bd68ebe113fbf8fc) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 5767108 7268529 10824525 c0_RelativeWidePack6815_P24 (wide_covered_join band 7268530 7900706 10824525 c1_RelativeWidePack6815_P24 (wide_covered_join band 7900707 8532883 10824525 c2_RelativeWidePack6815_P24 (wide_covered_join band 8532884 9165061 10824525 c3_RelativeWidePack6815_P24 (wide_covered_join band 9165062 9797238 10824525 c4_RelativeWidePack6815_P24 (wide_covered_join band 9797239 10429415 10824525 c5_RelativeWidePack6815_P24 c6))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 16)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 16≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤44)
    (hT0 : 3402≤T) (hT1 : T≤3815) (hnu : 5767108≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤30005041600743961 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R147

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R148
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨16,45,3332,3560,42650136169644217⟩
private def profiles_RelativeWidePack6815_P24 : ℕ → Profile
  | 0 => ⟨16536,4,5080⟩
  | 1 => ⟨24644,140,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P24 : WideCovered band 5898179 7135173 := wide_block_sound band profiles_RelativeWidePack6815_P24 5898179 7135173 (wideData 16 0x12ea1061d38002b7df82080082003fb04bdb800adf7e0000000002a4d18964002b7df80000000006c34573c800adf7e00000000042485ea2c002b7df82080082006ee856df800adf7e00000000022bc12826002b7df8000000000c819cbe002b7df82080082008c3d67e9800adf7e0000000001ad910828002b7df80000000007fa857af800adf7e0000000000ac953be2002b7df82080082004f615bda000adf7e0000000001a78138e4002b7df8d34034d009d3ad02c649fe082b7e802c02c03e82c02c03e83f70073faa00cbbeee6) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P24 : WideCovered band 7135174 7773622 := wide_block_sound band profiles_RelativeWidePack6815_P24 7135174 7773622 (wideData 16 0x208033b941b3d8800adf7e0000030c06bbe419a5b000adf7e08200208033db01832f000adf7e00000000062ce018b3b800adf7e0000000001f3c5bbba002b7df8208008201beed06dff4002b7df8000000000edf44eac800adf7e000000000520d1ffaa002b7df80000000010fb5066d2a002b7df8208008200afa9726a800adf7e00000000036dd1ae3c002b7df8000000000ee2876e8800adf7e000000000377c5bcfe002b7df82080082006df57ede000adf7e0000000002bbf12f3c002b7e802b02b03e82b02b03e8aa75f02f73d7e08dd7dea8) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P24 : WideCovered band 7773623 8412071 := wide_block_sound band profiles_RelativeWidePack6815_P24 7773623 8412071 (wideData 16 0x1fb2d42b3a9800adf7e082000000075a3d079e3c002b7df80000000001b32f019b1c000adf7e00000208006ed2406fb66002b7df80000000005de45eb8000adf7e0820000000bedb10bcd6a002b7df8000000000183af10ff6002b7df80000000001cb3f01a318800adf7e000002080579c41d7ff000adf7e0000030c06af941a2c9800adf7e08200208012dc41c688800adf7e000000000066ce0067c28002b7df8000008201eb5ae74002b7df82080000001ebdd428bae800adf7e000000000565812f28002b7e802d02d03e82d02d03e8aef0c03b73be008ef3ce6a) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P24 : WideCovered band 8412072 9050520 := wide_block_sound band profiles_RelativeWidePack6815_P24 8412072 9050520 (wideData 16 0x1fe8c0296da800adf7e00000208007ebe8060afc002b7df800000c3002ffbf43b278000adf7e08200208067a842c29d000adf7e00000000006d8685a48800adf7e0000000000a6e6807ab24002b7df80000082003be90abdfa002b7df80000000009d39066926002b7df82080000001ef9b42efab800adf7e000000000071f78432b000adf7e0000000000b28f4073ce4002b7df80000082001870f429bdd000adf7e000000000129941868e000adf7e0820000000758bd0b69e2002b7df80000000001e7aa19ca2002b7e802f02f03e82f02f03e89fb080492bda20908fbe2c) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P24 : WideCovered band 9050521 9688969 := wide_block_sound band profiles_RelativeWidePack6815_P24 9050521 9688969 (wideData 16 0x6bf700f5dae002b7df80000000001cb4802c79c800adf7e0000000000aabb1134cb8002b7df8208008200cea40bc830002b7df8000000001f920075df8002b7df80000000001abce02f64c800adf7e000000000077fe80e9aae002b7df8000000000a9ad0a7ab2002b7df82080082001fe6c43c65a800adf7e0000000007b7f019f3d000adf7e00000000006b9a40aac62002b7df80000000001eb0c02d3b8000adf7e0000000000649a8071d30002b7df80000000003db894482ff000adf7e0820020800629b007b8bc002b7e803883883e83883883e8fea7805826f6a091abadee) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P24 : WideCovered band 9688970 10327418 := wide_block_sound band profiles_RelativeWidePack6815_P24 9688970 10327418 (wideData 16 0x1cf7c07cf0d800adf7e00000000037a94886f8800adf7e0820020801b8b04aa5f000adf7e000000000064cb816bc68002b7df800000000018af9048339800adf7e00000000006cb20176df6002b7df80000000001cbba068e5a000adf7e08200208007f9f51369a6002b7df8000000001faec122da8002b7df80000000001839e03d63e800adf7e000000000064fe80f4fbe002b7df80000000001baec04db2c000adf7e0000000005f7803c2bf000adf7e08200208007bc71131a2c002b7df8000000001fba40e9d22002b7e803a03a03e83a03a03e96a28e06af0d7e092c79db0) (by decide +kernel)
private theorem c6 : WideCovered band 10327419 10965867 := wide_block_sound band profiles_RelativeWidePack6815_P24 10327419 10965867 (wideData 16 0x3b6bf16a77d000adf7e0820020801abd5197cb800adf7e00000000007f960325f38002b7df80000000002ab1d0ee6a8800adf7e0000000000a0ba42f6bb4002b7df80000000002b72e0ecfcb000adf7e0820020802b4e4ea3dd800adf7e00000000006d928220836002b7df80000000001dacb0a837d000adf7e000000000078a202a1d7a002b7df80000000001cb7d07f7db000adf7e00000000007eff82adaee002b7df82080082001ab4a47af58000adf7e00000000006a8bc1e49ee002b7df80000000001b2ba079e39800adfa00ee0ee0fa0ee0ee0fa060d22c08ead9ba093e38d72) (by decide +kernel)
private theorem c7 : WideCovered band 10965868 11005770 := wide_block_sound band profiles_RelativeWidePack6815_P24 10965868 11005770 (wideData 1 0xf40f40fa0f40f40fa078fbdb0ef26936094ff7d34) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 5898179 7135173 11005770 c0_RelativeWidePack6815_P24 (wide_covered_join band 7135174 7773622 11005770 c1_RelativeWidePack6815_P24 (wide_covered_join band 7773623 8412071 11005770 c2_RelativeWidePack6815_P24 (wide_covered_join band 8412072 9050520 11005770 c3_RelativeWidePack6815_P24 (wide_covered_join band 9050521 9688969 11005770 c4_RelativeWidePack6815_P24 (wide_covered_join band 9688970 10327418 11005770 c5_RelativeWidePack6815_P24 (wide_covered_join band 10327419 10965867 11005770 c6 c7)))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 16)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 16≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤45)
    (hT0 : 3332≤T) (hT1 : T≤3560) (hnu : 5898179≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤42650136169644217 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R148

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R149
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨16,46,3264,3300,45454847903335488⟩
private def profiles_RelativeWidePack6815_P24 : ℕ → Profile
  | 0 => ⟨8268,2,2540⟩
  | 1 => ⟨2984,24,635⟩
  | 2 => ⟨24724,139,5079⟩
  | 3 => ⟨24644,140,5079⟩
  | 4 => ⟨24703,141,5079⟩
  | 5 => ⟨24620,142,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P24 : WideCovered band 6029250 6996331 := wide_block_sound band profiles_RelativeWidePack6815_P24 6029250 6996331 (wideData 16 0xa2a17b60002bb6b80000000002d286ef8800aedae08200208016aa559e2002bb6b80000000001ba4475a800aedae000000000079d16d76002bb6b80000000002b716ad9800aedae0820020801283aa8800aedae00000000006aa13bb2002bb6c00000000001cb457cc000aedae0820020800bcd56a76002bb6b8000000001ed0ddb8002bb6b830c00c30029f0c44831ce7082bb6b82080082008aa00639abe000aedae0c30030c0371b47b28cab002bb6b830c0082003efee0ce22828084f6cf02a02a03f02902903f0e91cef400c8f5bf4) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P24 : WideCovered band 6996332 7641052 := wide_block_sound band profiles_RelativeWidePack6815_P24 6996332 7641052 (wideData 16 0x2080000001d343b3d800aedae00000000017bf1d932002bb6b80000000009a34066c30002bb6b82080082012cbd06ad2e002bb6b80000000003a24470f800aedae000000000134e1dbf0002bb6b80000000006fa40669fa002bb6b8208008200ea755fbb800aedb00000000000bac18bbe002bb6b80000000003e38764d800aedae0000000001b6941963a000aedae0820020806e03f2a800aedae0000000000acf1883c002bb6b8000000000392472db000aedae0820020801aa95ddb8002bb6b82a82a83f02a82a83f01cb1a02de0fbc10db6fb64) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P24 : WideCovered band 7641053 8285772 := wide_block_sound band profiles_RelativeWidePack6815_P24 7641053 8285772 (wideData 16 0x10928269aa2102bb6b80000000016f604e7d800aedae0000000007aadcf86a002bb6b82080082007c6b069b3a0c2bb6b8000000000aa640f5cf6082bb6b8000000000f92862ff800aedae000000000679c83afbe820aedae0000020800a0b49abf0c2bb6b82080000001a73bc1d6ef000aedae0000000002fb803ef88020aedae0000000004ecc1ef28002bb6b80000082004d7b077dfc002bb6b8208000001ab3f06ebbc002bb6b80000000007d206f3c000aedae00000000033fb0193a8800aedae0b40b40fc0b40b40fc6aa8039a5e6210ed3ad26) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P24 : WideCovered band 8285773 8930493 := wide_block_sound band profiles_RelativeWidePack6815_P24 8285773 8930493 (wideData 16 0x6ab331b9ec00aedae08200208016afc186a8030aedae0000000002f0801af5a800aedae0000000004f7b01ee8f800aedae0000000006769819b0e000aedae0000020800acdb907dd66002bb6b8208000001ca6e0e5ef2002bb6b8000000000dc7c63de000aedb000000000067f815b78002bb6b800000000019799c9d2a002bb6b82080082005a2f06bfe40c2bb6b8000000000beac132cf0082bb6b800000000118b84e89800aedae000000000668e8cca4002bb6b800000000059b195c9e9002bb6b82f02f03f02f02f03f05b3cd848b9fa818ff25ee6) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P24 : WideCovered band 8930494 9575214 := wide_block_sound band profiles_RelativeWidePack6815_P24 8930494 9575214 (wideData 16 0x3bce03bbfc800aedae082002080736a43be9c800aedae0000000001a1c0282bd000aedae0000000001ea91cda0002bb6b8000000000b8b00a6bae002bb6b80000000011a6c0b4920002bb6b800000820028290f5ae0002bb6b82080000019cf5061fa8002bb6c00000000008ba4070c64002bb6b8000000000cc70074ae6002bb6b80000000014e3c179a400aedae00000000067a881c7e8000aedae0000020800e9efd0b5ff0002bb6b82080000001df6d8487af000aedae0000000003abf0cbaf002bb6b83883883f03883883f01ba2904d72e2c1118f18a8) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P24 : WideCovered band 9575215 10219935 := wide_block_sound band profiles_RelativeWidePack6815_P24 9575215 10219935 (wideData 16 0x208008200bea10f4dfc002bb6b800000000059e81219b2002bb6b80000000005ee8125d72002bb6b80000000006de812ceba002bb6b800000000079380e4ee4002bb6b80000000009ee4164ba8002bb6b82080082010ae10f0ae6002bb6b80000000005ab80e7a32002bb6c00000000005ce00a3f7e002bb6b80000000007d3c0f28e4002bb6b80000000009ee412097c002bb6b800000000078e90bcd3c002bb6b82080082005e2d0b1eaa002bb6b800000000068700b28e2002bb6b80000000007d340b8e20002bb6b83a03a03f03a03a03f02df7a05d6de7c112abca6a) (by decide +kernel)
private theorem c6 : WideCovered band 10219936 10864655 := wide_block_sound band profiles_RelativeWidePack6815_P24 10219936 10864655 (wideData 16 0x8ea42aaee0002bb6b80000000007d74222ae6002bb6b80000000009ab02a8ca4002bb6b80000000009e702ace74002bb6b82080082003e352b2b24002bb6b80000000005da4173a3c002bb6b80000000006fe01e7d66002bb6b80000000007aec1eab70002bb6b80000000007f381f08b6002bb6b80000000007c6817adf6002bb6b820800820079251edc6c002bb6b80000000005d64169f72002bb6b80000000005bfc12ce2e002bb6b80000000006b28161c60002bb6b80000000007bb8178c6e002bb6b83b83b83f03b83b83f04927e07beca7a113ca7c2c) (by decide +kernel)
private theorem c7 : WideCovered band 10864656 11187015 := wide_block_sound band profiles_RelativeWidePack6815_P24 10864656 11187015 (wideData 8 0x12a285f4bf4002bb6b8208008200293053ad2a002bb6b8000000000ad203619f2002bb6b8000000000cb343f3864002bb6b8000000000cb383e8cfe002bb6b8000000000be7c37beac002bb6b8000000000be78368bfe002bb6b83d03d03f03d03d03f06da1d0babbe2c114e72dec) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6029250 6996331 11187015 c0_RelativeWidePack6815_P24 (wide_covered_join band 6996332 7641052 11187015 c1_RelativeWidePack6815_P24 (wide_covered_join band 7641053 8285772 11187015 c2_RelativeWidePack6815_P24 (wide_covered_join band 8285773 8930493 11187015 c3_RelativeWidePack6815_P24 (wide_covered_join band 8930494 9575214 11187015 c4_RelativeWidePack6815_P24 (wide_covered_join band 9575215 10219935 11187015 c5_RelativeWidePack6815_P24 (wide_covered_join band 10219936 10864655 11187015 c6 c7)))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 16)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 16≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤46)
    (hT0 : 3264≤T) (hT1 : T≤3300) (hnu : 6029250≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤45454847903335488 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R149
end MergedPart0
section MergedPart1
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R150
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨17,18,4257,4372,1424574087666458⟩
private def profiles_RelativeWidePack6815_P25 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P25 : WideCovered band 2359261 6293400 := wide_block_sound band profiles_RelativeWidePack6815_P25 2359261 6293400 (wideData 1 0x2082982082999b15a7200c823e70) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := c0_RelativeWidePack6815_P25
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 17)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 17≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤18)
    (hT0 : 4257≤T) (hT1 : T≤4372) (hnu : 2359261≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤1424574087666458 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R150

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R151
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨18,18,3938,4249,726207447517077⟩
private def profiles_RelativeWidePack6815_P25 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P25 : WideCovered band 2359260 6474645 := wide_block_sound band profiles_RelativeWidePack6815_P25 2359260 6474645 (wideData 3 0x13c672003f72f7a0000000005f83ec001fb9bbc0820a80820a8068d12ff0006bb9b34) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := c0_RelativeWidePack6815_P25
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 18)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 18≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤18)
    (hT0 : 3938≤T) (hT1 : T≤4249) (hnu : 2359260≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤726207447517077 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R151

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R152
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨18,19,3806,4199,1445814988581091⟩
private def profiles_RelativeWidePack6815_P25 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P25 : WideCovered band 2490331 6655890 := wide_block_sound band profiles_RelativeWidePack6815_P25 2490331 6655890 (wideData 1 0xaa0aa0aa0aa0aa0aa0b7e13ee600cda7e64) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := c0_RelativeWidePack6815_P25
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 18)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 18≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤19)
    (hT0 : 3806≤T) (hT1 : T≤4199) (hnu : 2490331≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤1445814988581091 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R152

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R153
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨18,19,4200,4250,1462590739470564⟩
private def profiles_RelativeWidePack6815_P25 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P25 : WideCovered band 2490331 6655890 := wide_block_sound band profiles_RelativeWidePack6815_P25 2490331 6655890 (wideData 1 0x2082a82082a8b9159e600cda7e64) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := c0_RelativeWidePack6815_P25
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 18)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 18≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤19)
    (hT0 : 4200≤T) (hT1 : T≤4250) (hnu : 2490331≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤1462590739470564 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R153

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R154
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨19,19,3536,3730,5361476641883917⟩
private def profiles_RelativeWidePack6815_P25 : ℕ → Profile
  | 0 => ⟨8268,2,2540⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P25 : WideCovered band 2490330 6837135 := wide_block_sound band profiles_RelativeWidePack6815_P25 2490330 6837135 (wideData 1 0xac0ac0ac0ac0ac0ac07da1edbc00d869e3e) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := c0_RelativeWidePack6815_P25
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 19)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 19≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤19)
    (hT0 : 3536≤T) (hT1 : T≤3730) (hnu : 2490330≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤5361476641883917 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R154

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R155
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨19,20,3423,3529,8208778260150074⟩
private def profiles_RelativeWidePack6815_P25 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨27543,195,5971⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P25 : WideCovered band 2621401 7018380 := wide_block_sound band profiles_RelativeWidePack6815_P25 2621401 7018380 (wideData 16 0x2080082013917d32c800a38be000000000069fe44ed8e80028e2f80000000001abe813d39b000a38be000000000724e148add800a38e0082002080360a0dfb5c000a38be0000000007a4c0debad000a38e00000000007bdb0e879d000a38be00000000006082c3ad96c0028e3802080082007a4b8b08800a38be0000000005fea0b87a9800a38be00000000063cc0bb7be800a38be2cb00b2c0522c282e0a33c820a38e00000000007e0062cae088b2bf00000000008e00001871bee0ac0ac002b02b0070bb800a38bee82082b82082b96b128220099a5ee4) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := c0_RelativeWidePack6815_P25
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 19)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 19≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤20)
    (hT0 : 3423≤T) (hT1 : T≤3529) (hnu : 2621401≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤8208778260150074 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R155
end MergedPart1
section MergedPart2
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R156
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨7,68,4061,4062,15999661226366636⟩
private def profiles_RelativeWidePack6815_P26 : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨44768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P26 : WideCovered band 8912821 9889542 := wide_block_sound band profiles_RelativeWidePack6815_P26 8912821 9889542 (wideData 16 0x603e6e800a6d3e0000000000603b2d000a6d3e00000000006837ac800a6d3e00000000006c33aa000a6d3c00000000007c2f1a800a6d3e0000000000a4279f000a6d3e0000000000b01e9f800a6d3e0000000000f80ed8800a6d3e0000000001640e2b400a6d3e00000000022c3ee9c00a6d3e20828820a325b56c7ee7d0829b4f80000000007be43e4ff390012da7a0000000003a9e5de619e5004b69f0000000000fe34060bb5af8008eb3e02080082001c640e8f3a98023acf60be0be12c0be0be12c0e4d06cbbdaa011a3abe0) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P26 : WideCovered band 9889543 10468339 := wide_block_sound band profiles_RelativeWidePack6815_P26 9889543 10468339 (wideData 16 0x61c9ba0029b4f80000000018733b800a6d3e000000000060764d800a6d3e08200208006d6e68000a6d3c000000000616cb80029b4f800000000185b2a800a6d3e000000000616cee0029b4f800000000185b5f800a6d3e000000000616e760029b4f80000000001816ff80029b4f8000000001c5e9b000a6d3e0000000000685f5d800a6d3c0820020800a956b9800a6d3e000000000610d280029b4f80000000018427d800a6d3e0e80e81360e80e81360abd059e39b2092f7a968) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P26 : WideCovered band 10468340 11445060 := wide_block_sound band profiles_RelativeWidePack6815_P26 10468340 11445060 (wideData 16 0x2902bbfc8012da7c0000000000ac0accea004b69f00000000002c02aa7e8012da7c0000000000b80a7d32004b69e82080082001d428fed8012da7c0000000000a8068ff6004b69e80000000002c1dff8004b69f00000000003a0cdec004b69e80000000004b11f6f004b69f030c00c3004de31f5869004b69f08200208004e7a06aba0f0012da7c08200208075fb700029b4f000000000186ebe000a6d3e00000000061bbea0029b4f800000000146f4e800a6d3e0ec0ec1360ec0ec1360b3e05cbdda2094864d24) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P26 : WideCovered band 11445061 12602655 := wide_block_sound band profiles_RelativeWidePack6815_P26 11445061 12602655 (wideData 16 0xf81a9ea2004b69f00000000003b069ebb8012da7c0000000000f41a68a6004b69f02080082001e05b71a0012da7a0000000000e01638bc004b69f000000000038058a3e8012da7a0000000000e4162a34004b69f02080082001904a36f0012da7a0000000000b012486e004b69f00000000002d048f7f0012da7c0000000000bc124c38004b69f020800820100eee70004b69e80000000002a03a65b0012da7c0000000000b00e8cb6004b69f00000000002c03a3ce8012da7c0f80f81360f80f81360ec907a7acb0095fbefa2) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P26 : WideCovered band 12602656 13543200 := wide_block_sound band profiles_RelativeWidePack6815_P26 12602656 13543200 (wideData 13 0x22c423c30004b69e82080082006d0f8bb88012da7c0000000001b833eaea004b69e80000000006d0cbec90012da7c0000000001ac322cb8004b69e82080082004d0ad7af0012da7c00000000016427bce8004b69f00000000005a09cf9a8012da7c0820020800f82699a8004b69e80000000004b07f67a0012da7c0000000001281f88f8004b69f00000000004907d2cc0012da7c120120136120120136135a09da68b0098973ef8) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8912821 9889542 13543200 c0_RelativeWidePack6815_P26 (wide_covered_join band 9889543 10468339 13543200 c1_RelativeWidePack6815_P26 (wide_covered_join band 10468340 11445060 13543200 c2_RelativeWidePack6815_P26 (wide_covered_join band 11445061 12602655 13543200 c3_RelativeWidePack6815_P26 c4_RelativeWidePack6815_P26))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 7)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 7≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤68)
    (hT0 : 4061≤T) (hT1 : T≤4062) (hnu : 8912821≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤15999661226366636 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R156

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R157
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨7,69,4006,4028,19715458798791055⟩
private def profiles_RelativeWidePack6815_P26 : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨45018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P26 : WideCovered band 9043892 9811796 := wide_block_sound band profiles_RelativeWidePack6815_P26 9043892 9811796 (wideData 16 0xb9d078ae0029edb80000000003ff82bcec00a7b6e0000000001b4b06f230029edb8000000000ceec7b5a400a7b6e1040041007a9b49ef2f000a7b6e0000000002f813fe80063db600000000036c1e0a80063db60000000003ac1bc980063db60000000003f41b8980063db80000000004601b3980063db618630618c3f0cbd06cc7cd7d0818f6e00000000008e2ed19c38ff80029edb80000000004a22d0cb278f2004bbaf00000000008ff3f5af66c3d004bbaf00000000009cbb81caaddbe008f75d83803804b03803804b03aada0a8e0ea4011c3dc3e) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P26 : WideCovered band 9811797 10396865 := wide_block_sound band profiles_RelativeWidePack6815_P26 9811797 10396865 (wideData 16 0x13819fb60029edb80000000012913dfe0029edb80000000015f1ab740029edb8000000001891affe0029edb82080082001ab96789800a7b6e0000000003b837cd800a7b6c00000000047c4eae000a7b6e0000000004ec4e3f000a7b6e0000000005684bd9800a7b6e0000000005602e0e000a7b6c0000000006ac47ae800a7b6e0000000007a846ed800a7b6e000000000063a10fe80029edb800000000019e016da000a7b6c00000000007480eaba0029edb83a83a84e03a83a84e01b7dc0596ae66092e638b6) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P26 : WideCovered band 10396866 11091634 := wide_block_sound band profiles_RelativeWidePack6815_P26 10396866 11091634 (wideData 16 0xb1b07cb1004bbae8000000000496c169a4012eebc186006180771062c3de8012eebc000000000530065ebc0029edb82080082011e5f9a00029edb8000000000eb19bbe0029edb00000000010e1ed600029edb80000000011b1efa60029edb8000000001291fab20029edb80000000011919eb60029edb000000000149018258000a7b6e000000000064060f2e0029edb82080082008859f200029edb8000000000eb1497a0029edb00000000010e19c320029edb83b03b04e03b03b04e01e2cf05bbbda0093f39e70) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P26 : WideCovered band 11091635 12261773 := wide_block_sound band profiles_RelativeWidePack6815_P26 11091635 12261773 (wideData 16 0x7ae04a24e8012eeba0000000000a2e04ee7d8012eebc00000000007de049a4e8012eebc0820020805ec12fd6c004bbaf00000000001ce00eacb0004bbae80000000001ef40fdb2c004bbaf00000000001dfc0e897e004bbaf02080082009e03eb1e0012eebc00000000006da02bb9f0012eeba000000000076f0383880012eebc000000000074c02a3588012eebc0000000000a3a02fbd88012eebc000000000076e0287ef8012eeba082002080060a4283ba8012eebc000000000073c1ecbc004bbae83d83d84e03d83d84e02930d06f6bbfe095a6e9a0) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P26 : WideCovered band 12261774 13431911 := wide_block_sound band profiles_RelativeWidePack6815_P26 12261774 13431911 (wideData 16 0x4ee0365b32004bbae82080082003ca03208b4004bbaf00000000003fac2b4e38004bbaf000000000049a42e9bac004bbaf02080082002da026ceaa004bbae80000000003bbc268a32004bbaf00000000003930227c70004bbae80000000003b6023dc20004bbaf02080082001e301bbd2e004bbae80000000002ebc1eba7e004bbaf00000000002cbc1b0e66004bbaf02080082001e6c1bef62004bbaf0000000000296416ba22004bbae80000000002b3c17eba8004bbaf000000000029ac167c6a004bbae83f83f84e03f83f84e02ee0808cb8a64097c3bcf6) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P26 : WideCovered band 13431912 13724445 := wide_block_sound band profiles_RelativeWidePack6815_P26 13431912 13724445 (wideData 4 0x6bf447f8b6004bbae82080082005b7046bbe0004bbaf000000000059a43a8d3e004bbae84984984e04984984e04b6ca0d8389f2099e2986a) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 9043892 9811796 13724445 c0_RelativeWidePack6815_P26 (wide_covered_join band 9811797 10396865 13724445 c1_RelativeWidePack6815_P26 (wide_covered_join band 10396866 11091634 13724445 c2_RelativeWidePack6815_P26 (wide_covered_join band 11091635 12261773 13724445 c3_RelativeWidePack6815_P26 (wide_covered_join band 12261774 13431911 13724445 c4_RelativeWidePack6815_P26 c5_RelativeWidePack6815_P26)))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 7)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 7≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤69)
    (hT0 : 4006≤T) (hT1 : T≤4028) (hnu : 9043892≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤19715458798791055 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R157

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R158
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨7,70,3952,3993,15543604759030708⟩
private def profiles_RelativeWidePack6815_P26 : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨45018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P26 : WideCovered band 9174963 9803262 := wide_block_sound band profiles_RelativeWidePack6815_P26 9174963 9803262 (wideData 16 0x17b907cbc002a25f80000000008b7c568bc00a897c0000000003b5f13e29002a25f841001040019a9949f21b000a897e000000000530174d000648be0000000005f8227c800648e00000000006201a1d800648be00000000066c161f800648be0000000006f4137a800648be0000000007f41e0a800648e0000000000062805eb6001922f8618e186394f6af5fcbd9ad08192380000000000acafc10a7ef24002a25f80000000006a6dc09db0a2c004c2be8000000000aba8d50d3df2f004c2bf03803804b03803804b1192081b83d9f8011e60cbc) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P26 : WideCovered band 9803263 10394603 := wide_block_sound band profiles_RelativeWidePack6815_P26 9803263 10394603 (wideData 16 0x19346b9a000a897e000000000063b14cfc002a25f00000000001ab46ede800a897e00000000006ab14da0002a25f80000000014d1cce8002a25f820800820029e5426d000a897c000000000062f149a8002a25f8000000000187c36bc800a897e000000000069b13caa002a25f80000000001a742f58000a897c000000000073e12d38002a25f80000000001dac266c800a897e0000000000a5f119bc002a25f80000000002ba0168a800a897e0000000000e8d0eb66002a25f83a83a84e83a83a84e82d3af058f4966092e3397a) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P26 : WideCovered band 10394604 11096821 := wide_block_sound band profiles_RelativeWidePack6815_P26 10394604 11096821 (wideData 16 0x13cd01869004c2bf000000000078f806f9ed004c2bf06180186004f4193da6c004c2be800000000018f4060e7a002a25f8208008201ee418e19800a897e0000000006fc6aac800a897c00000000006091fca0002a25f8000000001ea1ab6c002a25f800000000018bc06096a002a25f800000000018606b7f000a897c000000000066f01864d000a897e000000000065b1bba0002a25f82080082001ce17788800a897e0000000006f4560c800a897e000000000060d1ab76002a25f83b03b04e83b03b04e83a62e05b36e6c093f36934) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P26 : WideCovered band 11096822 12279503 := wide_block_sound band profiles_RelativeWidePack6815_P26 11096822 12279503 (wideData 16 0x2080082001c6c1329f0004c2bf00000000003d7c12f8f0004c2bf00000000003e7012ebfa004c2be80000000003da412f87a004c2bf0208008201cd03cedd00130afa0000000000e8b03c3af80130afc0000000000ede03c20a00130afa0000000000f6903c22a00130afc0820020802310e0864004c2bf00000000002fbc0b3a78004c2bf000000000039bc0b0a38004c2be80000000003cec0ad96a004c2bf000000000049bc0a9bfc004c2be82080082002d610a1b60004c2bf000000000039640668aa004c2be83d83d84e83d83d84e8482ff06ef7fbe095a79ee6) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P26 : WideCovered band 12279504 13462185 := wide_block_sound band profiles_RelativeWidePack6815_P26 12279504 13462185 (wideData 16 0x9cf837d8b0004c2bf0208008200792c332ab6004c2bf00000000007eb42e7cb4004c2be80000000007d3c2bcce2004c2bf00000000007c342b3cfa004c2be82080082004da423dca0004c2bf000000000069b8235bbc004c2be8000000000693c230866004c2bf0208008200482c1fbd7e004c2bf000000000058f81bfb72004c2bf000000000058e81bbeae004c2be8000000000592c1b9dba004c2bf02080082002d2417e832004c2be80000000004a60172ba8004c2bf00000000004ab8170f20004c2be83f83f84e83f83f84e85ae5a08c6dc6a097c7fe3a) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P26 : WideCovered band 13462186 13905690 := wide_block_sound band profiles_RelativeWidePack6815_P26 13462186 13905690 (wideData 6 0x208008200e9ac5f08ac004c2be8000000000dda8527b3e004c2bf0000000000cff84e3ea0004c2be8000000000cb384a5af2004c2bf02080082008eec3e993c004c2be84984984e84984984e88b31a0d8b8ee0099ea5dae) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 9174963 9803262 13905690 c0_RelativeWidePack6815_P26 (wide_covered_join band 9803263 10394603 13905690 c1_RelativeWidePack6815_P26 (wide_covered_join band 10394604 11096821 13905690 c2_RelativeWidePack6815_P26 (wide_covered_join band 11096822 12279503 13905690 c3_RelativeWidePack6815_P26 (wide_covered_join band 12279504 13462185 13905690 c4_RelativeWidePack6815_P26 c5_RelativeWidePack6815_P26)))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 7)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 7≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤70)
    (hT0 : 3952≤T) (hT1 : T≤3993) (hnu : 9174963≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤15543604759030708 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R158

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R159
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨7,71,3900,3956,20579247171543260⟩
private def profiles_RelativeWidePack6815_P26 : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨45268,250,10158⟩
  | 2 => ⟨27328,144,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P26 : WideCovered band 9306034 9735568 := wide_block_sound band profiles_RelativeWidePack6815_P26 9306034 9735568 (wideData 16 0x6dd04fb400192f980000000001ce8177e00064be600000000007aa07ab200192fa00000000001f68078b80064be60000000000a9b06d2e00192fa00000000002d201aba00064be60000000000bcb15d40064be80000000000f1f058a200192f9800000000048bc0f8e40064be6000000000165e02d2600192f980000000006c20066a80064be800000000022790cdbb00192f988210208415f6dc56af6b7b08192fa00000000009b65c0abf4bf8002a3eb80000000006da4b07bb1970004c7cf03803804b03803804b089e49099f5ee2011f31dfe) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P26 : WideCovered band 9735569 10277155 := wide_block_sound band profiles_RelativeWidePack6815_P26 9735569 10277155 (wideData 16 0x78e0fd64002a3eb80000000001fbc3b88000a8fae0000000000aec16c62002a3eb00000000002ce03649000a8fae0000000000e290bc6e002a3eb80000000003de826ba000a8fae000000000160b14966002a3eb800000000069e8122c000a8fae000000000237a02b79002a3eb8000000000dab83a8c400a8fae0000000005f6f0b9ab002a3eb00000000001d31d02d60ac00a8fae1040041000eee3533483e002a3eb80000000001970224f00064be600000000006590486c00192fa03a03a04f03a03a04f03e30904ee5bb4092ceba26) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P26 : WideCovered band 10277156 10874768 := wide_block_sound band profiles_RelativeWidePack6815_P26 10277156 10874768 (wideData 16 0x6fa1e830002a3eb80000000001cf0060a68002a3eb80000000001e2c0638ea002a3eb02080082001ff177dd800a8fae0000000000688188b2002a3eb80000000001a785fdf800a8fae00000000007181ddfc002a3eb80000000001bb86209000a8fae000000000071d17fba002a3eb80000000001d6c5fef800a8fae0000000000a081faf0002a3eb00000000001ffc6349000a8fae0820020800fac55aa4002a3eb80000000001af84698800a8fae000000000074e17aaa002a3eb03b03b04f03b03b04f04aba805a34b2e093d71c34) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P26 : WideCovered band 10874769 11920590 := wide_block_sound band profiles_RelativeWidePack6815_P26 10874769 11920590 (wideData 16 0x2080082016c03fa0900131f3c0000000000ffc02ceda80131f3c00000000013bc039b4d80131f3c000000000135b02afb980131f3a0000000001a19038f7a00131f3c0820020800bfc41ffdc00131f3a000000000135d01ff9c00131f3c000000000135c19b62004c7ce80000000006d20067b6c004c7cf00000000007f30728f40131f3a000000000376a01a6dbc0131f3c20800820023cc419f0bbc004c7ce80000000001a3c7719800a8fae00000000006dd01874b000a8fae00000000006ce1f830002a3eb03c03c04f03c03c04f04ee1c05d7d9ac094ea0dee) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P26 : WideCovered band 11920591 13115816 := wide_block_sound band profiles_RelativeWidePack6815_P26 11920591 13115816 (wideData 16 0x9b2026ccf8004c7cf02080082005be01fcc6a004c7cf000000000088741ffff6004c7cf00000000007bb81e7a3e004c7ce820800820059f41f58be004c7cf0000000000697c17cd20004c7ce80000000006eec1b0faa004c7cf00000000006a3c177be4004c7ce82080082003ba417dd36004c7cf000000000059b0134aa4004c7cf00000000005f68168dbe004c7cf00000000005be8131c30004c7ce82080082001ff81378bc004c7cf00000000004bf80f2eb2004c7ce80000000005a3412783e004c7cf03f03f04f03f03f04f06ca1807dbe924096f24a76) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P26 : WideCovered band 13115817 14086935 := wide_block_sound band profiles_RelativeWidePack6815_P26 13115817 14086935 (wideData 13 0xe38038e002e64807ee2bf0084c7ce80000000015c605e0f6a004c7cf00000000015de05e792c004c7ce8208008201093c4f4ee4004c7cf000000000118f44a5e68004c7ce8000000000f9b442087a004c7cf0000000000fdf8432868004c7ce8208008200a8b833e826004c7cf0000000000cdfc369c60004c7ce8000000000bbb42f9b32004c7cf020800820098a02f8b7c004c7ce80000000009af42719aa004c7cf04904904f04904904f09cade0af20db0099962dea) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 9306034 9735568 14086935 c0_RelativeWidePack6815_P26 (wide_covered_join band 9735569 10277155 14086935 c1_RelativeWidePack6815_P26 (wide_covered_join band 10277156 10874768 14086935 c2_RelativeWidePack6815_P26 (wide_covered_join band 10874769 11920590 14086935 c3_RelativeWidePack6815_P26 (wide_covered_join band 11920591 13115816 14086935 c4_RelativeWidePack6815_P26 c5_RelativeWidePack6815_P26)))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 7)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 7≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤71)
    (hT0 : 3900≤T) (hT1 : T≤3956) (hnu : 9306034≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤20579247171543260 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R159

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R160
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨8,59,4251,4260,9462236964409540⟩
private def profiles_RelativeWidePack6815_P26 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨43018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P26 : WideCovered band 7733181 9572581 := wide_block_sound band profiles_RelativeWidePack6815_P26 7733181 9572581 (wideData 16 0x17c66cf800a2c3e0000000001a0678c800a2c3e0000000001b06a78000a2c3e0000000001b86b98000a2c3e0000000001e86eef800a2c3e0820020802b16e79000a2c3e00000000016c5658800a2c3e000000000170569e800a2c3e0000000001a056fd000a2c3e0000000001ac5789800a2c3e0000000001bc5a3b000a2c3e0000000001ec5b28800a2c3e1c7005140532e059f3fb80828b0f82080000002a1aa3e0828b0f8924024900180d924090d27c03b03b04983b03b04982c15ca2010eb0e76) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P26 : WideCovered band 9572582 10458218 := wide_block_sound band profiles_RelativeWidePack6815_P26 9572582 10458218 (wideData 16 0x820020802750a6cfa004961f00000000011e01f66f8012587c00000000052407a8b2004961f00000000017f01da398012587c0000000007ac070c2c004961f00000000001aa0067c64004961f000000000028f857a88012587c00000000012cc19df5004961f0000000001197a267ce7004961e8820020801792f069fecd8012587c0000000001a87a79000a2c3e0000000001b87b8f800a2c3e0000000001bc7e49000a2c3e0820020801f56f0c000a2c3e0000000001645e5a000a2c3e0e20e21260e20e21265b9a05ceab7c192aaafe8) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P26 : WideCovered band 10458219 11548233 := wide_block_sound band profiles_RelativeWidePack6815_P26 10458219 11548233 (wideData 16 0x670163c7c004961f00000000019e058ee98012587c0000000006b0164b64004961f02080082009c049f3c0012587c0000000005a0126c7e004961f00000000016d049e490012587c0000000005f8128e7a004961f02080082004f03c3088012587c0000000004f40ee978004961e80000000014c03bbab8012587c0000000005340e8a7c004961f0208008200d0b7d60004961f00000000011c02db8c8012587c0000000004b80b6b3c004961f00000000014b02db8a0012587c0ee0ee1260ee0ee12672ff079719b81948afa30) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P26 : WideCovered band 11548234 12093240 := wide_block_sound band profiles_RelativeWidePack6815_P26 11548234 12093240 (wideData 8 0x19241f8b72004961e800000000018b81ece22004961f000000000018741e1ab4004961f02080082015a06d2fa0012587c0000000007a01a88a6004961f0000000001e8069b2f8012587c0000000007ac1a69fe004961f03d83d84983d83d849819748098f48ac1969609ae) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7733181 9572581 12093240 c0_RelativeWidePack6815_P26 (wide_covered_join band 9572582 10458218 12093240 c1_RelativeWidePack6815_P26 (wide_covered_join band 10458219 11548233 12093240 c2_RelativeWidePack6815_P26 c3_RelativeWidePack6815_P26)))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 8)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 8≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤59)
    (hT0 : 4251≤T) (hT1 : T≤4260) (hnu : 7733181≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤9462236964409540 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R160

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R161
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨8,60,4186,4231,9776950651964709⟩
private def profiles_RelativeWidePack6815_P26 : ℕ → Profile
  | 0 => ⟨16536,4,5080⟩
  | 1 => ⟨2984,24,635⟩
  | 2 => ⟨43268,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P26 : WideCovered band 7864252 9552544 := wide_block_sound band profiles_RelativeWidePack6815_P26 7864252 9552544 (wideData 16 0x770621f800a3a6e0000000007e062bc800a3a6c0000000007fc5e2b800a3a6e000000000060d14f2a0028e9b80000000001978672c000a3a6e000000000069b1aab80028e9b80000000001a38521f000a3a6e0820020800b3958d240028e9b8000000001ee13e760028e9b800000000018604fea000a3a6e00000000006080de3e0028e9b800000000019e85218800a3a6e0820020801e6bb12afaaccc20a3a6e0000000000fcc2c177de4f00126cbc1c70071c01afde827cb3ba02126cbc0e40e41280e40e41287b807caaa0118e9a74) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P26 : WideCovered band 9552545 10207188 := wide_block_sound band profiles_RelativeWidePack6815_P26 9552545 10207188 (wideData 16 0x3d3407aa00126cbc000000000174f0ba340049b2f06180186002c687b8cac0049b2e800000000018680619720028e9b8000000001fa1cae20028e9b800000000019280629680028e9b80000000003b418e5d000a3a6e0820020800b4726f800a3a6e0000000006a85e3b000a3a6e0000000007b4729c800a3a6e0000000007fc737b000a3a6e0000000007ec678d800a3a6e000000000061f1bc720028e9b800000000019747af8000a3a6e08200208006de5f9b60028e9b83883884a03883884a03c39d05befba0112a64cee) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P26 : WideCovered band 10207189 11309747 := wide_block_sound band profiles_RelativeWidePack6815_P26 10207189 11309747 (wideData 16 0x82002080065d03f6cc00126cbc0000000000efa048b4c00126cbc0000000000e6b03beff00126cba0000000000eef03d6e800126cbc08200208066c0f8db80049b2f00000000002de80b7bbe0049b2f00000000003a380eab760049b2f000000000038e00b696a0049b2f00000000003f240ee8e80049b2f020800820019710a5c300049b2f000000000038a00b1da00049b2f00000000002fbc07acf80049b2f00000000003b2c07593e0049b2f00000000004db40ae87e0049b2f00000000005ba0069fbc0049b2f03b83b84a03b83b84a03fb2806eecbb8113ce6c24) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P26 : WideCovered band 11309748 12274485 := wide_block_sound band profiles_RelativeWidePack6815_P26 11309748 12274485 (wideData 14 0x68ec2298720049b2e80000000006ae8232ff80049b2f02080082004b68223b760049b2f000000000058341b5fb40049b2f00000000005bf41eaaaa0049b2f000000000058301b0d6a0049b2f02080082003b381b7e760049b2f0000000000497416bea40049b2f00000000004d6417fef40049b2e80000000004a3c169f6e0049b2f02080082001fec13aca00049b2f00000000003fb813eabe0049b2f00000000003d2012a8f00049b2f03d03d04a03d03d04a05ba6c08aef8fe115daffa2) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7864252 9552544 12274485 c0_RelativeWidePack6815_P26 (wide_covered_join band 9552545 10207188 12274485 c1_RelativeWidePack6815_P26 (wide_covered_join band 10207189 11309747 12274485 c2_RelativeWidePack6815_P26 c3_RelativeWidePack6815_P26)))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 8)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 8≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤60)
    (hT0 : 4186≤T) (hT1 : T≤4231) (hnu : 7864252≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤9776950651964709 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R161
end MergedPart2
section MergedPart3
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R162
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨8,61,4122,4202,16497012708230383⟩
private def profiles_RelativeWidePack6815_P27 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨33072,8,10160⟩
  | 2 => ⟨2984,24,635⟩
  | 3 => ⟨43518,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P27 : WideCovered band 7995323 9493741 := wide_block_sound band profiles_RelativeWidePack6815_P27 7995323 9493741 (wideData 16 0x78f16d30002921f80000000001d7c461f800a487e0000000000a1817860002921f80000000001fe843cd800a487e0000000000adb17d7a002921f80000000002b7043bd000a487e0000000000baa12fba002921f80000000003af45bfe000a487e104004100072825a41a3f8f9e420a487e000000000063fef81deaeff8004a23f00000000007b758068aadaa004a23e820800820038ecf02dadd3c004a23f00000000001f7ce01cb48b4004a23f071c01c700782c905eeee2c084a23f030c00c3001e7c0ba96a09182fc03903904a83903904a95b1586a010aa0eb2) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P27 : WideCovered band 9493742 10051292 := wide_block_sound band profiles_RelativeWidePack6815_P27 9493742 10051292 (wideData 16 0x71f1a860002921f80000000001e747e8f000a487e000000000075d1ab36002921f80000000001fb006096e002921f80000000001ebc6e2b000a487e0000000000a590186fb800a487e0000000000a291c96e002921f82080082002ea56bbe000a487e000000000074c18c6c002921f80000000001cec579c000a487e00000000007cf1bc64002921f80000000001e785a4d800a487c0000000000a4f1cc7e002921f800000000028b45b9e800a487e0000000000b0d1e97a002921f83903904a83903904a85feb905aede3e192972c38) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P27 : WideCovered band 10051293 11061853 := wide_block_sound band profiles_RelativeWidePack6815_P27 10051293 11061853 (wideData 16 0x1a4903ab8f801288fc0000000001b4c03afff801288fc0820020805310bfc22004a23f00000000005a6c0b19fa004a23f00000000005e340afda6004a23e80000000006bec0aeb68004a23f00000000007ce00adca8004a23f02080082004e290a4be4004a23f00000000005d3c06e9ac004a23f00000000006dec065878004a23f0000000000893026df801288fc0000000002e380193ec401288fc186006180068801865cea004a23e800000000028f8065bfc002921f80000000001ffc060b2c002921f83a03a04a83a03a04a86d72d05e69ebe1939f3bf6) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P27 : WideCovered band 11061854 12176955 := wide_block_sound band profiles_RelativeWidePack6815_P27 11061854 12176955 (wideData 16 0xac201f886c004a23f0000000000ac381f5cf6004a23f02080082005e341b1b7e004a23f00000000008e241aa8a2004a23f00000000008ea41a8cee004a23e82080082005abc1a5f6c004a23f00000000007af4165a70004a23f00000000007bb4164a20004a23f00000000007cf81649e0004a23f02080082003cf4160a70004a23f00000000006ae0126a60004a23f00000000006c24125e6a004a23f000000000068680f2df4004a23e80000000006c7c125a60004a23f020800820019e40edabc004a23f03c83c84a83c83c84a8983ba07defaee1959eda76) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P27 : WideCovered band 12176956 12455730 := wide_block_sound band profiles_RelativeWidePack6815_P27 12176956 12455730 (wideData 4 0xcf3427996a004a23e8000000000c924262be6004a23f02080082007fb82269fe004a23f03e83e84a83e83e84a8cc7ac0ac22b24197aef9f2) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7995323 9493741 12455730 c0_RelativeWidePack6815_P27 (wide_covered_join band 9493742 10051292 12455730 c1_RelativeWidePack6815_P27 (wide_covered_join band 10051293 11061853 12455730 c2_RelativeWidePack6815_P27 (wide_covered_join band 11061854 12176955 12455730 c3_RelativeWidePack6815_P27 c4_RelativeWidePack6815_P27))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 8)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 8≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤61)
    (hT0 : 4122≤T) (hT1 : T≤4202) (hnu : 7995323≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤16497012708230383 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R162

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R163
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨8,62,4060,4172,18813173729294498⟩
private def profiles_RelativeWidePack6815_P27 : ℕ → Profile
  | 0 => ⟨33072,8,10160⟩
  | 1 => ⟨2984,24,635⟩
  | 2 => ⟨43768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P27 : WideCovered band 8126394 9465473 := wide_block_sound band profiles_RelativeWidePack6815_P27 8126394 9465473 (wideData 16 0x4a2453fd800a4eae0000000001ee855ae600293ab82080082014c10cfc00293ab8000000000397c4b5a800a4eae0000000000e8e0d8b600293ab80000000003d7c326f800a4eae000000000127d0b96000293ab00000000005b7c4f1a800a4eae0000000001a18098fe00293ab84100104016870d4ca728b308293ab8000000000cd62c07b3e93c004a74f020800820049b0802cad9ec004a74f00000000002d69b01c61ef4004a74f030c00c30029e4a3106e87fbed004a74f030c00c3002c3f8f0073ee4fbc088ce9e03803804b03803804b03bb00ee8bc010cad8b0) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P27 : WideCovered band 9465474 10029296 := wide_block_sound band profiles_RelativeWidePack6815_P27 9465474 10029296 (wideData 16 0x2080082003921063eec00293ab80000000002a646388000a4eae0000000000ac918ea600293ab80000000002bf863eb000a4eae0000000000b881bbee00293ab80000000002fe8767d000a4eae0000000000bfd1a87e00293ab000000000039e06b1e000a4eae000000000162f5b9a800293ab82080082002c38671d000a4eae0000000000aeb1496600293ab80000000002cf8522f800a4eae0000000000ba91487c00293ab80000000003878521b000a4eae0000000000f7a1bba600293ab83903904b03903904b08a36d05a329b81128fc8b0) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P27 : WideCovered band 10029297 10945507 := wide_block_sound band profiles_RelativeWidePack6815_P27 10029297 10945507 (wideData 16 0x231e02b3ab00129d3a0000000002e3d039ab880129d3c08200208016bb428aec80129d3c000000000232b029a4b00129d3c000000000230c019a5e80129d3c0000000002aa818864004a74f0000000000fc3006ae22004a74f00000000014d787eafc0129d3c00000000006987806ebff004a74e88200208001bf7c4197ae3c004a74f00000000002b64766f000a4eae0000000000b8e018b9a800a4eae0000000000b381debe00293ab80000000002db07a6c000a4eae0000000000bae1ecea00293ab03a03a04b03a03a04b099f8b05d6dcfe1139a9a6e) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P27 : WideCovered band 10945508 12073153 := wide_block_sound band profiles_RelativeWidePack6815_P27 10945508 12073153 (wideData 16 0x36be06d77d00129d3a082002080220b06c74d80129d3c0000000002bdf05af7c00129d3c000000000328e06865d00129d3c0000000002e9d05a7ec00129d3c08200208016ce05a7ae00129d3c00000000026af04a72c00129d3c000000000272e04a35a00129d3c0000000002e4e04ff5880129d3a0820020800a1903df1880129d3c000000000266f04838980129d3c000000000230f03af4c80129d3c0000000002a8f048bed80129d3c0820020800750e3ef8004a74f00000000007a240b0fee004a74f03c83c84b03c83c84b0c967a07b7f87411582bce2) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P27 : WideCovered band 12073154 12636975 := wide_block_sound band profiles_RelativeWidePack6815_P27 12073154 12636975 (wideData 8 0x13e342b1f7c004a74e8208008200fc242b2da2004a74f00000000011a20265fb0004a74f0000000001082022cce4004a74f00000000011af8263db2004a74e8208008200aa781f686e004a74f0000000000eba01f08e0004a74f03e83e84b03e83e84b10cbef09ea9aa811796683e) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8126394 9465473 12636975 c0_RelativeWidePack6815_P27 (wide_covered_join band 9465474 10029296 12636975 c1_RelativeWidePack6815_P27 (wide_covered_join band 10029297 10945507 12636975 c2_RelativeWidePack6815_P27 (wide_covered_join band 10945508 12073153 12636975 c3_RelativeWidePack6815_P27 c4_RelativeWidePack6815_P27))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 8)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 8≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤62)
    (hT0 : 4060≤T) (hT1 : T≤4172) (hnu : 8126394≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤18813173729294498 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R163

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R164
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨8,63,4001,4141,20393803666031911⟩
private def profiles_RelativeWidePack6815_P27 : ℕ → Profile
  | 0 => ⟨16536,4,5080⟩
  | 1 => ⟨2984,24,635⟩
  | 2 => ⟨43768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P27 : WideCovered band 8257465 9397653 := wide_block_sound band profiles_RelativeWidePack6815_P27 8257465 9397653 (wideData 16 0x820020802efa56a34002972f00000000003e3c3a8d800a5cbe000000000126a0dd2e002972f80000000004df833b9000a5cbe00000000016eb0bf24002972f84102104083b69ae90728a4a6b082972f80000000002c72bfc065da3eba004ae5f00000000010865c07b37ba2004ae5e82080082005b61e02cf5e28004ae5f00000000003abca01c2e972004ae5f00000000002abeb01877df2004ae5f00000000001e39e19a6ea8012b97a08200208066ae0dfb6c8012b97c0000000000619f83b3f6e004ae5f071c31450c6d2fd03924b26084ae5f03803804b82f82f84b82ce007abe2010a6cce0) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P27 : WideCovered band 9397654 9967748 := wide_block_sound band profiles_RelativeWidePack6815_P27 9397654 9967748 (wideData 16 0x387c674c800a5cbc0000000000e6b19eb8002972f80000000003afc6a2c000a5cbe0000000000f2b1ab6e002972f80000000003ea86bbd800a5cbe000000000123c1bbaa002972f8000000001ac1c976002972f820800820048a15a69000a5cbe0000000000bee11ffe002972f80000000003aa0526b800a5cbe0000000000f3b14df4002972f80000000003f64539c000a5cbe000000000129e14f76002972f80000000004e60564b800a5cbe00000000016d815bac002972f83903904b83903904b8a879b0596eb24111ff8b28) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P27 : WideCovered band 9967749 10751628 := wide_block_sound band profiles_RelativeWidePack6815_P27 9967749 10751628 (wideData 16 0x8200208026ae428f998012b97c0000000002b1d01a3190012b97c0000000002f380a9b8004ae5f00000000010df02f488012b97a00000000062a819ebd004ae5f061801860078418ffeaa004ae5f00000000003f64065876002972f82080082002ff90638f0002972f800000000038e07a1b000a5cbc0000000000e6b1ea2a002972f80000000003aa07b1b800a5cbe0000000000eed1ef6e002972f80000000003d207ece000a5cbe0000000000fa91fff8002972f80000000001b6c060de0002972f83a03a04b83a03a04b8bb75b05c6ab721138b1ee6) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P27 : WideCovered band 10751629 11891817 := wide_block_sound band profiles_RelativeWidePack6815_P27 10751629 11891817 (wideData 16 0xecf017496e004ae5f0000000000eef8173c2c004ae5f02080082007ca4170de6004ae5f0000000000caec132bac004ae5e8000000000cc2012fb76004ae5f0000000000bdac0fceb2004ae5f00000000008b60132972004ae5f020800820078e80f5eae004ae5e8000000000b96c0f38f6004ae5f0000000000bea80f38aa004ae5f0000000000ce340f497c004ae5f020800820018b10e3eba004ae5e8000000000a9ac0b6fb2004ae5f0000000000b8f80b58e4004ae5f0000000000cc380b3c38004ae5f03c83c84b83c83c84b8ea3bf07926f36114d32bb4) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P27 : WideCovered band 11891818 12818220 := wide_block_sound band profiles_RelativeWidePack6815_P27 11891818 12818220 (wideData 13 0x1caf037b964004ae5e82080082019cb82f28fe004ae5f0000000001ab282e5f6e004ae5f00000000019f2c2bcd7c004ae5f02080082012a642a0da8004ae5e80000000013bf4221bf0004ae5f00000000014fe0234f30004ae5f00000000014fbc231fe4004ae5f0208008200ccbc1f2a28004ae5e80000000011af41e0a34004ae5f00000000011b641bdd7a004ae5f0000000000fe641bcc6e004ae5f03e83e84b83e83e84b93c2ef0997c8a0116ea5b2e) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8257465 9397653 12818220 c0_RelativeWidePack6815_P27 (wide_covered_join band 9397654 9967748 12818220 c1_RelativeWidePack6815_P27 (wide_covered_join band 9967749 10751628 12818220 c2_RelativeWidePack6815_P27 (wide_covered_join band 10751629 11891817 12818220 c3_RelativeWidePack6815_P27 c4_RelativeWidePack6815_P27))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 8)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 8≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤63)
    (hT0 : 4001≤T) (hT1 : T≤4141) (hnu : 8257465≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤20393803666031911 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R164

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R165
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨8,64,3942,4110,21185938132043500⟩
private def profiles_RelativeWidePack6815_P27 : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨44018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P27 : WideCovered band 8388536 9361154 := wide_block_sound band profiles_RelativeWidePack6815_P27 8388536 9361154 (wideData 16 0x27bc06aee0029abb8000000000cff42fdf000a6aee00000000043ff09f680029abb80000000016ba42fdac00a6aec1861061840ede3dc41a25cb49420a6aee0000000000adb38a1d96287e004b36f00000000011a27d06c64820004b36f02080082005efcd02abed36004b36f00000000003eba901b74f7c004b36e800000000039eaf019add24004b36f02080082001d21d15de3a8012cdbc000000000063e6c33bbb4004b36f0000000001ea742b58e2004b36f0000000001aef0264b62004b36f02080082016d782b48ee004b36f02e02e04b02e02e04b06cb8c02c79da801092ccaa) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P27 : WideCovered band 9361155 9937520 := wide_block_sound band profiles_RelativeWidePack6815_P27 9361155 9937520 (wideData 16 0x820020801f985ea680029abb80000000003fb05ff9000a6aee0000000000f6f129720029abb80000000004bb0622c800a6aec000000000139c18af40029abb80000000004d68475a000a6aee000000000176d18eb20029abb80000000006af066ee000a6aee0000000000ad95aaa20029abb82080082005fb143ee800a6aee000000000133911ef40029abb800000000058744738000a6aec000000000161909c6a0029abb80000000006ab442c9000a6aee0000000001e9e0ff320029abb83903904c03903904c0bee7b058eae76091f71ef2) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P27 : WideCovered band 9937521 10621955 := wide_block_sound band profiles_RelativeWidePack6815_P27 9937521 10621955 (wideData 16 0x1964c01c66d4012cdbc0000000000aec740b7b71004b36f08200208002fecd41aa5a2c004b36f000000000049f0061f360029abb00000000003f7c733c800a6aee0000000001329018b4f800a6aee0000000001398018e9a000a6aee00000000013aa01868c800a6aee082002080164b5fb6e0029abb80000000003f2c735c000a6aee000000000121d1cfa40029abb80000000003e605efd000a6aec00000000012eb1dbee0029abb80000000004de87a0a800a6aee000000000131c18b340029abb83a03a04c03a03a04c0dbae905b7f82c093837cae) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P27 : WideCovered band 10621956 11774688 := wide_block_sound band profiles_RelativeWidePack6815_P27 10621956 11774688 (wideData 16 0xffe8134f66004b36f00000000012c7816dc72004b36f02080082003e70121ab2004b36f0000000000fa7c12bba0004b36e8000000000e9340f4cf6004b36f00000000010efc12bbb0004b36f02080082006e03ab688012cdbc000000000320f02de4b8012cdba0000000003b8a03b2bb8012cdbc0000000003a6902ca798012cdbc0000000004af803b69e8012cdbc082002080262a42876c0012cdbc000000000324f01bac88012cdbc00000000042ca02878c8012cdbc000000000470b15dac004b36f03c83c84c03c83c84c10a24f0782daa4094b36de0) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P27 : WideCovered band 11774689 12927420 := wide_block_sound band profiles_RelativeWidePack6815_P27 11774689 12927420 (wideData 16 0x67860378efe004b36f000000000018bdf0c973f8012cdbc0000000000658b433dd76004b36f020800820169f82a48ea004b36e8000000001beb4270f20004b36f0000000001dfe02a8ba2004b36f0208008201392023de26004b36f00000000018e2c22cca6004b36e80000000016b3c1ed922004b36f000000000189fc220928004b36f0208008200d82c1ba92a004b36f00000000012c3017dfe8004b36e80000000014d601b4aac004b36f00000000012fb817ac72004b36f02080082009db417bdac004b36f03e03e04c03e03e04c16b62f08d68bf0096ce293a) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P27 : WideCovered band 12927421 12999465 := wide_block_sound band profiles_RelativeWidePack6815_P27 12927421 12999465 (wideData 1 0x122122130122122130062e7ae0da2ea74098e6dcb2) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8388536 9361154 12999465 c0_RelativeWidePack6815_P27 (wide_covered_join band 9361155 9937520 12999465 c1_RelativeWidePack6815_P27 (wide_covered_join band 9937521 10621955 12999465 c2_RelativeWidePack6815_P27 (wide_covered_join band 10621956 11774688 12999465 c3_RelativeWidePack6815_P27 (wide_covered_join band 11774689 12927420 12999465 c4_RelativeWidePack6815_P27 c5_RelativeWidePack6815_P27)))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 8)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 8≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤64)
    (hT0 : 3942≤T) (hT1 : T≤4110) (hnu : 8388536≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤21185938132043500 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R165

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R166
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨8,65,3886,4078,21572164528332008⟩
private def profiles_RelativeWidePack6815_P27 : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨44268,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P27 : WideCovered band 8519607 9357149 := wide_block_sound band profiles_RelativeWidePack6815_P27 8519607 9357149 (wideData 16 0x7be78060e7b0029e3f80000082002e67b019fb8400a78fe10400208017cdfd2eeefe0029e3f80000000003e78239a00063c7e000000000123a08ebc0018f28000000000048e0138d80063c7e1041841060ecaba9418e0faba42063ca00000000000aaa79b18aaecbe004ba7f00000000012de49068f7c64004ba7e82080082007c2fe02cb2ca8004ba7f0000000000482cd01a63870004ba7f00000000002f21c1d9a4f8012e9fc0820020800a786866cae2004ba7e800000000019b890bf7ce8012e9fc000000000060f6c27c9f2004ba7f02e82e84b02e82e84b099e1d038f3e3e010b2e8e8) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P27 : WideCovered band 9357150 9939787 := wide_block_sound band profiles_RelativeWidePack6815_P27 9357150 9939787 (wideData 16 0x17db15bf60029e3f80000000006c3c575f800a78fe00000000012c774a000a78fe0820020801f5a55bec0029e3f80000000005aec56ba000a78fe000000000166b0eafe0029e3f80000000006b2c561c800a78fe0000000001adc0d82e0029e3f00000000008868533e800a78fe00000000022f90b92a0029e3f8000000000af6c5219000a78fe000000000329c0897e0029e3f8000000000fd682688000a78fe00000000036132ba800a78fe0000000003f5b03f630029e3f83983984c83983984c8c87ee058e3ae8091f6ae76) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P27 : WideCovered band 9939788 10522425 := wide_block_sound band profiles_RelativeWidePack6815_P27 9939788 10522425 (wideData 16 0x5df8066e740029e3f80000000005b700619e20029e3f80000000002ce9068af20029e3f82080082002b7c6f3a800a78fe00000000013b91fd780029e3f80000000004cf86ebe800a78fe00000000013981af340029e3f80000000005ce8061a760029e3f00000000005ab86eec800a78fe0000000001aaa018b5c000a78fe00000000017ad5cc3a0029e3f82080082002be4726b800a78fe00000000012ea15b660029e3f80000000005a306edf800a78fe000000000161915af60029e3f83a03a04c83a03a04c8fabe805af19e609383ce32) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P27 : WideCovered band 10522426 11651286 := wide_block_sound band profiles_RelativeWidePack6815_P27 10522426 11651286 (wideData 16 0x4eb904babc8012e9fc082002080124b04ab6d0012e9fc0000000003f8e03be688012e9fc000000000434e03b72f8012e9fa00000000047f903b34e8012e9fc0000000004fff03b38d8012e9fc0820020801ea942b3498012e9fc0000000003b1c01fe298012e9fa00000000046b8028a5d0012e9fc000000000530a01e7ca8012e9fc00000000067fd01b70d0012e9fc000000000064bbc621e8012e9fa00000000007ca6c570a4012e9fc000000000127b341608b5004ba7f08200208005df6d41b6ab2c004ba7f03b03b04c83b03b04c91979c05eb1f6609492edee) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P27 : WideCovered band 11651287 12816562 := wide_block_sound band profiles_RelativeWidePack6815_P27 11651287 12816562 (wideData 16 0x1933a0aefb90012e9fc000000000065b602e1de8004ba7f02080082018d6827bfbe004ba7f0000000001ed6823edb6004ba7e8000000001eb60239860004ba7f00000000018bb42358e4004ba7f02080082015e681e6ea4004ba7f000000000198b41e1ae6004ba7e80000000019a301bf8ba004ba7f0208008200e8601b4c38004ba7f00000000014f64175aee004ba7f00000000012f7013b9f4004ba7e80000000015da0172b6a004ba7f02080082008ebc16aa22004ba7f00000000011f3412fb2c004ba7f03e03e04c83e03e04c98b74d089f1cfc096af2d66) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P27 : WideCovered band 12816563 13180710 := wide_block_sound band profiles_RelativeWidePack6815_P27 12816563 13180710 (wideData 5 0x8200208006ddec434f3e004ba7e80000000001c7bc0f9b4a0012e9fc0000000000709703b3b76004ba7f02080082001939d0dd7980012e9fc120120132120120132064e6db0c8b4966098cb6cbe) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8519607 9357149 13180710 c0_RelativeWidePack6815_P27 (wide_covered_join band 9357150 9939787 13180710 c1_RelativeWidePack6815_P27 (wide_covered_join band 9939788 10522425 13180710 c2_RelativeWidePack6815_P27 (wide_covered_join band 10522426 11651286 13180710 c3_RelativeWidePack6815_P27 (wide_covered_join band 11651287 12816562 13180710 c4_RelativeWidePack6815_P27 c5_RelativeWidePack6815_P27)))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 8)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 8≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤65)
    (hT0 : 3886≤T) (hT1 : T≤4078) (hnu : 8519607≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤21572164528332008 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R166

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R167
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨8,66,3831,4045,22033923174676894⟩
private def profiles_RelativeWidePack6815_P27 : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨44518,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P27 : WideCovered band 8650678 9331605 := wide_block_sound band profiles_RelativeWidePack6815_P27 8650678 9331605 (wideData 16 0x2c3d221d00063fa80000000000f5c499f20018fe9820800820059f52fbc80063fa80000000000f1804da00018fe980000000003e6812cb00063fa8000000000122a048380018fe980000000004b3c0f4980063fa6000000000139c0396c0018fe984108104203ea0b61062f63bb10818fea00000000002e60cfc67aa6788012fe3c08200208043edac161c33f0012fe3c0000000001ffb780a8fb8a0012fe3c000000000125b78065da3a8012fe3a0000000000f68b0061af690012fe3c082002080075db447486a004bf8f02e82e84b02e82e84b0cdb5f03debd2a010d2fd26) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P27 : WideCovered band 9331606 9828497 := wide_block_sound band profiles_RelativeWidePack6815_P27 9331606 9828497 (wideData 16 0x99f04adc800a7f2c0000000002afa0fd360029fcb8000000000cb703b49800a7f2e0000000000f080d9ac0029fcb8000000000bce5676c000a7f2e00000000073d2bc8800a7f2e0820020800f8d06c720029fcb8000000000b8f41780029fcb830c00c301daac335cc00a7f2c0000000003b7a049720029fcb841001040019f9b499afe800a7f2e00000000012fe089ae0018fe980000000004ee8225c00063fa8000000000168e088fc0018fe98000000000aa488ea0018fea03903904d03903904d0eb62d04e6fdf0091eb5df0) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P27 : WideCovered band 9828498 10417407 := wide_block_sound band profiles_RelativeWidePack6815_P27 9828498 10417407 (wideData 16 0x1b1c1fb320029fcb000000000018b90678f40029fcb8208008201aa5bdec0029fcb800000000059b0637e000a7f2e00000000016f918da20029fcb80000000005fac6a78800a7f2e0000000001b781dfea0029fcb80000000006d7c6669000a7f2e0000000001e8d19b360029fcb00000000003db8676a000a7f2e0820020802abc5ddac0029fcb80000000005ea0578f000a7f2e00000000017da129fa0029fcb80000000006b7c477a800a7f2e0000000001e2e1197e0029fcb83a03a04d03a03a04d10ba6e059eecbe092ea4970) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P27 : WideCovered band 10417408 11300771 := wide_block_sound band profiles_RelativeWidePack6815_P27 10417408 11300771 (wideData 16 0x564d02ffed8012fe3a000000000560c01f3ba8012fe3c000000000762902dede8012fe3c000000000061da8065a76004bf8f0000000001bd68173b0012fe3a0000000003f9816e2a004bf8f0000000000b869c08a7fec012fe3a2080082002bfc21070fe8c8012fe3c0000000001abf0193fb800a7f2c0000000001b5801970e000a7f2e082002080178c418f1c800a7f2e000000000166f1e8a80029fcb80000000006820063f7c0029fcb80000000005d287afd800a7f2e00000000017ca1edaa0029fcb83b03b04d03b03b04d12c3e805d2eb26093fa2b2c) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P27 : WideCovered band 11300772 12478591 := wide_block_sound band profiles_RelativeWidePack6815_P27 11300772 12478591 (wideData 16 0x77ff07b71a0012fe3a000000000061a70227f66004bf8f0208008200e8f81a9a30004bf8f00000000018e7417ce76004bf8f0000000001bf3c1b4d26004bf8e80000000016bf4179b34004bf8f0208008200db20171df8004bf8f000000000158b813396e004bf8f0000000001796013ee3a004bf8e800000000118f013ed2e004bf8f02080082008df00f5fe6004bf8f00000000014fe812792e004bf8f00000000013ca80eceae004bf8e800000000189ac127eae004bf8f02080082004a610e08b8004bf8f03d83d84d03d83d84d18d77907c30f3a095da7ce2) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P27 : WideCovered band 12478592 13361955 := wide_block_sound band profiles_RelativeWidePack6815_P27 12478592 13361955 (wideData 12 0xa1d6847b878004bf8e800000000028f7e12b62b0012fe3c00000000007c8f0424ee8004bf8e82080082001bf4d0fca690012fe3c0000000000708b4339bf8004bf8e80000000001bb7b0cab8d8012fe3c082002080067864361af8004bf8f0000000000197ce09f34b8012fe3c000000000068d6c2b3ebe004bf8e80000000001937f09b2590012fe3c0820020805e1b08ce9a8012fe3c0fe0fe1340fe0fe134062fecc0a9fd9e8097fa483a) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8650678 9331605 13361955 c0_RelativeWidePack6815_P27 (wide_covered_join band 9331606 9828497 13361955 c1_RelativeWidePack6815_P27 (wide_covered_join band 9828498 10417407 13361955 c2_RelativeWidePack6815_P27 (wide_covered_join band 10417408 11300771 13361955 c3_RelativeWidePack6815_P27 (wide_covered_join band 11300772 12478591 13361955 c4_RelativeWidePack6815_P27 c5_RelativeWidePack6815_P27)))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 8)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 8≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤66)
    (hT0 : 3831≤T) (hT1 : T≤4045) (hnu : 8650678≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤22033923174676894 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R167
end MergedPart3
