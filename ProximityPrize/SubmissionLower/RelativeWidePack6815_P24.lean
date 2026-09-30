import ProximityPrize.SubmissionLower.RelativeWideBlocks6815
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R144
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨16,41,3670,3956,17619782869255014⟩
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨24414,146,5079⟩
  | 4 => ⟨29843,173,5971⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 5373895 7789007 := wide_block_sound band profiles 5373895 7789007 (wideData 16 0x11f68073cf6002abbf8000000001397406ac36002abbf80000000006f3907fc7c002abbf82080082008e29075e60002abbf8000000000f9b406e86c002abbf8000000001083c066bf8002abbf80000000001970077da4002abc80208008200ca3d072cb0002abbf8000000000be700608e4002abbf8000000000ef3006cc26002abbf80000000005928071b68002abbf871c01c7010bf3903ee08ae082abbf82080082001df4620e020aaefe0820041006f4320b02135dfe0630630019419402e806100196dfe40f20f20f20f20f20f207fe13aaa00ccbbeb4) (by decide +kernel)
private theorem c1 : WideCovered band 7789008 8402369 := wide_block_sound band profiles 7789008 8402369 (wideData 16 0x67f740b5a78002abbf80000000001fa7f42fb2e000aaefe0820020804b7c0293f8800aaefe0000000006bec02a37e800aaefe000000000770b01e35f000aaefe0000000001b3d42eebb800aaefe082002080567e42ba38000aaf200000000004f8a01b308000aaefe0000000006a29028ebc000aaefe000000000522d02b2ec000aaefe0820020800678690adfaa002abbf80000000010cbc068bf2002abbf80000000015b7007ac60002abbf80000000019d600a1bfe002abbf80000000018b3d077db8002abc802d02d03c82d02d03c92f7da04bbf8ee18ef77e3c) (by decide +kernel)
private theorem c2 : WideCovered band 8402370 9015731 := wide_block_sound band profiles 8402370 9015731 (wideData 16 0x63dac0bac6a002abbf80000000001c26c04b64e000aaefe000000000065a6813f82c002abbf8208008200293d843cfab000aaefe000000000060aa80e6f30002abbf80000000001970f03bb0f000aaefe0000000000698a80b9e32002abc80000000001f92c0fef72002abbf82080082001ffdc4486aa000aaefe00000000077e902e76a800aaefe0000000007e8f028a58000aaefe00000000006adb80ea8b4002abbf8000000001dc610fbbfa002abbf8208008200ae790a3ffa002abbf8000000001c8bc0aed74002abc802e82e83c82e82e83c96eb2e05c7ff3e1908e5e20) (by decide +kernel)
private theorem c3 : WideCovered band 9015732 9629093 := wide_block_sound band profiles 9015732 9629093 (wideData 16 0x7a824222c26002abbf80000000001fe9908b319000aaefe00000000007cc301abea0002abbf80000000010f6c26fb34002abbf82080082017e651bfe7c002abbf80000000001bf99068ffd000aaefe00000000006d9e8131afe002abc800000000001f24f06e21e800aaefe0000000000619a81edaac002abbf82080082001dbbd44d339000aaefe000000000068d6c1389e8002abbf80000000001b7bd05837e800aaefe00000000006eaec0f6db4002abbf80000000001ff4c05f208000aaefe0820020800b4d31177be2002abc803803803c83803803c9ef32e079faab4191a33de4) (by decide +kernel)
private theorem c4 : WideCovered band 9629094 10242455 := wide_block_sound band profiles 9629094 10242455 (wideData 16 0x130f706a8924002abbf80000000004c63f19dfbf000aaefe0000000000fbd384fdce8002abbf82080082007d355ecc7a002abbf80000000002feb810ca2d000aaefe0000000000b08ec332fa4002abbf800000000038f6f10b37f800aaf200000000000e8ae4433f20002abbf80000000002fa7b0cfb58800aaefe082002080076c653748b2002abbf800000000029ab90b8b3a000aaefe0000000000a9fa42e7dec002abbf800000000028b3908caec000aaefe0000000000b6b702ffcf0002abbf82080082001d7594bba2d800aaf200e60e60f20e60e60f206db2690aaf2af6192ba1da8) (by decide +kernel)
private theorem c5 : WideCovered band 10242456 10280790 := wide_block_sound band profiles 10242456 10280790 (wideData 1 0xee0ee0f20ee0ee0f20a7ae0d11afbe7e213cefd6c) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 5373895 7789007 10280790 c0 (wide_covered_join band 7789008 8402369 10280790 c1 (wide_covered_join band 8402370 9015731 10280790 c2 (wide_covered_join band 9015732 9629093 10280790 c3 (wide_covered_join band 9629094 10242455 10280790 c4 c5)))))
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
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨24504,145,5079⟩
  | 4 => ⟨29904,171,5971⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 5504966 7634957 := wide_block_sound band profiles 5504966 7634957 (wideData 16 0x119a8066e7a002af4b8000000001483006ab74002af4b80000000006af006fb7a002af4b82080082014dad072a34002af4b8000000000ef6c063d72002af4b8000000000fd2476ee000abd2e0000000002fec01aa7f800abd300820020805abc41bee9800abd2e000000000360c0182fc800abd2e0000000003b9e018e4b000abd2e0000000001feb019b5f800abd2e0000000003a2d418a19800abd2e2490092404b89f80eefabf820abd2e1450051400a3917da8084de8f8f3c03cf0019342fae824bd8f20e60e60f40e60e60f40b1f12ff000cef4ab2) (by decide +kernel)
private theorem c1 : WideCovered band 7634958 8254590 := wide_block_sound band profiles 7634958 8254590 (wideData 16 0x63b380a0974002af4b8000000000bf7c0a9b60002af4b8000000000186fb41eeea800abd2e0820020802e7c01e35a000abd2e000000000738a01db8b800abd2e000000000063a6407dc66002af4b800000000019769429fed000abd300820020804ec07787e002af4b80000000015d3c062bbc002af4b8000000001cd2407586a002af4b80000000007ee107ce68002af4b82080082012df907a9f8002af4b8000000001493c06baa0002af4b80000000017ea006fde6002af4b80000000005ea8067e20002af4b82c82c83d02c82c83d148f4904867f2618ed2bd68) (by decide +kernel)
private theorem c2 : WideCovered band 8254591 8874224 := wide_block_sound band profiles 8254591 8874224 (wideData 16 0x2080082001da3d43ef9e000abd2e000000000066eec0b4e30002af4b80000000001bb0b02effb000abd2e000000000079fa00e79a2002af4b800000000028a9f43e6d8800abd2e0820020800a7801ee7a000abd2e000000000064f740a9fb2002af4c00000000001b3eb02c68c000abd2e000000000062e2c0bcde2002af4b82080082002aada43b78f800abd2e0000000007a5c01febf800abd2e000000000060a7406cdee002af4b80000000001b27e02aacd800abd2e0000000002a6a42db3d000abd2e0820020800639b50b4834002af4c02e02e03d02e02e03d18face04f64aa418fea5f2a) (by decide +kernel)
private theorem c3 : WideCovered band 8874225 9493858 := wide_block_sound band profiles 8874225 9493858 (wideData 16 0x2bf2847ca4e800abd2e08200208006dca4134a2c002af4b80000000001b27f03a37a000abd2e00000000007ade413ec30002af4b8000000000293cc05ae7b000abd2e0000000004f1e45fe4d800abd2e082002080533b44cf2c800abd3000000000006df740fa87c002af4b80000000001ba8c02d64b000abd2e00000000007f9ac129e2a002af4b80000000003ffc13be2c002af4b82080082001ca5e44ab5b000abd2e000000000069dfc0e49f0002af4b80000000001c64a03af4c800abd2e00000000007bd640f4ea0002af4c03803803d03803803d1cebc906a2dc3c1918208ee) (by decide +kernel)
private theorem c4 : WideCovered band 9493859 10113492 := wide_block_sound band profiles 9493859 10113492 (wideData 16 0x20800820019a1b509e58800abd2e0000000000b5fe02ece70002af4b80000000002e60d0bb6fe800abd2e0000000000bdd682f2baa002af4b8000000000392e90bf3ef000abd2e000000000076b3c265ffa002af4b82080082001affb49d75e800abd300000000000a4c38221ff6002af4b80000000002a6ee089f9e000abd2e0000000000b0bb4232922002af4b80000000002eadd098b7c000abd2e0820020800b68e11f283e002af4b80000000001c76804ef6b800abd2e00000000007cb681a3de6002af4b800000000028ef806b639800abd300e60e60f40e60e60f406ab7a908c78e2019297aab2) (by decide +kernel)
private theorem c5 : WideCovered band 10113493 10462035 := wide_block_sound band profiles 10113493 10462035 (wideData 9 0x13daf44309fa002af4b820800820038e2c55ff7a800abd2e0000000000bf8b42adeb0002af4b80000000005d75856862ec20abd2e08200208006ba644bdae2002af4b80000000003e73c11ab18000abd2e0000000000fba284648ac002af4b80000000003fb88118f7e800abd2e0ec0ec0f40ec0ec0f40a59e3c0dae8da8193af4c76) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 5504966 7634957 10462035 c0 (wide_covered_join band 7634958 8254590 10462035 c1 (wide_covered_join band 8254591 8874224 10462035 c2 (wide_covered_join band 8874225 9493858 10462035 c3 (wide_covered_join band 9493859 10113492 10462035 c4 c5)))))
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
private def profiles : ℕ → Profile
  | 0 => ⟨16536,4,5080⟩
  | 1 => ⟨24535,143,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 5636037 7474634 := wide_block_sound band profiles 5636037 7474634 (wideData 16 0x2080082001cf87b09800acb3e00000000053d8018388000acb3e0000000002f790192bf000acb3e00000000023f95fb62002b2cf82080082002da1065a78002b2cf800000000129b47abb800acb3e000000000364d19ea0002b2d80000000000cd2906593c002b2cf820800820019e0060ce0002b2cf8000000000eda05a4d000acb3e0000000002b6c1eca4002b2cf8000000000b8a10629b2002b2cf82080082003be05f18800acb3e0000000003a491a872002b2cf871c01c7014f2ae0383cd64082b2d802b82b83d82b82b83d879ec075af400d92ceae) (by decide +kernel)
private theorem c1 : WideCovered band 7474635 8100539 := wide_block_sound band profiles 7474635 8100539 (wideData 16 0x7bce1deb8002b2cf80000000001a72901c2fd800acb3e00000000016eb41e27c000acb3e0000000004a9d41ba0c000acb3e082002080166801cbdf000acb3e0000000000629f406bcb6002b2cf8000000000ad3c066e60002b2cf80000000017bfd074d24002b2cf82080082001ce406f9f8002b2cf8000000001cda0067cb4002b2cf8000000000e9e87fde000acb3e0000000005a2941cbd8800acb3e082002080074a01ab5f000acb3e0000000005acf1ac72002b2cf8000000000ebfc067d62002b2d802c02c03d82c02c03d96ef2d03c6ec6008eab3a72) (by decide +kernel)
private theorem c2 : WideCovered band 8100540 8726445 := wide_block_sound band profiles 8100540 8726445 (wideData 16 0x3f2a02deaa000acb3e0000000006a7d4283f8000acb3e082002080438c42dbbe800acb3e000000000072c2807efbc002b2cf80000000001ee3d01ae4a000acb3e0000000003a2d42bfc9000acb3e08200208007bb250e0e74002b2d800000000001964c018a68000acb3e000000000072cbc079da2002b2cf80000000015b7c0a2baa002b2cf80000000010931072a76002b2cf8208008201b9350acb6a002b2cf80000000001a60a01cac9000acb3e00000000006ff6c064ab2002b2cf800000000169a50a0d6c002b2d802e02e03d82e02e03d99f7a9049fdfac08fc39e34) (by decide +kernel)
private theorem c3 : WideCovered band 8726446 9352350 := wide_block_sound band profiles 8726446 9352350 (wideData 16 0xa6ea40fbcf8002b2cf80000000002b69e02e318800acb3e000000000079c3513792e002b2cf82080082010f690fba6c002b2cf80000000001c67901f7df800acb3e0000000000a2c640e4cb6002b2cf80000000002b74e03c249800acb3e0000000007bbd42c66a000acb3e082002080076a710fcdec002b2cf80000000001d3ba02bff8800acb3e00000000007a8bc075bbc002b2cf800000000029fae02fb5f000acb3e00000000007fe390f0e38002b2cf82080082015e6d0b9b24002b2cf80000000001bf7801d24e000acb600be0be0f60be0be0f6060ab5a05a27ff2090de09f8) (by decide +kernel)
private theorem c4 : WideCovered band 9352351 9978256 := wide_block_sound band profiles 9352351 9978256 (wideData 16 0x2f2bf07ea0b000acb3e0000000000b99a41a68ac002b2cf80000000006ef122d962002b2cf82080082017d46cbdd800acb3e0000000000a6c38176a2a002b2cf800000000028b3b049f1d000acb3e0000000000b78b81a5870002b2d80000000001e8781b58ee002b2cf82080082001eb3944dbfb800acb3e00000000007c9a812bdba002b2cf800000000028ece04c7f8800acb3e0000000000a3e780ea9ec002b2cf80000000002d7bc0597ad800acb3e0000000000eefa117bce6002b2cf82080082001aa3a02ba8a000acb600e40e40f60e40e40f606cb7db06e64ef0091f66dba) (by decide +kernel)
private theorem c5 : WideCovered band 9978257 10604161 := wide_block_sound band profiles 9978257 10604161 (wideData 16 0x1b5d206299b2002b2cf80000000006db9d17f3e9000acb3e082002080069be13f8b68002b2cf80000000004bb5a0feb18000acb3e00000000012fdb43f2f64002b2cf80000000003ef3f0c925a800acb3e000000000137fb03f2aa8002b2cf80000000005eb53fbeb6002b2cf8208008200292ae08bafb800acb3e0000000000e8bf02b0c3a002b2cf80000000003b3c80ace48000acb3e0000000000e1f70226972002b2cf80000000003f2b80b8f48800acb3e0820020800aa9392a9c3e002b2cf800000000028fda05d27a800acb600ea0ea0f60ea0ea0f60a1a6fe09cbeaa20938ed97e) (by decide +kernel)
private theorem c6 : WideCovered band 10604162 10643280 := wide_block_sound band profiles 10604162 10643280 (wideData 1 0xf00f00f60f00f00f60f3fb5d10cb58b2094a73d60) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 5636037 7474634 10643280 c0 (wide_covered_join band 7474635 8100539 10643280 c1 (wide_covered_join band 8100540 8726445 10643280 c2 (wide_covered_join band 8726446 9352350 10643280 c3 (wide_covered_join band 9352351 9978256 10643280 c4 (wide_covered_join band 9978257 10604161 10643280 c5 c6))))))
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
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨24620,142,5079⟩
  | 3 => ⟨30072,168,5971⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 5767108 7268529 := wide_block_sound band profiles 5767108 7268529 (wideData 16 0x8200208046e81a8b2002b65b80000000011a2c738c800ad96e00000000027ce41830c800ad96e0820020801aeb4183ed800ad96e0000000003b0914bb0002b65b8000000000df2866bd800ad970000000000238d5e8e0002b65b82080082003aa1769f800ad96e000000000376817a78002b65b800000000079f466ec800ad96e000000000161a56c3a002b65b8208008200ad59ff8002b65b8000000000c9f057dd800ad96e1450030c04bde700b9b20d020ad96e2cb00d3400fab018adb824e9af20b40b40f80b40b40f80e3c129e400c9b2cea) (by decide +kernel)
private theorem c1 : WideCovered band 7268530 7900706 := wide_block_sound band profiles 7268530 7900706 (wideData 16 0x778e16ea8002b65b800000000018a2c019b88000ad96e000000000429941b779800ad96e08200208072fa41dece800ad96e0000000006e49018339000ad96e0000000007e9918bee002b65c0000000000d9350698a4002b65b80000000019eb9072aee002b65b82080082016d787aab800ad96e0000000005a7a018728000ad96e000000000133f5b8f8002b65b800000000158b106cee4002b65b82080082012ebc730a000ad96e000000000523c1efe2002b65b8000000000ba75063aa4002b65b82b82b83e02b82b83e14e29a039b892610dfa1c30) (by decide +kernel)
private theorem c2 : WideCovered band 7900707 8532883 := wide_block_sound band profiles 7900707 8532883 (wideData 16 0x7d928063cfa002b65b80000000011cfd07acf2002b65b80000000001f33e42e3ff800ad96e08200208072ab01d2b9800ad96e00000000007bef8070f24002b65b8000000000b86d0798be002b65c00000000007ca5068c6e002b65b82080082019cfd0a5f2c002b65b80000000001bf4801aade800ad96e000000000464d01c64a800ad96e000000000768a41f3eb000ad96e082002080470c41b658000ad96e000000000066de4065eea002b65b8000000001dfb806b962002b65b80000000014ff1073ff8002b65b82d82d83e02d82d83e16cebe03e70efe10f9349f2) (by decide +kernel)
private theorem c3 : WideCovered band 8532884 9165061 := wide_block_sound band profiles 8532884 9165061 (wideData 16 0x1e2cb02aeed000ad96e00000000007fd7006daa0002b65b80000000002af0a02defd000ad96e000000000077c350e8c78002b65b82080082001b69c43a6ae800ad96e000000000077b7407ff38002b65c0000000000283dc0192d8000ad96e000000000077d680ab9e4002b65b80000000001c2fc42f2ba800ad96e08200208006bea50e0a30002b65b80000000001df7d01e219800ad96e0000000000a3e747e2b000ad96e000000000566b028ffc000ad96e000000000071b790b7824002b65c0208008201496d0af9aa002b65b82f02f03e02f02f03e1ba64804cf2d3c110ae6fb4) (by decide +kernel)
private theorem c4 : WideCovered band 9165062 9797238 := wide_block_sound band profiles 9165062 9797238 (wideData 16 0x7dd6812bc36002b65b80000000002931904b34d000ad96e0000000000a7f700ecdfa002b65b8000000000187b805970b000ad96e0820020800acfa9168ae0002b65b80000000001db8b03b3af800ad97000000000007efe40f29ba002b65b800000000028abb02b65b800ad96e0000000000a4968122d32002b65b80000000002e6e844dbb8800ad96e0820020804ee9039ad8000ad96e00000000007ae680bbd7c002b65b80000000002822901ead9000ad96e0000000000b0bac0e9b34002b65b80000000002963c43ef28800ad96e0e40e40f80e40e40f8062b6ed05e6ddf6111c79d78) (by decide +kernel)
private theorem c5 : WideCovered band 9797239 10429415 := wide_block_sound band profiles 9797239 10429415 (wideData 16 0xea9b02bab68002b65b80000000003bb880af3dd800ad96e0000000000e487422dda8002b65b800000000099282edea4002b65b82080082017fe022de20002b65b80000000002c7cb07d278800ad9700000000000b78e41f8b66002b65b80000000002c35e05ef1a800ad96e0000000000e8ab0229878002b65b82080082002ea6c488a0a000ad96e0000000000a2aac1738ae002b65b800000000029fab05debc800ad96e0000000000a6a60130a2c002b65b80000000002df6d05ef3a800ad96e0000000007bc846daae000ad96e0ea0ea0f80ea0ea0f807197ce07dacea4112e2cb3a) (by decide +kernel)
private theorem c6 : WideCovered band 10429416 10824525 := wide_block_sound band profiles 10429416 10824525 (wideData 10 0x820020802a6ff11ebb67082b65b80000000006eb6919b61c000ad96e08200208007b953df2d000ad96e000000000132da443d8e0002b65b80000000004c7e810bf19000ad96e000000000132e74426cbc002b65b80000000004d72e108ba8000ad96e000000000123d3c333e36002b65b82080082001abaa4e93af000ad96e0ee0ee0f80ee0ee0f80aff2bf0bd68ebe113fbf8fc) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 5767108 7268529 10824525 c0 (wide_covered_join band 7268530 7900706 10824525 c1 (wide_covered_join band 7900707 8532883 10824525 c2 (wide_covered_join band 8532884 9165061 10824525 c3 (wide_covered_join band 9165062 9797238 10824525 c4 (wide_covered_join band 9797239 10429415 10824525 c5 c6))))))
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
private def profiles : ℕ → Profile
  | 0 => ⟨16536,4,5080⟩
  | 1 => ⟨24644,140,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 5898179 7135173 := wide_block_sound band profiles 5898179 7135173 (wideData 16 0x12ea1061d38002b7df82080082003fb04bdb800adf7e0000000002a4d18964002b7df80000000006c34573c800adf7e00000000042485ea2c002b7df82080082006ee856df800adf7e00000000022bc12826002b7df8000000000c819cbe002b7df82080082008c3d67e9800adf7e0000000001ad910828002b7df80000000007fa857af800adf7e0000000000ac953be2002b7df82080082004f615bda000adf7e0000000001a78138e4002b7df8d34034d009d3ad02c649fe082b7e802c02c03e82c02c03e83f70073faa00cbbeee6) (by decide +kernel)
private theorem c1 : WideCovered band 7135174 7773622 := wide_block_sound band profiles 7135174 7773622 (wideData 16 0x208033b941b3d8800adf7e0000030c06bbe419a5b000adf7e08200208033db01832f000adf7e00000000062ce018b3b800adf7e0000000001f3c5bbba002b7df8208008201beed06dff4002b7df8000000000edf44eac800adf7e000000000520d1ffaa002b7df80000000010fb5066d2a002b7df8208008200afa9726a800adf7e00000000036dd1ae3c002b7df8000000000ee2876e8800adf7e000000000377c5bcfe002b7df82080082006df57ede000adf7e0000000002bbf12f3c002b7e802b02b03e82b02b03e8aa75f02f73d7e08dd7dea8) (by decide +kernel)
private theorem c2 : WideCovered band 7773623 8412071 := wide_block_sound band profiles 7773623 8412071 (wideData 16 0x1fb2d42b3a9800adf7e082000000075a3d079e3c002b7df80000000001b32f019b1c000adf7e00000208006ed2406fb66002b7df80000000005de45eb8000adf7e0820000000bedb10bcd6a002b7df8000000000183af10ff6002b7df80000000001cb3f01a318800adf7e000002080579c41d7ff000adf7e0000030c06af941a2c9800adf7e08200208012dc41c688800adf7e000000000066ce0067c28002b7df8000008201eb5ae74002b7df82080000001ebdd428bae800adf7e000000000565812f28002b7e802d02d03e82d02d03e8aef0c03b73be008ef3ce6a) (by decide +kernel)
private theorem c3 : WideCovered band 8412072 9050520 := wide_block_sound band profiles 8412072 9050520 (wideData 16 0x1fe8c0296da800adf7e00000208007ebe8060afc002b7df800000c3002ffbf43b278000adf7e08200208067a842c29d000adf7e00000000006d8685a48800adf7e0000000000a6e6807ab24002b7df80000082003be90abdfa002b7df80000000009d39066926002b7df82080000001ef9b42efab800adf7e000000000071f78432b000adf7e0000000000b28f4073ce4002b7df80000082001870f429bdd000adf7e000000000129941868e000adf7e0820000000758bd0b69e2002b7df80000000001e7aa19ca2002b7e802f02f03e82f02f03e89fb080492bda20908fbe2c) (by decide +kernel)
private theorem c4 : WideCovered band 9050521 9688969 := wide_block_sound band profiles 9050521 9688969 (wideData 16 0x6bf700f5dae002b7df80000000001cb4802c79c800adf7e0000000000aabb1134cb8002b7df8208008200cea40bc830002b7df8000000001f920075df8002b7df80000000001abce02f64c800adf7e000000000077fe80e9aae002b7df8000000000a9ad0a7ab2002b7df82080082001fe6c43c65a800adf7e0000000007b7f019f3d000adf7e00000000006b9a40aac62002b7df80000000001eb0c02d3b8000adf7e0000000000649a8071d30002b7df80000000003db894482ff000adf7e0820020800629b007b8bc002b7e803883883e83883883e8fea7805826f6a091abadee) (by decide +kernel)
private theorem c5 : WideCovered band 9688970 10327418 := wide_block_sound band profiles 9688970 10327418 (wideData 16 0x1cf7c07cf0d800adf7e00000000037a94886f8800adf7e0820020801b8b04aa5f000adf7e000000000064cb816bc68002b7df800000000018af9048339800adf7e00000000006cb20176df6002b7df80000000001cbba068e5a000adf7e08200208007f9f51369a6002b7df8000000001faec122da8002b7df80000000001839e03d63e800adf7e000000000064fe80f4fbe002b7df80000000001baec04db2c000adf7e0000000005f7803c2bf000adf7e08200208007bc71131a2c002b7df8000000001fba40e9d22002b7e803a03a03e83a03a03e96a28e06af0d7e092c79db0) (by decide +kernel)
private theorem c6 : WideCovered band 10327419 10965867 := wide_block_sound band profiles 10327419 10965867 (wideData 16 0x3b6bf16a77d000adf7e0820020801abd5197cb800adf7e00000000007f960325f38002b7df80000000002ab1d0ee6a8800adf7e0000000000a0ba42f6bb4002b7df80000000002b72e0ecfcb000adf7e0820020802b4e4ea3dd800adf7e00000000006d928220836002b7df80000000001dacb0a837d000adf7e000000000078a202a1d7a002b7df80000000001cb7d07f7db000adf7e00000000007eff82adaee002b7df82080082001ab4a47af58000adf7e00000000006a8bc1e49ee002b7df80000000001b2ba079e39800adfa00ee0ee0fa0ee0ee0fa060d22c08ead9ba093e38d72) (by decide +kernel)
private theorem c7 : WideCovered band 10965868 11005770 := wide_block_sound band profiles 10965868 11005770 (wideData 1 0xf40f40fa0f40f40fa078fbdb0ef26936094ff7d34) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 5898179 7135173 11005770 c0 (wide_covered_join band 7135174 7773622 11005770 c1 (wide_covered_join band 7773623 8412071 11005770 c2 (wide_covered_join band 8412072 9050520 11005770 c3 (wide_covered_join band 9050521 9688969 11005770 c4 (wide_covered_join band 9688970 10327418 11005770 c5 (wide_covered_join band 10327419 10965867 11005770 c6 c7)))))))
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
private def profiles : ℕ → Profile
  | 0 => ⟨8268,2,2540⟩
  | 1 => ⟨2984,24,635⟩
  | 2 => ⟨24724,139,5079⟩
  | 3 => ⟨24644,140,5079⟩
  | 4 => ⟨24703,141,5079⟩
  | 5 => ⟨24620,142,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 6029250 6996331 := wide_block_sound band profiles 6029250 6996331 (wideData 16 0xa2a17b60002bb6b80000000002d286ef8800aedae08200208016aa559e2002bb6b80000000001ba4475a800aedae000000000079d16d76002bb6b80000000002b716ad9800aedae0820020801283aa8800aedae00000000006aa13bb2002bb6c00000000001cb457cc000aedae0820020800bcd56a76002bb6b8000000001ed0ddb8002bb6b830c00c30029f0c44831ce7082bb6b82080082008aa00639abe000aedae0c30030c0371b47b28cab002bb6b830c0082003efee0ce22828084f6cf02a02a03f02902903f0e91cef400c8f5bf4) (by decide +kernel)
private theorem c1 : WideCovered band 6996332 7641052 := wide_block_sound band profiles 6996332 7641052 (wideData 16 0x2080000001d343b3d800aedae00000000017bf1d932002bb6b80000000009a34066c30002bb6b82080082012cbd06ad2e002bb6b80000000003a24470f800aedae000000000134e1dbf0002bb6b80000000006fa40669fa002bb6b8208008200ea755fbb800aedb00000000000bac18bbe002bb6b80000000003e38764d800aedae0000000001b6941963a000aedae0820020806e03f2a800aedae0000000000acf1883c002bb6b8000000000392472db000aedae0820020801aa95ddb8002bb6b82a82a83f02a82a83f01cb1a02de0fbc10db6fb64) (by decide +kernel)
private theorem c2 : WideCovered band 7641053 8285772 := wide_block_sound band profiles 7641053 8285772 (wideData 16 0x10928269aa2102bb6b80000000016f604e7d800aedae0000000007aadcf86a002bb6b82080082007c6b069b3a0c2bb6b8000000000aa640f5cf6082bb6b8000000000f92862ff800aedae000000000679c83afbe820aedae0000020800a0b49abf0c2bb6b82080000001a73bc1d6ef000aedae0000000002fb803ef88020aedae0000000004ecc1ef28002bb6b80000082004d7b077dfc002bb6b8208000001ab3f06ebbc002bb6b80000000007d206f3c000aedae00000000033fb0193a8800aedae0b40b40fc0b40b40fc6aa8039a5e6210ed3ad26) (by decide +kernel)
private theorem c3 : WideCovered band 8285773 8930493 := wide_block_sound band profiles 8285773 8930493 (wideData 16 0x6ab331b9ec00aedae08200208016afc186a8030aedae0000000002f0801af5a800aedae0000000004f7b01ee8f800aedae0000000006769819b0e000aedae0000020800acdb907dd66002bb6b8208000001ca6e0e5ef2002bb6b8000000000dc7c63de000aedb000000000067f815b78002bb6b800000000019799c9d2a002bb6b82080082005a2f06bfe40c2bb6b8000000000beac132cf0082bb6b800000000118b84e89800aedae000000000668e8cca4002bb6b800000000059b195c9e9002bb6b82f02f03f02f02f03f05b3cd848b9fa818ff25ee6) (by decide +kernel)
private theorem c4 : WideCovered band 8930494 9575214 := wide_block_sound band profiles 8930494 9575214 (wideData 16 0x3bce03bbfc800aedae082002080736a43be9c800aedae0000000001a1c0282bd000aedae0000000001ea91cda0002bb6b8000000000b8b00a6bae002bb6b80000000011a6c0b4920002bb6b800000820028290f5ae0002bb6b82080000019cf5061fa8002bb6c00000000008ba4070c64002bb6b8000000000cc70074ae6002bb6b80000000014e3c179a400aedae00000000067a881c7e8000aedae0000020800e9efd0b5ff0002bb6b82080000001df6d8487af000aedae0000000003abf0cbaf002bb6b83883883f03883883f01ba2904d72e2c1118f18a8) (by decide +kernel)
private theorem c5 : WideCovered band 9575215 10219935 := wide_block_sound band profiles 9575215 10219935 (wideData 16 0x208008200bea10f4dfc002bb6b800000000059e81219b2002bb6b80000000005ee8125d72002bb6b80000000006de812ceba002bb6b800000000079380e4ee4002bb6b80000000009ee4164ba8002bb6b82080082010ae10f0ae6002bb6b80000000005ab80e7a32002bb6c00000000005ce00a3f7e002bb6b80000000007d3c0f28e4002bb6b80000000009ee412097c002bb6b800000000078e90bcd3c002bb6b82080082005e2d0b1eaa002bb6b800000000068700b28e2002bb6b80000000007d340b8e20002bb6b83a03a03f03a03a03f02df7a05d6de7c112abca6a) (by decide +kernel)
private theorem c6 : WideCovered band 10219936 10864655 := wide_block_sound band profiles 10219936 10864655 (wideData 16 0x8ea42aaee0002bb6b80000000007d74222ae6002bb6b80000000009ab02a8ca4002bb6b80000000009e702ace74002bb6b82080082003e352b2b24002bb6b80000000005da4173a3c002bb6b80000000006fe01e7d66002bb6b80000000007aec1eab70002bb6b80000000007f381f08b6002bb6b80000000007c6817adf6002bb6b820800820079251edc6c002bb6b80000000005d64169f72002bb6b80000000005bfc12ce2e002bb6b80000000006b28161c60002bb6b80000000007bb8178c6e002bb6b83b83b83f03b83b83f04927e07beca7a113ca7c2c) (by decide +kernel)
private theorem c7 : WideCovered band 10864656 11187015 := wide_block_sound band profiles 10864656 11187015 (wideData 8 0x12a285f4bf4002bb6b8208008200293053ad2a002bb6b8000000000ad203619f2002bb6b8000000000cb343f3864002bb6b8000000000cb383e8cfe002bb6b8000000000be7c37beac002bb6b8000000000be78368bfe002bb6b83d03d03f03d03d03f06da1d0babbe2c114e72dec) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6029250 6996331 11187015 c0 (wide_covered_join band 6996332 7641052 11187015 c1 (wide_covered_join band 7641053 8285772 11187015 c2 (wide_covered_join band 8285773 8930493 11187015 c3 (wide_covered_join band 8930494 9575214 11187015 c4 (wide_covered_join band 9575215 10219935 11187015 c5 (wide_covered_join band 10219936 10864655 11187015 c6 c7)))))))
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
