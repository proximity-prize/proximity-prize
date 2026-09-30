import ProximityPrize.SubmissionLower.RelativeWideBlocks6815
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R102
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨14,39,4214,4232,41106997183793118⟩
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨24544,160,5079⟩
  | 4 => ⟨24484,162,5079⟩
  | 5 => ⟨39518,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 5111755 9035023 := wide_block_sound band profiles 5111755 9035023 (wideData 16 0x8ee82e4f400a3ea0000000000432809cfdf000a3e7e00000000072cb0fee6cc00a3e7e0000000000689c4bee8eb0c28f9f841001040019218c9a21e340828f9f80000000001a7c0e49a200187cf80000000001aec0e4dee00187d800000000001b6c0e5cfe00187cf80000000001bf00e6c3c00187d800000000001f30134a3000187cf80000000001d7c0ecbe400187d8071c01c7002c2aa0ae39bac08187d800000000003c01d2c882061f601c70071c02bc0679b8090fafd03a03a000e80e8002805c800a3e7eb02083a82083a84815af200dff3e6c) (by decide +kernel)
private theorem c1 : WideCovered band 9035024 9555810 := wide_block_sound band profiles 9035024 9555810 (wideData 15 0x1f4c028b68000a3e7e000000000321b01f2a0028f9f80000000017d60161a2f0028f9f8000000001f8f61a4e650028f9f82080082003cb7ec6eaeba31028f9f82080082014c7547c9240028f9f80000000008eac5f68760028f9f800000000078b433dff60028fa800000000009f7852bf220028f9f8000000000aea03f9ab80028f9f8000000000daf42b8c380028f9f800000000188b07e0bac0028fa800000000001a3ec108a48800a3e7e0820020800a8e6d1f68ea0028f9f83883883a83883883a83ce3d10bbce64191a72abc) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 5111755 9035023 9555810 c0 c1)
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 14)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 14≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤39)
    (hT0 : 4214≤T) (hT1 : T≤4232) (hnu : 5111755≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤41106997183793118 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R102

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R103
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨14,40,4119,4208,41397517565572656⟩
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨24600,158,5079⟩
  | 4 => ⟨24420,164,5079⟩
  | 5 => ⟨24544,160,5079⟩
  | 6 => ⟨39768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 5242826 8701277 := wide_block_sound band profiles 5242826 8701277 (wideData 16 0x2f6d04936880062a680000000002f5f03875e80062a660000000001690ea83e0018a9a020800820018f7942a7cf00062a6800000000013e801d78c00062a68000000000168b01da7e80062a660000000001b6c02cecc80062a680000000001a5c01e6bc00062a660000000001b8a01eb6d00062a680000000001efa01f32900062a662cb00b2c0269afc229a62882062a681c70071c0062c01cf39020a4cae0820020805fc066de8088ca9e830c00c3007c02bc0464cf4062062001901900003c80062a67982a82a83b02a02a03b14a1587c00ea64e68) (by decide +kernel)
private theorem c1 : WideCovered band 8701278 9105055 := wide_block_sound band profiles 8701278 9105055 (wideData 16 0x266beb5e897f002932b820800820028a8bc183aee7142932b80000000001c7fc03df0a000a4cae0000000000adc604fcfc00a4cae000000000061f312b4cad9c20a4cae0000000007e2dc2f6af6d002932c04100104002d30b93d39c62082932b800000000059ec0a6ff00018a9980000000005bbc0a7b740018a9a00000000005df40a7f780018a9980000000007a300e8db80018a9a00000000006bfc0ab93e0018a9a00000000006fec0aceae0018a9a00000000007c640aebfc0018a99800000000089fc0b18e00018a9a02f82f83b02f82f83b0ab7fe099f7a7c190d24fe0) (by decide +kernel)
private theorem c2 : WideCovered band 9105056 9666833 := wide_block_sound band profiles 9105056 9666833 (wideData 16 0x128bc1349e2002932b800000000149e80e3b38002932b80000000019cfc0a7e2a002932b820800820089fbd45cece79182932b80000000001877f0ee61a000a4cae0000000000658683a5d60002932c00000000001db3e18e31e800a4cae000000000075ce43e2e6e002932b80000000002a30c0fff7b800a4cae0820020800f1ced5a1da6002932b80000000018e301bb97e002932b8000000001cee0177ba4002932b80000000001b7280dbffe800a4cae000000000072f300f9f7c002932c00000000002c6bb078bc002932b83903903b03903903b0b83bd0ee26b24191b7bf2c) (by decide +kernel)
private theorem c3 : WideCovered band 9666834 9737055 := wide_block_sound band profiles 9666834 9737055 (wideData 2 0xe8b013dd3e002932b83a03a03b03a03a03b10e7ed0df318e4312c258f0) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 5242826 8701277 9737055 c0 (wide_covered_join band 8701278 9105055 9737055 c1 (wide_covered_join band 9105056 9666833 9737055 c2 c3)))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 14)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 14≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤40)
    (hT0 : 4119≤T) (hT1 : T≤4208) (hnu : 5242826≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤41397517565572656 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R103

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R104
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨14,41,4029,4184,42361603806778530⟩
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨33072,8,10160⟩
  | 4 => ⟨24705,157,5079⟩
  | 5 => ⟨24352,166,5079⟩
  | 6 => ⟨24484,162,5079⟩
  | 7 => ⟨24544,160,5079⟩
  | 8 => ⟨24652,159,5079⟩
  | 9 => ⟨39768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 5373897 8515926 := wide_block_sound band profiles 5373897 8515926 (wideData 16 0x3a6d01ab2d80062d700000000004aee02bbcd80062d6e0000000004eee01c37c00062d700000000005edf01ce8980062d6e000000000762d01df5880062d700000020800a7843cf8e00062d6e0000030c00bdfe10b1aae0018b5c020800820039bc060db40018b5b80000000009c3076fd00062d70000000000327c01db5d80062d6e000000000326c1eee60018b5c0514014500dc6ca0786fb6a0818b5b82080082001f24072f300818b5c0b2c02cb01fe19b7a084ab5f89240249017c0cd780818b5be60ee0ee0ee0ee0ee0ee063a14e3600ecb5e64) (by decide +kernel)
private theorem c1 : WideCovered band 8515927 8799951 := wide_block_sound band profiles 8515927 8799951 (wideData 16 0x26fc01da1d80062d700000000002a4901d7df00062d6e00000000033e902d68d80062d70000000000322801e63b80062d6e000000000369e01ea3800062d700000000003bc901ef9e00062d6e0000000004e6903962a80062d700000000004f2e02928f80062d6e0000000005e1a02a3ff00062d700000000006f7902be8980062d6e0820020800e8db50f9de80018b5c00000000008bf0067f3c0018b5b800000000099a0067efe0018b5c0000000000aae006cb7e0018b5b8000000000ccb807fd320018b5c02f02f03b82f02f03b8fc27f07e75afc210a3babc) (by decide +kernel)
private theorem c2 : WideCovered band 8799952 9279244 := wide_block_sound band profiles 8799952 9279244 (wideData 16 0x820020800669610afa3000296af80000000002835906afb9800a5abe0000000000aaea80fdeb500296af80000000004c35b019e1c800a5abe0000000001f79240bf93ad490a5abe0000020805ace27427cb908296b802080000005e2aac3b20be508296af80000000003da5e048398000a5abe000000000178da416ff3d00296af80000000009affb5aa2dbe508296b802080082013873a0196b96d8020a5abe00000000052c803fa3c00062d6e000000000531802feb980062d700000000004f8c439ac980062d6e082002080069fe10e8aea0018b5c02f82f83b82f82f83b92eeca08eb2ce4210ea68ae) (by decide +kernel)
private theorem c3 : WideCovered band 9279245 9847294 := wide_block_sound band profiles 9279245 9847294 (wideData 16 0x15a28174eac00296af80000000016a68170ef000296af80000000016ae8138f7e00296af80000000015af40e88b200296af80000000008de9f4583786328296af800000000029f9d0fdebc000a5ae00000000000e98a46e19a400296af80000000003a6ea11cb9b800a5abe082002080136fa14afff400296af80000000001df980eafda800a5abe00000000006fda41e7af200296af80000000002a2580ebfcc800a5abe0000000000a8ca4179ba800296af80000000003e61e0ffaab800a5ae000000000016a934126f6a00296af83983983b83983983b91af2f0eafde60211e30ef6) (by decide +kernel)
private theorem c4 : WideCovered band 9847295 9918300 := wide_block_sound band profiles 9847295 9918300 (wideData 2 0x820020805aee47cf9b000a5abe0e80e80ee0e80e80ee060eabe0ebe4e6c492ee6aba) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 5373897 8515926 9918300 c0 (wide_covered_join band 8515927 8799951 9918300 c1 (wide_covered_join band 8799952 9279244 9918300 c2 (wide_covered_join band 9279245 9847294 9918300 c3 c4))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 14)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 14≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤41)
    (hT0 : 4029≤T) (hT1 : T≤4184) (hnu : 5373897≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤42361603806778530 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R104

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R105
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨14,42,3942,4159,35155338583529093⟩
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨24705,157,5079⟩
  | 3 => ⟨24808,156,5079⟩
  | 4 => ⟨24754,155,5079⟩
  | 5 => ⟨24420,164,5079⟩
  | 6 => ⟨24484,162,5079⟩
  | 7 => ⟨24534,163,5079⟩
  | 8 => ⟨24544,160,5079⟩
  | 9 => ⟨24652,159,5079⟩
  | 10 => ⟨40018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 5504968 8340684 := wide_block_sound band profiles 5504968 8340684 (wideData 16 0xc30048be842eb1b800638760820020800e9a17a3e0018e1e00000000016f740698340018e1d80000000019a283bba000638780000000007ecd0cb3a0018e1d80000000001a2cc08aec0018e1e00000000001e61b01bf5c800638760000000000ae9a8132e800638780000000000fac3c1f89c00638760000000000f3b62060cf70018e1e00000002004f7eb488a6ec20638760820020002b9feb0f5d780818e1e00000000013f7c2f19000638780c30030c0435c641aedb8c020638785d70175c00a4801973e82470ef40f00f00f00f00f00f0078814b3000ef26e60) (by decide +kernel)
private theorem c1 : WideCovered band 8340685 8627845 := wide_block_sound band profiles 8340685 8627845 (wideData 16 0x6bcf40bbcfe0018e1d80000082018e2c078db00018e1e00000000001feeb42833a000638760000030c00bcaf90af8ba0018e1e0208008200bf3c73fd00063876000000000460f01bf798006387800000000046991ac620018e1d80000000013fe4673c000638780000000005f1d18de60018e1d8000000001f8e007adec0018e1e000000000018efe1adf80018e1d80000000001b75d1ab220018e1e00000000001f71b19de20018e1e00000000002e7cc01f3af000638780000020800a4da10a4da40018e1d82f02f03c02e82e83c0babc806d2fce820ffa5bb0) (by decide +kernel)
private theorem c2 : WideCovered band 8627846 8915006 := wide_block_sound band profiles 8627846 8915006 (wideData 16 0x4af901dffc80063876000000000532a01e62d000638780000000005e9b01ee2f800638760000000007a2903979c000638780000000007f2f02962a800638760000000002b9942ae8b800638780000000000b1bf90b3cfe0018e1d82080082002cb10a48a60018e1e0000000000cf6c06697c0018e1d8000000000e8f4065fac0018e1e0000000000fcbc065eaa0018e1d80000000011bb8065fe20018e1e00000000016bac0a58f60018e1e000000000178600699720018e1e0000000001b8e406aab00018e1d82f82f83c02f82f83c12c39907b23ef0210bf6aa2) (by decide +kernel)
private theorem c3 : WideCovered band 8915007 9489328 := wide_block_sound band profiles 8915007 9489328 (wideData 16 0x1cec803b67f800a68ee0000000000a6d60167e240029a3b80000000002eead0492af000a68ee0000000000fb960078ba70029a3b80000000007be1804d2ba000a68ee000000000423cfc078921fc40a68ee0000020807328771f6eb30029a3c02080000008e3dac1de5c3b3c29a3b80000000005b30c0893ab000a68ee0000000001f9a703fcead0029a3b80000000013e79d02825ea50829a3b80000082001ff9dc2dfaa751029a3b82080000001bf582f0638fbe430a68ee0000000002fdc280ad82a9020a68ee0000000001708b9226ab2a420a68f00e20e20f00e20e20f0072ef381c8399762918aa9ea) (by decide +kernel)
private theorem c4 : WideCovered band 9489329 10063650 := wide_block_sound band profiles 9489329 10063650 (wideData 16 0x19adf08b379800a68ee000000000060e701a68300029a3b8000000000d9b8b44e3bb7b3029a3b80000000002cbbe11977e800a68ee0000000000ee9e4634a740029a3b80000000002f73a10e2cc000a68ee000000000121be8679cae0029a3c02080082003a34a5197da800a68ee000000000075b3c267d2a0029a3b80000000002a7280eaf9e000a68ee00000000007eb2422dae20029a3b80000000002e7bb0ecfd8000a68ee0000000000b6a301ffcea0029a3b80000000004962a10afbe800a68ee00000000016183023a8b80029a3c03a03a03c03a03a03c1cab9a0db38dac21296bfae) (by decide +kernel)
private theorem c5 : WideCovered band 10063651 10099545 := wide_block_sound band profiles 10063651 10099545 (wideData 1 0xea0ea0f00ea0ea0f0070d3fc0efa7f32513a2dd72) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 5504968 8340684 10099545 c0 (wide_covered_join band 8340685 8627845 10099545 c1 (wide_covered_join band 8627846 8915006 10099545 c2 (wide_covered_join band 8915007 9489328 10099545 c3 (wide_covered_join band 9489329 10063650 10099545 c4 c5)))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 14)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 14≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤42)
    (hT0 : 3942≤T) (hT1 : T≤4159) (hnu : 5504968≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤35155338583529093 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R105

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R106
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨14,43,3858,4134,26771686375167705⟩
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨24652,159,5079⟩
  | 4 => ⟨24705,157,5079⟩
  | 5 => ⟨24754,155,5079⟩
  | 6 => ⟨24808,156,5079⟩
  | 7 => ⟨24854,154,5079⟩
  | 8 => ⟨24799,153,5079⟩
  | 9 => ⟨24420,164,5079⟩
  | 10 => ⟨24484,162,5079⟩
  | 11 => ⟨24595,161,5079⟩
  | 12 => ⟨24704,160,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 5636039 8085420 := wide_block_sound band profiles 5636039 8085420 (wideData 16 0x689701b4940063ba0000000000077f64625880063b7e0000000000abe7c5f9b00063ba00000000000edde45be880063b7e00000000016cdf4075ff70018ee800000002005ce388c8630018ee8000000800138e29c5d7eac2063ba00820000000e0de50b4d2e0018edf8000000001c96c622b80063ba00000000000629385f5b00063b7e0c30030c0528d301abf67882063ba0145005140077e18e24084b77f0514014501c80cb20088eefe934c04d3006a019c0476ff20b00b0002c02c000e00bc0018edfe40620620f20620620f207de13ff200cfbbeb4) (by decide +kernel)
private theorem c1 : WideCovered band 8085421 8375717 := wide_block_sound band profiles 8085421 8375717 (wideData 16 0x820029baf098a90018ee800000000003e32f01a68e40063b7e000000000072ea50a38200018ee800000000002f3de44fecb43063b7e0820000002ba8b937a9b40818ee800000000001830d01b360018ee800000000001afd81dbe60018ee800000000001d69a08cfb0018edf80000000002b2891a8fe0018ee800000000003ab6b1ed2b0018edf80000000005bb780b9ee0018ee8000000820078ebc4a838cc2063b7e000000000125eb406fcfb0018ee800000000001ba8d41e7cc80063b7e0820000002e896d1bde620018ee802e02e03c82e02e03c95929c06b3ecf020fbb3a36) (by decide +kernel)
private theorem c2 : WideCovered band 8375718 8666014 := wide_block_sound band profiles 8375718 8666014 (wideData 16 0x1eaec533b80063ba0000000000064db84b9f80063b7e00000000006dd383ff900063ba000000000007af7c32da00063b7e0000000000b3ae007abec0018ee800000000003cbcc09ae20018ee800000082002effc13f40063ba00000000000bcbf85e8840063b7e0000030000beb220e2a230018ee802080080014e7fec3d2bac6063b7e00000000077290dcee0018ee8000000000019e7e01b38900063b7e0000000000bf92c3f18aa1c18ee80000000000186df078b8a42063b7e000000000079eb41b0a631018ee802f02f03c82f02f03c8f922b06da6e2029082aa28) (by decide +kernel)
private theorem c3 : WideCovered band 8666015 8956311 := wide_block_sound band profiles 8666015 8956311 (wideData 16 0x42b8018f2d00063ba000000000047ca018ec980063b7e0000000004f7c018bef00063ba0000000000664b01fa2c80063b7e000000000667f01960a00063ba0000000000762d01964c00063ba000000000006297c065d320018ee800000000001a63d019b1d80063b7e000000000072eb4067de00018ee80000008201ba640bade40018edf80000000001abcd41d78c00063ba00000030c007dee907f8e80018edf8208008200293f8428b0a80063ba00000000004eb916b6e0018edf80000000018868067bb00018ee802f82f83c82f82f83c97b2fd06df5a62410ca19fa) (by decide +kernel)
private theorem c4 : WideCovered band 8956312 9518761 := wide_block_sound band profiles 8956312 9518761 (wideData 16 0xb8e2e098649000a6efe0000000002a4f621f6a350029bbf8208008200186af3f6b9db71829bc800000000003a21d03fb59400a6efe00000000017df7836ae400a6efe00000000026ad78062fe5fc30a6efe00000000036eb32064c2abc40a6efe08200208006dce9cc1b2b9750829bbf80000000004df3d01d38b800a6efe0000000000f0cb006cc3a8530a6efe000000000279ae80b8cacc420a6f20000000000622a3a12acede420a6efe0820020800b2f698c2e75bb90829bbf80000000006ca0a07ebdb400a6efe08200208007d8e3e149b4fb00829bbf83803803c83803803c9ce22c07baf8ee4118f89ec) (by decide +kernel)
private theorem c5 : WideCovered band 9518762 10099355 := wide_block_sound band profiles 9518762 10099355 (wideData 16 0xefa3843cdf20029bbf80000000003e33810fa89800a6efe0820020800a9c2d5b0ba80029bc8000000000028e1b09f358800a6efe0000000000a5fa026ed3a0029bbf80000000002fae90e9b0a000a6efe0000000000b3ea0266ae20029bbf80000000003828a08feb9000a6efe00000000012ca203fb8aa0029bbf8000000000be782a9da20029bbf82080082004972c47e61c800a6f200000000000abe64232ef00029bbf800000000029e3a0483d9000a6efe0000000000eae7c235caa0029bbf80000000003e32c02f209800a6efe0e80e80f20e80e80f2063cb6a0bd3afe04129e69b0) (by decide +kernel)
private theorem c6 : WideCovered band 10099356 10280790 := wide_block_sound band profiles 10099356 10280790 (wideData 5 0x2080082013ff576cc660029bbf80000000003962812c67e000a6efe0000000000feaa8623f600029bbf800000000039a1f11a71c000a6efe0ec0ec0f20ec0ec0f20a5e26b11cafdaa413ab4974) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 5636039 8085420 10280790 c0 (wide_covered_join band 8085421 8375717 10280790 c1 (wide_covered_join band 8375718 8666014 10280790 c2 (wide_covered_join band 8666015 8956311 10280790 c3 (wide_covered_join band 8956312 9518761 10280790 c4 (wide_covered_join band 9518762 10099355 10280790 c5 c6))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 14)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 14≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤43)
    (hT0 : 3858≤T) (hT1 : T≤4134) (hnu : 5636039≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤26771686375167705 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R106

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R107
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨14,44,3778,4108,26873055909500298⟩
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨24595,161,5079⟩
  | 4 => ⟨24704,160,5079⟩
  | 5 => ⟨24652,159,5079⟩
  | 6 => ⟨24705,157,5079⟩
  | 7 => ⟨24754,155,5079⟩
  | 8 => ⟨24799,153,5079⟩
  | 9 => ⟨24896,152,5079⟩
  | 10 => ⟨24420,164,5079⟩
  | 11 => ⟨40518,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 5767110 7931177 := wide_block_sound band profiles 5767110 7931177 (wideData 16 0x1969b0ab360018fa980000000002b30d07df3803063ea800000000007a86c229b00063ea60000000000adc7c0b4f80063ea80000000000edffc1ece40063ea600000000016df3c06d8a40018faa00000002004dfde018aff40063ea6000000000125a2c1efa7d0818faa000000800108e9a41927b42063ea6082000000238eed1a2de20018faa00000000001932d09f340018fa985140145018ff7b06a35a240818faa051401450048e8070efe0829f4b84100104003860064d66088fb1e9d74075d00a91d0018fa9e40f40f40f40f40f40f40aa913df400d9f4ab2) (by decide +kernel)
private theorem c1 : WideCovered band 7931178 8224610 := wide_block_sound band profiles 7931178 8224610 (wideData 16 0xef9e4466b80063ea60000000001668f42f0900063ea80000000800e3b242790018fa980000000003ef481df7b0018faa02080080018ab5b46960942063ea8000000000064fb8072afe0018faa000000000019f48149bc0018fa980000000003db5a11b2fb03063ea8000000000079a3c2f2900063ea60000000000abef81e5e80063ea80000000000eaab41c0063ea6000000000161be433f840063ea80000000800a2b283beeb50818fa980000080002ce4942f3eb80063ea8000003000267a3c0f6aad0018fa982e02e03d02e02d83d02926e06e3acfa28f966b3a) (by decide +kernel)
private theorem c2 : WideCovered band 8224611 8518043 := wide_block_sound band profiles 8224611 8518043 (wideData 16 0x820000000b0ae90b792a0018fa980000000001879e01835880063ea8000000000064930073b80063ea6000000000070b247aea00063ea800000000007cc387b0f00063ea80000000000aa9743eb840063ea80000000000ebce85f7d80063ea600000000013e87056bd00063ea80000000801ebcac0aaebb0018fa980000000004c2dc01970c40063ea808200200073396d0e7a6b0818fa98000000000186dd1aa220018faa000000000019f8c19aa40018fa980000000001c31f189be0018faa00000000001f65f16d660018fa982e82e83d02e82e83d17a3dd06de9a6230fde3c2c) (by decide +kernel)
private theorem c3 : WideCovered band 8518044 8811476 := wide_block_sound band profiles 8518044 8811476 (wideData 16 0x1efc801937980063ea60000000000a9ce01e2c80063ea80000000000e2fb02348c0063ea600000000012f9fc6a48c0063ea80000000801a1fa86ecb80063ea80000000001bebbe0bef390018faa0208008001bea1fc58e6e82063ea60000000007b1b0b8ae0018faa000000000019fec0196ce00063ea600000000006cb2417fc80063ea8000000000077cfc3ab0018fa980000000002b3ce018edb00063ea80000000000e3da03b0d40063ea6000000000136b2c7aee80063ea80000000801b3b78073ce30018fa982f82f83d02f82f03d05e34806cb683c410a60cfe) (by decide +kernel)
private theorem c4 : WideCovered band 8811477 9178267 := wide_block_sound band profiles 8811477 9178267 (wideData 16 0x3b2f6c4baac00a7d2e0000000007f28300e7baf0029f4b800000000048e9ca3435939dcf0a7d2e0820020801238e4c9e823da80829f4b80000000001a6d91fb3e0018faa00000000001da9c0297ed80063ea800000000007dcac062cae0018fa98000008200296f9018b2e00063ea8000000000265e418bca80063ea60000000000e99ed0e8f720018faa000000c3001cb5d41e21f00063ea608200208007be6907bfb00018faa0000000001b86c3ff880063ea600000000006382806a8240018faa00000000001968e0cdb00018fa983803803d03803803d1aa36806dfdbe8490ebddf0) (by decide +kernel)
private theorem c5 : WideCovered band 9178268 9765133 := wide_block_sound band profiles 9178268 9765133 (wideData 16 0x17dcac266c220029f4b800000000088acc01b70d800a7d2e00000000006b9e82b8aa20029f4b8000008200fef7806bf0a400a7d2e0820000006bbef54b4a200029f4c00000000004eea802bf9a800a7d2e000000000134a707648710829f4b80000000010cf9d02ae28400a7d2e082002080064c6ad56de4fc20a7d2e0000000000efba417bf000a7d2e00000000017b870167b760029f4b80000000001ce4c02a26ebd0829f4b80000000015be3e03f6a9c00a7d300000020803e9a730e48a7dc20a7d2e082000000726c7b07dcfbf000a7d2e0e40e40f40e40e40f40a0abc80fee38b8291cadfa4) (by decide +kernel)
private theorem c6 : WideCovered band 9765134 10351998 := wide_block_sound band profiles 9765134 10351998 (wideData 16 0x4967a12ca89000a7d2e00000000016abb4663ff80029f4b80000000004c3381282bb800a7d2e082002080076c3563caee0029f4b80000000002cf790ada1b000a7d2e0000000000ed9f43e0d700029f4b80000000002ff9c0b869c800a7d2e0000000000f4c6c377e780029f4b800000000049b2d0faa6f800a7d2e0000000000ffb2427dfec0029f4b80000000003daaf519a38800a7d2e082002080062e2017beb20029f4b80000000002dfe908fb8e800a7d300000000000aeeec131aa20029f4b80000000003ce1908effd000a7d2e0ea0ea0f40ea0ea0f4072f2190bfe5e24492da8968) (by decide +kernel)
private theorem c7 : WideCovered band 10351999 10462035 := wide_block_sound band profiles 10351999 10462035 (wideData 3 0x30c00c3011afc844a3fae91029f4b80000000004962a148f3e000a7d2e0ee0ee0f40ee0ee0f40bfb33e13a3e972493ea2b2a) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 5767110 7931177 10462035 c0 (wide_covered_join band 7931178 8224610 10462035 c1 (wide_covered_join band 8224611 8518043 10462035 c2 (wide_covered_join band 8518044 8811476 10462035 c3 (wide_covered_join band 8811477 9178267 10462035 c4 (wide_covered_join band 9178268 9765133 10462035 c5 (wide_covered_join band 9765134 10351998 10462035 c6 c7)))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 14)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 14≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤44)
    (hT0 : 3778≤T) (hT1 : T≤4108) (hnu : 5767110≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤26873055909500298 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R107
