import ProximityPrize.SubmissionLower.RelativeWideBlocks6815
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R018
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨10,66,3254,3865,29906389501753189⟩
private def profiles : ℕ → Profile
  | 0 => ⟨25314,190,5079⟩
  | 1 => ⟨25360,187,5079⟩
  | 2 => ⟨25449,185,5079⟩
  | 3 => ⟨25484,182,5079⟩
  | 4 => ⟨44518,250,10158⟩
  | 5 => ⟨26531,139,5079⟩
  | 6 => ⟨26596,138,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 8650676 8848870 := wide_block_sound band profiles 8650676 8848870 (wideData 16 0x3ff8ec06bcbe0019b6d8000000000ee628129effc0066db8000000000371b28071afe940066db60000000001b7f7fc198ebef20c19b6e00000000018be6e449e8a65093aea0000000003acd7007aff4013aec00000000043c93c7e7e404ebb000000000179ad857d639804ebb0000000000ceeea05b259c04eba8000000001deb0e58aefd004ebb00000000019bfcb0dbe1c404ebb00000000001cbb9b06ec931013aec00000000057ec754a2cf6013aea00000208016a92ad82f6bda7013aec0000030007fdae9d50969eb1013aec0e00e01380e00be13806086483a0708b2dee010c339b2) (by decide +kernel)
private theorem c1 : WideCovered band 8848871 9165981 := wide_block_sound band profiles 8848871 9165981 (wideData 16 0x1879f2117fef8ac2066db600000000073be20328bf20019b6e000000000019afebc0e682a0019b6d80000000001ee383436c9fd0019b6e00000000003cb2930077b64fc0066db60000000002f0afbec7de18b50019b6e02080082001863cea12ece7e02066db60000000002fcdec0a09290019b6e00000000018c35e01833f3a0019b6d8000000000ebeab17964bc0066db8000000000466a28071c2d840066db60000000005e79b00e8a2ecc0066db600000000007ebfcf02da8feb0019b6d8208008200983a8e5125d35bc2066db80000000004e4f74766d380019b6d83803804e03803804e0e9e2be006f92eb2c010f69d64) (by decide +kernel)
private theorem c2 : WideCovered band 9165982 9483092 := wide_block_sound band profiles 9165982 9483092 (wideData 16 0x7c342ab980066db60000000001fde0aab60019b6e00080002008b382a9d80066db600000000023db0aa7e0019b6e00000000011cf04e60019b6d8000000000be38269d80066db8000000000362b098a00019b6d8000000000f838233e00066db80800020006ea9038e00019b6d830000c001da241e9b40066db80000000004bdc14e80066db6000002080061e701bc9c0066db60000000000b0cbc7acc40066db60800000c0179beeb53ff1a7d0819b6e00000000008da0a01be9840066db60e40e41380e40e41381b796ae18e26ea2191c35832) (by decide +kernel)
private theorem c3 : WideCovered band 9483093 9879480 := wide_block_sound band profiles 9483093 9879480 (wideData 16 0x71ea026fd000adb6e000000000077a3027a8400adb6e0000000000abd2c4b5f400adb6e1040041001e3ea93a8fe2002b6db0000000000cb3426ce80066db600000000033ff0987e0019b6e0000000000ebe02e2880066db60000000003ec90b86c0019b6e00000000010b602e0b80066db60000000003ad909dee0019b6e000000000078e41eb880066db600000000017ae0ae3a0019b6d800000000068642b7f00066db60000000001a7d0adfa0019b6e00000000006ef42a1980066db60e60e61380e60e613806fba6904e27a24212920b20) (by decide +kernel)
private theorem c4 : WideCovered band 9879481 10513701 := wide_block_sound band profiles 9879481 10513701 (wideData 16 0x53e8018b2d800adb6e000000000079901b73f800adb6e0000000000f7a018ea9800adb6e0820020803f3f019f3a800adb6c000000000732f018a3d800adb6e0000000006f5d189e8002b6db8000000000187cf0187cd800adb6e00000000006283c5b3e000adb6c0000000002a5d0187ab000adb6e0000000001e29018aee000adb6e00000000037f9149a4002b6db80000000006aa4063a26002b6db82080082013cb442de800adb6e000000000067f244ec8000adb6e00000000006ef24474d000adb6e0ea0ea1380ea0ea138073a67b05a6be64212f6da3c) (by decide +kernel)
private theorem c5 : WideCovered band 10513702 11147922 := wide_block_sound band profiles 10513702 11147922 (wideData 16 0x7aa901eb4f000adb6e0000000007bce01e7ed800adb6e000000000061f3407ff20002b6db80000000003ae0076e76002b6db02080082008f7407cfbe002b6db8000000001bda4073b20002b6db8000000001a92806cb3e002b6db8000000001e82c074da6002b6db0000000001c96c06bf6e002b6db80000000018e30075ffe002b6db80000000009d01de6e000adb6e0820020801e5f01ab7e000adb6e0000000006b6d01ae19000adb6e0000000006608018ada800adb6e000000000773c01aefa000adb6e0ee0ee1380ee0ee13807dfbfa05e37876214923ff6) (by decide +kernel)
private theorem c6 : WideCovered band 11147923 12297448 := wide_block_sound band profiles 11147923 12297448 (wideData 16 0x820020800e9cb432bd3e004ebae80000000004bb7909a7f90013aebc000000000131e7c23dfea004ebae80000000003c77c08d3380013aebc08200208006e9a41e99e8004ebaf000000000049fed07d33a8013aebc0000000000fdc6c16cca0004ebae80000000004b68b04e32d0013aebc0000000000b5c780fdbec004ebaf00000000001e35802c7dd8013aebc082002080075b78123ba4004ebae830c00c3009fb5e04dfdcc013aebc20800820013ac340afcb9c8013aebc08200208016dc02aa99000adb6e0000000006e6f01d73d000adb6e0f20f21380f20f21380a9abad06caef3a215abadb0) (by decide +kernel)
private theorem c7 : WideCovered band 12297449 13565890 := wide_block_sound band profiles 12297449 13565890 (wideData 16 0xc30030c004db7afd42aa79084ebae8000000001bf6ae02aaee22004ebaf02080082014fa1d01fb2bb2004ebae80000000012bb7f01c34974004ebaf00000000010d7bb01af4fb2004ebaf0208008200beb9b0193bb7a004ebaf0000000000bf3291ed38d8013aeba000000000327e3c7f1962004ebaf0208008200886ad1a8e8a0013aeba000000000226fb453297e004ebaf00000000007eef913af2c8013aeba0000000001fdd244e9b34004ebaf02080082004e2c911bbc80013aebc00000000017aaa4375c68004ebaf00000000005dfac0d8bcf8013aeba1201201381201201381229edb0be3cd2e217ceda6c) (by decide +kernel)
private theorem c8 : WideCovered band 13565891 13724445 := wide_block_sound band profiles 13565891 13724445 (wideData 2 0x11e25914870f4213aeba1341341381341341381a3a2eb18da58aa29a83ade0) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8650676 8848870 13724445 c0 (wide_covered_join band 8848871 9165981 13724445 c1 (wide_covered_join band 9165982 9483092 13724445 c2 (wide_covered_join band 9483093 9879480 13724445 c3 (wide_covered_join band 9879481 10513701 13724445 c4 (wide_covered_join band 10513702 11147922 13724445 c5 (wide_covered_join band 11147923 12297448 13724445 c6 (wide_covered_join band 12297449 13565890 13724445 c7 c8))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 10)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 10≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤66)
    (hT0 : 3254≤T) (hT1 : T≤3865) (hnu : 8650676≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤29906389501753189 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R018

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R019
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨10,67,3208,3773,31386533365713811⟩
private def profiles : ℕ → Profile
  | 0 => ⟨25314,190,5079⟩
  | 1 => ⟨25360,187,5079⟩
  | 2 => ⟨25449,185,5079⟩
  | 3 => ⟨25484,182,5079⟩
  | 4 => ⟨44518,250,10158⟩
  | 5 => ⟨26531,139,5079⟩
  | 6 => ⟨26596,138,5079⟩
  | 7 => ⟨26584,136,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 8781747 9101993 := wide_block_sound band profiles 8781747 9101993 (wideData 16 0xa6a7ff19b69d800678be00000000006cbe2f83eb5cb10019e2f82080082008e649ef06de64f420678be0000000004aae247a59f40019e38000000000089f6a10ab9f400678be000000000523d28421ebe0019e3800000000009e37c01cbdc6f0019e2f8000000001b977c12ee3dc00678e0000000000522cac166b72cc00678be0820020801e0dfeb44c7eca10819e380000000000ebeac13f78c000678be00000000033eeec268eb00019e380000000000bae4804c3ebc00678be000000000270fe85f9a670019e3800000000007925b01da1a3f0019e2f83803804e83803804e8ca2a93c071c74ce0010e66fa4) (by decide +kernel)
private theorem c1 : WideCovered band 9101994 9422239 := wide_block_sound band profiles 9101994 9422239 (wideData 16 0x800000079b4365b000678be0000000803edc03fb00019e2f80000000012bec0acf800678be0000000005b5a0bf800678e000000000073be02d710019e2f800000000019b1e07b6b0019e380000008001bfa8173b000678be0000000000aada0632dc00678e0000003080121e24077e730019e2f82000083005db28754f8ae7b420678be0000000001ac92c0e4cbd0019e2f80000000006ea1808e3dcc00678e00000000001f2e7446aefd0019e2f8000000001df33f468628bd0819e3800000000019d2b805e7b8c00678be0e40e413a0e40e413a1a4de691fd2b9b8111b38b72) (by decide +kernel)
private theorem c2 : WideCovered band 9422240 9742486 := wide_block_sound band profiles 9422240 9742486 (wideData 16 0x2080082003838371e000678be0000000002f4d09b2a0019e2f8000000000ca602678800678be00000000033fe098660019e380000000000de7c23ba000678be000000000423e0d97e0019e380000000000ff24233f800678be000000000464b08b660019e3800000000006f34224e000678be0000000001e9907eb60019e3800000000005cbc2f69000678be0000000001e8b098ae0019e3800000000008f341e1a000678be000000000279f06ca20019e380000000000afb017ed000678be0e60e613a0e60e613a06ab7ba04d7fef0212829f3e) (by decide +kernel)
private theorem c3 : WideCovered band 9742487 10382979 := wide_block_sound band profiles 9742487 10382979 (wideData 16 0x208008200ad74060d68002ba5f0000000001bfec0639b2002ba5f8000000001baa46689000ae97e0000000007a4d189e8002ba5f8000000000196df018e19000ae97e000000000437c16e30002ba5f8000000000daa4566c000ae97e0000000001ada018ed9000ae97e00000000042d812e32002ba5f00000000014f303f0c000ae97e08200208047591efb6002ba5f80000000001afe9038bc002ba5f80000000001e66f07eb6002ba5f000000000029f0805a7d002ba5f830000c0008e2aa03efcf400ae97e0ec0ea13a0ec0ea13a06296bb05af5da4212d62bea) (by decide +kernel)
private theorem c4 : WideCovered band 10382980 11023472 := wide_block_sound band profiles 10382980 11023472 (wideData 16 0x7b7c0a2c36002ba5f02080082005b6807696e002ba5f800000000188e006cfe4002ba5f8000000001be70075dec002ba5f8000000001a83006d9ac002ba5f8000000001b9f006daba002ba5f8000000001ba60077d68002ba5f8000000001ab01bb3c800ae97e08200208077006ec78002ba5f00000000019eb406ca7a002ba5f80000000018aa0063dbe002ba5f8000000001bd68069be8002ba5f8000000001ceb4067b7a002ba5f0000000001a87c063ee2002ba5f80000000001c01be9c000ae97e0ee0ee13a0ee0ee13a077b6bf05cadc24213f25ba4) (by decide +kernel)
private theorem c5 : WideCovered band 11023473 12064273 := wide_block_sound band profiles 11023473 12064273 (wideData 16 0x137c3426cf72004f2bf0208008200cde01faeb2004f2be80000000003ae6805cbdc0013cafc0000000000fc83c17dbfc004f2be80000000004afbd05b2ae8013cafc00000000012edf0079a38004f2be800000000048a3c02f3788013cafc0000000001619600f4d8013cafc0000000007b3ee44bbafd004f2bf08200208017f3cd43966eea004f2be82080082019d42a77d000ae97e0000000006edf01ee0d800ae97e0000000006b7901de18000ae97c0000000007ae802827d800ae97e00000000072bb01defa000ae97e0f20f213a0f20f213a0a18b1906aa49622158e8b3e) (by decide +kernel)
private theorem c6 : WideCovered band 12064274 13345259 := wide_block_sound band profiles 12064274 13345259 (wideData 16 0x11cbb901c6cfe8004f2bf00000000010af8c01b78d7e004f2be8208008200ce6fd01a7bce2004f2bf0000000000bf2b90183abe4004f2be80000000009fe9e1b82aa0013cafc0000000002aece0729828004f2be82080082006bbdf17ae8c8013cafc0000000001bf8ec4a5822004f2bf00000000007ca2813d7bd0013cafc082002080138da44aad2e004f2be80000000005e6680ed60b8013cafc0000000001609b02fdbba004f2be80000000005dbbb0dce1a8013cafc0820020800ad87c325fb8004f2be80000000003ea5e0896a88013cafc0fe0fe13a0fe0fe13a0ee8e9f0adb5f22217967b3e) (by decide +kernel)
private theorem c7 : WideCovered band 13345260 13905690 := wide_block_sound band profiles 13345260 13905690 (wideData 7 0x36cbf4060ab3bc013cafa08200208007bd24943ebfaad084f2bf030c00c3001ae68f87769ad004f2be8208008200ef750a28b5a4213cafc30c00c3000f9ce2b5c93ea8213cafa000000000734b3c0b1da9c0013cafc12812813a12812813a222afed18971a32219cedab2) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8781747 9101993 13905690 c0 (wide_covered_join band 9101994 9422239 13905690 c1 (wide_covered_join band 9422240 9742486 13905690 c2 (wide_covered_join band 9742487 10382979 13905690 c3 (wide_covered_join band 10382980 11023472 13905690 c4 (wide_covered_join band 11023473 12064273 13905690 c5 (wide_covered_join band 12064274 13345259 13905690 c6 c7)))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 10)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 10≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤67)
    (hT0 : 3208≤T) (hT1 : T≤3773) (hnu : 8781747≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤31386533365713811 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R019

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R020
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨10,68,3164,3341,30456977089708927⟩
private def profiles : ℕ → Profile
  | 0 => ⟨25360,187,5079⟩
  | 1 => ⟨25449,185,5079⟩
  | 2 => ⟨25484,182,5079⟩
  | 3 => ⟨25564,180,5079⟩
  | 4 => ⟨44768,250,10158⟩
  | 5 => ⟨26531,139,5079⟩
  | 6 => ⟨26596,138,5079⟩
  | 7 => ⟨26659,137,5079⟩
  | 8 => ⟨26644,135,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 8912818 9236200 := wide_block_sound band profiles 8912818 9236200 (wideData 16 0x1d2990492cbc0067be6000000000075be0271dfd0019ef980000000001e25f11cbdb40067be600000000036afe51e0a27cc2067be8000000000262aa87b193a0019ef98000000000896dd1af6fd40067be80000000003fdb7432ab7e0019ef980000000018dfa903c26c310019efa02080082002e21dbd0a4abd942067be60000000000f893c268c260019efa00000000004ee9e0eef9f00067be6000000000161ee01bf9360019efa00000000005c2ee049e2b40067be60000000001af838574d3d0019efa000000000078fe802b62daf0019ef983883884f03883884f02a66d78067b65eea011867aaa) (by decide +kernel)
private theorem c1 : WideCovered band 9236201 9559582 := wide_block_sound band profiles 9236201 9559582 (wideData 16 0x2080082001b312b6880067be60000000001b790e800067be6000000000221b05a680019ef980000000008be00a0d40067be80000000002a7f039e40019ef98000000000b9601769c0067be8000000000377d04a40067be600000000042aa029b90019efa00000000001c3ebf14ab9f8d42067be60000000000bcdb47fdc40067be60000000000eca681b09230019ef980000000002c33a01a708650019efa02080082015a3ca48fbad02067be6000000000075e28167cee0019efa00000000001d38f02eb8c00067be60e40e413c0e40e413c0a597fe18861ff6111d3ef78) (by decide +kernel)
private theorem c2 : WideCovered band 9559583 9882965 := wide_block_sound band profiles 9559583 9882965 (wideData 16 0x4b6033c900067be6000000000127d08cac0019ef980000000004fac33af80067be6000000000167d0cbec0019efa000000000059fc230e00067be60000000001a3b0cf3c0019efa000000000069241f4e80067be60000000001e7a0cf6a0019efa00000000007b681e2980067be600000000023a80cfe40019efa00000000004bf81abe00067be6000000000129a4d82e0019efa00000000017e488300019ef9800000000038292b0e00067be800000000017ff4db720019ef983a03a04f03a03a04f0dbaeb04da8da8212a36c64) (by decide +kernel)
private theorem c3 : WideCovered band 9882966 10529730 := wide_block_sound band profiles 9882966 10529730 (wideData 16 0x23791ff3e002bbeb00000000009bf07f0d000aefae0000000002aec1f8f6002bbeb8000000000bdbc7b8e800aefae00000000036c81eb3c002bbeb8000000000adf07a38800aefae0000000002b4e5de7e002bbeb82080082005ff5063e66002bbeb8000000000b9e04ece800aefac00000000033890ed64002bbeb8000000000f9742e99000aefae0000000004b4f06ce0002bbeb80000000017f68329002bbeb0000000000182ce0ba77002bbeb80000000001bec81ebb3002bbeb83b03b04f03b03b04f0b93cf05ab5932212f75cf8) (by decide +kernel)
private theorem c4 : WideCovered band 10529731 11176494 := wide_block_sound band profiles 10529731 11176494 (wideData 16 0x2080082001e780778e4002bbeb00000000008bb0073eba002bbeb80000000008df0073f7e002bbeb80000000009d28079ca0002bbeb80000000009fb407996a002bbeb0000000000a864075ce0002bbeb800000000059a5076c28002bbeb82080082004d7406bd7e002bbeb800000000088ac06a830002bbeb00000000008bf006a864002bbeb80000000008fec06a932002bbeb80000000009ce006ab72002bbeb8000000000aaf406aef8002bbeb00000000001da8073a7e002bbeb820800820068a906ad36002bbeb83b83b84f03b83b84f11fab905cfad78214964eb2) (by decide +kernel)
private theorem c5 : WideCovered band 11176495 12227487 := wide_block_sound band profiles 11176495 12227487 (wideData 16 0x820020804b4c0bca2c8013df3c000000000065e7c1e4fa2004f7ce800000000019eaf06cb498013df3c00000000006ab7417e82c004f7ce80000000001cbeb06862a8013df3c000000000376806c3ed8013df3a08200208013a802b38a0013df3c000000000069e741b19c013df3c0c30030c0436ea02f8c7b004f7cf0a28028a00caa4843821baa004f7ce80000000009e280a49fc002bbeb80000000009b7007f9e2002bbeb80000000009d3c07fab8002bbeb00000000009fa007fd7a002bbeb8000000000aa680a09a4002bbeb83d03d04f03d03d04f14e76a06b36c24215b3486a) (by decide +kernel)
private theorem c6 : WideCovered band 12227488 13521017 := wide_block_sound band profiles 12227488 13521017 (wideData 16 0x1eede80a2ca5a8013df3c0000000001e4cbc07fdb2e8013df3a08200208012ece006e8e6d8013df3c00000000012eda8066faec8013df3a0000000001238e4063baac8013df3c0820020800bdbec7efc2e004f7ce80000000003a6281c975a0013df3c0000000000b9bbc5ec964004f7cf00000000002d7a816832c0013df3c08200208006de3447fabe004f7ce80000000002867a10a22c8013df3c0000000000a6ff8473ca6004f7ce82080082001867f0eba3c8013df3c000000000070c242e79fe004f7ce80000000001c2de0ad6fb8013df3c12012013c12012013c0648f6c0b8f6bec217be7dba) (by decide +kernel)
private theorem c7 : WideCovered band 13521018 14086935 := wide_block_sound band profiles 13521018 14086935 (wideData 7 0x13ea345b0a3f004f7ce82080082015d768458309ef084f7cf00000000005ffdf11eb3ac013df3a000000000326f644fbd6b084f7cf02080082014d38d41c60a3f084f7ce8000000000bcb190fba3b4013df3c13413413c13413413c078cb4e1bfa5a36299fa692c) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8912818 9236200 14086935 c0 (wide_covered_join band 9236201 9559582 14086935 c1 (wide_covered_join band 9559583 9882965 14086935 c2 (wide_covered_join band 9882966 10529730 14086935 c3 (wide_covered_join band 10529731 11176494 14086935 c4 (wide_covered_join band 11176495 12227487 14086935 c5 (wide_covered_join band 12227488 13521017 14086935 c6 c7)))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 10)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 10≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤68)
    (hT0 : 3164≤T) (hT1 : T≤3341) (hnu : 8912818≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤30456977089708927 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R020

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R021
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨11,46,4298,4349,9161968566745543⟩
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨33072,8,10160⟩
  | 2 => ⟨40768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 6029255 9483627 := wide_block_sound band profiles 6029255 9483627 (wideData 16 0x7db01df6f800a0efe0000000000a6c02876e800a0efe082002080073941d29a000a0efe000000000070901b21f800a0efe000000000078f01da6e800a0efe000000000074801b609800a0efe000000000076a01b6ef000a0efe0000000000a1a01e6fb800a0f2000000000007d901bf59800a0efe0000000000a1a01c3b8000a0efe0820020800abe41cf5f800a0efe3cf00f3c013e9e81bd8ed9820a0efe186006180060e02f38902223bfa34d00d3400b80ad0109bfc8e38038e001a02b80060b7f903903903c83903903c8bd15e3800fc77e3c) (by decide +kernel)
private theorem c1 : WideCovered band 9483628 10280790 := wide_block_sound band profiles 9483628 10280790 (wideData 15 0x1ffd06c72c00121dfc000000000264806d2ce80121dfc082002080135f43a37c00121dfc0000000001a7e03ee3d00121dfe0000000001e5a03ab0d80121dfc00000000023bf02c70a00121dfc0000000002a0802da1a40121dfc00000000052e903fbf840121dfe1860061804fd0ade2e980121dfc0820020806ed07f9f600283bf80000000001cfc074c3e00283bf80000000001f2c07ede400283bf80000000001db8075ae200283bf80000000001e2c075e6c00283bf83883883c83883883c85bb2807d2fcb211293bcb6) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6029255 9483627 10280790 c0 c1)
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 11)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 11≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤46)
    (hT0 : 4298≤T) (hT1 : T≤4349) (hnu : 6029255≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤9161968566745543 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R021

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R022
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨11,47,4215,4324,9396426721297806⟩
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨41018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 6160326 9319394 := wide_block_sound band profiles 6160326 9319394 (wideData 16 0xf0801afbe000a1d2e0000000000f5901b2da800a1d2e0000000000fbd01b659800a1d2e000000000123d01ba58000a1d2e00000000012d901bebd800a1d2e0000000000b7d01c618000a1d30082002080136d41a3b8800a1d2e0000000000f6c01b2ad800a1d2e0000000000f0a01931f800a1d2e0000000000f8801961d800a1d2e000000000121e01976a000a1d2e00000000012df019b48000a1d2e145005140278c2c1b18a7c020a1d2e00000000053c6a59020a1d304d30134c04f8360c02060ea7903d03d03d03d03d03d19815c2400fee8e38) (by decide +kernel)
private theorem c1 : WideCovered band 9319395 9924322 := wide_block_sound band profiles 9319395 9924322 (wideData 16 0x1aafb81ee9e50048e8f08200208005c68e42b24bfe0048e8f0000000000493007df3a002874b80000000004e740a9c32002874b80000000004b7c07ff28002874b80000000004cec0a192e002874c02080082002b7107be36002874b80000000003c6c073b22002874b80000000003d60073e2c002874b80000000003e300749fa002874b80000000003f68074fa4002874b800000000048b8075eae002874b80000000004a68076f62002874b800000000038e80a4af8002874c02080082002b3d06dfe4002874b83803803d03803803d0b8be907929bb8191ebbcb2) (by decide +kernel)
private theorem c2 : WideCovered band 9924323 10462035 := wide_block_sound band profiles 9924323 10462035 (wideData 8 0x208008200482c235da20048e8f0000000000cea4161b6c0048e8f0000000000dbac134c280048e8f0000000000edfc1289660048e8f000000000118600f89f60048e8f00000000019ce41a2b600048e8f0000000001dff40b4a6a0048e8f03b03b03d03b03b03d0d9f380a86582619387ade2) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6160326 9319394 10462035 c0 (wide_covered_join band 9319395 9924322 10462035 c1 c2))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 11)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 11≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤47)
    (hT0 : 4215≤T) (hT1 : T≤4324) (hnu : 6160326≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤9396426721297806 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R022

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R023
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨11,48,4136,4299,9718602346092229⟩
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨33072,8,10160⟩
  | 4 => ⟨41018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 6291397 9113322 := wide_block_sound band profiles 6291397 9113322 (wideData 16 0x2080082007c6d06bb600028acf80000000004ff0062ca00028acf80000000004ff07afb800a2b6000000000017ce019a48800a2b3e0000000001ace019bed000a2b3e0000000001e0e01a22b800a2b3e0000000001faa01a72d000a2b3e00000000022a901af3e800a2b3e000000000433a5e9e40028acf82080082005bac76bd000a2b3e00000000017ed1dbbc0028ad8071c01c700e9748069afaf20828acf871c01c7002834073d7e0828acf8514014500182c67af82124e7c0000000003fc33dc82229cfa0ec0ec0f60ec0ec0f606ce1592a010939e34) (by decide +kernel)
private theorem c1 : WideCovered band 9113323 9657307 := wide_block_sound band profiles 9113323 9657307 (wideData 16 0x20800820038ed0a392e0028acf80000000005c38074e280028acf80000000005da00759fa0028ad800000000005f28075efe0028acf80000000005cb406fc740028acf800000000068f4073fae0028acf80000000006da8078cf20028acf800000000078e007a9bc0028acf82080082006a2d074fe60028acf800000000059fc06ce6c0028acf80000000005be406daba0028acf80000000004fe8063d660028acf8000000000687006ec320028acf80000000006ba806fd640028acf80000000006fa00719240028acf83803803d83803803d8fc20a06e21ebc211ba9ef2) (by decide +kernel)
private theorem c2 : WideCovered band 9657308 10575282 := wide_block_sound band profiles 9657308 10575282 (wideData 16 0x6b1907e38b80124e7c00000000072f807e3e800124e7c0000000006a9d05c78a00124e7c0820020801b7b45e77e80124e7c0000000005b180583fe80124e7c0000000005efa03f6bf80124e7c0000000006a2902b7ca00124e7e000000000066d2c0e5e60004939f00000000001ee6e01dbfc80124e7c0000000000ecfe82a7bef004939f08200208002eeea42cabc7e004939f80000000006a3c07eff40028acf80000000006bac07fcfc0028acf80000000006d340a0bae0028acf80000000006870076aa40028acf83903903d83903903d91eefa07c7fdb8212bf0ab4) (by decide +kernel)
private theorem c3 : WideCovered band 10575283 10643280 := wide_block_sound band profiles 10575283 10643280 (wideData 1 0x3b83b83d83b83b83d9bc2980bce4e60214a73d60) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6291397 9113322 10643280 c0 (wide_covered_join band 9113323 9657307 10643280 c1 (wide_covered_join band 9657308 10575282 10643280 c2 c3)))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 11)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 11≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤48)
    (hT0 : 4136≤T) (hT1 : T≤4299) (hnu : 6291397≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤9718602346092229 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R023
