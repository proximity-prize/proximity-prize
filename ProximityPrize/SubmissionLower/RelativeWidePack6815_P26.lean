import ProximityPrize.SubmissionLower.RelativeWideBlocks6815
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R156
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨7,68,4061,4062,15999661226366636⟩
private def profiles : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨44768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 8912821 9889542 := wide_block_sound band profiles 8912821 9889542 (wideData 16 0x603e6e800a6d3e0000000000603b2d000a6d3e00000000006837ac800a6d3e00000000006c33aa000a6d3c00000000007c2f1a800a6d3e0000000000a4279f000a6d3e0000000000b01e9f800a6d3e0000000000f80ed8800a6d3e0000000001640e2b400a6d3e00000000022c3ee9c00a6d3e20828820a325b56c7ee7d0829b4f80000000007be43e4ff390012da7a0000000003a9e5de619e5004b69f0000000000fe34060bb5af8008eb3e02080082001c640e8f3a98023acf60be0be12c0be0be12c0e4d06cbbdaa011a3abe0) (by decide +kernel)
private theorem c1 : WideCovered band 9889543 10468339 := wide_block_sound band profiles 9889543 10468339 (wideData 16 0x61c9ba0029b4f80000000018733b800a6d3e000000000060764d800a6d3e08200208006d6e68000a6d3c000000000616cb80029b4f800000000185b2a800a6d3e000000000616cee0029b4f800000000185b5f800a6d3e000000000616e760029b4f80000000001816ff80029b4f8000000001c5e9b000a6d3e0000000000685f5d800a6d3c0820020800a956b9800a6d3e000000000610d280029b4f80000000018427d800a6d3e0e80e81360e80e81360abd059e39b2092f7a968) (by decide +kernel)
private theorem c2 : WideCovered band 10468340 11445060 := wide_block_sound band profiles 10468340 11445060 (wideData 16 0x2902bbfc8012da7c0000000000ac0accea004b69f00000000002c02aa7e8012da7c0000000000b80a7d32004b69e82080082001d428fed8012da7c0000000000a8068ff6004b69e80000000002c1dff8004b69f00000000003a0cdec004b69e80000000004b11f6f004b69f030c00c3004de31f5869004b69f08200208004e7a06aba0f0012da7c08200208075fb700029b4f000000000186ebe000a6d3e00000000061bbea0029b4f800000000146f4e800a6d3e0ec0ec1360ec0ec1360b3e05cbdda2094864d24) (by decide +kernel)
private theorem c3 : WideCovered band 11445061 12602655 := wide_block_sound band profiles 11445061 12602655 (wideData 16 0xf81a9ea2004b69f00000000003b069ebb8012da7c0000000000f41a68a6004b69f02080082001e05b71a0012da7a0000000000e01638bc004b69f000000000038058a3e8012da7a0000000000e4162a34004b69f02080082001904a36f0012da7a0000000000b012486e004b69f00000000002d048f7f0012da7c0000000000bc124c38004b69f020800820100eee70004b69e80000000002a03a65b0012da7c0000000000b00e8cb6004b69f00000000002c03a3ce8012da7c0f80f81360f80f81360ec907a7acb0095fbefa2) (by decide +kernel)
private theorem c4 : WideCovered band 12602656 13543200 := wide_block_sound band profiles 12602656 13543200 (wideData 13 0x22c423c30004b69e82080082006d0f8bb88012da7c0000000001b833eaea004b69e80000000006d0cbec90012da7c0000000001ac322cb8004b69e82080082004d0ad7af0012da7c00000000016427bce8004b69f00000000005a09cf9a8012da7c0820020800f82699a8004b69e80000000004b07f67a0012da7c0000000001281f88f8004b69f00000000004907d2cc0012da7c120120136120120136135a09da68b0098973ef8) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8912821 9889542 13543200 c0 (wide_covered_join band 9889543 10468339 13543200 c1 (wide_covered_join band 10468340 11445060 13543200 c2 (wide_covered_join band 11445061 12602655 13543200 c3 c4))))
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
private def profiles : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨45018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 9043892 9811796 := wide_block_sound band profiles 9043892 9811796 (wideData 16 0xb9d078ae0029edb80000000003ff82bcec00a7b6e0000000001b4b06f230029edb8000000000ceec7b5a400a7b6e1040041007a9b49ef2f000a7b6e0000000002f813fe80063db600000000036c1e0a80063db60000000003ac1bc980063db60000000003f41b8980063db80000000004601b3980063db618630618c3f0cbd06cc7cd7d0818f6e00000000008e2ed19c38ff80029edb80000000004a22d0cb278f2004bbaf00000000008ff3f5af66c3d004bbaf00000000009cbb81caaddbe008f75d83803804b03803804b03aada0a8e0ea4011c3dc3e) (by decide +kernel)
private theorem c1 : WideCovered band 9811797 10396865 := wide_block_sound band profiles 9811797 10396865 (wideData 16 0x13819fb60029edb80000000012913dfe0029edb80000000015f1ab740029edb8000000001891affe0029edb82080082001ab96789800a7b6e0000000003b837cd800a7b6c00000000047c4eae000a7b6e0000000004ec4e3f000a7b6e0000000005684bd9800a7b6e0000000005602e0e000a7b6c0000000006ac47ae800a7b6e0000000007a846ed800a7b6e000000000063a10fe80029edb800000000019e016da000a7b6c00000000007480eaba0029edb83a83a84e03a83a84e01b7dc0596ae66092e638b6) (by decide +kernel)
private theorem c2 : WideCovered band 10396866 11091634 := wide_block_sound band profiles 10396866 11091634 (wideData 16 0xb1b07cb1004bbae8000000000496c169a4012eebc186006180771062c3de8012eebc000000000530065ebc0029edb82080082011e5f9a00029edb8000000000eb19bbe0029edb00000000010e1ed600029edb80000000011b1efa60029edb8000000001291fab20029edb80000000011919eb60029edb000000000149018258000a7b6e000000000064060f2e0029edb82080082008859f200029edb8000000000eb1497a0029edb00000000010e19c320029edb83b03b04e03b03b04e01e2cf05bbbda0093f39e70) (by decide +kernel)
private theorem c3 : WideCovered band 11091635 12261773 := wide_block_sound band profiles 11091635 12261773 (wideData 16 0x7ae04a24e8012eeba0000000000a2e04ee7d8012eebc00000000007de049a4e8012eebc0820020805ec12fd6c004bbaf00000000001ce00eacb0004bbae80000000001ef40fdb2c004bbaf00000000001dfc0e897e004bbaf02080082009e03eb1e0012eebc00000000006da02bb9f0012eeba000000000076f0383880012eebc000000000074c02a3588012eebc0000000000a3a02fbd88012eebc000000000076e0287ef8012eeba082002080060a4283ba8012eebc000000000073c1ecbc004bbae83d83d84e03d83d84e02930d06f6bbfe095a6e9a0) (by decide +kernel)
private theorem c4 : WideCovered band 12261774 13431911 := wide_block_sound band profiles 12261774 13431911 (wideData 16 0x4ee0365b32004bbae82080082003ca03208b4004bbaf00000000003fac2b4e38004bbaf000000000049a42e9bac004bbaf02080082002da026ceaa004bbae80000000003bbc268a32004bbaf00000000003930227c70004bbae80000000003b6023dc20004bbaf02080082001e301bbd2e004bbae80000000002ebc1eba7e004bbaf00000000002cbc1b0e66004bbaf02080082001e6c1bef62004bbaf0000000000296416ba22004bbae80000000002b3c17eba8004bbaf000000000029ac167c6a004bbae83f83f84e03f83f84e02ee0808cb8a64097c3bcf6) (by decide +kernel)
private theorem c5 : WideCovered band 13431912 13724445 := wide_block_sound band profiles 13431912 13724445 (wideData 4 0x6bf447f8b6004bbae82080082005b7046bbe0004bbaf000000000059a43a8d3e004bbae84984984e04984984e04b6ca0d8389f2099e2986a) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 9043892 9811796 13724445 c0 (wide_covered_join band 9811797 10396865 13724445 c1 (wide_covered_join band 10396866 11091634 13724445 c2 (wide_covered_join band 11091635 12261773 13724445 c3 (wide_covered_join band 12261774 13431911 13724445 c4 c5)))))
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
private def profiles : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨45018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 9174963 9803262 := wide_block_sound band profiles 9174963 9803262 (wideData 16 0x17b907cbc002a25f80000000008b7c568bc00a897c0000000003b5f13e29002a25f841001040019a9949f21b000a897e000000000530174d000648be0000000005f8227c800648e00000000006201a1d800648be00000000066c161f800648be0000000006f4137a800648be0000000007f41e0a800648e0000000000062805eb6001922f8618e186394f6af5fcbd9ad08192380000000000acafc10a7ef24002a25f80000000006a6dc09db0a2c004c2be8000000000aba8d50d3df2f004c2bf03803804b03803804b1192081b83d9f8011e60cbc) (by decide +kernel)
private theorem c1 : WideCovered band 9803263 10394603 := wide_block_sound band profiles 9803263 10394603 (wideData 16 0x19346b9a000a897e000000000063b14cfc002a25f00000000001ab46ede800a897e00000000006ab14da0002a25f80000000014d1cce8002a25f820800820029e5426d000a897c000000000062f149a8002a25f8000000000187c36bc800a897e000000000069b13caa002a25f80000000001a742f58000a897c000000000073e12d38002a25f80000000001dac266c800a897e0000000000a5f119bc002a25f80000000002ba0168a800a897e0000000000e8d0eb66002a25f83a83a84e83a83a84e82d3af058f4966092e3397a) (by decide +kernel)
private theorem c2 : WideCovered band 10394604 11096821 := wide_block_sound band profiles 10394604 11096821 (wideData 16 0x13cd01869004c2bf000000000078f806f9ed004c2bf06180186004f4193da6c004c2be800000000018f4060e7a002a25f8208008201ee418e19800a897e0000000006fc6aac800a897c00000000006091fca0002a25f8000000001ea1ab6c002a25f800000000018bc06096a002a25f800000000018606b7f000a897c000000000066f01864d000a897e000000000065b1bba0002a25f82080082001ce17788800a897e0000000006f4560c800a897e000000000060d1ab76002a25f83b03b04e83b03b04e83a62e05b36e6c093f36934) (by decide +kernel)
private theorem c3 : WideCovered band 11096822 12279503 := wide_block_sound band profiles 11096822 12279503 (wideData 16 0x2080082001c6c1329f0004c2bf00000000003d7c12f8f0004c2bf00000000003e7012ebfa004c2be80000000003da412f87a004c2bf0208008201cd03cedd00130afa0000000000e8b03c3af80130afc0000000000ede03c20a00130afa0000000000f6903c22a00130afc0820020802310e0864004c2bf00000000002fbc0b3a78004c2bf000000000039bc0b0a38004c2be80000000003cec0ad96a004c2bf000000000049bc0a9bfc004c2be82080082002d610a1b60004c2bf000000000039640668aa004c2be83d83d84e83d83d84e8482ff06ef7fbe095a79ee6) (by decide +kernel)
private theorem c4 : WideCovered band 12279504 13462185 := wide_block_sound band profiles 12279504 13462185 (wideData 16 0x9cf837d8b0004c2bf0208008200792c332ab6004c2bf00000000007eb42e7cb4004c2be80000000007d3c2bcce2004c2bf00000000007c342b3cfa004c2be82080082004da423dca0004c2bf000000000069b8235bbc004c2be8000000000693c230866004c2bf0208008200482c1fbd7e004c2bf000000000058f81bfb72004c2bf000000000058e81bbeae004c2be8000000000592c1b9dba004c2bf02080082002d2417e832004c2be80000000004a60172ba8004c2bf00000000004ab8170f20004c2be83f83f84e83f83f84e85ae5a08c6dc6a097c7fe3a) (by decide +kernel)
private theorem c5 : WideCovered band 13462186 13905690 := wide_block_sound band profiles 13462186 13905690 (wideData 6 0x208008200e9ac5f08ac004c2be8000000000dda8527b3e004c2bf0000000000cff84e3ea0004c2be8000000000cb384a5af2004c2bf02080082008eec3e993c004c2be84984984e84984984e88b31a0d8b8ee0099ea5dae) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 9174963 9803262 13905690 c0 (wide_covered_join band 9803263 10394603 13905690 c1 (wide_covered_join band 10394604 11096821 13905690 c2 (wide_covered_join band 11096822 12279503 13905690 c3 (wide_covered_join band 12279504 13462185 13905690 c4 c5)))))
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
private def profiles : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨45268,250,10158⟩
  | 2 => ⟨27328,144,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 9306034 9735568 := wide_block_sound band profiles 9306034 9735568 (wideData 16 0x6dd04fb400192f980000000001ce8177e00064be600000000007aa07ab200192fa00000000001f68078b80064be60000000000a9b06d2e00192fa00000000002d201aba00064be60000000000bcb15d40064be80000000000f1f058a200192f9800000000048bc0f8e40064be6000000000165e02d2600192f980000000006c20066a80064be800000000022790cdbb00192f988210208415f6dc56af6b7b08192fa00000000009b65c0abf4bf8002a3eb80000000006da4b07bb1970004c7cf03803804b03803804b089e49099f5ee2011f31dfe) (by decide +kernel)
private theorem c1 : WideCovered band 9735569 10277155 := wide_block_sound band profiles 9735569 10277155 (wideData 16 0x78e0fd64002a3eb80000000001fbc3b88000a8fae0000000000aec16c62002a3eb00000000002ce03649000a8fae0000000000e290bc6e002a3eb80000000003de826ba000a8fae000000000160b14966002a3eb800000000069e8122c000a8fae000000000237a02b79002a3eb8000000000dab83a8c400a8fae0000000005f6f0b9ab002a3eb00000000001d31d02d60ac00a8fae1040041000eee3533483e002a3eb80000000001970224f00064be600000000006590486c00192fa03a03a04f03a03a04f03e30904ee5bb4092ceba26) (by decide +kernel)
private theorem c2 : WideCovered band 10277156 10874768 := wide_block_sound band profiles 10277156 10874768 (wideData 16 0x6fa1e830002a3eb80000000001cf0060a68002a3eb80000000001e2c0638ea002a3eb02080082001ff177dd800a8fae0000000000688188b2002a3eb80000000001a785fdf800a8fae00000000007181ddfc002a3eb80000000001bb86209000a8fae000000000071d17fba002a3eb80000000001d6c5fef800a8fae0000000000a081faf0002a3eb00000000001ffc6349000a8fae0820020800fac55aa4002a3eb80000000001af84698800a8fae000000000074e17aaa002a3eb03b03b04f03b03b04f04aba805a34b2e093d71c34) (by decide +kernel)
private theorem c3 : WideCovered band 10874769 11920590 := wide_block_sound band profiles 10874769 11920590 (wideData 16 0x2080082016c03fa0900131f3c0000000000ffc02ceda80131f3c00000000013bc039b4d80131f3c000000000135b02afb980131f3a0000000001a19038f7a00131f3c0820020800bfc41ffdc00131f3a000000000135d01ff9c00131f3c000000000135c19b62004c7ce80000000006d20067b6c004c7cf00000000007f30728f40131f3a000000000376a01a6dbc0131f3c20800820023cc419f0bbc004c7ce80000000001a3c7719800a8fae00000000006dd01874b000a8fae00000000006ce1f830002a3eb03c03c04f03c03c04f04ee1c05d7d9ac094ea0dee) (by decide +kernel)
private theorem c4 : WideCovered band 11920591 13115816 := wide_block_sound band profiles 11920591 13115816 (wideData 16 0x9b2026ccf8004c7cf02080082005be01fcc6a004c7cf000000000088741ffff6004c7cf00000000007bb81e7a3e004c7ce820800820059f41f58be004c7cf0000000000697c17cd20004c7ce80000000006eec1b0faa004c7cf00000000006a3c177be4004c7ce82080082003ba417dd36004c7cf000000000059b0134aa4004c7cf00000000005f68168dbe004c7cf00000000005be8131c30004c7ce82080082001ff81378bc004c7cf00000000004bf80f2eb2004c7ce80000000005a3412783e004c7cf03f03f04f03f03f04f06ca1807dbe924096f24a76) (by decide +kernel)
private theorem c5 : WideCovered band 13115817 14086935 := wide_block_sound band profiles 13115817 14086935 (wideData 13 0xe38038e002e64807ee2bf0084c7ce80000000015c605e0f6a004c7cf00000000015de05e792c004c7ce8208008201093c4f4ee4004c7cf000000000118f44a5e68004c7ce8000000000f9b442087a004c7cf0000000000fdf8432868004c7ce8208008200a8b833e826004c7cf0000000000cdfc369c60004c7ce8000000000bbb42f9b32004c7cf020800820098a02f8b7c004c7ce80000000009af42719aa004c7cf04904904f04904904f09cade0af20db0099962dea) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 9306034 9735568 14086935 c0 (wide_covered_join band 9735569 10277155 14086935 c1 (wide_covered_join band 10277156 10874768 14086935 c2 (wide_covered_join band 10874769 11920590 14086935 c3 (wide_covered_join band 11920591 13115816 14086935 c4 c5)))))
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
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨43018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 7733181 9572581 := wide_block_sound band profiles 7733181 9572581 (wideData 16 0x17c66cf800a2c3e0000000001a0678c800a2c3e0000000001b06a78000a2c3e0000000001b86b98000a2c3e0000000001e86eef800a2c3e0820020802b16e79000a2c3e00000000016c5658800a2c3e000000000170569e800a2c3e0000000001a056fd000a2c3e0000000001ac5789800a2c3e0000000001bc5a3b000a2c3e0000000001ec5b28800a2c3e1c7005140532e059f3fb80828b0f82080000002a1aa3e0828b0f8924024900180d924090d27c03b03b04983b03b04982c15ca2010eb0e76) (by decide +kernel)
private theorem c1 : WideCovered band 9572582 10458218 := wide_block_sound band profiles 9572582 10458218 (wideData 16 0x820020802750a6cfa004961f00000000011e01f66f8012587c00000000052407a8b2004961f00000000017f01da398012587c0000000007ac070c2c004961f00000000001aa0067c64004961f000000000028f857a88012587c00000000012cc19df5004961f0000000001197a267ce7004961e8820020801792f069fecd8012587c0000000001a87a79000a2c3e0000000001b87b8f800a2c3e0000000001bc7e49000a2c3e0820020801f56f0c000a2c3e0000000001645e5a000a2c3e0e20e21260e20e21265b9a05ceab7c192aaafe8) (by decide +kernel)
private theorem c2 : WideCovered band 10458219 11548233 := wide_block_sound band profiles 10458219 11548233 (wideData 16 0x670163c7c004961f00000000019e058ee98012587c0000000006b0164b64004961f02080082009c049f3c0012587c0000000005a0126c7e004961f00000000016d049e490012587c0000000005f8128e7a004961f02080082004f03c3088012587c0000000004f40ee978004961e80000000014c03bbab8012587c0000000005340e8a7c004961f0208008200d0b7d60004961f00000000011c02db8c8012587c0000000004b80b6b3c004961f00000000014b02db8a0012587c0ee0ee1260ee0ee12672ff079719b81948afa30) (by decide +kernel)
private theorem c3 : WideCovered band 11548234 12093240 := wide_block_sound band profiles 11548234 12093240 (wideData 8 0x19241f8b72004961e800000000018b81ece22004961f000000000018741e1ab4004961f02080082015a06d2fa0012587c0000000007a01a88a6004961f0000000001e8069b2f8012587c0000000007ac1a69fe004961f03d83d84983d83d849819748098f48ac1969609ae) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7733181 9572581 12093240 c0 (wide_covered_join band 9572582 10458218 12093240 c1 (wide_covered_join band 10458219 11548233 12093240 c2 c3)))
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
private def profiles : ℕ → Profile
  | 0 => ⟨16536,4,5080⟩
  | 1 => ⟨2984,24,635⟩
  | 2 => ⟨43268,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 7864252 9552544 := wide_block_sound band profiles 7864252 9552544 (wideData 16 0x770621f800a3a6e0000000007e062bc800a3a6c0000000007fc5e2b800a3a6e000000000060d14f2a0028e9b80000000001978672c000a3a6e000000000069b1aab80028e9b80000000001a38521f000a3a6e0820020800b3958d240028e9b8000000001ee13e760028e9b800000000018604fea000a3a6e00000000006080de3e0028e9b800000000019e85218800a3a6e0820020801e6bb12afaaccc20a3a6e0000000000fcc2c177de4f00126cbc1c70071c01afde827cb3ba02126cbc0e40e41280e40e41287b807caaa0118e9a74) (by decide +kernel)
private theorem c1 : WideCovered band 9552545 10207188 := wide_block_sound band profiles 9552545 10207188 (wideData 16 0x3d3407aa00126cbc000000000174f0ba340049b2f06180186002c687b8cac0049b2e800000000018680619720028e9b8000000001fa1cae20028e9b800000000019280629680028e9b80000000003b418e5d000a3a6e0820020800b4726f800a3a6e0000000006a85e3b000a3a6e0000000007b4729c800a3a6e0000000007fc737b000a3a6e0000000007ec678d800a3a6e000000000061f1bc720028e9b800000000019747af8000a3a6e08200208006de5f9b60028e9b83883884a03883884a03c39d05befba0112a64cee) (by decide +kernel)
private theorem c2 : WideCovered band 10207189 11309747 := wide_block_sound band profiles 10207189 11309747 (wideData 16 0x82002080065d03f6cc00126cbc0000000000efa048b4c00126cbc0000000000e6b03beff00126cba0000000000eef03d6e800126cbc08200208066c0f8db80049b2f00000000002de80b7bbe0049b2f00000000003a380eab760049b2f000000000038e00b696a0049b2f00000000003f240ee8e80049b2f020800820019710a5c300049b2f000000000038a00b1da00049b2f00000000002fbc07acf80049b2f00000000003b2c07593e0049b2f00000000004db40ae87e0049b2f00000000005ba0069fbc0049b2f03b83b84a03b83b84a03fb2806eecbb8113ce6c24) (by decide +kernel)
private theorem c3 : WideCovered band 11309748 12274485 := wide_block_sound band profiles 11309748 12274485 (wideData 14 0x68ec2298720049b2e80000000006ae8232ff80049b2f02080082004b68223b760049b2f000000000058341b5fb40049b2f00000000005bf41eaaaa0049b2f000000000058301b0d6a0049b2f02080082003b381b7e760049b2f0000000000497416bea40049b2f00000000004d6417fef40049b2e80000000004a3c169f6e0049b2f02080082001fec13aca00049b2f00000000003fb813eabe0049b2f00000000003d2012a8f00049b2f03d03d04a03d03d04a05ba6c08aef8fe115daffa2) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7864252 9552544 12274485 c0 (wide_covered_join band 9552545 10207188 12274485 c1 (wide_covered_join band 10207189 11309747 12274485 c2 c3)))
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
