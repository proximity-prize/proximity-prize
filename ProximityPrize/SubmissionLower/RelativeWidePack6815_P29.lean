import ProximityPrize.SubmissionLower.RelativeWideBlocks6815
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R174
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨9,55,4192,4289,10175228031504137⟩
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨42518,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 7208896 9345289 := wide_block_sound band profiles 7208896 9345289 (wideData 16 0x7fc16d6c0028a7b80000000002afc73fd000a29ee0000000000b0b1dd340028a7b80000000002b3c5eff800a29ee0000000000bcf1f9220028a7b80000000002cfc060af60028a7b82080082004fa556ec800a29ee0000000000a6a17fb20028a7b80000000002ae0629f000a29ee0000000000a7c11f720028a7b80000000002df063fb800a29ee1450051401e88f816cfe3e020a29ee0c30000004b06a1d020a29ee1450071c00781c0124bbc65901964043033fb820618f7804804804804804804816d15b2200fea7aa0) (by decide +kernel)
private theorem c1 : WideCovered band 9345290 9989599 := wide_block_sound band profiles 9345290 9989599 (wideData 16 0x26e802bb300492ef030c00c3003ea6803962b40124bbc2080082000e5df5067f37880124bbc0000000000a9901831f000a29ee0000000000b59019eed000a29ee0000000000b9b01a2dc800a29ee0820020800b0b5f96a0028a7b80000000002968060aae0028a7b800000000029fc060dfc0028a7b8000000000296c76bc800a29ee0000000000ab81fcb00028a7b80000000002ca0062ba80028a7b80000000002d7c062cfa0028a7b80000000002cfc7a3f000a29ee0820020800f0a5faa00028a7c03803804803803804807fef905e30d7c191f2ee20) (by decide +kernel)
private theorem c2 : WideCovered band 9989600 11074751 := wide_block_sound band profiles 9989600 11074751 (wideData 16 0x2080082002f24132a3c00492ef00000000008fbc13ec2400492ef000000000089b8126d7800492ef00000000008cfc126f3800492ef020800820029e0134aa800492ef00000000006f740e8dae00492ef00000000007a600e6f7e00492ef0000000000986c121ea600492ef00000000008e340e892000492ef02080082002fb90b683e00492ef00000000007cbc0bd93e00492ef00000000007bb80a3d3c00492ef0000000000a8e00bffec00492ef0000000000af3407ae3c00492ef0000000000eda006fcf000492ef03b03b04803b03b04808ff9807af6d2419397bb3a) (by decide +kernel)
private theorem c3 : WideCovered band 11074752 11549505 := wide_block_sound band profiles 11074752 11549505 (wideData 7 0xca281f0b2a00492ef0000000000b8fc1b397400492ef0000000000ba381b28ec00492ef020800820068f81afe2600492ef00000000009a20169db600492ef0000000000a824175fa200492ef03c83c84803c83c8480ce398098fafb6195a22eba) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7208896 9345289 11549505 c0 (wide_covered_join band 9345290 9989599 11549505 c1 (wide_covered_join band 9989600 11074751 11549505 c2 c3)))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 9)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 9≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤55)
    (hT0 : 4192≤T) (hT1 : T≤4289) (hnu : 7208896≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤10175228031504137 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R174

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R175
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨9,56,4124,4261,10313480134692771⟩
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨42518,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 7339967 9226631 := wide_block_sound band profiles 7339967 9226631 (wideData 16 0x3d3c6319000a2ffe00000000012df018329000a2ffe00000000007cc19fe60028bff82080082005c7d761f800a2ffe0000000000bee12eba0028bff800000000039ac4e5e000a2ffe0000000000fac1986c0028bff80000000003e3c4b8f000a2ffe000000000135d1aea40028bff80000000004dfc4e88800a2ffe00000000017ff1cf260028bff800000000058ed52f8800a2ffe14500514027a830165d63c020a2ffe0820020800afc02b6af82125ffc34d00d34042833c802437ff00ec0ec1220ec0ec122065c158a60108bfe7c) (by decide +kernel)
private theorem c1 : WideCovered band 9226632 9775479 := wide_block_sound band profiles 9226632 9775479 (wideData 16 0xeed018b4d800a2ffe0000000000fcd019f6e000a2ffe0000000000f7b018bf9800a2ffe0820020800eb9419a09000a2ffe0000000000bbd1be7e0028bff80000000003ab8061e6c0028bff800000000038ec72ba800a2ffe0000000000e9d1dbe60028bff80000000003e68062e720028bff80000000003d387798800a2ffe0000000000e0065e280028bff82080082001be566db800a2ffe0000000000e6c1d9ac0028bff80000000002ffc5f4a800a2ffe0000000000e6f18b780028bff8380380488380380488afae805ce3e7a191d67e2c) (by decide +kernel)
private theorem c2 : WideCovered band 9775480 10838872 := wide_block_sound band profiles 9775480 10838872 (wideData 16 0x36f904ca0e80125ffc0820020800f00ecda000497ff0000000000aaac0e99be00497ff0000000000bba00eefac00497ff0000000000cc380efcac00497ff00000000009b340f1de000497ff0208008201ba42db2d00125ffc0000000002b8e02ba1b80125ffc0000000002b8f01c2af00125ffc0000000003a5e01e66c00125ffc0000000004bfb01de6c00125ffc0000000006f4f019ecd00125ffc000000000070d6012a800125ffc0000000000fd8280f6a7300497ff08200208005af0941ab5db400497ff0390390488390390488c970e068bcef4192db7dec) (by decide +kernel)
private theorem c3 : WideCovered band 10838873 11730750 := wide_block_sound band profiles 10838873 11730750 (wideData 13 0x12f74222bf400497ff00000000013bf4227cae00497ff0208008200af3c1ebc2600497ff00000000010d241bfbf000497ff00000000010e6c1be87000497ff0000000000ea341be9e200497ff02080082009e64176e2400497ff0000000000cfa0161f7c00497ff0000000000deac16aab200497ff0000000000ef6417497e00497ff02080082004828136be200497ff0000000000c92c12fbac00497ff03c03c04883c03c04890fe4b08bf5c64194e77d6c) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7339967 9226631 11730750 c0 (wide_covered_join band 9226632 9775479 11730750 c1 (wide_covered_join band 9775480 10838872 11730750 c2 c3)))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 9)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 9≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤56)
    (hT0 : 4124≤T) (hT1 : T≤4261) (hnu : 7339967≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤10313480134692771 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R175

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R176
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨9,57,4057,4234,10699101648235230⟩
private def profiles : ℕ → Profile
  | 0 => ⟨8268,2,2540⟩
  | 1 => ⟨2984,24,635⟩
  | 2 => ⟨42768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 7471038 9171092 := wide_block_sound band profiles 7471038 9171092 (wideData 16 0x16fe188200028f8b800000000068385f58800a3e2e0000000001b9818a240028f8b8000000000a8f5661c000a3e2e0820020801244b9e800a3e2e000000000168f17d680028f8b800000000059e842fa000a3e2e00000000017bf108e60028f8b80000000006db03f3a800a3e2e0000000001fa80f87c0028f8b80000000009b303e2e000a3e2e0820020807a1a6d2b7d239c20a3e2e000000000068fe81aeef40028f8b8208008200deffb05c64b340049f0f071c014501afe6a0a979bf20849f0f03803804902f82f849028f8061c6a010af8a7a) (by decide +kernel)
private theorem c1 : WideCovered band 9171093 9726211 := wide_block_sound band profiles 9171093 9726211 (wideData 16 0x13580183ca800a3e2e00000000013d80186ef000a3e2c000000000166c018a7b800a3e2e0820020801a4c5fe760028f8b80000000004b20060c260028f8b800000000048b86e38800a3e2e000000000129c1babe0028f8b80000000004c746f6d000a3e2e00000000013b81c92e0028f8b80000000005aac7a28800a3e2e0000000005a00648240028f8b82080082003fbd6a2d000a3e2e0000000000ffc169e40028f8b800000000049f45a8a800a3e2e000000000131e16af60028f8b8380380490380380490dee0e05bb1834111c7c876) (by decide +kernel)
private theorem c2 : WideCovered band 9726212 10593586 := wide_block_sound band profiles 9726212 10593586 (wideData 16 0xfbec0e9cee0049f0f0000000000eee00ab8ae0049f0f000000000119300a4ea20049f0f000000000189bc0e6d3a0049f0f0000000000edb5078d320049f0f0208008200a9f85b5a80127c3c0000000005749019a1a80127c3c0000000006aba01aeabc0127c3c1860061803abe019f29ec0049f0f000000000059ec06ac740028f8b800000000058b0066f2e0028f8b82080082003df1066ee80028f8b80000000003fe87e9f800a3e2e000000000123a1fc240028f8b80000000004e28065ee80028f8b8390390490390390490fb62c05f63ca2112cf8a34) (by decide +kernel)
private theorem c3 : WideCovered band 10593587 11703826 := wide_block_sound band profiles 10593587 11703826 (wideData 16 0x178fc1ec9f80049f0f00000000017a301e9d780049f0f0208008200ebbc1f1a240049f0f000000000138a817cc6c0049f0f00000000013a6817ab2a0049f0f0000000001693c1b6eea0049f0f02080082007aec167d3a0049f0f000000000119ec161d7c0049f0f00000000011cf413fdae0049f0f00000000011abc133cae0049f0f02080082005ce4163b300049f0f0000000000dff00f2fa40049f0f0000000000ed2c0f0f600049f0f0000000001282c12cda60049f0f0000000000bdb40f1e780049f0f03c03c04903c03c049148b2807ef587e114aba920) (by decide +kernel)
private theorem c4 : WideCovered band 11703827 11911995 := wide_block_sound band profiles 11703827 11911995 (wideData 3 0x1caac2699bc0049f0e8208008201297c235b760049f0f03d83d84903d83d8491cc60d0ad39da0116bb2ca0) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7471038 9171092 11911995 c0 (wide_covered_join band 9171093 9726211 11911995 c1 (wide_covered_join band 9726212 10593586 11911995 c2 (wide_covered_join band 10593587 11703826 11911995 c3 c4))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 9)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 9≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤57)
    (hT0 : 4057≤T) (hT1 : T≤4234) (hnu : 7471038≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤10699101648235230 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R176

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R177
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨9,58,3992,4205,24266187225847908⟩
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨2984,24,635⟩
  | 3 => ⟨43018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 7602109 9110848 := wide_block_sound band profiles 7602109 9110848 (wideData 16 0x1fa914b2c002930f80000000008fa45319000a4c3e0000000002adc14e6a002930f80000000007da8565f800a4c3e000000000279f55e7a002930f82080082008ced539c800a4c3e0000000001f9c0c8f6002930f80000000008fa826df000a4c3e082002080133aadd41b68c719420a4c3e0000000000ecda1801871aa7e0012987c0820020804f08201aae7de0012987a000000000230aac0b1af0a0012987c000000000170fbc0748fbc8012987c1450051404ffbfc1aaa31e0212987c1c70071c00a190197bf024649f00e40e41260e40e4126078814c6000fca8ab8) (by decide +kernel)
private theorem c1 : WideCovered band 9110849 9672240 := wide_block_sound band profiles 9110849 9672240 (wideData 16 0x1a191fe22002930f80000000006ba0060be8002930f80000000005b78061b36002930f820800820088f17fce800a4c3e000000000160f19cbe002930f80000000005aa4679f000a4c3e00000000017591a8f0002930f800000000068b06b0a800a4c3e0000000001b2e1b86a002930f800000000079bc6f78000a4c3e000000000164a1ac6e002930f8000000000983d5b5e000a4c3e082002080074d169b2002930f80000000005e2052aa800a4c3e0000000001a9a14a6c002930f83803804983803804990a2af05aacaae191ba793e) (by decide +kernel)
private theorem c2 : WideCovered band 9672241 10338892 := wide_block_sound band profiles 9672241 10338892 (wideData 16 0x1e8247f5f8012987c000000000069ea4727a4012987c186006180269067f3be8012987c00000000012cf01af3a800a4c3e0820020800aab419b88000a4c3e000000000169f018e8a800a4c3e00000000016fa018f39000a4c3e000000000175d01920f000a4c3e00000000017d901932a000a4c3e0000000001a6801967b000a4c3e0000000001b0b019a29800a4c3e0820020801a0e4196f8000a4c3c000000000160a1eaa8002930f80000000005824731f000a4c3e000000000160f1ae22002930f83903904983903904992970a05dfbee8192c2fcfe) (by decide +kernel)
private theorem c3 : WideCovered band 10338893 11461675 := wide_block_sound band profiles 10338893 11461675 (wideData 16 0x16eb41758e6004a61f00000000017a3c173f26004a61f00000000018864174962004a61f020800820099a4171938004a61f0000000001292c120da4004a61f0000000001396c122cf6004a61f00000000015b3012dd32004a61f000000000178b812fc78004a61e820800820019b50f7cf2004a61f00000000012a380ebbec004a61f00000000013f640eaa38004a61f000000000139280a7de2004a61f0000000001a8700e5fa4004a61f0208008200fb310b4e6e004a61f000000000139a407cbb2004a61f03b83b84983b83b84996ca8e07bb5e62193eea9b4) (by decide +kernel)
private theorem c4 : WideCovered band 11461676 12093240 := wide_block_sound band profiles 11461676 12093240 (wideData 9 0x668302a7b24004a61e82080082017f38269d74004a61f0000000000186de08fe8e8012987c000000000061ae023afb6004a61f02080082015fac2368fc004a61f0000000001bafc1e5a6e004a61f0000000001bbfc1e2c60004a61f00000000018e701a2f70004a61f03d83d84983d83d8499ee2ca09c6db3a195ffb932) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7602109 9110848 12093240 c0 (wide_covered_join band 9110849 9672240 12093240 c1 (wide_covered_join band 9672241 10338892 12093240 c2 (wide_covered_join band 10338893 11461675 12093240 c3 c4))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 9)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 9≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤58)
    (hT0 : 3992≤T) (hT1 : T≤4205) (hnu : 7602109≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤24266187225847908 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R177

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R178
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨9,59,3930,4176,21875831038933556⟩
private def profiles : ℕ → Profile
  | 0 => ⟨16536,4,5080⟩
  | 1 => ⟨2984,24,635⟩
  | 2 => ⟨43018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 7733180 9081380 := wide_block_sound band profiles 7733180 9081380 (wideData 16 0x2adb15874002969b8000000000c92056bd000a5a6e000000000368b0aaf6002969b80000000008920566c800a5a6e00000000022ba55fb4002969b800000000058281738800a5a6e0000000002bb855d3e002969b04100104004e36aa5067fbbf63082969b80000000003b6ffe0739babc8012acbc082002080566f7417cd38b0012acbc000000000271e3c0ade2e88012acbc0000000001a89280728b9b0012acbc000000000132f3c063cf7c8012acbc0820020800a7d6063daf2004ab2f071c01c7010ce5904b7d96e084ab2f02f82f84a02f82f84a04ab4079e6200feb4cb6) (by decide +kernel)
private theorem c1 : WideCovered band 9081381 9649043 := wide_block_sound band profiles 9081381 9649043 (wideData 16 0x1b7f1aaec002969b800000000088b0062870002969b80000000003de10639e8002969b8208008201ff57d62002969b80000000006a306b28800a5a6e0000000001b5a1af70002969b80000000006abc52cd000a5a6c0000000001f6a1bcbc002969b80000000008b6c72a8000a5a6e00000000022be14eb8002969b80000000004c5df72002969b82080082009b69767e000a5a6e0000000001a0c0ebf0002969b80000000007b38564b000a5a6e000000000225f15a26002969b83803804a03803804a12cb0a059f2c3e111b2eaf6) (by decide +kernel)
private theorem c2 : WideCovered band 9649044 10287664 := wide_block_sound band profiles 9649044 10287664 (wideData 16 0x1ab2f018bddc012acbc1860061804bbe01a7186e004ab2f00000000007f2806ca6a002969b80000000003c2906da72002969b82080082004f3c7b9d800a5a6e0000000001af80192cf800a5a6e0000000001b6a0193ae000a5a6c0000000001a6f1f86a002969b80000000007a20065f20002969b80000000007d20066db2002969b80000000005a2c060c78002969b82080082005ef5064f6e002969b800000000069387eaf000a5a6e000000000176a19cba002969b80000000006de0060832002969b83903904a03903904a14ef0b05d358f0112be38b4) (by decide +kernel)
private theorem c3 : WideCovered band 10287665 11422991 := wide_block_sound band profiles 10287665 11422991 (wideData 16 0x6658058fc80012acbc000000000763c05fad80012acbc0000000006bae058acc8012acbc0820020801b7a04e2db0012acbc000000000634d04df3a8012acba0000000005b3a03f26c0012acbc000000000621f03eb0e8012acbc0000000001a9904ef7d0012acbc082002080439d02ef4b0012acbc000000000532d02defd8012acbc00000000067ff03bb998012acbc0000000006a9e02b3a90012acbc0000000006f9b02df480012acbc0820020804f1b42baaa0012acbc0000000005b4c17e2e004ab2f03b83b84a03b83b84a19dbfe07b2fb70113e27d7c) (by decide +kernel)
private theorem c4 : WideCovered band 11422992 12274485 := wide_block_sound band profiles 11422992 12274485 (wideData 12 0x82002080065c6c2f5b20004ab2e80000000001ce4d0c87bc8012acbc00000000006def42b3a66004ab2f02080082001828b0aa33b8012acbc000000000069928270b60004ab2f0000000000193ee08ab090012acbc000000000064fa422692a004ab2f02080082018ff8234aea004ab2f0000000001e97c1b2e68004ab2e8000000001eaf01afc32004ab2f000000000018b2907b3ec8012acbc0f60f61280f60f61280638a2809a7fbfe115f718fa) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7733180 9081380 12274485 c0 (wide_covered_join band 9081381 9649043 12274485 c1 (wide_covered_join band 9649044 10287664 12274485 c2 (wide_covered_join band 10287665 11422991 12274485 c3 c4))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 9)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 9≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤59)
    (hT0 : 3930≤T) (hT1 : T≤4176) (hnu : 7733180≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤21875831038933556 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R178

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R179
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨9,60,3869,4147,22482227536500631⟩
private def profiles : ℕ → Profile
  | 0 => ⟨16536,4,5080⟩
  | 1 => ⟨2984,24,635⟩
  | 2 => ⟨43268,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 7864251 9012120 := wide_block_sound band profiles 7864251 9012120 (wideData 16 0xfff03b2a000a687c0000000004a6c119800a687e0000000005edd059ed0029a1f80000000001877c03ee00029a1f80000000001bb9d19b370029a1f8410010400683783d06b8249e90829a1f800000000049ffdac7e68e5e0012c8fc0820020806a48e41aac3df0012c8fc0000000002e09380adf6b88012c8fc0000000002698600a1e6ba0012c8fc00000000013c8a0060cf7f8012c8fc0820020800a6e205abc32004b23e80000000001e25d0abecb8012c8fc00000000006db6c1b4938004b23f0514014500fc38c03eafcec084b23f02f02f04a82f02f04a84ee807997200fc70ae4) (by decide +kernel)
private theorem c1 : WideCovered band 9012121 9586055 := wide_block_sound band profiles 9012121 9586055 (wideData 16 0x272f01822b000a687c00000000026df198a00029a1f80000000001fa10629240029a1f82080082006ef566b9800a687e0000000001fcd1986c0029a1f80000000007cbc4a6d000a687e000000000229911e200029a1f8000000000a9ec671b800a687e0000000002ab911aa80029a1f8000000000d8606af9000a687e00000000037c81186e0029a1f80000000003a214a18000a687e0000000002eec5ba380029a1f8208008200c37d9800a687e0000000002f1a10eb20029a1f83803804a83803804a94aaaa0592ccfe111a27eee) (by decide +kernel)
private theorem c2 : WideCovered band 9586056 10159990 := wide_block_sound band profiles 9586056 10159990 (wideData 16 0x7e70063b300029a1f0000000000986c06acfc0029a1f80000000008c6c064caa0029a1f80000000007829065a220029a1f82080082006d34063aa20029a1f80000000006ee87688000a687e0000000002208018f8a000a687e0000000001f0b1dea80029a1f80000000008c60062da60029a1f80000000008e300619700029a1f80000000002dfc7ec9800a687e082002080176f41928b000a687e0000000001b3d188600029a1f80000000007eb87afd800a687e0000000001ede18a280029a1f83903904a83903904a97833805bf8fb4112ae8eac) (by decide +kernel)
private theorem c3 : WideCovered band 10159991 11236119 := wide_block_sound band profiles 10159991 11236119 (wideData 16 0x1f83c13bb20004b23f00000000013fe413d9a8004b23f0208008200cb7c0fe87e004b23f00000000019f240f19ae004b23f000000000199380b8d32004b23f0000000001ffb00f0ae2004b23f00000000005fac0f0bbe004b23f02080082009df80b28b0004b23e8000000001bf200a2b74004b23f00000000001874c01db4c8012c8fc000000000065e3446da4012c8fc0000000000a0a3c46ca4012c8fc0000000000f7d280fde65004b23f08200208003da5941c79b34004b23f00000000007a24062d720029a1f83a03a04a83a03a04a99f31906832bfa113ba9e6a) (by decide +kernel)
private theorem c4 : WideCovered band 11236120 12383989 := wide_block_sound band profiles 11236120 12383989 (wideData 16 0x1ffdc0d93988012c8fc000000000078f782ef9a0004b23f02080082001a6e80bb6080012c8fc000000000072e202a79f8004b23f00000000001ca8b0a828a8012c8fc00000000006dfb827bc6e004b23f0208008201ebe8227af4004b23f00000000001966b078a6e0012c8fa000000000068ca81f5d68004b23f02080082017fac1f7e78004b23f00000000001877a06a6688012c8fc0000000000629e41a7968004b23f000000000018e4f069b5e8012c8fc08200208033ae05d6280012c8fc0000000006b8b04bf6d8012c8fc0f40f412a0f40f412a065a2dd08d35e64115ca5d68) (by decide +kernel)
private theorem c5 : WideCovered band 12383990 12455730 := wide_block_sound band profiles 12383990 12455730 (wideData 1 0xfc0fc12a0fc0fc12a079ca7b0d820962117e27ce4) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7864251 9012120 12455730 c0 (wide_covered_join band 9012121 9586055 12455730 c1 (wide_covered_join band 9586056 10159990 12455730 c2 (wide_covered_join band 10159991 11236119 12455730 c3 (wide_covered_join band 11236120 12383989 12455730 c4 c5)))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 9)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 9≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤60)
    (hT0 : 3869≤T) (hT1 : T≤4147) (hnu : 7864251≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤22482227536500631 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R179
