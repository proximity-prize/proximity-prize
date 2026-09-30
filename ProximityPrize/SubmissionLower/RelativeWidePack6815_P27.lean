import ProximityPrize.SubmissionLower.RelativeWideBlocks6815
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R162
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨8,61,4122,4202,16497012708230383⟩
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨33072,8,10160⟩
  | 2 => ⟨2984,24,635⟩
  | 3 => ⟨43518,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 7995323 9493741 := wide_block_sound band profiles 7995323 9493741 (wideData 16 0x78f16d30002921f80000000001d7c461f800a487e0000000000a1817860002921f80000000001fe843cd800a487e0000000000adb17d7a002921f80000000002b7043bd000a487e0000000000baa12fba002921f80000000003af45bfe000a487e104004100072825a41a3f8f9e420a487e000000000063fef81deaeff8004a23f00000000007b758068aadaa004a23e820800820038ecf02dadd3c004a23f00000000001f7ce01cb48b4004a23f071c01c700782c905eeee2c084a23f030c00c3001e7c0ba96a09182fc03903904a83903904a95b1586a010aa0eb2) (by decide +kernel)
private theorem c1 : WideCovered band 9493742 10051292 := wide_block_sound band profiles 9493742 10051292 (wideData 16 0x71f1a860002921f80000000001e747e8f000a487e000000000075d1ab36002921f80000000001fb006096e002921f80000000001ebc6e2b000a487e0000000000a590186fb800a487e0000000000a291c96e002921f82080082002ea56bbe000a487e000000000074c18c6c002921f80000000001cec579c000a487e00000000007cf1bc64002921f80000000001e785a4d800a487c0000000000a4f1cc7e002921f800000000028b45b9e800a487e0000000000b0d1e97a002921f83903904a83903904a85feb905aede3e192972c38) (by decide +kernel)
private theorem c2 : WideCovered band 10051293 11061853 := wide_block_sound band profiles 10051293 11061853 (wideData 16 0x1a4903ab8f801288fc0000000001b4c03afff801288fc0820020805310bfc22004a23f00000000005a6c0b19fa004a23f00000000005e340afda6004a23e80000000006bec0aeb68004a23f00000000007ce00adca8004a23f02080082004e290a4be4004a23f00000000005d3c06e9ac004a23f00000000006dec065878004a23f0000000000893026df801288fc0000000002e380193ec401288fc186006180068801865cea004a23e800000000028f8065bfc002921f80000000001ffc060b2c002921f83a03a04a83a03a04a86d72d05e69ebe1939f3bf6) (by decide +kernel)
private theorem c3 : WideCovered band 11061854 12176955 := wide_block_sound band profiles 11061854 12176955 (wideData 16 0xac201f886c004a23f0000000000ac381f5cf6004a23f02080082005e341b1b7e004a23f00000000008e241aa8a2004a23f00000000008ea41a8cee004a23e82080082005abc1a5f6c004a23f00000000007af4165a70004a23f00000000007bb4164a20004a23f00000000007cf81649e0004a23f02080082003cf4160a70004a23f00000000006ae0126a60004a23f00000000006c24125e6a004a23f000000000068680f2df4004a23e80000000006c7c125a60004a23f020800820019e40edabc004a23f03c83c84a83c83c84a8983ba07defaee1959eda76) (by decide +kernel)
private theorem c4 : WideCovered band 12176956 12455730 := wide_block_sound band profiles 12176956 12455730 (wideData 4 0xcf3427996a004a23e8000000000c924262be6004a23f02080082007fb82269fe004a23f03e83e84a83e83e84a8cc7ac0ac22b24197aef9f2) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7995323 9493741 12455730 c0 (wide_covered_join band 9493742 10051292 12455730 c1 (wide_covered_join band 10051293 11061853 12455730 c2 (wide_covered_join band 11061854 12176955 12455730 c3 c4))))
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
private def profiles : ℕ → Profile
  | 0 => ⟨33072,8,10160⟩
  | 1 => ⟨2984,24,635⟩
  | 2 => ⟨43768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 8126394 9465473 := wide_block_sound band profiles 8126394 9465473 (wideData 16 0x4a2453fd800a4eae0000000001ee855ae600293ab82080082014c10cfc00293ab8000000000397c4b5a800a4eae0000000000e8e0d8b600293ab80000000003d7c326f800a4eae000000000127d0b96000293ab00000000005b7c4f1a800a4eae0000000001a18098fe00293ab84100104016870d4ca728b308293ab8000000000cd62c07b3e93c004a74f020800820049b0802cad9ec004a74f00000000002d69b01c61ef4004a74f030c00c30029e4a3106e87fbed004a74f030c00c3002c3f8f0073ee4fbc088ce9e03803804b03803804b03bb00ee8bc010cad8b0) (by decide +kernel)
private theorem c1 : WideCovered band 9465474 10029296 := wide_block_sound band profiles 9465474 10029296 (wideData 16 0x2080082003921063eec00293ab80000000002a646388000a4eae0000000000ac918ea600293ab80000000002bf863eb000a4eae0000000000b881bbee00293ab80000000002fe8767d000a4eae0000000000bfd1a87e00293ab000000000039e06b1e000a4eae000000000162f5b9a800293ab82080082002c38671d000a4eae0000000000aeb1496600293ab80000000002cf8522f800a4eae0000000000ba91487c00293ab80000000003878521b000a4eae0000000000f7a1bba600293ab83903904b03903904b08a36d05a329b81128fc8b0) (by decide +kernel)
private theorem c2 : WideCovered band 10029297 10945507 := wide_block_sound band profiles 10029297 10945507 (wideData 16 0x231e02b3ab00129d3a0000000002e3d039ab880129d3c08200208016bb428aec80129d3c000000000232b029a4b00129d3c000000000230c019a5e80129d3c0000000002aa818864004a74f0000000000fc3006ae22004a74f00000000014d787eafc0129d3c00000000006987806ebff004a74e88200208001bf7c4197ae3c004a74f00000000002b64766f000a4eae0000000000b8e018b9a800a4eae0000000000b381debe00293ab80000000002db07a6c000a4eae0000000000bae1ecea00293ab03a03a04b03a03a04b099f8b05d6dcfe1139a9a6e) (by decide +kernel)
private theorem c3 : WideCovered band 10945508 12073153 := wide_block_sound band profiles 10945508 12073153 (wideData 16 0x36be06d77d00129d3a082002080220b06c74d80129d3c0000000002bdf05af7c00129d3c000000000328e06865d00129d3c0000000002e9d05a7ec00129d3c08200208016ce05a7ae00129d3c00000000026af04a72c00129d3c000000000272e04a35a00129d3c0000000002e4e04ff5880129d3a0820020800a1903df1880129d3c000000000266f04838980129d3c000000000230f03af4c80129d3c0000000002a8f048bed80129d3c0820020800750e3ef8004a74f00000000007a240b0fee004a74f03c83c84b03c83c84b0c967a07b7f87411582bce2) (by decide +kernel)
private theorem c4 : WideCovered band 12073154 12636975 := wide_block_sound band profiles 12073154 12636975 (wideData 8 0x13e342b1f7c004a74e8208008200fc242b2da2004a74f00000000011a20265fb0004a74f0000000001082022cce4004a74f00000000011af8263db2004a74e8208008200aa781f686e004a74f0000000000eba01f08e0004a74f03e83e84b03e83e84b10cbef09ea9aa811796683e) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8126394 9465473 12636975 c0 (wide_covered_join band 9465474 10029296 12636975 c1 (wide_covered_join band 10029297 10945507 12636975 c2 (wide_covered_join band 10945508 12073153 12636975 c3 c4))))
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
private def profiles : ℕ → Profile
  | 0 => ⟨16536,4,5080⟩
  | 1 => ⟨2984,24,635⟩
  | 2 => ⟨43768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 8257465 9397653 := wide_block_sound band profiles 8257465 9397653 (wideData 16 0x820020802efa56a34002972f00000000003e3c3a8d800a5cbe000000000126a0dd2e002972f80000000004df833b9000a5cbe00000000016eb0bf24002972f84102104083b69ae90728a4a6b082972f80000000002c72bfc065da3eba004ae5f00000000010865c07b37ba2004ae5e82080082005b61e02cf5e28004ae5f00000000003abca01c2e972004ae5f00000000002abeb01877df2004ae5f00000000001e39e19a6ea8012b97a08200208066ae0dfb6c8012b97c0000000000619f83b3f6e004ae5f071c31450c6d2fd03924b26084ae5f03803804b82f82f84b82ce007abe2010a6cce0) (by decide +kernel)
private theorem c1 : WideCovered band 9397654 9967748 := wide_block_sound band profiles 9397654 9967748 (wideData 16 0x387c674c800a5cbc0000000000e6b19eb8002972f80000000003afc6a2c000a5cbe0000000000f2b1ab6e002972f80000000003ea86bbd800a5cbe000000000123c1bbaa002972f8000000001ac1c976002972f820800820048a15a69000a5cbe0000000000bee11ffe002972f80000000003aa0526b800a5cbe0000000000f3b14df4002972f80000000003f64539c000a5cbe000000000129e14f76002972f80000000004e60564b800a5cbe00000000016d815bac002972f83903904b83903904b8a879b0596eb24111ff8b28) (by decide +kernel)
private theorem c2 : WideCovered band 9967749 10751628 := wide_block_sound band profiles 9967749 10751628 (wideData 16 0x8200208026ae428f998012b97c0000000002b1d01a3190012b97c0000000002f380a9b8004ae5f00000000010df02f488012b97a00000000062a819ebd004ae5f061801860078418ffeaa004ae5f00000000003f64065876002972f82080082002ff90638f0002972f800000000038e07a1b000a5cbc0000000000e6b1ea2a002972f80000000003aa07b1b800a5cbe0000000000eed1ef6e002972f80000000003d207ece000a5cbe0000000000fa91fff8002972f80000000001b6c060de0002972f83a03a04b83a03a04b8bb75b05c6ab721138b1ee6) (by decide +kernel)
private theorem c3 : WideCovered band 10751629 11891817 := wide_block_sound band profiles 10751629 11891817 (wideData 16 0xecf017496e004ae5f0000000000eef8173c2c004ae5f02080082007ca4170de6004ae5f0000000000caec132bac004ae5e8000000000cc2012fb76004ae5f0000000000bdac0fceb2004ae5f00000000008b60132972004ae5f020800820078e80f5eae004ae5e8000000000b96c0f38f6004ae5f0000000000bea80f38aa004ae5f0000000000ce340f497c004ae5f020800820018b10e3eba004ae5e8000000000a9ac0b6fb2004ae5f0000000000b8f80b58e4004ae5f0000000000cc380b3c38004ae5f03c83c84b83c83c84b8ea3bf07926f36114d32bb4) (by decide +kernel)
private theorem c4 : WideCovered band 11891818 12818220 := wide_block_sound band profiles 11891818 12818220 (wideData 13 0x1caf037b964004ae5e82080082019cb82f28fe004ae5f0000000001ab282e5f6e004ae5f00000000019f2c2bcd7c004ae5f02080082012a642a0da8004ae5e80000000013bf4221bf0004ae5f00000000014fe0234f30004ae5f00000000014fbc231fe4004ae5f0208008200ccbc1f2a28004ae5e80000000011af41e0a34004ae5f00000000011b641bdd7a004ae5f0000000000fe641bcc6e004ae5f03e83e84b83e83e84b93c2ef0997c8a0116ea5b2e) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8257465 9397653 12818220 c0 (wide_covered_join band 9397654 9967748 12818220 c1 (wide_covered_join band 9967749 10751628 12818220 c2 (wide_covered_join band 10751629 11891817 12818220 c3 c4))))
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
private def profiles : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨44018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 8388536 9361154 := wide_block_sound band profiles 8388536 9361154 (wideData 16 0x27bc06aee0029abb8000000000cff42fdf000a6aee00000000043ff09f680029abb80000000016ba42fdac00a6aec1861061840ede3dc41a25cb49420a6aee0000000000adb38a1d96287e004b36f00000000011a27d06c64820004b36f02080082005efcd02abed36004b36f00000000003eba901b74f7c004b36e800000000039eaf019add24004b36f02080082001d21d15de3a8012cdbc000000000063e6c33bbb4004b36f0000000001ea742b58e2004b36f0000000001aef0264b62004b36f02080082016d782b48ee004b36f02e02e04b02e02e04b06cb8c02c79da801092ccaa) (by decide +kernel)
private theorem c1 : WideCovered band 9361155 9937520 := wide_block_sound band profiles 9361155 9937520 (wideData 16 0x820020801f985ea680029abb80000000003fb05ff9000a6aee0000000000f6f129720029abb80000000004bb0622c800a6aec000000000139c18af40029abb80000000004d68475a000a6aee000000000176d18eb20029abb80000000006af066ee000a6aee0000000000ad95aaa20029abb82080082005fb143ee800a6aee000000000133911ef40029abb800000000058744738000a6aec000000000161909c6a0029abb80000000006ab442c9000a6aee0000000001e9e0ff320029abb83903904c03903904c0bee7b058eae76091f71ef2) (by decide +kernel)
private theorem c2 : WideCovered band 9937521 10621955 := wide_block_sound band profiles 9937521 10621955 (wideData 16 0x1964c01c66d4012cdbc0000000000aec740b7b71004b36f08200208002fecd41aa5a2c004b36f000000000049f0061f360029abb00000000003f7c733c800a6aee0000000001329018b4f800a6aee0000000001398018e9a000a6aee00000000013aa01868c800a6aee082002080164b5fb6e0029abb80000000003f2c735c000a6aee000000000121d1cfa40029abb80000000003e605efd000a6aec00000000012eb1dbee0029abb80000000004de87a0a800a6aee000000000131c18b340029abb83a03a04c03a03a04c0dbae905b7f82c093837cae) (by decide +kernel)
private theorem c3 : WideCovered band 10621956 11774688 := wide_block_sound band profiles 10621956 11774688 (wideData 16 0xffe8134f66004b36f00000000012c7816dc72004b36f02080082003e70121ab2004b36f0000000000fa7c12bba0004b36e8000000000e9340f4cf6004b36f00000000010efc12bbb0004b36f02080082006e03ab688012cdbc000000000320f02de4b8012cdba0000000003b8a03b2bb8012cdbc0000000003a6902ca798012cdbc0000000004af803b69e8012cdbc082002080262a42876c0012cdbc000000000324f01bac88012cdbc00000000042ca02878c8012cdbc000000000470b15dac004b36f03c83c84c03c83c84c10a24f0782daa4094b36de0) (by decide +kernel)
private theorem c4 : WideCovered band 11774689 12927420 := wide_block_sound band profiles 11774689 12927420 (wideData 16 0x67860378efe004b36f000000000018bdf0c973f8012cdbc0000000000658b433dd76004b36f020800820169f82a48ea004b36e8000000001beb4270f20004b36f0000000001dfe02a8ba2004b36f0208008201392023de26004b36f00000000018e2c22cca6004b36e80000000016b3c1ed922004b36f000000000189fc220928004b36f0208008200d82c1ba92a004b36f00000000012c3017dfe8004b36e80000000014d601b4aac004b36f00000000012fb817ac72004b36f02080082009db417bdac004b36f03e03e04c03e03e04c16b62f08d68bf0096ce293a) (by decide +kernel)
private theorem c5 : WideCovered band 12927421 12999465 := wide_block_sound band profiles 12927421 12999465 (wideData 1 0x122122130122122130062e7ae0da2ea74098e6dcb2) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8388536 9361154 12999465 c0 (wide_covered_join band 9361155 9937520 12999465 c1 (wide_covered_join band 9937521 10621955 12999465 c2 (wide_covered_join band 10621956 11774688 12999465 c3 (wide_covered_join band 11774689 12927420 12999465 c4 c5)))))
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
private def profiles : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨44268,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 8519607 9357149 := wide_block_sound band profiles 8519607 9357149 (wideData 16 0x7be78060e7b0029e3f80000082002e67b019fb8400a78fe10400208017cdfd2eeefe0029e3f80000000003e78239a00063c7e000000000123a08ebc0018f28000000000048e0138d80063c7e1041841060ecaba9418e0faba42063ca00000000000aaa79b18aaecbe004ba7f00000000012de49068f7c64004ba7e82080082007c2fe02cb2ca8004ba7f0000000000482cd01a63870004ba7f00000000002f21c1d9a4f8012e9fc0820020800a786866cae2004ba7e800000000019b890bf7ce8012e9fc000000000060f6c27c9f2004ba7f02e82e84b02e82e84b099e1d038f3e3e010b2e8e8) (by decide +kernel)
private theorem c1 : WideCovered band 9357150 9939787 := wide_block_sound band profiles 9357150 9939787 (wideData 16 0x17db15bf60029e3f80000000006c3c575f800a78fe00000000012c774a000a78fe0820020801f5a55bec0029e3f80000000005aec56ba000a78fe000000000166b0eafe0029e3f80000000006b2c561c800a78fe0000000001adc0d82e0029e3f00000000008868533e800a78fe00000000022f90b92a0029e3f8000000000af6c5219000a78fe000000000329c0897e0029e3f8000000000fd682688000a78fe00000000036132ba800a78fe0000000003f5b03f630029e3f83983984c83983984c8c87ee058e3ae8091f6ae76) (by decide +kernel)
private theorem c2 : WideCovered band 9939788 10522425 := wide_block_sound band profiles 9939788 10522425 (wideData 16 0x5df8066e740029e3f80000000005b700619e20029e3f80000000002ce9068af20029e3f82080082002b7c6f3a800a78fe00000000013b91fd780029e3f80000000004cf86ebe800a78fe00000000013981af340029e3f80000000005ce8061a760029e3f00000000005ab86eec800a78fe0000000001aaa018b5c000a78fe00000000017ad5cc3a0029e3f82080082002be4726b800a78fe00000000012ea15b660029e3f80000000005a306edf800a78fe000000000161915af60029e3f83a03a04c83a03a04c8fabe805af19e609383ce32) (by decide +kernel)
private theorem c3 : WideCovered band 10522426 11651286 := wide_block_sound band profiles 10522426 11651286 (wideData 16 0x4eb904babc8012e9fc082002080124b04ab6d0012e9fc0000000003f8e03be688012e9fc000000000434e03b72f8012e9fa00000000047f903b34e8012e9fc0000000004fff03b38d8012e9fc0820020801ea942b3498012e9fc0000000003b1c01fe298012e9fa00000000046b8028a5d0012e9fc000000000530a01e7ca8012e9fc00000000067fd01b70d0012e9fc000000000064bbc621e8012e9fa00000000007ca6c570a4012e9fc000000000127b341608b5004ba7f08200208005df6d41b6ab2c004ba7f03b03b04c83b03b04c91979c05eb1f6609492edee) (by decide +kernel)
private theorem c4 : WideCovered band 11651287 12816562 := wide_block_sound band profiles 11651287 12816562 (wideData 16 0x1933a0aefb90012e9fc000000000065b602e1de8004ba7f02080082018d6827bfbe004ba7f0000000001ed6823edb6004ba7e8000000001eb60239860004ba7f00000000018bb42358e4004ba7f02080082015e681e6ea4004ba7f000000000198b41e1ae6004ba7e80000000019a301bf8ba004ba7f0208008200e8601b4c38004ba7f00000000014f64175aee004ba7f00000000012f7013b9f4004ba7e80000000015da0172b6a004ba7f02080082008ebc16aa22004ba7f00000000011f3412fb2c004ba7f03e03e04c83e03e04c98b74d089f1cfc096af2d66) (by decide +kernel)
private theorem c5 : WideCovered band 12816563 13180710 := wide_block_sound band profiles 12816563 13180710 (wideData 5 0x8200208006ddec434f3e004ba7e80000000001c7bc0f9b4a0012e9fc0000000000709703b3b76004ba7f02080082001939d0dd7980012e9fc120120132120120132064e6db0c8b4966098cb6cbe) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8519607 9357149 13180710 c0 (wide_covered_join band 9357150 9939787 13180710 c1 (wide_covered_join band 9939788 10522425 13180710 c2 (wide_covered_join band 10522426 11651286 13180710 c3 (wide_covered_join band 11651287 12816562 13180710 c4 c5)))))
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
private def profiles : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨44518,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 8650678 9331605 := wide_block_sound band profiles 8650678 9331605 (wideData 16 0x2c3d221d00063fa80000000000f5c499f20018fe9820800820059f52fbc80063fa80000000000f1804da00018fe980000000003e6812cb00063fa8000000000122a048380018fe980000000004b3c0f4980063fa6000000000139c0396c0018fe984108104203ea0b61062f63bb10818fea00000000002e60cfc67aa6788012fe3c08200208043edac161c33f0012fe3c0000000001ffb780a8fb8a0012fe3c000000000125b78065da3a8012fe3a0000000000f68b0061af690012fe3c082002080075db447486a004bf8f02e82e84b02e82e84b0cdb5f03debd2a010d2fd26) (by decide +kernel)
private theorem c1 : WideCovered band 9331606 9828497 := wide_block_sound band profiles 9331606 9828497 (wideData 16 0x99f04adc800a7f2c0000000002afa0fd360029fcb8000000000cb703b49800a7f2e0000000000f080d9ac0029fcb8000000000bce5676c000a7f2e00000000073d2bc8800a7f2e0820020800f8d06c720029fcb8000000000b8f41780029fcb830c00c301daac335cc00a7f2c0000000003b7a049720029fcb841001040019f9b499afe800a7f2e00000000012fe089ae0018fe980000000004ee8225c00063fa8000000000168e088fc0018fe98000000000aa488ea0018fea03903904d03903904d0eb62d04e6fdf0091eb5df0) (by decide +kernel)
private theorem c2 : WideCovered band 9828498 10417407 := wide_block_sound band profiles 9828498 10417407 (wideData 16 0x1b1c1fb320029fcb000000000018b90678f40029fcb8208008201aa5bdec0029fcb800000000059b0637e000a7f2e00000000016f918da20029fcb80000000005fac6a78800a7f2e0000000001b781dfea0029fcb80000000006d7c6669000a7f2e0000000001e8d19b360029fcb00000000003db8676a000a7f2e0820020802abc5ddac0029fcb80000000005ea0578f000a7f2e00000000017da129fa0029fcb80000000006b7c477a800a7f2e0000000001e2e1197e0029fcb83a03a04d03a03a04d10ba6e059eecbe092ea4970) (by decide +kernel)
private theorem c3 : WideCovered band 10417408 11300771 := wide_block_sound band profiles 10417408 11300771 (wideData 16 0x564d02ffed8012fe3a000000000560c01f3ba8012fe3c000000000762902dede8012fe3c000000000061da8065a76004bf8f0000000001bd68173b0012fe3a0000000003f9816e2a004bf8f0000000000b869c08a7fec012fe3a2080082002bfc21070fe8c8012fe3c0000000001abf0193fb800a7f2c0000000001b5801970e000a7f2e082002080178c418f1c800a7f2e000000000166f1e8a80029fcb80000000006820063f7c0029fcb80000000005d287afd800a7f2e00000000017ca1edaa0029fcb83b03b04d03b03b04d12c3e805d2eb26093fa2b2c) (by decide +kernel)
private theorem c4 : WideCovered band 11300772 12478591 := wide_block_sound band profiles 11300772 12478591 (wideData 16 0x77ff07b71a0012fe3a000000000061a70227f66004bf8f0208008200e8f81a9a30004bf8f00000000018e7417ce76004bf8f0000000001bf3c1b4d26004bf8e80000000016bf4179b34004bf8f0208008200db20171df8004bf8f000000000158b813396e004bf8f0000000001796013ee3a004bf8e800000000118f013ed2e004bf8f02080082008df00f5fe6004bf8f00000000014fe812792e004bf8f00000000013ca80eceae004bf8e800000000189ac127eae004bf8f02080082004a610e08b8004bf8f03d83d84d03d83d84d18d77907c30f3a095da7ce2) (by decide +kernel)
private theorem c5 : WideCovered band 12478592 13361955 := wide_block_sound band profiles 12478592 13361955 (wideData 12 0xa1d6847b878004bf8e800000000028f7e12b62b0012fe3c00000000007c8f0424ee8004bf8e82080082001bf4d0fca690012fe3c0000000000708b4339bf8004bf8e80000000001bb7b0cab8d8012fe3c082002080067864361af8004bf8f0000000000197ce09f34b8012fe3c000000000068d6c2b3ebe004bf8e80000000001937f09b2590012fe3c0820020805e1b08ce9a8012fe3c0fe0fe1340fe0fe134062fecc0a9fd9e8097fa483a) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8650678 9331605 13361955 c0 (wide_covered_join band 9331606 9828497 13361955 c1 (wide_covered_join band 9828498 10417407 13361955 c2 (wide_covered_join band 10417408 11300771 13361955 c3 (wide_covered_join band 11300772 12478591 13361955 c4 c5)))))
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
