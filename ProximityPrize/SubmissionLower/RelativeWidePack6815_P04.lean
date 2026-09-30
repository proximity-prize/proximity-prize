import ProximityPrize.SubmissionLower.RelativeWideBlocks6815
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R024
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨11,49,4059,4274,10022184552707145⟩
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨41268,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 6422468 8898625 := wide_block_sound band profiles 6422468 8898625 (wideData 16 0xaefc068a740028e5b8000000000b8a46f6c800a396e0000000007fc06bfba0028e5b8000000000fff1773e000a396e0820020801efe1cfbc0028e5b80000000009a70738d800a396e00000000026ab0fc640028e5b8000000000c9f872dd800a397000000000036490c96c0028e5b80000000011fac6f99000a396e0c30030c0431a7017f8eeb020a396e00000000006ae19c660828e5b830c00c3016a0ce30088b35e19640659005c01940439af2068068001a81a800fc076001872de20b00b00f80ae0ae0f8070e14e7000eae5aac) (by decide +kernel)
private theorem c1 : WideCovered band 8898626 9448883 := wide_block_sound band profiles 8898626 9448883 (wideData 16 0x234d01d22b000a396e00000000026fe01e33f000a396e000000000062f01bb0c800a396e0820020800beb41c33c800a396e0000000001acc018b98000a396e0000000001f5c01b2ce000a396e000000000225a01b71d800a396e0000000001f4e018f3f800a397000000000026cf01bfab800a396e0000000002628019648800a396e0000000001a6a41cf29000a396e0820020801b90689f60028e5b80000000006c3c6bce000a396e000000000222d0196bb000a396e0000000001f6a1ace60028e5b82f82f83e02f82f83e13ae6e06ae0ca6191867a72) (by decide +kernel)
private theorem c2 : WideCovered band 9448884 10067922 := wide_block_sound band profiles 9448884 10067922 (wideData 16 0x1ca3b02cabe40126abc1860061800a99e80aaabec00126abc0000000002a6802ae1c800a396e00000000012ce02838e000a396e0820020805e00a08e20028e5b8000000000882407abe00028e5b80000000007de807687c0028e5b80000000008df407e9be0028e5c00000000007ff4074c7e0028e5b80000000009b740a0ab40028e5b80000000009ab807cb7e0028e5b82080082006c25077fe60028e5b80000000007c60073de00028e5b80000000006eb406ad3a0028e5b800000000088ec074fa60028e5b83883883e03883883e168eed07826d661928ba834) (by decide +kernel)
private theorem c3 : WideCovered band 10067923 10824525 := wide_block_sound band profiles 10067923 10824525 (wideData 11 0x64db822fd720049aaf000000000019a8b08af8980126abc0820020801f5f07feba00126abc000000000732905f2bf80126abc000000000063f341f0b200049aaf00000000001836b05bb5f00126abc000000000064f34164fa20049aaf000000000019bbf04e7cc00126abe0820020806f0843b6dc00126abc000000000063bf8120aa00049aaf03b03b03e03b03b03e1dd62a0a823d38193ab6a20) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6422468 8898625 10824525 c0 (wide_covered_join band 8898626 9448883 10824525 c1 (wide_covered_join band 9448884 10067922 10824525 c2 c3)))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 11)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 11≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤49)
    (hT0 : 4059≤T) (hT1 : T≤4274) (hnu : 6422468≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤10022184552707145 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R024

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R025
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨11,50,3985,4248,10347035358042453⟩
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨33072,8,10160⟩
  | 2 => ⟨41518,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 6553539 8779654 := wide_block_sound band profiles 6553539 8779654 (wideData 16 0x3b716b9a000a3f7e00000000032d95b87c0028fdf82080082002c3d062b320028fdf8000000000ccb036b9800a3f7e0000000003bcf0acf20028fdf8000000001496c6319000a3f7e0000000005eed049b60028fdf8000000001fbe00ecc400a3f7e0000000000709ec37db000a3f7e0000000000a9bb87f1d400a3f7e10400410017bcb93b1b660028fdf80000000004de03ec880061fbe14500514052ebb416ba2f902061fe0000002080177d02e2b80222fdfa7df0018418402ac07500187efe20fa0fa0fa0fa0fa0fa07bd14ca200ecfdea8) (by decide +kernel)
private theorem c1 : WideCovered band 8779655 9336183 := wide_block_sound band profiles 8779655 9336183 (wideData 16 0xde71072bfa0028fdf82080082008c300689b00028fdf80000000008bbc061f320028fdf80000000009f6c069c3e0028fdf8000000000a8b0065d280028fdf8000000000ac740638b60028fdf8000000000d8ec0709fe0028fdf8000000000adb8065bb00028fdf80000000011a2d066de80028fdf82080082005b380668a40028fdf800000000098b867ee000a3f7e00000000027f919c360028fdf8000000000ccbc065d6e0028fdf8000000000cda8675e000a3f7e0000000003b6d19aa80028fdf82f82f83e82f82f83e96838e068b7e24110e7fdac) (by decide +kernel)
private theorem c2 : WideCovered band 9336184 9892712 := wide_block_sound band profiles 9336184 9892712 (wideData 16 0x2f0801fb2e000a3f7e082002080177e41fa6b000a3f7e0000000002a2d01ebda800a3f7e000000000265c01c7f8800a3f7e00000000026f801ca8c800a3f7e0000000002e3d01f65a000a3f7e0000000002a9a01cf8b800a3f7e0000000002b9e01d34d000a3f7e0000000002ac0a1cf00028fdf8208008200182806cef60028fdf80000000008bb4069b240028fdf8000000000a86c073bb00028fdf80000000009a6406aab20028fdf80000000009ea006ae780028fdf8000000000bebc076f3c0028fdf83883883e83883883e99d3ab06d62aee111efed6e) (by decide +kernel)
private theorem c3 : WideCovered band 9892713 10866638 := wide_block_sound band profiles 9892713 10866638 (wideData 16 0x1afed08a76c00127efc000000000065fb01a89b80049fbf00000000001bf6c07fedb80127efc0000000000749a82218a60049fbf0208008200bde513dcf00049fbf0000000000197cd05a2bb00127efe000000000069efc13df600049fbf00000000001b70f03d29b80127efc0000000000768e8077bae0049fbf00000000002dee902931b00127efc000000000160a24060b2b0049fbf082002080038f4f42ab48720049fbf0000000000bb2c0a5d260028fdf8000000000ab3807c9640028fdf8000000000ad7407ccb20028fdf83983983e83983983e9ddb6a07c23ca2112f7dd30) (by decide +kernel)
private theorem c4 : WideCovered band 10866639 11005770 := wide_block_sound band profiles 10866639 11005770 (wideData 2 0x1c3dd098b2900127efc0f20f20fa0f20f20fa06efed90bfecdfe114eefe38) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6553539 8779654 11005770 c0 (wide_covered_join band 8779655 9336183 11005770 c1 (wide_covered_join band 9336184 9892712 11005770 c2 (wide_covered_join band 9892713 10866638 11005770 c3 c4))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 11)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 11≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤50)
    (hT0 : 3985≤T) (hT1 : T≤4248) (hnu : 6553539≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤10347035358042453 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R025

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R026
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨11,51,3913,4221,10696288606516687⟩
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨33072,8,10160⟩
  | 4 => ⟨41768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 6684610 8408187 := wide_block_sound band profiles 6684610 8408187 (wideData 16 0x4c6022ed00062ae600000000016c80cca40018aba00000000005b642b8f00062ae6000000000175f0ab380018aba00000000006b78360b80062ae60000000001a6f08b720018aba00000000007b3c36cc80062ae60000000001e9a08b360018aba00000000008de837ee00062ae6000000000238e08b740018aba0000000000aca43b5f00062ae60c30030c0572fbc163f67b02062ae80c30030c00fc801c7cf820a4dae0c30030c007e818fae084a6cf0f3c03cf00187432ee82465cf20ec0ec0fc0ec0ec0fc0ac9149f800ef36aa6) (by decide +kernel)
private theorem c1 : WideCovered band 8408188 8900637 := wide_block_sound band profiles 8408188 8900637 (wideData 16 0x3a6917ffe002936b80000000010aa05ee8000a4dae0000000004e7c16e76002936b80000000017ae45a1c800a4dae00000000076dc14fb4002936b8000000000a8644f0a000a4dae0000000000f0c119e0002936b80000000008e7833ef000a4dae0000000005bb903ef0002936b800000000019f45a6c800a4dae000000000068de8526002936b84100104002f2ec4d933e000a4dae0000000000e8f0caf80018ab980000000007e294aaf80062ae800000000013fd4d8fe0018ab982e82e83f02e82e83f17ffe805af6ba22108a8cbe) (by decide +kernel)
private theorem c2 : WideCovered band 8900638 9463438 := wide_block_sound band profiles 8900638 9463438 (wideData 16 0x2e4901a3ed000a4dae0000000002faa01a709800a4dae000000000335b01aa9c000a4dae0000000003a8d01be7f800a4dae000000000278075bf4002936b820800820078e1069abe002936b8000000000aa64060fe8002936b8000000000b824061920002936b8000000000bf60061b30002936b8000000000d860061dfc002936b8000000000ebe0062ae4002936b80000000010ab80639a8002936b80000000004abc064b24002936b80000000010d79066928002936b82080082005838060b3e002936c02f82f83f02f82f83f1b964d068638fa21186ce28) (by decide +kernel)
private theorem c3 : WideCovered band 9463439 10026239 := wide_block_sound band profiles 9463439 10026239 (wideData 16 0xbee0079d20002936b8000000000c96407a868002936b8000000000cc6407ace8002936b8000000000cfe807bab2002936b8000000000dc3007caae002936b8000000000997c07dca8002936b82080082004f31077d7c002936b8000000000ae70070a26002936b8000000000bbfc072e2a002936b8000000000ce780798f8002936b8000000000c9f8072a60002936b8000000000cf3c0739e2002936b8000000000ddb8074bfa002936b8208008200db2d074fac002936b8000000000a8e4068a30002936c03883883f03883883f1f830e06d2c9b62128f7fea) (by decide +kernel)
private theorem c4 : WideCovered band 10026240 11046315 := wide_block_sound band profiles 10026240 11046315 (wideData 16 0x1dfd808eb3d80129b3c000000000079cf8234928004a6cf00000000001e60f0ae30e80129b3c0820020803e1f06de2e80129b3c00000000006dc7817ea78004a6cf00000000001c31a05cf4b00129b3c000000000075e7c167fa0004a6cf00000000001ff2e04f2ac00129b3c08200208072ec46e65b00129b3c00000000006ae280a3c2e004a6cf00000000001ce8f149a4004a6cf00000000002964902934cc0129b3c186006180121d2c0abe7fc80129b3c0000000003b8802a21f800a4dae00000000007f902caf8000a4db00e80e80fc0e80e80fc063ca4f07bf68e62139a39ac) (by decide +kernel)
private theorem c5 : WideCovered band 11046316 11187015 := wide_block_sound band profiles 11046316 11187015 (wideData 2 0x20800820018e1f0bceaa00129b3c0f20f20fc0f20f20fc07abf390ca6eea82159b09f2) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6684610 8408187 11187015 c0 (wide_covered_join band 8408188 8900637 11187015 c1 (wide_covered_join band 8900638 9463438 11187015 c2 (wide_covered_join band 9463439 10026239 11187015 c3 (wide_covered_join band 10026240 11046315 11187015 c4 c5)))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 11)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 11≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤51)
    (hT0 : 3913≤T) (hT1 : T≤4221) (hnu : 6684610≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤10696288606516687 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R026

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R027
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨11,52,3844,4195,18367611252260895⟩
private def profiles : ℕ → Profile
  | 0 => ⟨8268,2,2540⟩
  | 1 => ⟨33072,8,10160⟩
  | 2 => ⟨41768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 6815681 8273929 := wide_block_sound band profiles 6815681 8273929 (wideData 16 0x9b6c2bdd00062dee0000000002aae0b8bc0018b7c0000000000bb6c2e8d80062dee000000000337c0bc340018b7c00000000017f0be7c0018b7b80000000003b2c13ce00062df00000000000aab4bea80018b7b80000000003b79334980062df000000000013394daa40018b7b80000000006a2d3a9b00062df008200208017684e9620018b7b80000000009a741bbf00062df00000000002a8f06cf40018b7b85140145018a6ec04fa8f2a0818b7c00000082006c740aa862084abdf82e82e83f82e02e03f83f30060a6600f96eea2) (by decide +kernel)
private theorem c1 : WideCovered band 8273930 8594032 := wide_block_sound band profiles 8273930 8594032 (wideData 16 0x20800ff9e00709a700296ef84100082009b6f850a38d800a5bbe0000000001f7a0e8ae0018b7b80000000008a3c3acc80062df000000000023d90edfa0018b7b80000000017b0f97a0018b7c00000000005a753f5d80062dee0000000001a8950a6c0018b7c00000000005cf13ade80062dee0820020801f92bbc00062df00000000001a3f0abe40018b7b80000000006c202b0c80062df00000000001bdd0ac7e0018b7b80000000007b702b4980062df00000000001ffc0adb00018b7b82e02e03f82e02e03f9aa7bc059ab9f010fea2e22) (by decide +kernel)
private theorem c2 : WideCovered band 8594033 9163105 := wide_block_sound band profiles 8594033 9163105 (wideData 16 0x3b9b018ba8000a5bbe00000000042b8018f0a000a5be000000000043ad1b96600296ef80000000014974060d7c00296ef80000000001869066a6e00296ef80000000011921068de000296ef820800820079b873cb000a5bbe0000000003ffa1983600296ef80000000011de8568f800a5bbe0000000004f280cd3800296ef80000000019bf85a18000a5bbe0000000007f8d14fb000296ef80000000001a6d813b6800296ef8000000000dbb4462a800a5bbe0000000003f680d82600296ef82f82f83f82f82f83f99870e05e61bbe110bb6d7e) (by decide +kernel)
private theorem c3 : WideCovered band 9163106 9732177 := wide_block_sound band profiles 9163106 9732177 (wideData 16 0xbeb0068ee200296ef8000000000e868072f7e00296ef8000000000ee28073ef000296ef8000000000fcfc07587c00296ef8000000000be6c076ce400296ef8208008200bdf5075a7000296ef8000000000ad2c060bfa00296ef8000000000ce7c069fe200296ef8000000000dc7c06aca800296ef8000000000ebe806bb2200296ef8000000000fce806cba200296ef8000000001183006deec00296ef80000000012d418b3a000a5bbe0820020802eae41b6df000a5bbe0000000003338018a1e000a5bbe0e00e00fe0e00e00fe060f6be069a9aac111c6e960) (by decide +kernel)
private theorem c4 : WideCovered band 9732178 10443518 := wide_block_sound band profiles 9732178 10443518 (wideData 16 0xbaebc5a5e0012af7c0000000002bdb02a33f8012af7c0000000001fa9e80e9def004abdf882002080039faf42c31c24004abdf00000000010da00a6f7800296ef80000000011b300a8f3200296ef80000000001d640aaa2a00296ef820800820089bc07dd6200296ef8000000000e92407b9f200296ef8000000000dde80778e400296ef8000000000e86c076e6600296ef8000000000fc7007d8f200296ef800000000109f007ea6a00296ef80000000004bb007fe6c00296ef8208008200ef01df5d000a5bbe0e40e40fe0e40e40fe065dedc06f38d26112d25d20) (by decide +kernel)
private theorem c5 : WideCovered band 10443519 11368260 := wide_block_sound band profiles 10443519 11368260 (wideData 13 0xb89a83718ec004abdf00000000002b2190b86088012af7c0000000000b8f2033eaaa004abdf02080082001a27a0bf7388012af7c00000000007a9741f9e7c004abdf0000000000297bc09ba3f0012af7c0000000000a98b426bba4004abdf0000000000286bc07869c0012af7c0820020805e01efdfe004abdf00000000001ea4e06b28e0012af7c000000000073c240fbaa0004abdf000000000029f3b05ce790012af7c0f00f00fe0f00f00fe0748b280a9fb96c114878b78) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6815681 8273929 11368260 c0 (wide_covered_join band 8273930 8594032 11368260 c1 (wide_covered_join band 8594033 9163105 11368260 c2 (wide_covered_join band 9163106 9732177 11368260 c3 (wide_covered_join band 9732178 10443518 11368260 c4 c5)))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 11)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 11≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤52)
    (hT0 : 3844≤T) (hT1 : T≤4195) (hnu : 6815681≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤18367611252260895 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R027

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R028
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨11,53,3777,4168,18931392792254785⟩
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨33072,8,10160⟩
  | 4 => ⟨2984,24,635⟩
  | 5 => ⟨42018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 6946752 8079461 := wide_block_sound band profiles 6946752 8079461 (wideData 16 0x20802fba0293a0018e3e0000000001097c17b0018e3d80000000017b2c0febc00638f80000000006203a88800638f600000000006fafc3f9cc00638f80020030000eccf006edab0018e3d82000080004fa0fe56acebaac20638f8000000000064860905f65c260018e3d80000000005ba890ca70b800638f800000000007dff4378af90018e3d800000000158b1a038ecb320018e3e030c00c3003c25ce85abee48020638f600000000013af01c3aa020638f80000020800adb18b640829a7b8b2c034d001aa4326a02471ef00e20e21200e20e21200bfd13da200eae3ce0) (by decide +kernel)
private theorem c1 : WideCovered band 8079462 8367133 := wide_block_sound band profiles 8079462 8367133 (wideData 16 0x3e7933ce800638f80820020800b8e4cb7c0018e3d80000000008d242fcf800638f800000000022d9079f80018e3d800000000098f01e18000638f80000000002bcb0c9340018e3d8000000000afa81bad000638f8000000000323b06be60018e3d8000000000ea382b1f800638f80000000003f4d089b20018e3d80000000011ba4178c000638f80000000002e59059b60018e3d80000000017c4da200018e3e000000000079f8132e000638f600000000023fa03c740018e3e02e02e04802e02e04819bb0e05828bf628fba7aa0) (by decide +kernel)
private theorem c2 : WideCovered band 8367134 8708743 := wide_block_sound band profiles 8367134 8708743 (wideData 16 0x7bf28136c800a69ee0000000000b5c6c061f3d0029a7b84100104006fa5e4f8b28800a69ee0000000001abb0aae20018e3d80000000007bf03b1e000638f80000000001e390abea0018e3d80000000007c602afe000638f8000000000237f0eaf40018e3d80000000008e602f2d800638f800000000026990ae220018e3d8000000000a8742bae000638f80000000002fef10cee0018e3d8000000000bd0baea0018e3e00000000001bfd2f0d000638f60000000001b7b52bbe0018e3e02e82e84802e82e8481dabf9059358e428fff9970) (by decide +kernel)
private theorem c3 : WideCovered band 8708744 9284088 := wide_block_sound band profiles 8708744 9284088 (wideData 16 0x361a019add000a69f000000000033c941a75b800a69ee082002080139068b3c0029a7b8000000000e8e85aee000a69ee000000000475901862c000a69ee00000000046ed159340029a7b80000000016af0061cec0029a7b8000000001a838062db80029a7b8000000001897c4f2e800a69ee00000000027ee419388800a69ee0000000000e2911e7c0029a7b82080082011b7d068c240029a7b80000000016fb853af000a69ee00000000063ae049b20029a7b8000000000187ce10ab60029a7b82f82f84802f82f8481eb24c05de9f76290d77bfc) (by decide +kernel)
private theorem c4 : WideCovered band 9284089 9859432 := wide_block_sound band profiles 9284089 9859432 (wideData 16 0x43cf01d37e000a69ee000000000432b01f7bd000a69ee00000000033e941cfcf000a69ee0820020803b4e01c2bc000a69ee00000000036de019e98000a69ee0000000003ffe01c6da800a69ee00000000043d801cadf000a69ee0000000003fcd01a35c000a69ee0000000004e9801d3db000a69ee00000000013f841ab2d000a69ee0820020800ade41c33b800a69ee0000000003b9b01a3d8800a69ee00000000037a81fab80029a7b80000000010f2006a82c0029a7b8000000001097c7f2f000a69ee0e20e21200e20e2120064cece0697bba6291e3b9be) (by decide +kernel)
private theorem c5 : WideCovered band 9859433 10614571 := wide_block_sound band profiles 9859433 10614571 (wideData 16 0x1f39c02f6d98012cbbc0000000000b8be0131cb0004b2ef0000000000387db01d64004b2ef00000000004eedb04be7cc012cbbc208008200062bf80b3ea8e0012cbbc00000000046cd028f0d000a69ee0000000003f9d01e7da000a69ee0000000004a7b02930b000a69ee000000000436b01eb5a800a69ee0000000004ede029aac000a69ee0000000003a3c029f9a000a69ee08200208013bb41e60b000a69ee0000000003f9b01e65e800a69ee0000000003aca01bfff800a69ee00000000043b901ea9e800a69ee0e60e61200e60e612006abeaa06f60ae8292efef7e) (by decide +kernel)
private theorem c6 : WideCovered band 10614572 11549505 := wide_block_sound band profiles 10614572 11549505 (wideData 13 0x3b6dc0eee1a8012cbbc0000000000ecc643aca30004b2ef02080082001f6cd0dfe2c8012cbbc0000000000bfde43379aa004b2ef00000000002cf4e0ab7380012cbbc0000000000b5ae02a5c32004b2ef00000000001fedd0a866b8012cbbc082002080062e341f9b6c004b2ef00000000002a24e07f66c8012cbbc0000000000adcfc1fd93c004b2ef00000000002b79806c70c8012cbbc0000000002e2e06a6a88012cbbc0f20f21200f20f212007dcb9f0aae8e60294b28872) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6946752 8079461 11549505 c0 (wide_covered_join band 8079462 8367133 11549505 c1 (wide_covered_join band 8367134 8708743 11549505 c2 (wide_covered_join band 8708744 9284088 11549505 c3 (wide_covered_join band 9284089 9859432 11549505 c4 (wide_covered_join band 9859433 10614571 11549505 c5 c6))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 11)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 11≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤53)
    (hT0 : 3777≤T) (hT1 : T≤4168) (hnu : 6946752≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤18931392792254785 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R028

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R029
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨11,54,3713,4140,47233173434858079⟩
private def profiles : ℕ → Profile
  | 0 => ⟨8268,2,2540⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨10041,86,2561⟩
  | 4 => ⟨42268,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 7077823 7981123 := wide_block_sound band profiles 7077823 7981123 (wideData 16 0x19fdeb016fa3be8007d83e000000000071e7af06f7782c001f60f80000000014af1e02d6bb2c001f60f8000000001fafda04a38e74001f60f80000000009df7a018798bc001f60f80000000015c2fc02e2abe4001f60f80000000001a6080dc33fc007d83e0c34430d11a5ef3a1ecbce7e081f60f8000000000000023c0000000001000029e0000000000200004ba0000000000300008f20082002080168d01c29f824788051401450018030018f0802080104002d286258020a6ffe0b60b61220b40b4122135a1fc2000ecefebc) (by decide +kernel)
private theorem c1 : WideCovered band 7981124 8246722 := wide_block_sound band profiles 7981124 8246722 (wideData 16 0xbb381e7f807b0c0000000000cbf41e6a007b0b8000000000de301e4c807b0b8000000000e9f406ba007b0b800000000118ec1b5f007b0c0000000200ce301b1c007b0b80000000004fb81ad9007b0c00000000005bbc1a78007b0b8000000000e8b00a98c07b0c000000800088a813db807b0b80000000009aec12c9007b0c0000000000b92c0f38007b0b8000000000dcb40b0d007b0c0000000000196e90edad01ec2e08240001037182bd41f74bafd427b0c02d82d83c82d82d83c8ea77bf40a2c6a9e218fa61964) (by decide +kernel)
private theorem c2 : WideCovered band 8246723 8496697 := wide_block_sound band profiles 8246723 8496697 (wideData 16 0x8f742adf807b0c00000000009c6c2b2e807b0b8000000000aa202b8e807b0b8000000000b8782bfc007b0b800000000049b01a8c807b0c000000000019f92ead007b0b80000000001db12f5e007b0c00000000002a2d322b807b0b80000000002fe1332c007b0c00000000001b341b2e007b0b80000000004af9370b007b0c02080082004c69379c007b0b80000000008b341f2a007b0c00000000008ffc1f0e807b0b80000000008eac0e3a807b0c02e02e04882e02e0489eeee904fb29fe20fe29b32) (by decide +kernel)
private theorem c3 : WideCovered band 8496698 8981024 := wide_block_sound band profiles 8496698 8981024 (wideData 16 0x48f55bf80007d83e08200208017ba1bb20001f60f8000000000f964367c0007d83e0000000004e1b169e4001f60f80000000015db45acf0007d83e0000000005bbb0acba001f60f8000000001de3457ee8007d83e0000000007feb079e2001f60f8000000000483453fd0007d83c0000000000f8c15aaa001f60f8000000001ce240b1cc007d83e0000000002fad118b4001f60f80000000002abba1cb23001f60f80000000002ba1810be1001f60f84100104007a29d4beedc8007d83e0ba0ba1220ba0ba122060e718058edb7c2109f1d20) (by decide +kernel)
private theorem c4 : WideCovered band 8981025 9480974 := wide_block_sound band profiles 8981025 9480974 (wideData 16 0xdca4062de2001f60f0000000000ccec6eae8007d83e0000000003e3a018f6c8007d83e0000000003af91cd74001f60f800000000118f8064b32001f60f8000000000a9a4066cb2001f60f8000000000697177cd0007d83e08200208017ae4197e80007d83e0000000002ffb15af8001f60f0000000000eb70738e8007d83e0000000003f4a1dcb0001f60f8000000000f92856180007d83e0000000004b681ed30001f60f80000000012de0562e8007d83e0000000001bcd0182d98007d83e0e00e01220e00e0122063fe3f05d6b8702119a28be) (by decide +kernel)
private theorem c5 : WideCovered band 9480975 10105913 := wide_block_sound band profiles 9480975 10105913 (wideData 16 0x2b38d0adf4003ea1f00000000003db1d12a77003ea1f00000000006fb9802baecc00fa87c1860061801e68b907583af000fa87c0000000003f9e01b23e0007d83e0000000005290719a2001f60f82080082005b41bb7a0007d83e0000000002ff901864d8007d83e0000000003a0b01a3990007d83c000000000367d018e3c8007d83e0000000003bbe01a28e8007d83e0000000003ffe01ab8f8007d83e0000000003e1d018e0d8007d83e0000000000aca01b3cf0007d83e000000000264a419abd8007d83e0e40e41220e40e4122069df1f06932db2212932c7a) (by decide +kernel)
private theorem c6 : WideCovered band 10105914 11105813 := wide_block_sound band profiles 10105914 11105813 (wideData 16 0x7deec1bc876003ea1f00000000001ff3806eb9f000fa87c0820020805bed07bb6a800fa87a000000000074ef0175be4003ea1f00000000001cf5f059afc800fa87c00000000007692c1658f4003ea1f00000000001e7ae05962b000fa87a0820020800a6c45bb9f000fa87c00000000006fcb4128fe8003ea1f00000000001be9d03d748800fa87c000000000073ff80f1fea003ea1e80000000001eebe03bb19800fa87c000000000129122862003ea1f0208008200fc280e9f20003ea1f00000000001c2ec01e6da000fa87a0ec0ec1220ec0ec122074af0f089a7dee213b3496e) (by decide +kernel)
private theorem c7 : WideCovered band 11105814 11730750 := wide_block_sound band profiles 11105814 11730750 (wideData 10 0xe3e3833697c003ea1e80000000003877b0ca758800fa87c0000000000e9e7036ac36003ea1f0000000000286390c8249800fa87c0820020800aab7826de22003ea1e80000000002afce09979c800fa87c0000000000abff8260e3a003ea1f00000000002d24d09ff1e000fa87c08200208077bf08823d800fa87a0f20f21220f20f21220aa867a0ad65cb8215a758e6) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7077823 7981123 11730750 c0 (wide_covered_join band 7981124 8246722 11730750 c1 (wide_covered_join band 8246723 8496697 11730750 c2 (wide_covered_join band 8496698 8981024 11730750 c3 (wide_covered_join band 8981025 9480974 11730750 c4 (wide_covered_join band 9480975 10105913 11730750 c5 (wide_covered_join band 10105914 11105813 11730750 c6 c7)))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 11)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 11≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤54)
    (hT0 : 3713≤T) (hT1 : T≤4140) (hnu : 7077823≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤47233173434858079 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R029
