import ProximityPrize.SubmissionLower.RelativeWideBlocks6815
set_option Elab.async false
section MergedPart0
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R024
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨11,49,4059,4274,10022184552707145⟩
private def profiles_RelativeWidePack6815_P04 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨41268,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P04 : WideCovered band 6422468 8898625 := wide_block_sound band profiles_RelativeWidePack6815_P04 6422468 8898625 (wideData 16 0xaefc068a740028e5b8000000000b8a46f6c800a396e0000000007fc06bfba0028e5b8000000000fff1773e000a396e0820020801efe1cfbc0028e5b80000000009a70738d800a396e00000000026ab0fc640028e5b8000000000c9f872dd800a397000000000036490c96c0028e5b80000000011fac6f99000a396e0c30030c0431a7017f8eeb020a396e00000000006ae19c660828e5b830c00c3016a0ce30088b35e19640659005c01940439af2068068001a81a800fc076001872de20b00b00f80ae0ae0f8070e14e7000eae5aac) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P04 : WideCovered band 8898626 9448883 := wide_block_sound band profiles_RelativeWidePack6815_P04 8898626 9448883 (wideData 16 0x234d01d22b000a396e00000000026fe01e33f000a396e000000000062f01bb0c800a396e0820020800beb41c33c800a396e0000000001acc018b98000a396e0000000001f5c01b2ce000a396e000000000225a01b71d800a396e0000000001f4e018f3f800a397000000000026cf01bfab800a396e0000000002628019648800a396e0000000001a6a41cf29000a396e0820020801b90689f60028e5b80000000006c3c6bce000a396e000000000222d0196bb000a396e0000000001f6a1ace60028e5b82f82f83e02f82f83e13ae6e06ae0ca6191867a72) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P04 : WideCovered band 9448884 10067922 := wide_block_sound band profiles_RelativeWidePack6815_P04 9448884 10067922 (wideData 16 0x1ca3b02cabe40126abc1860061800a99e80aaabec00126abc0000000002a6802ae1c800a396e00000000012ce02838e000a396e0820020805e00a08e20028e5b8000000000882407abe00028e5b80000000007de807687c0028e5b80000000008df407e9be0028e5c00000000007ff4074c7e0028e5b80000000009b740a0ab40028e5b80000000009ab807cb7e0028e5b82080082006c25077fe60028e5b80000000007c60073de00028e5b80000000006eb406ad3a0028e5b800000000088ec074fa60028e5b83883883e03883883e168eed07826d661928ba834) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P04 : WideCovered band 10067923 10824525 := wide_block_sound band profiles_RelativeWidePack6815_P04 10067923 10824525 (wideData 11 0x64db822fd720049aaf000000000019a8b08af8980126abc0820020801f5f07feba00126abc000000000732905f2bf80126abc000000000063f341f0b200049aaf00000000001836b05bb5f00126abc000000000064f34164fa20049aaf000000000019bbf04e7cc00126abe0820020806f0843b6dc00126abc000000000063bf8120aa00049aaf03b03b03e03b03b03e1dd62a0a823d38193ab6a20) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6422468 8898625 10824525 c0_RelativeWidePack6815_P04 (wide_covered_join band 8898626 9448883 10824525 c1_RelativeWidePack6815_P04 (wide_covered_join band 9448884 10067922 10824525 c2_RelativeWidePack6815_P04 c3_RelativeWidePack6815_P04)))
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
private def profiles_RelativeWidePack6815_P04 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨33072,8,10160⟩
  | 2 => ⟨41518,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P04 : WideCovered band 6553539 8779654 := wide_block_sound band profiles_RelativeWidePack6815_P04 6553539 8779654 (wideData 16 0x3b716b9a000a3f7e00000000032d95b87c0028fdf82080082002c3d062b320028fdf8000000000ccb036b9800a3f7e0000000003bcf0acf20028fdf8000000001496c6319000a3f7e0000000005eed049b60028fdf8000000001fbe00ecc400a3f7e0000000000709ec37db000a3f7e0000000000a9bb87f1d400a3f7e10400410017bcb93b1b660028fdf80000000004de03ec880061fbe14500514052ebb416ba2f902061fe0000002080177d02e2b80222fdfa7df0018418402ac07500187efe20fa0fa0fa0fa0fa0fa07bd14ca200ecfdea8) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P04 : WideCovered band 8779655 9336183 := wide_block_sound band profiles_RelativeWidePack6815_P04 8779655 9336183 (wideData 16 0xde71072bfa0028fdf82080082008c300689b00028fdf80000000008bbc061f320028fdf80000000009f6c069c3e0028fdf8000000000a8b0065d280028fdf8000000000ac740638b60028fdf8000000000d8ec0709fe0028fdf8000000000adb8065bb00028fdf80000000011a2d066de80028fdf82080082005b380668a40028fdf800000000098b867ee000a3f7e00000000027f919c360028fdf8000000000ccbc065d6e0028fdf8000000000cda8675e000a3f7e0000000003b6d19aa80028fdf82f82f83e82f82f83e96838e068b7e24110e7fdac) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P04 : WideCovered band 9336184 9892712 := wide_block_sound band profiles_RelativeWidePack6815_P04 9336184 9892712 (wideData 16 0x2f0801fb2e000a3f7e082002080177e41fa6b000a3f7e0000000002a2d01ebda800a3f7e000000000265c01c7f8800a3f7e00000000026f801ca8c800a3f7e0000000002e3d01f65a000a3f7e0000000002a9a01cf8b800a3f7e0000000002b9e01d34d000a3f7e0000000002ac0a1cf00028fdf8208008200182806cef60028fdf80000000008bb4069b240028fdf8000000000a86c073bb00028fdf80000000009a6406aab20028fdf80000000009ea006ae780028fdf8000000000bebc076f3c0028fdf83883883e83883883e99d3ab06d62aee111efed6e) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P04 : WideCovered band 9892713 10866638 := wide_block_sound band profiles_RelativeWidePack6815_P04 9892713 10866638 (wideData 16 0x1afed08a76c00127efc000000000065fb01a89b80049fbf00000000001bf6c07fedb80127efc0000000000749a82218a60049fbf0208008200bde513dcf00049fbf0000000000197cd05a2bb00127efe000000000069efc13df600049fbf00000000001b70f03d29b80127efc0000000000768e8077bae0049fbf00000000002dee902931b00127efc000000000160a24060b2b0049fbf082002080038f4f42ab48720049fbf0000000000bb2c0a5d260028fdf8000000000ab3807c9640028fdf8000000000ad7407ccb20028fdf83983983e83983983e9ddb6a07c23ca2112f7dd30) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P04 : WideCovered band 10866639 11005770 := wide_block_sound band profiles_RelativeWidePack6815_P04 10866639 11005770 (wideData 2 0x1c3dd098b2900127efc0f20f20fa0f20f20fa06efed90bfecdfe114eefe38) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6553539 8779654 11005770 c0_RelativeWidePack6815_P04 (wide_covered_join band 8779655 9336183 11005770 c1_RelativeWidePack6815_P04 (wide_covered_join band 9336184 9892712 11005770 c2_RelativeWidePack6815_P04 (wide_covered_join band 9892713 10866638 11005770 c3_RelativeWidePack6815_P04 c4_RelativeWidePack6815_P04))))
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
private def profiles_RelativeWidePack6815_P04 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨33072,8,10160⟩
  | 4 => ⟨41768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P04 : WideCovered band 6684610 8408187 := wide_block_sound band profiles_RelativeWidePack6815_P04 6684610 8408187 (wideData 16 0x4c6022ed00062ae600000000016c80cca40018aba00000000005b642b8f00062ae6000000000175f0ab380018aba00000000006b78360b80062ae60000000001a6f08b720018aba00000000007b3c36cc80062ae60000000001e9a08b360018aba00000000008de837ee00062ae6000000000238e08b740018aba0000000000aca43b5f00062ae60c30030c0572fbc163f67b02062ae80c30030c00fc801c7cf820a4dae0c30030c007e818fae084a6cf0f3c03cf00187432ee82465cf20ec0ec0fc0ec0ec0fc0ac9149f800ef36aa6) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P04 : WideCovered band 8408188 8900637 := wide_block_sound band profiles_RelativeWidePack6815_P04 8408188 8900637 (wideData 16 0x3a6917ffe002936b80000000010aa05ee8000a4dae0000000004e7c16e76002936b80000000017ae45a1c800a4dae00000000076dc14fb4002936b8000000000a8644f0a000a4dae0000000000f0c119e0002936b80000000008e7833ef000a4dae0000000005bb903ef0002936b800000000019f45a6c800a4dae000000000068de8526002936b84100104002f2ec4d933e000a4dae0000000000e8f0caf80018ab980000000007e294aaf80062ae800000000013fd4d8fe0018ab982e82e83f02e82e83f17ffe805af6ba22108a8cbe) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P04 : WideCovered band 8900638 9463438 := wide_block_sound band profiles_RelativeWidePack6815_P04 8900638 9463438 (wideData 16 0x2e4901a3ed000a4dae0000000002faa01a709800a4dae000000000335b01aa9c000a4dae0000000003a8d01be7f800a4dae000000000278075bf4002936b820800820078e1069abe002936b8000000000aa64060fe8002936b8000000000b824061920002936b8000000000bf60061b30002936b8000000000d860061dfc002936b8000000000ebe0062ae4002936b80000000010ab80639a8002936b80000000004abc064b24002936b80000000010d79066928002936b82080082005838060b3e002936c02f82f83f02f82f83f1b964d068638fa21186ce28) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P04 : WideCovered band 9463439 10026239 := wide_block_sound band profiles_RelativeWidePack6815_P04 9463439 10026239 (wideData 16 0xbee0079d20002936b8000000000c96407a868002936b8000000000cc6407ace8002936b8000000000cfe807bab2002936b8000000000dc3007caae002936b8000000000997c07dca8002936b82080082004f31077d7c002936b8000000000ae70070a26002936b8000000000bbfc072e2a002936b8000000000ce780798f8002936b8000000000c9f8072a60002936b8000000000cf3c0739e2002936b8000000000ddb8074bfa002936b8208008200db2d074fac002936b8000000000a8e4068a30002936c03883883f03883883f1f830e06d2c9b62128f7fea) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P04 : WideCovered band 10026240 11046315 := wide_block_sound band profiles_RelativeWidePack6815_P04 10026240 11046315 (wideData 16 0x1dfd808eb3d80129b3c000000000079cf8234928004a6cf00000000001e60f0ae30e80129b3c0820020803e1f06de2e80129b3c00000000006dc7817ea78004a6cf00000000001c31a05cf4b00129b3c000000000075e7c167fa0004a6cf00000000001ff2e04f2ac00129b3c08200208072ec46e65b00129b3c00000000006ae280a3c2e004a6cf00000000001ce8f149a4004a6cf00000000002964902934cc0129b3c186006180121d2c0abe7fc80129b3c0000000003b8802a21f800a4dae00000000007f902caf8000a4db00e80e80fc0e80e80fc063ca4f07bf68e62139a39ac) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P04 : WideCovered band 11046316 11187015 := wide_block_sound band profiles_RelativeWidePack6815_P04 11046316 11187015 (wideData 2 0x20800820018e1f0bceaa00129b3c0f20f20fc0f20f20fc07abf390ca6eea82159b09f2) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6684610 8408187 11187015 c0_RelativeWidePack6815_P04 (wide_covered_join band 8408188 8900637 11187015 c1_RelativeWidePack6815_P04 (wide_covered_join band 8900638 9463438 11187015 c2_RelativeWidePack6815_P04 (wide_covered_join band 9463439 10026239 11187015 c3_RelativeWidePack6815_P04 (wide_covered_join band 10026240 11046315 11187015 c4_RelativeWidePack6815_P04 c5_RelativeWidePack6815_P04)))))
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
private def profiles_RelativeWidePack6815_P04 : ℕ → Profile
  | 0 => ⟨8268,2,2540⟩
  | 1 => ⟨33072,8,10160⟩
  | 2 => ⟨41768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P04 : WideCovered band 6815681 8273929 := wide_block_sound band profiles_RelativeWidePack6815_P04 6815681 8273929 (wideData 16 0x9b6c2bdd00062dee0000000002aae0b8bc0018b7c0000000000bb6c2e8d80062dee000000000337c0bc340018b7c00000000017f0be7c0018b7b80000000003b2c13ce00062df00000000000aab4bea80018b7b80000000003b79334980062df000000000013394daa40018b7b80000000006a2d3a9b00062df008200208017684e9620018b7b80000000009a741bbf00062df00000000002a8f06cf40018b7b85140145018a6ec04fa8f2a0818b7c00000082006c740aa862084abdf82e82e83f82e02e03f83f30060a6600f96eea2) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P04 : WideCovered band 8273930 8594032 := wide_block_sound band profiles_RelativeWidePack6815_P04 8273930 8594032 (wideData 16 0x20800ff9e00709a700296ef84100082009b6f850a38d800a5bbe0000000001f7a0e8ae0018b7b80000000008a3c3acc80062df000000000023d90edfa0018b7b80000000017b0f97a0018b7c00000000005a753f5d80062dee0000000001a8950a6c0018b7c00000000005cf13ade80062dee0820020801f92bbc00062df00000000001a3f0abe40018b7b80000000006c202b0c80062df00000000001bdd0ac7e0018b7b80000000007b702b4980062df00000000001ffc0adb00018b7b82e02e03f82e02e03f9aa7bc059ab9f010fea2e22) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P04 : WideCovered band 8594033 9163105 := wide_block_sound band profiles_RelativeWidePack6815_P04 8594033 9163105 (wideData 16 0x3b9b018ba8000a5bbe00000000042b8018f0a000a5be000000000043ad1b96600296ef80000000014974060d7c00296ef80000000001869066a6e00296ef80000000011921068de000296ef820800820079b873cb000a5bbe0000000003ffa1983600296ef80000000011de8568f800a5bbe0000000004f280cd3800296ef80000000019bf85a18000a5bbe0000000007f8d14fb000296ef80000000001a6d813b6800296ef8000000000dbb4462a800a5bbe0000000003f680d82600296ef82f82f83f82f82f83f99870e05e61bbe110bb6d7e) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P04 : WideCovered band 9163106 9732177 := wide_block_sound band profiles_RelativeWidePack6815_P04 9163106 9732177 (wideData 16 0xbeb0068ee200296ef8000000000e868072f7e00296ef8000000000ee28073ef000296ef8000000000fcfc07587c00296ef8000000000be6c076ce400296ef8208008200bdf5075a7000296ef8000000000ad2c060bfa00296ef8000000000ce7c069fe200296ef8000000000dc7c06aca800296ef8000000000ebe806bb2200296ef8000000000fce806cba200296ef8000000001183006deec00296ef80000000012d418b3a000a5bbe0820020802eae41b6df000a5bbe0000000003338018a1e000a5bbe0e00e00fe0e00e00fe060f6be069a9aac111c6e960) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P04 : WideCovered band 9732178 10443518 := wide_block_sound band profiles_RelativeWidePack6815_P04 9732178 10443518 (wideData 16 0xbaebc5a5e0012af7c0000000002bdb02a33f8012af7c0000000001fa9e80e9def004abdf882002080039faf42c31c24004abdf00000000010da00a6f7800296ef80000000011b300a8f3200296ef80000000001d640aaa2a00296ef820800820089bc07dd6200296ef8000000000e92407b9f200296ef8000000000dde80778e400296ef8000000000e86c076e6600296ef8000000000fc7007d8f200296ef800000000109f007ea6a00296ef80000000004bb007fe6c00296ef8208008200ef01df5d000a5bbe0e40e40fe0e40e40fe065dedc06f38d26112d25d20) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P04 : WideCovered band 10443519 11368260 := wide_block_sound band profiles_RelativeWidePack6815_P04 10443519 11368260 (wideData 13 0xb89a83718ec004abdf00000000002b2190b86088012af7c0000000000b8f2033eaaa004abdf02080082001a27a0bf7388012af7c00000000007a9741f9e7c004abdf0000000000297bc09ba3f0012af7c0000000000a98b426bba4004abdf0000000000286bc07869c0012af7c0820020805e01efdfe004abdf00000000001ea4e06b28e0012af7c000000000073c240fbaa0004abdf000000000029f3b05ce790012af7c0f00f00fe0f00f00fe0748b280a9fb96c114878b78) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6815681 8273929 11368260 c0_RelativeWidePack6815_P04 (wide_covered_join band 8273930 8594032 11368260 c1_RelativeWidePack6815_P04 (wide_covered_join band 8594033 9163105 11368260 c2_RelativeWidePack6815_P04 (wide_covered_join band 9163106 9732177 11368260 c3_RelativeWidePack6815_P04 (wide_covered_join band 9732178 10443518 11368260 c4_RelativeWidePack6815_P04 c5_RelativeWidePack6815_P04)))))
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
private def profiles_RelativeWidePack6815_P04 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨33072,8,10160⟩
  | 4 => ⟨2984,24,635⟩
  | 5 => ⟨42018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P04 : WideCovered band 6946752 8079461 := wide_block_sound band profiles_RelativeWidePack6815_P04 6946752 8079461 (wideData 16 0x20802fba0293a0018e3e0000000001097c17b0018e3d80000000017b2c0febc00638f80000000006203a88800638f600000000006fafc3f9cc00638f80020030000eccf006edab0018e3d82000080004fa0fe56acebaac20638f8000000000064860905f65c260018e3d80000000005ba890ca70b800638f800000000007dff4378af90018e3d800000000158b1a038ecb320018e3e030c00c3003c25ce85abee48020638f600000000013af01c3aa020638f80000020800adb18b640829a7b8b2c034d001aa4326a02471ef00e20e21200e20e21200bfd13da200eae3ce0) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P04 : WideCovered band 8079462 8367133 := wide_block_sound band profiles_RelativeWidePack6815_P04 8079462 8367133 (wideData 16 0x3e7933ce800638f80820020800b8e4cb7c0018e3d80000000008d242fcf800638f800000000022d9079f80018e3d800000000098f01e18000638f80000000002bcb0c9340018e3d8000000000afa81bad000638f8000000000323b06be60018e3d8000000000ea382b1f800638f80000000003f4d089b20018e3d80000000011ba4178c000638f80000000002e59059b60018e3d80000000017c4da200018e3e000000000079f8132e000638f600000000023fa03c740018e3e02e02e04802e02e04819bb0e05828bf628fba7aa0) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P04 : WideCovered band 8367134 8708743 := wide_block_sound band profiles_RelativeWidePack6815_P04 8367134 8708743 (wideData 16 0x7bf28136c800a69ee0000000000b5c6c061f3d0029a7b84100104006fa5e4f8b28800a69ee0000000001abb0aae20018e3d80000000007bf03b1e000638f80000000001e390abea0018e3d80000000007c602afe000638f8000000000237f0eaf40018e3d80000000008e602f2d800638f800000000026990ae220018e3d8000000000a8742bae000638f80000000002fef10cee0018e3d8000000000bd0baea0018e3e00000000001bfd2f0d000638f60000000001b7b52bbe0018e3e02e82e84802e82e8481dabf9059358e428fff9970) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P04 : WideCovered band 8708744 9284088 := wide_block_sound band profiles_RelativeWidePack6815_P04 8708744 9284088 (wideData 16 0x361a019add000a69f000000000033c941a75b800a69ee082002080139068b3c0029a7b8000000000e8e85aee000a69ee000000000475901862c000a69ee00000000046ed159340029a7b80000000016af0061cec0029a7b8000000001a838062db80029a7b8000000001897c4f2e800a69ee00000000027ee419388800a69ee0000000000e2911e7c0029a7b82080082011b7d068c240029a7b80000000016fb853af000a69ee00000000063ae049b20029a7b8000000000187ce10ab60029a7b82f82f84802f82f8481eb24c05de9f76290d77bfc) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P04 : WideCovered band 9284089 9859432 := wide_block_sound band profiles_RelativeWidePack6815_P04 9284089 9859432 (wideData 16 0x43cf01d37e000a69ee000000000432b01f7bd000a69ee00000000033e941cfcf000a69ee0820020803b4e01c2bc000a69ee00000000036de019e98000a69ee0000000003ffe01c6da800a69ee00000000043d801cadf000a69ee0000000003fcd01a35c000a69ee0000000004e9801d3db000a69ee00000000013f841ab2d000a69ee0820020800ade41c33b800a69ee0000000003b9b01a3d8800a69ee00000000037a81fab80029a7b80000000010f2006a82c0029a7b8000000001097c7f2f000a69ee0e20e21200e20e2120064cece0697bba6291e3b9be) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P04 : WideCovered band 9859433 10614571 := wide_block_sound band profiles_RelativeWidePack6815_P04 9859433 10614571 (wideData 16 0x1f39c02f6d98012cbbc0000000000b8be0131cb0004b2ef0000000000387db01d64004b2ef00000000004eedb04be7cc012cbbc208008200062bf80b3ea8e0012cbbc00000000046cd028f0d000a69ee0000000003f9d01e7da000a69ee0000000004a7b02930b000a69ee000000000436b01eb5a800a69ee0000000004ede029aac000a69ee0000000003a3c029f9a000a69ee08200208013bb41e60b000a69ee0000000003f9b01e65e800a69ee0000000003aca01bfff800a69ee00000000043b901ea9e800a69ee0e60e61200e60e612006abeaa06f60ae8292efef7e) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P04 : WideCovered band 10614572 11549505 := wide_block_sound band profiles_RelativeWidePack6815_P04 10614572 11549505 (wideData 13 0x3b6dc0eee1a8012cbbc0000000000ecc643aca30004b2ef02080082001f6cd0dfe2c8012cbbc0000000000bfde43379aa004b2ef00000000002cf4e0ab7380012cbbc0000000000b5ae02a5c32004b2ef00000000001fedd0a866b8012cbbc082002080062e341f9b6c004b2ef00000000002a24e07f66c8012cbbc0000000000adcfc1fd93c004b2ef00000000002b79806c70c8012cbbc0000000002e2e06a6a88012cbbc0f20f21200f20f212007dcb9f0aae8e60294b28872) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6946752 8079461 11549505 c0_RelativeWidePack6815_P04 (wide_covered_join band 8079462 8367133 11549505 c1_RelativeWidePack6815_P04 (wide_covered_join band 8367134 8708743 11549505 c2_RelativeWidePack6815_P04 (wide_covered_join band 8708744 9284088 11549505 c3_RelativeWidePack6815_P04 (wide_covered_join band 9284089 9859432 11549505 c4_RelativeWidePack6815_P04 (wide_covered_join band 9859433 10614571 11549505 c5_RelativeWidePack6815_P04 c6_RelativeWidePack6815_P04))))))
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
private def profiles_RelativeWidePack6815_P04 : ℕ → Profile
  | 0 => ⟨8268,2,2540⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨10041,86,2561⟩
  | 4 => ⟨42268,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P04 : WideCovered band 7077823 7981123 := wide_block_sound band profiles_RelativeWidePack6815_P04 7077823 7981123 (wideData 16 0x19fdeb016fa3be8007d83e000000000071e7af06f7782c001f60f80000000014af1e02d6bb2c001f60f8000000001fafda04a38e74001f60f80000000009df7a018798bc001f60f80000000015c2fc02e2abe4001f60f80000000001a6080dc33fc007d83e0c34430d11a5ef3a1ecbce7e081f60f8000000000000023c0000000001000029e0000000000200004ba0000000000300008f20082002080168d01c29f824788051401450018030018f0802080104002d286258020a6ffe0b60b61220b40b4122135a1fc2000ecefebc) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P04 : WideCovered band 7981124 8246722 := wide_block_sound band profiles_RelativeWidePack6815_P04 7981124 8246722 (wideData 16 0xbb381e7f807b0c0000000000cbf41e6a007b0b8000000000de301e4c807b0b8000000000e9f406ba007b0b800000000118ec1b5f007b0c0000000200ce301b1c007b0b80000000004fb81ad9007b0c00000000005bbc1a78007b0b8000000000e8b00a98c07b0c000000800088a813db807b0b80000000009aec12c9007b0c0000000000b92c0f38007b0b8000000000dcb40b0d007b0c0000000000196e90edad01ec2e08240001037182bd41f74bafd427b0c02d82d83c82d82d83c8ea77bf40a2c6a9e218fa61964) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P04 : WideCovered band 8246723 8496697 := wide_block_sound band profiles_RelativeWidePack6815_P04 8246723 8496697 (wideData 16 0x8f742adf807b0c00000000009c6c2b2e807b0b8000000000aa202b8e807b0b8000000000b8782bfc007b0b800000000049b01a8c807b0c000000000019f92ead007b0b80000000001db12f5e007b0c00000000002a2d322b807b0b80000000002fe1332c007b0c00000000001b341b2e007b0b80000000004af9370b007b0c02080082004c69379c007b0b80000000008b341f2a007b0c00000000008ffc1f0e807b0b80000000008eac0e3a807b0c02e02e04882e02e0489eeee904fb29fe20fe29b32) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P04 : WideCovered band 8496698 8981024 := wide_block_sound band profiles_RelativeWidePack6815_P04 8496698 8981024 (wideData 16 0x48f55bf80007d83e08200208017ba1bb20001f60f8000000000f964367c0007d83e0000000004e1b169e4001f60f80000000015db45acf0007d83e0000000005bbb0acba001f60f8000000001de3457ee8007d83e0000000007feb079e2001f60f8000000000483453fd0007d83c0000000000f8c15aaa001f60f8000000001ce240b1cc007d83e0000000002fad118b4001f60f80000000002abba1cb23001f60f80000000002ba1810be1001f60f84100104007a29d4beedc8007d83e0ba0ba1220ba0ba122060e718058edb7c2109f1d20) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P04 : WideCovered band 8981025 9480974 := wide_block_sound band profiles_RelativeWidePack6815_P04 8981025 9480974 (wideData 16 0xdca4062de2001f60f0000000000ccec6eae8007d83e0000000003e3a018f6c8007d83e0000000003af91cd74001f60f800000000118f8064b32001f60f8000000000a9a4066cb2001f60f8000000000697177cd0007d83e08200208017ae4197e80007d83e0000000002ffb15af8001f60f0000000000eb70738e8007d83e0000000003f4a1dcb0001f60f8000000000f92856180007d83e0000000004b681ed30001f60f80000000012de0562e8007d83e0000000001bcd0182d98007d83e0e00e01220e00e0122063fe3f05d6b8702119a28be) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P04 : WideCovered band 9480975 10105913 := wide_block_sound band profiles_RelativeWidePack6815_P04 9480975 10105913 (wideData 16 0x2b38d0adf4003ea1f00000000003db1d12a77003ea1f00000000006fb9802baecc00fa87c1860061801e68b907583af000fa87c0000000003f9e01b23e0007d83e0000000005290719a2001f60f82080082005b41bb7a0007d83e0000000002ff901864d8007d83e0000000003a0b01a3990007d83c000000000367d018e3c8007d83e0000000003bbe01a28e8007d83e0000000003ffe01ab8f8007d83e0000000003e1d018e0d8007d83e0000000000aca01b3cf0007d83e000000000264a419abd8007d83e0e40e41220e40e4122069df1f06932db2212932c7a) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P04 : WideCovered band 10105914 11105813 := wide_block_sound band profiles_RelativeWidePack6815_P04 10105914 11105813 (wideData 16 0x7deec1bc876003ea1f00000000001ff3806eb9f000fa87c0820020805bed07bb6a800fa87a000000000074ef0175be4003ea1f00000000001cf5f059afc800fa87c00000000007692c1658f4003ea1f00000000001e7ae05962b000fa87a0820020800a6c45bb9f000fa87c00000000006fcb4128fe8003ea1f00000000001be9d03d748800fa87c000000000073ff80f1fea003ea1e80000000001eebe03bb19800fa87c000000000129122862003ea1f0208008200fc280e9f20003ea1f00000000001c2ec01e6da000fa87a0ec0ec1220ec0ec122074af0f089a7dee213b3496e) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P04 : WideCovered band 11105814 11730750 := wide_block_sound band profiles_RelativeWidePack6815_P04 11105814 11730750 (wideData 10 0xe3e3833697c003ea1e80000000003877b0ca758800fa87c0000000000e9e7036ac36003ea1f0000000000286390c8249800fa87c0820020800aab7826de22003ea1e80000000002afce09979c800fa87c0000000000abff8260e3a003ea1f00000000002d24d09ff1e000fa87c08200208077bf08823d800fa87a0f20f21220f20f21220aa867a0ad65cb8215a758e6) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7077823 7981123 11730750 c0_RelativeWidePack6815_P04 (wide_covered_join band 7981124 8246722 11730750 c1_RelativeWidePack6815_P04 (wide_covered_join band 8246723 8496697 11730750 c2_RelativeWidePack6815_P04 (wide_covered_join band 8496698 8981024 11730750 c3_RelativeWidePack6815_P04 (wide_covered_join band 8981025 9480974 11730750 c4_RelativeWidePack6815_P04 (wide_covered_join band 9480975 10105913 11730750 c5_RelativeWidePack6815_P04 (wide_covered_join band 10105914 11105813 11730750 c6_RelativeWidePack6815_P04 c7_RelativeWidePack6815_P04)))))))
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
end MergedPart0
section MergedPart1
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R030
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨11,55,3750,4112,31300588805895278⟩
private def profiles_RelativeWidePack6815_P05 : ℕ → Profile
  | 0 => ⟨16536,4,5080⟩
  | 1 => ⟨33072,8,10160⟩
  | 2 => ⟨2984,24,635⟩
  | 3 => ⟨42518,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P05 : WideCovered band 7208894 8044797 := wide_block_sound band profiles_RelativeWidePack6815_P05 7208894 8044797 (wideData 16 0x1b6c4a926011fa4082000000129c01ea0011fa40000000001f69b8a41b3087ab4247e9000000000019f7af81b9cacc80063f260000000005e0ef80f8c29900063f28000000000070f7d808d7afa00018fc980000000008ca1c018e8ef60018fca0000000001bc7bd04e358240018fc98000000000293ec08e248c0063f280000000000bff6107382cbc0063f2600000000047baa80b0f20c80063f280000000003b7925171af0940063f260000000000b28ace5afaaae90018fca00000000006aa58e4077f69cbe0818fc9830c00c3004bf8070cea0818fca02e02e04902e02e04906a2c07883a00eefc8ba) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P05 : WideCovered band 8044798 8274440 := wide_block_sound band profiles_RelativeWidePack6815_P05 8044798 8274440 (wideData 16 0xb4908d700018fc980000000002efc233b80063f280000000000ebe08b2a0018fc980000000003f6c226b00063f2800200000013df07e680018fc980000002006e2c1e1a00063f28080002000428b02be80018fc983000000002aede1aeb70018fca0200008200396d844ce3900063f260000000000a4847a70011fa40000000007e812180047e900000000001b351ab88047e880000000002a791e2b0047e9000000000018300fcb0047e900000000004e3923fc8047e902e02e04902d82d84918a74804ea8aee18faf2b7c) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P05 : WideCovered band 8274441 8568384 := wide_block_sound band profiles_RelativeWidePack6815_P05 8274441 8568384 (wideData 16 0x17ff4fd240018fc982080082001f6437fa80063f280000000001fad0bda60018fc980000000008834270f00063f28000000000233d09aba0018fc980000000009af0269d80063f280000000002a7909a240018fc98000000000b9fc266a00063f2800000000032f9099300018fc98000000000dfe0263b80063f280000000003f9c098760018fc980000000003b20260d00063f2800000000007f908fa80018fc9800000000028e423ca00063f280000000000a7f08e7e0018fc982e82e84902e82e84918ca5e0586297418fea4f38) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P05 : WideCovered band 8568385 8972557 := wide_block_sound band profiles_RelativeWidePack6815_P05 8568385 8972557 (wideData 16 0x7f5c1293c0029f8b800000000019f1d07cbc0029f8b80000000001d7f8118800a7e2e0000000000afdb8320b400a7e2e0000020800eecf0065b6f0029f8b84100082009bafa50829d000a7e2e0000000001e4e0cb380018fc980000000007cb4330d80063f2800000000022380cd640018fc980000000008d6c33b900063f2800000000026af0d8740018fc98000000000a8f836a880063f280000000000fff0dcb80018fc980000000003a6937ee00063f2800000000012094eb3a0018fc982f02f04902f02f0491bd2dd059a882c190b23828) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P05 : WideCovered band 8972558 9560444 := wide_block_sound band profiles_RelativeWidePack6815_P05 8972558 9560444 (wideData 16 0x428f019eaf800a7e2c00000000047ac01a23f800a7e2e0000000004edb01a65d800a7e2e0000000004e7c41d7ff800a7e2e0820020800e9f0196ff000a7e2e0000000003ae81e8a00029f8b8000000000feb877ea800a7e2e000000000474c1df3a0029f8b80000000013fe877c9000a7e2e0000000005e491e8600029f8b80000000012e707aae000a7e2e0000000001b2b5eef00029f8b80000000009b257fc8000a7e2e0820020800656b89000a7e2e00000000053490ff760029f8b8380380490380380491eaebb05e7f9f619197ca68) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P05 : WideCovered band 9560445 10148332 := wide_block_sound band profiles_RelativeWidePack6815_P05 9560445 10148332 (wideData 16 0xf9e407892c0029f8b8000000000fe68078df00029f8b80000000010be0079c220029f8b80000000011a7407acac0029f8b80000000014d01efeb800a7e2e08200208006fd01d218800a7e2e000000000377f01bacf800a7e2e000000000424b01e36f000a7e2e0000000003e6801bfec800a7e2e000000000422801c32a800a7e2e000000000465a01c73c000a7e2e00000000006df01ce0f000a7e2e08200208017ad41bec8800a7e2e000000000368b019a7c800a7e2e0000000003a2a019af8800a7e2e0e40e41240e40e4124063caf906ab7e70192a78c26) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P05 : WideCovered band 10148333 11030164 := wide_block_sound band profiles_RelativeWidePack6815_P05 10148333 11030164 (wideData 16 0x2aba906e7c80012fc3c0000000000b5c341add6a004bf0f02080082001968e45beba0012fc3c0000000000a8af41719fa004bf0f000000000029afc01ff180012fc3c0000000000bc8b82f294012fc3c000000000130c7c172c67004bf0f08200208001f33e02ee8da0004bf0f000000000109b00a2a320029f8b80000000010ca00a2cae0029f8b800000000119700a48200029f8b80000000013b280ae8200029f8b800000000129b80a58a20029f8b80000000006f429aac800a7e2e082002080229f01eb0b800a7e2e0e80e81240e80e8124069a6bd0792cea4193b74de6) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P05 : WideCovered band 11030165 11911995 := wide_block_sound band profiles_RelativeWidePack6815_P05 11030165 11911995 (wideData 12 0x132cfc57fb38004bf0e82080082002da0e12eb590012fc3c0000000000eeef4428bf8004bf0f00000000003f22c129eb80012fc3c0000000000ed9fc3e8df2004bf0f02080082001b37c0ccb8b8012fc3c0000000000b393c2e79ae004bf0f00000000002d24e0aeffc0012fc3c0000000000b78602b4a6a004bf0f0208008201e9702f0bbc004bf0f0000000000287aa07ca180012fc3c0f40f41240f40f41240a0863e0baa1df0195976ea4) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7208894 8044797 11911995 c0_RelativeWidePack6815_P05 (wide_covered_join band 8044798 8274440 11911995 c1_RelativeWidePack6815_P05 (wide_covered_join band 8274441 8568384 11911995 c2_RelativeWidePack6815_P05 (wide_covered_join band 8568385 8972557 11911995 c3_RelativeWidePack6815_P05 (wide_covered_join band 8972558 9560444 11911995 c4_RelativeWidePack6815_P05 (wide_covered_join band 9560445 10148332 11911995 c5_RelativeWidePack6815_P05 (wide_covered_join band 10148333 11030164 11911995 c6_RelativeWidePack6815_P05 c7_RelativeWidePack6815_P05)))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 11)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 11≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤55)
    (hT0 : 3750≤T) (hT1 : T≤4112) (hnu : 7208894≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤31300588805895278 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R030

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R031
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨11,56,3750,4084,30760068026545820⟩
private def profiles_RelativeWidePack6815_P05 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨2984,24,635⟩
  | 4 => ⟨42518,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P05 : WideCovered band 7339965 8026962 := wide_block_sound band profiles_RelativeWidePack6815_P05 7339965 8026962 (wideData 16 0x1c33970261ff7e00064a300000000000a89b6e0df69b70001928b8000000000fe26802daef66001928c000000000018bdf281b5961e80064a2e000000000174b204fef30001928c00000000001e69c0a934cc0064a2e0000000004f99e40effa6c00064a30000000000165ef50ab93dec0064a2e00000000037bba8074fe7b00064a3000000000063aff1278db4840064a2e000000000065aee808b72fea001928c00000000002cf6fb4671b62c824a49830c00c3001803012928000000000123f01c33b02064a300820020800e3b0192ec022628f80b60b61260b60b61260b5d13caa00eca48e8) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P05 : WideCovered band 8026963 8231204 := wide_block_sound band profiles_RelativeWidePack6815_P05 8026963 8231204 (wideData 16 0xaa240a7e00064a2e000000000433b01a25001928c00080000012c255f3c00064a2e000002080060e2026fd40064a30080000000065e0eefc001928b8000008201ddfd0f0ba6001928c00000000001b391aae004a4980000000002f3407a9004a4a00000000001ded1b1f804a4a000000000029711bb8004a4a00000000002d7d1e59004a49800000000039bc0749004a4a00000000003bf91f58004a4a00000000004b79226d804a4a00000000003ce006bd804a4982e02e04982d82d84996a2ec04ea38ec20faafe6c) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P05 : WideCovered band 8231205 8528283 := wide_block_sound band profiles_RelativeWidePack6815_P05 8231205 8528283 (wideData 16 0x1b7e07cf0001928b8000000000882c32a980064a2e0000000001fbd07afa001928b80000000009b30330f80064a3000000000026da07922001928b8000000000ab341ba800064a30000000000330f0cf20001928b8000000000d8a01aee00064a300000000003fcf0daee001928b80000000008ba41a1b00064a30000000000135c05cf8001928b80000000002e2937fe80064a3000000000017eb04db8001928b80000000004dbd3ecf00064a300000000001f3f03db4001928b82e82e84982e82e849969b4d05832d7620fdf0eb8) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P05 : WideCovered band 8528284 8862498 := wide_block_sound band profiles_RelativeWidePack6815_P05 8528284 8862498 (wideData 16 0x2ae1e0dd63002a30f84100104005eac84f9e4e000a8c3e0000000001a3f0d8b8001928b80000000006aec334d00064a300000000001adb0ae68001928b80000000007ca03f0900064a300000000001e9d0aff0001928b80000000008d28423980064a3000000000022fc0ba6a001928b800000000099a82e9f00064a30000000000177b11af0001928b80000000002abd2fbd00064a300000000001ecc52d72001928b80000000003f25338800064a300000000001acb4fb34001928b82f02f04982f02f04999eae9059679a0210a758a6) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P05 : WideCovered band 8862499 9456658 := wide_block_sound band profiles_RelativeWidePack6815_P05 8862499 9456658 (wideData 16 0x2e7106dff0002a30f8208008200bc3106cc72002a30f8000000000dd64060c3a002a30f8000000000db285b5b800a8c3e000000000428f1eae4002a30f80000000012df4060ae4002a30f80000000015d68060ee6002a30f80000000019db4061d62002a30f80000000004935062fae002a30f80000000003c603e89800a8c3e0000000003f3b419349000a8c3e0820020803a3915d60002a30f80000000017aec43ed800a8c3e00000000073bb0ea2a002a30f80000000001967f0aa7c002a30f83803804983803804999a2fb05e3cc60210fe68e2) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P05 : WideCovered band 9456659 10050817 := wide_block_sound band profiles_RelativeWidePack6815_P05 9456659 10050817 (wideData 16 0x10a7407dbbc002a30f8000000000ceb807ec20002a30f8208008200a861072c34002a30f8000000000d864071820002a30f8000000000dce4071bfe002a30f8000000000ea680729a2002a30f8000000000f8f80738fc002a30f8000000000fca4070e76002a30f8000000000fff006d97c002a30f8000000000fa35077ae0002a30f0208008200992806ab2c002a30f8000000000daa8069876002a30f8000000000e9fc069cfc002a30f8000000000ea64063c78002a30f8000000000ffe0066826002a30f8390390498390390499fc6fe069f1cea2128eeca2) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P05 : WideCovered band 10050818 10756382 := wide_block_sound band profiles_RelativeWidePack6815_P05 10050818 10756382 (wideData 16 0xa1f340be820004c61f00000000002871a02ea984013187c1860061801e1c600b6ef2c0013187c0000000004e5d02d6af000a8c3e0820020800aec42cf49000a8c3e0000000003ecf0296cc800a8c3e00000000037ee01ee79800a8c3e0000000004238029a1f000a8c3e000000000432b029b9f000a8c3e000000000464d029f9e000a8c3e00000000047b802a63e800a8c3e0820020801f0942968c800a8c3e00000000032af01c34f800a8c3e0000000003ace01eb7b000a8c3e0000000003bdb01eecd800a8c3e0e80e81260e80e8126064feda078209302139f7860) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P05 : WideCovered band 10756383 11944701 := wide_block_sound band profiles_RelativeWidePack6815_P05 10756383 11944701 (wideData 16 0x1228a4562b38004c61f00000000003c26f17a7fa8013187c0820020800e7af847b9a6004c61f00000000003830e0efe598013187c0000000000ecae043992a004c61f02080082001e68c0f9fcd8013187c0000000000abb742e2ce4004c61f00000000002cf090c8f5d8013187c0000000000adce02aac78004c61f00000000002b23d0ae6298013187c0820020804e4f09a2dd0013187c0000000000798b81a5a68004c61f000000000029ba907c2b88013187c0000000000b1a241f0cfe004c61f00000000002c68903ee1b8013187a0f40f41260f40f4126073972d0adb8b20214d61cf8) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P05 : WideCovered band 11944702 12093240 := wide_block_sound band profiles_RelativeWidePack6815_P05 11944702 12093240 (wideData 2 0x20800820049fbe1d878e8013187a0fa0fa1260fa0fa1260beb2f911b23f30216f72c76) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7339965 8026962 12093240 c0_RelativeWidePack6815_P05 (wide_covered_join band 8026963 8231204 12093240 c1_RelativeWidePack6815_P05 (wide_covered_join band 8231205 8528283 12093240 c2_RelativeWidePack6815_P05 (wide_covered_join band 8528284 8862498 12093240 c3_RelativeWidePack6815_P05 (wide_covered_join band 8862499 9456658 12093240 c4_RelativeWidePack6815_P05 (wide_covered_join band 9456659 10050817 12093240 c5_RelativeWidePack6815_P05 (wide_covered_join band 10050818 10756382 12093240 c6_RelativeWidePack6815_P05 (wide_covered_join band 10756383 11944701 12093240 c7_RelativeWidePack6815_P05 c8_RelativeWidePack6815_P05))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 11)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 11≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤56)
    (hT0 : 3750≤T) (hT1 : T≤4084) (hnu : 7339965≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤30760068026545820 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R031

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R032
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨11,57,3750,4055,31518451869895687⟩
private def profiles_RelativeWidePack6815_P05 : ℕ → Profile
  | 0 => ⟨16536,4,5080⟩
  | 1 => ⟨33072,8,10160⟩
  | 2 => ⟨2984,24,635⟩
  | 3 => ⟨42768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P05 : WideCovered band 7471036 8052704 := wide_block_sound band profiles_RelativeWidePack6815_P05 7471036 8052704 (wideData 16 0x4d2c0a7e804aab02080000008d73b2107ac7b93f092aac0000000000768acc0b8f9c20001934d800000000028efb683a6beed00064d38000000000464bb40e9e2ce80064d3600000000026df20072bbfb00064d380000000007619a81a0e39b00064d360000000000a5b741628f5001934e0000000001297fe03c689ae001934d80000000004b27b4293f87f001934e0000000000ceb7a01e7ffa2001934d80000000015b2a948e66ee7001934e00000000017b75d4ebb7ff5001934d830c00c300497ecf806fa39ae4081934e00000000003e70070cec082a69b82e02e04a02e02e04a05a3c07883a00eeaa9e6) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P05 : WideCovered band 8052705 8240339 := wide_block_sound band profiles_RelativeWidePack6815_P05 8052705 8240339 (wideData 16 0x13ff47e3001934e000000c0001ee6f1bbfb001934d80000000001f23a15d2d001934e02080080006f28b46dfcc80064d360000000001fca03ebc012aac000000000230d03e7c012aac000000000267e03e2a012aaa000000080227903db8012aac00000000017af14cc04aab000000000029e80ecf804aab00000000002b740e9d804aaa80000080002d380e6a804aab00000000002f640e2a004aab000000000039b80bde804aab00000000003ce40b7e004aaa82e02e04a02d82d84a128a8c04ebcee618fb22a2c) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P05 : WideCovered band 8240340 8540555 := wide_block_sound band profiles_RelativeWidePack6815_P05 8240340 8540555 (wideData 16 0x6c713f8b80064d38000000000228850e38001934d8208008201c84da6e001934e000000000078ac120c00064d3600000000022fe08f2c001934e00000000009ae4238e80064d360000000002abd08d6e001934e0000000000b9bc173e80064d36000000000332f04a6a001934e0000000000efe01f6b00064d3600000000046bf07b66001934e00000000014be41e0e00064d360000000005edf03b69001934e0000000200f8f8138f00064d360000020002e3f03cb8001934e02e82e84a02e02e04a11e33f05865c7418fe2387c) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P05 : WideCovered band 8540556 8840770 := wide_block_sound band profiles_RelativeWidePack6815_P05 8540556 8840770 (wideData 16 0x3a71328c00064d380000000001f4e52ca0001934d82080082004ae9463c80064d38000000000173a0cae2001934d80000000005e2c2ecd00064d38000000000178d098f6001934d80000000006d68331d00064d380000000001e490cda4001934d80000000007d6c33c880064d380000000001f1d07eb8001934d80000000008fe833ff00064d3600000000027bd0db3a001934d8000000000af28378d00064d380000000000e290e9aa001934d80000000014c07cec001934e02f02f04a02f02f04a16969905965d7a190aadb6c) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P05 : WideCovered band 8840771 9422437 := wide_block_sound band profiles_RelativeWidePack6815_P05 8840771 9422437 (wideData 16 0x7f6406de24002a69b8000000000a96d7f7d000a9a6e0820020800aed419ec8000a9a6e00000000036bc13836002a69b800000000118ac7b5f000a9a6c0000000004f9b1ef30002a69b80000000015a683b68800a9a6e000000000737f1dff0002a69b800000000018a2808d36002a69b8000000000df2c6f5e000a9a6e000000000665a01d26002a69b80000000013de02ee9000a9a6e000000000731c08ffc002a69b8000008200aba1b05a2edc00a9a6e104002080379b29524ba6002a69b82f82f84a02f82f84a188e8905af3f2c190f37e3a) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P05 : WideCovered band 9422438 10022868 := wide_block_sound band profiles_RelativeWidePack6815_P05 9422438 10022868 (wideData 16 0x375b01c76c000a9a6e000000000429f01faae000a9a6e082002080368d41fb59800a9a6e0000000002b9c019e0b000a9a6e00000000033bb01c64f000a9a6c0000000002ffd019e6d000a9a6e0000000003af801cb69000a9a6e0000000003b9b01bb6c000a9a6e0000000003feb01bb8b000a9a6e00000000032fc41dfaf800a9a6e0820020800e4b018a4d000a9a6e00000000033be01a32f800a9a6e000000000327e1df7a002a69b8000000000f934069ce4002a69b80000000010e7c06aeba002a69b83903904a03903904a1c879e0693aeee19286cbf8) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P05 : WideCovered band 10022869 10698354 := wide_block_sound band profiles_RelativeWidePack6815_P05 10022869 10698354 (wideData 16 0xac74c0ae6cec0132cbc2080082002239650edfb4e80132cbc0000000003e7d029e2a000a9a6e000000000472a02cfd9000a9a6e0820020800e4c42ceff000a9a6e000000000335901ee1c800a9a6e0000000003acd0292fc000a9a6e000000000365b01eadb800a9a6e0000000003e9b0297c8000a9a6e0000000003a4e01ef1a800a9a6e000000000433802a2ac800a9a6e0820020801fc8429e4f000a9a6e0000000002ee801bfe8800a9a6e00000000036cb01ea5b000a9a6e00000000032ab01c2bf000a9a6e0e80e81280e80e8128061875806f29e6e1939a19b6) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P05 : WideCovered band 10698355 11899216 := wide_block_sound band profiles_RelativeWidePack6815_P05 10698355 11899216 (wideData 16 0xf08a04f1ba8004cb2f00000000003bb4b12ee5c80132cbc082002080073eb83f2aa0004cb2f00000000002fa5c0ffb3c00132cba0000000000b49b036d9a0004cb2f00000000002aede0d920880132cbc082002080777f0a9bfd00132cbc0000000000a0d3c267a3a004cb2f000000000028e7c08ea0a80132cbc0000000000b5ea02ead34004cb2f0208008200692d1f5d3a004cb2f00000000001d3ab05a6f880132cba000000000079f3c12d866004cb2f000000000028f8c038f2d00132cbc0000000000b8a2c72d980132cbc0f40f41280f40f412806ccf4e0ae27ef6194c71ea0) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P05 : WideCovered band 11899217 12274485 := wide_block_sound band profiles_RelativeWidePack6815_P05 11899217 12274485 (wideData 5 0x16cde406083a980132cba000000000175b6c061d33800132cbc00000000013ad24721ab6004cb2f02080082002fa3d17a7dc00132cbc0fa0fa1280fa0fa1280b0ce7e10aa4f2e196ebb9fc) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7471036 8052704 12274485 c0_RelativeWidePack6815_P05 (wide_covered_join band 8052705 8240339 12274485 c1_RelativeWidePack6815_P05 (wide_covered_join band 8240340 8540555 12274485 c2_RelativeWidePack6815_P05 (wide_covered_join band 8540556 8840770 12274485 c3_RelativeWidePack6815_P05 (wide_covered_join band 8840771 9422437 12274485 c4_RelativeWidePack6815_P05 (wide_covered_join band 9422438 10022868 12274485 c5_RelativeWidePack6815_P05 (wide_covered_join band 10022869 10698354 12274485 c6_RelativeWidePack6815_P05 (wide_covered_join band 10698355 11899216 12274485 c7_RelativeWidePack6815_P05 c8_RelativeWidePack6815_P05))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 11)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 11≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤57)
    (hT0 : 3750≤T) (hT1 : T≤4055) (hnu : 7471036≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤31518451869895687 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R032

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R033
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨11,58,3725,3749,44481302807416666⟩
private def profiles_RelativeWidePack6815_P05 : ℕ → Profile
  | 0 => ⟨33072,8,10160⟩
  | 1 => ⟨9612,81,2493⟩
  | 2 => ⟨43018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P05 : WideCovered band 7602107 8052630 := wide_block_sound band profiles_RelativeWidePack6815_P05 7602107 8052630 (wideData 16 0x11cf80669e8c000a7d680000000006e4d01faff3c0029f5a8208008200ae74075e689000a7d6800000000012b907878d800a7d6a000000000266812efeb800a7d680000000001eef0da31b800a7d6a0000000000e2d518a2f400a7d6a0c36430d9178f383f58a3b020a7d6a000000000000002000000000000014000000000000002a80000000000000134000000000000009a000000000000004b2000000000140009a280b60b612a0b60b612a7340e897800ee688ec) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P05 : WideCovered band 8052631 8474594 := wide_block_sound band profiles_RelativeWidePack6815_P05 8052631 8474594 (wideData 16 0x2c202e2a80063eb40000000000e4d0bc700018fad00000082004cb9329900063eb608200000022ce49d2a0018fad0000000001d904bf00018fad0000000000183c0fa800063eb4000000000065f038260018fad80000000001b2007fa00063eb410460411866cd6d07ef34bb10818fad00000000006f28e1197682e0029f5a80000000003931d07e3faf20029f5a00000000003877e07ce0ee00029f5a8000000000296cf05afbce80029f5a000000000018f4f02d7b8ac0029f5a80000000001af8d03abef220029f5a02d82d83c82d82d83c899b7b17fb1a2008fb77bb6) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P05 : WideCovered band 8474595 8768134 := wide_block_sound band profiles_RelativeWidePack6815_P05 8474595 8768134 (wideData 16 0x2c2542da80063eb408200208006f84afe80018fad0000000000fc0a8220018fad80000000010d09fe80018fad00000000011f09fb60018fad00000000013909fa80018fad00000000014f09fb20018fad80000000016e09fbc0018fad00000000019809fee0018fad0000000001be0a8240018fad0000000001f80a87c0018fad800000000018e02a3a00063eb4000000000068a0a9a20018fad00000000001bac2a9d00063eb4000000000076d0abf40018fad82f02f04a82f02f04a81c34f058ad8f61109abe38) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P05 : WideCovered band 8768135 9226790 := wide_block_sound band profiles_RelativeWidePack6815_P05 8768135 9226790 (wideData 16 0x6f914a3a0029f5a00000000001e284b7b000a7d6a0000000000a5c10c340029f5a00000000002e7436db000a7d6a0000000000f9e08c380029f5a00000000005ce816c0029f5a80000000009a2443cdc00a7d680000000004b7b01f28c400a7d6a104004100068e31464b3a0029f5a0000000001280dbf60018fad00000000013b0ddea0018fad8000000001580dffe0018fad00000000016d0ea7c0018fad00000000018c0eda00018fad0000000001b80f9660018fad82f82f84a82f82f84a81e68b059fb966110e298e0) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P05 : WideCovered band 9226791 9813870 := wide_block_sound band profiles_RelativeWidePack6815_P05 9226791 9813870 (wideData 16 0x7f8069aa80029f5a000000000018a4069fb20029f5a8000000000193c06ae6a0029f5a00000000001a3406bfa60029f5a80000000001b6406dbe80029f5a02080082002ab106ade80029f5a8000000001e8018339800a7d68000000000060d01834f000a7d6a000000000064801839c800a7d68000000000068801864b000a7d6a00000000006db01873e000a7d68000000000074d018ac8800a7d6a00000000007ec018f19800a7d680000000000acb0196cb800a7d6a08200208016fa5aaec0029f5a03883884a83883884a828f0805f2af76111d6cdf6) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P05 : WideCovered band 9813871 10400950 := wide_block_sound band profiles_RelativeWidePack6815_P05 9813871 10400950 (wideData 16 0x60a01eabd800a7d68000000000061901eb7e000a7d6a000000000062901ee8e000a7d68000000000063d01f21a000a7d6a000000000065801f3fc800a7d68000000000067801fa8f800a7d6a08200208073107c9380029f5a0000000001df01c60a000a7d6a0000000007e0071aea0029f5a00000000001830071f740029f5a800000000018a0072d700029f5a00000000001928073da60029f5a800000000019b8074fbc0029f5a00000000003e41db6e800a7d6a0820020802650699e00029f5a03983984a83983984a82ba8a06be0c3c112e67b26) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P05 : WideCovered band 10400951 11428340 := wide_block_sound band profiles_RelativeWidePack6815_P05 10400951 11428340 (wideData 16 0x136f08efb88012fab200000000013ba08ca8d0012fab2000000000164a08abde8012fab20000000001749089b3c8012fab20820020807751bcf2c004beac800000000048ec164fe8004beac80000000004ce0130dae004beac80000000005c200f4c24004beac80000000007aa40a5d26004beac8000000000bd28726a4012fab200000000067aa0bda0ac012fab220800820062ee4386aa24004beac8000000000196c0a4ea40029f5a000000000019b80a5eb20029f5a80000000001a280a78240029f5a03b03b04a83b03b04a82e6b807ab99f0113f62836) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P05 : WideCovered band 11428341 12455730 := wide_block_sound band profiles_RelativeWidePack6815_P05 11428341 12455730 (wideData 14 0x10cb4067a2de0012fab20000000003efc0192ca32004beac8208008200a9b47a1962004beac8000000000bb306abefc004beac8000000000af3863e9b8004beac8000000000ac745faaa8004beac82080082005c204b0fe6004beac800000000088244769b8004beac80000000007f304638a0004beac82080082004c7c424a7c004beac80000000006878338e34004beac8000000000687432bffc004beac8000000000693c323c68004beac83e03e04a83e03e04a84d6ae0caa6fac115fa0a7a) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7602107 8052630 12455730 c0_RelativeWidePack6815_P05 (wide_covered_join band 8052631 8474594 12455730 c1_RelativeWidePack6815_P05 (wide_covered_join band 8474595 8768134 12455730 c2_RelativeWidePack6815_P05 (wide_covered_join band 8768135 9226790 12455730 c3_RelativeWidePack6815_P05 (wide_covered_join band 9226791 9813870 12455730 c4_RelativeWidePack6815_P05 (wide_covered_join band 9813871 10400950 12455730 c5_RelativeWidePack6815_P05 (wide_covered_join band 10400951 11428340 12455730 c6_RelativeWidePack6815_P05 c7_RelativeWidePack6815_P05)))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 11)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 11≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤58)
    (hT0 : 3725≤T) (hT1 : T≤3749) (hnu : 7602107≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤44481302807416666 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R033

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R034
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨11,58,3750,4025,31563107902589997⟩
private def profiles_RelativeWidePack6815_P05 : ℕ → Profile
  | 0 => ⟨8268,2,2540⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨2984,24,635⟩
  | 4 => ⟨43018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P05 : WideCovered band 7602107 8038175 := wide_block_sound band profiles_RelativeWidePack6815_P05 7602107 8038175 (wideData 16 0x158381f4ac04b0c02080080007bb3df507796eeb3092c300000000000aee68d12ba9b2e001960f8000000000eeaae038edde20019618000000000018e1e2c224c76b8006583e000000000134af04e897e001961800000000014a6dc04ca1bfa001960f8000000001ab790609e3d40065860000000000370aac0b5a60c0006583e000000000274b39129ba69c006586000000000023c8a01b696a001960f80000000002a72cad061822d6f001961800000000004fa8a6c07cc2efa0081960f830c00c3003b34070cea081961802080104001da8629d820aa87e0b60b612a0b40b412a0e3f1fde400ee688ec) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P05 : WideCovered band 8038176 8189850 := wide_block_sound band profiles_RelativeWidePack6815_P05 8038176 8189850 (wideData 16 0x5ea00a5f804b0b800000000069ec0a0f804b0c00000000006db407b8804b0b800000000079f4074e004b0c00000000007ee806dc004b0c00000000008c70065c004b0c00000000009ae86ee012c2e0000000002a9e15e004b0c0000000000bee0132c804b0c0000000000cd780ad012c300000000003a6e13ac04b0b8000000001087c067ac04b0c00000000012a7807fd404b0c00000002012dfc0becc04b0c0000000000eb301258c04b0b82e02e04a82e02d84a8d865d04ef592820fae68ae) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P05 : WideCovered band 8189851 8436323 := wide_block_sound band profiles_RelativeWidePack6815_P05 8189851 8436323 (wideData 16 0x2a212a098006583e0000000000e2f4aa7c00196180208008200adf80e6f8006583e00000000032bd029a400196180000000000efa81afb0006583e000000000466802df0001961800000000014a240768c006583e00000000063a9049a900196180000000001fa2c1f89c006583e0000020800f6bad167dfe001961800000000003b791b0f804b0b8208000000293c13bc004b0c00000000004df812ce804b0c00000000004e740b38804b0c000000000058e80afa004b0b82e02e04a82e02e04a92bbcd04efcf3820fd2eaa4) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P05 : WideCovered band 8436324 8739675 := wide_block_sound band profiles_RelativeWidePack6815_P05 8436324 8739675 (wideData 16 0x5be4271c8006583e00000000017b909be2001961800000000006f6c3aad8006583e0000000001b9f09c20001961800000000007b3026d98006583e000000000222e09aaa001961800000000008f60265d0006583e00000000027cf098ae00196180000000000bf783fbe0006583e000000000334b09a6400196180000000000ac20265f0006583e0000000001f02639000658600000000002b423d90006583e0000000003782388000658600000000002f4f54a7e001960f82f02f04a82f02f04a938a7d058b8dfa2109229e6) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P05 : WideCovered band 8739676 9118864 := wide_block_sound band profiles_RelativeWidePack6815_P05 8739676 9118864 (wideData 16 0x1fd245ea002aa1f80000000001b63c038a2002aa1f800000000028f8c08e79002aa1f841001040059f484f8f2b800aa87e000000000167c0ccfa001960f80000000005d28370b000658600000000001abf10da6001960f80000000006a34362f800658600000000001b6c0d9ee001960f800000000079b836ce000658600000000001f9e0dcf8001960f80000000008c2037ce80065860000000000165b54bb4001960f80000000005db93bfb8006583e0000000001b6a4fc36001960f82f82f84a82f82f84a95c73c05a28b34210db2db6) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P05 : WideCovered band 9118865 9725567 := wide_block_sound band profiles_RelativeWidePack6815_P05 9118865 9725567 (wideData 16 0xdc30067db8002aa1f8000000000efa8068a78002aa1f80000000003d6d077f7e002aa1f82080082007b3d066afe002aa1f8000000000b82873ed800aa87e000000000374801a2db800aa87e00000000036fd1cd76002aa1f8000000000fa247239800aa87e0000000004f2b01abf9000aa87c000000000562f1cbe6002aa1f80000000002ab8721d800aa87e0000000006b4d41ca0c000aa87e0820020801f7b13b6c002aa1f800000000109a83769000aa87e000000000561d17d20002aa1f83883884a83883884a96debe05f32e6a211bbcabe) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P05 : WideCovered band 9725568 10332270 := wide_block_sound band profiles_RelativeWidePack6815_P05 9725568 10332270 (wideData 16 0xdc2c0a48fa002aa1f8000000000cc3407a8f0002aa1f8000000000d8ac07adf6002aa1f8000000000fb640a7fae002aa1f80000000009ab907dca0002aa1f82080082009f7c06fa72002aa1f8000000000caf4079c6e002aa1f8000000000bbfc06fe70002aa1f8000000000c8f40709b4002aa1f0000000000ebfc07cea6002aa1f8000000000df64072b64002aa1f80000000008e21073dfe002aa1f82080082004ea4073be2002aa1f8000000000ade8066ba0002aa1f8000000000bb7c066bbc002aa1f83983984a83983984a9ba6bc06ba082c212cfda7c) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P05 : WideCovered band 10332271 11166487 := wide_block_sound band profiles_RelativeWidePack6815_P05 10332271 11166487 (wideData 16 0x29a5d07d699001348fc0000000000b4d601e8cf2004d23f00000000001ef7a028658001348fc082002080079d65129af4004d23f00000000002a28e0b004d23f06180186006836f02f2acac004d23f0000000000dde80bdf6c002aa1f82080082002c42b7dd000aa87e000000000339c0292ed800aa87c000000000375902a3cf000aa87e0000000003acd02b25a000aa87e00000000037bb0297be800aa87e0000000003aef029f29000aa87e0000000005e90b3cbe002aa1f82080082008b6c07aaf0002aa1f83a83a84a83a83a84a9ffb7907a63d6a213e3ea3a) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P05 : WideCovered band 11166488 12379893 := wide_block_sound band profiles_RelativeWidePack6815_P05 11166488 12379893 (wideData 16 0x17fa74067c39b001348fc0820020800fba6c7f6de0004d23f00000000004b37b1cd60b001348fc0000000000fbb2c632828004d23f00000000003f6da18de1e001348fc0820020800acdf457db34004d23f00000000002d6ad109279801348fc0000000000e0d244a98f2004d23e80000000003860f11ee1d801348fc0820020806ffd0bffaa001348fc0000000000a9d743618e6004d23f00000000002aeb90cde9d001348fc0000000000a2eac276af6004d23f0208008200ec202bddf6004d23f00000000001ee5a08d7ea001348fc0f60f612a0f60f612a071cbcc0bd698b4215ba5d68) (by decide +kernel)
private theorem c9_RelativeWidePack6815_P05 : WideCovered band 12379894 12455730 := wide_block_sound band profiles_RelativeWidePack6815_P05 12379894 12455730 (wideData 1 0xfe0fe12a0fe0fe12a0e38fde168bfeb6217e27ce4) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7602107 8038175 12455730 c0_RelativeWidePack6815_P05 (wide_covered_join band 8038176 8189850 12455730 c1_RelativeWidePack6815_P05 (wide_covered_join band 8189851 8436323 12455730 c2_RelativeWidePack6815_P05 (wide_covered_join band 8436324 8739675 12455730 c3_RelativeWidePack6815_P05 (wide_covered_join band 8739676 9118864 12455730 c4_RelativeWidePack6815_P05 (wide_covered_join band 9118865 9725567 12455730 c5_RelativeWidePack6815_P05 (wide_covered_join band 9725568 10332270 12455730 c6_RelativeWidePack6815_P05 (wide_covered_join band 10332271 11166487 12455730 c7_RelativeWidePack6815_P05 (wide_covered_join band 11166488 12379893 12455730 c8_RelativeWidePack6815_P05 c9_RelativeWidePack6815_P05)))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 11)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 11≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤58)
    (hT0 : 3750≤T) (hT1 : T≤4025) (hnu : 7602107≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤31563107902589997 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R034

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R035
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨11,59,3381,3995,31335780865062296⟩
private def profiles_RelativeWidePack6815_P05 : ℕ → Profile
  | 0 => ⟨9699,83,2468⟩
  | 1 => ⟨2984,24,635⟩
  | 2 => ⟨24769,195,5079⟩
  | 3 => ⟨9279,74,2353⟩
  | 4 => ⟨43018,250,10158⟩
  | 5 => ⟨26108,143,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P05 : WideCovered band 7733178 8088752 := wide_block_sound band profiles_RelativeWidePack6815_P05 7733178 8088752 (wideData 16 0x10468411a0fc872a41aa3b23102abc00000000006bfabf03f37bf4012db4000000000066a69b03b34836012db200000000062ae2d0ab8b1ac04b6d00000000001fb1ae4171a64900065b68000000000072933a04b7caf000196d9830db0c36c2a7d9f80f19f4883065b68000000000061f66e02f29af400196d980000000002ab28a01e18f9f00065b68000000000265a2c329eb200196d98209a08268a8208ed6b2e64f42065b68000000000076ae0b04c338e8002abab80000000002de3ba01f2ea6f000aaeae0000000001a1d28178f2d002abab8000000001d97c943ff1dbd002abab82d02d03c82d02d03c8eb60eec06ddaaf3000eeaada0) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P05 : WideCovered band 8088753 8131343 := wide_block_sound band profiles_RelativeWidePack6815_P05 8088753 8131343 (wideData 16 0x30d10c344df26e35070f3ca7b082969b00000000001a01d00080000000003d04e80180000000002f740f7d8013600000000017b907bf8009b0000000000aabc3e4bc04b60000000001b8f17afc012d8000000000d8f47faa404b80000000004fca10ee200196c0000000004fa810a3800196e0000000004f7e0fdaa00196e0000000002e7a028fe940065b80000000001b39d01becf800aae800000000169785afb000aae80000000013c60338c00065b02e02e04b02e02e04b0fc6ee3c076b30b7e10fb77c2e) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P05 : WideCovered band 8131344 8982802 := wide_block_sound band profiles_RelativeWidePack6815_P05 8131344 8982802 (wideData 16 0xa3835b05f6cf26002969b00000000001beaae4125cbac000a5a6a000000000063a79b038f0c60002969b02080082018c6df02b31ffa002969a830c00c3006d25d654f7ee7b400a5a6c0000000000f0e7d809fe4e72004ab2d8000000000287cbb8177a7988012acb6000000000069fbcb03e2cea8004ab2d0208008200deecb01d25af2004ab2d8000000000dc29c1ec7cf8012acb60000000004f6eb806dd79c8012acb60000000000fadb043e863004ab2d84100104001ee78201e7abb80012acb60000000000a2ab4160c60002969a8000000000282de04de3c800a5a6c0b60b60fc0b60b60fc07daf1f05d75f7018fcaeea8) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P05 : WideCovered band 8982803 9550441 := wide_block_sound band profiles_RelativeWidePack6815_P05 8982803 9550441 (wideData 16 0x17ee44edb000a5a6c00000000076ee1cd3e002969a80000000001839b1ceac002969b00000000001869d10fe0002969a8000000001cef07309000a5a6c000000000225c1cfae002969a80000000012870369f000a5a6c00000000026be1ce34002969a80000000008be87a2d800a5a6c0020000007b3c05ef8002969a8200008200f970727f800a5a6a000000000075a642eab800a5a6a00000000007e9602a69400a5a6c0000000000a9d3c6af002969a8619018640d832d75063df7ba1082969b02f02f03f02f02f03f0eb62a700698e2f7a1919adeae) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P05 : WideCovered band 9550442 10118079 := wide_block_sound band profiles_RelativeWidePack6815_P05 9550442 10118079 (wideData 16 0x639e01b30c800a5a6c0000000005bcd01923e000a5a6a0000000006e1f01b69b000a5a6a000000000732b01ba1f800a5a6a0000000006e2e0193f8800a5a6c000000000165e01bfde800a5a6a0000000000ebf41c72e800a5a6c0820020802f790183cd800a5a6a00000000063d80193ad800a5a6c0000000006b0c01968b800a5a6a00000000066881bffc002969a8000000001edf4066922002969a80000000014cb406793a002969b00000000004d78730e800a5a6a000000000071f41a6ef000a5a6c0e60e612c0e60e612c079fbab05d34f60212a62bfc) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P05 : WideCovered band 10118080 10863105 := wide_block_sound band profiles_RelativeWidePack6815_P05 10118080 10863105 (wideData 16 0x283db02d3df8012acb6000000000261944efed0012acb600000000013192c6759c012acb60000000005b2fb83229e1004ab2d8820020800d8fd942c2b9fe004ab2d8000000001cbe4076efc002969a800000000189b00a1ce4002969b000000000038750a2ee8002969a82080082013bf006e9ac002969b0000000001ad68075872002969a8000000001bc3c075c62002969a80000000019b3c06ceb0002969a8000000001ddac076e26002969b0000000001996c077e78002969a8000000000dc41bb5e000a5a6c0ea0ea12c0ea0ea12c0a2dbdc06a379fc213af7968) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P05 : WideCovered band 10863106 11998383 := wide_block_sound band profiles_RelativeWidePack6815_P05 10863106 11998383 (wideData 16 0x1a18b43e683e004ab2d80000000005f3ed0ecb3f0012acb6000000000170e2842ad72004ab2d82080082003bf0c0bc3ae0012acb60000000001309ac2b2ba8004ab2d80000000005965e0c96288012acb60000000000fedf42a3a2e004ab2d82080082001dfff08c3fc8012acb4000000000123a6c2618f0004ab2d80000000003d6dd07974c0012acb60000000000fbff41bef38004ab2d82080082012a74231de4004ab2d80000000002f6cf04e6fa8012acb60000000000e3c6c12c83c004ab2d800000000048e6805f7ac0012acb60f40f412c0f40f412c0bcfa3e09a26c76214eebcb6) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P05 : WideCovered band 11998384 12636975 := wide_block_sound band profiles_RelativeWidePack6815_P05 11998384 12636975 (wideData 9 0x30c00c300065b7ba44aa0bf6084ab2d0000000000dd2780193bd6a004ab2d8000000000deef80196fdae004ab2d8000000000bdadc1f9abe8012acb60820020801fff786bdd20004ab2d00000000009ce2c19be480012acb6000000000227af056cda4004ab2d80000000007f7c814aeba8012acb60fc0fc12c0fc0fc12c13cf66b0eb6ea68217834f72) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7733178 8088752 12636975 c0_RelativeWidePack6815_P05 (wide_covered_join band 8088753 8131343 12636975 c1_RelativeWidePack6815_P05 (wide_covered_join band 8131344 8982802 12636975 c2_RelativeWidePack6815_P05 (wide_covered_join band 8982803 9550441 12636975 c3_RelativeWidePack6815_P05 (wide_covered_join band 9550442 10118079 12636975 c4_RelativeWidePack6815_P05 (wide_covered_join band 10118080 10863105 12636975 c5_RelativeWidePack6815_P05 (wide_covered_join band 10863106 11998383 12636975 c6_RelativeWidePack6815_P05 c7_RelativeWidePack6815_P05)))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 11)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 11≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤59)
    (hT0 : 3381≤T) (hT1 : T≤3995) (hnu : 7733178≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤31335780865062296 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R035
end MergedPart1
section MergedPart2
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R036
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨11,60,3328,3964,34167255524904513⟩
private def profiles_RelativeWidePack6815_P06 : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨24769,195,5079⟩
  | 2 => ⟨24832,192,5079⟩
  | 3 => ⟨24889,189,5079⟩
  | 4 => ⟨43268,250,10158⟩
  | 5 => ⟨24986,187,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P06 : WideCovered band 7864249 8040831 := wide_block_sound band profiles_RelativeWidePack6815_P06 7864249 8040831 (wideData 16 0x1aefe03a62f400abc80000000001ab6d03caeec00abd000000000018f9b04d23d400abc800000000018f3d04f22dc00abd00000000001872f4dc21ac00abc82082082084960d7d075c208820abd00000000001c77a2012eaf8a0026eb000000000018e3dbd121d3bd404bce00000000005e3e8a0439afca80065e6e0000000000bf963e08c7c9aa001979c00000000011c75b0197b964001979b80000000001d72bfc136e2ed80065e70000000000069afc464b2d001979b800000000018a58e00b7afcb80065e7000000000043aeb10bf963940065e6e0b60b612c0b60b612c1bea38918e6de2c00f865d60) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P06 : WideCovered band 8040832 8086791 := wide_block_sound band profiles_RelativeWidePack6815_P06 8040832 8086791 (wideData 16 0x2969d09baebc026eb000000000159baa01ff6a70009bac0000000000ecca80b8cb0004de6000000000365dbd0a0d70cc0137980000000013df4801eb6a3c009bac000000000237d4bae59c0137980000000003a72919b20004de60000000000e98682f0e0013798000000000dc2136aa71004de60000000000e7e385b8ec0137900000000015ae93ed8e3004de60000000000e9c20073bef004de60000000000e6a600b1975004de6000000000638a51fa19c013798000000000393ec048e2dc0137982e02e04b82e02e04b8f8adc74078db7aea08fabdbe4) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P06 : WideCovered band 8086792 8130332 := wide_block_sound band profiles_RelativeWidePack6815_P06 8086792 8130332 (wideData 16 0x3f6fc07eb4a80137980000000018aac0a99f1004de60000000000fcea41f3966004de60000000000f6cac1bce3e004de6000000000667a02c67a40137980000000003e7bf07862b80137980000000011ea80f1be5004de60000000000f88fc1b4c20004de60000000000f49781a4bb8004de6000000000475f03ffafc0137980000000003d6fa06830b0013798000000000ca2813cbf9004de60000000000f3f241728f6004de60000000002b5ee5070dfba40137980000000002eb4c058fa8c026ea82e02e04b82e02e04b90df587007883eea608fb7bfba) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P06 : WideCovered band 8130333 8173872 := wide_block_sound band profiles_RelativeWidePack6815_P06 8130333 8173872 (wideData 16 0x46bdb806ef24ec026ea800000000159b0a01f78e7b009bac0000000006bda3c0b2fe1cc026eb00000000001829a640ef978a8026eb00000000013e6e91c9b8d40137980000000014ca9a01ffea6b004de60000000006b09bc06b8a6ac01379800000000108668039ebd8013798000000000fface1cb74cc00abc80000000011ba1a01839ba7002af40820020804388edd5bbf1e420abc8000000000dce116d8bf002af40000000007f0c018e6ac01379800000000048a3c08bfef80137980000000003e71a07ce0f00137902e02e04b82e02e04b91c7bff4077ba9a2408fc2ca3e) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P06 : WideCovered band 8173873 8309333 := wide_block_sound band profiles_RelativeWidePack6815_P06 8173873 8309333 (wideData 16 0x1fa82c17ed20012f38000000000460ef4062bbf8804bce00000000007bf3d1ff2c012f360000000001e7ca40b99ef012f380000000001bff2c1eb8e1012f380000000001b7828364e2d012f380000000001aac7053ee69012f360000000004bdd304a8eac012f380000000001e6fe8064a34a404bce00000000007a7ba01d32ba3012f380000000001ebfb00adf2dc404bcd80000000002c7f86427683fa004bce00000000009ca1e14ef8cc026eb0000000000dfe2f09aff94026eb0000000000fbb1b0df7584026eb02e82e84b82e82e84b889bd8ac06d9b09f010fce686c) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P06 : WideCovered band 8309334 8464144 := wide_block_sound band profiles_RelativeWidePack6815_P06 8309334 8464144 (wideData 16 0x320c0186a012f360000000004a3904cf1012f380000000003bbb079404bcd80000000016cec1baac04bce000000000138a40a4bc04bce00000003007d69c697b6d21cc24bce0000000000edabd03d66e004bcd80000000010db7d1892e012f380000000004f2ab00e3c31012f380000000005f9c6822ec6b012f38000000000632824075cb8ec04bcd800000000019f8e2c0758b1f404bce00000000001fbab300a8969fc04bce00000000001da1c7e12cca88c04bce0208008200ec32de30f197ea424bcd82e82e84b82e82e84b8fb2eb64071877bb810fef88a2) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P06 : WideCovered band 8464145 8677010 := wide_block_sound band profiles_RelativeWidePack6815_P06 8464145 8677010 (wideData 16 0x6a4e01b2d001979b8000000201fce4120a40065e70000000000067ae41f8dc0065e6e0000000c0325fb5f41c389a2d43065e700000000006f4db80ab8b3c40065e6e0820021002e6be2e01ce98f4902065e700000000001f9911e804bcd800000000069280efd004bce00000000008e240a4012f380000000001bcb039aa012f3800000000027eb119404bcd80000000008dac0778804bce0000000000ad381bf012f38000000000333901f63012f3800000000027ff01f6a012f360bc0bc12e0bc0ba12e069decf04cbc87c210966b78) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P06 : WideCovered band 8677011 8986633 := wide_block_sound band profiles_RelativeWidePack6815_P06 8677011 8986633 (wideData 16 0x17a80bd28001979b80000000005f602f8a80065e70000000000234b07d2c001979b80000000008abc23da00065e700000000001bab0be68001979b80080000006f78321b00065e700000000801bff0caf0001979b80000000006f7033ad80065e700000000001b5b0dbba001979b82000080013b341f7b00065e70000000000638c05e72001979b8000000001aaec167d00065e6e0000000003a7c04c72001979b80000000012b342e8001979c000000000168a80a59c0065e6e0be0be12e0be0be12e06c965904e32da2210cb98b4) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P06 : WideCovered band 8986634 9373662 := wide_block_sound band profiles_RelativeWidePack6815_P06 8986634 9373662 (wideData 16 0x2da7b19c27002af2f800000000038eec0ea2d002af2f80000002008a34c02fe99400abcbe1020040803b3a694bd9b2002af2f80000000001bf0432980065e6e0000000007e4462900065e700000000002e8474c00065e6e082002080274c09da2001979c0000000000dc602abc80065e6e0000000003b6d0bb2e001979c0000000000fd2c2ecc00065e6e000000000436d0bb38001979b80000000011fa42ed880065e6e000000000435f0bbac001979c00000000005cbc2efc00065e6e0e00e012e0e00e012e0729e3b04f3a97e211975ea2) (by decide +kernel)
private theorem c9_RelativeWidePack6815_P06 : WideCovered band 9373663 9992909 := wide_block_sound band profiles_RelativeWidePack6815_P06 9373663 9992909 (wideData 16 0x1ed70068aa6002af2f80000000001861801a35b000abcbe000000000063ff80699b8002af2f80000000019d7006a860002af2f800000000039a4069e78002af2f80000000006c747e4b800abcbe0820020800b8e01afbd800abcbe000000000060c607a08800abcbc000000000064978773f800abcbe000000000068fbc7688000abcbe00000000006ace837fb800abcbe0000000006aff1aeee002af2f80000000011aa06a0b800abcbe0000000004f8918f78002af2f80000000017b685ecf800abcbe0e60e612e0e60e612e076936905c319a0211fafc3a) (by decide +kernel)
private theorem c10 : WideCovered band 9992910 10612155 := wide_block_sound band profiles_RelativeWidePack6815_P06 9992910 10612155 (wideData 16 0x2080082007ab40a7caa002af2f8000000001fbac07c8e8002af2f8000000000182de01f2ee000abcbe000000000061cfc07d830002af2f8000000001f930072d74002af2f800000000018e7c01faed800abcbe000000000064841ffbb800abcbe082002080276e01ebff000abcbc000000000771801c7cc000abcbe00000000076aa01b7ab800abcbe0000000007aad01b31b000abcbe000000000062b6c0739ee002af2f80000000019828074aa8002af2f80000000014e41d79a800abcbe0820020800faf01d279800abcbe0e80e812e0e80e812e0a2de6b06834dea213928ff6) (by decide +kernel)
private theorem c11 : WideCovered band 10612156 11579727 := wide_block_sound band profiles_RelativeWidePack6815_P06 10612156 11579727 (wideData 16 0x82002080073b6822bd22004de5e80000000004ffed08ef2d8013797c00000000016b86422c9f2004de5f00000000004fa2904d61d8013797c00000000013dd701bcaa0004de5e800000000028a81a0e60004de5f0000000000787cd02dbfac013797c000000000430e641b39f7004de5f08200208006af50e9938f0013797a0000000003280ada7e002af2f820800820018aac02a2dd800abcbe000000000063af80a8b78002af2f80000000001926e02a39c800abcbe0000000000659f80a9b30002af2f800000000018eba0286bf000abcbe0ee0ee12e0ee0ee12e0adc36f06f63fa2214aa2bb4) (by decide +kernel)
private theorem c12 : WideCovered band 11579728 12818220 := wide_block_sound band profiles_RelativeWidePack6815_P06 11579728 12818220 (wideData 16 0x721de00a987ba0013797a08200208053fce407ed6888013797c0000000004ab9ac06f872c8013797c0000000004b3b6006fdaaa0013797c08200208036fb3c069d7580013797a0000000002f4cac760c2a004de5f0000000000caace1edb8f8013797c0000000002f7be073a8fe004de5f02080082005dbad14e7188013797a000000000236a7053adb0004de5f00000000008bf5a13f23f0013797c0000000001ae930421c66004de5f02080082004a73a0fc3b80013797c00000000017fab0339a72004de5f00000000005f3090be64e8013797c0fa0fa12e0fa0fa12e125d2ee0c8b8cf42169efeba) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7864249 8040831 12818220 c0_RelativeWidePack6815_P06 (wide_covered_join band 8040832 8086791 12818220 c1_RelativeWidePack6815_P06 (wide_covered_join band 8086792 8130332 12818220 c2_RelativeWidePack6815_P06 (wide_covered_join band 8130333 8173872 12818220 c3_RelativeWidePack6815_P06 (wide_covered_join band 8173873 8309333 12818220 c4_RelativeWidePack6815_P06 (wide_covered_join band 8309334 8464144 12818220 c5_RelativeWidePack6815_P06 (wide_covered_join band 8464145 8677010 12818220 c6_RelativeWidePack6815_P06 (wide_covered_join band 8677011 8986633 12818220 c7_RelativeWidePack6815_P06 (wide_covered_join band 8986634 9373662 12818220 c8_RelativeWidePack6815_P06 (wide_covered_join band 9373663 9992909 12818220 c9_RelativeWidePack6815_P06 (wide_covered_join band 9992910 10612155 12818220 c10 (wide_covered_join band 10612156 11579727 12818220 c11 c12))))))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 11)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 11≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤60)
    (hT0 : 3328≤T) (hT1 : T≤3964) (hnu : 7864249≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤34167255524904513 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R036

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R037
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨11,61,3277,3933,33040284130127184⟩
private def profiles_RelativeWidePack6815_P06 : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨24769,195,5079⟩
  | 2 => ⟨9353,74,2353⟩
  | 3 => ⟨43518,250,10158⟩
  | 4 => ⟨26184,140,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P06 : WideCovered band 7995320 8046632 := wide_block_sound band profiles_RelativeWidePack6815_P06 7995320 8046632 (wideData 16 0x4efa909d6a800138e00000000001b20b02fbad400aca80000000001afbf03969dc00acb00000000001971f048afec00acb00000000001939804afba400acb00000000008b39278d33002b2a00000000007f8380b78be002b2c0000000004a2e02becdc00669800000000128380b1cb50019a60000000005e380ad280019a60000000000fdb17973013880000000009b600bf94027208210208413b9328468ea089c800000000039b2bf0238f739004e2e8000000000196995bd63d404e2f02d82d84b02d82d84b10ef5c68070a76b7200fa66866) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P06 : WideCovered band 8046633 8085727 := wide_block_sound band profiles_RelativeWidePack6815_P06 8046633 8085727 (wideData 16 0x681fbd6d004e380000000000eea7c0e0f72004e360000000000e3878074fe4004e380000000001a9808926f40138d80000000003b28c02863a00138e0000000000897d2aae61004e360000000000eaeb4067d2e004e360000000000ea8ac6b4b80138d8000000000da713248f5004e380000000000e8c78124dc0138d80000000003a29911f27004e380000000004e9e4eab3dc0138d800000000039b8901dec8c0138e00000000001a67a08ff4940138d800000000018e680aaa3f40138e02e02e04c02e02e04c0fde086c077c7d9f608fae8ee6) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P06 : WideCovered band 8085728 8124822 := wide_block_sound band profiles_RelativeWidePack6815_P06 8085728 8124822 (wideData 16 0xfdc3c1e1fbc004e380000000000fa8a41b4db0004e360000000004f0f03a649c0138e00000000003eabb06bbeb00138d80000000003da4905fbc900138e00000000011aa80fd963004e360000000000f7cf017bd7a004e360000000000f28a4166d3e004e360000000003e1d04cf3840138e00000000003d3980597ea00138d80000000007eb0176b61004e380000000000f38e0136aa6004e360000000000f2b2412f976004e380000000000fdd06de5c40138d80000000003c38b03f77a00138e02e02e04c02e02e04c10da3ff8075cfadfe08fb759b4) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P06 : WideCovered band 8124823 8289463 := wide_block_sound band profiles_RelativeWidePack6815_P06 8124823 8289463 (wideData 16 0x2fa0f05eacf000aa9a0082002080078f06aa88800aa9a0000000000075a380e89f8002aa68030d30c34d0ab1c3d071cbbff5082aa6800000000011a01d66014000000000067d02da8001980000000005c6422980027200000000046c80292001390000000001a87406ccb60019a40000000003fa814af90019a60000000000789380e49f2002b2c000000000077cf80e28f8002b2c0000000002e8945bf3a400acb00000000001820801c3af40138d80000000003fabc07aa5900138e02e02e04c02e02e04c11f76838076c2bf6208fc21ca2) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P06 : WideCovered band 8289464 9144101 := wide_block_sound band profiles_RelativeWidePack6815_P06 8289464 9144101 (wideData 16 0x104484112437ab8b41ae28f0e420658e0082002080162dfff0dcb0d2e002aa6800000000002ea9f3c1e7a3ab000aa9a0000000000074b6bb0497baf4002aa5f80000000001b65cf40f3c26b800aa9a0000000000765fb00aaa28a800aa9a00c30030c0226fb2b56eeab3f002aa6802080082004c28c7833787fd00134b20000000000072b2fc03ef8f78004d2c800000000001d3bfa412292ab00134afe000000000063ff0b02c7b920004d2c80000000001abaed01b7fc66004d2c800000000015a33c0b83bfc0134b201040041000a3fb6d09bf6834004d2c800000000002f77d06a7ce800aa9a00b80b80fe0b80b80fe0a5e2cb05f628e010ff28c6e) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P06 : WideCovered band 9144102 9618900 := wide_block_sound band profiles_RelativeWidePack6815_P06 9144102 9618900 (wideData 16 0x6bc30533d800aa9a0000000000070bec2bf9000aa9a00000000000719f05f3c800aa9a0000000000066d200bfe800aa9a0000000000062e284698000aa9a00000000000a58703b18400aa9a00000000000a9bf00a09400aa9a0000000000174aac0a9c25002aa5f8410010400beaca51d69d000aa9a000000000043d90bbb8001963800000000007a782edd000658e0000000000167a0bba6001963800000000005a7c2eee000658e00000000000b7d118f40019638000000000059642fbb800658e00e20e21300e20e2130075ce2c04f66ae0191be8d6a) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P06 : WideCovered band 9618901 10226642 := wide_block_sound band profiles_RelativeWidePack6815_P06 9618901 10226642 (wideData 16 0x60e38070bbe002aa680000000001efec066df8002aa6800000000001964b01c7d8000aa9a00000000004eca019f1d800aa9a0000000000438074c6c002aa6800000000002afc069c3e002aa6802080082015efc7fcf000aa9a0000000000061924067838002aa5f80000000001821c1cb6c002aa68000000000019eea019f6f800aa9a0000000000061d306fb8800aa9a0000000000179801a65f800aa9a00000000002e5c1bdbe002aa6800000000002c6006c96e002aa680208008200bb2c6fd8000aa9a00e60e61300e60e613007d8b3c05c6db28192b6d8e6) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P06 : WideCovered band 10226643 10834384 := wide_block_sound band profiles_RelativeWidePack6815_P06 10226643 10834384 (wideData 16 0x2080082013cb80ac9b6002aa680000000001ff2007aff6002aa680000000000186cd01f60a000aa9a0000000000064da80a3c64002aa68000000000018b8c01ef4b000aa9a00000000007e9b029eec000aa9a000000000006eb01f69e000aa9a00820020804b4901ffda000aa97e000000000766901c25c000aa9a0000000000061fa007a96c002aa680000000001fcf4070d24002aa6800000000001922b01e3d8000aa9a00000000004fe801d35f800aa9a000000000007cf01cb2d000aa9a00820020802e1901e64d800aa9a00ea0ea1300ea0ea1300a7e2ec06936c7a193cb08e2) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P06 : WideCovered band 10834385 12011885 := wide_block_sound band profiles_RelativeWidePack6815_P06 10834385 12011885 (wideData 16 0x7b6df0ffe6a00134b2000000000012cbb83f0eec004d2c80208008200597ae0bf3ea80134b20000000000175b7c2e6abe004d2bf80000000005eb5f0aebef80134b200000000000ee9742b3f62004d2c802080082002a669079ee880134b20000000000126e6817eeba004d2bf80000000004f78c06aa9f00134b200000000001749e8174824004d2c800000000005a68e04d7ed80134b200000000000addf40e3a38004d2bf80000000006b79d0eeef004d2c80000000001db7390ee60840134b202080082004a0f750e9fecd00134b200f00f01300f00f01300b3ca0a078bcaa8194df38e0) (by decide +kernel)
private theorem c9_RelativeWidePack6815_P06 : WideCovered band 12011886 12999465 := wide_block_sound band profiles_RelativeWidePack6815_P06 12011886 12999465 (wideData 13 0x30c00c3001a087bf41a6d8e3084d2bf8000000001daf8902a6ba62004d2c800000000019e32b02820f7c004d2c802080082013c6d901dfa8fa004d2c800000000011b3ac01ab4eea004d2bf8000000000ffb49019b9bfe004d2c80000000000eeace018f5ffa004d2c802080082009c7281dea7880134b200000000002b8d6c66e97e004d2bf80000000009f33c16f29e80134b20000000000228fbc533c30004d2c802080082005ef4812b36880134b200fc0fc1300fc0fc130165ceea0dee7f6e1978798b8) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7995320 8046632 12999465 c0_RelativeWidePack6815_P06 (wide_covered_join band 8046633 8085727 12999465 c1_RelativeWidePack6815_P06 (wide_covered_join band 8085728 8124822 12999465 c2_RelativeWidePack6815_P06 (wide_covered_join band 8124823 8289463 12999465 c3_RelativeWidePack6815_P06 (wide_covered_join band 8289464 9144101 12999465 c4_RelativeWidePack6815_P06 (wide_covered_join band 9144102 9618900 12999465 c5_RelativeWidePack6815_P06 (wide_covered_join band 9618901 10226642 12999465 c6_RelativeWidePack6815_P06 (wide_covered_join band 10226643 10834384 12999465 c7_RelativeWidePack6815_P06 (wide_covered_join band 10834385 12011885 12999465 c8_RelativeWidePack6815_P06 c9_RelativeWidePack6815_P06)))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 11)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 11≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤61)
    (hT0 : 3277≤T) (hT1 : T≤3933) (hnu : 7995320≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤33040284130127184 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R037

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R038
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨11,62,3228,3901,33967310682341084⟩
private def profiles_RelativeWidePack6815_P06 : ℕ → Profile
  | 0 => ⟨9353,74,2353⟩
  | 1 => ⟨43768,250,10158⟩
  | 2 => ⟨26184,140,5079⟩
  | 3 => ⟨26253,139,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P06 : WideCovered band 8126391 8995102 := wide_block_sound band profiles_RelativeWidePack6815_P06 8126391 8995102 (wideData 16 0x1b3abac0ee8e5e800ad8fe0000000007609700a6eeeb800ad8fe0000000005ea868078e6a8000ad8fe0000000001f7823f53e61835002b63f80000000002d309f41ababac8013a9fc0000000000aeb3de05f32ff0004ea7e800000000138e991cff6a8013a9fc0000000007fcfa007196eb8013a9fc00000000007d877b4a9fcbfb004ea7f041001040069a1af85ecafc88013a9fa0000000000e7f241b6fe8002b63f800000000049a6f08fb6e000ad8fe0000000000e987c1a7d32002b63f820800820119a91619f2002b63f80000000002c2ea0596b8800ad8fe0b60b60fe0b60b60fe07ec33e058aaeb800fcacfea) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P06 : WideCovered band 8995103 9370227 := wide_block_sound band profiles_RelativeWidePack6815_P06 8995103 9370227 (wideData 16 0x13a80de360019b1f80000000002db047e880066c7e002000000139c0dc360019b2802000082008cb43abc00066c7e000000000471d0bdbe0019b28000000000118241bc800066c7e000000000522b0bc700019b2800000000015d3c2f0a80066c7e000000000478e05fe00019b28000000000089fc2e9980066c7e000000000232d0ba6e0019b280000000000cd2c137980066c7e1045041143e7ab294196efadd42066ca00820020801298ebe0b870cfa002b63f80000000002aab9b0176ce8c000ad8fc0bc0bc0fe0bc0bc0fe2a8babc19c77f2a0119edd7a) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P06 : WideCovered band 9370228 9903300 := wide_block_sound band profiles_RelativeWidePack6815_P06 9370228 9903300 (wideData 16 0x2080082011aa07ea9800ad8fe000000000066b2853fc800ad8fe000000000070ca4060ef2002b63f80000000001ce3e11cf0002b63f80000000001b2be0eae4002b63f800000000178b876cd000ad8fc000000000069ffc1a7c800ad8fe00000000007a9300e7cc00ad8fe000000000076fb03b09000ad8fe0020000001258a806ac2b002b63f8408010400897f850bb68800ad8fe0000000001aed0ff320019b1f800000000048ec3fdc00066ca0000000000179e0baec0019b1f80000000003db4435800066ca00e40e41320e40e41320799e5d04ff2d24091f63e64) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P06 : WideCovered band 9903301 10535090 := wide_block_sound band profiles_RelativeWidePack6815_P06 9903301 10535090 (wideData 16 0xa1801ee2c000ad8fe08200208066cb01bf4d800ad8fe0000000000648f4077a3c002b63f8000000000187db01b67b000ad8fe000000000063fb006daaa002b63f800000000019a5b01e779800ad8fc000000000166b01bb9d800ad8fe0000000000f4f01bf4f000ad8fe0820020804a3e01d25e000ad8fe000000000060b7c063ae2002b63f800000000018b58018a8c000ad8fe000000000066fec065920002b63f80000000001a2d801ae99000ad8fe0000000002b8b018a1f000ad8fc0000000002b6a0187ad000ad8fe0ea0ea1320ea0ea1320a1dafe05de9da0092fbbc26) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P06 : WideCovered band 10535091 11206367 := wide_block_sound band profiles_RelativeWidePack6815_P06 10535091 11206367 (wideData 16 0x2080082001339750f2e2bf0013a9fc00000000006d9a00b3fee002b63f800000000158b80e1b34002b63f82080082011a780aea2a002b63f80000000001966c0292c8000ad8fe000000000069fbc0aeca0002b63f000000000019ec802972c000ad8fe0000000000689e80a5864002b63f800000000018b4902a36e800ad8fe000000000070902bfeb800ad8fe082002080661f01efa8800ad8fe000000000061f20077e36002b63f800000000019e6c028b59000ad8fe000000000064c78078b6c002b63f000000000019a8d01e3a9800ad8fe0ee0ee1320ee0ee1320adce8806bb29fc09496dbe2) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P06 : WideCovered band 11206368 12469947 := wide_block_sound band profiles_RelativeWidePack6815_P06 11206368 12469947 (wideData 16 0xde63f1f8bab0013a9fc0820020801f88bc660d6a004ea7f00000000009e35a15ab5a0013a9fc000000000279b6c53fae8004ea7e80000000008b2ac10daeb0013a9fc08200208012cf20476ea2004ea7f00000000007a20b0eaf0d0013a9fc0000000001a6e3c2b9a6a004ea7e80000000007ceae0d9e4c8013a9fc08200208006b8b0324f22004ea7f00000000004db9d06ab8a0013a9fc00000000017ffbc1fffe4004ea7e80000000005c21803cb398013a9fc000000000223fac16d9e4004ea7f00000000007be99039b2a8013a9fc0fa0fa1320fa0fa1320eabf8b0ad6ad6e095c39d78) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P06 : WideCovered band 12469948 13180710 := wide_block_sound band profiles_RelativeWidePack6815_P06 12469948 13180710 (wideData 9 0x820020800f38b1d45ca7c0213a9fa28a00a2800ac9b3b4486df60084ea7f000000000018f982c0b5e6dd0013a9fc08200208073aca80ae968e8013a9fc000000000666c7407bf3ee8013a9fa000000000528a2806faf1d8013a9fc0000000004f5b78070a6998013a9fc082002080370e700659f8b8013a9fc1201201321201201321e3c2191292a9f0097f7dcf0) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8126391 8995102 13180710 c0_RelativeWidePack6815_P06 (wide_covered_join band 8995103 9370227 13180710 c1_RelativeWidePack6815_P06 (wide_covered_join band 9370228 9903300 13180710 c2_RelativeWidePack6815_P06 (wide_covered_join band 9903301 10535090 13180710 c3_RelativeWidePack6815_P06 (wide_covered_join band 10535091 11206367 13180710 c4_RelativeWidePack6815_P06 (wide_covered_join band 11206368 12469947 13180710 c5_RelativeWidePack6815_P06 c6_RelativeWidePack6815_P06))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 11)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 11≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤62)
    (hT0 : 3228≤T) (hT1 : T≤3901) (hnu : 8126391≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤33967310682341084 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R038

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R039
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨11,63,3180,3869,33197636390103700⟩
private def profiles_RelativeWidePack6815_P06 : ℕ → Profile
  | 0 => ⟨24832,192,5079⟩
  | 1 => ⟨24889,189,5079⟩
  | 2 => ⟨24986,187,5079⟩
  | 3 => ⟨25032,184,5079⟩
  | 4 => ⟨25120,182,5079⟩
  | 5 => ⟨43768,250,10158⟩
  | 6 => ⟨26184,140,5079⟩
  | 7 => ⟨26253,139,5079⟩
  | 8 => ⟨26320,138,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P06 : WideCovered band 8257462 8416977 := wide_block_sound band profiles_RelativeWidePack6815_P06 8257462 8416977 (wideData 16 0xb9e8b08a2dec04ef880000000014d3e810e77b004ef90000000000f86cf10b7f8c04ef90000000001abb3a0bc77b804ef9000000000179feb1f9e9c404ef88000000001ede8c01cb68e5013be400000000007596a80ebea9c04ef9000000000029f486c0f6f398c04ef90208008200eda29fd1aca78a424ef88000000000f82da19db6d004ef900000000004de4804fabc404ef90000000000ebf8b15b39c004ef900000000003c37e0cdffb404ef88000000000eaf4910d60f004ef90000000000e966f0daa3d004ef902e82e84d02e82e84d0eff49a806e8bd97000fe33aae) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P06 : WideCovered band 8416978 8576492 := wide_block_sound band profiles_RelativeWidePack6815_P06 8416978 8576492 (wideData 16 0xb9b6d0bd38fc04ef88000000000de61f10eb9e404ef900000000011db7b18dedc404ef880000000004d21ba10b0bb99424ef900000000009fbdf49c28b804ef882080082001e7bf44bfde004ef900000000006de8c09de0b004ef900000000003de4a0bef6013be40000000000f68ac637ac04ef880000000003d2ca029a5ac04ef900000000003d39b03db09404ef900000000007bebf0696ad804ef900000000003fa3b06eecd404ef880000000002b7caf1226d328424ef900000000010ca7814fe8e804ef902f02f04d02f02f04d0acaca3c062eace6e0908aaf26) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P06 : WideCovered band 8576493 8895523 := wide_block_sound band profiles_RelativeWidePack6815_P06 8576493 8895523 (wideData 16 0x30001400b3ff0959d7686b0819be9800000820038259b60a2973dc0066fa60820000002e6df6ac4baaff50819be9800000000158ffa0ddaea80066fa80000000005bfbec13fd6c0019be98000000001ad7dd07d749c0066fa800000000006283591da24a40066fa6000000000072bb3d02a368eb0019bea00000000003867dac1a09f99c0066fa608200208037efbaf45fe5d3f0819bea00000000001861df8075e7b900066fa60000000001eff7c7a1ba30019bea0000000001f92ec1c8b6d00066fa600000000006ad780b9ee7c40066fa80000000007eaea87e1f6f0019be982f82f84d02f82f84d0eefb928076826d7e110b35f60) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P06 : WideCovered band 8895524 9214554 := wide_block_sound band profiles_RelativeWidePack6815_P06 8895524 9214554 (wideData 16 0x17b20236c80066fa600000000037bf0ac2e0019be98000000000a8a42add80066fa60000000002eed08eb00019bea0000000000d82c1ec980066fa60000000003a7d06f2c0019bea0000000000fe641a7b00066fa6000000000475e05baa0019bea000000000148f012dd00066fa60020000805e7d038fc0019bea0000000001bbe8069b80066fa6000000000061ae8068a40066fa800000200006a8bc166c40066fa6000000000077cf42ec940066fa80000030000af8305abdc0066fa60e20e01340e20e013406afb5e04e66a2229182582e) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P06 : WideCovered band 9214555 9573464 := wide_block_sound band profiles_RelativeWidePack6815_P06 9214555 9573464 (wideData 16 0xf3aa07e1b400adf2e10400410023192d438974002b7cb0000000001297836c880066fa60000000003e5a0dba80019bea00000000005e60370c80066fa6000000000179b0dd260019bea00000000005ea4377a00066fa6000000000179a0df360019bea00000000005e2c3a2e00066fa6000000000175e0eae40019bea00000000005c783b4e80066fa600200008016b90f86e0019bea000000000058a03f0980066fa608000200047be09c2e0019bea00000000013ee823fc00066fa60e20e21340e20e2134078930804eb08a6291cf48fc) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P06 : WideCovered band 9573465 10211526 := wide_block_sound band profiles_RelativeWidePack6815_P06 9573465 10211526 (wideData 16 0x208008200cbe806ea6e002b7cb800000000018b5a018fdc800adf2c000000000065bbc063d26002b7cb80000000001a3ff018eb9000adf2e00000000006dc7c063962002b7cb8000000000db700638a8002b7cb8000000000cdfc06386c002b7cb8000000000cd34063a2c002b7cb8000000000cab8063e3a002b7cb8208008201cefc7f48000adf2c000000000074a687b68000adf2e000000000078fec4a49000adf2e00000000006fde03ba9800adf2e000000000067dbc2a4f800adf2e0000000000749640bef000adf2e0e80e81340e80e8134079a7fa05bee876292ab887e) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P06 : WideCovered band 10211527 10849587 := wide_block_sound band profiles_RelativeWidePack6815_P06 10211527 10849587 (wideData 16 0x19b99029f7e800adf2e0000000000ffa02a37f000adf2c0820020804fba02864a000adf2e0000000000648bc079c2c002b7cb8000000000196c901e76f000adf2e000000000066f7407a872002b7cb00000000001a3aa01eb3a800adf2e000000000520e01eef8000adf2e0000000000ecf01f35a000adf2e0820020804baf01d768000adf2c000000000065e7407783e002b7cb8000000000193ff01c30e800adf2e000000000066d6006f9ec002b7cb800000000019f7801bf88800adf2e0000000001ab901c30a000adf2e0ec0ec1340ec0ec1340a98b6c05fb5cec293c76a3a) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P06 : WideCovered band 10849588 11846559 := wide_block_sound band profiles_RelativeWidePack6815_P06 10849588 11846559 (wideData 16 0x1e3b782e5bf6004ef8f00000000005e6e80c93db0013be3a0820020800a3fe42ac8f6004ef8f00000000005bf9e0687df8013be3c0000000001a3820132db4004ef8f00000000007ae7b02a63c0013be3a0000000002a7dac0a39eb004ef8f00000000012d36c0dd7fdc013be3c2080082000f8e690fff34e0013be3c00000000006fee80b5fee002b7cb0000000001ef640bf9a2002b7cb8208008200c97c0b7f6a002b7cb800000000019f1a029aac800adf2e000000000068b340a6af2002b7cb80000000001a6ec029b2c800adf2e0f00f01340f00f01340b7be2e06efb830294e34bf4) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P06 : WideCovered band 11846560 13122683 := wide_block_sound band profiles_RelativeWidePack6815_P06 11846560 13122683 (wideData 16 0xa28028a002a75b2d0fcdedd0213be3c000000000069ea4e0383def0004ef8e800000000018faae80ba82bc8013be3c08200208063db2c07b8bbf0013be3c0000000005bdf34073f73d0013be3c000000000538f7c06ec7af8013be3a082002080377ee4066f77f8013be3c0000000003afc387f7d68004ef8f0000000000dcf9d1dab0d8013be3c0000000002fecbc72f978004ef8e82080082008e7ac188be98013be3c00000000026fef84e9c24004ef8f00000000009ab1a12a35d0013be3c00000000013af3846ff72004ef8e82080082006d31f0cef6a0013be3c0fc0fc1340fc0fc1341608b7b0cd70c2c296dfdcba) (by decide +kernel)
private theorem c9_RelativeWidePack6815_P06 : WideCovered band 13122684 13361955 := wide_block_sound band profiles_RelativeWidePack6815_P06 13122684 13361955 (wideData 3 0x20800820048fcdbd0acdb2a4213be3a00000000007fdae902ae6d7f004ef8f04c04c04d04c04c04d079b6da4062f7ddfc39997a830) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8257462 8416977 13361955 c0_RelativeWidePack6815_P06 (wide_covered_join band 8416978 8576492 13361955 c1_RelativeWidePack6815_P06 (wide_covered_join band 8576493 8895523 13361955 c2_RelativeWidePack6815_P06 (wide_covered_join band 8895524 9214554 13361955 c3_RelativeWidePack6815_P06 (wide_covered_join band 9214555 9573464 13361955 c4_RelativeWidePack6815_P06 (wide_covered_join band 9573465 10211526 13361955 c5_RelativeWidePack6815_P06 (wide_covered_join band 10211527 10849587 13361955 c6_RelativeWidePack6815_P06 (wide_covered_join band 10849588 11846559 13361955 c7_RelativeWidePack6815_P06 (wide_covered_join band 11846560 13122683 13361955 c8_RelativeWidePack6815_P06 c9_RelativeWidePack6815_P06)))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 11)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 11≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤63)
    (hT0 : 3180≤T) (hT1 : T≤3869) (hnu : 8257462≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤33197636390103700 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R039

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R040
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨11,64,3126,3835,33315626530704906⟩
private def profiles_RelativeWidePack6815_P06 : ℕ → Profile
  | 0 => ⟨24889,189,5079⟩
  | 1 => ⟨25032,188,5079⟩
  | 2 => ⟨24986,187,5079⟩
  | 3 => ⟨25032,184,5079⟩
  | 4 => ⟨25120,182,5079⟩
  | 5 => ⟨25155,179,5079⟩
  | 6 => ⟨44018,250,10158⟩
  | 7 => ⟨25897,151,5079⟩
  | 8 => ⟨26184,140,5079⟩
  | 9 => ⟨26253,139,5079⟩
  | 10 => ⟨26320,138,5079⟩
  | 11 => ⟨26312,136,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P06 : WideCovered band 8388533 8549616 := wide_block_sound band profiles_RelativeWidePack6815_P06 8388533 8549616 (wideData 16 0x122da9a42fbbb3f093d66000000000462e43d3b9004f5a00000000005ee0d169f9013d680820020807619b96abe3c013d680000000000ead28061f75013d660000000001b5aa41e6876013d680000000000ecbb80e3b77013d680000000000e9cf813cebf013d680000000001e5a241319f6013d66000000000065ce7f448a3e65093d680000000002348a406ceb8013d68000000000062b7884483fd6d093d68000000000326bec624d004f598000000000fb30f04eebf804f5a00000000013f2be0cabcb004f5a02f02f04d82f02f04d89cabb740629b8be8010833c30) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P06 : WideCovered band 8549617 8791241 := wide_block_sound band profiles_RelativeWidePack6815_P06 8549617 8791241 (wideData 16 0x1a649686bfdae0019eab80000000001862e3c07e968ec0067ab0000000000075cbfe04c35fed0019eab80000000004c72bb013be64dc0067ab0082002080420bafc43d68eb50819eab8000000001afaba1dd68a80067aae00000000066cbe83fca660019eab80000000009c6ba606ea824a03067ab0000000000177eb806caad013d660000000001a79f40b7d79013d680000000001bae74130837013d680000000001f4e6c1b8fe1013d680000000002398ec2778fb013d660000000002ac9e8377ca3013d680000000004358e40aab23013d680be0be1360be0be136170ae6e17fedfa4190aae928) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P06 : WideCovered band 8791242 9113408 := wide_block_sound band profiles_RelativeWidePack6815_P06 8791242 9113408 (wideData 16 0x1c73b0efeb0019eab8000008201bb6c067980067ab000000000012cd3407cdb10019eab82000003006bb89ad4a1b6f842067ab00000000001baf30234ef10019eab8000000000dafaf039a2f80067aae000000000269ff85bed250019eab800000000139a5a0bfadac0067ab000000000033693116aab7ac2067aae0000000001fb8fd43e8f80019eac000000000039e7834078969940067aae0000020803f7df60f0b77dc0067ab0082000000274a2c8c2da8a2d0819eab80000000011aeaa07924d80067ab000000000047f8200b182b0019eab83803804d83803804d8be33f38064df4926190e79de2) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P06 : WideCovered band 9113409 9435575 := wide_block_sound band profiles_RelativeWidePack6815_P06 9113409 9435575 (wideData 16 0x56cd08d260019eab8000000000de24229880067ab0000000000228d0dd3e0019eab8000000000b9b41faa00067ab000000000023db0dde80019eab8000000000cd641e8a80067aae00000000037cd06ce20019eab8000000000ac30377f80067ab000200000042ba05d760019eab8000000200bfa037b900067ab00000000004fdc04b260019eab8000000001797c0bcc80067ab0000000000428c0db6a0019eab8000000001f8201310019eac000000000159fc339f00067aae0e40e21360e40e2136073fe3f04df5af6311b6efb0) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P06 : WideCovered band 9435576 9918825 := wide_block_sound band profiles_RelativeWidePack6815_P06 9435576 9918825 (wideData 16 0x67091aa74002bb4f80000000001aa7d03c24002bb4f800000000019f5b12b2e002bb4f80080000001cefc0ce3a002bb4f80000000002a3bf02d6a002bb4f80000002003db4913921002bb4f80000000009b3b903d76fc00aed3c102004080439d71538efa002bb4f800000000048e04e7e00067aae0000000001a2b0deec0019eac00000000003a7c528d80067aae00200008017590ec6c0019eac0200008000ba242fdb00067aae0000000004e7b0dd3c0019eab80000000012cb423fe80067aae0e40e41360e40e413607c96db04f27d2a31286497e) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P06 : WideCovered band 9918826 10563159 := wide_block_sound band profiles_RelativeWidePack6815_P06 9918826 10563159 (wideData 16 0x1b2ab01df79800aed3e00000000043bf01bb2f800aed3e0000000001a6f01dbfc000aed3e08200208027fd01e228800aed3e000000000065ab806bb28002bb4f800000000019fb801af0c000aed3e00000000006ac6806ada2002bb4f00000000001aa8c0182ec800aed3e0000000003fa901b248800aed3e000000000275b01b639800aed3e000000000221b01bb28000aed3e08200208053f901a628800aed3e0000000000669e04bbf800aed3e000000000070834777b800aed3e000000000076ee4738e800aed3c0ea0ea1360ea0ea1360a2f78805cb9ba8312ffbaf0) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P06 : WideCovered band 10563160 11207492 := wide_block_sound band profiles_RelativeWidePack6815_P06 10563160 11207492 (wideData 16 0x1ba5d02c3cd800aed3e00000000006cce00ab8f0002bb4f80000000001b76a02aea8000aed3e000000000071c740b1dba002bb4f80000000017ca40b2d26002bb4f8208008200a8780b1b62002bb4f80000000001a39e028b0b800aed3c000000000065ae4077df4002bb4f80000000001ae88028b9c800aed3e00000000006cfe00a3ba0002bb4f800000000018eec0292ae000aed3c000000000169f02973d800aed3e0820020803a5b01d6fc800aed3e000000000066868076a2e002bb4f800000000019f6f01db0d000aed3c0ee0ee1360ee0ee1360b1eaff06a268b83149e5eac) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P06 : WideCovered band 11207493 12415617 := wide_block_sound band profiles_RelativeWidePack6815_P06 11207493 12415617 (wideData 16 0xb8f8a15ceae8013da7c000000000274868627fe0004f69f02080082006c6cc0fd3e90013da7a000000000267a2c461cfa004f69f00000000009a65a10a69e8013da7a00000000017df78323eac004f69f02080082003ca4d0ce3480013da7a0000000001b9b3c273ca2004f69f00000000006c3db06e7a98013da7c000000000231ba822adf4004f69f00000000007b7980283c80013da7a000000000133e700f2c62004f69f0000000000d8fbf03976bc013da7c0820020804f6ef96afdf70c4f69f00000000006c719059219c00aed3c0fa0fa1360fa0fa1360f9be0d0c8b9ebc395bb0a66) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P06 : WideCovered band 12415618 13543200 := wide_block_sound band profiles_RelativeWidePack6815_P06 12415618 13543200 (wideData 14 0xc30030c00b3afdc01e60821004f69e82080082002835e3122dc3dbc213da7c0820020800e8d23a4a934fc213da7a0820020800abc7d942cbab63084f69f0000000001ede090ee27fc013da7a28a00a28047f8b91ffdfea0413da7c000000000062af7802aee8ee004f69f00000000001867a3c0a8f3bd8013da7c08200208057ed74078d34c8013da7a00000000057e86806fa7288013da7c0000000004ffef406ad2fe0013da7c00000000042dfe4061ffd80013da7c0820020802edf68060d7e90013da7a1201201361201201361bff74d10c69da4317eb6c7e) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8388533 8549616 13543200 c0_RelativeWidePack6815_P06 (wide_covered_join band 8549617 8791241 13543200 c1_RelativeWidePack6815_P06 (wide_covered_join band 8791242 9113408 13543200 c2_RelativeWidePack6815_P06 (wide_covered_join band 9113409 9435575 13543200 c3_RelativeWidePack6815_P06 (wide_covered_join band 9435576 9918825 13543200 c4_RelativeWidePack6815_P06 (wide_covered_join band 9918826 10563159 13543200 c5_RelativeWidePack6815_P06 (wide_covered_join band 10563160 11207492 13543200 c6_RelativeWidePack6815_P06 (wide_covered_join band 11207493 12415617 13543200 c7_RelativeWidePack6815_P06 c8_RelativeWidePack6815_P06))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 11)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 11≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤64)
    (hT0 : 3126≤T) (hT1 : T≤3835) (hnu : 8388533≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤33315626530704906 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R040

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R041
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨11,65,3047,3060,33039857377540443⟩
private def profiles_RelativeWidePack6815_P06 : ℕ → Profile
  | 0 => ⟨24986,187,5079⟩
  | 1 => ⟨25079,185,5079⟩
  | 2 => ⟨25032,184,5079⟩
  | 3 => ⟨25120,182,5079⟩
  | 4 => ⟨25204,180,5079⟩
  | 5 => ⟨25234,177,5079⟩
  | 6 => ⟨44268,250,10158⟩
  | 7 => ⟨26253,139,5079⟩
  | 8 => ⟨26320,138,5079⟩
  | 9 => ⟨26312,136,5079⟩
  | 10 => ⟨26374,135,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P06 : WideCovered band 8519604 8763581 := wide_block_sound band profiles_RelativeWidePack6815_P06 8519604 8763581 (wideData 16 0x7e4f018bcde70019f6d82080082006e62c4cd27b691019f6e0000000000df28728faa0019f6d8000000000cb2c3f6fec0019f6e0000000000aef0177940067db6000000000268915e34b40067db80000000001e7801dec8350019f6d80000000005fb1e1eba39701419f6e00000000004a2022afa5013eea00000000013bd0bdf4fc04fbb00000000005e344298eb013eec00000000026ec05da1dc04fbb00000000002a690f88e8dc24fba8000000000eaf837fd23093eec0000000006e591bb79b804fbb02f82f84e02f82f84e0286bf1b932e74010a33db2) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P06 : WideCovered band 8763582 9088884 := wide_block_sound band profiles_RelativeWidePack6815_P06 8763582 9088884 (wideData 16 0x820020800f6b250778b0942067db60000000001a6b07930800067db80000000001aea03f7da00067db60000000001bdb06fe50019f6e000000000039387bcb230019f6d80000000008d2c523feb0019f6e00000000004a4382bb650819f6d8000000001b8ac3f9c00067db8000000000069de446bfeb0019f6d80000000002a62b828229350019f6e00000000006df7d468bfb40067db60820020805f3cc4a32f290819f6e00000000010b24060b6aa80067db600000000022b915b7ab40067db60000000004ecc0feb9f00067db60e00e01380e00e01381a7b6c064865e7a110e248b2) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P06 : WideCovered band 9088885 9414187 := wide_block_sound band profiles_RelativeWidePack6815_P06 9088885 9414187 (wideData 16 0x6d80cf340019f6d80000000001da8366980067db80000000000a1a1dc80067db6000000000176f4cc7c0019f6e02080082002d211bcd00067db60000000005e412dc80067db80000000006a0065980067db600000000076c121e40067db8000000000063e09b40067db600000000006ad02cb30019f6e00000000003a20d50b63be50819f6d800000000099e02a1be40019f6e00000000007f2c273bf50019f6d8000000000a9f84e9ba90019f6d80000000012cec1e2f6d0019f6d83903904e03903904e02d3bc15fa4d26291affba0) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P06 : WideCovered band 9414188 9739489 := wide_block_sound band profiles_RelativeWidePack6815_P06 9414188 9739489 (wideData 16 0x2080082002bb9361e00067db60000000002b0362880067db80000000002e4361980067db60000000002f8361900067db80000000002f827b800067db60000000003382e4b00067db60000000003ac33bc00067db60000000003f033cb00067db800000000043433d880067db60000000004601b8f00067db8000000000520336f00067db60000000005b0338e80067db800000000066433bd00067db60000000006f4265b80067db60000000007f822db00067db60e60e61380e60e6138775f04e3ccfc311ffae6e) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P06 : WideCovered band 9739490 10390094 := wide_block_sound band profiles_RelativeWidePack6815_P06 9739490 10390094 (wideData 16 0x18a0067e62002bedb82080082001eb5072838002bedb80000000016e1aea4002bedb0000000001bf019a0a000afb6e000000000720625d000afb6e000000000063a019648000afb6e000000000069a01968a000afb6c00000000006d9139b0002bedb80000000001f3c0649b4002bedb80000000002aa032cb000afb6e0000000000ec8018789800afb6e00000000013cc038ff002bedb80000082003bb85b8e000afb6e0000030c04e7881dec9c00afb6e0000000000aeb7917f9f7002bedb03b03b04e03b03b04e02c3aa85da59fa312d3def0) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P06 : WideCovered band 10390095 11040699 := wide_block_sound band profiles_RelativeWidePack6815_P06 10390095 11040699 (wideData 16 0x1ad02838b800afb6e0000000007bc0adeb4002bedb8000000001da028a59000afb6c0820020805b90a0f34002bedb80000000018801e718000afb6e0000000006300789fc002bedb8000000001bb01fe6c800afb6c0000000006a0073f66002bedb8000000001ef028688000afb6e00000000077c075ba0002bedb8208008200196d074c30002bedb80000000015e019edc800afb6e00000000067c072cf8002bedb8000000001bf01cb9e800afb6e0000000006f0067e2c002bedb03b83b84e03b83b84e01b22f05efa8aa313f34caa) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P06 : WideCovered band 11040700 12016608 := wide_block_sound band profiles_RelativeWidePack6815_P06 11040700 12016608 (wideData 16 0x132b0ad32d0013eebc00000000017a80db38d0013eebc000000000179e0993190013eebc0820020800bec45e6ee8013eeba0000000000fce02bfce8013eebc00000000013aa01beda4013eebc0c30030c07aabc1affded004fbaf0a28028a001b67d85972ca8004fbae8000000001fb02effc800afb6e0000000007380afe60002bedb8000000000183c0bceb6002bedb8000000001fa02ce8d800afb6e0820020802bd0b2a20002bedb8000000001b902af38800afb6e00000000063c0a0baa002bedb03c83c84e03c83c84e01da3d06e3ccbe31592ba64) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P06 : WideCovered band 12016609 13317818 := wide_block_sound band profiles_RelativeWidePack6815_P06 12016609 13317818 (wideData 16 0x28a00a28007fc6d072bb3f0213eebc0000000007aba03c24c22004fbaf00000000019ae40bd8a2b8013eebc082002080434e029bfda8004fbae8000000000fff0079cecd0013eebc0000000003a9f01ce0b34004fbae82080082009ff406cda7b8013eebc000000000278c0187fa2c004fbae80000000009ae8060860b0013eebc000000000271e0182dfb6004fbaf02080082004ae45f3a60004fbaf000000000069f04fd920004fbae800000000068e04b59ba004fbaf000000000068f4475bb0004fbae82080082001c3c3b0bfe004fbaf03f83f84e03f83f84e03933a0cdff8f03178ace3a) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P06 : WideCovered band 13317819 13724445 := wide_block_sound band profiles_RelativeWidePack6815_P06 13317819 13724445 (wideData 5 0x2080082013c396fec79084fbae830c00c30028bff0a9e494013eebc000000000077b7a1e9e2af4013eeba0820020800fbf7716aee4d4213eebc132132138132132138139af40638278b8419c7a9ae) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8519604 8763581 13724445 c0_RelativeWidePack6815_P06 (wide_covered_join band 8763582 9088884 13724445 c1_RelativeWidePack6815_P06 (wide_covered_join band 9088885 9414187 13724445 c2_RelativeWidePack6815_P06 (wide_covered_join band 9414188 9739489 13724445 c3_RelativeWidePack6815_P06 (wide_covered_join band 9739490 10390094 13724445 c4_RelativeWidePack6815_P06 (wide_covered_join band 10390095 11040699 13724445 c5_RelativeWidePack6815_P06 (wide_covered_join band 11040700 12016608 13724445 c6_RelativeWidePack6815_P06 (wide_covered_join band 12016609 13317818 13724445 c7_RelativeWidePack6815_P06 c8_RelativeWidePack6815_P06))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 11)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 11≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤65)
    (hT0 : 3047≤T) (hT1 : T≤3060) (hnu : 8519604≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤33039857377540443 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R041
end MergedPart2
section MergedPart3
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R042
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨11,65,3081,3742,34751473937064351⟩
private def profiles_RelativeWidePack6815_P07 : ℕ → Profile
  | 0 => ⟨24986,187,5079⟩
  | 1 => ⟨25032,184,5079⟩
  | 2 => ⟨25120,182,5079⟩
  | 3 => ⟨25204,180,5079⟩
  | 4 => ⟨25234,177,5079⟩
  | 5 => ⟨44268,250,10158⟩
  | 6 => ⟨25984,150,5079⟩
  | 7 => ⟨26253,139,5079⟩
  | 8 => ⟨26320,138,5079⟩
  | 9 => ⟨26312,136,5079⟩
  | 10 => ⟨26374,135,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P07 : WideCovered band 8519604 8722918 := wide_block_sound band profiles_RelativeWidePack6815_P07 8519604 8722918 (wideData 16 0x130a3d918e2797e0c19f6d80000000016b25999ae4ac04fbb02080082010cb5bb76e19a8b444fbb00000000011a23f08be80019f6d8000000000edacf15b319c0067db800000000026c876b1cfecc600c19f6d80000000005a78804d71dc04fbb00000000008f37d048b9d804fbb00000000006e22c0896ca404fba80000000007deee0bc69ac04fbb00000000009967d108728404fbb0000000000f830a05a769c04fbb0000000000edf781cfe6b404fba80000000002c749f50e8cfcec24fbb000000000018bafa1731a7e013eec0be0be1380be0be13822bfb0e1b9e8a64010a33db2) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P07 : WideCovered band 8722919 9048221 := wide_block_sound band profiles_RelativeWidePack6815_P07 8722919 9048221 (wideData 16 0x2a7e6c126ae20019f6d8000000000aff2a028a60019f6e00000000005826b1ee28a40067db60000000003779ac4f8d7b0019f6e00000000006ead0e0af2e42067db600000000006b834901ce6c00067db80000000000a2a70a0fd6db40067db60000000000f48f1b81f37d2d0019f6e00000082001c358290b79280019f6d8208000000aaf58bb13bc3e942067db80000000006a0e700618b7d80067db6000000000368bf0562f630019f6d8000000001eea0d10d25b00067db60000000004eea780a3eb6f40067db8000000000071c21d01873ff30019f6d83803804e03803804e07dfda6c067bb9a64090d74d64) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P07 : WideCovered band 9048222 9373524 := wide_block_sound band profiles_RelativeWidePack6815_P07 9048222 9373524 (wideData 16 0x18c70071d00067db600000000076bd06dee0019f6e00000000010c641a3a00067db600000000043ec05afc0019f6e00000000014af80a7980067db6000000000679e02eef0019f6e00000000019bb4065b00067db6000000000777d1aec0067db8000000080063c380f2f40067db60000000c013392fc509bab230819f6e0000000000cc36d09a65ec0067db60000000004298204bc8710019f6d8000000001dc7d906ab2fc0067db6000000000069a2a901f72c290019f6e02080082005f2392d07bf69f42067db60e20e21380e20e2138239d75b19ee3b6e191a70832) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P07 : WideCovered band 9373525 9698826 := wide_block_sound band profiles_RelativeWidePack6815_P07 9373525 9698826 (wideData 16 0x11cf836fd80067db60000000004b4f0dc300019f6e00000000012d342aaa80067db600000000052fd0bd680019f6d80000000009bac36e980067db60000000001e4c0dc300019f6e00000000007a60372f80067db60000000002aac07be20019f6e00000000007f2c371980067db6000000000221e0dda40019f6e000000000089e437cb00067db60020000002b780aa760019f6d8000000200be38276f00067db600000000026bd0ea360019f6e00000000009be03b7b00067db60e60e41380e60e4138075c24d04e66b7e291f6bb20) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P07 : WideCovered band 9698827 10308768 := wide_block_sound band profiles_RelativeWidePack6815_P07 9698827 10308768 (wideData 16 0x648606f7e800afb6c00000000006cb28067938002bedb80000000001b2ec19aa6002bedb8000000000196df019b29800afb6e0000000003ade019be8800afb6c0000000005fc815876002bedb800000000109ac066da2002bedb8008000000183890fb68002bedb80000000014b3c06696c002bedb80000002001de2c03a36002bedb82000080002a2ac0fd7c002bedb830000c0002e67e0cb21002bedb80000000007aa0902e35cc00afb6c10400408033a9614e2d2e002bedb8200008200da6c27ae00067db60e60e61380e60e613807bbfeb04fef8b0292c66dec) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P07 : WideCovered band 10308769 10959373 := wide_block_sound band profiles_RelativeWidePack6815_P07 10308769 10959373 (wideData 16 0x48740a3aea002bedb0208008200192e801fff8800afb6e000000000065ff407ac2a002bedb800000000019bfb01e67f800afb6e00000000006bc240a0aac002bedb00000000001868d01d3f8800afb6e0000000000f1c028b0b000afb6e082002080135801dad9800afb6e000000000064eec0739f0002bedb800000000018b1c01a2a8000afb6e000000000069a60073d76002bedb80000000001b27801cfe9800afb6e0000000005b1e01a3ca800afb6c000000000169f01dadd000afb6e000000000223c01a65c800afb6e0ee0ee1380ee0ee1380a6a71905eb4926293df5dee) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P07 : WideCovered band 10959374 11853956 := wide_block_sound band profiles_RelativeWidePack6815_P07 10959374 11853956 (wideData 16 0x3a0b09b2488013eebc08200208012382c175ce8004fbae800000000069a9a02d6080013eebc0000000001f4fa00698f7004fbaf030c00c300283de60064da0f4013eebc08200208006bc6e843d2abc313eeba2080082000fbeac165b7ef020afb6e00000000006de3c0b0fb4002bedb80000000001d23d02fa5d000afb6e0000000001a6802d31c000afb6e0820020806a9d02c79f800afb6e00000000006afec0acdae002bedb800000000019f090286ef000afb6c00000000006db2c0adaae002bedb80000000001aa790287ba000afb6e0f20f21380f20f21380b39fda06db4976294fecba8) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P07 : WideCovered band 11853957 13155166 := wide_block_sound band profiles_RelativeWidePack6815_P07 11853957 13155166 (wideData 16 0x68a3ba02fa39e6004fbaf0208008201abb2f029f5bbc004fbae80000000019b36b01ea8a72004fbaf00000000016df5d01cf38ee004fbae8208008200fef3a01b63a68004fbaf0000000000fc39a018ac866004fbae8000000000eeedd0182d9f6004fbaf0000000000f97ce0183abb2004fbaf02080082006f3bf17e3ee0013eebc00000000027cfa8525a3c004fbae80000000009da2e12f6680013eebc00000000022cebc47dba8004fbae82080082003df780ecaff8013eebc0000000001e293c2fbbf8004fbae80000000007a3580aeb290013eebc0fe0fe1380fe0fe138131c27e0c96ccea296e2f8e4) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P07 : WideCovered band 13155167 13724445 := wide_block_sound band profiles_RelativeWidePack6815_P07 13155167 13724445 (wideData 7 0x820020807e0d357388b9084fbae830c00c300f876f07bf0dc013eebc000000000173beca87962ef7004fbae8208008200693dbbb172aa68c213eebc0820020800aeae984196ee38084fbae80000000019e7ff04da7e65004fbaf04c04c04e04c04c04e09a27a7c066de8d3c3999fcc38) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8519604 8722918 13724445 c0_RelativeWidePack6815_P07 (wide_covered_join band 8722919 9048221 13724445 c1_RelativeWidePack6815_P07 (wide_covered_join band 9048222 9373524 13724445 c2_RelativeWidePack6815_P07 (wide_covered_join band 9373525 9698826 13724445 c3_RelativeWidePack6815_P07 (wide_covered_join band 9698827 10308768 13724445 c4_RelativeWidePack6815_P07 (wide_covered_join band 10308769 10959373 13724445 c5_RelativeWidePack6815_P07 (wide_covered_join band 10959374 11853956 13724445 c6_RelativeWidePack6815_P07 (wide_covered_join band 11853957 13155166 13724445 c7_RelativeWidePack6815_P07 c8_RelativeWidePack6815_P07))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 11)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 11≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤65)
    (hT0 : 3081≤T) (hT1 : T≤3742) (hnu : 8519604≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤34751473937064351 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R042

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R043
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨11,66,3003,3315,33234960734882178⟩
private def profiles_RelativeWidePack6815_P07 : ℕ → Profile
  | 0 => ⟨25032,184,5079⟩
  | 1 => ⟨25120,182,5079⟩
  | 2 => ⟨25204,180,5079⟩
  | 3 => ⟨25234,177,5079⟩
  | 4 => ⟨25309,175,5079⟩
  | 5 => ⟨44518,250,10158⟩
  | 6 => ⟨26004,148,5079⟩
  | 7 => ⟨26253,139,5079⟩
  | 8 => ⟨26320,138,5079⟩
  | 9 => ⟨26312,136,5079⟩
  | 10 => ⟨26374,135,5079⟩
  | 11 => ⟨26434,134,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P07 : WideCovered band 8650675 8917532 := wide_block_sound band profiles_RelativeWidePack6815_P07 8650675 8917532 (wideData 16 0x1a29ca00a68e69c00688e00000000004e0fa7064da29c00688be082002080120cb9ec2e75fbd081a23800000000003eebb12ff4fc00688be0000000002b6874377e3c001a2380000000000bcfdd03c35b800688be0000000003728f82f4c33001a23800000000011caea019a9cb7001a22f8000000001b8a5c02fe0ae1001a23800000000001ffaf6c4e1b7cf030688be0000000004eaca4062abbf40521c020800820039639753f397e0948700000000000b7b781ebdbc01486e000000000076e7427d800521c00000000001dedd159b10148700be0be13a0be0be13a0f1bfcb16b3283c010c33f34) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P07 : WideCovered band 8917533 9245970 := wide_block_sound band profiles_RelativeWidePack6815_P07 8917533 9245970 (wideData 16 0x2080082002f73a6b72bef5081a23800000000005a63b098feb000688be0000000000f6fe41edaa5001a23800000000006d6e903c39f800688be000000000223ee4264cc00688e00000000002b4a7c1abc7b001a22f8000000000ce70f01ca4ffd001a22f82080082002b35bf50b78acdc20688be0000000000fd860123ce6001a23800000000003fa8c0fb6a001a22f80000000004877904bb2dc00688e0000000000129c742ee8f9001a22f80000000008c36905bef8800688e00000000001aa928060cf69400688be0000000000a6bf112fa3eac20688be0e20e213a0e20e213a0eba39a1f9ebc2e091871936) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P07 : WideCovered band 9245971 9574409 := wide_block_sound band profiles_RelativeWidePack6815_P07 9245971 9574409 (wideData 16 0xbff01b2a800688e0000000000367806a7e001a22f8000000000fcb02edb800688e0000000000429e04e32001a22f80000000012b240f8e800688e000000000053fb02c76001a22f80000000018a30061a800688e000000000072ff1ee400688be0000000805239078a8001a238000000000199fc174fc00688be0000000000618702a5cc00688e000000000006ce38437f400688be0000000c006fd2aa4e8f1de3081a2380000000000d9a7c09fb7a400688be0000000005befac1b3e70001a22f83983984e83983984e9cee4a12ffa9b4211d72d22) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P07 : WideCovered band 9574410 9923374 := wide_block_sound band profiles_RelativeWidePack6815_P07 9574410 9923374 (wideData 16 0x1040041001edcf9462dfc002c25f80000000008d2433be000688be000000000264b0ce7a001a23800000000009db0336d800688be0000000002b1e0dda6001a2380000000000bf68463a000688be000000000321d0ce3e001a22f8000000000ba30336f000688be000000000338336c000688e000000000026c335b800688be000000000170334b800688e0000000000166b54aac001a22f8000000001cd4da2a001a238000000000019f936b9000688be082002080163d0a8fe001a22f83983984e83983984e9a9ec804e6ed3e292a748f0) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P07 : WideCovered band 9923375 10580251 := wide_block_sound band profiles_RelativeWidePack6815_P07 9923375 10580251 (wideData 16 0x8200208033006c8ec002c25f80000000011c28063a2e002c25f800000000159a006eeea002c25f80000000014ee4062a6c002c25f000000000179e0061b32002c25f8000000001bb64066c7c002c25f8000000000ceec06a97e002c25f80000000001b397f8f000b097c000000000073e5ebe0002c25f8208008200683c068bf0002c25f800000000199b03e18800b097e00000000077b80ac20002c25f800000000019f6d17ffa002c25f80000000001be2801e2b002c25f80000000001ff390eff5002c25f83b03b04e83b03b04e988b4905c2b96c293825e38) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P07 : WideCovered band 10580252 11237128 := wide_block_sound band profiles_RelativeWidePack6815_P07 10580252 11237128 (wideData 16 0x16bec0abe70002c25f8000000000c8300acb36002c25f82080082001c02c6d9000b097e0000000004ab801f34b800b097c0000000004bdd01f2fc000b097e00000000057db02a2ec000b097e000000000534801f66a000b097e000000000577d01f75b800b097c0000000001aec429b28800b097e0820020801f8f01e66a000b097e00000000046ca01bfba800b097e0000000004a8d01bf1a800b097e000000000575a01ef78000b097e00000000053cb01c22c800b097e0000000005b5801c2ae800b097e0f00f013a0f00f013a0628f1f05fe4f26294a28df2) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P07 : WideCovered band 11237129 12263498 := wide_block_sound band profiles_RelativeWidePack6815_P07 11237129 12263498 (wideData 16 0x12cee442ac6600582be80000000003ebe80bc29b00160afc0820020805a180ec72f80160afc0000000000eaa38275f2200582bf00000000002f28b04beed80160afa0000000001228f41a8e7800582bf00000000004a71b02db88c0160afa000000000221ffc163e2500582bf0000000000bce9f02c26b83160afa2080082002278a1126d3df020b097e000000000665d02f658000b097e0820020800a5a43a22c800b097e000000000536c02b72c800b097e000000000535b02ae79800b097e000000000563f02ae1e000b097e0f40f413a0f40f413a06aa7df06fbdf30295c2bdac) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P07 : WideCovered band 12263499 13577252 := wide_block_sound band profiles_RelativeWidePack6815_P07 12263499 13577252 (wideData 16 0x28b1a381bbde2ac0160afa0820020800f2a38f449b6cfb08582bf02080082001b2fd2906aef6cc2160afc28a00a2804b4b211afe30f84160afc0000000004a2d340b782e800160afa000000000466d780b2e22800160afc0000000003bdea40a797ac00160afa0820020801fcffc06f9a6a00160afc00000000027e8b406eabcf80160afa000000000222aa8064b62a00160afc08200208017dbb4064f39d80160afc0000000001ae8ec7368ee00582bf00000000005ab8a16b67800160afa00000000017fff8664e6a00582bf02080082002860c12a2dc80160afa12012013a12012013a0b497890df60ce2297c70c30) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P07 : WideCovered band 13577253 13905690 := wide_block_sound band profiles_RelativeWidePack6815_P07 13577253 13905690 (wideData 4 0xca2380eeafac0160afa0820020804fbca5470f7708582bf0000000000bb3180cd25ac0160afa13413413a13413413a0bfd7b916c79bb651a876ba4) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8650675 8917532 13905690 c0_RelativeWidePack6815_P07 (wide_covered_join band 8917533 9245970 13905690 c1_RelativeWidePack6815_P07 (wide_covered_join band 9245971 9574409 13905690 c2_RelativeWidePack6815_P07 (wide_covered_join band 9574410 9923374 13905690 c3_RelativeWidePack6815_P07 (wide_covered_join band 9923375 10580251 13905690 c4_RelativeWidePack6815_P07 (wide_covered_join band 10580252 11237128 13905690 c5_RelativeWidePack6815_P07 (wide_covered_join band 11237129 12263498 13905690 c6_RelativeWidePack6815_P07 (wide_covered_join band 12263499 13577252 13905690 c7_RelativeWidePack6815_P07 c8_RelativeWidePack6815_P07))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 11)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 11≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤66)
    (hT0 : 3003≤T) (hT1 : T≤3315) (hnu : 8650675≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤33234960734882178 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R043

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R044
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨12,43,4299,4332,10715462655907075⟩
private def profiles_RelativeWidePack6815_P07 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨40268,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P07 : WideCovered band 5636041 9449929 := wide_block_sound band profiles_RelativeWidePack6815_P07 5636041 9449929 (wideData 16 0x6ef01ffdd000a1abe000000000071b0286ab000a1ae0000000000078802ab3a000a1abe00000000007bd02b32f000a1abe0000000000a0902be6d000a1abe0820020800a494296a9800a1abe000000000065a01aab9800a1abe00000000006eb01e6fc800a1abe000000000071901ea5a000a1abe000000000074d01ee6d000a1ae0000000000079a01f348000a1abe1450051400f0e3c1fcc759820a1abe2490092404200afc2e0848b5f830c00c3007b0d9f208896be829029000a40a4003b038000a1abea81a81a83b81a81a83b87c15de200eeb5e64) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P07 : WideCovered band 9449930 9918300 := wide_block_sound band profiles_RelativeWidePack6815_P07 9449930 9918300 (wideData 14 0xa0e03b36b000a1abe0000000000a2d03b7fc800a1abe0000000000a4d03bf6f800a1abe0820020803e50e5b2000286af80000000001b6c0a7e2a00286af80000000001d780b7af200286af80000000001de40b882c00286af80000000001e3c0b983200286b800000000001ebc0baae800286af80000000001d3c0a9de200286af800000000028240bddaa00286af820800820019b10b2f6600286af80000000001be80a792c00286af83883883b83883883b8486ec08e2ee2c1928ba9f0) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 5636041 9449929 9918300 c0_RelativeWidePack6815_P07 c1_RelativeWidePack6815_P07)
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 12)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 12≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤43)
    (hT0 : 4299≤T) (hT1 : T≤4332) (hnu : 5636041≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤10715462655907075 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R044

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R045
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨12,44,4211,4307,10533886751814008⟩
private def profiles_RelativeWidePack6815_P07 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨40518,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P07 : WideCovered band 5767112 9219520 := wide_block_sound band profiles_RelativeWidePack6815_P07 5767112 9219520 (wideData 16 0xf4b01a7fb800a28ee000000000131901e6fe000a28ee00000000013ba01ea5c800a28ee000000000132901ab7c000a28ee000000000179f01f6cc000a28ee000000000174e01ae1c800a28f00000000001ece028ae8000a28ee0000000001bb841b7da000a28ee0820020800a3941be0d000a28ee000000000122e1aa740028a3b80000000005ab406ba700028a3b89240249009c3aa07aefbf00828a3b8b2c02cb013c1a930084926f8000000000db0d866090c3bc8a28028a003801e00061877983983983c03983983c15f15ba000f926e60) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P07 : WideCovered band 9219521 9761074 := wide_block_sound band profiles_RelativeWidePack6815_P07 9219521 9761074 (wideData 16 0x4ae40a98ec0028a3b80000000004ea00b1ce00028a3b800000000059200b68be0028a3b80000000004ce80a6fb60028a3b80000000005c380b8db20028a3b8000000000586c0a98300028a3c00000000003de00bd9e00028a3b82080082002ef907acbc0028a3b80000000004ba80a5eec0028a3b80000000004af40a0cf00028a3b80000000004b7c07e97e0028a3b800000000058f40a98e60028a3b80000000004db0079afe0028a3b80000000005ee40ad8f80028a3c00000000005c7407cbb60028a3b83883883c03883883c0abfa908822bf8191d38fee) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P07 : WideCovered band 9761075 10099545 := wide_block_sound band profiles_RelativeWidePack6815_P07 9761075 10099545 (wideData 9 0x20800820066ae04a3adea004926f00000000005bf40e6d360028a3b80000000005ca40e78200028a3b80000000004fe00b79fe0028a3b80000000005e680e8aa20028a3b800000000059b40b89a80028a3b800000000069280eafac0028a3c00000000005ca80bac380028a3b83983983c03983983c0cbb0d09963f6c192d7adb2) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 5767112 9219520 10099545 c0_RelativeWidePack6815_P07 (wide_covered_join band 9219521 9761074 10099545 c1_RelativeWidePack6815_P07 c2_RelativeWidePack6815_P07))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 12)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 12≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤44)
    (hT0 : 4211≤T) (hT1 : T≤4307) (hnu : 5767112≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤10533886751814008 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R045

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R046
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨12,45,4126,4283,10754170668401988⟩
private def profiles_RelativeWidePack6815_P07 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨33072,8,10160⟩
  | 2 => ⟨40518,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P07 : WideCovered band 5898183 9116660 := wide_block_sound band profiles_RelativeWidePack6815_P07 5898183 9116660 (wideData 16 0x1f9901af6c000a2efe00000000027df01fe8a800a2efe000000000277d01b669000a2efe0000000002e5e01b74d000a2efe0000000000790a8bf00028bbf8208008200dee10688720028bc8000000000078e47228800a2efe000000000235801935c000a2efe000000000278c018a29000a2efe0000000002b7f169b60028bbf8000000000d8344a0a000a2efe0000000004ac901ae9d000a2efe0000000005a7908ce20028bbf830c00c300d9a6d0787fd600828bc8134c04d3003d600baa3c08186dfe40f20f20f20f20f20f2063f1596800fb77e3c) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P07 : WideCovered band 9116661 9664486 := wide_block_sound band profiles_RelativeWidePack6815_P07 9116661 9664486 (wideData 16 0x7eac0a8fac0028bbf80000000009af00bae320028bbf80000000008cb40abb280028bbf800000000098a00acea00028bbf82080082006d210b78fa0028bbf80000000006c6c079cf40028bc800000000006e64079c3e0028bbf800000000089f80a9e620028bbf80000000007c6807ae680028bbf8000000000883407bbac0028bbf80000000009cf40aac340028bbf80000000009eac0a3ef00028bbf8208008200d9fd07b9f00028bbf800000000069fc06befa0028bc800000000007e2c07bcba0028bbf83803803c83803803c91938e07db0a6e111bb0ee6) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P07 : WideCovered band 9664487 10280790 := wide_block_sound band profiles_RelativeWidePack6815_P07 9664487 10280790 (wideData 15 0x18f3e01f25c40125dfc0000000000a29340749b1004977f06180186003e3ca04974dae004977f0000000000bf70122f7e0028bbf820800820029250e0bbc0028bc800000000008a6c0b9b7c0028bbf80000000009cf40e9e760028bbf80000000008d200ba8a80028bbf80000000008eb80baca80028bbf8000000000ab200ed9340028bbf80000000009bb40bd8fe0028bbf82080082003bfd0bbf220028bbf800000000089ac0b6a680028bc800000000007b300a8e6e0028bbf83903903c83903903c9487be08e308b2112bfeeaa) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 5898183 9116660 10280790 c0_RelativeWidePack6815_P07 (wide_covered_join band 9116661 9664486 10280790 c1_RelativeWidePack6815_P07 c2_RelativeWidePack6815_P07))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 12)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 12≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤45)
    (hT0 : 4126≤T) (hT1 : T≤4283) (hnu : 5898183≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤10754170668401988 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R046

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R047
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨12,46,4045,4258,10869489292214083⟩
private def profiles_RelativeWidePack6815_P07 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨40768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P07 : WideCovered band 6029254 8799742 := wide_block_sound band profiles_RelativeWidePack6815_P07 6029254 8799742 (wideData 16 0x3fb91592c0028f4b80000000013c2c43ce000a3d2e00000000066590ad600028f4b800000000018b08109000a3d2e000000000075ab01aa8000a3d2e0000000000bad30360d400a3d2e1040041001addad531b740028f4b80000000004af8439d80061ea8000000000133b10fe400187aa00000000004f20465880061ea6000000000165f11b6000187aa00000000005c68475c80061ea61450051404acaf81a5aee882061ea80000000000ffa02b2f882127a3c1c70071c05a4337d0222ec7a0e40e40f40e40e40f4079914e3600fde8e38) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P07 : WideCovered band 8799743 9353840 := wide_block_sound band profiles_RelativeWidePack6815_P07 8799743 9353840 (wideData 16 0x2e3a01ea6b800a3d2e000000000327b01f79a000a3d2e0000000003aee02ab88800a3d2e0000000002e1f429269800a3d2e0820020800a7b01beec000a3d2e00000000026c801b21d800a3d2e0000000002a3c01affe000a3d2e0000000002e1e01b21f800a3d30000000000329901b2b9000a3d2e00000000037dc01b3ca000a3d2e000000000423f01b75e800a3d2e0000000004e7b01be3a800a3d2e0000000004f4941c6cd800a3d2e0820020802ae8419b4b000a3d2e0000000002f1c1abb40028f4b82f82f83d02f82f83d14ea0d078a3ca6190ee6d2c) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P07 : WideCovered band 9353841 9907938 := wide_block_sound band profiles_RelativeWidePack6815_P07 9353841 9907938 (wideData 16 0xce280e08660028f4b8000000000ca740b8ca60028f4b8000000000ce2c0b9f620028f4b8000000000dab80bbda60028f4b82080082007bb10af9f20028f4b80000000009fec0a6a380028f4b8000000000aa6c0a6d2a0028f4b8000000000ad6c0a79e00028f4c0000000000b92c0a88e80028f4b8000000000bdb80a9ae00028f4b8000000000cb6c0aafb60028f4b80000000017b42b64f800a3d2e0820020800b107cf2e0028f4b80000000009ae0078c220028f4b80000000009e7c078e6c0028f4b83883883d03883883d18abea07ebffb4191f60ef0) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P07 : WideCovered band 9907939 10462035 := wide_block_sound band profiles_RelativeWidePack6815_P07 9907939 10462035 (wideData 12 0xfdb8124ca80028f4b871c01c7005da3f438bfd6d0028f4b82080082013eb51228660049e8f00000000001ab8b1db40127a3c0c3000000066d31b18d7bbc0127a3c20800618077ed69139b68980127a3c00000000037d803afb9000a3d2e0000000003a8d03b3ed800a3d2e0000000006710eec7e0028f4b8208008200ace00b6afe0028f4b8000000000baa40b696e0028f4b83983983d03983983d1cdf0a09867a2a192fbb8b4) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6029254 8799742 10462035 c0_RelativeWidePack6815_P07 (wide_covered_join band 8799743 9353840 10462035 c1_RelativeWidePack6815_P07 (wide_covered_join band 9353841 9907938 10462035 c2_RelativeWidePack6815_P07 c3_RelativeWidePack6815_P07)))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 12)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 12≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤46)
    (hT0 : 4045≤T) (hT1 : T≤4258) (hnu : 6029254≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤10869489292214083 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R047
end MergedPart3
