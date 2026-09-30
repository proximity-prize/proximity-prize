import ProximityPrize.SubmissionLower.RelativeWideBlocks6815
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R042
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨11,65,3081,3742,34751473937064351⟩
private def profiles : ℕ → Profile
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
private theorem c0 : WideCovered band 8519604 8722918 := wide_block_sound band profiles 8519604 8722918 (wideData 16 0x130a3d918e2797e0c19f6d80000000016b25999ae4ac04fbb02080082010cb5bb76e19a8b444fbb00000000011a23f08be80019f6d8000000000edacf15b319c0067db800000000026c876b1cfecc600c19f6d80000000005a78804d71dc04fbb00000000008f37d048b9d804fbb00000000006e22c0896ca404fba80000000007deee0bc69ac04fbb00000000009967d108728404fbb0000000000f830a05a769c04fbb0000000000edf781cfe6b404fba80000000002c749f50e8cfcec24fbb000000000018bafa1731a7e013eec0be0be1380be0be13822bfb0e1b9e8a64010a33db2) (by decide +kernel)
private theorem c1 : WideCovered band 8722919 9048221 := wide_block_sound band profiles 8722919 9048221 (wideData 16 0x2a7e6c126ae20019f6d8000000000aff2a028a60019f6e00000000005826b1ee28a40067db60000000003779ac4f8d7b0019f6e00000000006ead0e0af2e42067db600000000006b834901ce6c00067db80000000000a2a70a0fd6db40067db60000000000f48f1b81f37d2d0019f6e00000082001c358290b79280019f6d8208000000aaf58bb13bc3e942067db80000000006a0e700618b7d80067db6000000000368bf0562f630019f6d8000000001eea0d10d25b00067db60000000004eea780a3eb6f40067db8000000000071c21d01873ff30019f6d83803804e03803804e07dfda6c067bb9a64090d74d64) (by decide +kernel)
private theorem c2 : WideCovered band 9048222 9373524 := wide_block_sound band profiles 9048222 9373524 (wideData 16 0x18c70071d00067db600000000076bd06dee0019f6e00000000010c641a3a00067db600000000043ec05afc0019f6e00000000014af80a7980067db6000000000679e02eef0019f6e00000000019bb4065b00067db6000000000777d1aec0067db8000000080063c380f2f40067db60000000c013392fc509bab230819f6e0000000000cc36d09a65ec0067db60000000004298204bc8710019f6d8000000001dc7d906ab2fc0067db6000000000069a2a901f72c290019f6e02080082005f2392d07bf69f42067db60e20e21380e20e2138239d75b19ee3b6e191a70832) (by decide +kernel)
private theorem c3 : WideCovered band 9373525 9698826 := wide_block_sound band profiles 9373525 9698826 (wideData 16 0x11cf836fd80067db60000000004b4f0dc300019f6e00000000012d342aaa80067db600000000052fd0bd680019f6d80000000009bac36e980067db60000000001e4c0dc300019f6e00000000007a60372f80067db60000000002aac07be20019f6e00000000007f2c371980067db6000000000221e0dda40019f6e000000000089e437cb00067db60020000002b780aa760019f6d8000000200be38276f00067db600000000026bd0ea360019f6e00000000009be03b7b00067db60e60e41380e60e4138075c24d04e66b7e291f6bb20) (by decide +kernel)
private theorem c4 : WideCovered band 9698827 10308768 := wide_block_sound band profiles 9698827 10308768 (wideData 16 0x648606f7e800afb6c00000000006cb28067938002bedb80000000001b2ec19aa6002bedb8000000000196df019b29800afb6e0000000003ade019be8800afb6c0000000005fc815876002bedb800000000109ac066da2002bedb8008000000183890fb68002bedb80000000014b3c06696c002bedb80000002001de2c03a36002bedb82000080002a2ac0fd7c002bedb830000c0002e67e0cb21002bedb80000000007aa0902e35cc00afb6c10400408033a9614e2d2e002bedb8200008200da6c27ae00067db60e60e61380e60e613807bbfeb04fef8b0292c66dec) (by decide +kernel)
private theorem c5 : WideCovered band 10308769 10959373 := wide_block_sound band profiles 10308769 10959373 (wideData 16 0x48740a3aea002bedb0208008200192e801fff8800afb6e000000000065ff407ac2a002bedb800000000019bfb01e67f800afb6e00000000006bc240a0aac002bedb00000000001868d01d3f8800afb6e0000000000f1c028b0b000afb6e082002080135801dad9800afb6e000000000064eec0739f0002bedb800000000018b1c01a2a8000afb6e000000000069a60073d76002bedb80000000001b27801cfe9800afb6e0000000005b1e01a3ca800afb6c000000000169f01dadd000afb6e000000000223c01a65c800afb6e0ee0ee1380ee0ee1380a6a71905eb4926293df5dee) (by decide +kernel)
private theorem c6 : WideCovered band 10959374 11853956 := wide_block_sound band profiles 10959374 11853956 (wideData 16 0x3a0b09b2488013eebc08200208012382c175ce8004fbae800000000069a9a02d6080013eebc0000000001f4fa00698f7004fbaf030c00c300283de60064da0f4013eebc08200208006bc6e843d2abc313eeba2080082000fbeac165b7ef020afb6e00000000006de3c0b0fb4002bedb80000000001d23d02fa5d000afb6e0000000001a6802d31c000afb6e0820020806a9d02c79f800afb6e00000000006afec0acdae002bedb800000000019f090286ef000afb6c00000000006db2c0adaae002bedb80000000001aa790287ba000afb6e0f20f21380f20f21380b39fda06db4976294fecba8) (by decide +kernel)
private theorem c7 : WideCovered band 11853957 13155166 := wide_block_sound band profiles 11853957 13155166 (wideData 16 0x68a3ba02fa39e6004fbaf0208008201abb2f029f5bbc004fbae80000000019b36b01ea8a72004fbaf00000000016df5d01cf38ee004fbae8208008200fef3a01b63a68004fbaf0000000000fc39a018ac866004fbae8000000000eeedd0182d9f6004fbaf0000000000f97ce0183abb2004fbaf02080082006f3bf17e3ee0013eebc00000000027cfa8525a3c004fbae80000000009da2e12f6680013eebc00000000022cebc47dba8004fbae82080082003df780ecaff8013eebc0000000001e293c2fbbf8004fbae80000000007a3580aeb290013eebc0fe0fe1380fe0fe138131c27e0c96ccea296e2f8e4) (by decide +kernel)
private theorem c8 : WideCovered band 13155167 13724445 := wide_block_sound band profiles 13155167 13724445 (wideData 7 0x820020807e0d357388b9084fbae830c00c300f876f07bf0dc013eebc000000000173beca87962ef7004fbae8208008200693dbbb172aa68c213eebc0820020800aeae984196ee38084fbae80000000019e7ff04da7e65004fbaf04c04c04e04c04c04e09a27a7c066de8d3c3999fcc38) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8519604 8722918 13724445 c0 (wide_covered_join band 8722919 9048221 13724445 c1 (wide_covered_join band 9048222 9373524 13724445 c2 (wide_covered_join band 9373525 9698826 13724445 c3 (wide_covered_join band 9698827 10308768 13724445 c4 (wide_covered_join band 10308769 10959373 13724445 c5 (wide_covered_join band 10959374 11853956 13724445 c6 (wide_covered_join band 11853957 13155166 13724445 c7 c8))))))))
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
private def profiles : ℕ → Profile
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
private theorem c0 : WideCovered band 8650675 8917532 := wide_block_sound band profiles 8650675 8917532 (wideData 16 0x1a29ca00a68e69c00688e00000000004e0fa7064da29c00688be082002080120cb9ec2e75fbd081a23800000000003eebb12ff4fc00688be0000000002b6874377e3c001a2380000000000bcfdd03c35b800688be0000000003728f82f4c33001a23800000000011caea019a9cb7001a22f8000000001b8a5c02fe0ae1001a23800000000001ffaf6c4e1b7cf030688be0000000004eaca4062abbf40521c020800820039639753f397e0948700000000000b7b781ebdbc01486e000000000076e7427d800521c00000000001dedd159b10148700be0be13a0be0be13a0f1bfcb16b3283c010c33f34) (by decide +kernel)
private theorem c1 : WideCovered band 8917533 9245970 := wide_block_sound band profiles 8917533 9245970 (wideData 16 0x2080082002f73a6b72bef5081a23800000000005a63b098feb000688be0000000000f6fe41edaa5001a23800000000006d6e903c39f800688be000000000223ee4264cc00688e00000000002b4a7c1abc7b001a22f8000000000ce70f01ca4ffd001a22f82080082002b35bf50b78acdc20688be0000000000fd860123ce6001a23800000000003fa8c0fb6a001a22f80000000004877904bb2dc00688e0000000000129c742ee8f9001a22f80000000008c36905bef8800688e00000000001aa928060cf69400688be0000000000a6bf112fa3eac20688be0e20e213a0e20e213a0eba39a1f9ebc2e091871936) (by decide +kernel)
private theorem c2 : WideCovered band 9245971 9574409 := wide_block_sound band profiles 9245971 9574409 (wideData 16 0xbff01b2a800688e0000000000367806a7e001a22f8000000000fcb02edb800688e0000000000429e04e32001a22f80000000012b240f8e800688e000000000053fb02c76001a22f80000000018a30061a800688e000000000072ff1ee400688be0000000805239078a8001a238000000000199fc174fc00688be0000000000618702a5cc00688e000000000006ce38437f400688be0000000c006fd2aa4e8f1de3081a2380000000000d9a7c09fb7a400688be0000000005befac1b3e70001a22f83983984e83983984e9cee4a12ffa9b4211d72d22) (by decide +kernel)
private theorem c3 : WideCovered band 9574410 9923374 := wide_block_sound band profiles 9574410 9923374 (wideData 16 0x1040041001edcf9462dfc002c25f80000000008d2433be000688be000000000264b0ce7a001a23800000000009db0336d800688be0000000002b1e0dda6001a2380000000000bf68463a000688be000000000321d0ce3e001a22f8000000000ba30336f000688be000000000338336c000688e000000000026c335b800688be000000000170334b800688e0000000000166b54aac001a22f8000000001cd4da2a001a238000000000019f936b9000688be082002080163d0a8fe001a22f83983984e83983984e9a9ec804e6ed3e292a748f0) (by decide +kernel)
private theorem c4 : WideCovered band 9923375 10580251 := wide_block_sound band profiles 9923375 10580251 (wideData 16 0x8200208033006c8ec002c25f80000000011c28063a2e002c25f800000000159a006eeea002c25f80000000014ee4062a6c002c25f000000000179e0061b32002c25f8000000001bb64066c7c002c25f8000000000ceec06a97e002c25f80000000001b397f8f000b097c000000000073e5ebe0002c25f8208008200683c068bf0002c25f800000000199b03e18800b097e00000000077b80ac20002c25f800000000019f6d17ffa002c25f80000000001be2801e2b002c25f80000000001ff390eff5002c25f83b03b04e83b03b04e988b4905c2b96c293825e38) (by decide +kernel)
private theorem c5 : WideCovered band 10580252 11237128 := wide_block_sound band profiles 10580252 11237128 (wideData 16 0x16bec0abe70002c25f8000000000c8300acb36002c25f82080082001c02c6d9000b097e0000000004ab801f34b800b097c0000000004bdd01f2fc000b097e00000000057db02a2ec000b097e000000000534801f66a000b097e000000000577d01f75b800b097c0000000001aec429b28800b097e0820020801f8f01e66a000b097e00000000046ca01bfba800b097e0000000004a8d01bf1a800b097e000000000575a01ef78000b097e00000000053cb01c22c800b097e0000000005b5801c2ae800b097e0f00f013a0f00f013a0628f1f05fe4f26294a28df2) (by decide +kernel)
private theorem c6 : WideCovered band 11237129 12263498 := wide_block_sound band profiles 11237129 12263498 (wideData 16 0x12cee442ac6600582be80000000003ebe80bc29b00160afc0820020805a180ec72f80160afc0000000000eaa38275f2200582bf00000000002f28b04beed80160afa0000000001228f41a8e7800582bf00000000004a71b02db88c0160afa000000000221ffc163e2500582bf0000000000bce9f02c26b83160afa2080082002278a1126d3df020b097e000000000665d02f658000b097e0820020800a5a43a22c800b097e000000000536c02b72c800b097e000000000535b02ae79800b097e000000000563f02ae1e000b097e0f40f413a0f40f413a06aa7df06fbdf30295c2bdac) (by decide +kernel)
private theorem c7 : WideCovered band 12263499 13577252 := wide_block_sound band profiles 12263499 13577252 (wideData 16 0x28b1a381bbde2ac0160afa0820020800f2a38f449b6cfb08582bf02080082001b2fd2906aef6cc2160afc28a00a2804b4b211afe30f84160afc0000000004a2d340b782e800160afa000000000466d780b2e22800160afc0000000003bdea40a797ac00160afa0820020801fcffc06f9a6a00160afc00000000027e8b406eabcf80160afa000000000222aa8064b62a00160afc08200208017dbb4064f39d80160afc0000000001ae8ec7368ee00582bf00000000005ab8a16b67800160afa00000000017fff8664e6a00582bf02080082002860c12a2dc80160afa12012013a12012013a0b497890df60ce2297c70c30) (by decide +kernel)
private theorem c8 : WideCovered band 13577253 13905690 := wide_block_sound band profiles 13577253 13905690 (wideData 4 0xca2380eeafac0160afa0820020804fbca5470f7708582bf0000000000bb3180cd25ac0160afa13413413a13413413a0bfd7b916c79bb651a876ba4) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8650675 8917532 13905690 c0 (wide_covered_join band 8917533 9245970 13905690 c1 (wide_covered_join band 9245971 9574409 13905690 c2 (wide_covered_join band 9574410 9923374 13905690 c3 (wide_covered_join band 9923375 10580251 13905690 c4 (wide_covered_join band 10580252 11237128 13905690 c5 (wide_covered_join band 11237129 12263498 13905690 c6 (wide_covered_join band 12263499 13577252 13905690 c7 c8))))))))
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
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨40268,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 5636041 9449929 := wide_block_sound band profiles 5636041 9449929 (wideData 16 0x6ef01ffdd000a1abe000000000071b0286ab000a1ae0000000000078802ab3a000a1abe00000000007bd02b32f000a1abe0000000000a0902be6d000a1abe0820020800a494296a9800a1abe000000000065a01aab9800a1abe00000000006eb01e6fc800a1abe000000000071901ea5a000a1abe000000000074d01ee6d000a1ae0000000000079a01f348000a1abe1450051400f0e3c1fcc759820a1abe2490092404200afc2e0848b5f830c00c3007b0d9f208896be829029000a40a4003b038000a1abea81a81a83b81a81a83b87c15de200eeb5e64) (by decide +kernel)
private theorem c1 : WideCovered band 9449930 9918300 := wide_block_sound band profiles 9449930 9918300 (wideData 14 0xa0e03b36b000a1abe0000000000a2d03b7fc800a1abe0000000000a4d03bf6f800a1abe0820020803e50e5b2000286af80000000001b6c0a7e2a00286af80000000001d780b7af200286af80000000001de40b882c00286af80000000001e3c0b983200286b800000000001ebc0baae800286af80000000001d3c0a9de200286af800000000028240bddaa00286af820800820019b10b2f6600286af80000000001be80a792c00286af83883883b83883883b8486ec08e2ee2c1928ba9f0) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 5636041 9449929 9918300 c0 c1)
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
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨40518,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 5767112 9219520 := wide_block_sound band profiles 5767112 9219520 (wideData 16 0xf4b01a7fb800a28ee000000000131901e6fe000a28ee00000000013ba01ea5c800a28ee000000000132901ab7c000a28ee000000000179f01f6cc000a28ee000000000174e01ae1c800a28f00000000001ece028ae8000a28ee0000000001bb841b7da000a28ee0820020800a3941be0d000a28ee000000000122e1aa740028a3b80000000005ab406ba700028a3b89240249009c3aa07aefbf00828a3b8b2c02cb013c1a930084926f8000000000db0d866090c3bc8a28028a003801e00061877983983983c03983983c15f15ba000f926e60) (by decide +kernel)
private theorem c1 : WideCovered band 9219521 9761074 := wide_block_sound band profiles 9219521 9761074 (wideData 16 0x4ae40a98ec0028a3b80000000004ea00b1ce00028a3b800000000059200b68be0028a3b80000000004ce80a6fb60028a3b80000000005c380b8db20028a3b8000000000586c0a98300028a3c00000000003de00bd9e00028a3b82080082002ef907acbc0028a3b80000000004ba80a5eec0028a3b80000000004af40a0cf00028a3b80000000004b7c07e97e0028a3b800000000058f40a98e60028a3b80000000004db0079afe0028a3b80000000005ee40ad8f80028a3c00000000005c7407cbb60028a3b83883883c03883883c0abfa908822bf8191d38fee) (by decide +kernel)
private theorem c2 : WideCovered band 9761075 10099545 := wide_block_sound band profiles 9761075 10099545 (wideData 9 0x20800820066ae04a3adea004926f00000000005bf40e6d360028a3b80000000005ca40e78200028a3b80000000004fe00b79fe0028a3b80000000005e680e8aa20028a3b800000000059b40b89a80028a3b800000000069280eafac0028a3c00000000005ca80bac380028a3b83983983c03983983c0cbb0d09963f6c192d7adb2) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 5767112 9219520 10099545 c0 (wide_covered_join band 9219521 9761074 10099545 c1 c2))
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
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨33072,8,10160⟩
  | 2 => ⟨40518,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 5898183 9116660 := wide_block_sound band profiles 5898183 9116660 (wideData 16 0x1f9901af6c000a2efe00000000027df01fe8a800a2efe000000000277d01b669000a2efe0000000002e5e01b74d000a2efe0000000000790a8bf00028bbf8208008200dee10688720028bc8000000000078e47228800a2efe000000000235801935c000a2efe000000000278c018a29000a2efe0000000002b7f169b60028bbf8000000000d8344a0a000a2efe0000000004ac901ae9d000a2efe0000000005a7908ce20028bbf830c00c300d9a6d0787fd600828bc8134c04d3003d600baa3c08186dfe40f20f20f20f20f20f2063f1596800fb77e3c) (by decide +kernel)
private theorem c1 : WideCovered band 9116661 9664486 := wide_block_sound band profiles 9116661 9664486 (wideData 16 0x7eac0a8fac0028bbf80000000009af00bae320028bbf80000000008cb40abb280028bbf800000000098a00acea00028bbf82080082006d210b78fa0028bbf80000000006c6c079cf40028bc800000000006e64079c3e0028bbf800000000089f80a9e620028bbf80000000007c6807ae680028bbf8000000000883407bbac0028bbf80000000009cf40aac340028bbf80000000009eac0a3ef00028bbf8208008200d9fd07b9f00028bbf800000000069fc06befa0028bc800000000007e2c07bcba0028bbf83803803c83803803c91938e07db0a6e111bb0ee6) (by decide +kernel)
private theorem c2 : WideCovered band 9664487 10280790 := wide_block_sound band profiles 9664487 10280790 (wideData 15 0x18f3e01f25c40125dfc0000000000a29340749b1004977f06180186003e3ca04974dae004977f0000000000bf70122f7e0028bbf820800820029250e0bbc0028bc800000000008a6c0b9b7c0028bbf80000000009cf40e9e760028bbf80000000008d200ba8a80028bbf80000000008eb80baca80028bbf8000000000ab200ed9340028bbf80000000009bb40bd8fe0028bbf82080082003bfd0bbf220028bbf800000000089ac0b6a680028bc800000000007b300a8e6e0028bbf83903903c83903903c9487be08e308b2112bfeeaa) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 5898183 9116660 10280790 c0 (wide_covered_join band 9116661 9664486 10280790 c1 c2))
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
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨40768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 6029254 8799742 := wide_block_sound band profiles 6029254 8799742 (wideData 16 0x3fb91592c0028f4b80000000013c2c43ce000a3d2e00000000066590ad600028f4b800000000018b08109000a3d2e000000000075ab01aa8000a3d2e0000000000bad30360d400a3d2e1040041001addad531b740028f4b80000000004af8439d80061ea8000000000133b10fe400187aa00000000004f20465880061ea6000000000165f11b6000187aa00000000005c68475c80061ea61450051404acaf81a5aee882061ea80000000000ffa02b2f882127a3c1c70071c05a4337d0222ec7a0e40e40f40e40e40f4079914e3600fde8e38) (by decide +kernel)
private theorem c1 : WideCovered band 8799743 9353840 := wide_block_sound band profiles 8799743 9353840 (wideData 16 0x2e3a01ea6b800a3d2e000000000327b01f79a000a3d2e0000000003aee02ab88800a3d2e0000000002e1f429269800a3d2e0820020800a7b01beec000a3d2e00000000026c801b21d800a3d2e0000000002a3c01affe000a3d2e0000000002e1e01b21f800a3d30000000000329901b2b9000a3d2e00000000037dc01b3ca000a3d2e000000000423f01b75e800a3d2e0000000004e7b01be3a800a3d2e0000000004f4941c6cd800a3d2e0820020802ae8419b4b000a3d2e0000000002f1c1abb40028f4b82f82f83d02f82f83d14ea0d078a3ca6190ee6d2c) (by decide +kernel)
private theorem c2 : WideCovered band 9353841 9907938 := wide_block_sound band profiles 9353841 9907938 (wideData 16 0xce280e08660028f4b8000000000ca740b8ca60028f4b8000000000ce2c0b9f620028f4b8000000000dab80bbda60028f4b82080082007bb10af9f20028f4b80000000009fec0a6a380028f4b8000000000aa6c0a6d2a0028f4b8000000000ad6c0a79e00028f4c0000000000b92c0a88e80028f4b8000000000bdb80a9ae00028f4b8000000000cb6c0aafb60028f4b80000000017b42b64f800a3d2e0820020800b107cf2e0028f4b80000000009ae0078c220028f4b80000000009e7c078e6c0028f4b83883883d03883883d18abea07ebffb4191f60ef0) (by decide +kernel)
private theorem c3 : WideCovered band 9907939 10462035 := wide_block_sound band profiles 9907939 10462035 (wideData 12 0xfdb8124ca80028f4b871c01c7005da3f438bfd6d0028f4b82080082013eb51228660049e8f00000000001ab8b1db40127a3c0c3000000066d31b18d7bbc0127a3c20800618077ed69139b68980127a3c00000000037d803afb9000a3d2e0000000003a8d03b3ed800a3d2e0000000006710eec7e0028f4b8208008200ace00b6afe0028f4b8000000000baa40b696e0028f4b83983983d03983983d1cdf0a09867a2a192fbb8b4) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6029254 8799742 10462035 c0 (wide_covered_join band 8799743 9353840 10462035 c1 (wide_covered_join band 9353841 9907938 10462035 c2 c3)))
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
