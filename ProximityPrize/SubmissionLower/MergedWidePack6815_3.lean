import ProximityPrize.SubmissionLower.RelativeWideBlocks6815
set_option Elab.async false
section MergedPart0
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R072
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨13,42,4152,4261,10303233022929419⟩
private def profiles_RelativeWidePack6815_P12 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨33072,8,10160⟩
  | 4 => ⟨24799,165,5079⟩
  | 5 => ⟨24860,163,5079⟩
  | 6 => ⟨24970,162,5079⟩
  | 7 => ⟨24917,161,5079⟩
  | 8 => ⟨40018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P12 : WideCovered band 5504969 8832207 := wide_block_sound band profiles_RelativeWidePack6815_P12 5504969 8832207 (wideData 16 0x3fde05d77001875c00000000013c205afd40061d6e0000000001fe8109a0bc2061d700000000004eff0ee77c42061d6e000000000074fe007dd2f001875c00000000002d6ea029e6c00061d6e00000000012fbf81b387d001875c000000000068bbfc396d840061d6e0820020801f1cef23deb3081875c000000000108280a4aa4001875b871c01c700efe2c0bc6e8f8081875c09240249001ae4073ebe0828eaf830c00c3015b19f700849b5f8000000000eb0cf76090eb7c90400410002d02900061d6f982f82f83b82f82f83b98e159b000edb5e64) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P12 : WideCovered band 8832208 9297676 := wide_block_sound band profiles_RelativeWidePack6815_P12 8832208 9297676 (wideData 16 0x2080082017b210e3f3a0028eaf80000000007ce807dfa60028eaf80000000008af807be6e0028eaf80000000007d604e6c000a3abe0000000002b7a01ca2b800a3abe00000000033ac01b618000a3ae0000000000421a0197a9000a3abe000000000520a04c6d0028eaf8000000001ce6006cfff0028eaf80000000001c70f01eeecc00a3ae00000000000a6f380669b8e420a3abe0000000000e8afc069bea001875b80000000001f71a9196a001875c00000082007f75a41eb7cc0061d6e0820000000e487337eb7c001875c03803803b83803803b8d923d0a960ab0390f248ae) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P12 : WideCovered band 9297677 9849342 := wide_block_sound band profiles_RelativeWidePack6815_P12 9297677 9849342 (wideData 16 0x8c700ffea80028eaf80000000008e301208620028eaf80000000007ca40e2a7a0028eaf80000000009b24120efc0028eaf80000000009ee0122db40028eaf8000000000aba4125cbe0028eb80000000000acb80fcb300028eaf8208008200aefd0bfaac0028eaf80000000007c200bfaf20028eaf80000000007ef00bfb220028eaf80000000008aa80bfe3e0028eaf80000000007ab807fce40028eaf80000000009ce00bffec0028eaf8000000000acf80e28bc0028eb80000000000c8240e5a780028eaf83903903b83903903b8e966f09dbcb76411e72ef6) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P12 : WideCovered band 9849343 9918300 := wide_block_sound band profiles_RelativeWidePack6815_P12 9849343 9918300 (wideData 2 0xa8ac129f3e0028eaf83a03a03b83a03a03b91d7f90bb74a7e412ee8aba) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 5504969 8832207 9918300 c0_RelativeWidePack6815_P12 (wide_covered_join band 8832208 9297676 9918300 c1_RelativeWidePack6815_P12 (wide_covered_join band 9297677 9849342 9918300 c2_RelativeWidePack6815_P12 c3_RelativeWidePack6815_P12)))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 13)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 13≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤42)
    (hT0 : 4152≤T) (hT1 : T≤4261) (hnu : 5504969≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤10303233022929419 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R072

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R073
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨13,43,4065,4236,39514795961645534⟩
private def profiles_RelativeWidePack6815_P12 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨40268,250,10158⟩
  | 4 => ⟨24734,167,5079⟩
  | 5 => ⟨24799,165,5079⟩
  | 6 => ⟨24860,163,5079⟩
  | 7 => ⟨24917,161,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P12 : WideCovered band 5636040 8669829 := wide_block_sound band profiles_RelativeWidePack6815_P12 5636040 8669829 (wideData 16 0x66fc018f4c800628760000000007a1819e2c0018a1e0000000000192db0babc0018a1d80000000001b7ca098330018a1e00000000001f35d01a32a400628760000000007fc9018ffea10818a1e00000000004d68e1ebfd0018a1d800000000089a0b03fe09c00628780000000002aeaa3361eeb0018a1d820800820018a9ec5ee28e20818a1e0000000000db241a7e0006287600000000046bb19a6a0018a1e030c00c300ec3cb079bbeec0818a1e000000820028e00739640818a1e134c0555001f28066a700818a1de60f00f00f00f00f00f0067814f7200f826e60) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P12 : WideCovered band 8669830 8983669 := wide_block_sound band profiles_RelativeWidePack6815_P12 8669830 8983669 (wideData 16 0xb7de407cae5002923b80000000003a67c01ce6f65242923b80000000006937d03f31d800628760000000000f6def169ef90018a1e00000082008cf3a41da8a000628760820000001b0e7b4ed82d0818a1e0000000001dc3c0a9c700018a1d800000000018be9029e3a00062878000000000064ef8062c3f0018a1d80000000001d7c801d2db800628780000000000a7f2c06afae0018a1d80000000003828e04cb8cc00628780000000001638b8073b7d0018a1e00000000006975f858f49c00628780820020805e1b7b131d670818a1d82f82f83c02f82f83c18deab0bc29cfe290ca7aa2) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P12 : WideCovered band 8983670 9541607 := wide_block_sound band profiles_RelativeWidePack6815_P12 8983670 9541607 (wideData 16 0xab600a3ca0002923b8000000000d9e00becfa002923b8000000000bef80a18ec002923b8000000000fb640e0baa002923b8000000000ebb007faf6002923b80000000013a780e4fea002923b80000000013b2407ee7e002923b8000000001eded0eef26002923c02080082004b7c065eb8002923b8000000000ddac07de6c002923b8000000000cf2062aa800a48ee00000000047ca01de59800a48ee0000000004e1c0ffe6002923b8000000001aa600608b8002923b800000000018a7a019e6002923b83883883c03883883c11fe3908f74ebe1919aeaba) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P12 : WideCovered band 9541608 10099545 := wide_block_sound band profiles_RelativeWidePack6815_P12 9541608 10099545 (wideData 16 0xdd28123cb0002923b8000000001092413fd2e002923b8000000000e928122d6e002923b80000000010f70161b6e002923b8000000000f828123da0002923b800000000129bc1668b2002923b82080082008a350fbf26002923b8000000000da680fbcf6002923c0000000000bc740e19bc002923b8000000000e8ec0fcb60002923b8000000000cb780e0dbc002923b8000000000fb780ffae8002923b8000000000df680e28ba002923b80000000011cb0125bb0002923b82080082010cf90e49f0002923b83903903c03903903c18d38909f2dabc192a3087e) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 5636040 8669829 10099545 c0_RelativeWidePack6815_P12 (wide_covered_join band 8669830 8983669 10099545 c1_RelativeWidePack6815_P12 (wide_covered_join band 8983670 9541607 10099545 c2_RelativeWidePack6815_P12 c3_RelativeWidePack6815_P12)))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 13)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 13≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤43)
    (hT0 : 4065≤T) (hT1 : T≤4236) (hnu : 5636040≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤39514795961645534 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R073

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R074
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨13,44,3981,4211,20393197249711410⟩
private def profiles_RelativeWidePack6815_P12 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨24515,173,5079⟩
  | 4 => ⟨40518,250,10158⟩
  | 5 => ⟨24734,167,5079⟩
  | 6 => ⟨24799,165,5079⟩
  | 7 => ⟨24860,163,5079⟩
  | 8 => ⟨24917,161,5079⟩
  | 9 => ⟨25019,157,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P12 : WideCovered band 5767111 8464740 := wide_block_sound band profiles_RelativeWidePack6815_P12 5767111 8464740 (wideData 16 0x1ab3c1fdc00062ba000000000006286c477880062b7e000000000069f602eccc0062ba000000208006fb2032fd80062b7e0000000002adf0a8680018ae800000000003939b01c6dec0062b7e0000000000b1f7c6f7ac0062ba00000030001b5a280be9f10018ae802080080001b70b3923ecade42062ba000000000006d868672900062b7e000000000074934227a40062ba00000000000b192c169bb80018adf85140145001a75c603fb869a82062ba0000000000128902af7b02129dfc1c70071c05f4333d82233bfa0e40e40f20e40e40f207ce14c3a00fa77e3c) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P12 : WideCovered band 8464741 8746845 := wide_block_sound band profiles_RelativeWidePack6815_P12 8464741 8746845 (wideData 16 0x5cf8903d28dc0062ba00000020800f4b31438ca70818adf80000000002afc842cf3d80062ba00000000000adc750ad8640018adf82080000009c63b47be9d80062ba00000000000679e0060be20018adf80000000001b31b0b8f10018ae800000000001df2c019aadc0062ba000000000006187906cef6e42062ba0000000000120cf40f1db20018adf80000000005be0e04b349c0062ba0000000000274da006bdae0018adf800000000019a58d1ea3a40062ba00820020802a38f31a5efec02062b7e0000000004bfc13d260018ae802f02f03c82f02f03c94825c07879e6e210977926) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P12 : WideCovered band 8746846 9117107 := wide_block_sound band profiles_RelativeWidePack6815_P12 8746846 9117107 (wideData 16 0x1ba2c2a5d000a4efe00000000006886006e82800293bf80000000001c75817db700293bf80000000002b2ad029babc00a4efe0000000001fc941f3b8b724293bf80000000004930901da1b80062b7e0000000001abcb806be260018ae800000000009c23c888f09c0062ba00000000006e4b251e7ca50018ae802080082003ba1ac2f238c2062b7e000000000063f20073c360018ae800000000001aa5c01b66b80062b7e00000000007383806586a0018ae800000000001eafe01c70a40062b7e0000000000b0e64071b7f0018ae803803803c83803803c978aff0b826872390dbe8f8) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P12 : WideCovered band 9117108 9681317 := wide_block_sound band profiles_RelativeWidePack6815_P12 9117108 9681317 (wideData 16 0xfea5d0692dfc00a4efe1040041004e38b517a964a8a0a4efe000000000270b439b0f800a4efe08200208006aa02ae9f800a4efe0000000003ac9028f8d000a4efe0000000004a5b02f7a8000a4efe000000000434b028e09800a4f200000000004a6e0287ac000a4efe00000000052b90283ac000a4efe0000000006e1f039758800a4efe0000000006fad028eb8000a4efe0000000001f88428f2f800a4efe0820020807f6e41f33e000a4efe0000000004ef801ff99800a4efe0000000004bbf1db6600293c803883883c83883883c9bb28a08d37c2a211bb3de4) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P12 : WideCovered band 9681318 10245527 := wide_block_sound band profiles_RelativeWidePack6815_P12 9681318 10245527 (wideData 16 0x5bef059308000a4efe0000000005eeb0593cf000a4efe0000000006f4d069e29000a4efe082002080174a44be69800a4efe0000000004a1e03fa2c000a4efe0000000004aaf03f6cd000a4efe000000000578a04e3eb000a4f200000000004ebc03fa8f800a4efe145005140228b71166b62bcb0a4efe0820020800feba527fc2400293bf80000000001e35b069a0f800a4efe00000000007edbc13ca7000293bf80000000002ffbd0b9248800a4efe0000000000beb7407fe7a00293bf800000000048f4901e71d400a4f200ea0ea0f20ea0ea0f2063839b0eef5c66492c61da8) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P12 : WideCovered band 10245528 10280790 := wide_block_sound band profiles_RelativeWidePack6815_P12 10245528 10280790 (wideData 1 0xea0ea0f20ea0ea0f2069ef990c82bdf0213cefd6c) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 5767111 8464740 10280790 c0_RelativeWidePack6815_P12 (wide_covered_join band 8464741 8746845 10280790 c1_RelativeWidePack6815_P12 (wide_covered_join band 8746846 9117107 10280790 c2_RelativeWidePack6815_P12 (wide_covered_join band 9117108 9681317 10280790 c3_RelativeWidePack6815_P12 (wide_covered_join band 9681318 10245527 10280790 c4_RelativeWidePack6815_P12 c5_RelativeWidePack6815_P12)))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 13)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 13≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤44)
    (hT0 : 3981≤T) (hT1 : T≤4211) (hnu : 5767111≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤20393197249711410 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R074

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R075
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨13,45,3901,4186,30990128545803256⟩
private def profiles_RelativeWidePack6815_P12 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨24592,171,5079⟩
  | 4 => ⟨24640,172,5079⟩
  | 5 => ⟨24394,178,5079⟩
  | 6 => ⟨24434,175,5079⟩
  | 7 => ⟨24562,174,5079⟩
  | 8 => ⟨24515,173,5079⟩
  | 9 => ⟨40518,250,10158⟩
  | 10 => ⟨24734,167,5079⟩
  | 11 => ⟨24850,166,5079⟩
  | 12 => ⟨24799,165,5079⟩
  | 13 => ⟨24860,163,5079⟩
  | 14 => ⟨24917,161,5079⟩
  | 15 => ⟨25019,157,5079⟩
  | 16 => ⟨25064,155,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P12 : WideCovered band 5898182 8162281 := wide_block_sound band profiles_RelativeWidePack6815_P12 5898182 8162281 (wideData 16 0x20800e1d6d4afb7fd84062ea80000000002eccb416bdf3011b620000000001a2ebd131aa6011b64000000000679b753acb3e011b640820000002b1af1372a3d0d1b640000000000bbbbc4e0b72091b6200000000067d90186eb8046d9000000000179783b5ec046d90000000001efe0738d8046d90000000001cf306a8f4046d8830c00c3001924ab42bfc32d0246d900000000003c60071ee00818baa00000000002d68065b28088db1e1b6c06db005f0194046d8f2072072001d01d0013407a0018ba9e40a20a20f40a00a00f40a081497200db74ab2) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P12 : WideCovered band 8162282 8447522 := wide_block_sound band profiles_RelativeWidePack6815_P12 8162282 8447522 (wideData 16 0x69cac7700018baa00000000001da2d04bb30018ba980000000002a77f0cdbb0018baa00000000003aeb81b83b0018ba980000002004a2ec01da6ec0062ea80000000c0168cb223b9effcc062ea60000020801628f10668fdccb062ea808200000007f829bc2bf48211018ba98000000000ffbef03dbdabc1418baa0000000000afea843d23a2b1018ba98000000000ff66e03d32de81418baa0000000000682d06696ac42062ea600000000006bd790a6db4a42062ea80000000001e6b24575b610018baa00000000011d2d2268e2ec2062ea80ba0ba0f40ba0ba0f406ef26c1c8f6e2628fce8e38) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P12 : WideCovered band 8447523 8732763 := wide_block_sound band profiles_RelativeWidePack6815_P12 8447523 8732763 (wideData 16 0x82003f21d15ae2dc2062ea80000000002e0e241349a10018ba98000000000d8f3c49c34e00062ea808200000073787d0669eb944062ea600000000007dc380e4ee20018baa00000000005939b1ca7df83062ea6000000000465c5af2ab42062ea80000000000f0e340a3c320018ba980000000004e2be01d26b80062ea80000000001af9301e4a350018ba98000000000bc67d03ae7ac0062ea800000000007f9322a9e370018ba98208008200eea38c6935dfe0818baa00000000016e7c261b80062ea80000000006e5e079360018baa02f02f03d02f02f03d18834a06fb2db6490935f2a) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P12 : WideCovered band 8732764 9071487 := wide_block_sound band profiles_RelativeWidePack6815_P12 8732764 9071487 (wideData 16 0x71dec2e19400a5d300000000000a79a406cdb7002974b80000000002c24841f6f9f12c2974b80000000003a3c8178e20018ba980000000004c6c9039bc0018baa00000000006ee0f01831e40062ea60000000002f7ab80eadb30018baa00000000011a34ac9e3aac0062ea60820020804a19ff5a60818baa00000000001a64c1bfa40018ba980000000001c27a10e3a0018baa00000000001ea6d01eaa0018ba980000000002a39e13ff50018baa00000000003aa1c02a2ec00062ea8000000000125ef00aad210018baa03803803d03803803d18fbfd0aef5bf0690da2ffc) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P12 : WideCovered band 9071488 9641969 := wide_block_sound band profiles_RelativeWidePack6815_P12 9071488 9641969 (wideData 16 0x6bde039baa000a5d300000000003ee803a7dc000a5d2e0820020805f4842f608000a5d2e0000000004bdf029e6c800a5d2e000000000526f029aad000a5d2e00000000057c9029728800a5d2e000000000622c02939f800a5d2e0000000006e2802928c800a5d2e0000000007e7b029239800a5d300000000000659b00a4974002974b8000000001b9e40a4e36002974b80000000001a7af429af9000a5d2e082002080365e41d35f000a5d2e00000000066ad1cf3e002974b8000000001e9b852fc800a5d2e0e20e20f40e20e20f4060f2ed08c25fe2491afbb2c) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P12 : WideCovered band 9641970 10212450 := wide_block_sound band profiles_RelativeWidePack6815_P12 9641970 10212450 (wideData 16 0xfef743bf9ee002974b80000000001b6d90faf1e000a5d2e0820020800bac6d3f0c7c002974b80000000002960e07d76d800a5d2e0000000000aafac1bf920002974b80000000002d36806962d800a5d2e0000000000e4e28162b32002974b8000000000483ec03bbac000a5d2e0000000001b6d7c2f3e2a002974c00000000009dfa817a3b002974b80000000015f78a0bdb7b400a5d2e08200208006def7a5bf719c20a5d2e0000000000e8b60124d31002974b80000000005ee6d1ed76002974b80000000009da9b05ce9c400a5d2e0ea0ea0f40ea0ea0f4061bf190f839ae8792bb5cf0) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P12 : WideCovered band 10212451 10462035 := wide_block_sound band profiles_RelativeWidePack6815_P12 10212451 10462035 (wideData 7 0x64fb01bdce0002974b8000000000196eb06f7ab800a5d2e08200208007ee05ee8b000a5d2e000000000738905ae2b000a5d2e1450051403f2875164f6abcf0a5d2e0000000000e9de43e7b3c002974b83b83b83d03b83b83d02867fb0435bb7a01813c6feb2) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 5898182 8162281 10462035 c0_RelativeWidePack6815_P12 (wide_covered_join band 8162282 8447522 10462035 c1_RelativeWidePack6815_P12 (wide_covered_join band 8447523 8732763 10462035 c2_RelativeWidePack6815_P12 (wide_covered_join band 8732764 9071487 10462035 c3_RelativeWidePack6815_P12 (wide_covered_join band 9071488 9641969 10462035 c4_RelativeWidePack6815_P12 (wide_covered_join band 9641970 10212450 10462035 c5_RelativeWidePack6815_P12 c6_RelativeWidePack6815_P12))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 13)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 13≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤45)
    (hT0 : 3901≤T) (hT1 : T≤4186) (hnu : 5898182≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤30990128545803256 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R075

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R076
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨13,46,3823,4160,33078420730379481⟩
private def profiles_RelativeWidePack6815_P12 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨33072,8,10160⟩
  | 4 => ⟨24394,178,5079⟩
  | 5 => ⟨24434,175,5079⟩
  | 6 => ⟨24515,173,5079⟩
  | 7 => ⟨24640,172,5079⟩
  | 8 => ⟨24592,171,5079⟩
  | 9 => ⟨24304,180,5079⟩
  | 10 => ⟨40768,250,10158⟩
  | 11 => ⟨24734,167,5079⟩
  | 12 => ⟨24850,166,5079⟩
  | 13 => ⟨24799,165,5079⟩
  | 14 => ⟨24912,164,5079⟩
  | 15 => ⟨24860,163,5079⟩
  | 16 => ⟨24917,161,5079⟩
  | 17 => ⟨25019,157,5079⟩
  | 18 => ⟨25064,155,5079⟩
  | 19 => ⟨25162,154,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P12 : WideCovered band 6029253 7975796 := wide_block_sound band profiles_RelativeWidePack6815_P12 6029253 7975796 (wideData 16 0x292cbc1cfb9b3091ce6000000000060cbed47debec0473a00000002001c64ae14f2fab011ce808200200046e8ae0618f8cc2473a0000000000187df0182ab00473980000000001afdc02cb6d00473a00000000001b2ca01fa6b00473a00000000001aa7f10ea0011ce800000000006e864220e80473980000000001cb2e03a6d011ce80c30030c00a1a6fb0ff6a960091ce80c30030c00640c0473a030c00c30049ac0719be0829acf830c00c30028e4633c0212ce7e65901964006a90ca300818e6be40f60f60f60f60f60f60ac913f7600ddaceae) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P12 : WideCovered band 7975797 8119984 := wide_block_sound band profiles_RelativeWidePack6815_P12 7975797 8119984 (wideData 16 0x820020003e0b818fca8447398000000000182ac01a3b880473a000000000018bce019e5980473a0000000000197ee0196ad80473a00000000001a73b018e2e80473980000000001ba1901831e80473a00000000005b2af1daedc83473a00000000001cffe02db2011ce8000000000079c397768a5091ce60000000000adb74269880473a00000000002efbd15880473a00000000003beda0adb1011ce800000000012ae746b9b40473980000000005cbb901c7cfc0473a00000000007c37e02d6ca40473a02e02e03d82e02e03d928ba90cca1e3230f9ebab0) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P12 : WideCovered band 8119985 8390338 := wide_block_sound band profiles_RelativeWidePack6815_P12 8119985 8390338 (wideData 16 0xa3d745b59400639b00000030000bf9ec061ebf0018e6c000000030029f0acaeeb9772018e6c00000002001fb4e3942a8bb0018e6b82080080004b79ec19ec83d0818e6c00000000003925b039b2e000639ae0000000000f3e2007eae00018e6c00000000004ae5a04f7c0018e6b80000000005c31e02c2ec400639b00000000001f09f81e2d230018e6b8000000000dcfd849b3582f0818e6c0000000001eba4d0bfafec00639ae0000000003ebc725ad8baecb0639b00000000804f3830067d7fdbe0818e6b8000000000a9f4f43e69d40473a02e82e83d82e82e03d94a33b8c8e287840fc24fa8) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P12 : WideCovered band 8390339 8678715 := wide_block_sound band profiles_RelativeWidePack6815_P12 8390339 8678715 (wideData 16 0x82002000421a3f3bac3c0818e6c000000000029a7901f6af800639b00000000000b3de0071c300018e6c000000000039eda01839b000639ae000000000125e38231e000639b0000000000177f347b8d400639ae000000000233be80e5b690018e6c0000000000edecb07ea9c400639ae0820020804718a91a1bfd9820639b000000000066db12c7e0018e6b8000000001be3c0eff800639b0000000000063ee44faf000639ae000000000069a24063bc00639b0000000000074ae01a6d400639ae0000020807a9d0eeba0018e6c02f02f03d82e82e83d97bacd06d7aff8510866cb2) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P12 : WideCovered band 8678716 8967092 := wide_block_sound band profiles_RelativeWidePack6815_P12 8678716 8967092 (wideData 16 0xf5f6c4b98c00639b0000000000163e3c077d330018e6c0000000000883ba018a58000639b0000000000366cac167b730018e6b82080082001a73dbd1bce2f0818e6c00000000001a2490dff40018e6b80000000001b7f9018be0018e6c0000000000283a80293cd800639ae0000000000a2a2c72ca400639b00000000000bfbe40718f80018e6b80000000003bbac02da2c400639b00000000000ebd245278650818e6b80000000006ff3e0eeeab420639b00000000003b6c2007b9740018e6b80000082007b60a14d760018e6c03803803d82f82f83d82abdb0be35cea690cb9ea4) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P12 : WideCovered band 8967093 9525821 := wide_block_sound band profiles_RelativeWidePack6815_P12 8967093 9525821 (wideData 16 0x5e7c029b6c000a6b60000000000660b029ae9800a6b3e0000000006eb9029ae8800a6b3e000000000674e019f68000a6b3e000000000062ae40a4e260029acf80000000001a27b02972e800a6b3e000000000070e7c0a7a200029acf80000000001a35818b2e0029acf800000000018e1d429b2b000a6b3e08200208006fd7d0aad680029acf80000000001872c1fa600029acf800000000018e3910e2f0029acf80000000001cf99069b60029acf800000000029beb0eda70029acf80000000005d699429399e53429acf83883883d83883883d819e8dac2abb65f0181192d876) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P12 : WideCovered band 9525822 10102575 := wide_block_sound band profiles_RelativeWidePack6815_P12 9525822 10102575 (wideData 16 0x1feb680fcebc0029ad80000000000dd7cb0c8340029acf80000000011bfac4fee7f000a6b3e0000020806bd826061ea2bc00a6b3e082000000060961bc9b25b820a6b3e0000000001fee7813faa20029acf8000000000cb3ba0eafe9c00a6b3e0000000007b4bf24e9efd0029acf82080082001f3fb771b89e30829ad800000000004d36a02b3cf400a6b3e000000000229af8124cb40029acf84100104002ce1805ca2bfc3829acf8000000001e9e80e38bc0029acf8000000000186090397b8800a6b3e0000000002e6a03a7bb800a6b3e0e60e60f60e60e60f606cbeab08f37bf65129f3c38) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P12 : WideCovered band 10102576 10643280 := wide_block_sound band profiles_RelativeWidePack6815_P12 10102576 10643280 (wideData 14 0x2080082005fec642e697fd8012ce7c000000000069a701b2a380029acf80000000001a6df06c3cd800a6b3e000000000069dec1b09380029acf8514014500fa21944ef9fa94c29acf80000000005cf68179ece000a6b3e0000000000f1b394318a20029acf82080082002e74c0e8a08000a6b3e0000000000b39a82329260029acf80000000002dfec07ebeb000a6b3e0000000000fba6c36192c0029acf80000000003bbce06decb800a6b3e0000000001259ec175b640029acf83b83b83d83b83b83d81e778f437fc2db81993ab9ffc) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6029253 7975796 10643280 c0_RelativeWidePack6815_P12 (wide_covered_join band 7975797 8119984 10643280 c1_RelativeWidePack6815_P12 (wide_covered_join band 8119985 8390338 10643280 c2_RelativeWidePack6815_P12 (wide_covered_join band 8390339 8678715 10643280 c3_RelativeWidePack6815_P12 (wide_covered_join band 8678716 8967092 10643280 c4_RelativeWidePack6815_P12 (wide_covered_join band 8967093 9525821 10643280 c5_RelativeWidePack6815_P12 (wide_covered_join band 9525822 10102575 10643280 c6_RelativeWidePack6815_P12 c7_RelativeWidePack6815_P12)))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 13)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 13≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤46)
    (hT0 : 3823≤T) (hT1 : T≤4160) (hnu : 6029253≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤33078420730379481 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R076

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R077
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨13,47,3749,4134,33852173757673895⟩
private def profiles_RelativeWidePack6815_P12 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨33072,8,10160⟩
  | 4 => ⟨24154,185,5079⟩
  | 5 => ⟨24296,184,5079⟩
  | 6 => ⟨24348,181,5079⟩
  | 7 => ⟨24253,183,5079⟩
  | 8 => ⟨48205,359,10158⟩
  | 9 => ⟨48248,360,10158⟩
  | 10 => ⟨48056,364,10158⟩
  | 11 => ⟨24304,180,5079⟩
  | 12 => ⟨24439,179,5079⟩
  | 13 => ⟨24394,178,5079⟩
  | 14 => ⟨24196,186,5079⟩
  | 15 => ⟨24480,176,5079⟩
  | 16 => ⟨24515,173,5079⟩
  | 17 => ⟨41018,250,10158⟩
  | 18 => ⟨24592,171,5079⟩
  | 19 => ⟨24734,167,5079⟩
  | 20 => ⟨24799,165,5079⟩
  | 21 => ⟨24912,164,5079⟩
  | 22 => ⟨24860,163,5079⟩
  | 23 => ⟨24917,161,5079⟩
  | 24 => ⟨25064,155,5079⟩
  | 25 => ⟨25162,154,5079⟩
  | 26 => ⟨25200,152,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P12 : WideCovered band 6160324 7734037 := wide_block_sound band profiles_RelativeWidePack6815_P12 6160324 7734037 (wideData 16 0xbabcd0287cab6144bac0000000003ebe0dbee004baa0000000003f3b0ceea004bac0000000003fbd0c938004baa0000000003ffd0aca4004baa0000000003feb07e26004baa0000000005feb01dece0012eb00000000017c37c04b6ff60084baa0000000000619aac46cf1ea9084bac00000000077abbd1a1ab8c4223cd830c00c3004cace2c767ca8a0223cd8000000001000023cd82080082004df4070d26091e6c0c30030c00adb18aa0084baaf134c04d3001a74324c02479af20e80e80f80e80e80f80bda13ce800dfe5aac) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P12 : WideCovered band 7734038 7781863 := wide_block_sound band profiles_RelativeWidePack6815_P12 7734038 7781863 (wideData 16 0x11d77941961ced088f3600000000076de610a1f72f4223cd80000000001a77e394b8e7f008f36000000000122d30c48fa3de3208f360000000001e8ead845baee73108f3400000008022b83ca0dfa5b28348f3600000000006da39846eec8e1204baa000000000137da1942ae1f35004bac0000000001e1fecd07c73db50c4baa0820020000bdabf1699aaf0012eb0000000000aa302ec8000a7900000000001dab9612a3afddc50a7980000000001c68fe423ed6898212eb00000000006d6fe0192ee6a084baa00000000006ae36d08a34938184bac0b40b40f80b40b40f80faaa4917a6bee828ee25ff4) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P12 : WideCovered band 7781864 7918509 := wide_block_sound band profiles_RelativeWidePack6815_P12 7781864 7918509 (wideData 16 0x1b26a02ba4011e6c0000000000a08740e0bac011e6a0000000000759a036de40479b00000000001eb7f1cc79011e6c0000000000b4a3c0b2e7c011e6c0000000000ac9a8076fe9011e6a0000000000b7d740b4e6d011e6c0000000000fd8fc075eea011e6c000000000165c419a1e79091e6c0000000000f8ba50b3a79d42479a80000000007c70f0bd2cdc0479b0000000000baa9c0397bc40479b00000000002a21da106d9a08231d1e6c0000000000e8de4901c79a3bd82479a80000000009f3a905b2a84023cd82d82d83e02d82d83e04fa490fcfa96a68eee7ee4) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P12 : WideCovered band 7918510 8064266 := wide_block_sound band profiles_RelativeWidePack6815_P12 7918510 8064266 (wideData 16 0x7bb7c334a00479b000000000028f1905fea011e6a0000000000adf6c07ab40479b00000000002eedb0beb5011e6c0000000000edb6463bd40479b000000000049a3901abda40479a80000000005a69e02928c40479b00000000006f7d903a7e840479b00000000004c37b02d20c33091e6c000000000438bf81b4c25011e6a0000000003e7da332a83f011e6c000000000070faea43c77840479b00000082001fe28b206cdfb8c4479b0000000000d83ecc1d25ee1091e6c0820000000b3ca99c182cb37091e6c0b60b60f80b60b60f80e7d77d13ee1cb658f8fbd26) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P12 : WideCovered band 8064267 8273790 := wide_block_sound band profiles_RelativeWidePack6815_P12 8064267 8273790 (wideData 16 0x49ba80492aec0063cb600000000016dd241bdded0018f2e00000000008f2fb0bdae0018f2d8000000000eb7fc47cabdf11018f2e00000000019f32d169f09c0063cb6000000000064db0a0ffa19791018f2e000000020149b4881866cf9e8f063cb60000000003e48791acdbb011e6c0000000003adcfa17fde4c02479b02080080001c3f9e91a58adcc2479a800000000018a3e01869b80479b00000000001935d1f832011e6c000000000067db872fe00479b00000000001aea819b76011e6a00000000006fd6057dc80479b02e02e03e02e02e03e01e7fd24328aef98180fb38aa0) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P12 : WideCovered band 8273791 8565303 := wide_block_sound band profiles_RelativeWidePack6815_P12 8273791 8565303 (wideData 16 0x30c00c3008aace06868c671418f2d82080082006fbac468a7ee81018f2e000000000189a0061800063cb80000000007b790deec0018f2e0000000000192cf0d9ec0018f2d80000000001b22e0cbfa0018f2e00000082001b3b80a8350018f2d80000000012db41e0e80063cb8000000000662b03dae0018f2d800000000018efe01cf10018f2e000000c0003e3ae01e60c40063cb6000000000122c3c072a770018f2e00000003001c7e9bf32cdedb42063cb6082002080069e2ebc2827c670818f2e000000000038e290b840063cb60ba0ba0f80ba0ba0f80eadb3b14fe582e78fea3ab4) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P12 : WideCovered band 8565304 8856816 := wide_block_sound band profiles_RelativeWidePack6815_P12 8565304 8856816 (wideData 16 0x1ceda17f2d0018f2d80000000002a71a019edc00063cb80000000000b8eec72fc00063cb80000000003e1b15f37e42063cb80000000000b2b20425a670818f2d80000000007ab4f01929e80063cb80000000002e2b740f4880063cb60000000004e4f700a09290018f2e0000000200fd619caee4a40063cb60820020003f9f6316f8e9f86063cb800000000013da50ab80018f2d82080082005aac538d80063cb80c30030c047d9ed176df2dc5063cb60000000000fa924739d40063cb8000000000161fb80addeb0018f2d82f82f83e02f82f83e01bacce432cee3a81990afcda6) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P12 : WideCovered band 8856817 9257646 := wide_block_sound band profiles_RelativeWidePack6815_P12 8856817 9257646 (wideData 16 0x65a7c627f000a796e0000000007f4c42a60b800a796e000000000069ab8071e800a796e00000000006dae10aaa700029e5b80000000007af5903c65ac00a7970082002080464a750a9ee4c4d0a796e0000000000788e8330f00063cb60000000000ac8a40a2fbe0018f2e00000000002cbff02b360018f2d800000000039ac8018a1c40063cb800000000013597c071fae0018f2d80000000005ff4d03a2cec0063cb8000000000267ae81ace730018f2d80000000012eb284dde6ec2063cb80000000002f7b21232ae00018f2d83883883e03883883e01d28a782b5f33b01b10f76878) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P12 : WideCovered band 9257647 9840671 := wide_block_sound band profiles_RelativeWidePack6815_P12 9257647 9840671 (wideData 16 0x186006180677cad139cb3f8e0a796e0000000006a9b02d23d000a796e0000000006bed02c61e000a796e00000000076bc02d779800a796e0000000007a5c02bfdd000a7970000000000062bbc0ba9640029e5b800000000018f4e02bf79800a796e0000000004bca0386fb800a796e000000000063da50b38f60029e5b82080082018dfc0a3f2e0029e5b8000000001aa680719a20029e5b80000000001837d028e8f800a796e000000000060cbc06bb6e0029e5b80000000001ab9c02938e000a796e00000000006d960063cf20029e5b83903903e03903903e01af8ab0224b23901891de8c2a) (by decide +kernel)
private theorem c9_RelativeWidePack6815_P12 : WideCovered band 9840672 10423696 := wide_block_sound band profiles_RelativeWidePack6815_P12 9840672 10423696 (wideData 16 0x3cfcf07f658800a796e000000000125bb01ec8e60029e5b800000000068ead0dde5a800a796e0000000000aaebc1edcae0029e5b80000000005a6bf479a0a800a7970082002080225b47aaa9000a796e0000000000e58fc0b7c6a0029e5b80000000003db8808b7d0029e5b8000000000587b903c62dc00a796e000000000260a70124a400a796e0000000003649bc06eaa9fc20a796e0000020805ecb3a239ef10029e5b82080000001ebc867229a6a0829e5b80000000006cece03b6eb000a796e0000000002779600a3f230029e5b83b03b03e03b03b03e01c228b4371af9981c12ebb9ec) (by decide +kernel)
private theorem c10_RelativeWidePack6815_P12 : WideCovered band 10423697 10824525 := wide_block_sound band profiles_RelativeWidePack6815_P12 10423697 10824525 (wideData 8 0x69669029638c012eabc0000000001e2ca47f4aa5004baaf0208008201f828e08a2cc244c4baaf02080082003b38c4faf6d000a796e0000000000baa60272c7a0029e5b80000000002f2de098699000a796e0000000000faaf0365ef00029e5b83c03c03e03c03c03e02b3df6437dfa2d81d13fadfae) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6160324 7734037 10824525 c0_RelativeWidePack6815_P12 (wide_covered_join band 7734038 7781863 10824525 c1_RelativeWidePack6815_P12 (wide_covered_join band 7781864 7918509 10824525 c2_RelativeWidePack6815_P12 (wide_covered_join band 7918510 8064266 10824525 c3_RelativeWidePack6815_P12 (wide_covered_join band 8064267 8273790 10824525 c4_RelativeWidePack6815_P12 (wide_covered_join band 8273791 8565303 10824525 c5_RelativeWidePack6815_P12 (wide_covered_join band 8565304 8856816 10824525 c6_RelativeWidePack6815_P12 (wide_covered_join band 8856817 9257646 10824525 c7_RelativeWidePack6815_P12 (wide_covered_join band 9257647 9840671 10824525 c8_RelativeWidePack6815_P12 (wide_covered_join band 9840672 10423696 10824525 c9_RelativeWidePack6815_P12 c10_RelativeWidePack6815_P12))))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 13)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 13≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤47)
    (hT0 : 3749≤T) (hT1 : T≤4134) (hnu : 6160324≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤33852173757673895 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R077
end MergedPart0
section MergedPart1
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R078
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨13,48,3720,4108,34880795038857114⟩
private def profiles_RelativeWidePack6815_P13 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨48248,360,10158⟩
  | 4 => ⟨48205,359,10158⟩
  | 5 => ⟨24253,183,5079⟩
  | 6 => ⟨24304,180,5079⟩
  | 7 => ⟨24348,181,5079⟩
  | 8 => ⟨24296,184,5079⟩
  | 9 => ⟨24196,186,5079⟩
  | 10 => ⟨24154,185,5079⟩
  | 11 => ⟨29266,226,6051⟩
  | 12 => ⟨48056,364,10158⟩
  | 13 => ⟨29307,227,6051⟩
  | 14 => ⟨24394,178,5079⟩
  | 15 => ⟨24439,179,5079⟩
  | 16 => ⟨24480,176,5079⟩
  | 17 => ⟨24515,173,5079⟩
  | 18 => ⟨24592,171,5079⟩
  | 19 => ⟨24526,177,5079⟩
  | 20 => ⟨41018,250,10158⟩
  | 21 => ⟨24799,165,5079⟩
  | 22 => ⟨24912,164,5079⟩
  | 23 => ⟨24860,163,5079⟩
  | 24 => ⟨24917,161,5079⟩
  | 25 => ⟨25024,160,5079⟩
  | 26 => ⟨25120,156,5079⟩
  | 27 => ⟨25162,154,5079⟩
  | 28 => ⟨25200,152,5079⟩
  | 29 => ⟨25234,150,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P13 : WideCovered band 6291395 7667956 := wide_block_sound band profiles_RelativeWidePack6815_P13 6291395 7667956 (wideData 16 0x7f2919f73004bfc000000000060c347f3f4012ff0000000000187df018be84012ff00000000001a6ec079f0004bfc000000000069da01aacc012ff000000000019e1b01b2f8c012ff00000000001a61801c61b4012fe80000000001ae6b01d7cdc012ff00000000001e26d1dd3a004bfc000000000062cebc4aa6482f084bfc00000000006be71062deb84212ff00000000003d22b34060abbce4084bfc0c30030c0503008ff8000000000139a01c2ce02063fe00000000000f3b01929c0223fdfa0b60b60fa0b60b60fa0e1f13be000e9fdea8) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P13 : WideCovered band 7667957 7718599 := wide_block_sound band profiles_RelativeWidePack6815_P13 7667957 7718599 (wideData 16 0x460f07a7a004bfc00000000043b8039a0004bfc000000000662d01cf8c8012ff00000000001f71c65323a6bec912ff00000000003b6697d5a1862c4523fe00000000003c65cf85a2d64b0423fe00000000015b2cd03f22b380c8ff8000000000463eb50fc8fc9c223fe00000000001cb596827c86580223fd8000000000197db381f5b3dc0423fe00000000013e3c1a9dc012ff00000000014a3823aac012ff00000000018eb8e45b3daa9084bfc00000000056a96812ad2a98512ff00000000005db0d018a7824084bfc0b40b40fa0b40b40fa0a3dbdf0fbb9ea030ed24fe4) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P13 : WideCovered band 7718600 7748524 := wide_block_sound band profiles_RelativeWidePack6815_P13 7718600 7748524 (wideData 16 0x80008a6bcba22ab2398312ff0000000001ba7884e931a000a7f82080000001c69ca1664ae20029fe0000000002aed0a9f40029fe0000000002b190a8e20029fe0000000002f390feae0029fe000000000178cb8f4187ae7fdd30a7f800000000048e7ae85fbd2a88212ff0000000000283abb4326c2b90412ff00000000001afcf341ffe35e8a12ff0000000000fafc2fd88012ff0000000000fcf42e7e0012ff0000000000fd74267c8012fe80000000015dec06bff4004bfc000000000476f11832004bfc0b40b40fa0b40b40fa0ece73f15826cec28ede7f2a) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P13 : WideCovered band 7748525 7838299 := wide_block_sound band profiles_RelativeWidePack6815_P13 7748525 7838299 (wideData 16 0x5c3b90a8bdec047fb80000000008a70f02d22d4047fc00000000012c62d4acb6dbd091ff0000000000071eee9418bbda2fc947fc00000000003bf8a34071eaeafc2d1fee0000000002738f4127e4023fe00000000003be7a87922a4023fe00000000011ff8e43968973408ff80000000006ace753a4f73008ff80000000000658f4d44de6b4023fe00000000003cbdcf523583ad4223fe0000000000c86a8a1534df19cb23fd8000000200cc268205b69f098a23fe0000000000286cb297fc8f3004bfc0000000001298f99428fa933004bfc0b60b60fa0b60b40fa324aeec9d964ab428ee62ab4) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P13 : WideCovered band 7838300 7985623 := wide_block_sound band profiles_RelativeWidePack6815_P13 7838300 7985623 (wideData 16 0xefa0902f2ce4047fb80000000002962a8c93f84047fc00000000001a20835137cfb011ff0000002080061a3ed01eb9ea1111ff0000003000122f67f42833d2f011fee08200200006aea3e8882e9d047fc0000000000297dc0496398047fc00000000016cbee03f7dae0451ff000000000006de204e1fc047fb800000000028bda02b36b0047fc00000000001e20901ab4e4047fc00000000002c6a802863f8047fc00000000002a27e02b33bc047fb80000000003a21a01b76f0047fc00000000001aa6e419659a50d1ff00b60b60fa0b60b60fa0a4c26f10ebfcb478efbf966) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P13 : WideCovered band 7985624 8132948 := wide_block_sound band profiles_RelativeWidePack6815_P13 7985624 8132948 (wideData 16 0x820020005b8ce7062c6f091fee000000000068e700ad870011ff0000000000062f64630d8047fc00000000001977815abc011ff0000000000069870472b8047fc00000000001b3ce0c924011ff0000000000071e301baa0047fc00000000001df8d0ff8047fc00000000002aa8d02a23a8047fb80000000002a66e0ab75011ff00000000000b5bb05abdc047fc00000000003979a01963fc047fc00000000003f22c01e6cfc047fb80000000004ef1c02d7fec047fc00000000006d73e16830011ff00b80b80fa0b80b80fa7a3da432aea1b0188f9fef3e) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P13 : WideCovered band 8132949 8409181 := wide_block_sound band profiles_RelativeWidePack6815_P13 8132949 8409181 (wideData 16 0x79934468840063fe00000000000b9c240629f70018fef80000003002d2da4b82afef1818ff800000000002e3ecdb97c8c0063fbe000002080338ebd1688a6ac2063fe00820000000a59ed8c2cfbdba0018fef80000000004cfaa0687c880063fe0000000000169f6013a9be0018fef80000000004ae5b0b8afec0063fe0000000000064ba50a5a39f47063fbe000000000165aed132c70aca063fe00000000005708305fdfe30018fef80000000011fb1b0faac8a54018ff800000000001eaee627feeb5d99063fbe0000000803e6be11619a9011ff00ba0ba0fa0ba0b80fa4b883e32082cf0190fc3ed38) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P13 : WideCovered band 8409182 8703830 := wide_block_sound band profiles_RelativeWidePack6815_P13 8409182 8703830 (wideData 16 0x8200208077adff16be3bd82063fe000000000027ba58a6e0018ff80000000000cc25673f00063fe0082002080075e549240018fef8000000000ee7043f880063fe000000000042ab11db40018fef80000000010fac2f6d00063fe00000000004bc80af2a0018fef80000000015a382a0a00063fe0000000000628f08f240018fef8000000001c8f41eed80063fe00000000000618f8172f00063fbe00000000006993c2f9f80063fe0000000000072eb4321c00063fbe00000208006be600778c0063fe00bc0bc0fa0ba0ba0fa6faba41adf31d01a108ac938) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P13 : WideCovered band 8703831 8998478 := wide_block_sound band profiles_RelativeWidePack6815_P13 8703831 8998478 (wideData 16 0x2cfeb01ab4840063fe00000000000f9a7076ca80063fbe000000000132db00f3bf30018ff800000000007927f01a36d40063fbe0000000002e5ba00ecb390018ff800000000016efa84ce36ec2063fbe0000000001b4b7916ec3e0018ff802080082005df1c44efff80063fbe0000000000a0b3c6e6e80063fe0000000000664954c3c842063fbe0000000000a3e54a61a42063fe000000000012c9384b2e00063fbe00000000017c834322f40063fe000000000022fdb00a1d710018fef8000000000df65801b63940063fe00e00e00fa0e00e00fa4eaa242fcaabf81a90d2bd2a) (by decide +kernel)
private theorem c9_RelativeWidePack6815_P13 : WideCovered band 8998479 9532528 := wide_block_sound band profiles_RelativeWidePack6815_P13 8998479 9532528 (wideData 16 0x1b25f42ff38800a7f7e082002080722a02877f800a7f7e000000000729a01c32f000a7f7e0000000007f0f01b73c800a7f7e000000000066a6c076e200029fdf80000000001bb0e01f68d800a7f7e000000000074c640648a20029fdf800000000028f1c1cc6e0029fe800000000002962a01a61b800a7f7e000000000139a01b65b800a7f7e0000000000bbbb05e3e400a7f7e000000000232ef80fdc2b0029fdf80000002003e2dac2eb3d212c29fdf82080080014ce4ad4f31d02063fbe0000000000a3b2807ca7e0018ff803883883e83883883e81c75e602a7de4c01c119ab8fa) (by decide +kernel)
private theorem c10_RelativeWidePack6815_P13 : WideCovered band 9532529 10121825 := wide_block_sound band profiles_RelativeWidePack6815_P13 9532529 10121825 (wideData 16 0x1aa924070d7f0029fdf800000000068b6a01a6ac310829fdf80000000018cf7e07ea2f400a7f7e000000000075faa9c1ce6fe70029fdf82080082003b7ec8eca8d820a7f7e000000000229ef40a4aba0029fdf841001040058ab905b7fa6c3029fdf80000000001879e03aa4e800a7fa0082002080775943c34a000a7f7e00000000072ff02eaaa800a7f7e0000000006e2e02af6f000a7f7e000000000736e02ae1c800a7f7e000000000060e7c0b59700029fdf80000000001965c02f768000a7f7e000000000065e2c0ada6c0029fdf83983983e83983983e81c72834232832c01a12a2293e) (by decide +kernel)
private theorem c11_RelativeWidePack6815_P13 : WideCovered band 10121826 10784784 := wide_block_sound band profiles_RelativeWidePack6815_P13 10121826 10784784 (wideData 16 0x30c00c3001862f621b0b22bc012fefc1040041005e2c6a432babd9312fefc000000000124838362ee60029fdf80000000003ea3c08ee3e000a7f7e00000000012ebf023abb40029fdf80000000003d2bc498739800a7f7e0820020805a8845fb1e000a7f7e0000000000acca00fdd7a0029fe800000000002dbbc03967f000a7f7e0000000000fed641b8fa60029fdf800000000049a6c01b6f8800a7f7e00000000017b8fc6e49c00a7f7e00000000026cee816bf610029fdf8208008201ab38852f69d420a7f7e0000000000b997c076b730029fdf83b83b83e83b83b83e81f22e70322bf7d01e13b21920) (by decide +kernel)
private theorem c12_RelativeWidePack6815_P13 : WideCovered band 10784785 11005770 := wide_block_sound band profiles_RelativeWidePack6815_P13 10784785 11005770 (wideData 3 0x82002080061ee80669ba88012fefc00000000012d9380f9afe004bfbf03d03d03e83d03d03e84a2586c5eeaffb81a14db7f3c) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6291395 7667956 11005770 c0_RelativeWidePack6815_P13 (wide_covered_join band 7667957 7718599 11005770 c1_RelativeWidePack6815_P13 (wide_covered_join band 7718600 7748524 11005770 c2_RelativeWidePack6815_P13 (wide_covered_join band 7748525 7838299 11005770 c3_RelativeWidePack6815_P13 (wide_covered_join band 7838300 7985623 11005770 c4_RelativeWidePack6815_P13 (wide_covered_join band 7985624 8132948 11005770 c5_RelativeWidePack6815_P13 (wide_covered_join band 8132949 8409181 11005770 c6_RelativeWidePack6815_P13 (wide_covered_join band 8409182 8703830 11005770 c7_RelativeWidePack6815_P13 (wide_covered_join band 8703831 8998478 11005770 c8_RelativeWidePack6815_P13 (wide_covered_join band 8998479 9532528 11005770 c9_RelativeWidePack6815_P13 (wide_covered_join band 9532529 10121825 11005770 c10_RelativeWidePack6815_P13 (wide_covered_join band 10121826 10784784 11005770 c11_RelativeWidePack6815_P13 c12_RelativeWidePack6815_P13))))))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 13)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 13≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤48)
    (hT0 : 3720≤T) (hT1 : T≤4108) (hnu : 6291395≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤34880795038857114 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R078

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R079
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨13,49,3720,4082,35504637214351113⟩
private def profiles_RelativeWidePack6815_P13 : ℕ → Profile
  | 0 => ⟨16536,4,5080⟩
  | 1 => ⟨33072,8,10160⟩
  | 2 => ⟨29266,226,6051⟩
  | 3 => ⟨48205,359,10158⟩
  | 4 => ⟨24253,183,5079⟩
  | 5 => ⟨29307,227,6051⟩
  | 6 => ⟨29103,225,5971⟩
  | 7 => ⟨24348,181,5079⟩
  | 8 => ⟨24304,180,5079⟩
  | 9 => ⟨24154,185,5079⟩
  | 10 => ⟨48248,360,10158⟩
  | 11 => ⟨48056,364,10158⟩
  | 12 => ⟨24394,178,5079⟩
  | 13 => ⟨24439,179,5079⟩
  | 14 => ⟨24480,176,5079⟩
  | 15 => ⟨24562,174,5079⟩
  | 16 => ⟨24515,173,5079⟩
  | 17 => ⟨41268,250,10158⟩
  | 18 => ⟨24592,171,5079⟩
  | 19 => ⟨24526,177,5079⟩
  | 20 => ⟨24799,165,5079⟩
  | 21 => ⟨24912,164,5079⟩
  | 22 => ⟨24860,163,5079⟩
  | 23 => ⟨24970,162,5079⟩
  | 24 => ⟨24917,161,5079⟩
  | 25 => ⟨24970,159,5079⟩
  | 26 => ⟨25162,154,5079⟩
  | 27 => ⟨25200,152,5079⟩
  | 28 => ⟨25234,150,5079⟩
  | 29 => ⟨25324,149,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P13 : WideCovered band 6422466 7669439 := wide_block_sound band profiles_RelativeWidePack6815_P13 6422466 7669439 (wideData 16 0x5eebb7406caaeb6a0898ba0000000007bba01921bc0131b00000000001a74f0193fa80131b800000000018a4b019e7c40131b000000000018efb01b77c40131b80000000001968e01cabbc0131b00000000001c61e1ea28004c6e000000000069ce40798b9004c6c000000000060ca6d4a9e9b7b084c6e0000000000b3e75a57864929084c6c0000000000f48f01f3d37004c6e00000000017caa4f01daf8eed02131b00000000008000131b830c00c30100c0262e80000000004bb8070b3808192ba02d82d83f02d82d83f069ec077e3000ec36aa6) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P13 : WideCovered band 7669440 7720621 := wide_block_sound band profiles_RelativeWidePack6815_P13 7669440 7720621 (wideData 16 0xf8b80eac00131b00000000016de8073b2e004c6e000000000428c05af6004c6c000000000430a03ea6004c6e00000000042b9179c0131b00000000015f21b04b64a221c4c6e0c3000000172a7c062d21c83131b0208000000e9340e6004c6e000000000134ea9062d7bf42131b00000000014b60f44c71abb184c6e0000000001a8eafb41b26d3bfc5262e80000000006af3e3006c9b98381098ba0000000001a2c7fa41b25f69fc5262e00000000006dbdc10ae1e02262e80000000004c7df06ab3bc0262e82d02d03f02d02d03f08d2eff40a0fbe92628ed2cbb8) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P13 : WideCovered band 7720622 7750865 := wide_block_sound band profiles_RelativeWidePack6815_P13 7720622 7750865 (wideData 16 0x10bb6a0bf71e3f344c6e00000200026de3fc88ae5ae4384c6c00000000042b8e12349fe002a360820000000a29aca41871eb4002a38000000000277f09d60002a360000000002e4a11eb4002a360000000002fff16db8002a36000000000072da484a832f6f442a3800000000006dffb808efbff8084c6c0000000003e99740eb9f8a02131b80000000013b7c4a4d80131b00000000001a3ab241ffdb6e8a131b8000000000e9641ebb00131b00000000015b24074a7e004c6e0000000003e2808cf6004c6c0b40b40fc0b40b40fc0e6822b1583dca020edebf26) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P13 : WideCovered band 7750866 7846248 := wide_block_sound band profiles_RelativeWidePack6815_P13 7750866 7846248 (wideData 16 0x1659a43bfec04a5d00000000005a69e0c8209404a5c80000000008860f04f78e404a5d0000000000e83084a835e3721297400000000043cfa55abab1c4b4a5d00000000002a73830064f6bc3e1d297200000000027ba381bbc6b0098ba0000000001ebda30e6cfe9c8262e800000000149a684193cb40262e8000000001dab7f519e3ec0262e80000000001d34b790acbfa9c2262e8000000000497b8351e2dfcfc6262e800000020028fdca8265d2ef09262e000000000029708e91e6ae1cc8131b00000000005aabc55b33004c6e0b60b60fc0b60b40fc1fd93ba9afaae6c20ee66fae) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P13 : WideCovered band 7846249 7995140 := wide_block_sound band profiles_RelativeWidePack6815_P13 7846249 7995140 (wideData 16 0x12da7c07ffe5b424a5d0000000000e9eb9119a601297200000000007896e3a0af7012974000000000066bf0f47eb68c04a5d00000002001f6c842939b33112974000000000534af51e0bbd0129720820020006ba92f0719bcc484a5d0000000000fd33c02ea18f22d29740000000001e9c20066decd024a5d00000000001a70b018639404a5c80000000001f6fa01fa8c804a5d00000000001cba801ff4e404a5d00000000002ae8b01bade804a5d00000000002d3de01975b804a5c80000000001eec84193e8f70d29740b60b60fc0b60b60fc0a3826910eacebc68efeef24) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P13 : WideCovered band 7995141 8144032 := wide_block_sound band profiles_RelativeWidePack6815_P13 7995141 8144032 (wideData 16 0x208012deff1a7df9c024a5d00000000010a7147fc004a5c8208000001dcad63bd804a5d0000000001ff79b46b76b210929740000000000628303a7a004a5d0000000000193b808a6c012972000000000071e300a486001297400000000006db6006cd804a5d00000000001cb8b06fa7012974000000000079d38422cc04a5c80000000002b64801eb59804a5d00000000002ba78018a89404a5d00000000002f6dd01cf4ac04a5d00000000003f74c019b0a004a5c80000000004bfc802f749404a5d02e02e03f02e02e03f018abaa4329e2be8180fa31d7c) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P13 : WideCovered band 8144033 8432510 := wide_block_sound band profiles_RelativeWidePack6815_P13 8144033 8432510 (wideData 16 0x8d283b4c00064ae6000000000070ab43f8b40064ae800000000063ac06c2600192b9800000c0003bedc01c3dd40064ae80000000000eecac064bab00192b980000080002c2b9274a38ac8c6064ae8082000000425b6706bfbe98b064ae6000000000120b680afe7400192ba00000000004c7e902f3b00192b980000000005b78f03e64f40064ae80000000002fe979138ee0a4e064ae60000000002ebaf0569ba500192ba00000000005e79f05c6c8a50c192b980000000019f2ee0ae20dfd28192ba00000000002920fb4060fb5b3254192b982e82e83f02e82e83f049b82fe833b8190fc74bf4) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P13 : WideCovered band 8432511 8730294 := wide_block_sound band profiles_RelativeWidePack6815_P13 8432511 8730294 (wideData 16 0x4b4eb45f8a40064ae60820020806faea516fb6fb86064ae80000000004f8d418b3d00064ae600000000026bc54dba00192ba02080082009ee8531f80064ae6000000000329909eac00192ba0000000000f8e44e0980064ae60000000003bcb08d2800192ba00000000012b644baf00064ae60000000004b8e078ee00192ba00000000017b704b2f80064ae600000000063cb04efc00192ba0000000001fca04a7a00064ae6000000000063a7806fc00064ae8000002080067c2c467980064ae60bc0bc0fc0ba0ba0fc6e3be41aa83db018908fa8e4) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P13 : WideCovered band 8730295 9028079 := wide_block_sound band profiles_RelativeWidePack6815_P13 8730295 9028079 (wideData 16 0x283e8019a4f80064ae60000000000adf7c733900064ae80000000000e0e303e1d00064ae60000000000fdc74136bc0064ae8000000000161ce8138ff100192b980000000006e26c13b75a42064ae80000020802b5e69078be608192b980000000006ea80718ae00192ba00000000004bbac19ef300192b982080000019b22d418a9ceb10192ba000000000069f9e1abead03064ae8000000000524f55e788c2064ae80000000000f0ffc27d9c0064ae6000000000160e7c079c6000192ba00000000006e72d10d2500192b983803803f03803803f018bafa82f9b65b01a10d7fdb4) (by decide +kernel)
private theorem c9_RelativeWidePack6815_P13 : WideCovered band 9028080 9586425 := wide_block_sound band profiles_RelativeWidePack6815_P13 9028080 9586425 (wideData 16 0x66a700afd70002a36b80000000004fb80b2b22002a36b820800820018f4842ce58800a8dae00000000067de01cf8b800a8dae000000000739f01c7bf800a8db0000000000060e2406fd30002a36b800000000019a9e01b3e9800a8dae00000000006eb3c069b6a002a36b80000000001eba90192bd000a8dae0000000000afa2473a9000a8dae0000000000b9f783faf000a8dae0000000000b09bc2b9a400a8dae0000000001aff6c0b2b69002a36b8000000000ee39c82a67beb442a36b82080082001a258630a9eb108192b983883883f03883883f01c6cb602aaef9d01c11a25aa6) (by decide +kernel)
private theorem c10_RelativeWidePack6815_P13 : WideCovered band 9586426 10181994 := wide_block_sound band profiles_RelativeWidePack6815_P13 9586426 10181994 (wideData 16 0x15e67d09db99c00a8dae0820020804f4ae13fafb0002a36b80000000001b7db01c2abb5082a36b8000000000e96390cd35b400a8dae0000000007e4fbe3b6c23002a36c06180186001ca1afb163e398120a8dae000000000775d03975b800a8dae0000000007ebd039bcd000a8dae000000000061c3c0e8eb8002a36b80000000016da80ebd6c002a36b820800820178250e49e6002a36b80000000018e700acc36002a36b8000000001aa2c0acafe002a36b8000000001c9380acb7c002a36b8000000001ecf00acf70002a36b83983983f03983983f01bba838230b63981892aec9a0) (by decide +kernel)
private theorem c11_RelativeWidePack6815_P13 : WideCovered band 10181995 10814785 := wide_block_sound band profiles_RelativeWidePack6815_P13 10181995 10814785 (wideData 16 0x82002080064ff0a0ca73fbe644c6cf00000000004836b49dbec800a8dae082002080074a6c23cff6002a36b800000000029aa904ebb9800a8dae0000000000ad9f4125c70002a36b80000000003b6dd07defb000a8dae0000000000ecbf40bd8ba002a36b80000000004b25c01bacf800a8dae0000000001e3c3c1ac9b4002a36b8000000000ac2d803bbccc00a8dae0000000005bdca83bac63002a36b82080082001b309f5334cac082a36b80000000004de9a0386f9000a8dae00000000017eab41afd35002a36b8000000000bc7fa05b68cc00a8dae0f00f00fc0f00f00fc76fa742f6bb2f81e13bf7b62) (by decide +kernel)
private theorem c12_RelativeWidePack6815_P13 : WideCovered band 10814786 11187015 := wide_block_sound band profiles_RelativeWidePack6815_P13 10814786 11187015 (wideData 5 0x234dfc061b36e00131b3c00000000022ca6c6b78aa004c6cf00000000008d22f128a0980131b3c0000000002a1dbc0eaf20004c6cf03d83d83f03d83d83f03c7ad3c5fbeabf81894e3483e) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6422466 7669439 11187015 c0_RelativeWidePack6815_P13 (wide_covered_join band 7669440 7720621 11187015 c1_RelativeWidePack6815_P13 (wide_covered_join band 7720622 7750865 11187015 c2_RelativeWidePack6815_P13 (wide_covered_join band 7750866 7846248 11187015 c3_RelativeWidePack6815_P13 (wide_covered_join band 7846249 7995140 11187015 c4_RelativeWidePack6815_P13 (wide_covered_join band 7995141 8144032 11187015 c5_RelativeWidePack6815_P13 (wide_covered_join band 8144033 8432510 11187015 c6_RelativeWidePack6815_P13 (wide_covered_join band 8432511 8730294 11187015 c7_RelativeWidePack6815_P13 (wide_covered_join band 8730295 9028079 11187015 c8_RelativeWidePack6815_P13 (wide_covered_join band 9028080 9586425 11187015 c9_RelativeWidePack6815_P13 (wide_covered_join band 9586426 10181994 11187015 c10_RelativeWidePack6815_P13 (wide_covered_join band 10181995 10814785 11187015 c11_RelativeWidePack6815_P13 c12_RelativeWidePack6815_P13))))))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 13)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 13≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤49)
    (hT0 : 3720≤T) (hT1 : T≤4082) (hnu : 6422466≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤35504637214351113 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R079

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R080
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨13,50,3720,4054,35424324682627447⟩
private def profiles_RelativeWidePack6815_P13 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨29266,226,6051⟩
  | 4 => ⟨48205,359,10158⟩
  | 5 => ⟨24253,183,5079⟩
  | 6 => ⟨24304,180,5079⟩
  | 7 => ⟨24348,181,5079⟩
  | 8 => ⟨24296,184,5079⟩
  | 9 => ⟨24154,185,5079⟩
  | 10 => ⟨24196,186,5079⟩
  | 11 => ⟨48056,364,10158⟩
  | 12 => ⟨24394,178,5079⟩
  | 13 => ⟨24439,179,5079⟩
  | 14 => ⟨24480,176,5079⟩
  | 15 => ⟨24562,174,5079⟩
  | 16 => ⟨24515,173,5079⟩
  | 17 => ⟨41518,250,10158⟩
  | 18 => ⟨24592,171,5079⟩
  | 19 => ⟨24526,177,5079⟩
  | 20 => ⟨24799,165,5079⟩
  | 21 => ⟨24912,164,5079⟩
  | 22 => ⟨24860,163,5079⟩
  | 23 => ⟨24917,161,5079⟩
  | 24 => ⟨24970,159,5079⟩
  | 25 => ⟨25162,154,5079⟩
  | 26 => ⟨25200,152,5079⟩
  | 27 => ⟨25234,150,5079⟩
  | 28 => ⟨25324,149,5079⟩
  | 29 => ⟨25412,148,5079⟩
  | 30 => ⟨25351,147,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P13 : WideCovered band 6553537 7663180 := wide_block_sound band profiles_RelativeWidePack6815_P13 6553537 7663180 (wideData 16 0x669a8063ebe004cbe0000000007bf901ab3cc0132f8000000000182b901c20ec0132f8000000000187ff01d35c40132f80000000001b3fc1cb6c004cbe000000000065ee407cef5004cbe0000000007aac752a8aa6c42132f80000000002aff8069fa004cbe0000000000acd34857a2d96b084cbc00000000016edadd01daffbc882132f830c00c30100c0265f00000000001800012af8000000000123901c2ce02064df00000000000e3801929c02265ef84d30134c01644404abdf00e80e80fe0e80e80fe0b0a13bf000dd37ae2) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P13 : WideCovered band 7663181 7710199 := wide_block_sound band profiles_RelativeWidePack6815_P13 7663181 7710199 (wideData 16 0xfe78078980132f8000000000fd3c0e6a40132f80000000016ae006ac7e004cbe00000000062e93416dfe6a03132f8000000000da6806e840132f80000000005a36df5067d7bc3f184cbe0000000000f3f780e392a00997c0000000000e5f6c0a5ab900997c0000000000e9e300f0a2500997c000000000163978d019f8c23f07265e80000000015b20b45b3eeb1084cbe0000000004aba6c12ac37f05132f80000000004f75c018a7ee4084cbe000000000535e7d16d9f38c2132f8000000001af7c062b65004cbe0b40b40fe0b40b40fe0ae8f2b14f6492e28ecfbdf6) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P13 : WideCovered band 7710200 7743112 := wide_block_sound band profiles_RelativeWidePack6815_P13 7710200 7743112 (wideData 16 0x8f702239000a9b8000000000caf07ebf000a9c0000000000a8b3d41dedb2f342a6e000000000064b3ff48a6bf390c2a700c3000000065d74b08a69af2084cbe0820000004baf680fe83c802132f8000000001cce080682bffc084cbe0000000003b0d0ad24004cbe000000000277f6c0a18e0b06132f8000000000ddbc1f9980132f8000000000dda013d880132f80000000014a38071bee004cbe0000000003b0c05bb6004cbc0000000003b7b03efc004cbe0000000003aff01831004cbe0b40b40fe0b40b40fe0bbff0a14fef9a228edb7cac) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P13 : WideCovered band 7743113 7804237 := wide_block_sound band profiles_RelativeWidePack6815_P13 7743113 7804237 (wideData 16 0x3ab8ba8072be4d74152af80000000001eca3017db2500997c00000000026dea406ee6b00997c0000000002638bb0e5c3eecc265f00000000013f64c4e831b40265f0000000001bdecf45cb8ec0265f00000000001cf7af10adf6dec3265f00000000005a27bb52efaab843265f00000002002d7bb2836daeb984265f00000000002b26eb91e8b79e42132f0000000000e9ef84597af40132f80000000005df5f310bb9ace40132f80000000005f6cba163583de4d132f800000800128feb365aaeebe0e132f80000000001ded9b1724a6c002a6e0b60b60fe0b40b40fe123cf3f1fca0ebc20ee35ca0) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P13 : WideCovered band 7804238 7954697 := wide_block_sound band profiles_RelativeWidePack6815_P13 7804238 7954697 (wideData 16 0xc0001e29a256b6d3b012af80820020007f7cc1a74c6f312af60000000000769ec0e4f3e012af80000000003a9f700b9979d0f4abe00000000006db48019a98b8092af80000000000fc92d066cbdfc34abd80000000006ef6d019a78ee092af800000000007feb8063fbc012af80000000000a7e206b5f804abe00000000002873f41965b3b0d2af60000000000e483c3aaf404abe00000000005f2ab42d66833392af80000000001658fc0b3c29012af80000000001af9a8131a23012af600000000022f9f41edbf5012af80b60b60fe0b60b60fe06e8fe813fbc93230ef3d832) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P13 : WideCovered band 7954698 8105157 := wide_block_sound band profiles_RelativeWidePack6815_P13 7954698 8105157 (wideData 16 0x1182c07a9004abe00000000012fe0068a804abd80000000015aa84f2012af8000000000625805b404abe0000000001bd30063b404abe0000000001fff40a9ec04abd8000000000196fd03e77012af8000000080060868177c404abe0000000001c8f4228b404abe00000003012aedb46c298b3092af60000000000aedf86ede33092af80000000000a4b6807aae29424abe00000000009fac907ff1bc04abe0000000000f8f4a01db3a404abd8000000000e9b5ad3dfee404abe02e02e03f82e02e03f93ba9f8ff36e6470f9a2f2a) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P13 : WideCovered band 8105158 8359058 := wide_block_sound band profiles_RelativeWidePack6815_P13 8105158 8359058 (wideData 16 0xb29206a8a40064dee0000030001e8ca80e5cb1001937c02080080003e28bb95b292fbca064dee0000000001b6ce44ad960001937c0000000001bd75a059658683c1937b8000000000ee3aa02a368b2281937c00000000016f6b947ebc8e7101937b8000000000dba4b01abfc80064df0000000000621e61435965d4c064dee000000000074dedf03ababf1001937c00000000001f62cf6064e7ad3a641937b80000000015c23c47dedb404abe02080082001eb0cc6abdca4092af8000000000337e03822012af600000000037ed02d62012af80b80b80fe0b80b80fe62fbf0178deae0188fbe8e22) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P13 : WideCovered band 8359059 8659978 := wide_block_sound band profiles_RelativeWidePack6815_P13 8359059 8659978 (wideData 16 0x2e790ffa2001937b8000000000c97c3fbd80064df0000000000363e0eb6c001937b8000000000dae81b9e80064df000000000042990efb8001937b80000000012ab03b9d80064df000000000053c80ecb4001937b800000000188fc3ac880064df000000000072ae0e8b6001937b8000000000187e90de66001937c0000008201bcf41aeb80064dee0000000005a1a019fd001937c0000000000cfa4238b00064dee000000000473f06abc001937c00000000019fa00a1f00064dee0bc0bc0fe0ba0ba0fe5aa8741a6abbb8188ffeb834) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P13 : WideCovered band 8659979 8960898 := wide_block_sound band profiles_RelativeWidePack6815_P13 8659979 8960898 (wideData 16 0x4ab2901f3df40064dee0000000001aaae40fdb25001937c000000820059b5f18af0e42064dee0000000001fd8b91e4860001937c0000000000ec7e806ba9dc0064dee0000000001a6f73062a68cc2064df00820000007e9eab267862081937b80000000002aa8a16da3001937c00000000003b6df02d24d80064dee00000000012cb600abeea001937c00000000005db3b1be69001937b80000000008c3cb03bf4b40064df00000000003bb8b00b3977001937b80000000009c6ebc98788c0064df00820020802ba9bf17de79d06064dee0be0be0fe0be0be0fe7e69f01aca3ee01890c76e24) (by decide +kernel)
private theorem c9_RelativeWidePack6815_P13 : WideCovered band 8960899 9449894 := wide_block_sound band profiles_RelativeWidePack6815_P13 8960899 9449894 (wideData 16 0x6a8c01d658000a9bbe000000000778e01cffa000a9bbe0000000007f5d1ef64002a6ef800000000019efd01867f000a9bbe000000000073fa006a8ea002a6ef80000000002963e019719000a9bbe0000000000bd8f45b9cc00a9bbe00000000013fb3036b8400a9bbe00000208017ccf007de75002a6ef800000c3010fbdb02a23ced3c2a6ef82080082001b228311f6ee3081937b80000000001bb2b1f9f0001937c00000000001d7de14de2001937b80000000002963f01ba9f00064df00000000000b5e7406ff2c001937c03883883f83883883f819a7ae42a78b0881b91922bf4) (by decide +kernel)
private theorem c10_RelativeWidePack6815_P13 : WideCovered band 9449895 10051734 := wide_block_sound band profiles_RelativeWidePack6815_P13 9449895 10051734 (wideData 16 0x168f0a03affe000a9bbe18600618077de3d13cd6e8100a9bbe0000000006b9e03967d000a9bbe000000000626c02b76b800a9bbe0000000007a0e039f3a800a9bbe000000000060bac0eac2e002a6ef80000000002bb10eed32002a6ef82080082005ae50a4e64002a6ef80000000017ef00ad9ea002a6ef80000000019c780addfa002a6ef8000000001b8e40aadb8002a6ef8000000001af20078c68002a6ef800000000018a6e02c319000a9bbe000000000067be40b3e2c002a6ef80000000011ca50aa9f6002a6ef83983983f83983983f819fea6c222bfef018928e2a6a) (by decide +kernel)
private theorem c11_RelativeWidePack6815_P13 : WideCovered band 10051735 10653575 := wide_block_sound band profiles_RelativeWidePack6815_P13 10051735 10653575 (wideData 16 0x6b34a02f28f800a9bbe0000000000aed707a5c800a9bbe0000020802f7f64136dbf002a6ef8000000000dd70e8183b965082a6ef82080000001963ee3169968082a6ef80000000007a24c13bfb002a6ef8000000000db30d03d2ccc00a9bbe0000000002299fa4fc86f002a6ef82080082001864beb627962082a6ef80000000004dabd01d2db400a9bbe0000000001eda7c1bcea9002a6ef8000000000acb1c52d75ec20a9bbe00000208077bfe03f497f002a6f802080000001a7ba39066862ac20a9bbe0000000001acbfc06582a002a6ef83b83b83f83b83b83f81cb1fac3a0878b81c939f9e2a) (by decide +kernel)
private theorem c12_RelativeWidePack6815_P13 : WideCovered band 10653576 11368260 := wide_block_sound band profiles_RelativeWidePack6815_P13 10653576 11368260 (wideData 11 0xcf30f01fa4ca2004cbdf00000000009ea4d019a0cf4004cbdf02080082001bbea019bcbee004cbdf000000000058b4d0cd22800132f7c0000000001efa344ede3e004cbdf00000000004dfee11e27d40132f7c0000000002ac9bc061ea98c0132f7c08200208006ff2380dfaaeb66c4cbdf00000000002df3d04baca800a9bbe0000000000ebb2c0faf22002a6ef83d03d03f83d03d03f81b30c242bcb66901f14b319ec) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6553537 7663180 11368260 c0_RelativeWidePack6815_P13 (wide_covered_join band 7663181 7710199 11368260 c1_RelativeWidePack6815_P13 (wide_covered_join band 7710200 7743112 11368260 c2_RelativeWidePack6815_P13 (wide_covered_join band 7743113 7804237 11368260 c3_RelativeWidePack6815_P13 (wide_covered_join band 7804238 7954697 11368260 c4_RelativeWidePack6815_P13 (wide_covered_join band 7954698 8105157 11368260 c5_RelativeWidePack6815_P13 (wide_covered_join band 8105158 8359058 11368260 c6_RelativeWidePack6815_P13 (wide_covered_join band 8359059 8659978 11368260 c7_RelativeWidePack6815_P13 (wide_covered_join band 8659979 8960898 11368260 c8_RelativeWidePack6815_P13 (wide_covered_join band 8960899 9449894 11368260 c9_RelativeWidePack6815_P13 (wide_covered_join band 9449895 10051734 11368260 c10_RelativeWidePack6815_P13 (wide_covered_join band 10051735 10653575 11368260 c11_RelativeWidePack6815_P13 c12_RelativeWidePack6815_P13))))))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 13)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 13≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤50)
    (hT0 : 3720≤T) (hT1 : T≤4054) (hnu : 6553537≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤35424324682627447 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R080

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R081
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨13,51,3720,4027,36052282855491302⟩
private def profiles_RelativeWidePack6815_P13 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨29266,226,6051⟩
  | 4 => ⟨48248,360,10158⟩
  | 5 => ⟨24253,183,5079⟩
  | 6 => ⟨24348,181,5079⟩
  | 7 => ⟨29307,227,6051⟩
  | 8 => ⟨29103,225,5971⟩
  | 9 => ⟨24304,180,5079⟩
  | 10 => ⟨24296,184,5079⟩
  | 11 => ⟨24154,185,5079⟩
  | 12 => ⟨48205,359,10158⟩
  | 13 => ⟨24394,178,5079⟩
  | 14 => ⟨24196,186,5079⟩
  | 15 => ⟨24439,179,5079⟩
  | 16 => ⟨24526,177,5079⟩
  | 17 => ⟨24480,176,5079⟩
  | 18 => ⟨41768,250,10158⟩
  | 19 => ⟨24592,171,5079⟩
  | 20 => ⟨24799,165,5079⟩
  | 21 => ⟨24860,163,5079⟩
  | 22 => ⟨24970,162,5079⟩
  | 23 => ⟨24917,161,5079⟩
  | 24 => ⟨24970,159,5079⟩
  | 25 => ⟨25162,154,5079⟩
  | 26 => ⟨25200,152,5079⟩
  | 27 => ⟨25234,150,5079⟩
  | 28 => ⟨25324,149,5079⟩
  | 29 => ⟨25351,147,5079⟩
  | 30 => ⟨25436,146,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P13 : WideCovered band 6684608 7668040 := wide_block_sound band profiles_RelativeWidePack6815_P13 6684608 7668040 (wideData 16 0x661a018799c0134b80000000019e7c0689e5004d300000000006e0801b27d40134b80000000001932c01822800134c0000000001de38073833004d2e0000000007e9f01df8bc0134c00000000001a6eb19834004d2e000000000062f700a0b79004d300000000007e1e2d2e8fbab42134b800000000029289e55a2bf9ac2134c00000000002fb8909b7be40134b80000000005838ea4076d32f3c084d300c30030c0503009a3e0c30030c00fa801c2cd820aa9ee1c70071c00bcf01929a824b1ef00be0be1200be0be1200acd13be800df63ce0) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P13 : WideCovered band 7668041 7717924 := wide_block_sound band profiles_RelativeWidePack6815_P13 7668041 7717924 (wideData 16 0xd9ac7fa004d300000000004bf901aeae80134b8000000000ecb816fb00134c0000000000e8e40a0cc0134b8000000000e8f017ac40134b80000000016e75a05bf4aa6244d2e00000000013da37b419f692ca4c134c00000000002cb1a01c25ac0268f80000000002d35902df1fc0268f80000000004dbda6c066e33d2a1c9a3e000000000133d2c062aa9d07134b80000000005eaaf3d071f63c7f084d30000000000164e2427ff20089a3e000000000163eaff01b25cefc84268f80000000010e31c04ab1d320c4d2e0b40b41200b40b4120079c24810c6993630ed25a3e) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P13 : WideCovered band 7717925 7746429 := wide_block_sound band profiles_RelativeWidePack6815_P13 7717925 7746429 (wideData 16 0x1bb4a695bdef3002aa60820000000b3a24cc2f2af2c002aa8000000000228908c2c002aa600000000022ac08ae2002aa8000000000228f07a7c002aa80000000002eed1ede4002aa80000000001f5dbc0a6a7e8820aa98000000000bf7c943aefcbf382aa800000000033ed300eb924e0f134c000000000109b0372f80134b8000000001a9bce068278a0084d3000000000023eff80a18b2d0a134b8000000000cc281bbe00134c0000000000cb7c0f3e00134b80000000012ca4070d78004d300b40b41200b40b41200b5fa9a14fff8ea28ede6db6) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P13 : WideCovered band 7746430 7824818 := wide_block_sound band profiles_RelativeWidePack6815_P13 7746430 7824818 (wideData 16 0xf58b007ad71ec64b1e800000000029e08ed06adef9b5452c7c0000000000e4b60c01c668eca024b1f00000000006b68c05fbc8c0268f800000000089a2a01d7bdc0268f80000000001da6ac39b2833209a3c000000000439d3d1fcba7009a3e0000000005fbfbd339bb9009a3e000000000063b3cf4ad73c40268f80000000003dbdf71272b37f48268f800000020018289b027def3a89268f8000000000296cc750a89a1dc6134b80000000002939f7117dbe8cc2134c00000000005bbce310b6f68e40134b80000000003beaa34263a23f4f134c02d82d84802d82d0480bcb1aea067b21af060ee3eb28) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P13 : WideCovered band 7824819 7976846 := wide_block_sound band profiles_RelativeWidePack6815_P13 7824819 7976846 (wideData 16 0x74e3a1b6abd012c7a000000000064d2bc41c75ee9092c7c0000000800a6e63941d7ccb1192c7c0820020007f696e7bee37212c7c00000000006f8780b4b24012c7a000000000071e3c0accfe012c7c000000000360fe40b8a6890d4b1f0000000000696de0197ac3e112c7c000000000072ab406082c012c7a000000000077eb45e4f804b1f00000000001fb880ca76012c7c00000000007d8b40e1a21012c7c0000000000679f1063ea98454b1e80000000005e65c42dbdb71312c7c00000000012f8a8123abf012c7c0b60b61200b60b6120079cbdf13df2a7848efa5b60) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P13 : WideCovered band 7976847 8128874 := wide_block_sound band profiles_RelativeWidePack6815_P13 7976847 8128874 (wideData 16 0x32cc02f3e012c7a000000000374902ca6012c7c0000000003e290297c012c7c000000000438e01db6012c7c0000000004b9d018e8012c7a000000000568b0e9004b1f00000000018c2c07ed804b1f0000000201afb417ea804b1f0000000000eab4077d404b1e800000000119b80e8ac04b1f00000000014f3c1659404b1f00000000019efc1f6a404b1f0000000000183df0ba73012c7a00000000006ba64431dc04b1f000000030098f1d49ab9f3f092c7c0b80b81200b80b81205a7dec3e1d7cb0188f9eeab8) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P13 : WideCovered band 8128875 8394923 := wide_block_sound band profiles_RelativeWidePack6815_P13 8128875 8394923 (wideData 16 0x187bc05fe7001963d8000000000de2d765f000658f80000000000afe38768cc00658f600000300022efe80fdd79001963e02080080003ba79a15b3b26dca0658f6000000000173974335ba0001963e000000000018b5e3c1f0921c090658f6000000000627f2d1fae30ec80658f800000000023ecfc0aab61001963d8000000000cab0c0cf66a400658f80000000005bdd694f9878ac80658f60820020800b1da5d01aea9f0f930658f80c30030c04b18f01a5f24d434b1e82080082011fb3d469a3a68092c7c0000000002b6d05d74012c7c0b80b81200b80b81205bfee01769eed0190fc37a30) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P13 : WideCovered band 8394924 8698979 := wide_block_sound band profiles_RelativeWidePack6815_P13 8394924 8698979 (wideData 16 0x3288588fc001963d8208008200efa1060e78001963e00000000009fa033ae800658f60000000002b9c0cba0001963e0000000000beb03209800658f60000000003af815cba001963e0000000000ed742f4a000658f600000000043290b8ec001963e00000000012f7c2aac000658f60000000005f6816f72001963e0000000001a878277d800658f60000000007ebf08c2a001963e0000008201afec1be9800658f6000000000261b59c64001963e0000000000e9ac13cb000658f60bc0bc1200ba0ba1205a0ab41a3932e01910871bae) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P13 : WideCovered band 8698980 9003035 := wide_block_sound band profiles_RelativeWidePack6815_P13 8698980 9003035 (wideData 16 0x28f191ade3001963d80000000003875b01d36d800658f80000000000f5be40b7c6b001963d80000000003ef4e1792cec20658f8000002080223cf40ba9a1081963d80000000004baee44efec800658f8000000000572db02b19b1001963d800000c001adf7bcb9ba9400658f81040040800aff27166cf8e860658f6000000000328f18868001963e030c00c300c9b4d45beb8f9141963d80000000003eace018288800658f80000000001679200afe800658f60000000001f892007193f001963e0000000000d8aff04f32e400658f60e00e01200e00e01202eb9643238e6a01a10d23a7e) (by decide +kernel)
private theorem c9_RelativeWidePack6815_P13 : WideCovered band 9003036 9535134 := wide_block_sound band profiles_RelativeWidePack6815_P13 9003036 9535134 (wideData 16 0x1a72f02dbf8000aa9ee0000000004a4941dadf800aa9ee082002080764f42ca8b800aa9ee0000000005eba1c9ea002aa7b8000000001fab4074ab2002aa7b80000000001860911cbc002aa7b80000000001bb4c01ba49800aa9ee000000000077f640e39400aa9ee0000000000b7a64768f000aa9ee000000000124a2807e9fd002aa7b80000000008bacc01dfefc00aa9f0000000000224c3c0aecf9dcd0aa9ee0820020800649288449328c20658f6000000000067d7843cd800658f80000000000779600b0af0001963d838838848038838848019fad242a8f2e901b919b596e) (by decide +kernel)
private theorem c10_RelativeWidePack6815_P13 : WideCovered band 9535135 10143246 := wide_block_sound band profiles_RelativeWidePack6815_P13 9535135 10143246 (wideData 16 0x820000006f2aa223e97c082aa7b800000000078afb07ba6f400aa9ee0000000003b682c0ee92d002aa7b86180186010b35d45a76e24382aa7b800000000188e40e3e7c002aa7b80000000015ee40add7a002aa7b8000000001afb40e6bbc002aa7b800000000199640aef2a002aa7b8000000001fd740ec8b6002aa7b80000000004ca90b386c002aa7b82080082006f310bc920002aa7b80000000013e6c077de4002aa7b8000000001983c0aed38002aa7b80000000017dfc0768ae002aa7b8000000001ee3c0b19e2002aa7b8398398480398398480193b9a4223baef01912a29c6a) (by decide +kernel)
private theorem c11_RelativeWidePack6815_P13 : WideCovered band 10143247 10751358 := wide_block_sound band profiles_RelativeWidePack6815_P13 10143247 10751358 (wideData 16 0xb0cbc0e6b64002aa7b80000000002df5f01dfbcc00aa9ee0000000000e8d6c2269ad082aa7b800000000079a4802b6e8c00aa9ee0000020802b9ce00a0934002aa7b8000000000ebfcd04e22b400aa9ee082000000067d779578ee9420aa9ee000000000166cbc73da400aa9ee000000000234c601a7bf1002aa7b80000000013baba0493fd400aa9ee08200208006492ed4d9eab020aa9ee0000000000f4d74634dc00aa9ee00000000016eb38127e75002aa7b80000000007d2bf0187ce37082aa7b8000008200ab22a02a259400aa9ee0f00f01200ee0ee120466be8339baff81d13b6da2a) (by decide +kernel)
private theorem c12_RelativeWidePack6815_P13 : WideCovered band 10751359 11549505 := wide_block_sound band profiles_RelativeWidePack6815_P13 10751359 11549505 (wideData 12 0x2080082007ef68029b3a7e004d2ef00000000009b35901c758f0004d2ef00000000008e27d01abbb38004d2ef00000000008bb680192aff8004d2ef00000000008d7e81dae6b00134bbc00000000027f9f44fa9b4004d2ef0000000000ec65a19e3a004d2ef000000000019bcc640b08fe9c0134bbc08200208013e9b83eec7dc99134bbc00000000026eb09c7fd000aa9ee0000000000b2c751228a8002aa7b83d83d84803d83d84801ab38242b1ca5d81f14cb0fea) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6684608 7668040 11549505 c0_RelativeWidePack6815_P13 (wide_covered_join band 7668041 7717924 11549505 c1_RelativeWidePack6815_P13 (wide_covered_join band 7717925 7746429 11549505 c2_RelativeWidePack6815_P13 (wide_covered_join band 7746430 7824818 11549505 c3_RelativeWidePack6815_P13 (wide_covered_join band 7824819 7976846 11549505 c4_RelativeWidePack6815_P13 (wide_covered_join band 7976847 8128874 11549505 c5_RelativeWidePack6815_P13 (wide_covered_join band 8128875 8394923 11549505 c6_RelativeWidePack6815_P13 (wide_covered_join band 8394924 8698979 11549505 c7_RelativeWidePack6815_P13 (wide_covered_join band 8698980 9003035 11549505 c8_RelativeWidePack6815_P13 (wide_covered_join band 9003036 9535134 11549505 c9_RelativeWidePack6815_P13 (wide_covered_join band 9535135 10143246 11549505 c10_RelativeWidePack6815_P13 (wide_covered_join band 10143247 10751358 11549505 c11_RelativeWidePack6815_P13 c12_RelativeWidePack6815_P13))))))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 13)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 13≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤51)
    (hT0 : 3720≤T) (hT1 : T≤4027) (hnu : 6684608≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤36052282855491302 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R081

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R082
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨13,52,3720,3999,37279216348883173⟩
private def profiles_RelativeWidePack6815_P13 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨33072,8,10160⟩
  | 4 => ⟨29266,226,6051⟩
  | 5 => ⟨48205,359,10158⟩
  | 6 => ⟨24253,183,5079⟩
  | 7 => ⟨24348,181,5079⟩
  | 8 => ⟨24304,180,5079⟩
  | 9 => ⟨48056,364,10158⟩
  | 10 => ⟨24196,186,5079⟩
  | 11 => ⟨24296,184,5079⟩
  | 12 => ⟨48248,360,10158⟩
  | 13 => ⟨24394,178,5079⟩
  | 14 => ⟨24439,179,5079⟩
  | 15 => ⟨24480,176,5079⟩
  | 16 => ⟨41768,250,10158⟩
  | 17 => ⟨24799,165,5079⟩
  | 18 => ⟨24860,163,5079⟩
  | 19 => ⟨24917,161,5079⟩
  | 20 => ⟨24970,159,5079⟩
  | 21 => ⟨25162,154,5079⟩
  | 22 => ⟨25200,152,5079⟩
  | 23 => ⟨25234,150,5079⟩
  | 24 => ⟨25324,149,5079⟩
  | 25 => ⟨25351,147,5079⟩
  | 26 => ⟨25436,146,5079⟩
  | 27 => ⟨25456,144,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P13 : WideCovered band 6815679 7662856 := wide_block_sound band profiles_RelativeWidePack6815_P13 6815679 7662856 (wideData 16 0x18ea406effd004da00000000006a0e01cf29c0135f800000000018bec1aa3a004da000000000073c801eef8c01368000000000019a4e15c24004da0000000000060a700a4df7004da0000000000663a392a8bf7d4213680000000000283cc615e7a3acc2136800000000002dadb0ad28ac0136800000000004c70df0076e7fc60084da0000000000200004da00c30030c0503009b200000000000ed801c2ce024b8802080104001de0626b020aaffe0c300514073432390226bff80b60b61220b60b61220a8d13be000e96febc) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P13 : WideCovered band 7662857 7706055 := wide_block_sound band profiles_RelativeWidePack6815_P13 7662857 7706055 (wideData 16 0x5379b816fd2c805136800000000003ce5d418b6f31084da000000000012ac309419b7d6cfc6136800000000004bf3c2c067eb7cbe249afe0000000002fcf07deb004da00000000000ea879061ee6fc21368000000000049b3a018aa8fc0c4da0000000000127e66a419f69228c8136800000000004a65e2c067da3e30249b200000000003bad0cd2d004da00000000000e4c7d06386acc21368000000000148f437f88013680000000000dee7844aaeeb3084da0000000000575801968fc0136800000000016ce8068f25004da00b40b41220b40b41220a19fba14fa8bf030ecfb9b0) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P13 : WideCovered band 7706056 7740854 := wide_block_sound band profiles_RelativeWidePack6815_P13 7706056 7740854 (wideData 16 0x22bab5076eebf4b0ab800000000008f70801e218f2282ae000000000006787bb4a872e75242ae0000000000067de5d09ff78f8204d7e000000000066d7fa0aa23aa80c4da00000000002bdc079ee004da00000000002b8e03c62004da000000000042de01c61f8013680000000000bc6013cc0013680000000000b9ec4a1004da000000000046ad01c61c8013680000000000c96806fd8013680000000000befc12aec0136800000000012b20070fee004da000000000033a80396d004da00b40b41220b40b41220ac822e14faaa7230edafcae) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P13 : WideCovered band 7740855 7790053 := wide_block_sound band profiles_RelativeWidePack6815_P13 7740855 7790053 (wideData 16 0x22582c0b4d7f009b2000000000026aa330e8ebdeca26c8000000000119ae844c77ec026c80000000001a83f95883bb4026bf80000000002a3ca7522b8f4e4426c80000000000493a8351788a684b26c8000000000019aa974328c31a8826c800000002003ba2ab51a5b74fc21368000000000019e6dbd4779e5004da000000000053daf132a9b884d136800000000005e309fd1e1b2bd82136800000080010f31c6016cfa9302ae00820000000b5de9bc2be0bf2002ae00000000001efc07ffa002ae00000000001f1a07eac002ae00b40b41220b40b41220f8aaf81fabaaf828ee319ac) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P13 : WideCovered band 7790054 7938849 := wide_block_sound band profiles_RelativeWidePack6815_P13 7790054 7938849 (wideData 16 0x1a39e028339004b8800000000001abee01d38e004b7f80000000001b7c901a67c004b8800000000001c6ed1bd7a012e200000000000aac641a5ee0012e200000000002edcf00b4e21e0d4b7f80000000005da68018efc70092e200000000000a4e2c478b004b8800000000002aedd01b31cc04b8800000000008eee943f68d6d292dfe000000000135aa8061eb6012e20000000000167abc1f7ae3012e200000000003a9c2d2a4a749444b8800000000001b20ba5063d2793f252dfe0000000000b98a8f01ca99349874b8802d82d84882d82d8488fbb8b0faebae268eef8aaa) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P13 : WideCovered band 7938850 8092445 := wide_block_sound band profiles_RelativeWidePack6815_P13 7938850 8092445 (wideData 16 0x439e0ad404b8800000000013ee41e5c004b7f80000000015df80759404b88000000000198e00bbc404b880000000001e9e41a1c004b8800000002018ff016b9404b7f80000000017eec1f5fc04b880000000000b8a80e09804b88000000000018e3b0db77012e2000000000006ee244edd404b7f80000003009df3c49bb3c63092e200000000002bfae80f4c67012e200000000000ac8e61e5ce5012e200000000007e1de53e39ab012dfe0000000800b2d32c42efccf5112e200b80b81220b80b61220f98e3a92ee9b6a68f964aa2) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P13 : WideCovered band 8092446 8332439 := wide_block_sound band profiles_RelativeWidePack6815_P13 8092446 8332439 (wideData 16 0x20001aee788d3de8e75081970802080000003b76b360bf9efcc4065bfe000000000132ba016bc3e0019708000000000059a8c01820c00065bfe0000000001a893016e8e3001970800000000008926b10cb4b40065bfe0000000006698f13fbd61eca065c2000000000073aef4171eafc40065bfe08200208007afade01b638e7991065c20000000000231c02cb0012dfe00000000027d807eb2012e200000000002a3a0292c012e200000000002e1a01de8012e2000000000032a902ea8012dfe0000000003a0805fb2012e200b80b81220b80b81224ef8f0175e7af0180fbb0a7a) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P13 : WideCovered band 8332440 8639631 := wide_block_sound band profiles_RelativeWidePack6815_P13 8332440 8639631 (wideData 16 0xade847ba00065c200000000002f8f11ff800196ff8000000000be34222b80065c200000000003b0e11ef800196ff800000000109303f8800065c20000000000474808aba00196ff80000000015eac4a1880065c20000000000625803abc00196ff8000000001f964472e80065c20000002080666e128e800196ff80000000015cfc0b3840065c2000000000057443aa80065bfe0000000006eab03be3001970800000000019bfc62600196ff80000000012d641fb800065c200bc0bc1220ba0ba12243fa341a3964d8180ff77e6c) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P13 : WideCovered band 8639632 8946823 := wide_block_sound band profiles_RelativeWidePack6815_P13 8639632 8946823 (wideData 16 0x1638a006fa29001970800000000006bb0e1dab9fc2065bfe0000020803b9b3427200197080000000000b93b9c49f38c0065bfe1040020803ecd6b13f9b9c84065c2000000000026ba0fbaa00196ff8000000000baec634800065c200000000002e3b0fabc00196ff8000000000dc7c677800065c200000000003e191adae00196ff830c00c3003da2f05c788670c197080000000000ccf1a0886adc0065bfe08200208042cbe117c939b02065c200000000001fee5293600196ff8208008200fc7d7ab800065c200bc0bc1220bc0bc12267edec1a8c3d801810c2fe3c) (by decide +kernel)
private theorem c9_RelativeWidePack6815_P13 : WideCovered band 8946824 9388411 := wide_block_sound band profiles_RelativeWidePack6815_P13 8946824 9388411 (wideData 16 0x66b81e9f6002abff800000000018a5b01daca000aaffe0000000000669b4461b800aaffe000000000072d200efb000aaffe0000000000a8cf04fbec00aaffe0000000000fc8f0323f800aaffe00000000007bdf50a7e67c490aaffe00000000017bbac0fbaa900196ff8000000000a8b9d1dab100197080208008201fdbda49870942065bfe000000000067e34071e28001970800000000001c21b01fe1e80065bfe00000000006fca06bff40065c200000000000a4a28069f2a00196ff80000000002aff902c77dc0065c200e20e21220e20e21227acc702abdf1f019918e7e2c) (by decide +kernel)
private theorem c10_RelativeWidePack6815_P13 : WideCovered band 9388412 10002795 := wide_block_sound band profiles_RelativeWidePack6815_P13 9388412 10002795 (wideData 16 0x16c680e9cfa002abff80000000014c340b3ff2002abff80000000015e200b48f8002abff80000000017aec0b4db6002abff8000000001d9f40f29f8002abff80000000013fec0ba834002abff8208008201cf390b5ba2002abff80000000012c6007d8b0002abff80000000017a740b4bba002abff8000000001696007cdf6002abff80000000018e7007bfac002abff8000000001cb6007b92a002abff800000000018fcc02b65d800aaffe00000000022b802bf68800aaffe000000000062ead0a0df2002abff839839848839839848818329281fbeedf81811febdf4) (by decide +kernel)
private theorem c11_RelativeWidePack6815_P13 : WideCovered band 10002796 10617179 := wide_block_sound band profiles_RelativeWidePack6815_P13 10002796 10617179 (wideData 16 0x9cb49029a8e400aaffe0000020803b7f7c12edea002abff820800000018edf2572db3b082abff80000000004b35d03c289000aaffe00000000017ecec1f8aff002abff8000000000cc38d07d2ddc00aaffe082002080662df533fe74082abff80000000003871910bfe002abff80000000004a6cf02d25ac00aaffe00000000012ff780659f3cc20aaffe0000000004679742b9cf1002abff80000082019ab7ccccf3ec00aaffe082000000236c3f439ca1082abff800000000068efb03bed002abff8000000000ab6ac088749c00aaffe0ee0ee1220ee0ee1227a7ee83accf9a01a9393bdb4) (by decide +kernel)
private theorem c12_RelativeWidePack6815_P13 : WideCovered band 10617180 11577154 := wide_block_sound band profiles_RelativeWidePack6815_P13 10617180 11577154 (wideData 16 0xe8b5b02d3dca0004d7ff02080082003f2af01cb9b7a004d7ff00000000009a68c01d61b28004d7ff00000000006b21c1bbb4a00135ffc00000000023a830066b38a80135ffc0000000001ade740ece6e004d7ff0000000000c9b8c08c62900135ffc0000000004e8ab8128d3ab40135ffc082002080060c7ae13d338765c4d7ff00000000002ef6f02ba2002abff80000000004b7991cd36002abff80000000006f7fc07f208c00aaffe08200208047efe92a3bb3082abff830c00c3005eadc04e21d400aaffe0820020800a18a92e2be9082abff83d03d04883d03d0488187fd642bd9aaf81c94aabd74) (by decide +kernel)
private theorem c13_RelativeWidePack6815_P13 : WideCovered band 11577155 11730750 := wide_block_sound band profiles_RelativeWidePack6815_P13 11577155 11730750 (wideData 2 0x3fb8700e4fe8c80135ffc0fa0fa1220fa0fa1221628f8b01931de58818169e9d20) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6815679 7662856 11730750 c0_RelativeWidePack6815_P13 (wide_covered_join band 7662857 7706055 11730750 c1_RelativeWidePack6815_P13 (wide_covered_join band 7706056 7740854 11730750 c2_RelativeWidePack6815_P13 (wide_covered_join band 7740855 7790053 11730750 c3_RelativeWidePack6815_P13 (wide_covered_join band 7790054 7938849 11730750 c4_RelativeWidePack6815_P13 (wide_covered_join band 7938850 8092445 11730750 c5_RelativeWidePack6815_P13 (wide_covered_join band 8092446 8332439 11730750 c6_RelativeWidePack6815_P13 (wide_covered_join band 8332440 8639631 11730750 c7_RelativeWidePack6815_P13 (wide_covered_join band 8639632 8946823 11730750 c8_RelativeWidePack6815_P13 (wide_covered_join band 8946824 9388411 11730750 c9_RelativeWidePack6815_P13 (wide_covered_join band 9388412 10002795 11730750 c10_RelativeWidePack6815_P13 (wide_covered_join band 10002796 10617179 11730750 c11_RelativeWidePack6815_P13 (wide_covered_join band 10617180 11577154 11730750 c12_RelativeWidePack6815_P13 c13_RelativeWidePack6815_P13)))))))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 13)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 13≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤52)
    (hT0 : 3720≤T) (hT1 : T≤3999) (hnu : 6815679≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤37279216348883173 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R082

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R083
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨13,53,3720,3971,37260553836215299⟩
private def profiles_RelativeWidePack6815_P13 : ℕ → Profile
  | 0 => ⟨8268,2,2540⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨29266,226,6051⟩
  | 4 => ⟨48248,360,10158⟩
  | 5 => ⟨24253,183,5079⟩
  | 6 => ⟨24348,181,5079⟩
  | 7 => ⟨24304,180,5079⟩
  | 8 => ⟨24296,184,5079⟩
  | 9 => ⟨24154,185,5079⟩
  | 10 => ⟨48098,365,10158⟩
  | 11 => ⟨48056,364,10158⟩
  | 12 => ⟨48205,359,10158⟩
  | 13 => ⟨24394,178,5079⟩
  | 14 => ⟨24439,179,5079⟩
  | 15 => ⟨24480,176,5079⟩
  | 16 => ⟨42018,250,10158⟩
  | 17 => ⟨24860,163,5079⟩
  | 18 => ⟨24917,161,5079⟩
  | 19 => ⟨24970,159,5079⟩
  | 20 => ⟨25200,152,5079⟩
  | 21 => ⟨25234,150,5079⟩
  | 22 => ⟨25324,149,5079⟩
  | 23 => ⟨25351,147,5079⟩
  | 24 => ⟨25436,146,5079⟩
  | 25 => ⟨25456,144,5079⟩
  | 26 => ⟨25472,142,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P13 : WideCovered band 6946750 7666808 := wide_block_sound band profiles_RelativeWidePack6815_P13 6946750 7666808 (wideData 16 0x32383912af74dc2137c80000000015dac06fd33004df00000000005b8801cffbc0137c8000000001edbc633e00137c000000000199e807bf63004df2000000000061bfc4f8900137c0000000001c9a40a59b5004df2000000000679ef12ebfeae42137c00000000001df3a7157bf79942137c80000000002ab180ad69940137c00000000004921d68076c78a78084df00c30030c0503009be20000000000600004be9000000000038a4070b3808197ca02080104001c60626b020abe2e0b40b41240b20b21240bbd1fca400eb7c8ba) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P13 : WideCovered band 7666809 7710448 := wide_block_sound band profiles_RelativeWidePack6815_P13 7666809 7710448 (wideData 16 0x10eac06ed28004df20000000002f9906ca9004df00000000002f8a0b937004df20000000004b0f2016fbe0905137c00000000003ffeab5067eaa837204df2000000000120fff9019fad3bc8926f88000000000afb81f0840137c000000000038b58418e1de7084df20000000000fcc34063b6ad83137c00000000003eabffd067ef8ff5204df20000000000fbd358019fbd67a0926f80000000000dc243b8c40137c00000000002de2b418a3db3084df20000000000f6f70062962b83137c0000000000fd61945b70fbd104df20b40b41240b40b412407bdf7c14f2bc2028ed22fe0) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P13 : WideCovered band 7710449 7744390 := wide_block_sound band profiles_RelativeWidePack6815_P13 7710449 7744390 (wideData 16 0x6de81ebb000abe00000000006d781a7b800abe80000000009a747788800abe000000000018e7da12a1bf4cc20abe00000000005fbbd41ee1d77084df2000000000070cfd90e8eaa6c084df0000000000360b09aee004df200000000056dd601a08b9a82137c00000000007ab3902860ae6184df20000000002a5c04b2a004df0000000000279d01f67004df20000000003ef801c66e80137c0000000000ac34773004df00000000003f5a01b69f80137c0000000000ba600b3004df20b40b41240b40b41240a58eae14fbcfb828edb89b0) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P13 : WideCovered band 7744391 7809849 := wide_block_sound band profiles_RelativeWidePack6815_P13 7744391 7809849 (wideData 16 0x7ad8f43e3efda914be900000000004c39805df9b4026f800000000005e2cf01eb484026f8800000000079ecd09937dc026f8800000000078efec3867c3b309be20000000003fad694a2fff009be20000000005b38bd2a08b7009be20000000000a6ba8a49df7fa1109be20000000001bdf2c854ae3aa7249be200000000012ddfca1c93bd78189be000000008012c93af4697beb5084df000000000006c973854a32ec0137c80000000001be8ce5335abefc2137c0000000000297ea212bddf9b03137c8000008000e83f8e60e9864e420abe02d82d84902d02d04901ca39ec061badbb820ee38924) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P13 : WideCovered band 7809850 7965013 := wide_block_sound band profiles_RelativeWidePack6815_P13 7809850 7965013 (wideData 16 0x67eb1d429bab33112fa40000000800e4bade418b0bb1012fa20820020000b4cbac93cb5ecc4be9000000000018e98019e1e004be90000000000196fc1ac2a012fa40000000003bca20120b32e8d4be880000000001932906864012fa4000000000068bb41a7a404be90000000000aa6d843d7fdaf312fa40000000002a5cfc0b2fb6e0f4be880000000005ba5e018fdb38092fa4000000000224ebd0f7cfc9cc4be9000000000039b9905b2fec04be900000000003ffaf08a7ce404be880000000001fbcd01f61f35092fa40b60b61240b60b612406af28815ea886030ef68c76) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P13 : WideCovered band 7965014 8120177 := wide_block_sound band profiles_RelativeWidePack6815_P13 7965014 8120177 (wideData 16 0xb970764012fa4000000000361d079b8012fa200000000037bd02c804be900000000010a701e0f804be900000000011de4060a404be9000000000158781b6e804be880000000017ca80b3b404be90000000200cab01a4d004be900000000011ca0161cc04be900000000005b6c163a804be880000000019ab8264cc04be90000000000a9f40ba8804be900000000001a27810e77012fa40000000005aad038e3012fa20000000000ac864062fed012fa40b80b81240b80b61241f5db0174dbab8180f9b7cee) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P13 : WideCovered band 8120178 8382016 := wide_block_sound band profiles_RelativeWidePack6815_P13 8120178 8382016 (wideData 16 0x7abb03c7100197c980000000001efcd12bf700197ca000000c0005de3c02c60dc0065f260820020000bc9b9f578378e318197ca00000000003aa281bfe800197c980000000003cf4904eef8c0065f280000000001e08b4460a6800197c980000000005ce8813e70e40065f2800000000077ade5429a2cf4c065f260000000000eda393fb8f0a42065f280820020800be9f2801dfb9e9f95065f260000000001f7c07ae2012fa40000000001f9a028ea012fa4000000000261807ae0012fa2000000000267b01ca0012fa40b80b81240b80b81244a6d30173e6ef0180fc26d66) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P13 : WideCovered band 8382017 8692344 := wide_block_sound band profiles_RelativeWidePack6815_P13 8382017 8692344 (wideData 16 0x47895bd3200197c982080082010c539b000197ca00000000008e783b8b80065f26000000000274a0ed6800197ca0000000000ad203b0f00065f260000000002faf0eb6a00197ca0000000000da6037c880065f260000000003e3b0dafc00197ca00000000011b70336d00065f26000000000530c0cd3c00197ca00000000018c702f9a00065f260000000007a5c0bc7200197ca00000082014ee02a6d80065f260000000001bfa09baa00197ca0000000000b93c1bab80065f260bc0bc1240ba0ba1244348a01a0d2cd01810839828) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P13 : WideCovered band 8692345 9002672 := wide_block_sound band profiles_RelativeWidePack6815_P13 8692345 9002672 (wideData 16 0x1f64c0ccf200197c980000000002ba8808eff00197ca00000000003a79f01ae0dc0065f260000000000bffb46ea96d08197ca00000000008d77f09ef600197c9800000820099b18828629c0065f280000030005ebdfd2b0c3700197c984100102002a67d859f1bb808197ca000000000099e4533a00065f260000000002a0f14faa00197ca0000000000afe856ac80065f26000000000323e15f2200197ca0000000000dc2c5b0d00065f260000000003e7a17b2400197ca00000000007d2562de80065f260be0be1240be0be12457ca6c1a7f7cb01810cf78f8) (by decide +kernel)
private theorem c9_RelativeWidePack6815_P13 : WideCovered band 9002673 9506954 := wide_block_sound band profiles_RelativeWidePack6815_P13 9002673 9506954 (wideData 16 0x65ae007ef26002af8b80000000003f650a1938002af8b80000000001b2ef4296ac800abe2c08200208056ab018a38000abe2e0000000006fca1befe002af8b800000000018e1d14a74002af8b80000000001bb5b08bf6002af8b800000000028eab0c837002af8b80000000003b72901d3cf400abe2e0000000000a08a90a9bb38c70abe2e00000000016bf68167ced00197c980000000009bb9e0393ed40065f280820020807648b516d9f108197c980000000001935e01cf2f80065f2800000000006aaf806cd3600197c983883884903883884901834d342a9f75a819119b59e8) (by decide +kernel)
private theorem c10_RelativeWidePack6815_P13 : WideCovered band 9506955 10127610 := wide_block_sound band profiles_RelativeWidePack6815_P13 9506955 10127610 (wideData 16 0x5b5803ba2d000abe2e000000000627803c32d800abe2e0000000002e4d43d24b000abe2e0820020802f2b02dab8800abe2e0000000004a8e02cf39000abe2e0000000004ecf02d21d800abe2e00000000053bd02d619000abe2e0000000005b8f02db5c000abe2e000000000669d02e64f800abe2e00000000006e842f3aa800abe2e0820020802f8e42b3ce800abe2e0000000004a4b01fa2d800abe2e0000000004fdf01f73d000abe2e0000000005abb01f6c8000abe2e000000000675e01f6df800abe2e0e60e61240e60e6124761ba41fecb2c818129b4862) (by decide +kernel)
private theorem c11_RelativeWidePack6815_P13 : WideCovered band 10127611 10748266 := wide_block_sound band profiles_RelativeWidePack6815_P13 10127611 10748266 (wideData 16 0x177d7c0a5b6f002af8b82080082005cb4a4d9639c20abe2e000000000131c24168a26002af8b80000000006d78e04be9ec00abe2e0000000003b88a0072bff002af8b8208008201eb2ab55a28bc20abe2e0000000000ea930063e3a002af8b80000000004f398028ffbc00abe2e000000000237ae8275bab002af8b82080082012ba4b4dd2ba020abe2e0000000000aab28065b39002af8b80000000001ba2941d74af7082af8b80000000006f6f902be49000abe2e00000000033fda40f5f73002af8b80000000004ae1edcda5ac00abe2e0f00f01240f00f0124576f6a3a8f27e01a13b30a22) (by decide +kernel)
private theorem c12_RelativeWidePack6815_P13 : WideCovered band 10748267 11756832 := wide_block_sound band profiles_RelativeWidePack6815_P13 10748267 11756832 (wideData 16 0x8200208022bf200b7bae900137c3c0000000002ef8ac0aeb77b80137c3c0000000002aece00a482f900137c3c00000000027c8bc07ba69a00137c3c00000000016ed20074824c80137c3c0820020800e6eb0726c64004df0f00000000005929b10e76800137c3c00000000013fa742e7a00137c3c00000000016b868064e24cc0137c3c00000000007fbb4d11c3d968544df0f00000000007abbc04cf3bc00abe2e0820020804a0cb9439cbb082af8b80000000002b6c9028bdf000abe2e0000000000bd930127c3f002af8b8000000000593ba03a7dac00abe2e0f60f61240f60f61245659fc2a393dd01c94cacbe2) (by decide +kernel)
private theorem c13_RelativeWidePack6815_P13 : WideCovered band 11756833 11911995 := wide_block_sound band profiles_RelativeWidePack6815_P13 11756833 11911995 (wideData 2 0x5a98f4162cf7980137c3a0fc0fc1240fc0fc124167de0801aa2f3ad81816caa8bc) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6946750 7666808 11911995 c0_RelativeWidePack6815_P13 (wide_covered_join band 7666809 7710448 11911995 c1_RelativeWidePack6815_P13 (wide_covered_join band 7710449 7744390 11911995 c2_RelativeWidePack6815_P13 (wide_covered_join band 7744391 7809849 11911995 c3_RelativeWidePack6815_P13 (wide_covered_join band 7809850 7965013 11911995 c4_RelativeWidePack6815_P13 (wide_covered_join band 7965014 8120177 11911995 c5_RelativeWidePack6815_P13 (wide_covered_join band 8120178 8382016 11911995 c6_RelativeWidePack6815_P13 (wide_covered_join band 8382017 8692344 11911995 c7_RelativeWidePack6815_P13 (wide_covered_join band 8692345 9002672 11911995 c8_RelativeWidePack6815_P13 (wide_covered_join band 9002673 9506954 11911995 c9_RelativeWidePack6815_P13 (wide_covered_join band 9506955 10127610 11911995 c10_RelativeWidePack6815_P13 (wide_covered_join band 10127611 10748266 11911995 c11_RelativeWidePack6815_P13 (wide_covered_join band 10748267 11756832 11911995 c12_RelativeWidePack6815_P13 c13_RelativeWidePack6815_P13)))))))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 13)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 13≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤53)
    (hT0 : 3720≤T) (hT1 : T≤3971) (hnu : 6946750≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤37260553836215299 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R083
end MergedPart1
section MergedPart2
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R084
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨13,53,3750,3971,37326754903242029⟩
private def profiles_RelativeWidePack6815_P14 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨33072,8,10160⟩
  | 4 => ⟨24348,181,5079⟩
  | 5 => ⟨24253,183,5079⟩
  | 6 => ⟨24296,184,5079⟩
  | 7 => ⟨48205,359,10158⟩
  | 8 => ⟨48056,364,10158⟩
  | 9 => ⟨24304,180,5079⟩
  | 10 => ⟨24394,178,5079⟩
  | 11 => ⟨24439,179,5079⟩
  | 12 => ⟨42018,250,10158⟩
  | 13 => ⟨24860,163,5079⟩
  | 14 => ⟨24917,161,5079⟩
  | 15 => ⟨24970,159,5079⟩
  | 16 => ⟨25200,152,5079⟩
  | 17 => ⟨25234,150,5079⟩
  | 18 => ⟨25324,149,5079⟩
  | 19 => ⟨25351,147,5079⟩
  | 20 => ⟨25436,146,5079⟩
  | 21 => ⟨25456,144,5079⟩
  | 22 => ⟨25472,142,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P14 : WideCovered band 6946750 7734692 := wide_block_sound band profiles_RelativeWidePack6815_P14 6946750 7734692 (wideData 16 0x6c31e028798a2084df200000000022db04934004df0000000000339901c36f80137c80000000008fb813fd80137c00000000008d2006ab40137c8000000000dcfc07292c004df0000000000268b09bc0137c0000000000dceaa04bb2ef2084df00000000001ffe06b00137c830c00c3001bf0e70432d26882137c00000000008000137c8000000001000026f882080082002db4070d2e08197ca030c00c3001aec62a9020abe2e0820041005f8325902137c3c0b40b41240b20b212407aa13cba00eb7c8ba) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P14 : WideCovered band 7734693 7785605 := wide_block_sound band profiles_RelativeWidePack6815_P14 7734693 7785605 (wideData 16 0x5f7fac4a2bac026f88000000000ea2df43b70f69089be20000000004fcd65234efb009be20000000007ede393fb823009be20000000000f5b39b4af22af9209be20000000006e1afc2e6865f0926f8000000020048fad691ebb6bbc8137c0000000001682e9499a0b40137c8000000000befbee1222c64fc3137c00000000005be9de042cf78ac5137c8208008000da7b9f252af27f02137c00000000005f741f89800abe0000000001f9ee84a933d2b0c2afa0000000007f78602a2d6af82137c0000000000fa3c06bbfe004df20b40b41240b40b41240bec64a1fca8d2038ee27c78) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P14 : WideCovered band 7785606 7926222 := wide_block_sound band profiles_RelativeWidePack6815_P14 7785606 7926222 (wideData 16 0xd9baf04872f7e0d2fa400000000076fe12ef4012fa20000000000609a82278804be9000000000018f3f03e7d012fa4000000000067fb04aea404be900000000001ae9a418aee350d2fa2000000000139af80649f9e024be900000000007975a43e23be1092fa40000000000babfc166ae7012fa40000000000f0ca0222a2b012fa2000000000077b2007cfa4aca4be900000000005d7a848c73ce90d2fa40000000006b8e7c3e5da298b4be900000000003fefa05be4c4026f8000000000058abc01bf3ac026f882d82d84902d82d84907ced80fbf6aa250eeefdec) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P14 : WideCovered band 7926223 8081386 := wide_block_sound band profiles_RelativeWidePack6815_P14 7926223 8081386 (wideData 16 0x3f3b01d004be900000000012c681ff8804be880000000014e24066ac04be900000002008f781fb8004be90000000000dcf80e2bc04be900000000011907c6e012fa20000000004ece06973012fa40000000000b2c06d34012fa40000000007a790be79012fa400000000022fc03eb0012fa2000000000077db463a9404be90000000001faf01ef9c04be9000000030019edb2b32d9ebfc44be900000002002dfe8a9728a39012fa20820020000a9fe4c81863d2f092fa40b60b61240b60b612407cca8813fe9e6848f92bee0) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P14 : WideCovered band 8081387 8304434 := wide_block_sound band profiles_RelativeWidePack6815_P14 8081387 8304434 (wideData 16 0xbdb30062aa000197c980000000003979e04d31f40065f280000000001a5a7446dd7800197c980000000004f7ab13bb9fc0065f280000000006a8cf142b86edc2065f260000000000e09bd3fbaa19ca065f280820020800b2fe4b01e20ef0e11065f260000000001ba807e7a012fa40000000001bbb02ca8012fa40000000001feb07f2a012fa2000000000224a028f2012fa400000000026ec07fb6012fa400000000027ae01cb0012fa40000000002efe07ff6012fa2000000000326c1d9004be902e02e04902e02e0490eda0c05d29ee460fb7af38) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P14 : WideCovered band 8304435 8614762 := wide_block_sound band profiles_RelativeWidePack6815_P14 8304435 8614762 (wideData 16 0x26bb0f96600197c98000000000ab743e3f80065f280000000002f6a0ed6e00197c98000000000da743a8e00065f280000000003eae0de2000197c9800000000128a437c880065f28000000000573d0da2600197c98000000001aca036ba80065f28000002080429c0cbee00197c98000000000182032df80065f280000000000bdc0afa400197c980000000004aec2a4880065f280000000002b0a06b2200197c980000000015a286b000197ca00000000002a7de1ab7b00197c982f02f04902e82e8490bd30c068769f860ff21bec) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P14 : WideCovered band 8614763 8925090 := wide_block_sound band profiles_RelativeWidePack6815_P14 8614763 8925090 (wideData 16 0x1a18685edb2f08197c980000082008a6c981878f40065f280000000004a3ced1fcbaf00197c984100082014ab31639ecc02065f28000000000223e1593e00197c980000000008eb0571c00065f28000000000275b15ff000197c98000000000ad6c5b3a00065f280000000002fce17aae00197c98000000000db3c629a80065f28000000000276c59be000197c980000000010ea56e1c00065f28082002080423e5aeac00197c9800000000079303ec800065f280000000001f890fa6800197c982f02f04902f02f04913f73f069b1db4610bbfcbc) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P14 : WideCovered band 8925091 9351791 := wide_block_sound band profiles_RelativeWidePack6815_P14 8925091 9351791 (wideData 16 0x18c74771a000abe2e0000000007bbd16b34002af8b80000000001a62f0ba3e002af8b80000000001ee9808821002af8b8000000000382f801babac00abe2e000000000078b690a9cadcc70abe2e000000000137af813dab500197c980000000008ab3d02cbbcc0065f28082002080674d791e4f7f08197c980000000001829c01d79880065f28000000000065a7806f97600197c98000000000193ec01c62dc0065f28000000000075eb4428c00065f260000000000a4f34126a40065f280000000000bd968064dad00197c983883884903883884914ebe90aba5e7c71187ddac) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P14 : WideCovered band 9351792 9972446 := wide_block_sound band profiles_RelativeWidePack6815_P14 9351792 9972446 (wideData 16 0x108bc0b4da2002af8b800000000118b40b59ba002af8b80000000012afc0b6a60002af8b800000000148780b8862002af8b80000000016a3c0bad6a002af8b80000000004efd0bec68002af8b82080082006e290aab32002af8b8000000000ffbc07f96e002af8b80000000011c7807ee76002af8b80000000013d7807edba002af8b80000000016cf407efe0002af8b8000000001ae2c07fda6002af8b8000000000183ca02863c800abe2e000000000275c42920f800abe2e082002080062c750a0afe002af8b039039049039039049198bde07e24f6c611f64fec) (by decide +kernel)
private theorem c9_RelativeWidePack6815_P14 : WideCovered band 9972447 10593102 := wide_block_sound band profiles_RelativeWidePack6815_P14 9972447 10593102 (wideData 16 0x33fd305a99c00abe2e0820020806b88f15e2afd082af8b80000000002f6ec01aa3e800abe2e00000000012a86c07acf5002af8b80000000007d7ee099388c00abe2e082002080427ce93318b6082af8b8000000000286fe0183ec400abe2e0000000000ba8a413c923002af8b8000000000282c801b7ed23082af8b8000000000bba0a02f62d400abe2e0000000000fab7f6abb6d002af8b8618018600cda6bc4fe5932202af8b80000000013fa80efba0002af8b80000000015aac0f2860002af8b8000000000ea3d0f5db0002af8b83a83a84903a83a8491efe2908f76b386138e19aa) (by decide +kernel)
private theorem c10_RelativeWidePack6815_P14 : WideCovered band 10593103 11446504 := wide_block_sound band profiles_RelativeWidePack6815_P14 10593103 11446504 (wideData 16 0x128df4074ce2e00137c3c0820020800ebc78724970004df0f00000000004c358118f0980137c3c00000000012ca2c537f00137c3c000000000136ce0064b7dbc0137c3c000000000077efe911d36c30544df0f00000000006bb9904972a400abe2e0820020803fbd7147c86f082af8b80000000002924a029f1e800abe2e0000000000b2828121fbb002af8b80000000004c64e038228c00abe2e0820020803259693a4c39082af8b830c00c300283ed0a87b002af8b8208008200bb70424923082af8b80000000004823d05c3eb800abe2e0f40f41240f40f412462cfe42bdbe4f81994a3db6a) (by decide +kernel)
private theorem c11_RelativeWidePack6815_P14 : WideCovered band 11446505 11911995 := wide_block_sound band profiles_RelativeWidePack6815_P14 11446505 11911995 (wideData 6 0x4f3f24163faaf80137c3a000000000436fe812986eb80137c3c0820020801ebff40b7faca80137c3c0000000002a39b00af8f5b00137c3c000000000266ce80a4d2f800137c3c0fa0fa1240fa0fa1240e8a38a1ee25ce4615febfec) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6946750 7734692 11911995 c0_RelativeWidePack6815_P14 (wide_covered_join band 7734693 7785605 11911995 c1_RelativeWidePack6815_P14 (wide_covered_join band 7785606 7926222 11911995 c2_RelativeWidePack6815_P14 (wide_covered_join band 7926223 8081386 11911995 c3_RelativeWidePack6815_P14 (wide_covered_join band 8081387 8304434 11911995 c4_RelativeWidePack6815_P14 (wide_covered_join band 8304435 8614762 11911995 c5_RelativeWidePack6815_P14 (wide_covered_join band 8614763 8925090 11911995 c6_RelativeWidePack6815_P14 (wide_covered_join band 8925091 9351791 11911995 c7_RelativeWidePack6815_P14 (wide_covered_join band 9351792 9972446 11911995 c8_RelativeWidePack6815_P14 (wide_covered_join band 9972447 10593102 11911995 c9_RelativeWidePack6815_P14 (wide_covered_join band 10593103 11446504 11911995 c10_RelativeWidePack6815_P14 c11_RelativeWidePack6815_P14)))))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 13)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 13≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤53)
    (hT0 : 3750≤T) (hT1 : T≤3971) (hnu : 6946750≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤37326754903242029 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R084

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R085
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨13,54,3720,3942,37329975288252481⟩
private def profiles_RelativeWidePack6815_P14 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨29266,226,6051⟩
  | 4 => ⟨48056,364,10158⟩
  | 5 => ⟨24253,183,5079⟩
  | 6 => ⟨24348,181,5079⟩
  | 7 => ⟨24304,180,5079⟩
  | 8 => ⟨48205,359,10158⟩
  | 9 => ⟨48248,360,10158⟩
  | 10 => ⟨24154,185,5079⟩
  | 11 => ⟨24394,178,5079⟩
  | 12 => ⟨24439,179,5079⟩
  | 13 => ⟨42268,250,10158⟩
  | 14 => ⟨24860,163,5079⟩
  | 15 => ⟨24917,161,5079⟩
  | 16 => ⟨24970,159,5079⟩
  | 17 => ⟨25200,152,5079⟩
  | 18 => ⟨25234,150,5079⟩
  | 19 => ⟨25324,149,5079⟩
  | 20 => ⟨25351,147,5079⟩
  | 21 => ⟨25436,146,5079⟩
  | 22 => ⟨25456,144,5079⟩
  | 23 => ⟨25472,142,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P14 : WideCovered band 7077821 7668014 := wide_block_sound band profiles_RelativeWidePack6815_P14 7077821 7668014 (wideData 16 0x47de01b618c0139880000000012e24071b7b004e60000000000674a19828004e62000000000536f01e3cac013988000000001bee452dc8013988000000001787c0a1cbd004e620000000006eee1bfe9004e6200000000073d80183ec40139880000000001abbc31526f3cc4213988000000001cfaff4dbafda7084e620000000000f692ae01db5ae09821398830c00c30140c0272900000000001800013928000000000122b02a3388213987c0000000005e43239822728f80b60b61260b60b612607ac13be000e8e48e8) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P14 : WideCovered band 7668015 7707197 := wide_block_sound band profiles_RelativeWidePack6815_P14 7668015 7707197 (wideData 16 0x2a680bf3d004e6200000000042dabc16f9e29851398000000000099b0464004e620000000003ebf6516cfebf4413988000000001082ec05b6db36144e62000000000270d08877004e620000000000b696d062bb2ec2139880000000003b37c018b9cf00c4e620000000002add0cba3004e620000000000b1ae1061fe5c42139880000000003aa98018a5ebc0c4e620000000003ac8a916d8fa8c413988000000000f97bc05b3adf4144e620000000003a1abd16ceb7e4413988000000000c921b04aabbe20c4e620b40b41260b40b4126069cb2a10c6ab3030ed25afe) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P14 : WideCovered band 7707198 7741483 := wide_block_sound band profiles_RelativeWidePack6815_P14 7707198 7741483 (wideData 16 0x1a2d06b34002b3000000000017fb04d36002b32000000000176d740a6afba050acc00000000008de3f43ae393b082b320000000000f9dbc063c39a0213988000000001edfce0aa22938184e62000000000233f03f20004e620000000002e5e1ccb4004e620000000002b1f13b20004e62000000000236f039bd004e62000000000376c01bf3f00139880000000009a340eaec013988000000000dff006cdae004e6200000000027bf03c2f004e62000000000275909db1004e620b40b41260b40b412607cdbef14fe8b2228edb1f3c) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P14 : WideCovered band 7741484 7792910 := wide_block_sound band profiles_RelativeWidePack6815_P14 7741484 7792910 (wideData 16 0x5e6d902efdf40272900000000001db3d84a6694027290000000000bc71e43b2eea3209ca200000000043acf9234af9009ca4000000000671e7d3b6aab009ca40000000000b7e68e4aae2c7d109ca40000000004f99b82b3b7bf05272900000000001b67ced2e492f004e62000000080133c22f47aeefa5104e62000000000174efad42ea0f69004e62000000000079ef3a09e29e3d1c4e620000020002f5a63805fa6b78004e620000000003f2e6a07cc22b000acc02080000001b2bfad5afef8002b3200000000017c805e74002b300b40b41260b40b41260bfefea1fae8d3040ee32be6) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P14 : WideCovered band 7792911 7939846 := wide_block_sound band profiles_RelativeWidePack6815_P14 7792911 7939846 (wideData 16 0x2080000013f2fa4fff3f804e498000000001edb82b4c004e4a00000000001c299058a0b804e4a0000000000192290fbb5013928000000000077f3c134ff0013926000000000329d380f98a3c094e4a00000000009af5a43f71ae5213928000000000270df40b8bbfa8b4e4a00000000005820c42ea0d212939260000000000e7d340a5e340139280000000000e7bbc266d3301392800000000013d9e86fb8c04e4a0000000000b869f4ad27eaf11392600000000072ea783e9ff2a0d4e4a00000000003e6ba018a3fc0272902d82d84982d82d8498eef580faa2b3458eefe8e0) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P14 : WideCovered band 7939847 8096578 := wide_block_sound band profiles_RelativeWidePack6815_P14 7939847 8096578 (wideData 16 0xd8783af0139260000000003ec806b2c013928000000000470906ba80139280000000004f0b02a2501392800000008033df068200139260000000000a2a05f7e013928000000000463d05c77013928000000000128f04f60013928000000000161804cb00139260000000007b0e0ccff013928000000000331e1bb804e4a00000000010f34066cc04e4a00000000001aea9109710139260000000000e083006bfef0139280000000c00b1a25accdb383b1139280b80b81260b80b81260b6afca92a60fb058f966d34) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P14 : WideCovered band 8096579 8331675 := wide_block_sound band profiles_RelativeWidePack6815_P14 8096579 8331675 (wideData 16 0xbbeb46a7d40066a2e0820000000b083e957a6aa3b1019a8b80000000004d76e0ee3cf00066a2e0000000000bff603ebdff0019a8c00000000006aac805975880066a2e000000000778f2142d9e8a48066a30000000000463d60072bb1b40066a2e0820020800a4e2ab01a7283c90d066a300000000001b1c06d7e0139260000000001bce058f00139280000000001e9e039a6013928000000000229b06da8013928000000000261c06da201392600000000026d817a804e4a0000000000afb81b2e804e4a02e02e04982e02e0498f8a2c05c65bb668fbb8e2c) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P14 : WideCovered band 8331676 8645139 := wide_block_sound band profiles_RelativeWidePack6815_P14 8331676 8645139 (wideData 16 0x8d684ede80066a2e00000000023480aefe0019a8c00000000009cac2a9f00066a2e0000000002f8813fa20019a8c0000000000ca2c275a00066a2e0000000003bff129f00019a8c00000000010e782eaa80066a2e0000000004f7b07cfe0019a8c00000000019b305a2d80066a2e0000000007a68068b60019a8c00000082017ff00f4e00066a2e0000000002f3858a640019a8c00000000013ef46790019a8b8000000001edf81a6b40066a3000000000026ab56de60019a8b82f02f04982e82e8498da27a05f72eba68ff778a6) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P14 : WideCovered band 8645140 8958603 := wide_block_sound band profiles_RelativeWidePack6815_P14 8645140 8958603 (wideData 16 0x39acb02dbee40066a2e0000000000edd2472382b0819a8c000000000099acd0392cb40066a2e00000000013e93b2a1faf0019a8c000000020019e3ce91f5ff90019a8b8410010201ece5885d32faa0819a8c000000000088a4439c00066a2e000000000239e10e660019a8c0000000000ad746b3d00066a2e0000000002ba911bf40019a8c0000000000ca704e8800066a2e0000000003b8d1c97c0019a8c00000000001e794e4e00066a2e0000000005ae841877f80066a3000000000037ed568720019a8b82f82f84982f82f84993ee6a068f5a7a690c3ba76) (by decide +kernel)
private theorem c9_RelativeWidePack6815_P14 : WideCovered band 8958604 9350433 := wide_block_sound band profiles_RelativeWidePack6815_P14 8958604 9350433 (wideData 16 0x208008201ac71076ebe002b30f8000000001fff04fd9000acc3e0c30030c00f7f6c0a99ef002b30f82080082008d6bf42bb1f331c2b30f80000000001cb2b01ba1c80066a2e00000000007f9a8064d740019a8c00000000002cb6a16cee0019a8b80000000003ae5804be1fc0066a3000000000016ff300aeaed0019a8b80000000009d70b06938840066a3008200208072ac7d0ab9fd0819a8b8000000000182191dcae0019a8c0000000000196aa118fa0019a8b80000000001b3bb019280019a8c00000000001dfde15fe90019a8b83883884983883884999d23a0ab3db787918ffc66) (by decide +kernel)
private theorem c10_RelativeWidePack6815_P14 : WideCovered band 9350434 9977360 := wide_block_sound band profiles_RelativeWidePack6815_P14 9350434 9977360 (wideData 16 0x421f02ce3a000acc3e000000000463802cfcc000acc3e00000000043ce029bfd800acc3e0000000004bda02aedc800acc3e0000000005a8f02e2ac000acc3e00000000066b802f2ab000acc3e0000000003a2d42826d000acc3e0820020801b4f42a75f000acc3e000000000478a01fa7b800acc3e0000000004ffd01fb09000acc3e00000000052180186fd800acc3c0000000006e4901f61a000acc3e000000000061c2c07ea7c002b30f80000000001af0c02838f800acc3e000000000671b0fe2a002b30f839839849839839849959fcf07d63bb8691f638e0) (by decide +kernel)
private theorem c11_RelativeWidePack6815_P14 : WideCovered band 9977361 10604288 := wide_block_sound band profiles_RelativeWidePack6815_P14 9977361 10604288 (wideData 16 0x2a9a3c133d2d002b30f8000000000b9a1ddaeeffc00acc3e08200208026b923060e22082b30f800000000049a4e01c608000acc3e08200208026dc7907df60082b30f830c00c30079ada04a679c00acc3e0820020800f5ce9125c3e002b30f80000000001b20841ce493f082b30f80000000005bfbb19c76002b30f8000000000aaadb1dba4002b30f80000000008dacd8196edb3002b30f86180186015fa0ec5bed9be202b30f80000000013df00ec936002b30f800000000158f80eeea2002b30f80000000016f3c0f2ce4002b30f83a83a84983a83a8499db39d08db9c6c6938ebc7e) (by decide +kernel)
private theorem c12_RelativeWidePack6815_P14 : WideCovered band 10604289 11387947 := wide_block_sound band profiles_RelativeWidePack6815_P14 10604289 11387947 (wideData 16 0x1a7cb837fbfc004e61f0000000000b9b1d1a8fae8013987c00000000046deb00add2af4013987c082002080678b2c4acfefa1513987c0000000000aba600becf4002b30f80000000002ffc902cbb8400acc3e00000000016bdac6e9b400acc3e082002080375b754bbb39082b30f80000000001ea0b0e9b8002b30f80000000002be9f018bd8c00acc3e000000000122aa83e6b800acc3c0000000000fef25532ba5082b30f80000082010f30809ab7d400acc3e08200000057dae90eddeb082b30f80000000003ba3c02e23e800acc3e0f40f41260f40f412667fd3c2bfa3ab81a14a7483e) (by decide +kernel)
private theorem c13_RelativeWidePack6815_P14 : WideCovered band 11387948 12093240 := wide_block_sound band profiles_RelativeWidePack6815_P14 11387948 12093240 (wideData 9 0x6ffe7022696180013987a0820020804bfe68163ce9b0013987c0000000004aa9381378f9f8013987c00000000036a9680e98ada0013987c0000000003b5f7c0f3f25f0013987c0820020800ff86407bab298013987c0000000002368380a092cb0013987c0000000001a2d2c064825d0013987c0fa0fa1260fa0fa1260bed30f1c9648fc695efb932) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7077821 7668014 12093240 c0_RelativeWidePack6815_P14 (wide_covered_join band 7668015 7707197 12093240 c1_RelativeWidePack6815_P14 (wide_covered_join band 7707198 7741483 12093240 c2_RelativeWidePack6815_P14 (wide_covered_join band 7741484 7792910 12093240 c3_RelativeWidePack6815_P14 (wide_covered_join band 7792911 7939846 12093240 c4_RelativeWidePack6815_P14 (wide_covered_join band 7939847 8096578 12093240 c5_RelativeWidePack6815_P14 (wide_covered_join band 8096579 8331675 12093240 c6_RelativeWidePack6815_P14 (wide_covered_join band 8331676 8645139 12093240 c7_RelativeWidePack6815_P14 (wide_covered_join band 8645140 8958603 12093240 c8_RelativeWidePack6815_P14 (wide_covered_join band 8958604 9350433 12093240 c9_RelativeWidePack6815_P14 (wide_covered_join band 9350434 9977360 12093240 c10_RelativeWidePack6815_P14 (wide_covered_join band 9977361 10604288 12093240 c11_RelativeWidePack6815_P14 (wide_covered_join band 10604289 11387947 12093240 c12_RelativeWidePack6815_P14 c13_RelativeWidePack6815_P14)))))))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 13)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 13≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤54)
    (hT0 : 3720≤T) (hT1 : T≤3942) (hnu : 7077821≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤37329975288252481 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R085

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R086
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨13,54,3750,3942,37910004887150554⟩
private def profiles_RelativeWidePack6815_P14 : ℕ → Profile
  | 0 => ⟨33072,8,10160⟩
  | 1 => ⟨24348,181,5079⟩
  | 2 => ⟨24304,180,5079⟩
  | 3 => ⟨24253,183,5079⟩
  | 4 => ⟨24296,184,5079⟩
  | 5 => ⟨24154,185,5079⟩
  | 6 => ⟨48248,360,10158⟩
  | 7 => ⟨48205,359,10158⟩
  | 8 => ⟨24394,178,5079⟩
  | 9 => ⟨42268,250,10158⟩
  | 10 => ⟨24439,179,5079⟩
  | 11 => ⟨24860,163,5079⟩
  | 12 => ⟨24917,161,5079⟩
  | 13 => ⟨24970,159,5079⟩
  | 14 => ⟨25200,152,5079⟩
  | 15 => ⟨25234,150,5079⟩
  | 16 => ⟨25324,149,5079⟩
  | 17 => ⟨25351,147,5079⟩
  | 18 => ⟨25436,146,5079⟩
  | 19 => ⟨25456,144,5079⟩
  | 20 => ⟨25472,142,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P14 : WideCovered band 7077821 7741483 := wide_block_sound band profiles_RelativeWidePack6815_P14 7077821 7741483 (wideData 16 0x4e6d8029a8968102b300000000001f082d0ec921ac30acc800000000088f9a03aef9fc084e620000000004319a41a28beb02139880000000005d3ba02875af4084e620000000001eec04bb6004e62000000000275c1dab8004e62000000000264a148ba004e620000000001f1902d21004e620000000002fbb01c31b8013988000000000882c0b6dc013988000000000ece2a05c6efae084e620000000000b2b6d062febac21398830c00c3001a66f7c432d63b02139880000000010000272902d82d84982d82d84985e680e8db000eda8ab8) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P14 : WideCovered band 7741484 7792910 := wide_block_sound band profiles_RelativeWidePack6815_P14 7741484 7792910 (wideData 16 0x30028b52a6f2acc2272900000000001be7c83e638c0272900000000009ff3f43af5ee5309ca20000000003b1eb11effe5009ca40000000005a3a6d33f8a3009ca40000000000abf74c4a964df90c9ca4000000000463d302b28e2e022729000000000019e3fed222aaf004e620000000800fe827b4783782d0c4e6200000000013786ee42ae3deb004e62000000000165965d088b4ff7244e620000000001f9e7cb46efc966204e62082002000369c3eb81b26b2b242b30000000000163d07ab8002b32000000000162e069a8002b300b40b41260b40b41260b2f6bb1fc77f7e38ee32be6) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P14 : WideCovered band 7792911 7939846 := wide_block_sound band profiles_RelativeWidePack6815_P14 7792911 7939846 (wideData 16 0x2080080001c6fde53ab9fdece4e498000000001aca4336e804e4a00000000008ba4f02f27be04539280000000006e690d8b901392800000000017086d0b2a6bdd04e498000000000ad2eb03e7cdb635392800000000006583006dda7013928000000000060d21063d2adc54e4a00000000004a31e018ecd3e113926000000000179a7d0fbaea9cc4e4a00000000002e6fc08ff4f404e4a000000000049ffa119e3013928000000000271ca12b4ff6b434e49800000020018f2c346699e3f0d4e4a00000000016978239dc0272902d82d84982d82d04984bbdc05b67afa48eefe8e0) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P14 : WideCovered band 7939847 8096578 := wide_block_sound band profiles_RelativeWidePack6815_P14 7939847 8096578 (wideData 16 0xba6837a013926000000000369c07b740139280000000003e4c07d2201392800000000043c81dfc04e4a00000082009e301f2d804e4980000000001d711f9e804e4a0000000000cdb80eba404e4a000000000019ed1f59004e4a00000000001f252218804e4980000000015d30225ec04e4a0000000000ef06f3c0139280000000002a91ecf004e4a00000000010de40bc8404e4980000000001c66e14cb3013928000003000061f78271f404e4a02e02e04982e02d84986caeb05c6f96048f966d34) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P14 : WideCovered band 8096579 8331675 := wide_block_sound band profiles_RelativeWidePack6815_P14 8096579 8331675 (wideData 16 0x820000000a2f6d07592c0019a8b80000000012c600f5fc0066a2e000000000079ca2d578f3c3d0819a8b80000000002cbeb0f968d40066a3000000000016f838173ab60019a8b80000000019e23b50be7d333019a8c0000000000ee74e01c69c690019a8b82080082001eeeff0069db5c723c19a8c00000000005d641e49004e4980000000005fe0172b004e4a00000000006aa40f68004e4a000000000079701e89804e4a00000000007eac1e9d004e498000000000892806bd804e4a00000000009bf01eab804e4a02e02e04982e02e0498d83de05ca686248fbb8e2c) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P14 : WideCovered band 8331676 8645139 := wide_block_sound band profiles_RelativeWidePack6815_P14 8331676 8645139 (wideData 16 0x1eff148300019a8b80000000007bb42eed00066a3000000000022980afb20019a8b8000000000a964537c00066a300000000002b3b0abf80019a8b8000000000cfe04e7f80066a300000000003b190cbb40019a8b800000000118a023ed00066a3000000000057ee17e720019a8b8000000001a8f0223f80066a300000020804b6b06a6a0019a8b80000000012fb96ff800066a30000000000272904ae00019a8b8000000000ec6c07ce80066a30000000000066d25065b220019a8b82f02f04982e82e8498db23905f70f3c48ff778a6) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P14 : WideCovered band 8645140 8958603 := wide_block_sound band profiles_RelativeWidePack6815_P14 8645140 8958603 (wideData 16 0xb8c700b086b0019a8b80000000002fba91bef3ac2066a300000000001fecf00b0bfb0019a8b80000000004a38fc8dfe840066a300000000807aeabd0ebaf30019a8b841001020178b6e85ba19b61019a8c00000000006fe846af80066a2e0000000001f3e11b260019a8c000000000099ec6eae00066a2e00000000026bb129e00019a8c0000000000ad2c522c80066a2e000000000338e1d97a0019a8c00000000003fb5527980066a2e0000000006648418e2f80066a300820020802b7a54b7c0019a8b82f02f04982f02f04991b2490693cebc490c3ba76) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P14 : WideCovered band 8958604 9350433 := wide_block_sound band profiles_RelativeWidePack6815_P14 8958604 9350433 (wideData 16 0x8200208072d06a82c002b30f8000000001bd685a2a000acc3e0000000000628b87aa9400acc3e00000000016aa2d0b09eeac90acc3e00000000006bdf4071bbe0019a8b80000000001db5801a3ea00066a300000000000a7c34726a00066a2e0000000000bcd74127ea90019a8c00000000004e248028af940066a2e00000000022bd7c16feb90019a8c02080082018c21d44a30842066a2e0000000006f6d1fdf60019a8c00000000001828e13d320019a8b800000000019b9c049660019a8c00000000001c2bf129ab0019a8b83883884983883884996968f0abb4ebe6118ffc66) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P14 : WideCovered band 9350434 9977360 := wide_block_sound band profiles_RelativeWidePack6815_P14 9350434 9977360 (wideData 16 0x37cb02d268000acc3e0000000003b9902d61b800acc3e0000000003b3d02a24a000acc3e00000000042bc02b36b800acc3e0000000004e8c02e7ad800acc3e00000000057db02fa19800acc3e000000000473f4287fa000acc3e08200208027d0a6c2c002b30f8000000000faec07fb7c002b30f80000000011a6807feea002b30f80000000011aac062ee0002b30f00000000017bb807eefe002b30f8000000001cff00a0caa002b30f80000000001974a028f78800acc3e00000000047fb13c6a002b30f83983984983983984992c24b07dafae0491f638e0) (by decide +kernel)
private theorem c9_RelativeWidePack6815_P14 : WideCovered band 9977361 10604288 := wide_block_sound band profiles_RelativeWidePack6815_P14 9977361 10604288 (wideData 16 0x8f39803f6cbc00acc3e000000000275d6f636c33002b30f820800820088b6cc2c349c20acc3e0000000000f483807a8a0002b30f82080082008939e41a718020acc3e0c30030c00bcba80a49f7002b30f820800820058fc0a896c002b30f800000000019a1e41ce7923082b30f80000000004e2380196df000acc3e00000000023de30073e32002b30f80000000007c38e818f382d002b30f86180186012fe58c5b34f3a282b30f800000000118a80edbea002b30f80000000012a2c0f09f8002b30f80000000013e780f4936002b30f83a83a84983a83a84999b75b08e398f04938ebc7e) (by decide +kernel)
private theorem c10_RelativeWidePack6815_P14 : WideCovered band 10604289 11387947 := wide_block_sound band profiles_RelativeWidePack6815_P14 10604289 11387947 (wideData 16 0x5b33d0eb3fb8013987c0000000002768e46bc8a2004e61f0000000000f8aeb02b2ed3b004e61f02080082016a3fc12bb79765c4e61f00000000002863b038f6b800acc3e0000000000b2f700acaf7002b30f80000000004d2ff0fda5002b30f8208008200beaa853e3ecc20acc3e0000000000729704a49800acc3e0000000000a4cbc771cc00acc3e0000000000f0db86209800acc3c000000000138efd525ba9082b30f8000008200eb748088e9d400acc3e0000000003fdfff3b19b1002b30f82080000001bf3f8bee59020acc3e0f40f41260f40f41265afa342e1860c81894a7483e) (by decide +kernel)
private theorem c11_RelativeWidePack6815_P14 : WideCovered band 11387948 12093240 := wide_block_sound band profiles_RelativeWidePack6815_P14 11387948 12093240 (wideData 9 0x5f9a20228a29e0013987a08200208043b938164d73d0013987c0000000003fafa0138aeda8013987c0000000002f0cac0e9fe6d8013987c000000000336b780f4efdf8013987c0820020800edef807bce4f0013987c0000000001f0bb00a0de5c0013987c000000000168ab8064b6ab8013987c0fa0fa1260fa0fa1260b1ee8c1caf0e22495efb932) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7077821 7741483 12093240 c0_RelativeWidePack6815_P14 (wide_covered_join band 7741484 7792910 12093240 c1_RelativeWidePack6815_P14 (wide_covered_join band 7792911 7939846 12093240 c2_RelativeWidePack6815_P14 (wide_covered_join band 7939847 8096578 12093240 c3_RelativeWidePack6815_P14 (wide_covered_join band 8096579 8331675 12093240 c4_RelativeWidePack6815_P14 (wide_covered_join band 8331676 8645139 12093240 c5_RelativeWidePack6815_P14 (wide_covered_join band 8645140 8958603 12093240 c6_RelativeWidePack6815_P14 (wide_covered_join band 8958604 9350433 12093240 c7_RelativeWidePack6815_P14 (wide_covered_join band 9350434 9977360 12093240 c8_RelativeWidePack6815_P14 (wide_covered_join band 9977361 10604288 12093240 c9_RelativeWidePack6815_P14 (wide_covered_join band 10604289 11387947 12093240 c10_RelativeWidePack6815_P14 c11_RelativeWidePack6815_P14)))))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 13)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 13≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤54)
    (hT0 : 3750≤T) (hT1 : T≤3942) (hnu : 7077821≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤37910004887150554 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R086

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R087
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨13,55,3700,3912,49009564034460501⟩
private def profiles_RelativeWidePack6815_P14 : ℕ → Profile
  | 0 => ⟨8268,2,2540⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨260066,55,81717⟩
  | 4 => ⟨24253,183,5079⟩
  | 5 => ⟨29266,226,6051⟩
  | 6 => ⟨24296,184,5079⟩
  | 7 => ⟨29307,227,6051⟩
  | 8 => ⟨24154,185,5079⟩
  | 9 => ⟨48056,364,10158⟩
  | 10 => ⟨48205,359,10158⟩
  | 11 => ⟨48248,360,10158⟩
  | 12 => ⟨24196,186,5079⟩
  | 13 => ⟨24304,180,5079⟩
  | 14 => ⟨24394,178,5079⟩
  | 15 => ⟨24439,179,5079⟩
  | 16 => ⟨42518,250,10158⟩
  | 17 => ⟨24912,164,5079⟩
  | 18 => ⟨24860,163,5079⟩
  | 19 => ⟨24917,161,5079⟩
  | 20 => ⟨25162,154,5079⟩
  | 21 => ⟨25200,152,5079⟩
  | 22 => ⟨25234,150,5079⟩
  | 23 => ⟨25324,149,5079⟩
  | 24 => ⟨25351,147,5079⟩
  | 25 => ⟨25436,146,5079⟩
  | 26 => ⟨25456,144,5079⟩
  | 27 => ⟨25472,142,5079⟩
  | 28 => ⟨25549,141,5079⟩
  | 29 => ⟨25624,140,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P14 : WideCovered band 7208892 7649360 := wide_block_sound band profiles_RelativeWidePack6815_P14 7208892 7649360 (wideData 16 0xf80f8003e03e00706d80063db20b30b3002cc2cc076ae12f2e9020a7b6600000000000000200000000000000400000000000000a000000000000014000000000000001a000000000000000ae000000000000013a80000000000000066d000000000040000ada8000000000800013ad030c00c30140c0275980000000002cb80709f40819b4e00000000001a6c623e820ada6e0b60b61280b60b61280af81fbaa00eaea9e6) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P14 : WideCovered band 7649361 7715630 := wide_block_sound band profiles_RelativeWidePack6815_P14 7649361 7715630 (wideData 16 0xfcb2fa41b228accc712ee8000000001df38909fe8ca8108f740000000000a4a60174f64008f760000000000beda2f0187f9a4b8223dd0000000000fbe0072e28004bba000000000168cb10a6db98c512ee80000000002d3b931060864eed088f740000000000ab8700a1d2a008f760000000000addac7fde8023dd00000000002c60903a7b008f760000000000b4df406dda5008f740000000000b68239018a58f598223dd800000000118f872dbc012ee8f3c03cf001c2eb3452586288212ee95540555005817008f740f60f61280f60f6128063fe85a4baa18ecee82a) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P14 : WideCovered band 7715631 7745337 := wide_block_sound band profiles_RelativeWidePack6815_P14 7715631 7745337 (wideData 16 0x164da0d42c74db30029ec0820020001f0aaca81d2bf691029ee0000000007a3af827cce1b030a7b80000000005f702f1e800a7b80000000005ebc2a09800a7b0000000001dd2e849fbe96d0829ee0000000003b2e0ed30004bba000000000063b39d0c963966084bba0000000002f2f158fa004bba0000000002f6e13de4004bba0000000005f8b681fe875a0812ee80000000008cf4268c8012ee8000000000c9b406f8ee004bbc00000000026fe0eaa2004bba000000000266e08cb8004bba0b40b41280b40b412807b8a0c14f3db2820ede2876) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P14 : WideCovered band 7745338 7813891 := wide_block_sound band profiles_RelativeWidePack6815_P14 7745338 7813891 (wideData 16 0xaa7490febfac047ba00000000016e76c0ee3ccea551eea00000000012bb6c134a35008f7400000000016ebec1a2f25008f7400000000006adff0e58a5fc223dd0000000000b93b84bab9e4023dd8000000000f865b429b9ac023dd00000000017931a55faecc023dd00000000002a38c712698e6bd223dd0000000000b8ffe6506592bb3d448f760000000001b6c63c019e9b27f1023dd00000000004979d21073cbdfc012ee80000002006cabde1167db0ac512ef00000000001f77928060d7b98012ee8000000000befbb380b0df6c490a7b02d82d84a02d82d04a05aa7faa063ae4cba50ee39ee0) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P14 : WideCovered band 7813892 7960140 := wide_block_sound band profiles_RelativeWidePack6815_P14 7813892 7960140 (wideData 16 0xe8d24070efb011ee8000000000128cf5ccda7fd2d111eea0820020000b4aa799d9e8b4247ba000000000019b6c04cb4b8047ba8000000001bde80fddc047ba0000000000ca32c03f668260d1eea0000000006ed8119fd011eea000000000067c300b1a6c011eea0000000000628f4067bf5011ee8000000000066a2007f833011eea0000000000778a807be24011ee80000000006b2e419278610d1eea0000000000f0c790b196c9c447ba00000000002eb1b088f1e4047ba800000000049adb14a71011ee80b60b61280b60b6128062ca8b13c7cf2e68ef6faf0) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P14 : WideCovered band 7960141 8106389 := wide_block_sound band profiles_RelativeWidePack6815_P14 7960141 8106389 (wideData 16 0x2ae901fba011ee80000000002f6902d34011eea00000000036de06ea6011ee80000000003b5c01832011eea000000000468908962011ee8000000080269e0a80047ba80000000002ab122e88047ba8000000000982c52d011eea00000200006f805ca0011ee80000000001f280192e011eea0000030003ee9048a7011ee80000020000a6e48e32011eea0000000005e0907f6f011ee80000000006ed229b0047ba800000c0001a2a910d35011ee80b80b81280b80b612823cb2016dbe3c0180f9ad822) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P14 : WideCovered band 8106390 8362325 := wide_block_sound band profiles_RelativeWidePack6815_P14 8106390 8362325 (wideData 16 0xc301dc25727e00063db2082002080263c098f80018f6d00000000010ff416d800063db200000000052e9048260018f6c8000000001997c0a3b80063db20000000007fdd12a40063db2000000000069e702248c0063db20000000000709a2955dace3d1018f6c80000000009cb2907830e40063db20000000001a2b3942e9f8942063db4000000000070d2db06af5c3d0018f6c82080082007d31941b60820e07063db20000000001e6e02ca6011ee8000000000229b07c78011eea000000000232e02a70011ee80b80b81280b80b81283aebf416ebb5b8180fbead34) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P14 : WideCovered band 8362326 8654823 := wide_block_sound band profiles_RelativeWidePack6815_P14 8362326 8654823 (wideData 16 0x6a6c1e7980063db20000000001f3c0ea7e0018f6d00000000008ae83ac980063db2000000000267a0ebee0018f6c8000000000aa6c3b3e00063db20000000002f390ee720018f6c8000000000d9e03e1b00063db20000000003b6808d2c0018f6c80000000011bac2a0d80063db200000000056bb0f9aa0018f6d0000008200fa283f7f00063db200000000017e850c720018f6c800000000089e9478a00063db20000000002fcc53d740018f6c800000c30129b55bec00063db20bc0bc1280bc0bc1283fcfec178c36f0180fff0afc) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P14 : WideCovered band 8654824 8947321 := wide_block_sound band profiles_RelativeWidePack6815_P14 8654824 8947321 (wideData 16 0x3caef048bf0018f6c80000000004a2dd16967bc2063db400000208012eb202659c0063db20000000001a2e71164ca40018f6c8208000000f87fb49c2da80063db200000000057a952ee4842063db2000000000069ea452ec80063db20000000000e1bfc4a7c2a0c18f6c800000000119684bab310818f6c82080082006dfaa04fbe9e00818f6d0000000000b8b056fc80063db200000000032e916ba00018f6c8000000000ae695f4b00063db20000000003f9a599620018f6c820800820118b56a0f80063db20bc0bc1280bc0bc1284bec7017ff33f81810c6bd60) (by decide +kernel)
private theorem c9_RelativeWidePack6815_P14 : WideCovered band 8947322 9422630 := wide_block_sound band profiles_RelativeWidePack6815_P14 8947322 9422630 (wideData 16 0x436b01a7fc000a7b640000000004e6f019e8c800a7b6600000000053af0eeac0029ed90000000001ccf4063db20029ed900000000001969c01862d800a7b64000000000071a600f1f400a7b660000000000ade6c0ad9400a7b6400000000012bdf83bae400a7b6400000208022fdec0bafeb0029ed90208000001ac77f42fa4dbb1c29ed98000000001abf4367f00063db2000000000064cbc0a987e0018f6c8000000000192df07daf0018f6c80000000001b2ba1ccf50018f6c80000000001fefe01b76980063db20e20e21280e20e21285b8c302a592ec019918e6fa4) (by decide +kernel)
private theorem c10_RelativeWidePack6815_P14 : WideCovered band 9422631 10007626 := wide_block_sound band profiles_RelativeWidePack6815_P14 9422631 10007626 (wideData 16 0x6180186013d76f45aeafe02029ed90000000000e9bc0acc620029ed98000000000da7007c8fc0029ed90000000000ffb40aca7a0029ed900000000011cf80b0da40029ed900000000013bf00b3f240029ed980000000007901fade000a7b640820020803a2f42a649800a7b6400000000037fb01f20b000a7b640000000003e8f01f3a8000a7b660000000003b7e019ffc000a7b640000000004e0e01fa1c000a7b6400000000057ff028298000a7b640000000006a58028f8f000a7b6600000000007f9419fed800a7b640e60e61280e60e61285a8d7c1eddfea8181286aff0) (by decide +kernel)
private theorem c11_RelativeWidePack6815_P14 : WideCovered band 10007627 10592622 := wide_block_sound band profiles_RelativeWidePack6815_P14 10007627 10592622 (wideData 16 0x820020800fbde91259620029ed900000000001c67911ee00029ed98000000001e821063d6aec20a7b640000000000ec8fc5a5fc00a7b6400000000017ec30121e7e0029ed90000000000b9b2f0bce19c00a7b660820020805beae9221e2a0829ed9000000000028ba802ca7a400a7b640000000000effec176e800a7b6400000000017693c0f8f290029ed98208008200fc64c55ae4f420a7b640000000000a49a4133a7c0029ed9000000000029be802def8c00a7b640000000000f8c2c469a800a7b660000000000ea96c070faadc20a7b640ee0ee1280ee0ee1285bddac36ff2ca01a13961c78) (by decide +kernel)
private theorem c12_RelativeWidePack6815_P14 : WideCovered band 10592623 11470116 := wide_block_sound band profiles_RelativeWidePack6815_P14 10592623 11470116 (wideData 16 0x3aef916cb480012eeaa000000000126c20730e72004bbaa00000000003af8c10da498012eeaa000000000138c20627d22004bbaa00000000004caad08ca4d8012eeaa0820020800e6b3147686a004bbaa030c00c301cc7d918d71a4012eeaa0000000002b0f3e26893c99712eea808200208017c86f0afa760829ed9000000000039a2b03dedc000a7b66000000000133ba40bae770029ed90000000000987fc09db1c400a7b64082002080530de126f8710829ed9000000000029b7801b7ea800a7b660000000000e3aac1afec00a7b640f40f41280f40f4128574aa82a4aeac01c94a38920) (by decide +kernel)
private theorem c13_RelativeWidePack6815_P14 : WideCovered band 11470117 12274485 := wide_block_sound band profiles_RelativeWidePack6815_P14 11470117 12274485 (wideData 11 0x1fbe0b84c39f75004bbaa02080082001e62bbb0608e094212eeaa082002080060c34b43bbd92f084bbaa0618018600883ad459a8bec584bbaa8000000000c836c039e8ba2004bbaa00000000009977e02b27a3a004bbaa8208008200687de029a3c20004bbaa00000000005e6da01baaaa0004bbaa80000000006c78f01d31a36004bbaa000000000059b7b019a5fe4004bbaa83e83e84a03e83e84a02b2bdb85e5eade01816831b30) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7208892 7649360 12274485 c0_RelativeWidePack6815_P14 (wide_covered_join band 7649361 7715630 12274485 c1_RelativeWidePack6815_P14 (wide_covered_join band 7715631 7745337 12274485 c2_RelativeWidePack6815_P14 (wide_covered_join band 7745338 7813891 12274485 c3_RelativeWidePack6815_P14 (wide_covered_join band 7813892 7960140 12274485 c4_RelativeWidePack6815_P14 (wide_covered_join band 7960141 8106389 12274485 c5_RelativeWidePack6815_P14 (wide_covered_join band 8106390 8362325 12274485 c6_RelativeWidePack6815_P14 (wide_covered_join band 8362326 8654823 12274485 c7_RelativeWidePack6815_P14 (wide_covered_join band 8654824 8947321 12274485 c8_RelativeWidePack6815_P14 (wide_covered_join band 8947322 9422630 12274485 c9_RelativeWidePack6815_P14 (wide_covered_join band 9422631 10007626 12274485 c10_RelativeWidePack6815_P14 (wide_covered_join band 10007627 10592622 12274485 c11_RelativeWidePack6815_P14 (wide_covered_join band 10592623 11470116 12274485 c12_RelativeWidePack6815_P14 c13_RelativeWidePack6815_P14)))))))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 13)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 13≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤55)
    (hT0 : 3700≤T) (hT1 : T≤3912) (hnu : 7208892≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤49009564034460501 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R087

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R088
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨13,56,3700,3882,49074482642422725⟩
private def profiles_RelativeWidePack6815_P14 : ℕ → Profile
  | 0 => ⟨8268,2,2540⟩
  | 1 => ⟨33072,8,10160⟩
  | 2 => ⟨260066,55,81717⟩
  | 3 => ⟨24253,183,5079⟩
  | 4 => ⟨29307,227,6051⟩
  | 5 => ⟨24348,181,5079⟩
  | 6 => ⟨29266,226,6051⟩
  | 7 => ⟨24296,184,5079⟩
  | 8 => ⟨48248,360,10158⟩
  | 9 => ⟨48056,364,10158⟩
  | 10 => ⟨48205,359,10158⟩
  | 11 => ⟨24154,185,5079⟩
  | 12 => ⟨24304,180,5079⟩
  | 13 => ⟨24439,179,5079⟩
  | 14 => ⟨24394,178,5079⟩
  | 15 => ⟨42518,250,10158⟩
  | 16 => ⟨24860,163,5079⟩
  | 17 => ⟨24970,162,5079⟩
  | 18 => ⟨24917,161,5079⟩
  | 19 => ⟨24970,159,5079⟩
  | 20 => ⟨25200,152,5079⟩
  | 21 => ⟨25234,150,5079⟩
  | 22 => ⟨25324,149,5079⟩
  | 23 => ⟨25351,147,5079⟩
  | 24 => ⟨25436,146,5079⟩
  | 25 => ⟨25456,144,5079⟩
  | 26 => ⟨25472,142,5079⟩
  | 27 => ⟨25549,141,5079⟩
  | 28 => ⟨25624,140,5079⟩
  | 29 => ⟨25630,138,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P14 : WideCovered band 7339963 7663353 := wide_block_sound band profiles_RelativeWidePack6815_P14 7339963 7663353 (wideData 16 0x1b6c06db001a63e74525aa9f82134b19640659009b018c04b1b84904900124124001a06e000658ba0b30b3002cc2cc0664e12f2ed020aa97600000000000000400000000000000a000000000000014000000000000001a000000000000000ae000000000100013c000000000000000678800000000040000ae88000000000800013c9030c00c3001903013c300000000000eab02a2bb8213c8fc0b60b612a0b60b612a0a4c1fbaa00ea788ec) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P14 : WideCovered band 7663354 7710825 := wide_block_sound band profiles_RelativeWidePack6815_P14 7663354 7710825 (wideData 16 0x22d801d71004d2c00000000022bd06967004d2a000000000336a01c33a00134b00000000009870161840134a80000000002bf1f310628bd8311c4d2c000000000071e600a1863009a3600000000056297127f8b4d44268e00000000003bf0d78070bf0f640c9a36000000000270efd129b6a8c4134a8000000000beec4ad9c0134b0000000000a937904a7df6e144d2a0000000000e8e65a41c2dd63e42134b0000000000382bf7806c8aba62089a3800000000037ff018e8dc0134a80000000013b68064d2c004d2c0b40b412a0b40b412a06aca2e14ea686618ecfc8fc) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P14 : WideCovered band 7710826 7744056 := wide_block_sound band profiles_RelativeWidePack6815_P14 7710826 7744056 (wideData 16 0x7e2c765f800aa980000000017875b08e7b860082aa6000000000164f08baa002aa40000000000b3f2a941834cfda480aa980000000019e3aa09f31eee144d2c000000000064af6e0dfa8fa41c4d2a0000000005bddec239d7f902134b00000000016e68909a3dfe0084d2c00000000016a9280a0e68988134b00000000007b6c1b0d80134a80000000007b3c0f9a00134b0000000000afe806fde0004d2a0000000001fba04932004d2c0000000001fbe01972004d2a0000000001f9d02f77004d2c0b40b412a0b40b412a0729bde14f6286018edb8ebe) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P14 : WideCovered band 7744057 7812892 := wide_block_sound band profiles_RelativeWidePack6815_P14 7744057 7812892 (wideData 16 0xbbafa54de98f7452c6e000000000069a71f018fae64b074b1b00000000004ab3c01aa1b40268d80000000004fa6a81ab58b5089a38000000000223c650a782bec2268d8000000000bd35d44d31840268d80000000013fa2c429f38bd389a3600000000006feb9b46ee7efd109a380000000001708bdd55f71baf449a360000000000aaea9917c34866409a380000000000b7bffe41b69e35004d2a0000000001aafac844ef383f244d2c0000000803219e0857cffda1144d2c000000000528b67d14d64ff80c4d2c0000000003bdca906b8b1d440aa902d82d84a82d82d04a879e3ab60659b9ea840ee37b76) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P14 : WideCovered band 7812893 7964805 := wide_block_sound band profiles_RelativeWidePack6815_P14 7812893 7964805 (wideData 16 0x2ab7f018398c04b1b80000003003924df333f9e1d424b1b02080082001d74b7a06ba3b9c44b1b8000000001c93c0aebac012c6c00000000077af029a08004b1b8000000001ff2c07caa8012c6e000000000062b68071a6a012c6e0000000001f2fac0b6b2fd034b1b00000000003e3ba0196d9e40d2c6e000000000066b2013a9004b1b00000000001affc0a8f5012c6e0000000001ae9a50fcb24ac44b1b00000000002e64e05c25f804b1b80000000002ea4803f3cac04b1b00000000003ca2c069beec04b1b82d82d84a82d82d84a9dbabb13db6c3660ef6e8e4) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P14 : WideCovered band 7964806 8116718 := wide_block_sound band profiles_RelativeWidePack6815_P14 7964806 8116718 (wideData 16 0x8bf40fda004b1b80000000009b640f79004b1b0000000000abf40efb004b1b8000000000be6c0e78804b1b0000000000daf40bde004b1b8000000000fe602b6d804b1b80000000011db40bb9004b1b8000000200ffb00aaf804b1b000000000068f0078b804b1b80000000007c700608804b1b00000000009ba84004b1b8000000000c9e006dc404b1b00000000010a300efec04b1b80000000016fe01bea404b1b0000000000696d326a804b1b82e02e04a82e02d84a878b1d05b6d8b478f9b6e76) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P14 : WideCovered band 8116719 8373071 := wide_block_sound band profiles_RelativeWidePack6815_P14 8116719 8373071 (wideData 16 0x13d7c061a400658bc000000000071d74438a400658ba0000000000eeea50ab92c001962e82080000001e78aa95b8d23dc20658ba0000000000b1a28067e7e001962e80000000002fb4f02a70a400658ba00000000012dde812ca7c001962e80000000005ce5801d61c400658ba0000000001f9ee4320eeb001962f0000000000aae8d53935af3101962e82080082001afdb2006ac2efae1c1962e80000000005c34135d004b1b00000000006a64238e004b1b80000000006bac129a804b1b000000000078641268004b1b82e02e04a82e02e04a8cd74905bb5b6a78fbffc28) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P14 : WideCovered band 8373072 8676897 := wide_block_sound band profiles_RelativeWidePack6815_P14 8373072 8676897 (wideData 16 0x2080082017879061d74001962f00000000005fa82ffa800658ba0000000001afd0bdac001962e8000000000792c2ecb000658ba000000000234c13f3c001962e80000000008fa82f19000658ba0000000002a3f0af7a001962e8000000000bd202afc000658ba000000000371b09efc001962f0000000001186c5b3f000658ba0000000004f1b09eac001962e80000000018a6023cb800658ba0000020806ebc07db4001962e8000000000986d4f1c000658ba00000000017d95092c001962e82f02f04a82e82e84a8bce1d05ea3dba790826df8) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P14 : WideCovered band 8676898 8980723 := wide_block_sound band profiles_RelativeWidePack6815_P14 8676898 8980723 (wideData 16 0x1f31e01bf3c800658bc0000000000a9f340e2c69001962e80000000002db5914a6cf420658ba000000000178ee817483f081962e80000082008a31804b2df800658ba0000000006eafab37a92d001962e8410008200ada8f859e7eac081962e80000000006f2c5fcc800658ba0000000001bad1187c001962f00000000007bec4689000658ba000000000228811b78001962e80000000009ffc6f78000658ba0000000002ac912ef0001962e8000000000be7c4eca000658ba000000000163f5497c001962e82f82f84a82f82f84a8f832a068718b2790cb893c) (by decide +kernel)
private theorem c9_RelativeWidePack6815_P14 : WideCovered band 8980724 9417472 := wide_block_sound band profiles_RelativeWidePack6815_P14 8980724 9417472 (wideData 16 0x12fe9065bb4002aa5d020800820129fd07c928002aa5d00000000013cb82a29000aa9740000000006f6a018a4f000aa9760000000000629ac333a400aa974000000000075938071d800aa974000000000128ba50b38fee490aa9740000000000a28b02e9ac00658ba0000000000bc97806dd3f001962f00000000004b2ab03b2bf400658ba0000000001f5eac0f6f29001962e820800820178b2b44b69a420658ba000000000623f0e8a4001962e80000000001874802bb8a000658ba000000000061eac22cbc00658ba0e20e212a0e20e212a5acd2c2a7f33d81911969ca0) (by decide +kernel)
private theorem c10_RelativeWidePack6815_P14 : WideCovered band 9417473 10025123 := wide_block_sound band profiles_RelativeWidePack6815_P14 9417473 10025123 (wideData 16 0x20800820118b90b99fa002aa5d0000000000cdf80b2b36002aa5d0000000000bdb807faa8002aa5d0000000000ebb40b4ce6002aa5d0000000000dde40a0938002aa5d00000000010c280b09be002aa5d00000000011fb40ac8b2002aa5d00000000004fe80a4db6002aa5d82080082012f710b0d68002aa5d0000000000bfb006cb6c002aa5d0000000000fa300a1e34002aa5d0000000000f9a006ac22002aa5d800000000148240a4b2a002aa5d00000000015bb8068f76002aa5d0000000001aebc065ffe002aa5d03983984a83983984a92b2fe07c3392e792863d76) (by decide +kernel)
private theorem c11_RelativeWidePack6815_P14 : WideCovered band 10025124 10632775 := wide_block_sound band profiles_RelativeWidePack6815_P14 10025124 10632775 (wideData 16 0x125be4167df7082aa5d00000000009aede04cffcc00aa9740000000004b7b2722faa9002aa5d0208008200687a46fda3082aa5d80000000003a249019f3fc00aa9740820020802228350ef8420aa974000000000068d60065ee4002aa5d00000000001c77f18fa7002aa5d80000000002c25902c3fe000aa9740000000000e78bc229833002aa5d00000000005af091cfbc8c20aa9740000000003388fa0ac9b5002aa5d86180186016cf8dc3fb2f22282aa5d0000000000dd700b3fea002aa5d0000000000eca80b4df0002aa5d03a83a84a83a83a84a98967908cbfef27939a6bfc) (by decide +kernel)
private theorem c12_RelativeWidePack6815_P14 : WideCovered band 10632776 11468297 := wide_block_sound band profiles_RelativeWidePack6815_P14 10632776 11468297 (wideData 16 0x167d68064af5c00134aea08200208016ec5ccab800134ae80000000000e29243f08f2004d2ba800000000039b0807beda00134ae80000000000f9a241f3aed004d2ba8000000000186dd64329d60e17134ae80000000000edb640eac32002aa5d00000000005d63c04baed400aa97608200208037da2d4b6c31082aa5d00000000001dfbc01e6ab000aa9740000000000acfe83a6e800aa9740000000000f7e3c0a3da5002aa5d8208008200aa66b50fec9420aa974000000000069df0376002aa5d00000000001da2d0287cc400aa9740f40f412a0f40f412a5a1abc2ad926d81c14ae9aa4) (by decide +kernel)
private theorem c13_RelativeWidePack6815_P14 : WideCovered band 11468298 12455730 := wide_block_sound band profiles_RelativeWidePack6815_P14 11468298 12455730 (wideData 13 0x8200208007c8a2d4fea5c7d084d2ba02080082016ba2d439edb2b084d2ba0000000000edb8a02a7dffa004d2ba06180186001924f290b5ab8cd8134aea00000000052eefc1b1af9a80134ae808200208032fc6c137a3d800134aea0000000002e5e680efbefc80134ae8000000000279de00e08af880134aea00000000023b9280b4d38980134ae808200208012fb200a1e31e80134aea0000000001309f00678a8900134ae8000000000160a3806acb2e00134aea0fa0fa12a0fa0fa12a0a7b7fc19a2fe7c796833afa) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7339963 7663353 12455730 c0_RelativeWidePack6815_P14 (wide_covered_join band 7663354 7710825 12455730 c1_RelativeWidePack6815_P14 (wide_covered_join band 7710826 7744056 12455730 c2_RelativeWidePack6815_P14 (wide_covered_join band 7744057 7812892 12455730 c3_RelativeWidePack6815_P14 (wide_covered_join band 7812893 7964805 12455730 c4_RelativeWidePack6815_P14 (wide_covered_join band 7964806 8116718 12455730 c5_RelativeWidePack6815_P14 (wide_covered_join band 8116719 8373071 12455730 c6_RelativeWidePack6815_P14 (wide_covered_join band 8373072 8676897 12455730 c7_RelativeWidePack6815_P14 (wide_covered_join band 8676898 8980723 12455730 c8_RelativeWidePack6815_P14 (wide_covered_join band 8980724 9417472 12455730 c9_RelativeWidePack6815_P14 (wide_covered_join band 9417473 10025123 12455730 c10_RelativeWidePack6815_P14 (wide_covered_join band 10025124 10632775 12455730 c11_RelativeWidePack6815_P14 (wide_covered_join band 10632776 11468297 12455730 c12_RelativeWidePack6815_P14 c13_RelativeWidePack6815_P14)))))))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 13)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 13≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤56)
    (hT0 : 3700≤T) (hT1 : T≤3882) (hnu : 7339963≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤49074482642422725 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R088

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R089
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨13,57,3700,3749,47824769168565689⟩
private def profiles_RelativeWidePack6815_P14 : ℕ → Profile
  | 0 => ⟨16536,4,5080⟩
  | 1 => ⟨33072,8,10160⟩
  | 2 => ⟨260057,55,81712⟩
  | 3 => ⟨24253,183,5079⟩
  | 4 => ⟨24348,181,5079⟩
  | 5 => ⟨24296,184,5079⟩
  | 6 => ⟨24196,186,5079⟩
  | 7 => ⟨48056,364,10158⟩
  | 8 => ⟨29307,227,6051⟩
  | 9 => ⟨48205,359,10158⟩
  | 10 => ⟨48248,360,10158⟩
  | 11 => ⟨24304,180,5079⟩
  | 12 => ⟨24394,178,5079⟩
  | 13 => ⟨42768,250,10158⟩
  | 14 => ⟨24439,179,5079⟩
  | 15 => ⟨24860,163,5079⟩
  | 16 => ⟨24917,161,5079⟩
  | 17 => ⟨24970,159,5079⟩
  | 18 => ⟨25019,157,5079⟩
  | 19 => ⟨25200,152,5079⟩
  | 20 => ⟨25234,150,5079⟩
  | 21 => ⟨25324,149,5079⟩
  | 22 => ⟨25351,147,5079⟩
  | 23 => ⟨25436,146,5079⟩
  | 24 => ⟨25519,145,5079⟩
  | 25 => ⟨25456,144,5079⟩
  | 26 => ⟨25472,142,5079⟩
  | 27 => ⟨25549,141,5079⟩
  | 28 => ⟨25700,137,5079⟩
  | 29 => ⟨25630,138,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P14 : WideCovered band 7471034 7673305 := wide_block_sound band profiles_RelativeWidePack6815_P14 7471034 7673305 (wideData 16 0x13bd1ece4004e7c0000000000f8a01afbf40139f00000000004a7067edc0139f000000000058680b8800139f00000000004aa8077831004e7c0610610018418402bde68526fefe82139f0b2c02cb004d0f009cfa0fc0fc003f03f000e017a0019af882cc2cc00b30b3006cb04bcbba082b3e9800000000000000b0000000000000009f000000000040004f60000000000000019ee000000000100002bbc0c30030c05600709f2082bbab82d82d84b02d82d84b0182c077ca400eb3dc2e) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P14 : WideCovered band 7673306 7712699 := wide_block_sound band profiles_RelativeWidePack6815_P14 7673306 7712699 (wideData 16 0x39a806af6a004e7c0000000000a7f07fa3004e7c0000000000b0809d80139f000000000039a07bba00139f00000000002ae8424f40139f00000000003cf006b8f4004e7c0000000000afe139e9004e7c0000000000f8a01a2ee80139f80000000002d7c56e9c0139f00000000003f6406587a004e7c0000000000b9a60129eb9d83139f00000000002cee844aef8b5084e7c000000000129c01922a80139f00000000003974061969004e7c000000000131f0186dd80139f02d02d04b02d02d04b0c820914e62a2818ed2fdf0) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P14 : WideCovered band 7712700 7744707 := wide_block_sound band profiles_RelativeWidePack6815_P14 7712700 7744707 (wideData 16 0x208008000faa6da606de6f9c40acf80000000001dac1fdb800acf80000000002c7c06f9a4002b3e0000000001bda2427b9e5c050acf80000000001ee4733b000acf80000000017a73b4187982cbc20acf80000000010cb5d17eb1a26084e7c00000000016fff42288f7a02139f80000000006ebfb09ef7a3a084e7c00000000006de3c0a0d36f04139f00000000001fe80a2800139f00000000001f281688c0139f0000000000386c06feb0004e7c00000000007fd068ff004e7c0000000000e3d01b6cd00139f02d02d04b02d02d04b0dc7dc14f2da3418edbcd74) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P14 : WideCovered band 7744708 7811185 := wide_block_sound band profiles_RelativeWidePack6815_P14 7744708 7811185 (wideData 16 0x27a9b0669ef2d954e7c00000000017882f75009cf8000000000077dab2a9e62942273e80000000001b26d03e75dc0273e00000000015f6b0e1ea7a42273e00000000002fe1f53860e40273e00000000004a2084c8b6ac0273e8000000000c82bf48be487f409cf80000000005aaaed1a4ebce45273e80000000002bfca47b67aa4109cf800000000047dbe9262b2b004e7c000000000065a23842aecc35004e7e00000000012eda8b4ccfbcbb3c4e7c000000080222eed1b4fee982139f0000000000286bb2d0609609400acf82d82d84b02d82d04b09f33cf6064c3ba7848ee38e64) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P14 : WideCovered band 7811186 7968762 := wide_block_sound band profiles_RelativeWidePack6815_P14 7811186 7968762 (wideData 16 0x2be3c4f8a50139f000000000046c9b53aa832e424e7c8000008201cfe45bf9250939f00820000001f483e5a6ef00139f20000000001b3e0382f0139f20000000002b0c04ce89804e7c80000000007e340628b30139f00000000000bb8200fe96cc834e7c80000000002965e43f30ff90939f00000000000a38280b8868f874e7c800000000019ebc42e66f3f1939f00000000004f2a029728004e7c80000000012b74222e790139f0000000000725f0d8f50139f20000000000e7fa92a7feae504e7c02d82d84b02d82d84b0c92c91e87ddec18ef6bbb4) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P14 : WideCovered band 7968763 8126339 := wide_block_sound band profiles_RelativeWidePack6815_P14 7968763 8126339 (wideData 16 0xa6a05e380139f00000000000adf05e700139f20000000000b6b05e7c0139f00000000000bd91d9c04e7c80000000003b7016f9004e7c80000000003f3c16eb804e7c80000000004bf816dc804e7c000000000059ec13a9004e7c800000000068a80f9c404e7c00000000007bb0130e004e7c800000000099341298804e7c0000000000bc240fec004e7c8000000000eeb832aec04e7c000000000149ec1a60139f20000000001b4dc28e90139f00b80b812c0b80b812c479b85b22f2468f9bf9e6) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P14 : WideCovered band 8126340 8382401 := wide_block_sound band profiles_RelativeWidePack6815_P14 8126340 8382401 (wideData 16 0x61f64731d40066be20000000006f2cc7bbf0019af880000000006a38941bfccc0066be20820020802fcd7f5eec6a842066be200000000076db0cef0b00066be2000000000430d109f0cc0066be2000000000065b200b5afa0019af880000000001bbfa04ead840066be40000000001afcb94afafe8c2066be20820020804ad8bc06ac75b701419af880000000001a24075a804e7c00000000001ba017db804e7c80000000001c7817dd004e7c00000000001da017dc004e7c80000000001df4067e804e7c02e02e04b02e02e04b03b75a05b68bfe68fc32ff8) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P14 : WideCovered band 8382402 8697555 := wide_block_sound band profiles_RelativeWidePack6815_P14 8382402 8697555 (wideData 16 0x4aa43bb880066be200000000016fc1e8300019af88000000000cbad43a800066be208200208022ec55a280019af8800000000028fc428b00066be20000000000a5b07aba0019af880000000002d68426f00066be20000000000ba905fa00019af900000000003c28427c00066be20000000000fc803f740019af880000000004fa4420b00066be20000000001a2a10c7e0019af880000000007b342ef0019af88000000000a8b83fcf00066be2000000000373e07f310019af882f02f04b02f02f04b02ab6805e7db3269083aae6) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P14 : WideCovered band 8697556 9012708 := wide_block_sound band profiles_RelativeWidePack6815_P14 8697556 9012708 (wideData 16 0x2a8a10f250019af88000000000cfe806ea3d0019af880000000013a28066f6a0019af88000000000baf87bfbb50819af880000000001af6d0383abc0066be20000000000af9bc0beca00019af884100104003e3ad459669301019af880000000001c2036c800066be4000000000079c158760019af880000000001e30368980066be20000000000a4c15ef80019af88000000000293c365f80066be20000000000b4816fe80019af880000000002fb8621b00066be20000000000e4c0dfec0019af882f82f84b02f82f84b03fb7e06834de2690d21f28) (by decide +kernel)
private theorem c9_RelativeWidePack6815_P14 : WideCovered band 9012709 9406651 := wide_block_sound band profiles_RelativeWidePack6815_P14 9012709 9406651 (wideData 16 0x1097c1e1c000acfa400000000072da1fe62002b3e980000000001f37c1fde5002b3e900000000007fb60a9e3fccb0acfa40000000001e08e52a4ebd0019af882080082001de9b82a26982066be200000000026ef01abb800066be20000000002f0b01874800066be40000000003b1d14ba60019af880000000012f2c7a8ec0066be20000000006a5b04ea5cc0066be200000000006bb7012e92d0019af880000082001ffed09d3cf42066be20820000001ace651a7cee0019af8800000000079a84b3980066be20e20e212c0e20e212c1b19f02aad309018119e9b6c) (by decide +kernel)
private theorem c10_RelativeWidePack6815_P14 : WideCovered band 9406652 10036958 := wide_block_sound band profiles_RelativeWidePack6815_P14 9406652 10036958 (wideData 16 0x134e02e2be800acfa4000000000166b02eefe800acfa40820020801e2942af4e000acfa40000000000fdf02d368800acfa40000000000f8802824d000acfa400000000012580282df800acfa6000000000136d0283e9000acfa400000000016ec028a5a000acfa40000000001b1902922a000acfa4000000000072f429f39800acfa60820020801a1e429b1f000acfa4000000000129f01a69d000acfa4000000000162c019b19800acfa40000000001a6d018bbd800acfa60000000001fed1ddea002b3e903983984b03983984b04ebeb07bfb8a0692831a7a) (by decide +kernel)
private theorem c11_RelativeWidePack6815_P14 : WideCovered band 10036959 10667266 := wide_block_sound band profiles_RelativeWidePack6815_P14 10036959 10667266 (wideData 16 0x1bcec520ec00acfa4000000000072cb412b9ba002b3e980000000003ab080e9bab400acfa40820020801b6b653fd9ef082b3e900000000017864062e3a002b3e9000000000018e1f02d608400acfa60000000000a3e640b8e32082b3e9000000000049a1843da1e000acfa400000208006f9e1fc1821efd002b3e902080000001bf2caa5f18fb082b3e980000000001d25d02f319000acfa40000000000eb8bc127ff9002b3e906180186004ca0944ee7fa6302b3e900000000003d700b4834002b3e980000000003f700b4f34002b3e903a83a84b03a83a84b06bad808c2bea86939e0b20) (by decide +kernel)
private theorem c12_RelativeWidePack6815_P14 : WideCovered band 10667267 11376361 := wide_block_sound band profiles_RelativeWidePack6815_P14 10667267 11376361 (wideData 16 0x6cc7c2a8da4004e7ca0000000000b87a90f9f4c20744e7ca00000000015fe07bff400acfa4000000000066afc07ba78002b3e902080082002d2bf42e2abc20acfa4000000000372e02d29c800acfa60000000003fd902aa5a400acfa40000000006b8917aa1002b3e900000000001be5904f2fcc00acfa40820020800efaf92f7bf9082b3e98000000000ddbc061b61002b3e900000000008ab8621ef3082b3e9000000000018e2801e2c8c20acfa40000000000a8c6c17e96b002b3e982080082004de6a45beff420acfa40f40f412c0f40f412c1bc8742e49fbf81b14b6fba8) (by decide +kernel)
private theorem c13_RelativeWidePack6815_P14 : WideCovered band 11376362 12479399 := wide_block_sound band profiles_RelativeWidePack6815_P14 11376362 12479399 (wideData 16 0x18600618026fa38765d7ac02139f28000000000233808a6df000acfa4000000000233e0887ae000acfa6000000000237807eeae000acfa4082002080064ce0b41ba18e99de0acfa4082002080171c601f5cbcd00139f2a00000000013ed3c17ae3ff00139f280000000000f98f012b861800139f2a0000000000e99a00f5be0800139f2808200208007b8680e1af1e80139f2800000000007ca7c07f936800139f28000000000077cf00768f2b80139f2a000000000075afc06deeaf80139f2808200208057ca01ebede8004e7ca8000000001db2c4a8eac004e7ca03e83e84b03e83e84b12c25b198baafe695ee5abc) (by decide +kernel)
private theorem c14_RelativeWidePack6815_P14 : WideCovered band 12479400 12636975 := wide_block_sound band profiles_RelativeWidePack6815_P14 12479400 12636975 (wideData 2 0x20800820099b7a42be78af0c4e7ca04a04a04b04a04a04b16a6cf0197a9f2c81e97fafdb6) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7471034 7673305 12636975 c0_RelativeWidePack6815_P14 (wide_covered_join band 7673306 7712699 12636975 c1_RelativeWidePack6815_P14 (wide_covered_join band 7712700 7744707 12636975 c2_RelativeWidePack6815_P14 (wide_covered_join band 7744708 7811185 12636975 c3_RelativeWidePack6815_P14 (wide_covered_join band 7811186 7968762 12636975 c4_RelativeWidePack6815_P14 (wide_covered_join band 7968763 8126339 12636975 c5_RelativeWidePack6815_P14 (wide_covered_join band 8126340 8382401 12636975 c6_RelativeWidePack6815_P14 (wide_covered_join band 8382402 8697555 12636975 c7_RelativeWidePack6815_P14 (wide_covered_join band 8697556 9012708 12636975 c8_RelativeWidePack6815_P14 (wide_covered_join band 9012709 9406651 12636975 c9_RelativeWidePack6815_P14 (wide_covered_join band 9406652 10036958 12636975 c10_RelativeWidePack6815_P14 (wide_covered_join band 10036959 10667266 12636975 c11_RelativeWidePack6815_P14 (wide_covered_join band 10667267 11376361 12636975 c12_RelativeWidePack6815_P14 (wide_covered_join band 11376362 12479399 12636975 c13_RelativeWidePack6815_P14 c14_RelativeWidePack6815_P14))))))))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 13)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 13≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤57)
    (hT0 : 3700≤T) (hT1 : T≤3749) (hnu : 7471034≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤47824769168565689 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R089
end MergedPart2
section MergedPart3
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R090
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨13,57,3750,3852,40214889553166861⟩
private def profiles_RelativeWidePack6815_P15 : ℕ → Profile
  | 0 => ⟨8268,2,2540⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨42768,250,10158⟩
  | 4 => ⟨24253,183,5079⟩
  | 5 => ⟨24296,184,5079⟩
  | 6 => ⟨24154,185,5079⟩
  | 7 => ⟨48248,360,10158⟩
  | 8 => ⟨48056,364,10158⟩
  | 9 => ⟨48205,359,10158⟩
  | 10 => ⟨24304,180,5079⟩
  | 11 => ⟨24665,169,5079⟩
  | 12 => ⟨24439,179,5079⟩
  | 13 => ⟨24394,178,5079⟩
  | 14 => ⟨24860,163,5079⟩
  | 15 => ⟨24917,161,5079⟩
  | 16 => ⟨24970,159,5079⟩
  | 17 => ⟨25019,157,5079⟩
  | 18 => ⟨25200,152,5079⟩
  | 19 => ⟨25234,150,5079⟩
  | 20 => ⟨25324,149,5079⟩
  | 21 => ⟨25351,147,5079⟩
  | 22 => ⟨25436,146,5079⟩
  | 23 => ⟨25456,144,5079⟩
  | 24 => ⟨25472,142,5079⟩
  | 25 => ⟨25549,141,5079⟩
  | 26 => ⟨25700,137,5079⟩
  | 27 => ⟨25630,138,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P15 : WideCovered band 7471034 7735890 := wide_block_sound band profiles_RelativeWidePack6815_P15 7471034 7735890 (wideData 16 0x8e3780687cbe0084f7600000000067fcf44a4ca7d8413dd00000000016efe9508e5bad0c4f760000000005bed6042396cb0213dd00000000001bac570004f7600000000006ff14e8013dd00000000001c68528004f76000000000071b17cc013dd00000000001d2c2b2004f760c30030c017a8f01619b1c8213dd0000000000800013dd0000000001000027ba820800820019b0070d2e093db40c30030c00600c0067b6808200410057862aa020aeeae0b40b412c0b20b212c068b1fdfc00ec7b96a) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P15 : WideCovered band 7735891 7783816 := wide_block_sound band profiles_RelativeWidePack6815_P15 7735891 7783816 (wideData 16 0x98ab478e4027ba80000000013b711b7ac027ba80000000002aa0d4192db4027ba80000003001fe9d25636d7afc327ba80000082002875a32639ca688227ba800000c00019f6b139e7004f74000000000074d336b4c4013dd800000000029ecd418a9cc013dd0000000000ea208f9063b78a31244f740000000003a9bafe018eecfbd8813dd02080080001a77a376a9938a4d0aee80000000002d6c1288000aef00000000003e2472ae800aee8000000000eb3494a93a967082bba000000000362afc23fca2f8213dd82d02d04b02d02d04b01b69fb0060dadcbc38ee2a8b8) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P15 : WideCovered band 7783817 7925072 := wide_block_sound band profiles_RelativeWidePack6815_P15 7783817 7925072 (wideData 16 0x5b70078013db40000000001ac8068e8013db20000000001bfb01823013db4000000000221901fa9013db400000000026b90393d013db40000000002ea804bbe013db2000000000367e05da9013db4000000000429bb13b69b284f4f6d00000000001d2fa03bbcb404f6d00000000006f6cf49f77b2f313db20000000000fac685f2ab3013db400000008053b8f0671a2e9024f6d00000000002af0079e0027ba80000000013fbc26394027ba80000000005e680ba009ee80b60b612c0b60b412c56bc05a2bc3c18eeeccfa) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P15 : WideCovered band 7925073 8086508 := wide_block_sound band profiles_RelativeWidePack6815_P15 7925073 8086508 (wideData 16 0x1e8f04e68013db4000000000231d0ad2e013db2000000000274b03e6c013db40000000002eab03bf8013db4000000000370903928013db40000020803a4e0e8e0013db2000000000075803a60013db40000000000b3e02dae013db400000000012c801d62013db4000000000635a54ce4013db200000000007cb02ef2013db4000000000169a1ee004f6d0000000000daa80e7e404f6d02080000002d64f41ce98004f6c80000000004af0063f804f6d02d82d84b02d82d84b06da9e05aad83e18f92aaf4) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P15 : WideCovered band 8086509 8298392 := wide_block_sound band profiles_RelativeWidePack6815_P15 8086509 8298392 (wideData 16 0x123930068f6cc00067b68000000000678ca8474ee5987067b660000000000ba821132fe2c42067b680000000002e6fb93a9e7bfc4067b66000000000069fe99019a086ae03067b680820020800779a8166c67a904f6c80000000002df4135e004f6d00000000002fa81338804f6d00000000003ab81fcd804f6d00000000003c3c1a2d004f6c80000000003e6412fd004f6d0000000000493412ba804f6d00000000004d6c1b69804f6d000000000059bc1f8e004f6c80000000005d701288004f6d02e02e04b02e02e04b06c3a805baa96018fba5d6a) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P15 : WideCovered band 8298393 8621264 := wide_block_sound band profiles_RelativeWidePack6815_P15 8298393 8621264 (wideData 16 0x130811f3c0019eda00000000004ce8238a80067b6600000000017591296c0019eda000000000068281f6980067b660000000001f0a12cf20019eda00000000008ab81a6980067b660000000002b5d139f20019eda0000000000ccec0ff880067b6600000000043b91487a0019eda00000000015df81620019ed98000000001fbf4565f80067b6800000208006c9e022fb40067b660000000003bdd55eb80019eda00000000002e66901a78d40067b66000000000122ed3daf0019eda02f02f04b02e82e84b018eab85f3992418fef79b6) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P15 : WideCovered band 8621265 8944135 := wide_block_sound band profiles_RelativeWidePack6815_P15 8621265 8944135 (wideData 16 0x2b3aa1d9c0067b680000000000ffd340a89e90019ed984100104005920a45b3db6a5819eda000000000038ec3b5980067b660000000000f7c16cea0019eda00000000003d683b6b80067b6600000000012e817cb80019eda00000000004bb83bbf80067b6600000000016ea1982c0019eda00000000005d603ebd80067b660000000001bfa1b8f80019ed980000000007c6c42c800067b6600000000026f91ec280019eda0000000000bdfd4acb80067b660820020805bdc5f86a0019eda02f02f04b02f02f04b08eec906820bfc190bedea6) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P15 : WideCovered band 8944136 9267007 := wide_block_sound band profiles_RelativeWidePack6815_P15 8944136 9267007 (wideData 16 0x1fbc69b1e40067b680820020802a8cff2f1d370819ed980000000012dbc0b09220019eda00000000012f6c1eddc0067b660000000006e1a028e4c00067b680000000007bab01d2f940067b6600000000006ec20061ae00019eda00000000002825e0586a9c0067b660000000000f0a780bd8e90019eda0208008200aee0c4597bac2067b66000000000322b12b7b0019eda00000000011b6c069efe0019ed980000000014e247b5b80067b68000000000673e0ee740019ed98000000001feb006ee270019eda03883884b03883884b0b864c0abfbefa7918e4b74) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P15 : WideCovered band 9267008 9892569 := wide_block_sound band profiles_RelativeWidePack6815_P15 9267008 9892569 (wideData 16 0x1f9d028e7a000aeeae000000000233a028e7d800aeeae000000000276d028f6d800aeeae0000000002e7a02939d000aeeae00000000036cc029b29000aeeac000000000434a02a789800aeeae0820020807bee42ab5f800aeeae00000000023f801ab6f800aeeae0000000002b2b019f09000aeeae00000000033e9018e9f000aeeae000000000434a1d9fe002bbab80000000016eac4f49000aeeae000000000062b240a58800aeeac00000000007bffc063a3f002bbab800000000018210a2fa3ddd0aeeae0e60e612c0e60e612c1b2b24278929c81891dbb864) (by decide +kernel)
private theorem c9_RelativeWidePack6815_P15 : WideCovered band 9892570 10538312 := wide_block_sound band profiles_RelativeWidePack6815_P15 9892570 10538312 (wideData 16 0x19b4f01ebda000aeeae00000000006cff0278c31002bbab80000000002d70b09b618c20aeeae0000000001ba8e4364c28002bbab800000000119f59d2cf19400aeeae082002080139eb67e4ff9082bbab80000000002cbc902ca8e000aeeae1040041004fbe44e7dbb4782bbab82080082005cb40b9e6a002bbab80000000007de40b9a2c002bbab80000000007f300b3df4002bbab80000000008bf00b4ba2002bbab800000000099e80b4fb2002bbab0000000000ab780bab28002bbab800000000019b10e3b2e002bbab83a83a84b03a83a84b0ce2dd08abea68192fa8a20) (by decide +kernel)
private theorem c10_RelativeWidePack6815_P15 : WideCovered band 10538313 11184055 := wide_block_sound band profiles_RelativeWidePack6815_P15 10538313 11184055 (wideData 16 0xae9b46b8c000aeeae082002080168f216abd420aeeae000000000725b02a23f000aeeae000000000062db4078b3b002bbab80000000001de5803db7dc00aeeae08200208013bf753eb9b7082bbab80000000016a74136e400aeeae000000000062ae40a5c6c002bbab80000000004b70065876dc20aeeae0000000000bb92c078af2002bbab80000000005e73903ab5a400aeeae0820020802e2865675f420aeeae00000000006ac742e4e000aeeac0000000000a0aa40eee6b002bbab80000000003ff4c07ac00aeeae0f40f412c0f40f412c1bdd302eeb66f01a94975bbe) (by decide +kernel)
private theorem c11_RelativeWidePack6815_P15 : WideCovered band 11184056 12314104 := wide_block_sound band profiles_RelativeWidePack6815_P15 11184056 12314104 (wideData 16 0x579d0a97c9800aeeac0820020800b3aefb41ce4d20a41b82bbab8208008200deb78099f7da0004f74f0000000000aea0a06970cb4004f74f00000000007fef804b61a68004f74f00000000006f70903d7cc2e004f74e82080082004a78c03bbcfba004f74f00000000004a21a02926e72004f74f00000000003ebf801dfbe74004f74f00000000003cf9a01aef938004f74f00000000003d68d1bfe8a0013dd3c00000000012bf682b6a0013dd3c000000000224a300bd8a7fc013dd3c082002080430d645b3970a01b44f74e8000000001f8ac3fcb800aeeae0fa0fa12c0fa0fa12c2e3cfc271dbea01c95b62d7c) (by decide +kernel)
private theorem c12_RelativeWidePack6815_P15 : WideCovered band 12314105 12636975 := wide_block_sound band profiles_RelativeWidePack6815_P15 12314105 12636975 (wideData 6 0x13dfe406efa1a4013dd3a104004100065ea9e018b6f20b0213dd3c0000000006a4a0ca78c000aeeae08200208013f84ad76a000aeeae0000000004a8e08c6ae000aeeae12212212c12212212c4a7de42f98f8981d17ca1e7e) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7471034 7735890 12636975 c0_RelativeWidePack6815_P15 (wide_covered_join band 7735891 7783816 12636975 c1_RelativeWidePack6815_P15 (wide_covered_join band 7783817 7925072 12636975 c2_RelativeWidePack6815_P15 (wide_covered_join band 7925073 8086508 12636975 c3_RelativeWidePack6815_P15 (wide_covered_join band 8086509 8298392 12636975 c4_RelativeWidePack6815_P15 (wide_covered_join band 8298393 8621264 12636975 c5_RelativeWidePack6815_P15 (wide_covered_join band 8621265 8944135 12636975 c6_RelativeWidePack6815_P15 (wide_covered_join band 8944136 9267007 12636975 c7_RelativeWidePack6815_P15 (wide_covered_join band 9267008 9892569 12636975 c8_RelativeWidePack6815_P15 (wide_covered_join band 9892570 10538312 12636975 c9_RelativeWidePack6815_P15 (wide_covered_join band 10538313 11184055 12636975 c10_RelativeWidePack6815_P15 (wide_covered_join band 11184056 12314104 12636975 c11_RelativeWidePack6815_P15 c12_RelativeWidePack6815_P15))))))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 13)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 13≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤57)
    (hT0 : 3750≤T) (hT1 : T≤3852) (hnu : 7471034≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤40214889553166861 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R090

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R091
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨13,58,3685,3699,75297964709973231⟩
private def profiles_RelativeWidePack6815_P15 : ℕ → Profile
  | 0 => ⟨412932,88,129764⟩
  | 1 => ⟨29307,227,6051⟩
  | 2 => ⟨29266,226,6051⟩
  | 3 => ⟨24296,184,5079⟩
  | 4 => ⟨24253,183,5079⟩
  | 5 => ⟨24196,186,5079⟩
  | 6 => ⟨48056,364,10158⟩
  | 7 => ⟨48205,359,10158⟩
  | 8 => ⟨48248,360,10158⟩
  | 9 => ⟨24304,180,5079⟩
  | 10 => ⟨24394,178,5079⟩
  | 11 => ⟨24154,185,5079⟩
  | 12 => ⟨24348,181,5079⟩
  | 13 => ⟨24439,179,5079⟩
  | 14 => ⟨24526,177,5079⟩
  | 15 => ⟨43018,250,10158⟩
  | 16 => ⟨24480,176,5079⟩
  | 17 => ⟨24917,161,5079⟩
  | 18 => ⟨24970,159,5079⟩
  | 19 => ⟨25019,157,5079⟩
  | 20 => ⟨25234,150,5079⟩
  | 21 => ⟨25324,149,5079⟩
  | 22 => ⟨25351,147,5079⟩
  | 23 => ⟨25436,146,5079⟩
  | 24 => ⟨25519,145,5079⟩
  | 25 => ⟨25456,144,5079⟩
  | 26 => ⟨25472,142,5079⟩
  | 27 => ⟨25549,141,5079⟩
  | 28 => ⟨25624,140,5079⟩
  | 29 => ⟨25699,135,5079⟩
  | 30 => ⟨25630,138,5079⟩
  | 31 => ⟨25700,137,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P15 : WideCovered band 7602105 7650496 := wide_block_sound band profiles_RelativeWidePack6815_P15 7602105 7650496 (wideData 16 0x175e03b7988013f980000000003cec3748e3004fe60000000000fae0f96acc013f980000000006c38069b60004fe400000000017bd13ae4a0013f980000000002c601bb829002bf20000000000b9b05f70c400afd00000000003ea80628ec002bf20000000000bb907fa09c00afd000000000018ade49dbff29082bf20000000000b7c02eef9000afd00000000001e7416cdef0019f84510114401efc7807fb60ba40819fa2490092400a83400afd0b2c02cb007b17009fac0f60f612e0f60f612e0f99018e2f3c00ec67d60) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P15 : WideCovered band 7650497 7691247 := wide_block_sound band profiles_RelativeWidePack6815_P15 7650497 7691247 (wideData 16 0x63e1fdec004fe60000000006740628fb004fe6000000000065e1d930004fe60000000006f00678b5004fe4000000000068a19fe8004fe600000000077c06cde3004fe600000000006af16b78004fe600000000006cb15822004fe6000000000062b01d7c9c013f980000000001bfc43390013f98000000000197c07de67004fe6000000000073f0bb30004fe600000000006a9029e6a4013f980000000001e3816aa8013f980000000007da507f862ac213f982d02d04b82d02d04b83ab2a16ef0eae18ece3ae6) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P15 : WideCovered band 7691248 7731998 := wide_block_sound band profiles_RelativeWidePack6815_P15 7691248 7731998 (wideData 16 0x1ca1a089e2e64084fe60c300000007e9fc27aa2ab8413f98208000000d8300a09a9f0313f98000000000bc2d07f86284213f90000000000cf3c07fff0d0313f98000000001bc019adc8013f980000000012e0bef5004fe60000000007600678e0004fe60000000004ec439cc013f98000000001ea019b5c8013f980000000014b158ab004fe60000000007f4064efc004fe600000000057062edc013f980000000001868062ef0004fe6000000000061e01866e8013f982d02d04b82d02d04b83d3ef14de5de420ed72fa4) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P15 : WideCovered band 7731999 7760015 := wide_block_sound band profiles_RelativeWidePack6815_P15 7731999 7760015 (wideData 16 0x5aede46ea9bb5284fe6000000000175e7d073dbfc4013f980000000009aafd4196d86d004fe60000000000a68fbd5eaa3b6b144fe6000000000471c685e2cb1a0313f980000000001d76dbd0aee30cc30afc8000000000ac60fe926f837a440afd0208008200ebacee61f0ef4a800afc8000000000ed15a000afd00000000017f01bb28800afc8000000000fc02d24002bf4000000000078c28238db0b050afc80000000007a700638aaf820afd0000000000cf75075eb09c40afc80000000004a368568b18fb182bf40b40b412e0b40b412e2b5830076e78efa10ee22c62) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P15 : WideCovered band 7760016 7877174 := wide_block_sound band profiles_RelativeWidePack6815_P15 7760016 7877174 (wideData 16 0x4824474ec04fce00000000004d30073e77013f380000000000ef941f718a11d3f380000000007e9e48bec97b413f360000000003bba05ffcc804fce00000000001eb3955b259313d3f38000000000127e7c0648ed978093f380000000001e2b02a6b84027ea80000000008cec0e39e9009fac0000000002b7b049bea4027eb0000000000bbf00ecd299c227eb0000000000eea723fbb3009fac0000000007e984dc26ac027eb00000000002c3a848d66823289fac0000000000f38e1078c299c027eb02d82d84b82d82d84b87d75f9e82e96220ee7e9e8) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P15 : WideCovered band 7877175 8040178 := wide_block_sound band profiles_RelativeWidePack6815_P15 7877175 8040178 (wideData 16 0x292c1a9b004fce00000000002ce016cec04fce00000000003aa0165e804fce00000000004a702ab8404fcd80000000005efc4309c04fce00000000002baf0bcbc04fce00000000004b292f89fcfc24fce00000000001fa0942879e35213f360000000001649a50a9ff5ac74fce000000000198a5d5ffaef424fce0208008201ca65c9cdbbf804fce0000000000dabc079da9e064fcd80000000002d3807ccb2013f380000000000bc901bafd004fce0000000000396477a8004fce02d82d84b82d82d84b83be1813d2eaaa48f86d822) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P15 : WideCovered band 8040179 8213369 := wide_block_sound band profiles_RelativeWidePack6815_P15 8040179 8213369 (wideData 16 0x8200208017ddb806bfbdd623419f9b8000000000bd02f68013f380000000003641e4b804fce0000000000dc02d30013f360000000003f01e5a804fce0000000000ff02a7e013f3800000000046c07d9004fce000000000149079b4013f3600000000056806cd004fce00000000018e079e8013f380000000006b4622013f380000000007ec1e78004fcd800000000018b0139013f38000000000067f01869013f3800000000006ff06e6a013f380b80b812e0b80b812e5bfa05aaa9b478faebafa) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P15 : WideCovered band 8213370 8539376 := wide_block_sound band profiles_RelativeWidePack6815_P15 8213370 8539376 (wideData 16 0x60e0ac280019f9b800000000019bc27ca00067e7000000000006fa098280019f9b80000000001ebc1fbf80067e700000000000a990cca70019f9b800000000039a83a00019f9c00000000004ca8167940067e6e0000000001e480fc6d0019f9c0000000000197085686ecf50c19f9b8000000000a96f5f0fab0019f9c0000000001cfb2a54c3ae613019f9b82080082015d3a89fb29c02067e700000000000e0ab03a7ee8e09067e6e0000000000a1e2d36eba8cc8067e70000000000477e0e8f8c40067e6e0ba0ba12e0ba0ba12e1f5b3806fe37df848fdb1c60) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P15 : WideCovered band 8539377 8865383 := wide_block_sound band profiles_RelativeWidePack6815_P15 8539377 8865383 (wideData 16 0xfd11be80019f9b80000000011811d660019f9c00000000012d11efa0019f9b80000000014e1296e0019f9c00000000017912c340019f9b80000000019b0f8e60019f9c0000000001ca0c9b60019f9b800000000018b44f0d80067e70000000000068e14b3a0019f9b80000000001c68575900067e7000000000007cf17afe0019f9b80000000002b7467ea80067e7008200208026df59fba0019f9b80000000013e038e00019f9c00000000018b0bbb20019f9b82f02f04b82f02f04b818fca05ea2aec790aaea2e) (by decide +kernel)
private theorem c9_RelativeWidePack6815_P15 : WideCovered band 8865384 9191390 := wide_block_sound band profiles_RelativeWidePack6815_P15 8865384 9191390 (wideData 16 0x3ba4066a340019f9b80000000004b28634f80067e7000000000016ba03fbe940067e6e000000000230a01fbecc0067e70000000000328e109f3f42067e6e0000000003a4f83d2ce00067e70000002080173804e7fa00067e6e08200000007aae30759e00019f9c00000000002d741a0880067e6e0000000000e9d0ffab0019f9c0208008200df38125c30f04067e6e0000000006606a0f80067e700000000007206ead80067e6e0000000007f8760f80067e70082002080123c52f6c0019f9b82f82f84b82f82f84b81a64e068bfd3a790faaffc) (by decide +kernel)
private theorem c10_RelativeWidePack6815_P15 : WideCovered band 9191391 9721152 := wide_block_sound band profiles_RelativeWidePack6815_P15 9191391 9721152 (wideData 16 0x1fb00a286a002bf2f80000000002b6807bc7e002bf2f800000000038e4063fa8002bf2f80000000004e340a8f6e002bf2f82080082009d29074f64002bf2f00000000001dec131cc00afcbe0000000000b0f11828002bf2f80000000003cb80709000afcbe000000000175f1cb6b002bf2f80000000005c310a2ca7a490afcbe0000000001f8802ae5ec0067e6e000000000333b01f2f9c0067e700000000003e3d86af1dc0067e6e082002080077ce313a9270819f9c00000000001fec3a58c0067e6e0e40e412e0e40e412e079df82a2e31b01911ca7dec) (by decide +kernel)
private theorem c11_RelativeWidePack6815_P15 : WideCovered band 9721153 10373166 := wide_block_sound band profiles_RelativeWidePack6815_P15 9721153 10373166 (wideData 16 0x6180186001ce3843dbffee282bf2f80000000001a640ee9b0002bf2f80000000001b240f0fa0002bf2f80000000001a7c0b98fc002bf2f820800820019e90f2974002bf2f000000000018a00b5bb0002bf2f800000000018f40b2d30002bf2f800000000018b80a3a66002bf2f80000000001abc0b8d72002bf2f80000000001c200bbebe002bf2f80000000001c340a1aa0002bf2f82080082002aad0e1bee002bf2f800000000018e80a0fea002bf2f000000000019e40a1a2a002bf2f800000000019bc066b2a002bf2f83a03a04b83a03a04b81cfac07ebc9e6792cfa9be) (by decide +kernel)
private theorem c12_RelativeWidePack6815_P15 : WideCovered band 10373167 11025181 := wide_block_sound band profiles_RelativeWidePack6815_P15 10373167 11025181 (wideData 16 0x7b38131d3b002bf2f8000000000cc2047ca79082bf2f8208008201eb2d126d72002bf2f830c00c30068648c18ed827082bf2f82080082006973d85e249c20afcbc000000000367b04bbfb000afcbe0820020806fae45af5bc20afcbe0000000000ff91c8a3002bf2f80000000006b780a6fee002bf2f80000000009d744b98400afcbe00000000047bf079f4fc00afcbe082002080068fb54b3b6b082bf2f80000000004eb00bb8bd002bf2f80000000008a7c2a59800afcbe000000000323c0eff69420afcbe0f20f212e0f20f212e06d9e83369acb81a13ef3d7a) (by decide +kernel)
private theorem c13_RelativeWidePack6815_P15 : WideCovered band 11025182 12003203 := wide_block_sound band profiles_RelativeWidePack6815_P15 11025182 12003203 (wideData 16 0x1ee640f6d76c8013f97c00000000056e902a208a6004fe5f0000000001aff00baae590013f97c08200208007ad4183bbfe004fe5f0000000000ee6c0669acb8013f97c00000000022db0abae9c013f97c0000000003fae14a3294013f97a000000000120c6052ec72a1b13f97c000000000360d05ff2ec00afcbe08200208072e941a309020afcbe00000000012fb01f279000afcbe0000000001a8b0ec26002bf2f8000000000a8600ac8a5002bf2f02080082016be53e1a820afcbe000000000124f03de68000afcbe0f80f812e0f80f812e073dbc26e96ba81d158ed938) (by decide +kernel)
private theorem c14_RelativeWidePack6815_P15 : WideCovered band 12003204 12818220 := wide_block_sound band profiles_RelativeWidePack6815_P15 12003204 12818220 (wideData 14 0x2080082004ae6d4eaa793b144fe5e800000000058a143c86494213f97c186006180164f74072b2ee72084fe5f00000000002afc1fad6c002bf2f80000000002b341f59e0002bf2f80000000002ba41f0dba002bf2f00000000002c381edea0002bf2f80000000002d341eceea002bf2f80000000002ea81ee8f0002bf2f82080082002c6116cde4002bf2f8208008200aea1c41bf3977d5c0afcbe0000000000798f01e8d77c0013f97c0820020800698a41af96ad0013f97a0fe0fe12e0fe0fe12e277e7806ba7fba6797872fa2) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7602105 7650496 12818220 c0_RelativeWidePack6815_P15 (wide_covered_join band 7650497 7691247 12818220 c1_RelativeWidePack6815_P15 (wide_covered_join band 7691248 7731998 12818220 c2_RelativeWidePack6815_P15 (wide_covered_join band 7731999 7760015 12818220 c3_RelativeWidePack6815_P15 (wide_covered_join band 7760016 7877174 12818220 c4_RelativeWidePack6815_P15 (wide_covered_join band 7877175 8040178 12818220 c5_RelativeWidePack6815_P15 (wide_covered_join band 8040179 8213369 12818220 c6_RelativeWidePack6815_P15 (wide_covered_join band 8213370 8539376 12818220 c7_RelativeWidePack6815_P15 (wide_covered_join band 8539377 8865383 12818220 c8_RelativeWidePack6815_P15 (wide_covered_join band 8865384 9191390 12818220 c9_RelativeWidePack6815_P15 (wide_covered_join band 9191391 9721152 12818220 c10_RelativeWidePack6815_P15 (wide_covered_join band 9721153 10373166 12818220 c11_RelativeWidePack6815_P15 (wide_covered_join band 10373167 11025181 12818220 c12_RelativeWidePack6815_P15 (wide_covered_join band 11025182 12003203 12818220 c13_RelativeWidePack6815_P15 c14_RelativeWidePack6815_P15))))))))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 13)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 13≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤58)
    (hT0 : 3685≤T) (hT1 : T≤3699) (hnu : 7602105≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤75297964709973231 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R091

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R092
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨13,58,3700,3821,49220799040818505⟩
private def profiles_RelativeWidePack6815_P15 : ℕ → Profile
  | 0 => ⟨259971,55,81688⟩
  | 1 => ⟨24253,183,5079⟩
  | 2 => ⟨24296,184,5079⟩
  | 3 => ⟨24154,185,5079⟩
  | 4 => ⟨48056,364,10158⟩
  | 5 => ⟨29266,226,6051⟩
  | 6 => ⟨48205,359,10158⟩
  | 7 => ⟨48248,360,10158⟩
  | 8 => ⟨24304,180,5079⟩
  | 9 => ⟨24348,181,5079⟩
  | 10 => ⟨24394,178,5079⟩
  | 11 => ⟨43018,250,10158⟩
  | 12 => ⟨24439,179,5079⟩
  | 13 => ⟨24480,176,5079⟩
  | 14 => ⟨24860,163,5079⟩
  | 15 => ⟨24917,161,5079⟩
  | 16 => ⟨24970,159,5079⟩
  | 17 => ⟨25019,157,5079⟩
  | 18 => ⟨25200,152,5079⟩
  | 19 => ⟨25234,150,5079⟩
  | 20 => ⟨25324,149,5079⟩
  | 21 => ⟨25351,147,5079⟩
  | 22 => ⟨25436,146,5079⟩
  | 23 => ⟨25519,145,5079⟩
  | 24 => ⟨25456,144,5079⟩
  | 25 => ⟨25472,142,5079⟩
  | 26 => ⟨25549,141,5079⟩
  | 27 => ⟨25624,140,5079⟩
  | 28 => ⟨25699,135,5079⟩
  | 29 => ⟨25630,138,5079⟩
  | 30 => ⟨25700,137,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P15 : WideCovered band 7602105 7698888 := wide_block_sound band profiles_RelativeWidePack6815_P15 7602105 7698888 (wideData 16 0x23eb018eda0013f980000000009920061e3e004fe60000000001af81cb7f004fe6000000000274f0182ac0013f980000000006f3c061da5004fe60000000002a6d1de38004fe60000000001eeb019b3f4013f90000000000aee06b4e8013f9800000000088bc06c9e3004fe60000000002f2b17938004fe6000000000320815dfa004fe6000000000268e01d69e4013f98000000000cf7446ce8013f98d34034d01bd3891492fa6e084fe60be0be002f82f8033006e0019f9c02084b82084b94b385a4a3600ecafbae) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P15 : WideCovered band 7698889 7738366 := wide_block_sound band profiles_RelativeWidePack6815_P15 7698889 7738366 (wideData 16 0x68d7e857eecb7d082bf4000000000624bfc37d9e4f0213f98000000000adf0064874004fe6000000000521ea0324c3ba8213f98000000000aa35d05fb6b66084fe60000000000f0bec0a0b68f8213f980000000004c782f1ac013f900000000007be406adfa004fe60000000001edf019bca8013f9800000000058b02f1d4013f980000000007eac067cb0004fe6000000000167a10be5004fe6000000000226b019e5e0013f980000000005bbc537b4013f980000000008c74065b3a004fe60b40b412e0b40b412e060ab9f14eb1be808eda1ef6) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P15 : WideCovered band 7738367 7780390 := wide_block_sound band profiles_RelativeWidePack6815_P15 7738367 7780390 (wideData 16 0x22eab533fba3009fac0000000003ad8f10a4b658c327eb000000000019b08ed226825ed027eb00000000008832f0aa62a343c9faa00000000006ea75e46dedcf9384fe60000000000718e9f41c35cbb004fe60000000000b0cfab4182d92f004fe60000000004be86bb5d931ae31c4fe60000020804ffb64a16e65dbc144fe600000300076aea9071ff8f430afc80000000008e318f10e7f20c420afd0208008000de6fc26062871a440afc80000000003fb0764002bf40000000003eaf3823a9ff9870afc80000000001fe9c018e8ae6082bf40b40b412e0b40b412e073fa581f970ae030ee2cbee) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P15 : WideCovered band 7780391 7917925 := wide_block_sound band profiles_RelativeWidePack6815_P15 7780391 7917925 (wideData 16 0x16f3c07dffe013f3800000000063bb01c218004fce0000000001bab07f09804fce0000000001ebf02b28004fcd800000000018b3b0fc27013f380000000000688f0071aa5013f3800000000006fd300bef6b013f380000000002bc9b92aac3edce4fcd8000000000482ad069fb9804fce0000000000feae955b64c61153f3800000000006ed7ce01ba686aa114fce0000000001dcf8137e4027ea80000000006da6b4a96aea5089fac0000000000bcdf81219a9009fac0000000000f7964172f21009fac0b60b612e0b60b612e2fcb0fd6ef7650eee6838) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P15 : WideCovered band 7917926 8080929 := wide_block_sound band profiles_RelativeWidePack6815_P15 7917926 8080929 (wideData 16 0x9ab8376013f380000000002b980bec04fce0000000000cfb41f2f804fce0000000000f828078e404fcd80000000012be41ee8004fce00000000016b30120b404fce0000000001cd641bed004fce00000002019eec221b404fcd8000000001fe7c36bcc04fce0000000000ac78075b004fce0000000001a8a67b0dc04fce00000000001c3ef51be9013f360000000c007b86694ef74e23093f38000000000064f3b981cf1e6d093f380820020802f4fa9263b36013f380b60b612e0b60b612e063f7fe15d34e6848f8fcce0) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P15 : WideCovered band 8080930 8294870 := wide_block_sound band profiles_RelativeWidePack6815_P15 8080930 8294870 (wideData 16 0x6a0ca43a9bbc909067e6e000000000478b2536fc6ffc8067e70000000000139ae037aa2d0019f9b80000000006835e01c79d670019f9b82080082001ce7d6406c8a3a6a1c19f9b800000000038f00e3b804fce00000000003cb01ebc004fce00000000003d200bbd804fcd800000000049701edd004fce00000000004a680b2b804fce00000000004da40a6b804fce00000000005ba41f1b004fcd80000000005df00788804fce00000000006d7c1f4c004fce000000000079a4066a804fce02e02e04b82e02e04b87c22e05ae5f6458fb7afb8) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P15 : WideCovered band 8294871 8620877 := wide_block_sound band profiles_RelativeWidePack6815_P15 8294871 8620877 (wideData 16 0x820020802bb854f640019f9b80000000005aac0edc80067e700000000001b2d0bef40019f9b80000000007ca42f0a80067e6e00000000023ad0b87a0019f9b8000000000abfc2b1880067e70000000000338909e700019f9b8000000000ff6023bc80067e700000000004f8c0bae30019f9b8000000001bcf00a4e80067e70000000000067c200b8ec0067e6e00000000007dcb42f7a40067e700000000000e68ea7f0dc0067e6e0000000004228e15b6e6b845067e700000000001faa26f5486ab3f1819f9b82f02f04b82f02f04b88aaeae2070cbce6650fef0dbc) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P15 : WideCovered band 8620878 8946884 := wide_block_sound band profiles_RelativeWidePack6815_P15 8620878 8946884 (wideData 16 0x2080082002de0a05a7eba21819f9b80000000013831772800067e700820020801fcd50dbe0019f9b80000000003f24463d80067e6e000000000127811df40019f9b80000000004ce047ea80067e70000000000161a1297a0019f9b80000000005cb44b0c00067e700000000001a7c12f600019f9b80000000006ebc3f0e00067e700000000001f680cd7c0019f9b80000000009ab0523a00067e700000000002e0f158b40019f9b8000000000da6c5afc00067e70000000000274a58b320019f9b82f82f84b82f82f84b88ff1b05f35836590bedbaa) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P15 : WideCovered band 8946885 9272892 := wide_block_sound band profiles_RelativeWidePack6815_P15 8946885 9272892 (wideData 16 0x122d6617f8670019f9b8208008200f8328c5f2adc2067e70000000000464a0d8e50019f9b80000000018afc071c2a0019f9c0000000001de2c0688f60019f9b8000000000197bf1b8220019f9c00000000001ba8d03f22b40067e6e0000000000a9c6407ab370019f9c00000000003aa2c10861c42067e6e00000208012cf6d123a3a0019f9c02080000006d25844d37a80067e6e0000000004ee916f640019f9c0000000001792c1edf80067e6e000000000731c0e9750019f9c02080082003e24804977fe42019f9b83803804b83803804b8ade09069ba9e25918ea978) (by decide +kernel)
private theorem c9_RelativeWidePack6815_P15 : WideCovered band 9272893 9884155 := wide_block_sound band profiles_RelativeWidePack6815_P15 9272893 9884155 (wideData 16 0x9c2c0a1ca4002bf2f0000000000acb80a1f6a002bf2f8000000000abf0067866002bf2f8000000000dfb80a1ae4002bf2f80000000010f2c0a38ba002bf2f80000000014ef807ceea002bf2f8000000001ae64065cea002bf2f80000000001864b42aef9800afcbe08200208023d941bf88000afcbc0000000003be903cfd002bf2f80000000015ef44abc800afcbe0000000007e0b03b74002bf2f80000000001c63d19afd002bf2f80000000001bf59428b597b342bf2f800000000028beb029e0fc0067e6e0e60e612e0e60e612e233a34275e69981891de6f68) (by decide +kernel)
private theorem c10_RelativeWidePack6815_P15 : WideCovered band 9884156 10536170 := wide_block_sound band profiles_RelativeWidePack6815_P15 9884156 10536170 (wideData 16 0x1a77e02e308c00afcbe0000000000a7ea43b3c800afcbe0000000000e8d3c3b99b1082bf2f80000000008f2df0687e002bf2f82080082011f6be419ae829082bf2f84100104004bbcc05821c2a382bf2f8000000000bf640f1d74002bf2f8000000000baa80b9eaa002bf2f8208008200acad0f1c34002bf2f000000000099780b6838002bf2f80000000009cb80b39f0002bf2f80000000009b380a3efa002bf2f8000000000bcb40b9b32002bf2f8000000000cfe40bcd36002bf2f8000000000d9280a2920002bf2f83a83a84b83a83a84b8eaade08922dfc592f78cb4) (by decide +kernel)
private theorem c11_RelativeWidePack6815_P15 : WideCovered band 10536171 11188184 := wide_block_sound band profiles_RelativeWidePack6815_P15 10536171 11188184 (wideData 16 0xb6d7c0a6da7002bf2f020800820068a6f43822082bf2f800000000018fcb03e6d9800afcbe000000000069fb8061e39002bf2f80000000001ffee04b768400afcbe000000000072a2d475cef082bf2f82080082003a2ae43dacd000afcbe0c300000032acfc7a88e9082bf2f8208000000b8fab4aeb49420afcbc0000000000f2abc1368a4002bf2f82080082007c32a45eb2d420afcbe000000000062aa067e8400afcbe000000000077c7c0aab76002bf2f80000000002cf4e0dce5002bf2f80000000004eae906fa2cc00afcbe0f40f412e0f40f412e1ff8f82f2ca5a81a94972872) (by decide +kernel)
private theorem c12_RelativeWidePack6815_P15 : WideCovered band 11188185 12288459 := wide_block_sound band profiles_RelativeWidePack6815_P15 11188185 12288459 (wideData 16 0x820020800bdbbae41bf8fe3f41882bf2f8000000000fb72907a74ab0004fe5f0208008200b8bea06bfbab6004fe5e80000000007cbba03b3dfb2004fe5f00000000008aa3c03de69aa004fe5f00000000005e69e02a2bc78004fe5f00000000007a67802eb9cf6004fe5f0208008200febd060eb0c8013f97c0000000000ffef0066baa80013f97c0000000000a8e342a9f7b004fe5f00000000004a3c914822d4013f97a000000000062dbbe14c36b7406113f97c0000000000f0c2c178cf5002bf2f82080082007d79d59a32082bf2f800000000019b5e01fb3f000afcbe0fa0fa12e0fa0fa12e36dbe4271a34c01d15b6bc2e) (by decide +kernel)
private theorem c13_RelativeWidePack6815_P15 : WideCovered band 12288460 12818220 := wide_block_sound band profiles_RelativeWidePack6815_P15 12288460 12818220 (wideData 10 0x20800820019738f53acc7794513f97a00000000006be6943c8fb84213f97c18600618006cc6f901caf9e4f8213f97c00000000052f807efdf800afcbe000000000536907db08800afcbe000000000563d07ca0d800afcbc00000000057a807be5a800afcbe0000000005bbb07ba8d000afcbe0000000000b6d07bf3e800afcbe12412412e12412412e468af02758acb81e17c30bf4) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7602105 7698888 12818220 c0_RelativeWidePack6815_P15 (wide_covered_join band 7698889 7738366 12818220 c1_RelativeWidePack6815_P15 (wide_covered_join band 7738367 7780390 12818220 c2_RelativeWidePack6815_P15 (wide_covered_join band 7780391 7917925 12818220 c3_RelativeWidePack6815_P15 (wide_covered_join band 7917926 8080929 12818220 c4_RelativeWidePack6815_P15 (wide_covered_join band 8080930 8294870 12818220 c5_RelativeWidePack6815_P15 (wide_covered_join band 8294871 8620877 12818220 c6_RelativeWidePack6815_P15 (wide_covered_join band 8620878 8946884 12818220 c7_RelativeWidePack6815_P15 (wide_covered_join band 8946885 9272892 12818220 c8_RelativeWidePack6815_P15 (wide_covered_join band 9272893 9884155 12818220 c9_RelativeWidePack6815_P15 (wide_covered_join band 9884156 10536170 12818220 c10_RelativeWidePack6815_P15 (wide_covered_join band 10536171 11188184 12818220 c11_RelativeWidePack6815_P15 (wide_covered_join band 11188185 12288459 12818220 c12_RelativeWidePack6815_P15 c13_RelativeWidePack6815_P15)))))))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 13)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 13≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤58)
    (hT0 : 3700≤T) (hT1 : T≤3821) (hnu : 7602105≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤49220799040818505 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R092

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R093
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨13,58,3750,3821,40052327279034927⟩
private def profiles_RelativeWidePack6815_P15 : ℕ → Profile
  | 0 => ⟨16536,4,5080⟩
  | 1 => ⟨33072,8,10160⟩
  | 2 => ⟨43018,250,10158⟩
  | 3 => ⟨48205,359,10158⟩
  | 4 => ⟨24253,183,5079⟩
  | 5 => ⟨24304,180,5079⟩
  | 6 => ⟨24439,179,5079⟩
  | 7 => ⟨24394,178,5079⟩
  | 8 => ⟨24860,163,5079⟩
  | 9 => ⟨24917,161,5079⟩
  | 10 => ⟨24970,159,5079⟩
  | 11 => ⟨25019,157,5079⟩
  | 12 => ⟨25200,152,5079⟩
  | 13 => ⟨25234,150,5079⟩
  | 14 => ⟨25324,149,5079⟩
  | 15 => ⟨25351,147,5079⟩
  | 16 => ⟨25436,146,5079⟩
  | 17 => ⟨25519,145,5079⟩
  | 18 => ⟨25456,144,5079⟩
  | 19 => ⟨25472,142,5079⟩
  | 20 => ⟨25549,141,5079⟩
  | 21 => ⟨25624,140,5079⟩
  | 22 => ⟨25699,135,5079⟩
  | 23 => ⟨25630,138,5079⟩
  | 24 => ⟨25700,137,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P15 : WideCovered band 7602105 7740913 := wide_block_sound band profiles_RelativeWidePack6815_P15 7602105 7740913 (wideData 16 0x6680699400afd0000000001a820c5abf5e650c4fe60000000006a1dfc6afda1c8213f98000000001db1788013f98000000001ea16c0013f98000000001fa1680013f980000000001824570004fe6000000000061a1390013f9000000000018606af004fe6000000000063a1380013f9800000000019344a8004fe6000000000065e11c8013f9830c00c3003fb9e04ff7ab4084fe6000000000400009fac0000000006b8070d2c0819f9c02d82d84b82d82d84b81ba80788a400ed3f86c) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P15 : WideCovered band 7740914 7790578 := wide_block_sound band profiles_RelativeWidePack6815_P15 7740914 7790578 (wideData 16 0x801e6d41821009fac0000000002a0942ba3009fac000000000566948c7f009fac000000000074c3166eac027eb00000000001b65c5482f009fac00000200013b87a0ecdb0009faa00000000022ab0397d004fe60000030004f79d6bf1004fe60000000005e3f4aae9004fe6000000000075be1670fc013f98000008000187aec4861e8013f98000000000ca018800afc8208000000cf16b000afd0000000000cd01e800afc8000000000da159000afd02d02d04b82d02d04b84b6be058e3aec10ee31bb4) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P15 : WideCovered band 7790579 7938300 := wide_block_sound band profiles_RelativeWidePack6815_P15 7790579 7938300 (wideData 16 0xe9806e404fce00000000003da81fa013f36000000000128f03dbc013f38000000000136e02967013f380000000001738049b2013f380000000001a9d04831013f360000000001f3d038ba013f38000000000324df53b4e658c74fce0000000001bfb40b58ad013f380000000001acaad2ace3cf424fcd80000000002ae9e078abd004fce00000000002baed1be359404fce0000000000fd3ee19ee1be0113f3800000000046c801b24009faa00000000027bcc18f8009fac0b60b612e0b60b612e3efd859b0f3e10eef9f70) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P15 : WideCovered band 7938301 8101304 := wide_block_sound band profiles_RelativeWidePack6815_P15 7938301 8101304 (wideData 16 0x49e00b5f004fce00000000004fb426fe004fcd80000000005bec0abb004fce00000000006aac07bc004fce00000000007ce82a8d004fce00000000008e7c06ab804fcd8000000000aebc2e89004fce0000000000d92c4f6013f3800000000043a90cf24013f380000020802b0e0c8c04fcd8000000000aebc0bc8c04fce00000000013ead43bb804fce00000000011bf41afe404fce00000000001976a59eea013f36000000000064e78430ec04fce02e02e04b82d82d84b81c38e05ab583a10f964b30) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P15 : WideCovered band 8101305 8335621 := wide_block_sound band profiles_RelativeWidePack6815_P15 8101305 8335621 (wideData 16 0xc0137e3cf41a3ff6be4b067e6e0820020800ede71c81f6fd631019f9c0000000000fa3180ebbaf360c19f9b8000000000ab70c4dce6f790819f9c00000000002e7fb0ceb2cc0067e6e0000000000f18a0070c7bac0067e6e0820020807a28f406cb368a21819f9b80000000001eac0f88004fce000000000028e42239804fce000000000029240f3d004fcd80000000002ba8229a004fce00000000002c340eee004fce00000000002e240e5b804fce000000000039a4235b004fcd80000000003af80bdf804fce02e02e04b82e02e04b84d60c05b639e210fbe2e28) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P15 : WideCovered band 8335622 8661628 := wide_block_sound band profiles_RelativeWidePack6815_P15 8335622 8661628 (wideData 16 0x42dc5be660019f9b8208008200cc61575d00067e700000000000e1c0dfbc0019f9b80000000003920130e00067e700000000000fbd0d9e40019f9b80000000004ba0362b00067e6e000000000165f0cf260019f9b80000000006960336c00067e700000000001efc0cb7a0019f9b80000000009ab8324d80067e700000000002f3907a2d0019f9b800000000109ac1fbb00067e700000000005e5e05b2a0019f9b80000000001924a1ff80067e7000000000007bf66238a40067e6e0bc0bc12e0bc0bc12e0abe85eb89b210ffa0a7a) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P15 : WideCovered band 8661629 8987635 := wide_block_sound band profiles_RelativeWidePack6815_P15 8661629 8987635 (wideData 16 0x573e01a21bc0067e6e0000000001a6a0183eb270819f9c02080082001ce1e05ab0b6a3019f9b82080082011db173d800067e7000000000007da0bea00019f9b80000000002a3c47da80067e6e0000000000af912cf20019f9b80000000002da84bcd80067e700000000000bed139e40019f9b80000000003a3c4f5b00067e700000000000f58149a80019f9b8000000000482c43e800067e70000000000130b0ea360019f9b80000000005be85a0f00067e700000000001af817af20019f9b82f82f84b82f82f84b85abbf068208a2110c7d868) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P15 : WideCovered band 8987636 9313643 := wide_block_sound band profiles_RelativeWidePack6815_P15 8987636 9313643 (wideData 16 0x67a640799ab0019f9b80000000001ffe91f9b30019f9c00000000002b35b84d6a8c0067e6e082002080239fef26eae90819f9c0000000000a874271ec0067e6e0000000003a9c01db1c00067e7000000000046f801ba8b00067e6e0000000005a78018bac00067e700000000006e4f03cb0c40067e6e00000000006b93806b9b10019f9c000000000029a0c03eb8ac0067e6e0820020801e0e7d1a78650819f9c00000000009ef0065de20019f9b8000000000bb606bdd80067e70000000000372c0c9bc0019f9b83883884b83883884b8983090abe9cea491979e36) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P15 : WideCovered band 9313644 9965657 := wide_block_sound band profiles_RelativeWidePack6815_P15 9313644 9965657 (wideData 16 0x7db00a4ebc002bf2f8208008200be690bc8b8002bf2f80000000005cb00a3c62002bf2f000000000069bc0a48e8002bf2f8000000000693c0699b0002bf2f800000000089a40a49ee002bf2f80000000009f640a6cae002bf2f8000000000c9f80a196a002bf2f8000000000fdbc06b92e002bf2f82080082001832b42ae69800afcbe0000000001fcf019eb8000afcbc000000000238d119400afcbe00000000033ac16f24002bf2f800000000129a827ad800afcbe00000000073aa0f9e7002bf2f83983984b83983984b85b3af07cb9f7e111ebea74) (by decide +kernel)
private theorem c9_RelativeWidePack6815_P15 : WideCovered band 9965658 10617672 := wide_block_sound band profiles_RelativeWidePack6815_P15 9965658 10617672 (wideData 16 0x2eb4805fa5c400afcbe0820020801afdbd572bfb082bf2f80000000018bfc0aff25002bf2f80000000001aa4b1dbae002bf2f80000000001f6d90e8f2d420afcbe000000000166f380a0eb0002bf2f8208008200ac2e941aa4be3082bf2f84100104002cfb90583f860502bf2f80000000006ff40f492c002bf2f80000000006d300bc966002bf2f820800820069b10efab6002bf2f00000000005b2c0b7f6e002bf2f80000000005d200b59bc002bf2f80000000005c300a5e7e002bf2f80000000006e700bbe64002bf2f83a83a84b83a83a84b88f2a808b25d241138b7e30) (by decide +kernel)
private theorem c10_RelativeWidePack6815_P15 : WideCovered band 10617673 11269686 := wide_block_sound band profiles_RelativeWidePack6815_P15 10617673 11269686 (wideData 16 0x16da80a6cf4002bf2f8000000001fe38761c800afcbe000000000072ef4074e63002bf2f02080082003c7ee419648420afcbe000000000561f0483ab800afcbe000000000633f198eb002bf2f8000000000197180482f9400afcbe0000000000bef6143fa65082bf2f820800820049a00a0928002bf2f80000000001b24623bed082bf2f80000000015b304379f3082bf2f000000000028e2f05b769000afcbe08200208012d9651eca67082bf2f800000000149284bb9400afcbe000000000060ce80b5f60002bf2f83d03d04b83d03d04b8986cf0bbacb30794ab19ee) (by decide +kernel)
private theorem c11_RelativeWidePack6815_P15 : WideCovered band 11269687 12369961 := wide_block_sound band profiles_RelativeWidePack6815_P15 11269687 12369961 (wideData 16 0x1ebc47d34f000afcbe08200208023ac059bba800afcbe082002080076ebeb41c2ca628c1a02bf2f80000000009873c07b3aa7a004fe5f02080082006c28f06ca4d6c004fe5e80000000004baff03bb0928004fe5f00000000004f24e03e3d976004fe5f00000000003b37c02a71ebc004fe5f00000000004a3b802f29e76004fe5f02080082009a6d060de7e8013f97c0000000000ab838067a37b0013f97c00000000006adb027af39004fe5f00000000002c2a9138f9d4013f97a00000000052beb4537efe9819c4fe5f000000000028a0d0586be400afcbe0fc0fc12e0fc0fc12e122be0275baf881a95caadaa) (by decide +kernel)
private theorem c12_RelativeWidePack6815_P15 : WideCovered band 12369962 12818220 := wide_block_sound band profiles_RelativeWidePack6815_P15 12369962 12818220 (wideData 8 0x820020805a1fb53b4aa9d4513f97a000000000676a50f2cf31084fe5f0618018601a92de01cb8b75d0213f97c000000000320b08825a000afcbe000000000324c07eb8f000afcbe00000000032cc07daca000afcbc000000000339d07cf5c000afcbe12412412e12412412e2b38f02a7df5f01b17d6fd70) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7602105 7740913 12818220 c0_RelativeWidePack6815_P15 (wide_covered_join band 7740914 7790578 12818220 c1_RelativeWidePack6815_P15 (wide_covered_join band 7790579 7938300 12818220 c2_RelativeWidePack6815_P15 (wide_covered_join band 7938301 8101304 12818220 c3_RelativeWidePack6815_P15 (wide_covered_join band 8101305 8335621 12818220 c4_RelativeWidePack6815_P15 (wide_covered_join band 8335622 8661628 12818220 c5_RelativeWidePack6815_P15 (wide_covered_join band 8661629 8987635 12818220 c6_RelativeWidePack6815_P15 (wide_covered_join band 8987636 9313643 12818220 c7_RelativeWidePack6815_P15 (wide_covered_join band 9313644 9965657 12818220 c8_RelativeWidePack6815_P15 (wide_covered_join band 9965658 10617672 12818220 c9_RelativeWidePack6815_P15 (wide_covered_join band 10617673 11269686 12818220 c10_RelativeWidePack6815_P15 (wide_covered_join band 11269687 12369961 12818220 c11_RelativeWidePack6815_P15 c12_RelativeWidePack6815_P15))))))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 13)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 13≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤58)
    (hT0 : 3750≤T) (hT1 : T≤3821) (hnu : 7602105≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤40052327279034927 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R093

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R094
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨13,59,3600,3624,40141123639256505⟩
private def profiles_RelativeWidePack6815_P15 : ℕ → Profile
  | 0 => ⟨29266,226,6051⟩
  | 1 => ⟨29307,227,6051⟩
  | 2 => ⟨46277,356,9657⟩
  | 3 => ⟨48098,365,10158⟩
  | 4 => ⟨48056,364,10158⟩
  | 5 => ⟨24154,185,5079⟩
  | 6 => ⟨24296,184,5079⟩
  | 7 => ⟨24253,183,5079⟩
  | 8 => ⟨24348,181,5079⟩
  | 9 => ⟨24304,180,5079⟩
  | 10 => ⟨24394,178,5079⟩
  | 11 => ⟨24526,177,5079⟩
  | 12 => ⟨24480,176,5079⟩
  | 13 => ⟨43018,250,10158⟩
  | 14 => ⟨24515,173,5079⟩
  | 15 => ⟨24917,161,5079⟩
  | 16 => ⟨24970,159,5079⟩
  | 17 => ⟨25019,157,5079⟩
  | 18 => ⟨25234,150,5079⟩
  | 19 => ⟨25324,149,5079⟩
  | 20 => ⟨25351,147,5079⟩
  | 21 => ⟨25436,146,5079⟩
  | 22 => ⟨25456,144,5079⟩
  | 23 => ⟨25536,143,5079⟩
  | 24 => ⟨25549,141,5079⟩
  | 25 => ⟨25624,140,5079⟩
  | 26 => ⟨25630,138,5079⟩
  | 27 => ⟨25764,134,5079⟩
  | 28 => ⟨25700,137,5079⟩
  | 29 => ⟨25699,135,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P15 : WideCovered band 7733176 7744588 := wide_block_sound band profiles_RelativeWidePack6815_P15 7733176 7744588 (wideData 16 0x820020802f6e66983faac77081a24000000000065901cbfa00068900000000016f01bebc40068900000000001b78437f000b0a030c00c3006b05b67f020b0a800000000040ae00208200208030cb0028000000000ad10c3a00a8800000000019304e5880524000000000063a01b24800068980000000003aa0a09cbac2a081a260000000007a0065bf6001a2400000000006dd14d21001a26000000000073f01becb000b0b00000000001cb006a870002c2c0b40b41300b40b41304a5de0075b7bdb400ee22afa) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P15 : WideCovered band 7744589 7796591 := wide_block_sound band profiles_RelativeWidePack6815_P15 7744589 7796591 (wideData 16 0x15b2c1758b100a8600000000006edc07eea8402a180000000000e8a72e49a300a8620000000000778e507ed37d422a1800000000003fa0c47ba8b7508a860000000000323d614bb826bc42a18000000000049f9914a278ea14a860000000000161cb53ef8ef00583000000000023ece90a4be0dc0160c000000000018f3ffd4658799c4160c0000000000993cb0da7aaae0c583000000000007083ed4effebb7082c28000000000071d2d844b79bb9082c280000000000e4c25a4983ebed082c280000000006b4ef91e4878f030b0a02d82d84c02d82d84c08df3fee076fa6f7c20ee37b3c) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P15 : WideCovered band 7796592 7945538 := wide_block_sound band profiles_RelativeWidePack6815_P15 7796592 7945538 (wideData 16 0x3a638ed078ba6d43522802080082003cbd8fa0b99e6f44522800000000003c7490a82b8b61548a0000000000130c1feea0148a200000000013dd0e8a80148a000000000016ec07de50148a00000000001a48018ebac0522800000000009a2107a835f42522880000000001fa8b48826f250948a0000000000460901d67e00522800000000011d2c36e82b0148a00000000000f586d53bd34ac4522880000000007f39d018edc2d98b522800000000009bb8160efd00a8600000000002f3f04dfaf402a1802d82d84c02d82d84c01f7ec0f9ffdb050ef25dfe) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P15 : WideCovered band 7945539 8109893 := wide_block_sound band profiles_RelativeWidePack6815_P15 7945539 8109893 (wideData 16 0x1ae80f9a80522800000000001bf86f20148a00000000000768019b30148a000000000007f802b640148a20000000000a6f06abd0148a00000000000b5c11e00522800000000002e26849dae8270948a000000000023181897c0148a00000000002abc079640148a000000000033f811eff0148a00000000003f3c09ce39c0522800000000017ba013be790148a2000000000060afc069fa5a4252280000000000fdfb0a48759425228000000000049af95dbb5a40522802e02e04c02e02e04c05b7db93e24d6850f972da6) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P15 : WideCovered band 8109894 8335883 := wide_block_sound band profiles_RelativeWidePack6815_P15 8109894 8335883 (wideData 16 0x82002080331def236b6af42068922000000000529f0ce2ba000689200000000004fe81f9b3001a24880000000013fe05a282f001a24800000000002b3ca4ccf1cb5081a24880000000010870801dfd92880b06892000000000012fd0ad2a0148a0000000000173c0beb80148a20000000001e5c01e6f0148a0000000000275b0dd3e0148a00000000000e613e8c0522800000082004a2046ed005228800000000018b58d98ec0148a000000000052690a9330148a0082000000062ae15a4900522802e02e04c02e02e04c01ceae05a2592468fbf3dac) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P15 : WideCovered band 8335884 8664594 := wide_block_sound band profiles_RelativeWidePack6815_P15 8335884 8664594 (wideData 16 0xe6b11ffa001a248800000000048e05a8e0006892000000000016a80ca22001a24880000000007b702ebd800689200000000002e5e0a9aa001a24880000000012f281f3d80068920082002080074f3106fc30001a248800000000028600ab8800689200000000000af905fc00689220000000000e2e03e77001a24800000000003ea4c4ccf4dab0c1a2488000000000d9e40bcf21001a24800000000012a20224b75001a24880000000015a31222cf1dc40689200000000000aeaac1b8aeb001a24802f02f04c02f02f04c02d2dd1afa8dbc60ffa1936) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P15 : WideCovered band 8664595 8993304 := wide_block_sound band profiles_RelativeWidePack6815_P15 8664595 8993304 (wideData 16 0x6791ba24001a24880000000001a6c5a9b8006892000000000006de158a4001a24880000000001d20579e0006892000000000007c816de0001a248800000000029a85ffb80068920082002080264f5df7e001a2480000000001c80dd66001a2480000000001ed0dbe0001a2488000000000187c367980068920000000000065f0cf62001a24880000000001bac5bd800068920000000000071a0d8e4001a24880000000001e603379800689200000000000a3b0caf8001a24802f82f84c02f82f84c01ea4d05eb2a26690ca3964) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P15 : WideCovered band 8993305 9322015 := wide_block_sound band profiles_RelativeWidePack6815_P15 8993305 9322015 (wideData 16 0x2e9903b6edc00689220000000004a6d019b4d400689200820020800a0eb9323ea5081a24880000000003a6806d8be001a24800000000003e280658e2001a24880000000004b6c6afa0006892000000000016bb0c9e2001a24880000000006df8231bc006892000000000023eb01a26ec00689220000000001a7f1d8f6cc20689200000000005e4c05d2be8006892200000000006783406783d001a24800000000002b39ec6c77ec00689221040041002fce84e35f60101a2480000000001e91382a001a24803803804c03803804c029b3d06920f226919a5970) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P15 : WideCovered band 9322016 9876714 := wide_block_sound band profiles_RelativeWidePack6815_P15 9322016 9876714 (wideData 16 0x2080082005da50b4976002c28880000000001fbc06ccb8002c28880000000002a6406bfa6002c28880000000002fe40a28e2002c28880000000003a64063ebe002c28800000000004d3c0a6db6002c28880000000005efc6ea9800b0a2200000000023ba0cff8002c2888000000001086c0a7862002c288800000000018ecc01bf9dc00b0a220820020800b8fe90a58fdec90b0a220000000000e9e07ff4001a24800000000004cb80a2964001a24880000000004e244e5bc00689200000000001b8f01c2af000689200e60e61300e60e61300b182c270de7e81891ea797e) (by decide +kernel)
private theorem c9_RelativeWidePack6815_P15 : WideCovered band 9876715 10534135 := wide_block_sound band profiles_RelativeWidePack6815_P15 9876715 10534135 (wideData 16 0x820020800a9e670eca6d082c28880000000010b300ebaa2002c2888000000001b9b85b7f400b0a2200000000007dd6833ac73002c28886180186003824d448f383e282c28800000000002ab80f39bc002c288800000000029ac0bcd6c002c28880000000002b2c0be8b0002c2888000000000d843fad9000b0a200820020800640a5be6002c28880000000001f6c0aeab0002c288800000000028e80b0ee0002c2888000000000293c0a48a2002c28800000000002e200e0da6002c28880000000002ea00a78e8002c28883a83a84c03a83a84c02eade07f7c9f4692f6adb6) (by decide +kernel)
private theorem c10_RelativeWidePack6815_P15 : WideCovered band 10534136 11191557 := wide_block_sound band profiles_RelativeWidePack6815_P15 10534136 11191557 (wideData 16 0x46ea03ff7002c28882080082001b2bf52e7f8420b0a220000000001b9c018e88800b0a22000000000262e1abe1002c2888000000000bf60234d39082c2880000000001b83406692b002c28880000000001829f85ce8b800b0a220820020800b8af7062922ac20b0a2200000000037ab02c62d000b0a220000000005a781087f002c28882080082001c28842aeddc20b0a220000000001f9b01b348000b0a220000000002b0901975fc00b0a20000000000425f06a74f400b0a2200000000077ac12ca2e420b0a220f40f41300f40f4130074ae8321a22c8199496edf0) (by decide +kernel)
private theorem c11_RelativeWidePack6815_P15 : WideCovered band 11191558 12259867 := wide_block_sound band profiles_RelativeWidePack6815_P15 11191558 12259867 (wideData 16 0xf8ebc23cfe0d00160c240000000000ae9b016fa64d00160c2408200208006baa012cb35f80160c24000000000073a200efa79c00160c2200000000006cae00b9d26a80160c240000000000608e4070bacb80160c2400000000006c8b807fda0980160c240820020802e58418bbaf200583088000000000e830365d2b0058309030c00c3008ffe894f7acf46c58308820800820019fdbcacb4fc20b0a2200000000033dc11ba0002c28880000000015e340b28bb002c28802080082001bb5d559ec082c28880000000007930169b000b0a220fa0fa1300fa0fa1300b6a7c26d979c81c15b72e2c) (by decide +kernel)
private theorem c12_RelativeWidePack6815_P15 : WideCovered band 12259868 12999465 := wide_block_sound band profiles_RelativeWidePack6815_P15 12259868 12999465 (wideData 13 0x2080082003ff3a42f749bf145830880000000001cf5f04aedeb90058309020800820078bfc4cd7fb370858308800000000018acd51e22d3710583090410010400bcfc901de79abb03160c22000000000138c07cbfe000b0a220820020800ec946ab2f800b0a220000000000e7f059719000b0a220000000000ebe05860a800b0a220000000000f1804f3fc000b0a220000000000f8f04e7ac000b0a22000000000123e04de69000b0a201241241301241241300bf824236fe5c01d97bb9a78) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7733176 7744588 12999465 c0_RelativeWidePack6815_P15 (wide_covered_join band 7744589 7796591 12999465 c1_RelativeWidePack6815_P15 (wide_covered_join band 7796592 7945538 12999465 c2_RelativeWidePack6815_P15 (wide_covered_join band 7945539 8109893 12999465 c3_RelativeWidePack6815_P15 (wide_covered_join band 8109894 8335883 12999465 c4_RelativeWidePack6815_P15 (wide_covered_join band 8335884 8664594 12999465 c5_RelativeWidePack6815_P15 (wide_covered_join band 8664595 8993304 12999465 c6_RelativeWidePack6815_P15 (wide_covered_join band 8993305 9322015 12999465 c7_RelativeWidePack6815_P15 (wide_covered_join band 9322016 9876714 12999465 c8_RelativeWidePack6815_P15 (wide_covered_join band 9876715 10534135 12999465 c9_RelativeWidePack6815_P15 (wide_covered_join band 10534136 11191557 12999465 c10_RelativeWidePack6815_P15 (wide_covered_join band 11191558 12259867 12999465 c11_RelativeWidePack6815_P15 c12_RelativeWidePack6815_P15))))))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 13)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 13≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤59)
    (hT0 : 3600≤T) (hT1 : T≤3624) (hnu : 7733176≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤40141123639256505 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R094

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R095
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨13,59,3625,3649,40165473124689310⟩
private def profiles_RelativeWidePack6815_P15 : ℕ → Profile
  | 0 => ⟨48056,364,10158⟩
  | 1 => ⟨48098,365,10158⟩
  | 2 => ⟨29266,226,6051⟩
  | 3 => ⟨29307,227,6051⟩
  | 4 => ⟨48024,369,10028⟩
  | 5 => ⟨48205,359,10158⟩
  | 6 => ⟨24196,186,5079⟩
  | 7 => ⟨24253,183,5079⟩
  | 8 => ⟨24348,181,5079⟩
  | 9 => ⟨24304,180,5079⟩
  | 10 => ⟨24394,178,5079⟩
  | 11 => ⟨24296,184,5079⟩
  | 12 => ⟨24480,176,5079⟩
  | 13 => ⟨43018,250,10158⟩
  | 14 => ⟨24515,173,5079⟩
  | 15 => ⟨24917,161,5079⟩
  | 16 => ⟨24970,159,5079⟩
  | 17 => ⟨25019,157,5079⟩
  | 18 => ⟨25234,150,5079⟩
  | 19 => ⟨25324,149,5079⟩
  | 20 => ⟨25351,147,5079⟩
  | 21 => ⟨25436,146,5079⟩
  | 22 => ⟨25456,144,5079⟩
  | 23 => ⟨25536,143,5079⟩
  | 24 => ⟨25549,141,5079⟩
  | 25 => ⟨25624,140,5079⟩
  | 26 => ⟨25630,138,5079⟩
  | 27 => ⟨25764,134,5079⟩
  | 28 => ⟨25700,137,5079⟩
  | 29 => ⟨25699,135,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P15 : WideCovered band 7733176 7744340 := wide_block_sound band profiles_RelativeWidePack6815_P15 7733176 7744340 (wideData 16 0x208008200ecb3e3a1b3db58c9068900000000001a240efa800b0a030c00c3006fbd3b3d79082c2808200208020ce0018000000000c63200a00000000006007db00500000000002803f68001a00000000002c03de0002c8000000000990cc7800a8800000000019b0076d68001a26000000000068f01de9840068980000000003b2ae09e27c36082c2c000000000123b382f7a65c820b0a8000000001b804af5002c2c00000000056df01f21e62082c2c0b40b41300b40b4130370ef4068a30ba000ee22afa) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P15 : WideCovered band 7744341 7797617 := wide_block_sound band profiles_RelativeWidePack6815_P15 7744341 7797617 (wideData 16 0x7aec0e3db6ec22a0f80000000019f281a9b2700a83e0000000002ae23de6100a86000000000006f9e136986500a83e0000000000f8e31271fe9a442a0f80000000004e37e4cd7bbc02a0f8000000000e960224c31b032a0f800000000079f4846af286708582e0000000001b0d354aa9ad0058300000000002b6ab5063aeafc0160b80000000002abfea90608a697d085830000000000525dfc5abea2d82160b80000000002b378bd339c24dca0b0a000000000038b1d790fae358400b0a00000000001bbdfe1161b7c8800b0a02d82d84c02d82d84c09df2f26072bbbef200ee36f6c) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P15 : WideCovered band 7797618 7946534 := wide_block_sound band profiles_RelativeWidePack6815_P15 7797618 7946534 (wideData 16 0x820020801b6d621b0cb8b44521f000000000038a3f08c35e240d487c00000000012de01b7da80521f00000000018c6007da3ce03521f80000000004f70637b80521f00000000005b780e4d00521f000000000068bc5a0dc0521f00000000006fe00769f501487c0000000001f2841ef2efb09487c000000000079c25225b74dc2521f0000000000fdb9135ceddc9521f0000000001dee8071eff01487e00000000012cc744e2eb5902521f00000000009ca80a5c6b00a83e0000000002ec802eec8c02a0f82d82d84c02d82d84c02827c0f9a9af850ef27e20) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P15 : WideCovered band 7946535 8110857 := wide_block_sound band profiles_RelativeWidePack6815_P15 7946535 8110857 (wideData 16 0x6aa02df601487c000000000070904aba01487c000000000074c02ff301487c00000000007e903ba401487e0000000000a5e0596901487c0000000000b490283001487c0000000000e4801a3801487c0000000000f6f0ab6d01487c000000000135c028a301487c0000000000a5ee527af73ec2521f00000000010c2407bd3d01487c0000000005b2e03d69e40521f80000000001866a06e6dec0521f00000000005be30e0828ec4521f00000000003e74e54d29e40521f02e02e04c02e02e04c04e27e93963dfe50f974d2a) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P15 : WideCovered band 8110858 8357342 := wide_block_sound band profiles_RelativeWidePack6815_P15 8110858 8357342 (wideData 16 0x2b59c996ce3f101a23e000000000019bcae51efb7b9c00688fa0820020806abee20aee64a420688f8000000000531902d2db000688fa00000000053e9109258400688f80000000005aea01bf9e31001a23e80000000001eafe4e8a8dfb081a23e0000000000eefaf01ea9ee1c0b0688f80000000001bfd01c7601487c000002080324c528f401487c082000000676d52d6601487c0000000006646ba01487e000000000738169b00521f0000000001df01e40521f000000000018b813fd80521f02e02e04c02e02e04c01ceec05a6183268fbf5cb0) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P15 : WideCovered band 8357343 8685988 := wide_block_sound band profiles_RelativeWidePack6815_P15 8357343 8685988 (wideData 16 0x2cb8536a800688f80000000000e3d0e966001a23e80000000003fbc3a2d000688f8000000000167e0dfe6001a23e80000000007a7c37df000688f80000000005b5941babf000688fa082002080071c47e78001a23e00000000001da413fa800688f80000000000a0c039b0001a23e00000000002ba86a4001a23e800000000038780aecc00688f800000000012380bb7a001a23e80000000005aac2e4bc00688f80000000000e48a933c9ace430688fa00000000056ec47ef6b73101a23e02f02f04c02f02f04c058e3d1abe2b2860ffeb874) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P15 : WideCovered band 8685989 9014634 := wide_block_sound band profiles_RelativeWidePack6815_P15 8685989 9014634 (wideData 16 0x618148b0001a23e0000000000192852dc800688fa000000000068c14f3a001a23e00000000001b6c571a000688fa000000000077d0187cc800688f800000000007bf18a70001a23e80000000006f7967af000688f80820020800e13b48800688f80000000007203a09800688f80000000007ac37ae800688fa000000000064f16d32001a23e0000000000197c3a0a000688fa00000000006ae0dea8001a23e00000000001c383738000688fa000000000078d0db2a001a23e02f82f84c02f82f84c01f2c905f23a20690cecfa0) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P15 : WideCovered band 9014635 9343280 := wide_block_sound band profiles_RelativeWidePack6815_P15 9014635 9343280 (wideData 16 0x236d01a75a800688f80000000002e4803a35d400688fa00000000047dc1ea79001a23e0000000001ec740eaaa3001a23e82080082002eecf4893cdc20688f80000000000f7e019e5b800688fa00000000012cb1d83e001a23e00000000005aa43e7f000688f80000000001b5e04d35001a23e00000000008ee0062ef3001a23e8000000000cc680b5ee7001a23e000000000109a4531cab081a23e800000000019a2e13aff001a23e0000000000296bec5879a400688fa1040041001adf84daf83e101a23e03803804c03803804c029f3f0697cc606919eeeac) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P15 : WideCovered band 9343281 9959491 := wide_block_sound band profiles_RelativeWidePack6815_P15 9343281 9959491 (wideData 16 0xe3e038fee800b09f20000000000eb902af5f000b09f2082002080176a42bb1f000b09f000000000007fc01bf4d000b09f20000000000a8a01af2f800b09f20000000000e0a029ebf000b09f20000000000e99019eaa800b09f0000000000127b01876c000b09f20000000001a8e02ae1f800b09f2000000000239f178be002c27c8000000000fab84e2002c27c0000008200ab380afb6a002c27c800000c3003ce98c6ff2ac00b09f208200208007bd6207f871fc90b09f200000000016eb0283b9800688f80e60e61300e60e61300b7aec271bebd81891ef0db8) (by decide +kernel)
private theorem c9_RelativeWidePack6815_P15 : WideCovered band 9959492 10616783 := wide_block_sound band profiles_RelativeWidePack6815_P15 9959492 10616783 (wideData 16 0x6ede1df22bc20b09f20820020800a2e71227c66002c27c80000000009df06e0c800b09f0000000000226f15e728c20b09f20000000006bfe01dbe9400b09f200000000007dc703eece9002c27c86180186002fb0d44ae8924282c27c00000000002ab40f4e62002c27c800000000029ac0be9e4002c27c80000000002b340bfe68002c27c8208008200286d0feaf4002c27c00000000001d7c0a5fb6002c27c80000000001e6c0a5862002c27c800000000029ec0bd9b4002c27c800000000029600a5ebe002c27c03a83a84c03a83a84c02fffc08933af06938acaf8) (by decide +kernel)
private theorem c10_RelativeWidePack6815_P15 : WideCovered band 10616784 11274075 := wide_block_sound band profiles_RelativeWidePack6815_P15 10616784 11274075 (wideData 16 0x79784b1d000b09f20000000002a1a01be18c00b09f2000000000424805cb6b400b09f008200208006b82d3a8f23082c27c80000000006eb8070ab6002c27c80000000007e28168c7f002c27c8000000000da740b19f9082c27c0000000001ae384e7b000b09f2000000000060df21acb71002c27c82080082002e2bbd8d7fd420b09f200000000037af03bfef800b09f0082002080060bbd1fcca7082c27c80000000006b300ecabc002c27c80000000007f200a0fe0002c27c8000000000aca4224c400b09f00f40f41300f40f41300e1c702e6b7ee81a14ab0930) (by decide +kernel)
private theorem c11_RelativeWidePack6815_P15 : WideCovered band 11274076 12342174 := wide_block_sound band profiles_RelativeWidePack6815_P15 11274076 12342174 (wideData 16 0x123f04eadf800b09f0104004100524e6d072a688bf702c27c80000000003927907a7bcea00582f900000000003869b07974c6800582f882080082001ae0b04a31eae00582f9000000000019e8902c3de2600582f880000000001ba7b02fe08ac00582f900000000001aeed02c24b7400582f880000000001a77e01eb68e800582f902080082013cf92acdba00582f880000000013c600b28e000582f9030c00c30098349959709226c582f882080082001a66acfd768c20b09f200000000033d901970c000b09f20820020807edc47c68b420b09f00fa0fa1300fa0fa1300e3d70272a30f01c15cb3f68) (by decide +kernel)
private theorem c12_RelativeWidePack6815_P15 : WideCovered band 12342175 12999465 := wide_block_sound band profiles_RelativeWidePack6815_P15 12342175 12999465 (wideData 11 0x820020800ff93d0bef32845160be2000000000074c3812586ff40160be20820020801e1831335df8942160be2000000000721950e6ab2b10582f90410010400baa1a01da1ff1b83160be2000000000138d07da8b000b09f20820020800ecd469f48000b09f20000000000e8b059f7e800b09f00000000000ebe058eff800b09f20000000000f1a04ff0a800b09f21241241301241241300e6eb4261fe9981d97cfa86e) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7733176 7744340 12999465 c0_RelativeWidePack6815_P15 (wide_covered_join band 7744341 7797617 12999465 c1_RelativeWidePack6815_P15 (wide_covered_join band 7797618 7946534 12999465 c2_RelativeWidePack6815_P15 (wide_covered_join band 7946535 8110857 12999465 c3_RelativeWidePack6815_P15 (wide_covered_join band 8110858 8357342 12999465 c4_RelativeWidePack6815_P15 (wide_covered_join band 8357343 8685988 12999465 c5_RelativeWidePack6815_P15 (wide_covered_join band 8685989 9014634 12999465 c6_RelativeWidePack6815_P15 (wide_covered_join band 9014635 9343280 12999465 c7_RelativeWidePack6815_P15 (wide_covered_join band 9343281 9959491 12999465 c8_RelativeWidePack6815_P15 (wide_covered_join band 9959492 10616783 12999465 c9_RelativeWidePack6815_P15 (wide_covered_join band 10616784 11274075 12999465 c10_RelativeWidePack6815_P15 (wide_covered_join band 11274076 12342174 12999465 c11_RelativeWidePack6815_P15 c12_RelativeWidePack6815_P15))))))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 13)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 13≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤59)
    (hT0 : 3625≤T) (hT1 : T≤3649) (hnu : 7733176≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤40165473124689310 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R095
end MergedPart3
