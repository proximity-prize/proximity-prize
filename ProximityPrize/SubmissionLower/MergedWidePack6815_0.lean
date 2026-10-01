import ProximityPrize.SubmissionLower.RelativeWideBlocks6815
set_option Elab.async false
section MergedPart0
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R000
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨10,49,4336,4362,8672446898194066⟩
private def profiles_RelativeWidePack6815_P00 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨41268,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P00 : WideCovered band 6422469 9719978 := wide_block_sound band profiles_RelativeWidePack6815_P00 6422469 9719978 (wideData 16 0x131911c22004839f00000000007ca406f8ab004839f86180186003869070fe0d80120e7c000000000170072dee00282cf82080082002c01a288800a0b3e0000000004b8061de400282cf80000000015c01a28c000a0b3e0000000005ac0699f000282cf80000000017b01a7f9800a0b3e00000000063006af2800282cf80000000019e01afff000a0b3e1c70071c00a9e201aed2eb820a0b3e34d00d3400e46c00a0b3e1860061802a0067fe4088873e8b2c02cb001d019400609af903d83d83d83d83d83d86815fb6010a39e34) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P00 : WideCovered band 9719979 10643280 := wide_block_sound band profiles_RelativeWidePack6815_P00 9719979 10643280 (wideData 14 0x2080082001a2c1afd38004839f00000000002c6016aaf8004839f00000000002d2016a93e004839f00000000002c6c137c7a004839f00000000002e3413c920004839f02080082004130cb8004839f00000000002a64120aa4004839f00000000002be40ffe34004839f80000000002a740b78f6004839f0000000000393c0fdfe6004839f02080082001ca50edce6004839f00000000002a2c0aedf8004839f80000000002d3c0a5f64004839f03a03a03d83a03a03d82eb6e08ae2e6a112d69930) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6422469 9719978 10643280 c0_RelativeWidePack6815_P00 c1_RelativeWidePack6815_P00)
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 10)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 10≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤49)
    (hT0 : 4336≤T) (hT1 : T≤4362) (hnu : 6422469≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤8672446898194066 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R001
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨10,50,4257,4336,19532329570198181⟩
private def profiles_RelativeWidePack6815_P00 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨33072,8,10160⟩
  | 4 => ⟨41518,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P00 : WideCovered band 6553540 9456476 := wide_block_sound band profiles_RelativeWidePack6815_P00 6553540 9456476 (wideData 16 0x82002080073a0182ee800a196e0000000000a1f019eec000a196e0000000000a4c01a21e800a196e00000000007f8018698800a196e0000000000aad01a6ec800a196e0000000000aee01ab19000a196e0000000000aa9018eb8800a19700820020800b2a41ab9d800a196e00000000007981dcb8002865b80000000001f7c7fcf800a196e0000000000a49018bfc000a196e1c70071c01b7ce81a2964c820a196e0c30030c07a0074d2e082865b871c01c700fb1aaa20848aaf8d34034d00ac0d92a090a6bc83e03e03e03e03e03e16c15d2a010caae30) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P00 : WideCovered band 9456477 10357387 := wide_block_sound band profiles_RelativeWidePack6815_P00 9456477 10357387 (wideData 16 0x9aa4168f720048aaf800000000088241259740048aaf02080082002d2d0e082e0048aaf00000000006ef80beab20048aaf00000000008ba40ed8bc0048aaf00000000008eec0a6dec0048aaf0000000000baa40778240048aaf00000000012cfc0e9c340048aaf0000000001d92c0b18c0122abe0000000000aba6416aeb10048aaf082002080038a2941d209f20048aaf000000000029b806bfb0002865b80000000002afc06ef6e002865b800000000029a4067f72002865b80000000002ca8070e2c002865b83883883e03883883e07abba06cfceea2128e6ee6) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P00 : WideCovered band 10357388 10824525 := wide_block_sound band profiles_RelativeWidePack6815_P00 10357388 10824525 (wideData 7 0x2080082006b381b4ce20048aaf000000000089bc171da80048aaf00000000008bf4170bec0048aaf000000000099b8178f740048aaf02080082001f24171ce40048aaf00000000006ffc125d6a0048aaf03b03b03e03b03b03e0a9b6b099a78fa213f27cf2) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6553540 9456476 10824525 c0_RelativeWidePack6815_P00 (wide_covered_join band 9456477 10357387 10824525 c1_RelativeWidePack6815_P00 c2_RelativeWidePack6815_P00))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 10)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 10≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤50)
    (hT0 : 4257≤T) (hT1 : T≤4336) (hnu : 6553540≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤19532329570198181 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R001

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R002
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨10,51,4181,4310,11453932412571267⟩
private def profiles_RelativeWidePack6815_P00 : ℕ → Profile
  | 0 => ⟨16536,4,5080⟩
  | 1 => ⟨41768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P00 : WideCovered band 6684611 9351576 := wide_block_sound band profiles_RelativeWidePack6815_P00 6684611 9351576 (wideData 16 0xf1e0196e8800a1f7e0000000000ed9018329000a1f7e000000000122801a61e800a1f7e0000000000fb80187ff000a1f7e000000000123f018b7e800a1f7e082002080169841ab9d000a1f7e0000000000bed1abb200287df80000000003c64061f2c00287df80000000003aa06bff800a1f7e0000000000f1a1b97600287df80000000004a7c06497a00287df800000000049a0730a000a1f7e000000000165c019e0b800a1f7e082002080236c5ece800287df8924024900ac7bd05e3e83408287e803903903e83903903e82b2007caa6010efbe2c) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P00 : WideCovered band 9351577 10060517 := wide_block_sound band profiles_RelativeWidePack6815_P00 9351577 10060517 (wideData 16 0x33ed0283ae00123efc0000000003fdc01c2e900123efe000000000571c148660048fbf0000000001dcb01289a50048fbf06180186001921074a3be00123efc000000000134c01de1d800a1f7e0820020800e0b41a3be800a1f7e0000000000e7901968b000a1f7e0000000000f7f01b35d800a1f7e0000000000eea019a1a800a1f7e0000000000ff801b60d000a1f7e0000000000fab01a30c000a1f7e0000000000fec01a229800a1f7e0820020800e6d41c688000a1f7e0000000000bff1fcf400287e803803803e83803803e8bdef906ab3b76091f3adee) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P00 : WideCovered band 10060518 11005770 := wide_block_sound band profiles_RelativeWidePack6815_P00 10060518 11005770 (wideData 14 0x108641bdc300048fbf00000000010b601bcef00048fbf0000000001186c1beaee0048fbf02080082003a24164a6c0048fbf0000000000dc3816be360048fbf0000000000e8ec16bbba0048fbf0000000000f82816cee80048fbf02080082002a3816dd240048fbf80000000009eec0e1ab00048fbf0000000000cbac0fe8660048fbf0000000000dd700fccf20048fbf0000000000fd280fcb6c0048fbf000000000119740bece00048fbf03b03b03e83b03b03e8ec2ff08bb0dac093aa5aa6) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6684611 9351576 11005770 c0_RelativeWidePack6815_P00 (wide_covered_join band 9351577 10060517 11005770 c1_RelativeWidePack6815_P00 c2_RelativeWidePack6815_P00))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 10)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 10≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤51)
    (hT0 : 4181≤T) (hT1 : T≤4310) (hnu : 6684611≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤11453932412571267 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R002

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R003
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨10,52,4107,4284,11559364790206579⟩
private def profiles_RelativeWidePack6815_P00 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨33072,8,10160⟩
  | 4 => ⟨41768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P00 : WideCovered band 6815682 9069651 := wide_block_sound band profiles_RelativeWidePack6815_P00 6815682 9069651 (wideData 16 0x4eb06fbc800a2dae00000000016f91fe3a0028b6c000000000068680628380028b6b800000000069b477de000a2dae0000000001bce1ef620028b6b80000000008f250609680028b6b82080082014d17f700028b6b80000000004ef457ce800a2dae00000000016ab15fe80028b6b80000000006cec7e0f800a2dae1c7005140376e6c17193de820a2dae0c30051400a6c01cee8020a2dae0c30030c0063a19de008496cf00000000011c0cef0088ab9e175c05d7008a1b00186b9e20fc0fc0fc0fc0fc0fc068a1583c00f8b6aa6) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P00 : WideCovered band 9069652 9616068 := wide_block_sound band profiles_RelativeWidePack6815_P00 9069652 9616068 (wideData 16 0x1398019b7c000a2dae00000000013ed019e4c800a2db00000000001658019f69800a2dae0000000001a1e01c2ee000a2dae000000000176f01a738800a2dae0000000000e5b41ab7c000a2dae0820020800aca01874b800a2dae00000000012fd0183db800a2dae000000000136a018688000a2dae00000000013df01875c800a2dae000000000178901a3ab800a2dae000000000177c0193fa000a2dae0000000001a190192da000a2dae082002080228941937e800a2dae000000000129c1bbe20028b6b82f82f83f02f82f83f0f9b6d05fad8bc211af4ef4) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P00 : WideCovered band 9616069 10572297 := wide_block_sound band profiles_RelativeWidePack6815_P00 9616069 10572297 (wideData 16 0x13cf0132c3400496cf02080082003abc17dd3400496cf0000000000f8ec0ea83200496cf0000000001097c0e3daa00496cf00000000013fa80f68e400496cf00000000016cf80ead7800496cf0000000001ac380aebba00496cf80000000010f2c07cdbe00496cf02080082013ea90b6d2c00496cf00000000016c743b0840125b3c0c30000002e78363f7cb500496cf08200186009becfc2866db200496cf00000000006af807792a0028b6b80000000005fe40709b00028b6b820800820048a506bde00028b6b83883883f03883883f1183ce06c65e3e212b608b6) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P00 : WideCovered band 10572298 11187015 := wide_block_sound band profiles_RelativeWidePack6815_P00 10572298 11187015 (wideData 9 0x19d64221c2600496cf0000000001a92c1fff7600496cf02080082009ea41b8d6200496cf00000000017d281e9c3800496cf00000000015b341a68fe00496cf00000000016a241a5db000496cf02080082007c681b1a7e00496cf00000000011cb013782e00496cf03b83b83f03b83b83f188a2d09aae9ae214a6eb6e) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6815682 9069651 11187015 c0_RelativeWidePack6815_P00 (wide_covered_join band 9069652 9616068 11187015 c1_RelativeWidePack6815_P00 (wide_covered_join band 9616069 10572297 11187015 c2_RelativeWidePack6815_P00 c3_RelativeWidePack6815_P00)))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 10)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 10≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤52)
    (hT0 : 4107≤T) (hT1 : T≤4284) (hnu : 6815682≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤11559364790206579 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R003

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R004
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨10,53,4036,4257,11933826726466278⟩
private def profiles_RelativeWidePack6815_P00 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨42018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P00 : WideCovered band 6946753 8950248 := wide_block_sound band profiles_RelativeWidePack6815_P00 6946753 8950248 (wideData 16 0x89ac728d000a3bbe000000000226b12eaa0028eef8000000000abb076fa000a3bbe0000000001a5b5efb80028eef82080082008cf57208000a3bbe0000000001e2f14a7c0028eef80000000007f7c5249800a3bbe000000000261913fb40028eef8000000000ac244f9c800a3bbe000000000327f10db20028eef8000000000eabc1fdf800a3bbe1450030c03edee816babad820a3bbe082002080124902b29f82126f7c0c30051405b8336f0222def86590196401606c043bdf20f80f80fe0f80f80fe076b14df400faeeea2) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P00 : WideCovered band 8950249 9502937 := wide_block_sound band profiles_RelativeWidePack6815_P00 8950249 9502937 (wideData 16 0x1b4d0193fd800a3bbe0000000001e7e019fd9800a3bbe0000000001f7901a60c000a3bbe00000000022bf41aabd800a3bbe082002080176e1feec0028eef80000000005ffc0609ba0028eef80000000006ab4060d7a0028eef80000000006df0061a6e0028eef80000000006af4671c800a3bbe0000000001f99018b2e800a3be0000000000230d018f9f800a3bbe08200208036be41964d800a3bbe00000000017bd1aca40028eef80000000006a3c6ba8000a3bbe0000000001b991b9620028eef82f82f83f82f82f83f92965e05de4ca819192cb6e) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P00 : WideCovered band 9502938 10262883 := wide_block_sound band profiles_RelativeWidePack6815_P00 9502938 10262883 (wideData 16 0x628f02c3fb00126f7c000000000760901ff9e00126f7c0000000000618a44a0940126f7c000000000079f344e8cc0126f7c0000000000f2aec160c790049bdf08200208003ae0841ee5c7e0049bdf00000000006970068f320028eef800000000069b0067e600028eef80000000006f3406cd7c0028eef8000000000797006dba80028eef80000000007c2006eb2e0028eef8000000000383006fc740028eef82080082001eed06986c0028eef8000000000683c065c760028eef80000000006a3006682a0028eef83883883f83883883f94b6cc069fdc621929a3f30) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P00 : WideCovered band 10262884 11368260 := wide_block_sound band profiles_RelativeWidePack6815_P00 10262884 11368260 (wideData 16 0x62d60231bf20049bdf02080082014ff826193c0049bdf0000000001fbac1fa82c0049bdf0000000001ff641f7ee00049bdf0000000001eb241e0b320049bdf0208008200bc3c1b6f380049bdf0000000001a93c1a0cfa0049bdf0000000001b87417fcf80049bdf0000000001cbfc1a0c780049bdf0000000000deac13987e0049bdf0208008200bcf8135e6c0049bdf00000000017d3012ea200049bdf00000000019de412d9f20049bdf00000000018b740bfa620049bdf0000000000c96c12a9e20049bdf03b83b83f83b83b83f9ada8d08c2faf6193db3d24) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6946753 8950248 11368260 c0_RelativeWidePack6815_P00 (wide_covered_join band 8950249 9502937 11368260 c1_RelativeWidePack6815_P00 (wide_covered_join band 9502938 10262883 11368260 c2_RelativeWidePack6815_P00 c3_RelativeWidePack6815_P00)))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 10)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 10≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤53)
    (hT0 : 4036≤T) (hT1 : T≤4257) (hnu : 6946753≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤11933826726466278 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R004

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R005
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨10,54,3968,4230,12128527754247205⟩
private def profiles_RelativeWidePack6815_P00 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨2984,24,635⟩
  | 4 => ⟨42268,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P00 : WideCovered band 7077824 8824574 := wide_block_sound band profiles_RelativeWidePack6815_P00 7077824 8824574 (wideData 16 0x109f06f3c800a49ee0000000001af80ec66002927b8000000000eae57758000a49ee08200208026f95bab0002927b8000000000ad7017b9000a49ee0000000003a1c0ef64002927b80000000010bb41e3e800a49ee000000000539c02a38002927b8000000001ce641a3e800a49ee000000000066e785e69400a49ee00000000007ffe447ed400a49ee1040041000a6c6bb4fd6e9a3082927b871c01c7002d259bc53faedd020a49ee0000000000e9901caac020a49ee0820020800adf01977f82230f780bc0bc1200bc0bc1200a5a14ba000fd27aa0) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P00 : WideCovered band 8824575 9383535 := wide_block_sound band profiles_RelativeWidePack6815_P00 8824575 9383535 (wideData 16 0x79e0068f74002927b8208008200ba21060cf6002927c00000000007a707bfc000a49ee0000000001b9f17eaa002927b800000000089fc7f4c800a49ee00000000023cf0182de000a49ee000000000234918a62002927b8000000000ad740628a4002927b80000000005c20063cf6002927b8000000000a9f16aa8000a49ee0820020800a4b1c970002927b80000000008b3863ac800a49ee00000000022ca11de4002927b8000000000ab6467d9000a49ee0000000002b390feee002927b82f82f84802f82f84814a7a905c62c32210f37dea) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P00 : WideCovered band 9383536 9942495 := wide_block_sound band profiles_RelativeWidePack6815_P00 9383536 9942495 (wideData 16 0x8b7406bbf2002927b80000000009ebc074cea002927b82080082005e79071e2a002927b80000000006eb0063ab0002927b80000000007fac06ad6c002927b80000000008a2006ba76002927b80000000007d3c064a6c002927b8000000000982c06ce7e002927b80000000008ebc068c26002927b80000000003d7506c8e6002927b82080082002ee4066bee002927b80000000006d38771a800a49ee0000000001fcb019639800a49ee00000000022ab0197aa800a49ee0000000001fad1ebfc002927b8388388480388388481793ef05ff39f0211fbbbac) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P00 : WideCovered band 9942496 10990545 := wide_block_sound band profiles_RelativeWidePack6815_P00 9942496 10990545 (wideData 16 0x19da01a8df6004a2ef0208008200d9b013eef8004a2ef00000000001835f05e3f900128bbc0000000007a1d04ce2e00128bbc000000000060e30130f3e004a2ef0208008200592912ccac004a2ef0000000001d964126e34004a2ef0000000001ba780bae74004a2ef0000000001fafc0af8a0004a2ef000000000019b1801f79f80128bbc00000000007cbf00ec9e2004a2ef00000000002bff910b00128bbc00000000017ec6412bc39004a2ef08200208006dfd841df9c62004a2ef000000000088ec06cc38002927b8398398480398398481aa3db06d24a2621383f96c) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P00 : WideCovered band 10990546 11549505 := wide_block_sound band profiles_RelativeWidePack6815_P00 10990546 11549505 (wideData 8 0x208008201fef02add32004a2ef00000000001a29c08bb8a00128bbc000000000068a60229868004a2ef00000000001b7fe09bf3800128bbc08200208052e908834880128bbc000000000060ce01acce8004a2ef000000000018fba06fb5800128bbc0f20f21200f20f2120067a25a09f648682158e2afe) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7077824 8824574 11549505 c0_RelativeWidePack6815_P00 (wide_covered_join band 8824575 9383535 11549505 c1_RelativeWidePack6815_P00 (wide_covered_join band 9383536 9942495 11549505 c2_RelativeWidePack6815_P00 (wide_covered_join band 9942496 10990545 11549505 c3_RelativeWidePack6815_P00 c4_RelativeWidePack6815_P00))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 10)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 10≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤54)
    (hT0 : 3968≤T) (hT1 : T≤4230) (hnu : 7077824≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤12128527754247205 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R005
end MergedPart0
section MergedPart1
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R006
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨10,55,3901,4203,12617051697948470⟩
private def profiles_RelativeWidePack6815_P01 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨2984,24,635⟩
  | 3 => ⟨42518,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P01 : WideCovered band 7208895 8551320 := wide_block_sound band profiles_RelativeWidePack6815_P01 7208895 8551320 (wideData 16 0x16cd0ba760018aff800000000059a81f0f00062c200000000001a4a0bce80018aff80000000006ce82fbe00062c200000000001b0d07cfa0018aff80000000007df032ba80062c200000000000bc84cdea0018aff82080082002c2daad43597e842062c2000000000057c8b812f9fbb800a4ffe0000000004a1d200f9b7dc800a4ffe0000000002348a8078dfaa000a4ffe000000000065c3d848da3a3b00293ff851400c3002ea6de4526b74d82129ffc0820020800bad0196b882233ff84d30155401344c0467ff00ec0ec1220ec0ec1220aa81497e00eeafebc) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P01 : WideCovered band 8551321 9116552 := wide_block_sound band profiles_RelativeWidePack6815_P01 8551321 9116552 (wideData 16 0x2fbe169f400293ff8000000000efac060ffa00293ff8000000000acac5e0a800a4ffe0000000001b595793e00293ff8208008200d8e106397400293ff8000000000aaec3a68800a4ffe00000000033ed15e6200293ff8000000000df28372f000a4ffe000000000427c0a9f000293ff80000000015d68577b800a4ffe00000000066cc05e2400293ff8000000000187af10d800a4ffe000000000772b0fbe600293ff80000000001c3db11da500293ff80000082001ba1c05c6f00293ff82f82f84882f02f0489082f805b3287c190b22e6e) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P01 : WideCovered band 9116553 9681784 := wide_block_sound band profiles_RelativeWidePack6815_P01 9116553 9681784 (wideData 16 0x9bac063aac00293ff8000000000af6406a8f000293ff8000000000b8a00679a000293ff8000000000ba21065f2400293ff82080082006d7c064ba800293ff80000000008a3472ff000a4ffe000000000237f1cc3c00293ff8000000000ac3006582e00293ff8000000000a8e876d8800a4ffe000000000329c019e48800a4ffe0000000000fd81f87a00293ff8000000000ba717fea000a4ffe0820020801e4f1efb400293ff80000000008eb05aab800a4ffe00000000027b817ea200293ff83803804883803804899832b05d28860191bb2e2e) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P01 : WideCovered band 9681785 10388324 := wide_block_sound band profiles_RelativeWidePack6815_P01 9681785 10388324 (wideData 16 0x1a23e01cf2c00129ffc000000000074ca84edc80129ffc0c30030c04a5b3032dba1004a7ff0820020800f93bf4286aa32004a7ff000000000038ed07baae00293ff82080082007ca4068f3000293ff80000000008ea0068c2e00293ff8000000000a9a0070a2600293ff80000000009b74069aa200293ff80000000009f3c06ab3200293ff8000000000bb2007293e00293ff80000000003db006bc2600293ff82080082002a6106ebbc00293ff800000000089f40629fc00293ff80000000008ca0062b2e00293ff8390390488390390489ca7bf069608a2192c62dee) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P01 : WideCovered band 10388325 11518788 := wide_block_sound band profiles_RelativeWidePack6815_P01 10388325 11518788 (wideData 16 0x79cb82a48ec004a7ff02080082013c201e8cfc004a7ff00000000001ba0a07f6c800129ffc00000000006efac1fbb22004a7ff00000000001c35b07efec80129ffc0820020802b2d06870a80129ffc000000000063fe016fa6c004a7ff00000000001a28905ff3800129ffc00000000006b86c1a0e3e004a7ff02080082003a68172966004a7ff0000000001c9b40e8e3a004a7ff000000000018fce04a2bb00129ffc0000000000688e8125d28004a7ff00000000001be29048fe800129ffc0000000002b7a028e5900129ffc0f00f01220f00f0122064a68b08b7ff68193fabda4) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P01 : WideCovered band 11518789 11730750 := wide_block_sound band profiles_RelativeWidePack6815_P01 11518789 11730750 (wideData 3 0x82002080062c742a0b26004a7ff00000000001e3dd0ab2fd00129ffc0f60f61220f60f612207692190bc29b661968ebd24) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7208895 8551320 11730750 c0_RelativeWidePack6815_P01 (wide_covered_join band 8551321 9116552 11730750 c1_RelativeWidePack6815_P01 (wide_covered_join band 9116553 9681784 11730750 c2_RelativeWidePack6815_P01 (wide_covered_join band 9681785 10388324 11730750 c3_RelativeWidePack6815_P01 (wide_covered_join band 10388325 11518788 11730750 c4_RelativeWidePack6815_P01 c5_RelativeWidePack6815_P01)))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 10)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 10≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤55)
    (hT0 : 3901≤T) (hT1 : T≤4203) (hnu : 7208895≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤12617051697948470 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R006

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R007
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨10,56,3837,4175,13324851088604044⟩
private def profiles_RelativeWidePack6815_P01 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨2984,24,635⟩
  | 3 => ⟨42518,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P01 : WideCovered band 7339966 8518692 := wide_block_sound band profiles_RelativeWidePack6815_P01 7339966 8518692 (wideData 16 0x1b4a09bbc0018bc980000000007928271a00062f280000000001f6f09d260018bc980000000008b38278a80062f2800000000016190dbbc0018bc982080082002efcb65436b6ce42062f280000000006b7e2413ab7ca000a5e2e0000000004f9aa40f4ffbb800a5e2e00000000026ed24076cb2c000a5e2e00000000006ea6bd49b6ebfb002978b8000000001096b902b3c8b0004af0f00000000001fa1ea4332c3988012bc3c0820020806f5e4bd7ff800a5e2e1450030c06fdba016da27e020a5e2e0820020800e5d0193ee022378780b80b81240b60b61240b6f13f6600f8bc8ba) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P01 : WideCovered band 8518693 9018758 := wide_block_sound band profiles_RelativeWidePack6815_P01 8518693 9018758 (wideData 16 0x135a0182cf800a5e2e00000000026ec5ce68002978b820800820088f1669a800a5e2e00000000036a80e9fe002978b8000000000fafc33a8000a5e2e0000000004a5d0aff6002978b8000000001692822e9000a5e2e0000000006ffe04ea2002978b800000000019f5b129ae002978b80000000001d3e905df7002978b80000000002964d14bad002978b84100104006baea4bf39e000a5e2e000000000165e09a3c0018bc980000000005be826a980062f28000000000179f09aec0018bc982e82e84902e82e84918c7ba04fa5d72190a60fb0) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P01 : WideCovered band 9018759 9590262 := wide_block_sound band profiles_RelativeWidePack6815_P01 9018759 9590262 (wideData 16 0x1e9c019ac9800a5e2e08200208027ea41ba7c800a5e2e00000000026eb1dc30002978b80000000009fec775b000a5e2e0000000002b491df6a002978b8000000000bb6c7a7d000a5e2e00000000032cc1edf8002978b8000000000dcf07ecb800a5e2e000000000071d418e9b800a5e2e082002080274f419b4d000a5e2e0000000002a1f17b34002978b8000000000af685e8e800a5e2e0000000002ffb1793a002978b8000000000dae05e2b000a5e2e0000000003e3917874002978b8380380490380380491aee4b05bf7a3e191a34c3a) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P01 : WideCovered band 9590263 10161765 := wide_block_sound band profiles_RelativeWidePack6815_P01 9590263 10161765 (wideData 16 0xca74072c2e002978b8000000000de2c079aaa002978b82080082006a31075d7c002978b8000000000a8f4069cf2002978b8000000000ab60069ef6002978b8000000000ae2806a9f0002978b8000000000b96806ada2002978b8000000000bd6406bab2002978b8000000000c9f406c8fa002978b80000000004b710768a6002978b82080082005ce40659b2002978b80000000009e74063be0002978b8000000000a9e8063e66002978b8000000000adf00649a2002978b8000000000bae8064e22002978b8390390490390390491eea8805fe4de2192af0df8) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P01 : WideCovered band 10161766 11269054 := wide_block_sound band profiles_RelativeWidePack6815_P01 10161766 11269054 (wideData 16 0x76f281fdaf6004af0f0000000001baf01efea2004af0f020800820018a6805bbdb0012bc3c000000000068ff8167a6e004af0f00000000001ca1d06ba4a0012bc3c00000000006f960164e22004af0f02080082005c79131c6a004af0f000000000018f0e03be3b8012bc3c00000000006dff81338f0004af0f00000000001b62803820f0012bc3c000000000076fa80b1bbc004af0f00000000001fe3a01e7bf8012bc3c000000000072c790f4d7e004af0f00000000003d33f01db5a4012bc3c208008200060b78074ea4b0012bc3c0e80e81240e80e81240639f2b06d63ba6193bacfb8) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P01 : WideCovered band 11269055 11911995 := wide_block_sound band profiles_RelativeWidePack6815_P01 11269055 11911995 (wideData 9 0xae87c33b92e004af0e80000000002b3790cbb5e8012bc3c0000000000a5f34379e2c004af0f02080082001d33909f2a80012bc3c00000000007cc2826fef8004af0f00000000001fb2a09d6ca8012bc3c082002080067a682a7bae004af0f00000000001c2ea07a37f8012bc3c0f40f41240f40f4124077a35d0ab34da8195d25b38) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7339966 8518692 11911995 c0_RelativeWidePack6815_P01 (wide_covered_join band 8518693 9018758 11911995 c1_RelativeWidePack6815_P01 (wide_covered_join band 9018759 9590262 11911995 c2_RelativeWidePack6815_P01 (wide_covered_join band 9590263 10161765 11911995 c3_RelativeWidePack6815_P01 (wide_covered_join band 10161766 11269054 11911995 c4_RelativeWidePack6815_P01 c5_RelativeWidePack6815_P01)))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 10)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 10≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤56)
    (hT0 : 3837≤T) (hT1 : T≤4175) (hnu : 7339966≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤13324851088604044 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R007

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R008
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨10,57,3775,4147,25491065119051915⟩
private def profiles_RelativeWidePack6815_P01 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨2984,24,635⟩
  | 3 => ⟨42768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P01 : WideCovered band 7471037 8464089 := wide_block_sound band profiles_RelativeWidePack6815_P01 7471037 8464089 (wideData 16 0x1bf9ad8419b4ca1c42063a300820020800fcaad916c639220029b0f80000000019af4e0487ddfc0029b0f80000000016ab0f03da1fea0029b0f8000000000ee27f02b72bf20029b0f830c00c3004dbfb3d067da1cf10029b0f82080082003e25f3c061968d64004b61f00000000002820a702f4de0b8012d87c082002080070afd263b300029b0f800000000029edc0a8f6a000a6c3e0000000000a0d3c22ff220029b0f80000000016cf463d0029b0f80000000001ee2c05874a000a6c3e0c30000005f4f28131efdf820a6c3e0000030c00efb01932f0223a8f80b80b81260b80b81260beb13d6800ee748e8) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P01 : WideCovered band 8464090 8807142 := wide_block_sound band profiles_RelativeWidePack6815_P01 8464090 8807142 (wideData 16 0x1bf9e08d670029b0f80000082006faea03c67cc00a6c3e1040020802bad3d3e8dba0029b0f80000000008b2c36bc80063a2e000000000228909a7c0018e8c00000000014e4e82a0018e8b800000000018ed274a00063a30000000000133d4ee6e0018e8b800000000028b52a8900063a2e0000000000adc4aaac0018e8b8208008200da4d9e20018e8c0000000000686c1a6f80063a2e0000000001e4909f700018e8c00000000006fa017ef80063a2e000000000226d0a8260018e8c02e82e84982e82e8499a9a1f04eb3870190976da0) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P01 : WideCovered band 8807143 9384918 := wide_block_sound band profiles_RelativeWidePack6815_P01 8807143 9384918 (wideData 16 0x36bb1ccac0029b0f8000000000cff44f3c800a6c3e000000000426b1cf7e0029b0f80000000012a7c775d800a6c3e000000000132f5ede60029b0f8000000000a9a90609e80029b0f82080082005c3c633d800a6c3e0000000003ad914c720029b0f80000000010a70524c800a6c3e00000000043bf08a3a0029b0f8000000001687c47dc000a6c3e0000000006bae10f6e0029b0f8000000000182480fc700029b0f80000000009fa43718000a6c3e0000000003ba90aa3a0029b0f83803804983803804999cfeb05aa59a6190ef7fea) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P01 : WideCovered band 9384919 9962693 := wide_block_sound band profiles_RelativeWidePack6815_P01 9384919 9962693 (wideData 16 0x2fff01a32e000a6c3e0000000002e4801873b000a6c3e000000000363c01a759800a6c3e00000000037af01ab0a800a6c3e0000000002b0e01af38800a6c3e0820020802bcf41b31c000a6c3c0000000002e18018a19000a6c3e0000000002f2b018abb800a6c3e000000000327a018b9d000a6c3e0000000002efe1b83a0029b0f8000000000df34063de40029b0f8000000000f8a4064d3a0029b0f80000000003869065f2c0029b0f820800820069b1064b7e0029b0f8000000000bbe07228800a6c3e0e20e21260e20e2126060b66e05d3eff4191fe0baa) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P01 : WideCovered band 9962694 10793246 := wide_block_sound band profiles_RelativeWidePack6815_P01 9962694 10793246 (wideData 16 0x1ef3803f25a8012d87c08200208072cf449e6a0012d87c00000000006eae80b4dac004b61f00000000001cf1d01af988012d87c0000000000a0cbc362f4012d87c0000000000eae2406eca5004b61f06180186014d3007ab7ae0012d87c0820020800fe901ce3b800a6c3e000000000325801b78c000a6c3e0000000002f5a01a738800a6c3e000000000365e01c20b000a6c3e000000000375b01c368000a6c3e0000000003a8901c71a800a6c3e000000000168a01cb3e800a6c3e08200208006cd41baba800a6c3e0e60e61260e60e6126064e208069eeea21938a8f68) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P01 : WideCovered band 10793247 11948797 := wide_block_sound band profiles_RelativeWidePack6815_P01 10793247 11948797 (wideData 16 0x20800820028e4a0def2d8012d87c0000000000b2d28320c60004b61f00000000002c7db0bdebd8012d87c0000000000a8e3427f9f8004b61f02080082001a6cc0a83db0012d87c0000000000a1b6c26092a004b61f000000000028a8808f2ce0012d87c00000000007c9b41f0c6c004b61f020800820169a01eff7e004b61f00000000001d7fb06e68d0012d87c00000000007887c1b7ca8004b61f00000000001d6ba05dab98012d87c082002080175905e78f0012d87c00000000006ea2413e870004b61f00000000001c74d04eb5f8012d87a0f20f21260f20f2126072cfdf08efecea194de5cf8) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P01 : WideCovered band 11948798 12093240 := wide_block_sound band profiles_RelativeWidePack6815_P01 11948798 12093240 (wideData 2 0x3ab0f0ff3b98012d87a0fa0fa1260fa0fa1260afaacc0d9bccb0196f76c76) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7471037 8464089 12093240 c0_RelativeWidePack6815_P01 (wide_covered_join band 8464090 8807142 12093240 c1_RelativeWidePack6815_P01 (wide_covered_join band 8807143 9384918 12093240 c2_RelativeWidePack6815_P01 (wide_covered_join band 9384919 9962693 12093240 c3_RelativeWidePack6815_P01 (wide_covered_join band 9962694 10793246 12093240 c4_RelativeWidePack6815_P01 (wide_covered_join band 10793247 11948797 12093240 c5_RelativeWidePack6815_P01 c6_RelativeWidePack6815_P01))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 10)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 10≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤57)
    (hT0 : 3775≤T) (hT1 : T≤4147) (hnu : 7471037≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤25491065119051915 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R008

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R009
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨10,58,3714,4118,26809193959670747⟩
private def profiles_RelativeWidePack6815_P01 : ℕ → Profile
  | 0 => ⟨16536,4,5080⟩
  | 1 => ⟨33072,8,10160⟩
  | 2 => ⟨2984,24,635⟩
  | 3 => ⟨43018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P01 : WideCovered band 7602108 8259161 := wide_block_sound band profiles_RelativeWidePack6815_P01 7602108 8259161 (wideData 16 0x9b6a901af98f40029e9b800000000029e6f61330a7e9c00a7a6e0000000000b99bd80ef2b960004bb2f02080082014afd421c380029e9b80000000002a37f098b09000a7a6e0000000006b8801829e800a7a6e00000000007efa417bd740029e9b80000000001f72d03e219800a7a6e00000000070cc2d9c00a7a6e0000000001b3c7c060c78c800a7a6e00000000006dfe8124d6f0018f4d80000000003b73c018beb00063d380000000001649b042d9a10018f4d80000000008aafd04b388600818f4e030c00c3005870070a720829e9b82e02e04a02e02e04a06f6c077d3600ee3d86e) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P01 : WideCovered band 8259162 8642443 := wide_block_sound band profiles_RelativeWidePack6815_P01 8259162 8642443 (wideData 16 0xa9b813bd80063d38000000000325e09cba0018f4d80000000003c2c276d80063d380000000003b427b800063d360000000001e02a1900063d38000000000164d03ce20018f4d80000000005d0a8b00018f4e00000000007b4ab200018f4d8000000001ad4ae760018f4e00000000001d692ebb80063d360820020801abd2dc5ff6be6f0818f4e02080082003969c2043ccecb000a7a6e0000000006798b80f7af1e000a7a6e0000000005b4ae00ecaebf000a7a6e0000000003e683c0a89e5c000a7a6e0b80b81280b80b81280a2aea80ab3ebbe10feaabe0) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P01 : WideCovered band 8642444 9025723 := wide_block_sound band profiles_RelativeWidePack6815_P01 8642444 9025723 (wideData 16 0x887c37bf000a7a6e082002080722f0ad2e0029e9b80000000001877c09ae70029e9b830000c3001e32a059f30029e9b84080104003ab2d4baa6d800a7a6e000000000471264980063d360000000000f7f4e9ea0018f4e00000000004c653b8c00063d3608200208016ed09fa80018f4e00000000006e2826fd80063d360000000001b8b07bea0018f4d80000000007a301f7a00063d36000000000223d09bb60018f4e00000000008dac26ff80063d3600000000026cb09ca00018f4e02f02f04a02f02f04a1cee6c04ee8862190c33b6c) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P01 : WideCovered band 9025724 9609770 := wide_block_sound band profiles_RelativeWidePack6815_P01 9025724 9609770 (wideData 16 0xdda86fbd000a7a6e00000000042090187de000a7a6e0000000003f4f199be0029e9b80000000010ea4063be00029e9b800000000099650658300029e9b80000000005d316bef000a7a6e082002080322f1b8b60029e9b8000000000eef45aba000a7a6c000000000426c14b2a0029e9b80000000013c2867ff800a7a6e000000000529a0edee0029e9b8000000001aab467cd800a7a6e000000000074f1acb20029e9b80000000008e3c2e3c800a7a6e0000000000ecd5aeae0029e9b83883884a03883884a1efab805ab39e8191a63d64) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P01 : WideCovered band 9609771 10193817 := wide_block_sound band profiles_RelativeWidePack6815_P01 9609771 10193817 (wideData 16 0x339b019fd8000a7a6e0000000003b0901ba9a800a7a6e00000000036ed019bd9000a7a6e0000000003f8f01bf59800a7a6e000000000434a01c39a800a7a6e0000000001edc41a60e000a7a6e08200208017fb01aa3c000a7a6e00000000033cc0193fe000a7a6c00000000033aa0187fd800a7a6e0000000003b6801a238800a7a6e00000000037ce0182c8000a7a6e000000000435b01a77a000a7a6e000000000072941ae3f000a7a6e082002080169a4186d9000a7a6e000000000360801834e000a7a6e0e40e41280e40e4128064beaa05df5820192b38b22) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P01 : WideCovered band 10193818 11179397 := wide_block_sound band profiles_RelativeWidePack6815_P01 10193818 11179397 (wideData 16 0x75f6816383a004bb2f00000000001e7eb04f7bf8012ecba000000000072fe8139c32004bb2f02080082008c05b2ca8012ecbc0000000000709bc0e083e004bb2f00000000001db9f02bf798012ecbc0000000000a2cbc077b22004bb2f00000000003a22a02ffd98012ecbc000000000132d2406bb77004bb2f00000000009fb6808af884012ecbc2080082002ba9f10a4c6ef0012ecbc0000000003fde01dacf000a7a6e000000000430a01de7e800a7a6e0000000003ed801bf2c000a7a6e082002080227c41e3a9800a7a6e0e80e81280e80e8128069c6df06af886c193c2d8e0) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P01 : WideCovered band 11179398 12274485 := wide_block_sound band profiles_RelativeWidePack6815_P01 11179398 12274485 (wideData 15 0x48a7b11d3ee0012ecba0000000000e7c6c43fcaa004bb2f02080082003a7bb0faf5d8012ecbc0000000000e3a34363862004bb2f0000000000387db0cdb6a0012ecbc08200208007bca82fcc22004bb2f00000000002dbdd0ba64c8012ecbc0000000000adaa8274836004bb2f00000000002ba0d09baac0012ecba082002080062c3c2358f4004bb2f000000000029a9d08c78b0012ecbc00000000007f9281e4aea004bb2f0000000000286f907867d8012ecbc0820020803f3806d3bc8012ecbc0f40f41280f40f412807e826c09ca582c195bb9ae6) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7602108 8259161 12274485 c0_RelativeWidePack6815_P01 (wide_covered_join band 8259162 8642443 12274485 c1_RelativeWidePack6815_P01 (wide_covered_join band 8642444 9025723 12274485 c2_RelativeWidePack6815_P01 (wide_covered_join band 9025724 9609770 12274485 c3_RelativeWidePack6815_P01 (wide_covered_join band 9609771 10193817 12274485 c4_RelativeWidePack6815_P01 (wide_covered_join band 10193818 11179397 12274485 c5_RelativeWidePack6815_P01 c6_RelativeWidePack6815_P01))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 10)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 10≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤58)
    (hT0 : 3714≤T) (hT1 : T≤4118) (hnu : 7602108≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤26809193959670747 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R009

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R010
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨10,59,3656,4088,22659965433996529⟩
private def profiles_RelativeWidePack6815_P01 : ℕ → Profile
  | 0 => ⟨9131,74,2353⟩
  | 1 => ⟨2984,24,635⟩
  | 2 => ⟨43018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P01 : WideCovered band 7733179 8766237 := wide_block_sound band profiles_RelativeWidePack6815_P01 7733179 8766237 (wideData 16 0x2a68a806acee9001308fc0000000002af8b006be7de001308fc0820020801a6a3c7b397e004c23f0000000000493cd10bb38801308fc00000000013dcbc4f1f34004c23f00000000004ca8a11babd001308fc0000000000e2a2826ee74004c23e8208008200196aa0b8e9a001308fc0000000000a7e641b7ca2004c23f000000000179e40abb61004c23f00000000001d33e03ce6ec01308fc0004c001332df30066b23c831308fc104484112074cb17f8f3a082a21f80000000013e300a1dee002a21f800000000149b00a0824002a21f82c82c83e02c82c83e19da3c03d3c8a000eea7f72) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P01 : WideCovered band 8766238 9504135 := wide_block_sound band profiles_RelativeWidePack6815_P01 8766238 9504135 (wideData 16 0x138ac6acc000a887c0000000000bff01974f800a887e0000000000fcd5bdba002a21f82080082003a7177d8800a887e000000000433b18af6002a21f8000000001183446b8000a887e00000000056ea1aef0002a21f80000000016b283f9a800a887e0000000006ae90e8e6002a21f80000000015b386b0f000a887e00000000032ce0af2e002a21f86192186486cb2dfd6f9f38dc40a887e0000000000af8a2c0ad72dec004c23f0000000000193c9b413ebadb001308fc0820020805fafa80eca2eb001308fa0ba0ba0f80ba0ba0f80e793fa0e8e7fb0010ef1d76) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P01 : WideCovered band 9504136 10094454 := wide_block_sound band profiles_RelativeWidePack6815_P01 9504136 10094454 (wideData 16 0x3eea01a2e8000a887c0000000004a4d01c74e000a887e000000000177a01aa18000a887e082002080161d41c30e800a887e000000000365e01871d800a887e000000000373b0183bc800a887e000000000423801a62b800a887e0000000003e8801871c000a887e000000000429f0187cc000a887e0000000002fad01afce800a887e0000000001b2d418f68800a887e0820020800ebf018fce000a887e0000000003a4e1da26002a21f8000000000eba86a2b800a887e000000000471b018bd9800a887e0e40e412a0e40e412a065d67a05cb0de61129aaeac) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P01 : WideCovered band 10094455 10906143 := wide_block_sound band profiles_RelativeWidePack6815_P01 10094455 10906143 (wideData 16 0x82002080722e03f35b001308fc0000000000729b006dff0004c23f00000000002a20a02a2ab001308fc0000000000bedfc066eaa004c23e80000000004c64a1cb73004c23f0820020800786107bebbc801308fc000000000431c01daff800a887e0000000003e7d01be7a000a887e0000000003f5a01bee8800a887e0000000004a1901e26c000a887e00000000043ba01c34e800a887e000000000136e01ea9f800a887e08200208007ea01b64b800a887e000000000377a019eef000a887e0000000003fcd01be9e000a887e0e80e812a0e80e812a06b9efb0696a936113aabe6a) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P01 : WideCovered band 10906144 12086781 := wide_block_sound band profiles_RelativeWidePack6815_P01 10906144 12086781 (wideData 16 0xf2aa43a18b8004c23f00000000003922c0bf2fa801308fc0000000000efc70368cb8004c23f02080082001eeab0bb75b001308fa0000000000b8ba42a9ee4004c23f00000000002ba4808ce5f001308fc0000000000b3d7427fdec004c23f020800820019e0c08ab39801308fc0000000000a7ef81f5fbe004c23f00000000002822d069639801308fc0000000000ad9fc1f19aa004c23f0208008200bba41aed36004c23e80000000001f61f05cb3b801308fc0000000000779640ffefc004c23f000000000029f1c05a37e001308fc0f40f412a0f40f412a07bba9b08f26e62114fa597a) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P01 : WideCovered band 12086782 12455730 := wide_block_sound band profiles_RelativeWidePack6815_P01 12086782 12455730 (wideData 5 0x82002080162c2063ee26004c23e80000000004f3e813f6f8001308fc000000000128ba843ff34004c23f00000000004c70c128f79801308fc0fc0fc12a0fc0fc12a0e0bfae0dbe5f381179a78f6) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7733179 8766237 12455730 c0_RelativeWidePack6815_P01 (wide_covered_join band 8766238 9504135 12455730 c1_RelativeWidePack6815_P01 (wide_covered_join band 9504136 10094454 12455730 c2_RelativeWidePack6815_P01 (wide_covered_join band 10094455 10906143 12455730 c3_RelativeWidePack6815_P01 (wide_covered_join band 10906144 12086781 12455730 c4_RelativeWidePack6815_P01 c5_RelativeWidePack6815_P01)))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 10)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 10≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤59)
    (hT0 : 3656≤T) (hT1 : T≤4088) (hnu : 7733179≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤22659965433996529 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R010

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R011
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨10,60,3599,4058,27139337404664886⟩
private def profiles_RelativeWidePack6815_P01 : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨43268,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P01 : WideCovered band 7864250 8460840 := wide_block_sound band profiles_RelativeWidePack6815_P01 7864250 8460840 (wideData 16 0x18fdc0e83f00192d982080080005bebcf95b8d30b42064b660820020800a4e7ed0a927d72002a3ab8000000001e9eae03ef4a3c002a3ab80000000013d34902bfaffc002a3ab8000000000dfa3a01e23ab6002a3ab80000000002abfd752ba827dc00a8eae0000000000e2cb3f0dcebc62004c74f000000000078a1f1987ef800a8eae0820020801fea12e6ca000a8eae0000000000b0dec2318b8002a3ab80000000018bf8173b800a8eae0000000000a1b2413aaf4002a3ab80000000001f25b029e6a000a8eae00000000007ace00a6929002a3ab82d82d84b02d82d84b1cb7b904d39eae00f8a8da0) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P01 : WideCovered band 8460841 8759136 := wide_block_sound band profiles_RelativeWidePack6815_P01 8460841 8759136 (wideData 16 0x49e01a1c80064b660000000001a1329f80064b68000000000138e05da600192d98000000001f94d82000192da00000000003e381e7800064b6600200000047d322a00064b680800020801f0809c2400192d98000000000cd3807aa00064b680000000003e5b06aae00192d98000000000fe6832600192da000000000138f4169f80064b66000000000531801dfd00192da000000000199e80f7a80064b660000000804e5e1dc80064b68000000000569904fb700192d982f02f04b02f02e84b1baffc04da9cb0090971bf8) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P01 : WideCovered band 8759137 9132005 := wide_block_sound band profiles_RelativeWidePack6815_P01 8759137 9132005 (wideData 16 0x1bb3c0acac002a3ab80000000001ef8807fa9002a3ab80000000002da6e15f23002a3ab04100104007a27a4cf219800a8eae0000000001f580a86400192d980000000007d2c225d80064b68000000000237a0af6200192d980000000008b281e4a80064b6800000000027bb0b82e00192d980000000009cec1bd880064b680000000002eac0b92000192d98000000000b9f81b5800064b68000000000361f0baa600192d980000000014a0bc3400192da00000000003e341ac980064b660be0be12c0be0be12c060cf8c04e638b0090df88e8) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P01 : WideCovered band 9132006 9728596 := wide_block_sound band profiles_RelativeWidePack6815_P01 9132006 9728596 (wideData 16 0x14a20060c60002a3ab8000000001e9018689000a8eae000000000172c418a5c000a8eac082002080128a1db7c002a3ab80000000010bbc5f2e000a8eae0000000004a19179ba002a3ab800000000148745ba9800a8eae000000000635c1fb7e002a3ab8000000001ade063b9000a8eae00000000012ac16cba002a3ab80000000002fb05a7a000a8eae0000000000bef15eaa002a3ab80000000003924568b800a8eae082002080320a10ab6002a3ab8000000001c9a41f38800a8eae0e20e212c0e20e212c063aefa05a3986a091bf4e38) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P01 : WideCovered band 9728597 10325186 := wide_block_sound band profiles_RelativeWidePack6815_P01 9728597 10325186 (wideData 16 0x11c3c06e922002a3ab80000000012a6c06edf8002a3ab8000000000effc06fc6e002a3ab00000000007bf9070c74002a3ab8208008200bdac067a3e002a3ab8000000000fb60065ef0002a3ab80000000010ee4069a2e002a3ab8000000001296406be24002a3ab80000000012828067b30002a3ab800000000108e8068976002a3ab80000000006bf1069932002a3ab02080082002be0064f70002a3ab8000000000f8347e19800a8eae0000000003fdd1f8b6002a3ab800000000118687e89800a8eae0e60e612c0e60e612c069ceda05d70fae092d21ff6) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P01 : WideCovered band 10325187 11294647 := wide_block_sound band profiles_RelativeWidePack6815_P01 10325187 11294647 (wideData 16 0x2ae0905d2ef00131d3c00000000013d905c3da80131d3c082002080071d280fb8b6004c74f000000000028e5e048b9b00131d3c0000000000ada600f9a3c004c74f00000000002de7d029f4a80131d3c0000000000f6dac7b8e80131d3a0000000001a0f74079979004c74f00000000009fe8a03c2ba40131d3c2080082002e9aed0a58be880131d3c0000000004e7b01db8b000a8eae0000000004e9901df08000a8eae0000000001f8c41e2ea000a8eae0820020803e4901b69b800a8eae0000000004a1f01d2f8000a8eae0ea0ea12c0ea0ea12c06fefda06a79968093e2f9b2) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P01 : WideCovered band 11294648 12487828 := wide_block_sound band profiles_RelativeWidePack6815_P01 11294648 12487828 (wideData 16 0x176c2c56b8b6004c74f00000000005835d14aa6c00131d3c0820020800f7e3842fdec004c74e80000000004db1811af4d80131d3c000000000124c343bc96c004c74f02080082002cf6a0de22a80131d3c0000000000e7ea82edd2e004c74e80000000003ceb80cdb2f00131d3c0000000000e79382bb926004c74f02080082001be7f09cf7880131d3c0000000000b1974228e6c004c74f00000000002f76b09caaf00131d3c0000000000b5a38220a26004c74f02080082014d301e2876004c74f000000000028adb05f37800131d3a0f60f612c0f60f612c0a88bfe09ce3cee095d7dc2a) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P01 : WideCovered band 12487829 12636975 := wide_block_sound band profiles_RelativeWidePack6815_P01 12487829 12636975 (wideData 2 0x2080082005f6681affc900131d3a0fe0fe12c0fe0fe12c0fef7ee109edfb6097fb7fa4) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7864250 8460840 12636975 c0_RelativeWidePack6815_P01 (wide_covered_join band 8460841 8759136 12636975 c1_RelativeWidePack6815_P01 (wide_covered_join band 8759137 9132005 12636975 c2_RelativeWidePack6815_P01 (wide_covered_join band 9132006 9728596 12636975 c3_RelativeWidePack6815_P01 (wide_covered_join band 9728597 10325186 12636975 c4_RelativeWidePack6815_P01 (wide_covered_join band 10325187 11294647 12636975 c5_RelativeWidePack6815_P01 (wide_covered_join band 11294648 12487828 12636975 c6_RelativeWidePack6815_P01 c7_RelativeWidePack6815_P01)))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 10)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 10≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤60)
    (hT0 : 3599≤T) (hT1 : T≤4058) (hnu : 7864250≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤27139337404664886 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R011
end MergedPart1
section MergedPart2
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R012
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨10,61,3502,3507,27072996365050479⟩
private def profiles_RelativeWidePack6815_P02 : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨43518,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P02 : WideCovered band 7995321 8494567 := wide_block_sound band profiles_RelativeWidePack6815_P02 7995321 8494567 (wideData 16 0x5d14cc04ace000000000069018f5012b360000000001bc074e404ace00000000007c02a3d012b380820820820e2f3d064a348b7092b38082002080075cb8561afeb000a9cbe000000000374d04f25ab6002a72f80000000008b300bfcb99000a9cbe0c30030c00abc6d066873ce1002a72f82080082002deeb01aa4f3aa8013397c0000000000bda1efe4b000a9cbe0000000000b1c19dbfd800a9cbe0000000000acd16c33a000a9cbe08200208042d37db30002a72f80000000019d07874a000a9cbe0b60b612c0b60b612c2ffc04d63e3a00faa9bae) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P02 : WideCovered band 8494568 8692381 := wide_block_sound band profiles_RelativeWidePack6815_P02 8494568 8692381 (wideData 16 0xbb0ca80064e7000000000037806c940064e6e0000000004341f49c0064e700000000005683baac0064e6e0820020800b9e44ef9c80064e700000000000b007e9004acd80000000002f01ea2012b380000000000bc075a804acd80000000003901c2c012b380000000000e806ad004acd80000000003c0192e012b380000000000f8770012b3800000000012457e012b3800000000012c362012b360000000001340e8012b380bc0bc12e0bc0bc12e277b04c3ce7c0909e1ae6) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P02 : WideCovered band 8692382 8993812 := wide_block_sound band profiles_RelativeWidePack6815_P02 8692382 8993812 (wideData 16 0x5b0ac3e001939c00000000005f0ad66001939b80000000006e0aee4001939c00000000007a0893c001939b80000000008a07b66001939c00000000009e0b9a2001939b8000000000bc0bcb0001939b82080082001de922fa80064e6e00000000012417ce80064e70000000000138171f80064e6e000000000160166800064e70000000000174137900064e6e0000000001ac126900064e700000000001e40f0e80064e6e00000000022c0b7980064e700be0be12e0be0be12e2a9a04d6eafe090cf68e8) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P02 : WideCovered band 8993813 9427119 := wide_block_sound band profiles_RelativeWidePack6815_P02 8993813 9427119 (wideData 16 0x2603f2d800a9cbe0000000002e0376a000a9cbe0000000003642e48000a9cbe0000000004601ed9800a9cbe0000000005bc075e800a9cbe0000000007fc538ac00a9cbe1040041000b7e4caf18800a9cbc0000000000b82a3a00064e6e0000000000e02a3c80064e700000000000e82a3d80064e6e0000000000ec2a4c80064e700000000000f42a5a00064e6e0000000000fc2a6e00064e700000000001242a8980064e6e00000000012c2aad00064e700e00e012e0e00e012e2f7904e67ba80919a2eb6) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P02 : WideCovered band 9427120 10029982 := wide_block_sound band profiles_RelativeWidePack6815_P02 9427120 10029982 (wideData 16 0x1a4063de2002a72f80000000006d01926a800a9cbe0000000001e4064ee8002a72f80000000007e01977a800a9cbe000000000234066f7a002a72f8208008200e9418ec8800a9cbe00000000016c5b5d800a9cbc0000000001a46638800a9cbe0000000001e06fda800a9cbe0000000001f8720f800a9cbe000000000234728b000a9cbe0000000002a4735b000a9cbe0000000002f876aa000a9cbe0000000003ac7aae000a9cbe0000000003343b6c000a9cbe0e60e612e0e60e612e2fed05a72f68092875f7c) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P02 : WideCovered band 10029983 10632844 := wide_block_sound band profiles_RelativeWidePack6815_P02 10029983 10632844 (wideData 16 0x5c01ab6e000a9cbe0000000001ac072cbe002a72f80000000006c01ce19000a9cbe0000000001bc073d2e002a72f80000000007801d2df800a9cbe0000000001f0075be6002a72f82080082005c41c3fc000a9cbc000000000168064cae002a72f80000000005f01a639000a9cbe0000000001a406b962002a72f80000000006d01af8d000a9cbe0000000001e006ccb4002a72f80000000007b01b749000a9cbe08200208022106d868002a72f80000000005c018efa000a9cbc0e80e812e0e80e812e3ede05e36b280939afb3a) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P02 : WideCovered band 10632845 11763211 := wide_block_sound band profiles_RelativeWidePack6815_P02 10632845 11763211 (wideData 16 0x8200208032422c960004ce5f0000000001c907d38c8013397c00000000073c1efeee004ce5e8000000001a805e77e8013397c000000000060d07aabd8013397c0820020800b5172b2a004ce5f00000000019a05926d0013397a0000000005ec0e6868004ce5f0000000000182012faee004ce5f00000000001a24125cba004ce5f0208008201de43badf8013397a0c30030c016ec019b1ac013397c0000000001f1f039a9c4013397c20800820026ba428abeec004ce5f00000000007e01fa3b000a9cbe0ee0ee12e0ee0ee12e470b06bfdaf8094ae8ef6) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P02 : WideCovered band 11763212 12818220 := wide_block_sound band profiles_RelativeWidePack6815_P02 11763212 12818220 (wideData 14 0x2080082002be07ea8b4004ce5e80000000002d74730ea0004ce5f00000000002a6c6208ae004ce5f02080082001ea05f6bb6004ce5f00000000001f70521af6004ce5e80000000001ee44e2c78004ce5f00000000001cf4425fa2004ce5f020800820018683e79b4004ce5f00000000001b603a1a38004ce5e80000000001b2c373fe4004ce5f0208008201690ba7fa0013397c00000000006390abf888013397c000000000062f0a9edb8013397c0fa0fa12e0fa0fa12e767f0ae249b6096cb29b2) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7995321 8494567 12818220 c0_RelativeWidePack6815_P02 (wide_covered_join band 8494568 8692381 12818220 c1_RelativeWidePack6815_P02 (wide_covered_join band 8692382 8993812 12818220 c2_RelativeWidePack6815_P02 (wide_covered_join band 8993813 9427119 12818220 c3_RelativeWidePack6815_P02 (wide_covered_join band 9427120 10029982 12818220 c4_RelativeWidePack6815_P02 (wide_covered_join band 10029983 10632844 12818220 c5_RelativeWidePack6815_P02 (wide_covered_join band 10632845 11763211 12818220 c6_RelativeWidePack6815_P02 c7_RelativeWidePack6815_P02)))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 10)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 10≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤61)
    (hT0 : 3502≤T) (hT1 : T≤3507) (hnu : 7995321≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤27072996365050479 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R012

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R013
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨10,61,3539,4028,28225868518720469⟩
private def profiles_RelativeWidePack6815_P02 : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨43518,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P02 : WideCovered band 7995321 8494567 := wide_block_sound band profiles_RelativeWidePack6815_P02 7995321 8494567 (wideData 16 0x1fea04012b38000000000236f0cec04acd80000000009cf06f5012b380000000002b5901b61012b3808208200226bfa9e419348a0dc24ace020800820058f8eb0567ca79000a9cbe000000000069da9c04f77ea2002a72f80000000019d3a903831eb8002a72f830c00c30079bc9f9066aab8ef002a72f82080082008ae8cb006abe0b2c004ce5f00000000008f68e1fa7dd800a9cbe0000000001f8cb06a0b36002a72f80000000007aaec16e6f8800a9cbe082002080072af537bbf2002a72f80000000002bafa07933a000a9cbe0b60b612c0b60b612c064d24904db08fa00faa9bae) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P02 : WideCovered band 8494568 8730060 := wide_block_sound band profiles_RelativeWidePack6815_P02 8494568 8730060 (wideData 16 0x2aaa03d7a001939c0000000000bfa40b9e80064e6e0000000803a1a01dac001939c00000000010ef01b8001939b80000000018d24176b40064e70000000000062ee832c940064e6e000000000065d242b6dc0064e70000000000074a2c4a58c0064e6e08200200017b839176c62001939b8000000000a874076e804acd8000000000adf0071b804ace00000002009ea406bb804ace00000000005e2c064f804ace000000000069bc766012b360000000001b6f14d804ace02f02f04b82f02e84b9ebb7d04ca0e7e0909e1ae6) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P02 : WideCovered band 8730061 9031491 := wide_block_sound band profiles_RelativeWidePack6815_P02 8730061 9031491 (wideData 16 0x6dd0aee8001939c00000000001a3c2bfa80064e6e000000000062f0b93c001939c0000000001bc0bae6001939b80000000011b0bcf8001939c0000000000297c23fe00064e6e0000000000b4d08af6001939c0000000000ba4caac001939b82080082007fb422bb80064e6e0000000002fbb06d22001939b8000000000cf341acb80064e700000000003a3d068e2001939b8000000000fcac178e00064e70000000000469f05b24001939b80000000013b7c13dd80064e700be0be12e0be0be12e060f73d04dbcbee090d7fda6) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P02 : WideCovered band 9031492 9540156 := wide_block_sound band profiles_RelativeWidePack6815_P02 9031492 9540156 (wideData 16 0x3e717ffe000a9cbe0820020803ead0bc7e002a72f8000000001896c47ed800a9cbe0000000006ffb10d30002a72f8000000000186790efb2002a72f80000000001a36b0cd66002a72f800000000019f1e09afe002a72f8000000001ebb8129f800a9cbe000000000079ee0462a400a9cbe0000000000e4e28069c7b002a72f0410010400892194dffad800a9cbe000000000275e0abf0001939b8000000000aa6c2b1800064e700000000002bfb0acb2001939b8000000000be382b5800064e700e00e012e0e00e012e064d35804ee8b36091a2cb74) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P02 : WideCovered band 9540157 10143018 := wide_block_sound band profiles_RelativeWidePack6815_P02 9540157 10143018 (wideData 16 0x2080082004841b23e800a9cbe00000000043ec01923e000a9cbc0000000003f8c1ca22002a72f80000000012ebc064b7c002a72f8000000001492c064fb6002a72f80000000015df8065d74002a72f800000000059a8066d20002a72f80000000005ef5067f74002a72f82080082007ba4061df6002a72f80000000010cf45e9e800a9cbc0000000004b7a19e78002a72f80000000015a687379000a9cbe0000000005f4a1cf70002a72f80000000019b34768d800a9cbe00000000012d77ac800a9cbe0e60e612e0e60e612e0699fec05b6dffa092a32db6) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P02 : WideCovered band 10143019 10783560 := wide_block_sound band profiles_RelativeWidePack6815_P02 10143019 10783560 (wideData 16 0x8200208002d33d02869a20004ce5f00000000005ebc07f820002a72f82080082007d38078b3a002a72f80000000010f2406bae6002a72f80000000013b34073aae002a72f80000000014834073e6a002a72f80000000014e24074b72002a72f80000000015d24075a24002a72f80000000011a41daae000a9cbe0820020801afc01c2b9800a9cbc000000000422c01965f000a9cbe00000000047bc01a78e000a9cbe0000000004e2e01afc9000a9cbe000000000521c01b318000a9cbe000000000566f01b6ca800a9cbe0ea0ea12e0ea0ea12e06fd21b05fae97c093b6c972) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P02 : WideCovered band 10783561 11989285 := wide_block_sound band profiles_RelativeWidePack6815_P02 10783561 11989285 (wideData 16 0x3abbd0acf9c0013397c0000000000eafe02abbbc004ce5f00000000003a65e09e39c0013397c0820020800659fc22dca2004ce5f00000000002d78807e20b0013397c0000000000b89e81f39a8004ce5e80000000002bf5d05f38a0013397c00000000072be07ba4c0013397c08200208007fbb41728b4004ce5f00000000002b3dc059e3e8013397a0000000000a7b6c0e8df8004ce5f00000000003876f04ce1e0013397c000000000520a04aa7a8013397c0820020802fda03ae080013397a0000000000a6c245a89c013397c0f40f412e0f40f412e07f9f5e08cbffe6094db8eac) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P02 : WideCovered band 11989286 12818220 := wide_block_sound band profiles_RelativeWidePack6815_P02 11989286 12818220 (wideData 11 0x820020801f78ac7f39ba004ce5e8000000000897ea1ceb788013397c0000000001e0834628c76004ce5f02080082005c67b17f65a0013397c00000000017bf3c528be4004ce5e80000000005d38913a6cd0013397c00000000013cf6842bf3e004ce5f020800820039b1c0fae1e8013397c0000000001299b03a6bbc004ce5e800000000049f190de63a0013397c0fc0fc12e0fc0fc12e0e29a4c0befc9ec09782be26) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7995321 8494567 12818220 c0_RelativeWidePack6815_P02 (wide_covered_join band 8494568 8730060 12818220 c1_RelativeWidePack6815_P02 (wide_covered_join band 8730061 9031491 12818220 c2_RelativeWidePack6815_P02 (wide_covered_join band 9031492 9540156 12818220 c3_RelativeWidePack6815_P02 (wide_covered_join band 9540157 10143018 12818220 c4_RelativeWidePack6815_P02 (wide_covered_join band 10143019 10783560 12818220 c5_RelativeWidePack6815_P02 (wide_covered_join band 10783561 11989285 12818220 c6_RelativeWidePack6815_P02 c7_RelativeWidePack6815_P02)))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 10)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 10≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤61)
    (hT0 : 3539≤T) (hT1 : T≤4028) (hnu : 7995321≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤28225868518720469 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R013

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R014
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨10,62,3450,3996,28652606475617611⟩
private def profiles_RelativeWidePack6815_P02 : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨25159,195,5079⟩
  | 2 => ⟨25216,192,5079⟩
  | 3 => ⟨43768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P02 : WideCovered band 8126392 8516619 := wide_block_sound band profiles_RelativeWidePack6815_P02 8126392 8516619 (wideData 16 0x5ef9cc7c379a9012cbc08200208027ad65fc5dbdae8092cba000000000165c6412ae7e012cbc000000000171ca0129be2012cbc0000000002b68f45bdf22012cbc00000000013adb80a79a7012cba082102084061aa4c42d7caec092cbc0000000000fc9ed80cee79b4001965e02080082002faee2c2e4c3ee000aaaee000000000065be7803ef4b66002aabb8000000001882cc02bb5820002aabb80000000011835f01de58ba002aabb8000000000cf6c901a65b68002aabb8000000000ab21c01826ff0002aabb80000000008dbc919f37b000aaaee0b80b812c0b80b812c074dade06933a2e00fcaa9bc) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P02 : WideCovered band 8516620 8678421 := wide_block_sound band profiles_RelativeWidePack6815_P02 8516620 8678421 (wideData 16 0x802f8eeec01b74b7ab03065978000000000263b0ee804b2e80000000009ae05ea012cbc00000000033aa02aef012cbc0000000003abf03937012cbc000000000429f04963012cba0000000004b5a05afd012cbc000000000571c06ebb012cbc000000000467a01ee9012cbc000000000736a0aaeb012cba0000000c0171e6f85ed37aa7092cbc0000000003e5b243a6d39012cbc0000000004bf8605e7a3d012cbc000000000663e38065d79f404b2e80000000001920efc07ee72cc04b2f02f82f84c02f82f84c03c2ecac067c69cee110a2ccf2) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P02 : WideCovered band 8678422 8982988 := wide_block_sound band profiles_RelativeWidePack6815_P02 8678422 8982988 (wideData 16 0x4afc04a76001965e00000000007fe426ec800659760000000002ab803abc001965e0000000000bea80ade80065976000000000225908cea001965e0000000000f9245a8001965d8000000001287477b001965e0000000000d96c1af800065976000002080675c04eb3001965e000000c0001863a08df9001965d80080000001931807e73001965e00000000001c63b0dd2f001965d80000000002e2ac01936fc0065978080002000332c69841b7a937ac20659760000000002b6b34321be6001965d82f82f84c02f82f84c0d92dd600729a9aaa110cbb9e0) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P02 : WideCovered band 8982989 9306590 := wide_block_sound band profiles_RelativeWidePack6815_P02 8982989 9306590 (wideData 16 0x4100104008e63d4ed2ef000aaaee0000000002f180bebc001965d80000000002f6027b9000659780000000000be809ea6001965d8000000000eb0ee60001965e00000000002de02a29800659760000000000b7c0a876001965e00000000018f4ffba001965d800000000029e82b1b000659780000000000a3a0ad6a001965d82080082008ee42ff9000659780000000002ff8068fa001965d8000000000cf2c179d800659780000000003b2b07e32001965d8000000000fefc1f2e800659760e00e01300e00e0130067cebc04de5c2c19196e8ae) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P02 : WideCovered band 9306591 9915724 := wide_block_sound band profiles_RelativeWidePack6815_P02 9306591 9915724 (wideData 16 0x6a8e018a4e800aaaee0000000006a6818aa4002aabb800000000168018e7d800aaaee0000000005f87f5e800aaaee00000000057c777c000aaaee082002080464c1c8a6002aabb80000000017d2c3a7f000aaaee00000000077aa17aec002aabb000000000018afd16efe002aabb8000000000196ad08df0002aabb80000000013b64520b000aaaee000000000773f1be800aaaee00000000063dd0dc28002aabb800000000018a3a08e2c002aabb80000000002e3890187afc00aaaee0e60e61300e60e6130065af1805a65aba191eaba68) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P02 : WideCovered band 9915725 10524858 := wide_block_sound band profiles_RelativeWidePack6815_P02 9915725 10524858 (wideData 16 0x16de8070f62002aabb80000000015978068ffc002aabb80000000018e64072970002aabb8000000000afac073a2e002aabb80000000002b6d06af68002aabb8208008200eb2006bb28002aabb80000000014a60066abe002aabb80000000014b68063ca6002aabb00000000017aac069dae002aabb80000000016a24061aa4002aabb8000000000ea2c06b9b8002aabb80000000003ea106ccee002aabb82080082002ee4060f64002aabb80000000014eb8061ae2002aabb80000000013e7863cb800aaaee0e80e81300e80e8130072b6bb05cacd34192ff1824) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P02 : WideCovered band 10524859 11476630 := wide_block_sound band profiles_RelativeWidePack6815_P02 10524859 11476630 (wideData 16 0xbcce8166ce6004d36e800000000039e2b04f33a80134dbc0820020804e9846a3ed00134dbc0000000000afce80e4eb6004d36f00000000002df0b01ffed80134dba0000000000ebef8574b80134dbc000000000136ae4079fb3004d36f000000000098e0e03861fc0134dbc2080082000fb9e90a9af2a00134dbc0000000005f1a01deab000aaaee0000000005e1e01cf8d800aaaee000000000678b01eb6c800aaaee000000000438d01cafd800aaaee000000000136d41f368800aaaee082002080535f01c31c800aaaee0ec0ec1300ec0ec13007aa38d069b2eb8194936de0) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P02 : WideCovered band 11476631 12694898 := wide_block_sound band profiles_RelativeWidePack6815_P02 11476631 12694898 (wideData 16 0x7c39f16df1c00134dba0000000001fdbf85fde7e004d36f02080082004e65e12ffd900134dbc00000000016fdf4424abc004d36f00000000005ab590fb74800134dba00000000016bbf8437bac004d36f020800820038e9c0cbadc00134dbc000000000122f682eaafc004d36f000000000048afd0afe5d80134dba0000000000b98e42b7cb8004d36f0208008200387de0a8bde00134dbc0000000000e7cf8222cb6004d36f00000000003aad907ef2c80134dba00000000007ff681f78ea004d36f020800820028a3f07cf2e00134dbc0f80f81300f80f81300b8aa0809c3fd62196864828) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P02 : WideCovered band 12694899 12999465 := wide_block_sound band profiles_RelativeWidePack6815_P02 12694899 12999465 (wideData 4 0xbe3b801932d20004d36e8000000000bee2c01939a66004d36f00000000009b3fe1eef6e80134dbc12212213012212213013fcfa910cafce6198aefba0) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8126392 8516619 12999465 c0_RelativeWidePack6815_P02 (wide_covered_join band 8516620 8678421 12999465 c1_RelativeWidePack6815_P02 (wide_covered_join band 8678422 8982988 12999465 c2_RelativeWidePack6815_P02 (wide_covered_join band 8982989 9306590 12999465 c3_RelativeWidePack6815_P02 (wide_covered_join band 9306591 9915724 12999465 c4_RelativeWidePack6815_P02 (wide_covered_join band 9915725 10524858 12999465 c5_RelativeWidePack6815_P02 (wide_covered_join band 10524859 11476630 12999465 c6_RelativeWidePack6815_P02 (wide_covered_join band 11476631 12694898 12999465 c7_RelativeWidePack6815_P02 c8_RelativeWidePack6815_P02))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 10)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 10≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤62)
    (hT0 : 3450≤T) (hT1 : T≤3996) (hnu : 8126392≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤28652606475617611 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R014

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R015
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨10,63,3399,3965,28343111664229959⟩
private def profiles_RelativeWidePack6815_P02 : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨25159,195,5079⟩
  | 2 => ⟨25216,192,5079⟩
  | 3 => ⟨43768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P02 : WideCovered band 8257463 8555550 := wide_block_sound band profiles_RelativeWidePack6815_P02 8257463 8555550 (wideData 16 0x12ce9e1cda8cc04b9800000000018e7a801b77827012e3e000000000064878902af2ef3012e6000000000007bbf6d04a74bab012e3e0820020802b0ef6c58c388c24b980000000000b878e19ef3b804b9800000000004cef8019f2f804b98000000000049bdd01eb9cc04b8f8000000000aee9a15a78f804b9800000000003f3ac0787ccc04b980208608219dcfae43a68e26092e600820020801a8e6ba159f88f2002ae3f80000000001c69cf41379b6c000ab8fe000000000761ba40badb0f000ab8fe0000000004f7cb407d838a800ab8fe0b80b812c0b80b812c0bea3eb09df3c6200feaafea) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P02 : WideCovered band 8555551 8709402 := wide_block_sound band profiles_RelativeWidePack6815_P02 8555551 8709402 (wideData 16 0x233f15ec04b9800000000006d640abc804b9800000000009fe806cd404b980000000000af7807dc404b8f80000000008d2806de004b980000000000cff80bfcc04b980000000000ec2c0fac404b980000000000be2006b012e3e00000000047bc05c3f012e600000000c01ebae1f5e9acb3d092e600000000001fa92c7eee004b9800000000008b3cb01cfc9c04b8f800000000099e3d04efabc04b980000000000aaf8d09920fc04b980000000000cae3c0d97aac04b9802f82f84c82f82f84c86f3cda0063cb58be110ab8eba) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P02 : WideCovered band 8709403 8969026 := wide_block_sound band profiles_RelativeWidePack6815_P02 8709403 8969026 (wideData 16 0x52db1be00065ca00000000002aef05ee4001971f8000000000aee416bd00065ca000000000043ad01c33001971f8000000000f9e80b3800065ca000000000043dd02aa0001971f80000002016e2c0a5fc0065c7e0000000007f4808c77001971f80000000001828d05aa1001972800000000001a7ed0a877001971f82080080004f6cd4592e880065ca00000000002f8e03af8012e3e0000000801edb0fb004b980000000000786017a012e6000000000016bc02fec012e600be0be1320be0bc132065931d04c21d76190d25ab2) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P02 : WideCovered band 8969027 9276729 := wide_block_sound band profiles_RelativeWidePack6815_P02 8969027 9276729 (wideData 16 0xdcb42e6800065ca00000000002e3a08b22001971f80000000002d34321d00065ca00000000000b0c0c9e0001971f80000000004fb81ebb00065ca00000000000ac90cbf2001971f800000000028fc339900065c7e00000000016fb078ea001971f80000000001e74367d00065ca0002000000069a0ddf8001971f8000000200683c1beb00065ca00800020002a5b09e6e001971f8000000000f8a01f8a80065ca00000000003e1a02e64001971f80000000011f2c1e4a80065ca00e00e01320e00e0132068d79d04d69ae41919339a2) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P02 : WideCovered band 9276730 9872903 := wide_block_sound band profiles_RelativeWidePack6815_P02 9276730 9872903 (wideData 16 0x730c19b3a002ae3f8000000000acf463ea800ab8fe0000000002740659f8002ae3f00000000005a746699800ab8fe082002080120d01924a000ab8fe0000000006a3f0fce0002ae3f8000000001dce43669000ab8fe000000000065fe45e6d000ab8fe000000000069c70237b000ab8fe000000000067b6812cd800ab8fe0000000005efb10bf2002ae3f00000000001c3ba08da9002ae3f80000000002b31c18f7b002ae3f80000000002f2bf1493f002ae3f84100104008c30d4eb3ee000ab8fe0e20e21320e20e213206ccb9d04ea68fa191dec970) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P02 : WideCovered band 9872904 10488309 := wide_block_sound band profiles_RelativeWidePack6815_P02 9872904 10488309 (wideData 16 0x5b8801aa9a000ab8fe0000000006b2b01cf1c800ab8fe000000000475901aefa800ab8fc00000000006b841b248000ab8fe0820020801f4f01c35d000ab8fe000000000524f018a4e800ab8fe000000000564e018a0f800ab8fe000000000662901abbc000ab8fe000000000620a018b2d800ab8fe0000000004bee01b33e000ab8fe000000000330063ee0002ae3f0000000001fa41930e000ab8fe08200208047a801939f000ab8fe000000000570c1a922002ae3f80000000017a34674e000ab8fe0e80e81320e80e8132073bec905be78b8192f3e92c) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P02 : WideCovered band 10488310 11334492 := wide_block_sound band profiles_RelativeWidePack6815_P02 10488310 11334492 (wideData 16 0xabc201678e8004da7e8000000001bab00a9be6004da7f02080082001bb2803926f001369fc0000000000f4968065d76004da7f0000000000582b90186ad401369fa186006180164f3c0a3e679801369fc0820020802e9c0283dd800ab8fe0000000005b7a01cafc800ab8fe0000000005e8e01cb0e800ab8fe0000000006b4901eeaf000ab8fe00000000063a901ce9d800ab8fc0000000006a0e01d33a800ab8fe0000000000ead41f678800ab8fe082002080322e01b7fd000ab8fe0000000005f0a01c77f800ab8fe0ec0ec1320ec0ec13207be7bf068b6c701948b08e8) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P02 : WideCovered band 11334493 12565304 := wide_block_sound band profiles_RelativeWidePack6815_P02 11334493 12565304 (wideData 16 0x1b9ba857c9b8004da7e82080082005ba1c11d38f001369fc00000000017793c3f9f72004da7f00000000005b6680ecbab001369fc0820020800f1bf83b5ee0004da7e80000000004c75d0c932b001369fc0000000000ffaf82a0db2004da7f00000000004ca4f0bc2aa801369fc08200208007d8f02a8dac004da7e80000000003cbfe08de6b801369fc0000000000e5df01bc97c004da7f00000000003ee4808aebe801369fc08200208057ab07da2e001369fa0000000000b6bbc162c6c004da7f00000000002ffaf058f5d001369fc0f80f81320f80f81320b7828b0997dcb0195e2ff74) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P02 : WideCovered band 12565305 13180710 := wide_block_sound band profiles_RelativeWidePack6815_P02 12565305 13180710 (wideData 8 0x47a8f4075937d001369fa00000000046adec073d7e8001369fc0820020802fcf64068de98801369fc0000000002e5e74060e298001369fc0000000002edae4061ba3a001369fa082002080227c287619ea004da7f00000000008bacf18b72b801369fc12012013212012013213997380f93aa621988f3eec) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8257463 8555550 13180710 c0_RelativeWidePack6815_P02 (wide_covered_join band 8555551 8709402 13180710 c1_RelativeWidePack6815_P02 (wide_covered_join band 8709403 8969026 13180710 c2_RelativeWidePack6815_P02 (wide_covered_join band 8969027 9276729 13180710 c3_RelativeWidePack6815_P02 (wide_covered_join band 9276730 9872903 13180710 c4_RelativeWidePack6815_P02 (wide_covered_join band 9872904 10488309 13180710 c5_RelativeWidePack6815_P02 (wide_covered_join band 10488310 11334492 13180710 c6_RelativeWidePack6815_P02 (wide_covered_join band 11334493 12565304 13180710 c7_RelativeWidePack6815_P02 c8_RelativeWidePack6815_P02))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 10)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 10≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤63)
    (hT0 : 3399≤T) (hT1 : T≤3965) (hnu : 8257463≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤28343111664229959 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R015

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R016
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨10,64,3349,3932,30476358836534067⟩
private def profiles_RelativeWidePack6815_P02 : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨25159,195,5079⟩
  | 2 => ⟨25216,192,5079⟩
  | 3 => ⟨25314,190,5079⟩
  | 4 => ⟨44018,250,10158⟩
  | 5 => ⟨25360,187,5079⟩
  | 6 => ⟨26466,142,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P02 : WideCovered band 8388534 8582808 := wide_block_sound band profiles_RelativeWidePack6815_P02 8388534 8582808 (wideData 16 0x2aba6c362ead012fe2000000000323bf8524a67012fe40000000003b9ab07ab8bd012fe40000000006a88ec6fbb404bf90000000001ae72a01f37e33012fe2000000000068dbb8039bdae3012fe40000000000a8b25f069e2bf1012fe40820020802ebd61c43b2ddf0092fe40000000000fae3406dff9012fe20000000002ace2052a868012fe40000000000e9fe41acef3012fe40000000002a79a4432c28012fe40000000000b9abc33dc35012fe20822020880f19301bcf35b824bf900000000003f7eba8328bb2e00065fa80ba0ba12c0ba0ba12c1f6939918b7e9e40108abdf8) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P02 : WideCovered band 8582809 8757655 := wide_block_sound band profiles_RelativeWidePack6815_P02 8582809 8757655 (wideData 16 0x30000c01728b9d59861fef092fe40000000000b4b36e59dbb9ef092fe40000000000a2868d1ab6d8780c197e980000000001da5843db7b804bf900000000002ff3d606b3dbbc424bf900000000001aa2cf967bdf6a83065fa60000020800ebbe1901de782d012fe200000300033eabbfc8e36eb9012fe4082002000171b61e84e74ca6092fe20000000001a7f7012f83c012fe40000000001f79f01fdca6012fe40000000002a7f283e7862012fe40000000001e2bf80a8a404bf880000000007b64f03839cc04bf900000000007ffcb06a7cdc04bf902f82f84d02f82f84d08937bb4062d33f24110b2ea34) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P02 : WideCovered band 8757656 9068494 := wide_block_sound band profiles_RelativeWidePack6815_P02 8757656 9068494 (wideData 16 0xefa40bdc80065fa800000000046fe01d2c00197e980000000014ef406700197ea00080000019cb00acb40065fa6000002080060b6c179ec0065fa600000300006ae702bf940065fa600000000007bd744eb940065fa80000000000baa74062ce100197e9800c000300283cd7506bc7bb790c197ea0208008200ab64a7d738df410197e98000000000afabe028e9a80065fa800000000026687c33ef2700197e9800000000079ea80187fb7900197ea00000000004b6ff02921f6f00197e98000000000ca74d02aeabbb00197ea03803804d03803804d0c86dd28075a3b8fc190df6df4) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P02 : WideCovered band 9068495 9379333 := wide_block_sound band profiles_RelativeWidePack6815_P02 9068495 9379333 (wideData 16 0x2db4323a00065fa80000000000b190ca6800197e980000000002aa8331a80065fa80020000000a0d0cee600197e982000082008df8275d00065fa6000000000362c07da800197e98000000000e8301eff00065fa80000000003e3807a2600197e980000000010ae01e0a00065fa8000000000479f06dac00197e980000000010ff41ab800065fa80000000001e5908eec00197e980000000007de8231800065fa80000000002a8d05aa600197e98000000000bbe4136c80065fa80e20e21340e20e2134069b33d04d70ab2211ab5ee2) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P02 : WideCovered band 9379334 9942728 := wide_block_sound band profiles_RelativeWidePack6815_P02 9379334 9942728 (wideData 16 0x820020802bbd1cef4002afcb0000000001ab7856cb800abf2e000000000060e6c7e49000abf2e000000000061ebc520f000abf2e000000000066f644b38800abf2e000000000439c10e62002afcb80000000014b383a9c000abf2e0000000006a0f0ada6002afcb800000000018ece0587c002afcb00000000001d33d04e35002afcb80080000002e32f18a69002afcb80000000003a76d0ffa5002afcb84080104008d2084ed6de800abf2e0000000000e080bde400197e980000000002f702fae00065fa80e40e41340e40e413406e8f6f04e7dd3e211f74fb0) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P02 : WideCovered band 9942729 10564406 := wide_block_sound band profiles_RelativeWidePack6815_P02 9942729 10564406 (wideData 16 0x820020800ad801e2bd800abf2c0000000005a6e019f7c000abf2e0000000005e5b019faf000abf2e000000000629d01a20b000abf2e000000000676d01a2ba800abf2e0000000006ecf01a3ad800abf2e000000000064c01a70d800abf2e0000000007ad06ac30002afcb8208008200ea60063ef8002afcb00000000019be0067b7e002afcb80000000018d3c7f6e000abf2e0000000006b581fdba002afcb8000000001d9a07fa9800abf2e00000000023ab01820b000abf2e0000000000eae0182db000abf2e0ea0ea1340ea0ea134075827805ba5c34213867a3e) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P02 : WideCovered band 10564407 11341503 := wide_block_sound band profiles_RelativeWidePack6815_P02 10564407 11341503 (wideData 16 0x3cf3d02eaad80137e3c0000000001389ec0a8820004df8f00000000006a71d02831e40137e3a2080082000b7d340a6f71e80137e3c0000000006a8901e70f000abf2e0000000006bbf01e76d000abf2e00000000072ed01f34e000abf2e0000000007b4f02866c000abf2e0000000002b7f01ef19800abf2c0820020800f9d01e729000abf2e0000000005f2901c20b000abf2e000000000628c01c24f800abf2e000000000663801c2c9000abf2c0000000006a3c01c39a000abf2e0000000006ea801c6ac000abf2e0ee0ee1340ee0ee13407d9a7a06879ca22149e5bfa) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P02 : WideCovered band 11341504 12584859 := wide_block_sound band profiles_RelativeWidePack6815_P02 11341504 12584859 (wideData 16 0x1bcca44ab970004df8f00000000005d64911c79a00137e3c08200208012fbb03a5fa8004df8e80000000005e7ca0f8fb980137e3c000000000164a3c337f34004df8f02080082002d6cf0bff7900137e3c0000000000ffde4271eea004df8e80000000004aa3b0a961800137e3c00000000012ca6427ab2a004df8f02080082001969808be4f00137e3c0000000000e682c1b08ec004df8e80000000003a7bb0693a900137e3c0000000001249281f6d3a004df8f00000000001de6b05d7aa00137e3c0820020806fe804cf3f80137e3a0f80f81340f80f81340b9b7cd09871e3a215e3f93a) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P02 : WideCovered band 12584860 13361955 := wide_block_sound band profiles_RelativeWidePack6815_P02 12584860 13361955 (wideData 10 0x28a00a2803378f81f982df84137e3a0820020804e9ea407db6a800137e3c000000000460fb0070c26f80137e3a0000000003ebe7c06bc6ac00137e3c0000000003a4bb806bb33a80137e3a0820020802a88287b9cf2004df8f0000000000a93791c964d00137e3c000000000271df46a8978004df8f020800820078b7f18dece00137e3a12012013412012013413ac7580ed26dbe21893bcb2) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8388534 8582808 13361955 c0_RelativeWidePack6815_P02 (wide_covered_join band 8582809 8757655 13361955 c1_RelativeWidePack6815_P02 (wide_covered_join band 8757656 9068494 13361955 c2_RelativeWidePack6815_P02 (wide_covered_join band 9068495 9379333 13361955 c3_RelativeWidePack6815_P02 (wide_covered_join band 9379334 9942728 13361955 c4_RelativeWidePack6815_P02 (wide_covered_join band 9942729 10564406 13361955 c5_RelativeWidePack6815_P02 (wide_covered_join band 10564407 11341503 13361955 c6_RelativeWidePack6815_P02 (wide_covered_join band 11341504 12584859 13361955 c7_RelativeWidePack6815_P02 c8_RelativeWidePack6815_P02))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 10)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 10≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤64)
    (hT0 : 3349≤T) (hT1 : T≤3932) (hnu : 8388534≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤30476358836534067 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R016

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R017
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨10,65,3301,3899,29721485741079288⟩
private def profiles_RelativeWidePack6815_P02 : ℕ → Profile
  | 0 => ⟨25216,192,5079⟩
  | 1 => ⟨25361,191,5079⟩
  | 2 => ⟨25314,190,5079⟩
  | 3 => ⟨25360,187,5079⟩
  | 4 => ⟨25449,185,5079⟩
  | 5 => ⟨44268,250,10158⟩
  | 6 => ⟨26536,141,5079⟩
  | 7 => ⟨26531,139,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P02 : WideCovered band 8519605 8676592 := wide_block_sound band profiles_RelativeWidePack6815_P02 8519605 8676592 (wideData 16 0x82005b66fc48b7ae70139660000000000b8961d45b77ead0939680820000000e1826ec4d6a9300939680000000002b8f744bcee40139680000000001a0da837eb404e598000000000883b904830d804e5a0000000000a978808decf804e5a000000000078f2b07f3bd404e5a0000000000de24d0ceeef004e5980000000008ffff0f9ffb404e5a0000000000ab25816be08404e5a00000000013be0f02cf4d804e5a00000000010aa3801a77d3d01396600000000057abb00a1d36ac04e5a00000000001a2bd6c065ae3d404e5a02f82f84d82f82f84d84b74d38067be2d6a010a33830) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P02 : WideCovered band 8676593 8931697 := wide_block_sound band profiles_RelativeWidePack6815_P02 8676593 8931697 (wideData 16 0x1a6dd3c130b2e840066ab008200208022a9e9f44b79e670819aab80000000017b66901be6b7a0019aac00000000005fbe8128fef40066aae000000000571e7c6f8e760019aac00000000001ebbc01e6cd650019aab800000000038e7a02be4faf0019aab80000000006e298f4673f30903066aae000000000165ff8435c2b013968000000000527fb90fec65dc24e5a00000000003ca3d5bab1c004e5980000000001b34844bfcb004e5a0000000000296b901e619804e5a00000000001c6886c6a6ae7b444e5a000000820048ffbfa0b1f319c0066aae0e00e01360be0be1367fbd62079ea6aa2010cb8e70) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P02 : WideCovered band 8931698 9245672 := wide_block_sound band profiles_RelativeWidePack6815_P02 8931698 9245672 (wideData 16 0x2bfb089ae0019aac000800000128f06640019aab8000000200cc24265f00066ab0000000000668902db50019aab800000000128f81e4f00066ab0000002000067bec273ac0066aae00000000007197432f840066aae00000000007ba3037bc40066aae000003000127d740799f70019aac000c0080001ab29bf7699a9c42066aae082000000223ff2dc38b69390819aac0000000000ecaab0af6cd80066aae0000000003e7eec0b9daa0019aac00000000010d77808ff2b40066aae0000000004f4c386f7ced0019aac03883884d83883884d88b2fb38065eeeb2a1918ab870) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P02 : WideCovered band 9245673 9559647 := wide_block_sound band profiles_RelativeWidePack6815_P02 9245673 9559647 (wideData 16 0x2eec2fcf80066ab00000000000a7f0cfb00019aab8208008200bfe42e7c80066ab000000000032bb07c3c0019aab8000000000eb7c2ede00066ab00000000003a1a079680019aab80000000010bb42ec900066aae000000000428f06de20019aab8000000000ebfc1ebd80066ab00000000001a2a0a93c0019aab80000000008d3c177e80066ab00000000001a5e0b8760019aab8000000000a8ec13eb00066ab00000000001e0e0af320019aab8000000000c9700fbf80066ab00e40e41360e40e413606bfe5a04db0864291d70a3e) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P02 : WideCovered band 9559648 10167972 := wide_block_sound band profiles_RelativeWidePack6815_P02 9559648 10167972 (wideData 16 0x208008200f964061a30002b34f8000000001bafc6fda800acd3e0000000007a2f1bc7e002b34f0000000000187391b9e4002b34f80000000001832a1aefa002b34f80000000010c2c3a2f800acd3e000000000362f17e3a002b34f8000000000dfe45ff8000acd3e0000000003fda16ff8002b34f80080000012eb85759800acd3e0000000005f8c13b62002b34f02000082001b27a09d6e002b34f830000c0003a6aa01939a400acd3e0000000001f883c0e08a9002b34f8408010200c9ecd50b73e800acd3c0e60e61360e60e6136070ee8f04ee797e292a35c2c) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P02 : WideCovered band 10167973 10795922 := wide_block_sound band profiles_RelativeWidePack6815_P02 10167973 10795922 (wideData 16 0x6e806ff3e002b34f820800820119f807186a002b34f80000000019ae406dcb6002b34f0000000001ab6806df2a002b34f8000000001bda406eabc002b34f8000000001d9f806eff2002b34f80000000008e6406fef4002b34f80000000001fa8066c20002b34f8208008200acac06bc22002b34f80000000018d7c0658fe002b34f8000000001a964065a2a002b34f0000000001bfe4065c6a002b34f8000000001e9bc065fec002b34f8000000000bcbc066cf6002b34f80000000005eb07218000acd3e0ec0ec1360ec0ec136078ce4805c6ea66293bbffe6) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P02 : WideCovered band 10795923 11737846 := wide_block_sound band profiles_RelativeWidePack6815_P02 10795923 11737846 (wideData 16 0x2080082001daae06cb5e80139a7c0000000000be9600f0df6004e69e80000000003f31e04db9e00139a7c000000000133dbc122964004e69f00000000004c79b038eab80139a7c0000000001ba8a80e0879004e69e8000000000ea39e06abfcc0139a7c20800820027e9b10b3e7cf00139a7c0000000007aea028bdf800acd3e000000000061a01e7ab800acd3e082002080428c01ef4f000acd3c0000000006e0e01db79800acd3e0000000006f9b01de08000acd3e000000000737901deea000acd3e00000000077af01e21c000acd3c0f00f01360f00f01360a1d74a069bbab2294d6aba2) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P02 : WideCovered band 11737847 12993745 := wide_block_sound band profiles_RelativeWidePack6815_P02 11737847 12993745 (wideData 16 0x9f35b1ea33800139a7c08200208026cf386b3cf2004e69e80000000009ae5e18d21e80139a7c000000000220c68531eec004e69f02080082005e2bc14b61b00139a7c0000000001b9fac46bcf0004e69e80000000006d2ee10cfbd80139a7c000000000139bf437bab6004e69f02080082004869f0d8eae80139a7c000000000163aa832393a004e69e80000000004bf5909eac900139a7c0000000000b4cf42f0fa4004e69e82080082003e6fe08f27b00139a7c000000000123b3c22ff6e004e69e80000000003d7cd06b2cd00139a7c0fc0fc1360fc0fc1360e6928c09f21a30296c66e68) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P02 : WideCovered band 12993746 13543200 := wide_block_sound band profiles_RelativeWidePack6815_P02 12993746 13543200 (wideData 7 0x820020800a1e67947aad873084e69e8c30030c00186ad2d1b5ca7902139a7c000000000624ee40a2daac80139a7a0000000004efca4075aa5b00139a7c0820020803feae0071da4880139a7a0000000003b8aec0688f1980139a7c1241241361241241361ac9b9d12c678bc298f7bdbe) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8519605 8676592 13543200 c0_RelativeWidePack6815_P02 (wide_covered_join band 8676593 8931697 13543200 c1_RelativeWidePack6815_P02 (wide_covered_join band 8931698 9245672 13543200 c2_RelativeWidePack6815_P02 (wide_covered_join band 9245673 9559647 13543200 c3_RelativeWidePack6815_P02 (wide_covered_join band 9559648 10167972 13543200 c4_RelativeWidePack6815_P02 (wide_covered_join band 10167973 10795922 13543200 c5_RelativeWidePack6815_P02 (wide_covered_join band 10795923 11737846 13543200 c6_RelativeWidePack6815_P02 (wide_covered_join band 11737847 12993745 13543200 c7_RelativeWidePack6815_P02 c8_RelativeWidePack6815_P02))))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 10)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 10≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤65)
    (hT0 : 3301≤T) (hT1 : T≤3899) (hnu : 8519605≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤29721485741079288 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R017
end MergedPart2
section MergedPart3
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R018
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨10,66,3254,3865,29906389501753189⟩
private def profiles_RelativeWidePack6815_P03 : ℕ → Profile
  | 0 => ⟨25314,190,5079⟩
  | 1 => ⟨25360,187,5079⟩
  | 2 => ⟨25449,185,5079⟩
  | 3 => ⟨25484,182,5079⟩
  | 4 => ⟨44518,250,10158⟩
  | 5 => ⟨26531,139,5079⟩
  | 6 => ⟨26596,138,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P03 : WideCovered band 8650676 8848870 := wide_block_sound band profiles_RelativeWidePack6815_P03 8650676 8848870 (wideData 16 0x3ff8ec06bcbe0019b6d8000000000ee628129effc0066db8000000000371b28071afe940066db60000000001b7f7fc198ebef20c19b6e00000000018be6e449e8a65093aea0000000003acd7007aff4013aec00000000043c93c7e7e404ebb000000000179ad857d639804ebb0000000000ceeea05b259c04eba8000000001deb0e58aefd004ebb00000000019bfcb0dbe1c404ebb00000000001cbb9b06ec931013aec00000000057ec754a2cf6013aea00000208016a92ad82f6bda7013aec0000030007fdae9d50969eb1013aec0e00e01380e00be13806086483a0708b2dee010c339b2) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P03 : WideCovered band 8848871 9165981 := wide_block_sound band profiles_RelativeWidePack6815_P03 8848871 9165981 (wideData 16 0x1879f2117fef8ac2066db600000000073be20328bf20019b6e000000000019afebc0e682a0019b6d80000000001ee383436c9fd0019b6e00000000003cb2930077b64fc0066db60000000002f0afbec7de18b50019b6e02080082001863cea12ece7e02066db60000000002fcdec0a09290019b6e00000000018c35e01833f3a0019b6d8000000000ebeab17964bc0066db8000000000466a28071c2d840066db60000000005e79b00e8a2ecc0066db600000000007ebfcf02da8feb0019b6d8208008200983a8e5125d35bc2066db80000000004e4f74766d380019b6d83803804e03803804e0e9e2be006f92eb2c010f69d64) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P03 : WideCovered band 9165982 9483092 := wide_block_sound band profiles_RelativeWidePack6815_P03 9165982 9483092 (wideData 16 0x7c342ab980066db60000000001fde0aab60019b6e00080002008b382a9d80066db600000000023db0aa7e0019b6e00000000011cf04e60019b6d8000000000be38269d80066db8000000000362b098a00019b6d8000000000f838233e00066db80800020006ea9038e00019b6d830000c001da241e9b40066db80000000004bdc14e80066db6000002080061e701bc9c0066db60000000000b0cbc7acc40066db60800000c0179beeb53ff1a7d0819b6e00000000008da0a01be9840066db60e40e41380e40e41381b796ae18e26ea2191c35832) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P03 : WideCovered band 9483093 9879480 := wide_block_sound band profiles_RelativeWidePack6815_P03 9483093 9879480 (wideData 16 0x71ea026fd000adb6e000000000077a3027a8400adb6e0000000000abd2c4b5f400adb6e1040041001e3ea93a8fe2002b6db0000000000cb3426ce80066db600000000033ff0987e0019b6e0000000000ebe02e2880066db60000000003ec90b86c0019b6e00000000010b602e0b80066db60000000003ad909dee0019b6e000000000078e41eb880066db600000000017ae0ae3a0019b6d800000000068642b7f00066db60000000001a7d0adfa0019b6e00000000006ef42a1980066db60e60e61380e60e613806fba6904e27a24212920b20) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P03 : WideCovered band 9879481 10513701 := wide_block_sound band profiles_RelativeWidePack6815_P03 9879481 10513701 (wideData 16 0x53e8018b2d800adb6e000000000079901b73f800adb6e0000000000f7a018ea9800adb6e0820020803f3f019f3a800adb6c000000000732f018a3d800adb6e0000000006f5d189e8002b6db8000000000187cf0187cd800adb6e00000000006283c5b3e000adb6c0000000002a5d0187ab000adb6e0000000001e29018aee000adb6e00000000037f9149a4002b6db80000000006aa4063a26002b6db82080082013cb442de800adb6e000000000067f244ec8000adb6e00000000006ef24474d000adb6e0ea0ea1380ea0ea138073a67b05a6be64212f6da3c) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P03 : WideCovered band 10513702 11147922 := wide_block_sound band profiles_RelativeWidePack6815_P03 10513702 11147922 (wideData 16 0x7aa901eb4f000adb6e0000000007bce01e7ed800adb6e000000000061f3407ff20002b6db80000000003ae0076e76002b6db02080082008f7407cfbe002b6db8000000001bda4073b20002b6db8000000001a92806cb3e002b6db8000000001e82c074da6002b6db0000000001c96c06bf6e002b6db80000000018e30075ffe002b6db80000000009d01de6e000adb6e0820020801e5f01ab7e000adb6e0000000006b6d01ae19000adb6e0000000006608018ada800adb6e000000000773c01aefa000adb6e0ee0ee1380ee0ee13807dfbfa05e37876214923ff6) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P03 : WideCovered band 11147923 12297448 := wide_block_sound band profiles_RelativeWidePack6815_P03 11147923 12297448 (wideData 16 0x820020800e9cb432bd3e004ebae80000000004bb7909a7f90013aebc000000000131e7c23dfea004ebae80000000003c77c08d3380013aebc08200208006e9a41e99e8004ebaf000000000049fed07d33a8013aebc0000000000fdc6c16cca0004ebae80000000004b68b04e32d0013aebc0000000000b5c780fdbec004ebaf00000000001e35802c7dd8013aebc082002080075b78123ba4004ebae830c00c3009fb5e04dfdcc013aebc20800820013ac340afcb9c8013aebc08200208016dc02aa99000adb6e0000000006e6f01d73d000adb6e0f20f21380f20f21380a9abad06caef3a215abadb0) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P03 : WideCovered band 12297449 13565890 := wide_block_sound band profiles_RelativeWidePack6815_P03 12297449 13565890 (wideData 16 0xc30030c004db7afd42aa79084ebae8000000001bf6ae02aaee22004ebaf02080082014fa1d01fb2bb2004ebae80000000012bb7f01c34974004ebaf00000000010d7bb01af4fb2004ebaf0208008200beb9b0193bb7a004ebaf0000000000bf3291ed38d8013aeba000000000327e3c7f1962004ebaf0208008200886ad1a8e8a0013aeba000000000226fb453297e004ebaf00000000007eef913af2c8013aeba0000000001fdd244e9b34004ebaf02080082004e2c911bbc80013aebc00000000017aaa4375c68004ebaf00000000005dfac0d8bcf8013aeba1201201381201201381229edb0be3cd2e217ceda6c) (by decide +kernel)
private theorem c8_RelativeWidePack6815_P03 : WideCovered band 13565891 13724445 := wide_block_sound band profiles_RelativeWidePack6815_P03 13565891 13724445 (wideData 2 0x11e25914870f4213aeba1341341381341341381a3a2eb18da58aa29a83ade0) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8650676 8848870 13724445 c0_RelativeWidePack6815_P03 (wide_covered_join band 8848871 9165981 13724445 c1_RelativeWidePack6815_P03 (wide_covered_join band 9165982 9483092 13724445 c2_RelativeWidePack6815_P03 (wide_covered_join band 9483093 9879480 13724445 c3_RelativeWidePack6815_P03 (wide_covered_join band 9879481 10513701 13724445 c4_RelativeWidePack6815_P03 (wide_covered_join band 10513702 11147922 13724445 c5_RelativeWidePack6815_P03 (wide_covered_join band 11147923 12297448 13724445 c6_RelativeWidePack6815_P03 (wide_covered_join band 12297449 13565890 13724445 c7_RelativeWidePack6815_P03 c8_RelativeWidePack6815_P03))))))))
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
private def profiles_RelativeWidePack6815_P03 : ℕ → Profile
  | 0 => ⟨25314,190,5079⟩
  | 1 => ⟨25360,187,5079⟩
  | 2 => ⟨25449,185,5079⟩
  | 3 => ⟨25484,182,5079⟩
  | 4 => ⟨44518,250,10158⟩
  | 5 => ⟨26531,139,5079⟩
  | 6 => ⟨26596,138,5079⟩
  | 7 => ⟨26584,136,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P03 : WideCovered band 8781747 9101993 := wide_block_sound band profiles_RelativeWidePack6815_P03 8781747 9101993 (wideData 16 0xa6a7ff19b69d800678be00000000006cbe2f83eb5cb10019e2f82080082008e649ef06de64f420678be0000000004aae247a59f40019e38000000000089f6a10ab9f400678be000000000523d28421ebe0019e3800000000009e37c01cbdc6f0019e2f8000000001b977c12ee3dc00678e0000000000522cac166b72cc00678be0820020801e0dfeb44c7eca10819e380000000000ebeac13f78c000678be00000000033eeec268eb00019e380000000000bae4804c3ebc00678be000000000270fe85f9a670019e3800000000007925b01da1a3f0019e2f83803804e83803804e8ca2a93c071c74ce0010e66fa4) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P03 : WideCovered band 9101994 9422239 := wide_block_sound band profiles_RelativeWidePack6815_P03 9101994 9422239 (wideData 16 0x800000079b4365b000678be0000000803edc03fb00019e2f80000000012bec0acf800678be0000000005b5a0bf800678e000000000073be02d710019e2f800000000019b1e07b6b0019e380000008001bfa8173b000678be0000000000aada0632dc00678e0000003080121e24077e730019e2f82000083005db28754f8ae7b420678be0000000001ac92c0e4cbd0019e2f80000000006ea1808e3dcc00678e00000000001f2e7446aefd0019e2f8000000001df33f468628bd0819e3800000000019d2b805e7b8c00678be0e40e413a0e40e413a1a4de691fd2b9b8111b38b72) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P03 : WideCovered band 9422240 9742486 := wide_block_sound band profiles_RelativeWidePack6815_P03 9422240 9742486 (wideData 16 0x2080082003838371e000678be0000000002f4d09b2a0019e2f8000000000ca602678800678be00000000033fe098660019e380000000000de7c23ba000678be000000000423e0d97e0019e380000000000ff24233f800678be000000000464b08b660019e3800000000006f34224e000678be0000000001e9907eb60019e3800000000005cbc2f69000678be0000000001e8b098ae0019e3800000000008f341e1a000678be000000000279f06ca20019e380000000000afb017ed000678be0e60e613a0e60e613a06ab7ba04d7fef0212829f3e) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P03 : WideCovered band 9742487 10382979 := wide_block_sound band profiles_RelativeWidePack6815_P03 9742487 10382979 (wideData 16 0x208008200ad74060d68002ba5f0000000001bfec0639b2002ba5f8000000001baa46689000ae97e0000000007a4d189e8002ba5f8000000000196df018e19000ae97e000000000437c16e30002ba5f8000000000daa4566c000ae97e0000000001ada018ed9000ae97e00000000042d812e32002ba5f00000000014f303f0c000ae97e08200208047591efb6002ba5f80000000001afe9038bc002ba5f80000000001e66f07eb6002ba5f000000000029f0805a7d002ba5f830000c0008e2aa03efcf400ae97e0ec0ea13a0ec0ea13a06296bb05af5da4212d62bea) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P03 : WideCovered band 10382980 11023472 := wide_block_sound band profiles_RelativeWidePack6815_P03 10382980 11023472 (wideData 16 0x7b7c0a2c36002ba5f02080082005b6807696e002ba5f800000000188e006cfe4002ba5f8000000001be70075dec002ba5f8000000001a83006d9ac002ba5f8000000001b9f006daba002ba5f8000000001ba60077d68002ba5f8000000001ab01bb3c800ae97e08200208077006ec78002ba5f00000000019eb406ca7a002ba5f80000000018aa0063dbe002ba5f8000000001bd68069be8002ba5f8000000001ceb4067b7a002ba5f0000000001a87c063ee2002ba5f80000000001c01be9c000ae97e0ee0ee13a0ee0ee13a077b6bf05cadc24213f25ba4) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P03 : WideCovered band 11023473 12064273 := wide_block_sound band profiles_RelativeWidePack6815_P03 11023473 12064273 (wideData 16 0x137c3426cf72004f2bf0208008200cde01faeb2004f2be80000000003ae6805cbdc0013cafc0000000000fc83c17dbfc004f2be80000000004afbd05b2ae8013cafc00000000012edf0079a38004f2be800000000048a3c02f3788013cafc0000000001619600f4d8013cafc0000000007b3ee44bbafd004f2bf08200208017f3cd43966eea004f2be82080082019d42a77d000ae97e0000000006edf01ee0d800ae97e0000000006b7901de18000ae97c0000000007ae802827d800ae97e00000000072bb01defa000ae97e0f20f213a0f20f213a0a18b1906aa49622158e8b3e) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P03 : WideCovered band 12064274 13345259 := wide_block_sound band profiles_RelativeWidePack6815_P03 12064274 13345259 (wideData 16 0x11cbb901c6cfe8004f2bf00000000010af8c01b78d7e004f2be8208008200ce6fd01a7bce2004f2bf0000000000bf2b90183abe4004f2be80000000009fe9e1b82aa0013cafc0000000002aece0729828004f2be82080082006bbdf17ae8c8013cafc0000000001bf8ec4a5822004f2bf00000000007ca2813d7bd0013cafc082002080138da44aad2e004f2be80000000005e6680ed60b8013cafc0000000001609b02fdbba004f2be80000000005dbbb0dce1a8013cafc0820020800ad87c325fb8004f2be80000000003ea5e0896a88013cafc0fe0fe13a0fe0fe13a0ee8e9f0adb5f22217967b3e) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P03 : WideCovered band 13345260 13905690 := wide_block_sound band profiles_RelativeWidePack6815_P03 13345260 13905690 (wideData 7 0x36cbf4060ab3bc013cafa08200208007bd24943ebfaad084f2bf030c00c3001ae68f87769ad004f2be8208008200ef750a28b5a4213cafc30c00c3000f9ce2b5c93ea8213cafa000000000734b3c0b1da9c0013cafc12812813a12812813a222afed18971a32219cedab2) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8781747 9101993 13905690 c0_RelativeWidePack6815_P03 (wide_covered_join band 9101994 9422239 13905690 c1_RelativeWidePack6815_P03 (wide_covered_join band 9422240 9742486 13905690 c2_RelativeWidePack6815_P03 (wide_covered_join band 9742487 10382979 13905690 c3_RelativeWidePack6815_P03 (wide_covered_join band 10382980 11023472 13905690 c4_RelativeWidePack6815_P03 (wide_covered_join band 11023473 12064273 13905690 c5_RelativeWidePack6815_P03 (wide_covered_join band 12064274 13345259 13905690 c6_RelativeWidePack6815_P03 c7_RelativeWidePack6815_P03)))))))
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
private def profiles_RelativeWidePack6815_P03 : ℕ → Profile
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
private theorem c0_RelativeWidePack6815_P03 : WideCovered band 8912818 9236200 := wide_block_sound band profiles_RelativeWidePack6815_P03 8912818 9236200 (wideData 16 0x1d2990492cbc0067be6000000000075be0271dfd0019ef980000000001e25f11cbdb40067be600000000036afe51e0a27cc2067be8000000000262aa87b193a0019ef98000000000896dd1af6fd40067be80000000003fdb7432ab7e0019ef980000000018dfa903c26c310019efa02080082002e21dbd0a4abd942067be60000000000f893c268c260019efa00000000004ee9e0eef9f00067be6000000000161ee01bf9360019efa00000000005c2ee049e2b40067be60000000001af838574d3d0019efa000000000078fe802b62daf0019ef983883884f03883884f02a66d78067b65eea011867aaa) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P03 : WideCovered band 9236201 9559582 := wide_block_sound band profiles_RelativeWidePack6815_P03 9236201 9559582 (wideData 16 0x2080082001b312b6880067be60000000001b790e800067be6000000000221b05a680019ef980000000008be00a0d40067be80000000002a7f039e40019ef98000000000b9601769c0067be8000000000377d04a40067be600000000042aa029b90019efa00000000001c3ebf14ab9f8d42067be60000000000bcdb47fdc40067be60000000000eca681b09230019ef980000000002c33a01a708650019efa02080082015a3ca48fbad02067be6000000000075e28167cee0019efa00000000001d38f02eb8c00067be60e40e413c0e40e413c0a597fe18861ff6111d3ef78) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P03 : WideCovered band 9559583 9882965 := wide_block_sound band profiles_RelativeWidePack6815_P03 9559583 9882965 (wideData 16 0x4b6033c900067be6000000000127d08cac0019ef980000000004fac33af80067be6000000000167d0cbec0019efa000000000059fc230e00067be60000000001a3b0cf3c0019efa000000000069241f4e80067be60000000001e7a0cf6a0019efa00000000007b681e2980067be600000000023a80cfe40019efa00000000004bf81abe00067be6000000000129a4d82e0019efa00000000017e488300019ef9800000000038292b0e00067be800000000017ff4db720019ef983a03a04f03a03a04f0dbaeb04da8da8212a36c64) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P03 : WideCovered band 9882966 10529730 := wide_block_sound band profiles_RelativeWidePack6815_P03 9882966 10529730 (wideData 16 0x23791ff3e002bbeb00000000009bf07f0d000aefae0000000002aec1f8f6002bbeb8000000000bdbc7b8e800aefae00000000036c81eb3c002bbeb8000000000adf07a38800aefae0000000002b4e5de7e002bbeb82080082005ff5063e66002bbeb8000000000b9e04ece800aefac00000000033890ed64002bbeb8000000000f9742e99000aefae0000000004b4f06ce0002bbeb80000000017f68329002bbeb0000000000182ce0ba77002bbeb80000000001bec81ebb3002bbeb83b03b04f03b03b04f0b93cf05ab5932212f75cf8) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P03 : WideCovered band 10529731 11176494 := wide_block_sound band profiles_RelativeWidePack6815_P03 10529731 11176494 (wideData 16 0x2080082001e780778e4002bbeb00000000008bb0073eba002bbeb80000000008df0073f7e002bbeb80000000009d28079ca0002bbeb80000000009fb407996a002bbeb0000000000a864075ce0002bbeb800000000059a5076c28002bbeb82080082004d7406bd7e002bbeb800000000088ac06a830002bbeb00000000008bf006a864002bbeb80000000008fec06a932002bbeb80000000009ce006ab72002bbeb8000000000aaf406aef8002bbeb00000000001da8073a7e002bbeb820800820068a906ad36002bbeb83b83b84f03b83b84f11fab905cfad78214964eb2) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P03 : WideCovered band 11176495 12227487 := wide_block_sound band profiles_RelativeWidePack6815_P03 11176495 12227487 (wideData 16 0x820020804b4c0bca2c8013df3c000000000065e7c1e4fa2004f7ce800000000019eaf06cb498013df3c00000000006ab7417e82c004f7ce80000000001cbeb06862a8013df3c000000000376806c3ed8013df3a08200208013a802b38a0013df3c000000000069e741b19c013df3c0c30030c0436ea02f8c7b004f7cf0a28028a00caa4843821baa004f7ce80000000009e280a49fc002bbeb80000000009b7007f9e2002bbeb80000000009d3c07fab8002bbeb00000000009fa007fd7a002bbeb8000000000aa680a09a4002bbeb83d03d04f03d03d04f14e76a06b36c24215b3486a) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P03 : WideCovered band 12227488 13521017 := wide_block_sound band profiles_RelativeWidePack6815_P03 12227488 13521017 (wideData 16 0x1eede80a2ca5a8013df3c0000000001e4cbc07fdb2e8013df3a08200208012ece006e8e6d8013df3c00000000012eda8066faec8013df3a0000000001238e4063baac8013df3c0820020800bdbec7efc2e004f7ce80000000003a6281c975a0013df3c0000000000b9bbc5ec964004f7cf00000000002d7a816832c0013df3c08200208006de3447fabe004f7ce80000000002867a10a22c8013df3c0000000000a6ff8473ca6004f7ce82080082001867f0eba3c8013df3c000000000070c242e79fe004f7ce80000000001c2de0ad6fb8013df3c12012013c12012013c0648f6c0b8f6bec217be7dba) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P03 : WideCovered band 13521018 14086935 := wide_block_sound band profiles_RelativeWidePack6815_P03 13521018 14086935 (wideData 7 0x13ea345b0a3f004f7ce82080082015d768458309ef084f7cf00000000005ffdf11eb3ac013df3a000000000326f644fbd6b084f7cf02080082014d38d41c60a3f084f7ce8000000000bcb190fba3b4013df3c13413413c13413413c078cb4e1bfa5a36299fa692c) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8912818 9236200 14086935 c0_RelativeWidePack6815_P03 (wide_covered_join band 9236201 9559582 14086935 c1_RelativeWidePack6815_P03 (wide_covered_join band 9559583 9882965 14086935 c2_RelativeWidePack6815_P03 (wide_covered_join band 9882966 10529730 14086935 c3_RelativeWidePack6815_P03 (wide_covered_join band 10529731 11176494 14086935 c4_RelativeWidePack6815_P03 (wide_covered_join band 11176495 12227487 14086935 c5_RelativeWidePack6815_P03 (wide_covered_join band 12227488 13521017 14086935 c6_RelativeWidePack6815_P03 c7_RelativeWidePack6815_P03)))))))
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
private def profiles_RelativeWidePack6815_P03 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨33072,8,10160⟩
  | 2 => ⟨40768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P03 : WideCovered band 6029255 9483627 := wide_block_sound band profiles_RelativeWidePack6815_P03 6029255 9483627 (wideData 16 0x7db01df6f800a0efe0000000000a6c02876e800a0efe082002080073941d29a000a0efe000000000070901b21f800a0efe000000000078f01da6e800a0efe000000000074801b609800a0efe000000000076a01b6ef000a0efe0000000000a1a01e6fb800a0f2000000000007d901bf59800a0efe0000000000a1a01c3b8000a0efe0820020800abe41cf5f800a0efe3cf00f3c013e9e81bd8ed9820a0efe186006180060e02f38902223bfa34d00d3400b80ad0109bfc8e38038e001a02b80060b7f903903903c83903903c8bd15e3800fc77e3c) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P03 : WideCovered band 9483628 10280790 := wide_block_sound band profiles_RelativeWidePack6815_P03 9483628 10280790 (wideData 15 0x1ffd06c72c00121dfc000000000264806d2ce80121dfc082002080135f43a37c00121dfc0000000001a7e03ee3d00121dfe0000000001e5a03ab0d80121dfc00000000023bf02c70a00121dfc0000000002a0802da1a40121dfc00000000052e903fbf840121dfe1860061804fd0ade2e980121dfc0820020806ed07f9f600283bf80000000001cfc074c3e00283bf80000000001f2c07ede400283bf80000000001db8075ae200283bf80000000001e2c075e6c00283bf83883883c83883883c85bb2807d2fcb211293bcb6) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6029255 9483627 10280790 c0_RelativeWidePack6815_P03 c1_RelativeWidePack6815_P03)
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
private def profiles_RelativeWidePack6815_P03 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨41018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P03 : WideCovered band 6160326 9319394 := wide_block_sound band profiles_RelativeWidePack6815_P03 6160326 9319394 (wideData 16 0xf0801afbe000a1d2e0000000000f5901b2da800a1d2e0000000000fbd01b659800a1d2e000000000123d01ba58000a1d2e00000000012d901bebd800a1d2e0000000000b7d01c618000a1d30082002080136d41a3b8800a1d2e0000000000f6c01b2ad800a1d2e0000000000f0a01931f800a1d2e0000000000f8801961d800a1d2e000000000121e01976a000a1d2e00000000012df019b48000a1d2e145005140278c2c1b18a7c020a1d2e00000000053c6a59020a1d304d30134c04f8360c02060ea7903d03d03d03d03d03d19815c2400fee8e38) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P03 : WideCovered band 9319395 9924322 := wide_block_sound band profiles_RelativeWidePack6815_P03 9319395 9924322 (wideData 16 0x1aafb81ee9e50048e8f08200208005c68e42b24bfe0048e8f0000000000493007df3a002874b80000000004e740a9c32002874b80000000004b7c07ff28002874b80000000004cec0a192e002874c02080082002b7107be36002874b80000000003c6c073b22002874b80000000003d60073e2c002874b80000000003e300749fa002874b80000000003f68074fa4002874b800000000048b8075eae002874b80000000004a68076f62002874b800000000038e80a4af8002874c02080082002b3d06dfe4002874b83803803d03803803d0b8be907929bb8191ebbcb2) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P03 : WideCovered band 9924323 10462035 := wide_block_sound band profiles_RelativeWidePack6815_P03 9924323 10462035 (wideData 8 0x208008200482c235da20048e8f0000000000cea4161b6c0048e8f0000000000dbac134c280048e8f0000000000edfc1289660048e8f000000000118600f89f60048e8f00000000019ce41a2b600048e8f0000000001dff40b4a6a0048e8f03b03b03d03b03b03d0d9f380a86582619387ade2) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6160326 9319394 10462035 c0_RelativeWidePack6815_P03 (wide_covered_join band 9319395 9924322 10462035 c1_RelativeWidePack6815_P03 c2_RelativeWidePack6815_P03))
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
private def profiles_RelativeWidePack6815_P03 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨33072,8,10160⟩
  | 4 => ⟨41018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P03 : WideCovered band 6291397 9113322 := wide_block_sound band profiles_RelativeWidePack6815_P03 6291397 9113322 (wideData 16 0x2080082007c6d06bb600028acf80000000004ff0062ca00028acf80000000004ff07afb800a2b6000000000017ce019a48800a2b3e0000000001ace019bed000a2b3e0000000001e0e01a22b800a2b3e0000000001faa01a72d000a2b3e00000000022a901af3e800a2b3e000000000433a5e9e40028acf82080082005bac76bd000a2b3e00000000017ed1dbbc0028ad8071c01c700e9748069afaf20828acf871c01c7002834073d7e0828acf8514014500182c67af82124e7c0000000003fc33dc82229cfa0ec0ec0f60ec0ec0f606ce1592a010939e34) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P03 : WideCovered band 9113323 9657307 := wide_block_sound band profiles_RelativeWidePack6815_P03 9113323 9657307 (wideData 16 0x20800820038ed0a392e0028acf80000000005c38074e280028acf80000000005da00759fa0028ad800000000005f28075efe0028acf80000000005cb406fc740028acf800000000068f4073fae0028acf80000000006da8078cf20028acf800000000078e007a9bc0028acf82080082006a2d074fe60028acf800000000059fc06ce6c0028acf80000000005be406daba0028acf80000000004fe8063d660028acf8000000000687006ec320028acf80000000006ba806fd640028acf80000000006fa00719240028acf83803803d83803803d8fc20a06e21ebc211ba9ef2) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P03 : WideCovered band 9657308 10575282 := wide_block_sound band profiles_RelativeWidePack6815_P03 9657308 10575282 (wideData 16 0x6b1907e38b80124e7c00000000072f807e3e800124e7c0000000006a9d05c78a00124e7c0820020801b7b45e77e80124e7c0000000005b180583fe80124e7c0000000005efa03f6bf80124e7c0000000006a2902b7ca00124e7e000000000066d2c0e5e60004939f00000000001ee6e01dbfc80124e7c0000000000ecfe82a7bef004939f08200208002eeea42cabc7e004939f80000000006a3c07eff40028acf80000000006bac07fcfc0028acf80000000006d340a0bae0028acf80000000006870076aa40028acf83903903d83903903d91eefa07c7fdb8212bf0ab4) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P03 : WideCovered band 10575283 10643280 := wide_block_sound band profiles_RelativeWidePack6815_P03 10575283 10643280 (wideData 1 0x3b83b83d83b83b83d9bc2980bce4e60214a73d60) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6291397 9113322 10643280 c0_RelativeWidePack6815_P03 (wide_covered_join band 9113323 9657307 10643280 c1_RelativeWidePack6815_P03 (wide_covered_join band 9657308 10575282 10643280 c2_RelativeWidePack6815_P03 c3_RelativeWidePack6815_P03)))
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
end MergedPart3
