import ProximityPrize.SubmissionLower.RelativeWideBlocks6815
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R000
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨10,49,4336,4362,8672446898194066⟩
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨41268,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 6422469 9719978 := wide_block_sound band profiles 6422469 9719978 (wideData 16 0x131911c22004839f00000000007ca406f8ab004839f86180186003869070fe0d80120e7c000000000170072dee00282cf82080082002c01a288800a0b3e0000000004b8061de400282cf80000000015c01a28c000a0b3e0000000005ac0699f000282cf80000000017b01a7f9800a0b3e00000000063006af2800282cf80000000019e01afff000a0b3e1c70071c00a9e201aed2eb820a0b3e34d00d3400e46c00a0b3e1860061802a0067fe4088873e8b2c02cb001d019400609af903d83d83d83d83d83d86815fb6010a39e34) (by decide +kernel)
private theorem c1 : WideCovered band 9719979 10643280 := wide_block_sound band profiles 9719979 10643280 (wideData 14 0x2080082001a2c1afd38004839f00000000002c6016aaf8004839f00000000002d2016a93e004839f00000000002c6c137c7a004839f00000000002e3413c920004839f02080082004130cb8004839f00000000002a64120aa4004839f00000000002be40ffe34004839f80000000002a740b78f6004839f0000000000393c0fdfe6004839f02080082001ca50edce6004839f00000000002a2c0aedf8004839f80000000002d3c0a5f64004839f03a03a03d83a03a03d82eb6e08ae2e6a112d69930) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6422469 9719978 10643280 c0 c1)
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
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨33072,8,10160⟩
  | 4 => ⟨41518,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 6553540 9456476 := wide_block_sound band profiles 6553540 9456476 (wideData 16 0x82002080073a0182ee800a196e0000000000a1f019eec000a196e0000000000a4c01a21e800a196e00000000007f8018698800a196e0000000000aad01a6ec800a196e0000000000aee01ab19000a196e0000000000aa9018eb8800a19700820020800b2a41ab9d800a196e00000000007981dcb8002865b80000000001f7c7fcf800a196e0000000000a49018bfc000a196e1c70071c01b7ce81a2964c820a196e0c30030c07a0074d2e082865b871c01c700fb1aaa20848aaf8d34034d00ac0d92a090a6bc83e03e03e03e03e03e16c15d2a010caae30) (by decide +kernel)
private theorem c1 : WideCovered band 9456477 10357387 := wide_block_sound band profiles 9456477 10357387 (wideData 16 0x9aa4168f720048aaf800000000088241259740048aaf02080082002d2d0e082e0048aaf00000000006ef80beab20048aaf00000000008ba40ed8bc0048aaf00000000008eec0a6dec0048aaf0000000000baa40778240048aaf00000000012cfc0e9c340048aaf0000000001d92c0b18c0122abe0000000000aba6416aeb10048aaf082002080038a2941d209f20048aaf000000000029b806bfb0002865b80000000002afc06ef6e002865b800000000029a4067f72002865b80000000002ca8070e2c002865b83883883e03883883e07abba06cfceea2128e6ee6) (by decide +kernel)
private theorem c2 : WideCovered band 10357388 10824525 := wide_block_sound band profiles 10357388 10824525 (wideData 7 0x2080082006b381b4ce20048aaf000000000089bc171da80048aaf00000000008bf4170bec0048aaf000000000099b8178f740048aaf02080082001f24171ce40048aaf00000000006ffc125d6a0048aaf03b03b03e03b03b03e0a9b6b099a78fa213f27cf2) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6553540 9456476 10824525 c0 (wide_covered_join band 9456477 10357387 10824525 c1 c2))
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
private def profiles : ℕ → Profile
  | 0 => ⟨16536,4,5080⟩
  | 1 => ⟨41768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 6684611 9351576 := wide_block_sound band profiles 6684611 9351576 (wideData 16 0xf1e0196e8800a1f7e0000000000ed9018329000a1f7e000000000122801a61e800a1f7e0000000000fb80187ff000a1f7e000000000123f018b7e800a1f7e082002080169841ab9d000a1f7e0000000000bed1abb200287df80000000003c64061f2c00287df80000000003aa06bff800a1f7e0000000000f1a1b97600287df80000000004a7c06497a00287df800000000049a0730a000a1f7e000000000165c019e0b800a1f7e082002080236c5ece800287df8924024900ac7bd05e3e83408287e803903903e83903903e82b2007caa6010efbe2c) (by decide +kernel)
private theorem c1 : WideCovered band 9351577 10060517 := wide_block_sound band profiles 9351577 10060517 (wideData 16 0x33ed0283ae00123efc0000000003fdc01c2e900123efe000000000571c148660048fbf0000000001dcb01289a50048fbf06180186001921074a3be00123efc000000000134c01de1d800a1f7e0820020800e0b41a3be800a1f7e0000000000e7901968b000a1f7e0000000000f7f01b35d800a1f7e0000000000eea019a1a800a1f7e0000000000ff801b60d000a1f7e0000000000fab01a30c000a1f7e0000000000fec01a229800a1f7e0820020800e6d41c688000a1f7e0000000000bff1fcf400287e803803803e83803803e8bdef906ab3b76091f3adee) (by decide +kernel)
private theorem c2 : WideCovered band 10060518 11005770 := wide_block_sound band profiles 10060518 11005770 (wideData 14 0x108641bdc300048fbf00000000010b601bcef00048fbf0000000001186c1beaee0048fbf02080082003a24164a6c0048fbf0000000000dc3816be360048fbf0000000000e8ec16bbba0048fbf0000000000f82816cee80048fbf02080082002a3816dd240048fbf80000000009eec0e1ab00048fbf0000000000cbac0fe8660048fbf0000000000dd700fccf20048fbf0000000000fd280fcb6c0048fbf000000000119740bece00048fbf03b03b03e83b03b03e8ec2ff08bb0dac093aa5aa6) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6684611 9351576 11005770 c0 (wide_covered_join band 9351577 10060517 11005770 c1 c2))
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
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨33072,8,10160⟩
  | 4 => ⟨41768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 6815682 9069651 := wide_block_sound band profiles 6815682 9069651 (wideData 16 0x4eb06fbc800a2dae00000000016f91fe3a0028b6c000000000068680628380028b6b800000000069b477de000a2dae0000000001bce1ef620028b6b80000000008f250609680028b6b82080082014d17f700028b6b80000000004ef457ce800a2dae00000000016ab15fe80028b6b80000000006cec7e0f800a2dae1c7005140376e6c17193de820a2dae0c30051400a6c01cee8020a2dae0c30030c0063a19de008496cf00000000011c0cef0088ab9e175c05d7008a1b00186b9e20fc0fc0fc0fc0fc0fc068a1583c00f8b6aa6) (by decide +kernel)
private theorem c1 : WideCovered band 9069652 9616068 := wide_block_sound band profiles 9069652 9616068 (wideData 16 0x1398019b7c000a2dae00000000013ed019e4c800a2db00000000001658019f69800a2dae0000000001a1e01c2ee000a2dae000000000176f01a738800a2dae0000000000e5b41ab7c000a2dae0820020800aca01874b800a2dae00000000012fd0183db800a2dae000000000136a018688000a2dae00000000013df01875c800a2dae000000000178901a3ab800a2dae000000000177c0193fa000a2dae0000000001a190192da000a2dae082002080228941937e800a2dae000000000129c1bbe20028b6b82f82f83f02f82f83f0f9b6d05fad8bc211af4ef4) (by decide +kernel)
private theorem c2 : WideCovered band 9616069 10572297 := wide_block_sound band profiles 9616069 10572297 (wideData 16 0x13cf0132c3400496cf02080082003abc17dd3400496cf0000000000f8ec0ea83200496cf0000000001097c0e3daa00496cf00000000013fa80f68e400496cf00000000016cf80ead7800496cf0000000001ac380aebba00496cf80000000010f2c07cdbe00496cf02080082013ea90b6d2c00496cf00000000016c743b0840125b3c0c30000002e78363f7cb500496cf08200186009becfc2866db200496cf00000000006af807792a0028b6b80000000005fe40709b00028b6b820800820048a506bde00028b6b83883883f03883883f1183ce06c65e3e212b608b6) (by decide +kernel)
private theorem c3 : WideCovered band 10572298 11187015 := wide_block_sound band profiles 10572298 11187015 (wideData 9 0x19d64221c2600496cf0000000001a92c1fff7600496cf02080082009ea41b8d6200496cf00000000017d281e9c3800496cf00000000015b341a68fe00496cf00000000016a241a5db000496cf02080082007c681b1a7e00496cf00000000011cb013782e00496cf03b83b83f03b83b83f188a2d09aae9ae214a6eb6e) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6815682 9069651 11187015 c0 (wide_covered_join band 9069652 9616068 11187015 c1 (wide_covered_join band 9616069 10572297 11187015 c2 c3)))
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
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨42018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 6946753 8950248 := wide_block_sound band profiles 6946753 8950248 (wideData 16 0x89ac728d000a3bbe000000000226b12eaa0028eef8000000000abb076fa000a3bbe0000000001a5b5efb80028eef82080082008cf57208000a3bbe0000000001e2f14a7c0028eef80000000007f7c5249800a3bbe000000000261913fb40028eef8000000000ac244f9c800a3bbe000000000327f10db20028eef8000000000eabc1fdf800a3bbe1450030c03edee816babad820a3bbe082002080124902b29f82126f7c0c30051405b8336f0222def86590196401606c043bdf20f80f80fe0f80f80fe076b14df400faeeea2) (by decide +kernel)
private theorem c1 : WideCovered band 8950249 9502937 := wide_block_sound band profiles 8950249 9502937 (wideData 16 0x1b4d0193fd800a3bbe0000000001e7e019fd9800a3bbe0000000001f7901a60c000a3bbe00000000022bf41aabd800a3bbe082002080176e1feec0028eef80000000005ffc0609ba0028eef80000000006ab4060d7a0028eef80000000006df0061a6e0028eef80000000006af4671c800a3bbe0000000001f99018b2e800a3be0000000000230d018f9f800a3bbe08200208036be41964d800a3bbe00000000017bd1aca40028eef80000000006a3c6ba8000a3bbe0000000001b991b9620028eef82f82f83f82f82f83f92965e05de4ca819192cb6e) (by decide +kernel)
private theorem c2 : WideCovered band 9502938 10262883 := wide_block_sound band profiles 9502938 10262883 (wideData 16 0x628f02c3fb00126f7c000000000760901ff9e00126f7c0000000000618a44a0940126f7c000000000079f344e8cc0126f7c0000000000f2aec160c790049bdf08200208003ae0841ee5c7e0049bdf00000000006970068f320028eef800000000069b0067e600028eef80000000006f3406cd7c0028eef8000000000797006dba80028eef80000000007c2006eb2e0028eef8000000000383006fc740028eef82080082001eed06986c0028eef8000000000683c065c760028eef80000000006a3006682a0028eef83883883f83883883f94b6cc069fdc621929a3f30) (by decide +kernel)
private theorem c3 : WideCovered band 10262884 11368260 := wide_block_sound band profiles 10262884 11368260 (wideData 16 0x62d60231bf20049bdf02080082014ff826193c0049bdf0000000001fbac1fa82c0049bdf0000000001ff641f7ee00049bdf0000000001eb241e0b320049bdf0208008200bc3c1b6f380049bdf0000000001a93c1a0cfa0049bdf0000000001b87417fcf80049bdf0000000001cbfc1a0c780049bdf0000000000deac13987e0049bdf0208008200bcf8135e6c0049bdf00000000017d3012ea200049bdf00000000019de412d9f20049bdf00000000018b740bfa620049bdf0000000000c96c12a9e20049bdf03b83b83f83b83b83f9ada8d08c2faf6193db3d24) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6946753 8950248 11368260 c0 (wide_covered_join band 8950249 9502937 11368260 c1 (wide_covered_join band 9502938 10262883 11368260 c2 c3)))
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
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨2984,24,635⟩
  | 4 => ⟨42268,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 7077824 8824574 := wide_block_sound band profiles 7077824 8824574 (wideData 16 0x109f06f3c800a49ee0000000001af80ec66002927b8000000000eae57758000a49ee08200208026f95bab0002927b8000000000ad7017b9000a49ee0000000003a1c0ef64002927b80000000010bb41e3e800a49ee000000000539c02a38002927b8000000001ce641a3e800a49ee000000000066e785e69400a49ee00000000007ffe447ed400a49ee1040041000a6c6bb4fd6e9a3082927b871c01c7002d259bc53faedd020a49ee0000000000e9901caac020a49ee0820020800adf01977f82230f780bc0bc1200bc0bc1200a5a14ba000fd27aa0) (by decide +kernel)
private theorem c1 : WideCovered band 8824575 9383535 := wide_block_sound band profiles 8824575 9383535 (wideData 16 0x79e0068f74002927b8208008200ba21060cf6002927c00000000007a707bfc000a49ee0000000001b9f17eaa002927b800000000089fc7f4c800a49ee00000000023cf0182de000a49ee000000000234918a62002927b8000000000ad740628a4002927b80000000005c20063cf6002927b8000000000a9f16aa8000a49ee0820020800a4b1c970002927b80000000008b3863ac800a49ee00000000022ca11de4002927b8000000000ab6467d9000a49ee0000000002b390feee002927b82f82f84802f82f84814a7a905c62c32210f37dea) (by decide +kernel)
private theorem c2 : WideCovered band 9383536 9942495 := wide_block_sound band profiles 9383536 9942495 (wideData 16 0x8b7406bbf2002927b80000000009ebc074cea002927b82080082005e79071e2a002927b80000000006eb0063ab0002927b80000000007fac06ad6c002927b80000000008a2006ba76002927b80000000007d3c064a6c002927b8000000000982c06ce7e002927b80000000008ebc068c26002927b80000000003d7506c8e6002927b82080082002ee4066bee002927b80000000006d38771a800a49ee0000000001fcb019639800a49ee00000000022ab0197aa800a49ee0000000001fad1ebfc002927b8388388480388388481793ef05ff39f0211fbbbac) (by decide +kernel)
private theorem c3 : WideCovered band 9942496 10990545 := wide_block_sound band profiles 9942496 10990545 (wideData 16 0x19da01a8df6004a2ef0208008200d9b013eef8004a2ef00000000001835f05e3f900128bbc0000000007a1d04ce2e00128bbc000000000060e30130f3e004a2ef0208008200592912ccac004a2ef0000000001d964126e34004a2ef0000000001ba780bae74004a2ef0000000001fafc0af8a0004a2ef000000000019b1801f79f80128bbc00000000007cbf00ec9e2004a2ef00000000002bff910b00128bbc00000000017ec6412bc39004a2ef08200208006dfd841df9c62004a2ef000000000088ec06cc38002927b8398398480398398481aa3db06d24a2621383f96c) (by decide +kernel)
private theorem c4 : WideCovered band 10990546 11549505 := wide_block_sound band profiles 10990546 11549505 (wideData 8 0x208008201fef02add32004a2ef00000000001a29c08bb8a00128bbc000000000068a60229868004a2ef00000000001b7fe09bf3800128bbc08200208052e908834880128bbc000000000060ce01acce8004a2ef000000000018fba06fb5800128bbc0f20f21200f20f2120067a25a09f648682158e2afe) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7077824 8824574 11549505 c0 (wide_covered_join band 8824575 9383535 11549505 c1 (wide_covered_join band 9383536 9942495 11549505 c2 (wide_covered_join band 9942496 10990545 11549505 c3 c4))))
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
