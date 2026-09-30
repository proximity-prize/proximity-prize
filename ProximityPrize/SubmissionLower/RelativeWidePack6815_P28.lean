import ProximityPrize.SubmissionLower.RelativeWideBlocks6815
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R168
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨8,67,3777,4012,21418250682550398⟩
private def profiles : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨44518,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 8781749 9358331 := wide_block_sound band profiles 8781749 9358331 (wideData 16 0x18f82a6d00064aae0000000000e016e880064aae0000000000f2b4ab3600192ac00000000006904ffe00192ab80000000004afd2b4c00064ab00000000002f812ea80064aae082002080076e498e800192ac00000000004cbc079800064aae00000000016dd05a2800192ac00000000005be84ea00192ab8410a104282da0ca557ca788c2064ab0000000000074b7bd0dd29c72004c69f02080082012b66e04f77baa004c69e80000000007d29a01fb2b6a004c69f000000000048e9b01866830004c69f02f02f04b02f02f04b12f62c0582dba2010f31964) (by decide +kernel)
private theorem c1 : WideCovered band 9358332 9897714 := wide_block_sound band profiles 9358332 9897714 (wideData 16 0x1f7d0e960002a34f800000000098fc4669800a8d3e0000000002acf10bee002a34f0000000000c8f43f49800a8d3e0000000003aeb0ec68002a34f80000000010aec362a000a8d3e0000000000bdf0af74002a34f00000000006a2c1f6d000a8d3e000000000360902aa6002a34f8000000001c9742209c00a8d3e0000000000a4fa4060a31002a34f800000020078b9b03d3df400a8d3e1040040802bee393ba8fa002a34f800000000058341a2a00064aae00000000017ce0a8e000192ac03903904d83903904d8ff37d04e21e6a091f2aaa4) (by decide +kernel)
private theorem c2 : WideCovered band 9897715 10492896 := wide_block_sound band profiles 9897715 10492896 (wideData 16 0x6d707f1c000a8d3e0000000001e0d1ff6a002a34f80000000007ba0060b64002a34f80000000005ca0061874002a34f82080082007e65060ae6002a34f80000000005f78673c800a8d3e0000000001a7e19d28002a34f00000000006cfc676e800a8d3e0000000001e2a19eec002a34f80000000007d206a28800a8d3e000000000229f1ab32002a34f800000000078fc6bbb800a8d3e00000000027185bc20002a34f82080082001b3c57d9000a8d3e0000000001b9c138ea002a34f03a03a04d83a03a04d92c25a059adee4092fac922) (by decide +kernel)
private theorem c3 : WideCovered band 10492897 11385668 := wide_block_sound band profiles 10492897 11385668 (wideData 16 0x2080082007f7d0bfeb0004c69f000000000158f40ac960004c69f000000000188280a4dea004c69f0000000001ce6407aa38004c69e8000000000196ba01aaba00131a7c000000000076c3c33dd00131a7a0000000000e1834077961004c69f08200208003a77841aab8ea004c69e80000000006da8065924002a34f80000000006f7c065bfa002a34f80000000006fb8063ebe002a34f80000000007878062b3c002a34f80000000003ef9066e24002a34f82080082003fb47feb800a8d3e0000000001a4a1f8ba002a34f03b03b04d83b03b04d94e61905d298720948b6cbe) (by decide +kernel)
private theorem c4 : WideCovered band 11385669 12576031 := wide_block_sound band profiles 11385669 12576031 (wideData 16 0x208008201d924223b30004c69f000000000018bea07ee7d00131a7c00000000006387c1f7dbc004c69f02080082013ef01e9aaa004c69e8000000001b92c179c64004c69f0000000001beb417a92c004c69e8000000001de741a4878004c69f0208008200c964176974004c69e80000000018c2413cdf0004c69f00000000019a2013ba38004c69f0000000001aba413b964004c69f02080082005a6c130af4004c69e80000000015c240f8aaa004c69f00000000016de40f6b20004c69f000000000189600f1b34004c69f03e03e04d83e03e04d9b9f8d07caeb7e095eeefa2) (by decide +kernel)
private theorem c5 : WideCovered band 12576032 13543200 := wide_block_sound band profiles 12576032 13543200 (wideData 13 0xe4c30639d6e004c69e80000000002fb5817a29c00131a7c0820020800a8b3c532cf6004c69e80000000002a7eb1283c800131a7c0000000000a6e38465820004c69e82080082001e24d10a72f00131a7c000000000078be8372924004c69f00000000001ca4e0beee900131a7c000000000075bbc334c60004c69e82080082001935f0bb3cc80131a7c00000000006bbac2a4fbc004c69f00000000001abae09f3a980131a7c120120136120120136067ea4a0ac36baa098923ef8) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8781749 9358331 13543200 c0 (wide_covered_join band 9358332 9897714 13543200 c1 (wide_covered_join band 9897715 10492896 13543200 c2 (wide_covered_join band 10492897 11385668 13543200 c3 (wide_covered_join band 11385669 12576031 13543200 c4 c5)))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 8)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 8≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤67)
    (hT0 : 3777≤T) (hT1 : T≤4012) (hnu : 8781749≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤21418250682550398 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R168

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R169
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨8,68,3725,3978,20947737827292686⟩
private def profiles : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨44768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 8912820 9401501 := wide_block_sound band profiles 8912820 9401501 (wideData 16 0x5c7c0bbd00064db600000000017fc01c7a001936e00000000006f240efd80064db60000000001f3b02f68001936e00000000008bf40a6c00064db6000000000272801afa001936e0000000000af2c2ac001936d8000000000bf241f0b40064db80000000003b4d03975001936d80000000011b7416da40064db8000000000565a08b75001936d8618c186304c63ef10618e3fb9081936d80000000001de096c33ce7ea000a9b6e000000000078fa580dce0ca6004cbaf0208008200fcead03ee9df2004cbaf02f02f04b02f02f04b1f9bba07beffb6011932da2) (by decide +kernel)
private theorem c1 : WideCovered band 9401502 9815000 := wide_block_sound band profiles 9401502 9815000 (wideData 16 0x820020800ecc51a22002a6db030c00c30119781709c00a9b6e0820020802b3c05f72002a6db830c00c30159b00a5dc00a9b6e0000020801ee8a0123cb5002a6db84100082007fe5c4dd7ff000a9b6e0000000001a7c09ba2001936d80000000016c49bfe001936e00000000002b25271e80064db60000000000b6849d38001936e00000000014804c26001936d800000000038bd272d80064db60820020800b09499a6001936d80000000004cec171c00064db800000000013de05a32001936d83903904e03903904e11ca1c04debb3e091fbf832) (by decide +kernel)
private theorem c2 : WideCovered band 9815001 10416453 := wide_block_sound band profiles 9815001 10416453 (wideData 16 0x79645fcd800a9b6c00000000022881ccf6002a6db800000000098647a58800a9b6e00000000027b91eea2002a6db800000000068615e5e000a9b6e0820020800e1e5bf6e002a6db80000000007bfc5b8a800a9b6e0000000001e6f0fbb2002a6db80000000008e745a48800a9b6c000000000277b1682a002a6db80000000009fb8379c000a9b6e00000000032a814aac002a6db8000000000ebbc53ee800a9b6c0000000000e453aa800a9b6e000000000130c079fa002a6db83a83a84e03a83a84e12beca059289f0092e6babe) (by decide +kernel)
private theorem c3 : WideCovered band 10416454 11093088 := wide_block_sound band profiles 10416454 11093088 (wideData 16 0x28e0f0af71004cbaf08200208001d7fb41ab783a004cbae800000000089e0069f7e002a6db80000000007db4063f72002a6db80000000004d3806b8ec002a6db82080082002b31067aea002a6db80000000006c2c7b5c000a9b6e0000000001e2e0186e9800a9b6e0000000001f2e018ead800a9b6c0000000001fde018f8f800a9b6e0000000001eff1dce0002a6db80000000008ea0064eac002a6db80000000007bb9065dba002a6db02080082004aec6249000a9b6e0000000001e1c1d8f2002a6db83b03b04e03b03b04e15eb3b05befd32093fa2878) (by decide +kernel)
private theorem c4 : WideCovered band 11093089 12295995 := wide_block_sound band profiles 11093089 12295995 (wideData 16 0x473f06b33c00132ebc0820020807a2d05fa7a80132eba0000000006ffa0586fd80132ebc000000000739d04fbeb80132ebc082002080326b05ea5e00132ebc0000000005eda03eeed00132eba0000000006f6d04cb5980132ebc00000000067cf03d7eb00132ebc000000000724e03ce1d80132ebc0820020800b8d43fb6f00132eba0000000005a0b02bb0880132ebc00000000072590397f800132ebc00000000072b901fb7c80132ebc000000000062dfc06f9a4004cbae8000000001bf340ac9fe004cbaf03e03e04e03e03e04e19e2ae079f5dba095a7583a) (by decide +kernel)
private theorem c5 : WideCovered band 12295996 13498901 := wide_block_sound band profiles 12295996 13498901 (wideData 16 0xe28f05a1ff2004cbaf00000000002da79139a2f80132eba0820020800a6dac4b6b68004cbaf000000000028fde0efe3b00132ebc0000000000a1c283aac2e004cbaf00000000001ee2d0f924f80132eba082002080071c242ecfe0004cbaf00000000001dfdf0c8e2900132eba000000000072a682b4cae004cbaf0208008200182e809df6d00132eba00000000006cfe427083a004cbaf00000000001a31e08aa7e80132ebc00000000006ce3c26687e004cbaf02080082013b741bdc7a004cbae80000000001866906c68e00132ebc0fe0fe1380fe0fe13806697ad09aaae6a097ce2bb0) (by decide +kernel)
private theorem c6 : WideCovered band 13498902 13724445 := wide_block_sound band profiles 13498902 13724445 (wideData 3 0x1289bc7bfaf4004cbae80000000003d7ef1ad23c80132ebc1281281381281281380a2b79f0ff6afe4099f2ff24) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8912820 9401501 13724445 c0 (wide_covered_join band 9401502 9815000 13724445 c1 (wide_covered_join band 9815001 10416453 13724445 c2 (wide_covered_join band 10416454 11093088 13724445 c3 (wide_covered_join band 11093089 12295995 13724445 c4 (wide_covered_join band 12295996 13498901 13724445 c5 c6))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 8)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 8≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤68)
    (hT0 : 3725≤T) (hT1 : T≤3978) (hnu : 8912820≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤20947737827292686 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R169

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R170
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨8,69,3675,3943,24202393185243491⟩
private def profiles : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨25988,196,5079⟩
  | 2 => ⟨26034,193,5079⟩
  | 3 => ⟨45018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 9043891 9423719 := wide_block_sound band profiles 9043891 9423719 (wideData 16 0x46ec05ce9001962f80000000014fec2319400658e00000000006b6c02fb1001962f80000000001835810eff0019638000000000038f88657aae638c20658be0000000001afa3c062ca48c00658be000000000236c3c0a8ae7a400658be0000000003afe60164df7ac00658e00820020800b3b299419b7be8081962f80000000006bf3d1ce70e000658e0000000000075afc3fcba5001962f80000000006869d0eb35d000658e018638618e4e9c750edcf4f820658be000000000075c23d0bee28ba0019638000000000019bbb6022fa38e800aa97e0be0be12c0be0be12c0afaadb11e6eb38011b349e0) (by decide +kernel)
private theorem c1 : WideCovered band 9423720 9727581 := wide_block_sound band profiles 9423720 9727581 (wideData 16 0x5825374e000658be0000000000ac848fe2001963802080082002bf41ac9000658be000000000130b059ae0019638000000000059741f8e000658be000000000168805bea001962f80000000005c68129a000658be00000000017fc03eee001963800000000006bfc0e9d800658be0000000001f5d07b36001963800000000007ef80a9e000658be000000000237b01bfa001963800000000009e6846e001962f8000000000bdbc13c8000658be000000000339c018f3001962f83983984e83983984e90d31804dfadb019282ae6e) (by decide +kernel)
private theorem c2 : WideCovered band 9727582 10297323 := wide_block_sound band profiles 9727582 10297323 (wideData 16 0x269812cbe002aa5f8000000000bafc6ac8800aa97c0000000002f3911c28002aa5f8000000000dd7c4fbf800aa97e000000000074c56fec002aa5f80000000016d4ede0002aa5f02080082008ab56a18000aa97e0000000002ad906d7e002aa5f8000000000d9e0379f800aa97e0000000003a6b1f9800aa97c0000000004b6908b74002aa5f80000000015e60270cc00aa97e000000000779f09b7d002aa5f82080082001df094aa20c000aa97e000000000071948ea4001962f83a03a04e83a03a04e93a6fc04eadf2a192cbca3a) (by decide +kernel)
private theorem c3 : WideCovered band 10297324 10905048 := wide_block_sound band profiles 10297324 10905048 (wideData 16 0x1ffb0186c8800aa97e00000000022ac0186fc800aa97c000000000276901a38f800aa97e0000000000aad018ab8800aa97e0820020800e7e419a5e000aa97e0000000001e1f1aee0002aa5f000000000089f0061874002aa5f80000000007e3c6b8c800aa97e000000000265c01876a800aa97e00000000023ab1afe2002aa5f00000000009c346e3e800aa97e00000000007fc418e7e000aa97e082002080138d5a930002aa5f800000000089a86aef800aa97e0000000001fad13be8002aa5f83b03b04e83b03b04e96a68a05ab68e2193dba934) (by decide +kernel)
private theorem c4 : WideCovered band 10905049 11930584 := wide_block_sound band profiles 10905049 11930584 (wideData 16 0x1828d04b2ed00134afa0820020803b4127b2e004d2bf0000000001abb00ebd66004d2be8000000001cd300e6ee2004d2bf00000000001824d03874e80134afc000000000065f380bbd60004d2bf0000000000bd790b3e2c004d2be82080082011bf8070f26004d2bf0000000000186dd0b9a2004d2be830c00c3003d72903a7fe40134afc2080082007a4941badb78004d2be80000000009fa806fbac002aa5f80000000004cf90699f0002aa5f82080082006d6c067c3c002aa5f80000000007b6c0618e2002aa5f83c03c04e83c03c04e999b7b05eabb2a194efd8ee) (by decide +kernel)
private theorem c5 : WideCovered band 11930585 13146034 := wide_block_sound band profiles 11930585 13146034 (wideData 16 0x2869f0d966e80134afa00000000007dab43389fc004d2bf02080082001a3db0ad7a900134afa000000000073eb02a683e004d2bf00000000001cead09fadb00134afc0820020807eec0997af80134afc000000000065e241e1c24004d2be80000000001a7ce07ea8f80134afc00000000006aab41f7938004d2be82080082013a201bba3e004d2bf000000000018b5f0696b880134afa000000000063b241a2f32004d2bf00000000001934b068a6d00134afc08200208023fe05939d80134afc00000000077ae04df3c00134afa0fc0fc13a0fc0fc13a063cb8908a21ff2196f3aa6c) (by decide +kernel)
private theorem c6 : WideCovered band 13146035 13905690 := wide_block_sound band profiles 13146035 13905690 (wideData 10 0x5b21c01931df8004d2be82080082004ae9d0183b9b4004d2bf0000000000482481b832b80134afa0000000000f7ea4665920004d2bf00000000003c3af17cb0980134afa0820020800aff244f8b2c004d2bf00000000002cf4f119fee00134afc0000000000b1eb4438fec004d2bf02080082001fa8f0fe76880134afa12412413a12412413a0788bdc0cc6a9721999e09e0) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 9043891 9423719 13905690 c0 (wide_covered_join band 9423720 9727581 13905690 c1 (wide_covered_join band 9727582 10297323 13905690 c2 (wide_covered_join band 10297324 10905048 13905690 c3 (wide_covered_join band 10905049 11930584 13905690 c4 (wide_covered_join band 11930585 13146034 13905690 c5 c6))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 8)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 8≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤69)
    (hT0 : 3675≤T) (hT1 : T≤3943) (hnu : 9043891≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤24202393185243491 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R170

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R171
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨8,70,3625,3879,24157628611101568⟩
private def profiles : ℕ → Profile
  | 0 => ⟨25988,196,5079⟩
  | 1 => ⟨26034,193,5079⟩
  | 2 => ⟨45018,250,10158⟩
  | 3 => ⟨27100,141,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 9174962 9481960 := wide_block_sound band profiles 9174962 9481960 (wideData 16 0x2b1a01d6100196f98000000000ca38070a40065be60000000003b1816bc0065be600000000042be0a96b00196fa00000000014c6c172f40065be60000000000e78e9b5dcf5ef508196fa00000000003c63a0feea9c0065be60000000000f7bb8060dacb40065be800000000026ad2c12bfbd00196f980000000006e21e038ecd2f00196fa02080082002932df10ede3db42065be6000000000167fe85e3e2400196fa00000000004fa9811a7bb00065be6000000000076c1ecb9e40065be8000000000124cb80acbe900196f983903904f03903904f04d24bac06aa68d6c011c65aaa) (by decide +kernel)
private theorem c1 : WideCovered band 9481961 9788958 := wide_block_sound band profiles 9481961 9788958 (wideData 16 0x1acc0aeb200196f980000000001d282ade00065be60000000003a51e0d80065be60000000000e3f4b8ac00196fa00000000004a468e600196f980000000003e692e7f80065be80000000000e4f49e7e00196f982080082004aa012bc00065be8000000000165a06c3400196f9800000000058a40aaa80065be600000000017fa05ef000196f980000000006a200eff00065be80000000001b9c02cac00196f980000000007e7412fc80065be8000000000222901a2300196f983983984f03983984f10ea5904dada261128fcf78) (by decide +kernel)
private theorem c2 : WideCovered band 9788959 10402955 := wide_block_sound band profiles 9788959 10402955 (wideData 16 0x820020801a0b15a2c002abeb00000000008dec6e9c800aafae000000000230a13fac002abeb80000000009ab04eb9800aafae0000000002ac812cf2002abeb0000000000bdb8478b800aafae0000000003b7d1b9a6002abeb80000000007da84328000aafae0000000002713e2e800aafac000000000770361f800aafae0000000000ebc0a8b2002abeb8208008200df14a38002abeb8000000000ee7c2e2002abeb800000000129a4167c400aafae0c30030c00bec780718bd002abeb83b03b04f03b03b04f0eff6f05932fec112dfa82a) (by decide +kernel)
private theorem c3 : WideCovered band 10402956 11016952 := wide_block_sound band profiles 10402956 11016952 (wideData 16 0x2080082002924064be0002abeb00000000007d28064cae002abeb80000000008838065e2a002abeb80000000007ef8062b72002abeb800000000089e0062cf4002abeb00000000008d34062fb2002abeb80000000006e6c063fee002abeb820800820079e5068cae002abeb80000000006ff06fad800aafac0000000001ea81bdf6002abeb80000000007da86f58000aafae000000000225b1bd34002abeb80000000009da006396a002abeb80000000009bf4727e800aafae0000000000b8f1cbfc002abeb83b83b84f03b83b84f15a22d05abcb6e113f699e4) (by decide +kernel)
private theorem c4 : WideCovered band 11016953 12168196 := wide_block_sound band profiles 11016953 12168196 (wideData 16 0x82002080335b0686ee80135f3c0000000006ada049b3b00135f3a0000000006edc048a0800135f3c0000000000619ec13e8ec004d7ce8000000000d8700fcf70004d7cf0208008200df6c0fca28004d7cf000000000198280b2fb8004d7cf0000000001be6c0a8a22004d7ce800000000019729038f4c00135f3c000000000069d7006be20004d7ce8000000000ca300a98fc004d7cf00000000002c2ce01a6bcc0135f3a000000000276cf41fa8a7004d7cf08200208009f33a41db3b26004d7ce80000000008ef0069eb0002abeb83c83c84f03c83c84f1897c905ef4fbc1158b8b7e) (by decide +kernel)
private theorem c5 : WideCovered band 12168197 13396190 := wide_block_sound band profiles 12168197 13396190 (wideData 16 0xaeda4439d2e004d7cf000000000029afc11ca6b80135f3a08200208007bd2c365dea004d7cf00000000002879c0df25e80135f3a00000000007aea8325822004d7cf020800820019a4b0af7fb80135f3c0000000000749282b7df6004d7cf00000000001bbac09b22e80135f3a000000000065de42a9c72004d7cf020800820018f8e07c37c00135f3a000000000065fa01e9aaa004d7cf00000000001aae908961880135f3a0820020804b3b06ea0c80135f3c000000000060afc17eba2004d7cf000000000018a6e0693ed00135f3c0fe0fe13c0fe0fe13c064a38e08db2da6117aebf62) (by decide +kernel)
private theorem c6 : WideCovered band 13396191 14086935 := wide_block_sound band profiles 13396191 14086935 (wideData 9 0x13ac20063ef5ac0135f3a38e00e3802b3b75136affb82135f3c000000000171aec067aa5980135f3a00000000013792c061a3fc00135f3c0820020800f296072eb26004d7ce80000000003e2db1ab21a80135f3c0000000000eab345e3bbc004d7ce82080082002e32b16ba7800135f3c12612613c12612613c07d835e0e963dfa119daaab6) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 9174962 9481960 14086935 c0 (wide_covered_join band 9481961 9788958 14086935 c1 (wide_covered_join band 9788959 10402955 14086935 c2 (wide_covered_join band 10402956 11016952 14086935 c3 (wide_covered_join band 11016953 12168196 14086935 c4 (wide_covered_join band 12168197 13396190 14086935 c5 c6))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 8)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 8≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤70)
    (hT0 : 3625≤T) (hT1 : T≤3879) (hnu : 9174962≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤24157628611101568 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R171

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R172
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨9,53,4337,4342,9615460244502145⟩
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨42018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 6946754 9861934 := wide_block_sound band profiles 6946754 9861934 (wideData 16 0x32c7e2a80121b3c000000000434672980121b3c0000000006384fef80121b3c000000000066d02a7be40121b3e18600618072506682ee00121b3c0000000000b1065c6c002836b82080082002d1dcb2002836b80000000003a1de76002836b80000000003b1e8b4002836b80000000003e018ea8000a0dae0000000000f8060a22002836b80000000003e1fe2c002836b8924024900cfbc17cbedf020a0dae0c30030c006c6b4882121b3c14500514060daa00888b9e83b83b83f03b83b83f01c15f6e011a6ce28) (by decide +kernel)
private theorem c1 : WideCovered band 9861935 10921999 := wide_block_sound band profiles 9861935 10921999 (wideData 16 0x2080082005c04d7ee80121b3c00000000037c13dca400486cf0000000000cd049e3b80121b3c000000000364127be000486cf02080082004d04df3900121b3c0000000002b40eaff000486cf0000000000ba03a7ae00121b3c0000000003701238b200486cf0000000000cf03b20b80121b3c0820020800710e983200486cf0000000000ac02d38980121b3c0000000002bc0accb600486cf8000000000ea039fb880121b3c0000000003b40aaeb800486cf0208008200ae41f6dc80121b3c0e80e80fc0e80e80fc421807b77a70192f7eff8) (by decide +kernel)
private theorem c2 : WideCovered band 10922000 11187015 := wide_block_sound band profiles 10922000 11187015 (wideData 4 0x208008200ab06bfa800121b3c0000000003ac168b2a00486cf0000000000ec059e9e00121b3c0f00f00fc0f00f00fc539f09a3183a194fb5b7a) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6946754 9861934 11187015 c0 (wide_covered_join band 9861935 10921999 11187015 c1 c2))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 9)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 9≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤53)
    (hT0 : 4337≤T) (hT1 : T≤4342) (hnu : 6946754≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤9615460244502145 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R172

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R173
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨9,54,4264,4316,9814159154075436⟩
private def profiles : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨42268,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 7077825 9491195 := wide_block_sound band profiles 7077825 9491195 (wideData 16 0x1ae4062c7a00286ef82080082001cb96b29000a1bbe000000000062e1cfb200286ef8000000000192876a8800a1bbe000000000065e1de3200286ef80000000001a207aac000a1bbe00000000006aa1effa00286ef80000000001b607fbd000a1be000000000006d060f7800286ef82080082016859d2a00286ef892402490048e5d05cbbde608286ef80000000012c01d35e020a1bbe0820020804ec067c2a08897be1b6c06db00d063010af7c1c70071c002f01980060def883883883f83883883f8bf15cf400fc6eea2) (by decide +kernel)
private theorem c1 : WideCovered band 9491196 10429728 := wide_block_sound band profiles 9491196 10429728 (wideData 16 0x3fe00e5df40048bdf00000000004b2c0e6ba00048bdf80000000004ffc0e8ce20048bdf02080082002a650b1f700048bdf00000000003e280a6ee00048bdf00000000004aac0a38600048bdf00000000005860073df20048bdf000000000069684e7b00122f7c00000000027ee1cbaa0048bdf00000000011eb4369fc0122f7c00000000006fdbc166a750048bdf08200208002872e41af4b6c0048bdf000000000019a806287400286ef800000000019f8062cba00286ef80000000001a740639fa00286ef83883883f83883883f84b32c0683ebf019296afb4) (by decide +kernel)
private theorem c2 : WideCovered band 10429729 11368260 := wide_block_sound band profiles 10429729 11368260 (wideData 14 0x170e06ab0f00122f7c000000000172906a61a80122f7c000000000175a06a3ca00122f7c0820020800e08068a7b00122f7c000000000135d058f3f00122f7c000000000136905822880122f7c00000000012d904b79d00122f7c0000000000bdd0596db00122f7c0820020800e5e048f9e00122f7c000000000125a048e8d80122f7c00000000012c804928800122f7c0000000001368049b7900122f7c0820020800b40f1db40048bdf03b03b03f83b03b03f85ef8d0882aee2194835bfc) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7077825 9491195 11368260 c0 (wide_covered_join band 9491196 10429728 11368260 c1 c2))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 9)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 9≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤54)
    (hT0 : 4264≤T) (hT1 : T≤4316) (hnu : 7077825≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤9814159154075436 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R173
