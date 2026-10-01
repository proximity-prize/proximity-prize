import ProximityPrize.SubmissionLower.RelativeWideBlocks6815
set_option Elab.async false
section MergedPart0
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R168
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨8,67,3777,4012,21418250682550398⟩
private def profiles_RelativeWidePack6815_P28 : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨44518,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P28 : WideCovered band 8781749 9358331 := wide_block_sound band profiles_RelativeWidePack6815_P28 8781749 9358331 (wideData 16 0x18f82a6d00064aae0000000000e016e880064aae0000000000f2b4ab3600192ac00000000006904ffe00192ab80000000004afd2b4c00064ab00000000002f812ea80064aae082002080076e498e800192ac00000000004cbc079800064aae00000000016dd05a2800192ac00000000005be84ea00192ab8410a104282da0ca557ca788c2064ab0000000000074b7bd0dd29c72004c69f02080082012b66e04f77baa004c69e80000000007d29a01fb2b6a004c69f000000000048e9b01866830004c69f02f02f04b02f02f04b12f62c0582dba2010f31964) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P28 : WideCovered band 9358332 9897714 := wide_block_sound band profiles_RelativeWidePack6815_P28 9358332 9897714 (wideData 16 0x1f7d0e960002a34f800000000098fc4669800a8d3e0000000002acf10bee002a34f0000000000c8f43f49800a8d3e0000000003aeb0ec68002a34f80000000010aec362a000a8d3e0000000000bdf0af74002a34f00000000006a2c1f6d000a8d3e000000000360902aa6002a34f8000000001c9742209c00a8d3e0000000000a4fa4060a31002a34f800000020078b9b03d3df400a8d3e1040040802bee393ba8fa002a34f800000000058341a2a00064aae00000000017ce0a8e000192ac03903904d83903904d8ff37d04e21e6a091f2aaa4) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P28 : WideCovered band 9897715 10492896 := wide_block_sound band profiles_RelativeWidePack6815_P28 9897715 10492896 (wideData 16 0x6d707f1c000a8d3e0000000001e0d1ff6a002a34f80000000007ba0060b64002a34f80000000005ca0061874002a34f82080082007e65060ae6002a34f80000000005f78673c800a8d3e0000000001a7e19d28002a34f00000000006cfc676e800a8d3e0000000001e2a19eec002a34f80000000007d206a28800a8d3e000000000229f1ab32002a34f800000000078fc6bbb800a8d3e00000000027185bc20002a34f82080082001b3c57d9000a8d3e0000000001b9c138ea002a34f03a03a04d83a03a04d92c25a059adee4092fac922) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P28 : WideCovered band 10492897 11385668 := wide_block_sound band profiles_RelativeWidePack6815_P28 10492897 11385668 (wideData 16 0x2080082007f7d0bfeb0004c69f000000000158f40ac960004c69f000000000188280a4dea004c69f0000000001ce6407aa38004c69e8000000000196ba01aaba00131a7c000000000076c3c33dd00131a7a0000000000e1834077961004c69f08200208003a77841aab8ea004c69e80000000006da8065924002a34f80000000006f7c065bfa002a34f80000000006fb8063ebe002a34f80000000007878062b3c002a34f80000000003ef9066e24002a34f82080082003fb47feb800a8d3e0000000001a4a1f8ba002a34f03b03b04d83b03b04d94e61905d298720948b6cbe) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P28 : WideCovered band 11385669 12576031 := wide_block_sound band profiles_RelativeWidePack6815_P28 11385669 12576031 (wideData 16 0x208008201d924223b30004c69f000000000018bea07ee7d00131a7c00000000006387c1f7dbc004c69f02080082013ef01e9aaa004c69e8000000001b92c179c64004c69f0000000001beb417a92c004c69e8000000001de741a4878004c69f0208008200c964176974004c69e80000000018c2413cdf0004c69f00000000019a2013ba38004c69f0000000001aba413b964004c69f02080082005a6c130af4004c69e80000000015c240f8aaa004c69f00000000016de40f6b20004c69f000000000189600f1b34004c69f03e03e04d83e03e04d9b9f8d07caeb7e095eeefa2) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P28 : WideCovered band 12576032 13543200 := wide_block_sound band profiles_RelativeWidePack6815_P28 12576032 13543200 (wideData 13 0xe4c30639d6e004c69e80000000002fb5817a29c00131a7c0820020800a8b3c532cf6004c69e80000000002a7eb1283c800131a7c0000000000a6e38465820004c69e82080082001e24d10a72f00131a7c000000000078be8372924004c69f00000000001ca4e0beee900131a7c000000000075bbc334c60004c69e82080082001935f0bb3cc80131a7c00000000006bbac2a4fbc004c69f00000000001abae09f3a980131a7c120120136120120136067ea4a0ac36baa098923ef8) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8781749 9358331 13543200 c0_RelativeWidePack6815_P28 (wide_covered_join band 9358332 9897714 13543200 c1_RelativeWidePack6815_P28 (wide_covered_join band 9897715 10492896 13543200 c2_RelativeWidePack6815_P28 (wide_covered_join band 10492897 11385668 13543200 c3_RelativeWidePack6815_P28 (wide_covered_join band 11385669 12576031 13543200 c4_RelativeWidePack6815_P28 c5_RelativeWidePack6815_P28)))))
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
private def profiles_RelativeWidePack6815_P28 : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨44768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P28 : WideCovered band 8912820 9401501 := wide_block_sound band profiles_RelativeWidePack6815_P28 8912820 9401501 (wideData 16 0x5c7c0bbd00064db600000000017fc01c7a001936e00000000006f240efd80064db60000000001f3b02f68001936e00000000008bf40a6c00064db6000000000272801afa001936e0000000000af2c2ac001936d8000000000bf241f0b40064db80000000003b4d03975001936d80000000011b7416da40064db8000000000565a08b75001936d8618c186304c63ef10618e3fb9081936d80000000001de096c33ce7ea000a9b6e000000000078fa580dce0ca6004cbaf0208008200fcead03ee9df2004cbaf02f02f04b02f02f04b1f9bba07beffb6011932da2) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P28 : WideCovered band 9401502 9815000 := wide_block_sound band profiles_RelativeWidePack6815_P28 9401502 9815000 (wideData 16 0x820020800ecc51a22002a6db030c00c30119781709c00a9b6e0820020802b3c05f72002a6db830c00c30159b00a5dc00a9b6e0000020801ee8a0123cb5002a6db84100082007fe5c4dd7ff000a9b6e0000000001a7c09ba2001936d80000000016c49bfe001936e00000000002b25271e80064db60000000000b6849d38001936e00000000014804c26001936d800000000038bd272d80064db60820020800b09499a6001936d80000000004cec171c00064db800000000013de05a32001936d83903904e03903904e11ca1c04debb3e091fbf832) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P28 : WideCovered band 9815001 10416453 := wide_block_sound band profiles_RelativeWidePack6815_P28 9815001 10416453 (wideData 16 0x79645fcd800a9b6c00000000022881ccf6002a6db800000000098647a58800a9b6e00000000027b91eea2002a6db800000000068615e5e000a9b6e0820020800e1e5bf6e002a6db80000000007bfc5b8a800a9b6e0000000001e6f0fbb2002a6db80000000008e745a48800a9b6c000000000277b1682a002a6db80000000009fb8379c000a9b6e00000000032a814aac002a6db8000000000ebbc53ee800a9b6c0000000000e453aa800a9b6e000000000130c079fa002a6db83a83a84e03a83a84e12beca059289f0092e6babe) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P28 : WideCovered band 10416454 11093088 := wide_block_sound band profiles_RelativeWidePack6815_P28 10416454 11093088 (wideData 16 0x28e0f0af71004cbaf08200208001d7fb41ab783a004cbae800000000089e0069f7e002a6db80000000007db4063f72002a6db80000000004d3806b8ec002a6db82080082002b31067aea002a6db80000000006c2c7b5c000a9b6e0000000001e2e0186e9800a9b6e0000000001f2e018ead800a9b6c0000000001fde018f8f800a9b6e0000000001eff1dce0002a6db80000000008ea0064eac002a6db80000000007bb9065dba002a6db02080082004aec6249000a9b6e0000000001e1c1d8f2002a6db83b03b04e03b03b04e15eb3b05befd32093fa2878) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P28 : WideCovered band 11093089 12295995 := wide_block_sound band profiles_RelativeWidePack6815_P28 11093089 12295995 (wideData 16 0x473f06b33c00132ebc0820020807a2d05fa7a80132eba0000000006ffa0586fd80132ebc000000000739d04fbeb80132ebc082002080326b05ea5e00132ebc0000000005eda03eeed00132eba0000000006f6d04cb5980132ebc00000000067cf03d7eb00132ebc000000000724e03ce1d80132ebc0820020800b8d43fb6f00132eba0000000005a0b02bb0880132ebc00000000072590397f800132ebc00000000072b901fb7c80132ebc000000000062dfc06f9a4004cbae8000000001bf340ac9fe004cbaf03e03e04e03e03e04e19e2ae079f5dba095a7583a) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P28 : WideCovered band 12295996 13498901 := wide_block_sound band profiles_RelativeWidePack6815_P28 12295996 13498901 (wideData 16 0xe28f05a1ff2004cbaf00000000002da79139a2f80132eba0820020800a6dac4b6b68004cbaf000000000028fde0efe3b00132ebc0000000000a1c283aac2e004cbaf00000000001ee2d0f924f80132eba082002080071c242ecfe0004cbaf00000000001dfdf0c8e2900132eba000000000072a682b4cae004cbaf0208008200182e809df6d00132eba00000000006cfe427083a004cbaf00000000001a31e08aa7e80132ebc00000000006ce3c26687e004cbaf02080082013b741bdc7a004cbae80000000001866906c68e00132ebc0fe0fe1380fe0fe13806697ad09aaae6a097ce2bb0) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P28 : WideCovered band 13498902 13724445 := wide_block_sound band profiles_RelativeWidePack6815_P28 13498902 13724445 (wideData 3 0x1289bc7bfaf4004cbae80000000003d7ef1ad23c80132ebc1281281381281281380a2b79f0ff6afe4099f2ff24) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8912820 9401501 13724445 c0_RelativeWidePack6815_P28 (wide_covered_join band 9401502 9815000 13724445 c1_RelativeWidePack6815_P28 (wide_covered_join band 9815001 10416453 13724445 c2_RelativeWidePack6815_P28 (wide_covered_join band 10416454 11093088 13724445 c3_RelativeWidePack6815_P28 (wide_covered_join band 11093089 12295995 13724445 c4_RelativeWidePack6815_P28 (wide_covered_join band 12295996 13498901 13724445 c5_RelativeWidePack6815_P28 c6_RelativeWidePack6815_P28))))))
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
private def profiles_RelativeWidePack6815_P28 : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨25988,196,5079⟩
  | 2 => ⟨26034,193,5079⟩
  | 3 => ⟨45018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P28 : WideCovered band 9043891 9423719 := wide_block_sound band profiles_RelativeWidePack6815_P28 9043891 9423719 (wideData 16 0x46ec05ce9001962f80000000014fec2319400658e00000000006b6c02fb1001962f80000000001835810eff0019638000000000038f88657aae638c20658be0000000001afa3c062ca48c00658be000000000236c3c0a8ae7a400658be0000000003afe60164df7ac00658e00820020800b3b299419b7be8081962f80000000006bf3d1ce70e000658e0000000000075afc3fcba5001962f80000000006869d0eb35d000658e018638618e4e9c750edcf4f820658be000000000075c23d0bee28ba0019638000000000019bbb6022fa38e800aa97e0be0be12c0be0be12c0afaadb11e6eb38011b349e0) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P28 : WideCovered band 9423720 9727581 := wide_block_sound band profiles_RelativeWidePack6815_P28 9423720 9727581 (wideData 16 0x5825374e000658be0000000000ac848fe2001963802080082002bf41ac9000658be000000000130b059ae0019638000000000059741f8e000658be000000000168805bea001962f80000000005c68129a000658be00000000017fc03eee001963800000000006bfc0e9d800658be0000000001f5d07b36001963800000000007ef80a9e000658be000000000237b01bfa001963800000000009e6846e001962f8000000000bdbc13c8000658be000000000339c018f3001962f83983984e83983984e90d31804dfadb019282ae6e) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P28 : WideCovered band 9727582 10297323 := wide_block_sound band profiles_RelativeWidePack6815_P28 9727582 10297323 (wideData 16 0x269812cbe002aa5f8000000000bafc6ac8800aa97c0000000002f3911c28002aa5f8000000000dd7c4fbf800aa97e000000000074c56fec002aa5f80000000016d4ede0002aa5f02080082008ab56a18000aa97e0000000002ad906d7e002aa5f8000000000d9e0379f800aa97e0000000003a6b1f9800aa97c0000000004b6908b74002aa5f80000000015e60270cc00aa97e000000000779f09b7d002aa5f82080082001df094aa20c000aa97e000000000071948ea4001962f83a03a04e83a03a04e93a6fc04eadf2a192cbca3a) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P28 : WideCovered band 10297324 10905048 := wide_block_sound band profiles_RelativeWidePack6815_P28 10297324 10905048 (wideData 16 0x1ffb0186c8800aa97e00000000022ac0186fc800aa97c000000000276901a38f800aa97e0000000000aad018ab8800aa97e0820020800e7e419a5e000aa97e0000000001e1f1aee0002aa5f000000000089f0061874002aa5f80000000007e3c6b8c800aa97e000000000265c01876a800aa97e00000000023ab1afe2002aa5f00000000009c346e3e800aa97e00000000007fc418e7e000aa97e082002080138d5a930002aa5f800000000089a86aef800aa97e0000000001fad13be8002aa5f83b03b04e83b03b04e96a68a05ab68e2193dba934) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P28 : WideCovered band 10905049 11930584 := wide_block_sound band profiles_RelativeWidePack6815_P28 10905049 11930584 (wideData 16 0x1828d04b2ed00134afa0820020803b4127b2e004d2bf0000000001abb00ebd66004d2be8000000001cd300e6ee2004d2bf00000000001824d03874e80134afc000000000065f380bbd60004d2bf0000000000bd790b3e2c004d2be82080082011bf8070f26004d2bf0000000000186dd0b9a2004d2be830c00c3003d72903a7fe40134afc2080082007a4941badb78004d2be80000000009fa806fbac002aa5f80000000004cf90699f0002aa5f82080082006d6c067c3c002aa5f80000000007b6c0618e2002aa5f83c03c04e83c03c04e999b7b05eabb2a194efd8ee) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P28 : WideCovered band 11930585 13146034 := wide_block_sound band profiles_RelativeWidePack6815_P28 11930585 13146034 (wideData 16 0x2869f0d966e80134afa00000000007dab43389fc004d2bf02080082001a3db0ad7a900134afa000000000073eb02a683e004d2bf00000000001cead09fadb00134afc0820020807eec0997af80134afc000000000065e241e1c24004d2be80000000001a7ce07ea8f80134afc00000000006aab41f7938004d2be82080082013a201bba3e004d2bf000000000018b5f0696b880134afa000000000063b241a2f32004d2bf00000000001934b068a6d00134afc08200208023fe05939d80134afc00000000077ae04df3c00134afa0fc0fc13a0fc0fc13a063cb8908a21ff2196f3aa6c) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P28 : WideCovered band 13146035 13905690 := wide_block_sound band profiles_RelativeWidePack6815_P28 13146035 13905690 (wideData 10 0x5b21c01931df8004d2be82080082004ae9d0183b9b4004d2bf0000000000482481b832b80134afa0000000000f7ea4665920004d2bf00000000003c3af17cb0980134afa0820020800aff244f8b2c004d2bf00000000002cf4f119fee00134afc0000000000b1eb4438fec004d2bf02080082001fa8f0fe76880134afa12412413a12412413a0788bdc0cc6a9721999e09e0) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 9043891 9423719 13905690 c0_RelativeWidePack6815_P28 (wide_covered_join band 9423720 9727581 13905690 c1_RelativeWidePack6815_P28 (wide_covered_join band 9727582 10297323 13905690 c2_RelativeWidePack6815_P28 (wide_covered_join band 10297324 10905048 13905690 c3_RelativeWidePack6815_P28 (wide_covered_join band 10905049 11930584 13905690 c4_RelativeWidePack6815_P28 (wide_covered_join band 11930585 13146034 13905690 c5_RelativeWidePack6815_P28 c6_RelativeWidePack6815_P28))))))
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
private def profiles_RelativeWidePack6815_P28 : ℕ → Profile
  | 0 => ⟨25988,196,5079⟩
  | 1 => ⟨26034,193,5079⟩
  | 2 => ⟨45018,250,10158⟩
  | 3 => ⟨27100,141,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P28 : WideCovered band 9174962 9481960 := wide_block_sound band profiles_RelativeWidePack6815_P28 9174962 9481960 (wideData 16 0x2b1a01d6100196f98000000000ca38070a40065be60000000003b1816bc0065be600000000042be0a96b00196fa00000000014c6c172f40065be60000000000e78e9b5dcf5ef508196fa00000000003c63a0feea9c0065be60000000000f7bb8060dacb40065be800000000026ad2c12bfbd00196f980000000006e21e038ecd2f00196fa02080082002932df10ede3db42065be6000000000167fe85e3e2400196fa00000000004fa9811a7bb00065be6000000000076c1ecb9e40065be8000000000124cb80acbe900196f983903904f03903904f04d24bac06aa68d6c011c65aaa) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P28 : WideCovered band 9481961 9788958 := wide_block_sound band profiles_RelativeWidePack6815_P28 9481961 9788958 (wideData 16 0x1acc0aeb200196f980000000001d282ade00065be60000000003a51e0d80065be60000000000e3f4b8ac00196fa00000000004a468e600196f980000000003e692e7f80065be80000000000e4f49e7e00196f982080082004aa012bc00065be8000000000165a06c3400196f9800000000058a40aaa80065be600000000017fa05ef000196f980000000006a200eff00065be80000000001b9c02cac00196f980000000007e7412fc80065be8000000000222901a2300196f983983984f03983984f10ea5904dada261128fcf78) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P28 : WideCovered band 9788959 10402955 := wide_block_sound band profiles_RelativeWidePack6815_P28 9788959 10402955 (wideData 16 0x820020801a0b15a2c002abeb00000000008dec6e9c800aafae000000000230a13fac002abeb80000000009ab04eb9800aafae0000000002ac812cf2002abeb0000000000bdb8478b800aafae0000000003b7d1b9a6002abeb80000000007da84328000aafae0000000002713e2e800aafac000000000770361f800aafae0000000000ebc0a8b2002abeb8208008200df14a38002abeb8000000000ee7c2e2002abeb800000000129a4167c400aafae0c30030c00bec780718bd002abeb83b03b04f03b03b04f0eff6f05932fec112dfa82a) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P28 : WideCovered band 10402956 11016952 := wide_block_sound band profiles_RelativeWidePack6815_P28 10402956 11016952 (wideData 16 0x2080082002924064be0002abeb00000000007d28064cae002abeb80000000008838065e2a002abeb80000000007ef8062b72002abeb800000000089e0062cf4002abeb00000000008d34062fb2002abeb80000000006e6c063fee002abeb820800820079e5068cae002abeb80000000006ff06fad800aafac0000000001ea81bdf6002abeb80000000007da86f58000aafae000000000225b1bd34002abeb80000000009da006396a002abeb80000000009bf4727e800aafae0000000000b8f1cbfc002abeb83b83b84f03b83b84f15a22d05abcb6e113f699e4) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P28 : WideCovered band 11016953 12168196 := wide_block_sound band profiles_RelativeWidePack6815_P28 11016953 12168196 (wideData 16 0x82002080335b0686ee80135f3c0000000006ada049b3b00135f3a0000000006edc048a0800135f3c0000000000619ec13e8ec004d7ce8000000000d8700fcf70004d7cf0208008200df6c0fca28004d7cf000000000198280b2fb8004d7cf0000000001be6c0a8a22004d7ce800000000019729038f4c00135f3c000000000069d7006be20004d7ce8000000000ca300a98fc004d7cf00000000002c2ce01a6bcc0135f3a000000000276cf41fa8a7004d7cf08200208009f33a41db3b26004d7ce80000000008ef0069eb0002abeb83c83c84f03c83c84f1897c905ef4fbc1158b8b7e) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P28 : WideCovered band 12168197 13396190 := wide_block_sound band profiles_RelativeWidePack6815_P28 12168197 13396190 (wideData 16 0xaeda4439d2e004d7cf000000000029afc11ca6b80135f3a08200208007bd2c365dea004d7cf00000000002879c0df25e80135f3a00000000007aea8325822004d7cf020800820019a4b0af7fb80135f3c0000000000749282b7df6004d7cf00000000001bbac09b22e80135f3a000000000065de42a9c72004d7cf020800820018f8e07c37c00135f3a000000000065fa01e9aaa004d7cf00000000001aae908961880135f3a0820020804b3b06ea0c80135f3c000000000060afc17eba2004d7cf000000000018a6e0693ed00135f3c0fe0fe13c0fe0fe13c064a38e08db2da6117aebf62) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P28 : WideCovered band 13396191 14086935 := wide_block_sound band profiles_RelativeWidePack6815_P28 13396191 14086935 (wideData 9 0x13ac20063ef5ac0135f3a38e00e3802b3b75136affb82135f3c000000000171aec067aa5980135f3a00000000013792c061a3fc00135f3c0820020800f296072eb26004d7ce80000000003e2db1ab21a80135f3c0000000000eab345e3bbc004d7ce82080082002e32b16ba7800135f3c12612613c12612613c07d835e0e963dfa119daaab6) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 9174962 9481960 14086935 c0_RelativeWidePack6815_P28 (wide_covered_join band 9481961 9788958 14086935 c1_RelativeWidePack6815_P28 (wide_covered_join band 9788959 10402955 14086935 c2_RelativeWidePack6815_P28 (wide_covered_join band 10402956 11016952 14086935 c3_RelativeWidePack6815_P28 (wide_covered_join band 11016953 12168196 14086935 c4_RelativeWidePack6815_P28 (wide_covered_join band 12168197 13396190 14086935 c5_RelativeWidePack6815_P28 c6_RelativeWidePack6815_P28))))))
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
private def profiles_RelativeWidePack6815_P28 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨42018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P28 : WideCovered band 6946754 9861934 := wide_block_sound band profiles_RelativeWidePack6815_P28 6946754 9861934 (wideData 16 0x32c7e2a80121b3c000000000434672980121b3c0000000006384fef80121b3c000000000066d02a7be40121b3e18600618072506682ee00121b3c0000000000b1065c6c002836b82080082002d1dcb2002836b80000000003a1de76002836b80000000003b1e8b4002836b80000000003e018ea8000a0dae0000000000f8060a22002836b80000000003e1fe2c002836b8924024900cfbc17cbedf020a0dae0c30030c006c6b4882121b3c14500514060daa00888b9e83b83b83f03b83b83f01c15f6e011a6ce28) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P28 : WideCovered band 9861935 10921999 := wide_block_sound band profiles_RelativeWidePack6815_P28 9861935 10921999 (wideData 16 0x2080082005c04d7ee80121b3c00000000037c13dca400486cf0000000000cd049e3b80121b3c000000000364127be000486cf02080082004d04df3900121b3c0000000002b40eaff000486cf0000000000ba03a7ae00121b3c0000000003701238b200486cf0000000000cf03b20b80121b3c0820020800710e983200486cf0000000000ac02d38980121b3c0000000002bc0accb600486cf8000000000ea039fb880121b3c0000000003b40aaeb800486cf0208008200ae41f6dc80121b3c0e80e80fc0e80e80fc421807b77a70192f7eff8) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P28 : WideCovered band 10922000 11187015 := wide_block_sound band profiles_RelativeWidePack6815_P28 10922000 11187015 (wideData 4 0x208008200ab06bfa800121b3c0000000003ac168b2a00486cf0000000000ec059e9e00121b3c0f00f00fc0f00f00fc539f09a3183a194fb5b7a) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 6946754 9861934 11187015 c0_RelativeWidePack6815_P28 (wide_covered_join band 9861935 10921999 11187015 c1_RelativeWidePack6815_P28 c2_RelativeWidePack6815_P28))
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
private def profiles_RelativeWidePack6815_P28 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨42268,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P28 : WideCovered band 7077825 9491195 := wide_block_sound band profiles_RelativeWidePack6815_P28 7077825 9491195 (wideData 16 0x1ae4062c7a00286ef82080082001cb96b29000a1bbe000000000062e1cfb200286ef8000000000192876a8800a1bbe000000000065e1de3200286ef80000000001a207aac000a1bbe00000000006aa1effa00286ef80000000001b607fbd000a1be000000000006d060f7800286ef82080082016859d2a00286ef892402490048e5d05cbbde608286ef80000000012c01d35e020a1bbe0820020804ec067c2a08897be1b6c06db00d063010af7c1c70071c002f01980060def883883883f83883883f8bf15cf400fc6eea2) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P28 : WideCovered band 9491196 10429728 := wide_block_sound band profiles_RelativeWidePack6815_P28 9491196 10429728 (wideData 16 0x3fe00e5df40048bdf00000000004b2c0e6ba00048bdf80000000004ffc0e8ce20048bdf02080082002a650b1f700048bdf00000000003e280a6ee00048bdf00000000004aac0a38600048bdf00000000005860073df20048bdf000000000069684e7b00122f7c00000000027ee1cbaa0048bdf00000000011eb4369fc0122f7c00000000006fdbc166a750048bdf08200208002872e41af4b6c0048bdf000000000019a806287400286ef800000000019f8062cba00286ef80000000001a740639fa00286ef83883883f83883883f84b32c0683ebf019296afb4) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P28 : WideCovered band 10429729 11368260 := wide_block_sound band profiles_RelativeWidePack6815_P28 10429729 11368260 (wideData 14 0x170e06ab0f00122f7c000000000172906a61a80122f7c000000000175a06a3ca00122f7c0820020800e08068a7b00122f7c000000000135d058f3f00122f7c000000000136905822880122f7c00000000012d904b79d00122f7c0000000000bdd0596db00122f7c0820020800e5e048f9e00122f7c000000000125a048e8d80122f7c00000000012c804928800122f7c0000000001368049b7900122f7c0820020800b40f1db40048bdf03b03b03f83b03b03f85ef8d0882aee2194835bfc) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7077825 9491195 11368260 c0_RelativeWidePack6815_P28 (wide_covered_join band 9491196 10429728 11368260 c1_RelativeWidePack6815_P28 c2_RelativeWidePack6815_P28))
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
end MergedPart0
section MergedPart1
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R174
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨9,55,4192,4289,10175228031504137⟩
private def profiles_RelativeWidePack6815_P29 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨16536,4,5080⟩
  | 3 => ⟨42518,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P29 : WideCovered band 7208896 9345289 := wide_block_sound band profiles_RelativeWidePack6815_P29 7208896 9345289 (wideData 16 0x7fc16d6c0028a7b80000000002afc73fd000a29ee0000000000b0b1dd340028a7b80000000002b3c5eff800a29ee0000000000bcf1f9220028a7b80000000002cfc060af60028a7b82080082004fa556ec800a29ee0000000000a6a17fb20028a7b80000000002ae0629f000a29ee0000000000a7c11f720028a7b80000000002df063fb800a29ee1450051401e88f816cfe3e020a29ee0c30000004b06a1d020a29ee1450071c00781c0124bbc65901964043033fb820618f7804804804804804804816d15b2200fea7aa0) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P29 : WideCovered band 9345290 9989599 := wide_block_sound band profiles_RelativeWidePack6815_P29 9345290 9989599 (wideData 16 0x26e802bb300492ef030c00c3003ea6803962b40124bbc2080082000e5df5067f37880124bbc0000000000a9901831f000a29ee0000000000b59019eed000a29ee0000000000b9b01a2dc800a29ee0820020800b0b5f96a0028a7b80000000002968060aae0028a7b800000000029fc060dfc0028a7b8000000000296c76bc800a29ee0000000000ab81fcb00028a7b80000000002ca0062ba80028a7b80000000002d7c062cfa0028a7b80000000002cfc7a3f000a29ee0820020800f0a5faa00028a7c03803804803803804807fef905e30d7c191f2ee20) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P29 : WideCovered band 9989600 11074751 := wide_block_sound band profiles_RelativeWidePack6815_P29 9989600 11074751 (wideData 16 0x2080082002f24132a3c00492ef00000000008fbc13ec2400492ef000000000089b8126d7800492ef00000000008cfc126f3800492ef020800820029e0134aa800492ef00000000006f740e8dae00492ef00000000007a600e6f7e00492ef0000000000986c121ea600492ef00000000008e340e892000492ef02080082002fb90b683e00492ef00000000007cbc0bd93e00492ef00000000007bb80a3d3c00492ef0000000000a8e00bffec00492ef0000000000af3407ae3c00492ef0000000000eda006fcf000492ef03b03b04803b03b04808ff9807af6d2419397bb3a) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P29 : WideCovered band 11074752 11549505 := wide_block_sound band profiles_RelativeWidePack6815_P29 11074752 11549505 (wideData 7 0xca281f0b2a00492ef0000000000b8fc1b397400492ef0000000000ba381b28ec00492ef020800820068f81afe2600492ef00000000009a20169db600492ef0000000000a824175fa200492ef03c83c84803c83c8480ce398098fafb6195a22eba) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7208896 9345289 11549505 c0_RelativeWidePack6815_P29 (wide_covered_join band 9345290 9989599 11549505 c1_RelativeWidePack6815_P29 (wide_covered_join band 9989600 11074751 11549505 c2_RelativeWidePack6815_P29 c3_RelativeWidePack6815_P29)))
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
private def profiles_RelativeWidePack6815_P29 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨8268,2,2540⟩
  | 2 => ⟨33072,8,10160⟩
  | 3 => ⟨42518,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P29 : WideCovered band 7339967 9226631 := wide_block_sound band profiles_RelativeWidePack6815_P29 7339967 9226631 (wideData 16 0x3d3c6319000a2ffe00000000012df018329000a2ffe00000000007cc19fe60028bff82080082005c7d761f800a2ffe0000000000bee12eba0028bff800000000039ac4e5e000a2ffe0000000000fac1986c0028bff80000000003e3c4b8f000a2ffe000000000135d1aea40028bff80000000004dfc4e88800a2ffe00000000017ff1cf260028bff800000000058ed52f8800a2ffe14500514027a830165d63c020a2ffe0820020800afc02b6af82125ffc34d00d34042833c802437ff00ec0ec1220ec0ec122065c158a60108bfe7c) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P29 : WideCovered band 9226632 9775479 := wide_block_sound band profiles_RelativeWidePack6815_P29 9226632 9775479 (wideData 16 0xeed018b4d800a2ffe0000000000fcd019f6e000a2ffe0000000000f7b018bf9800a2ffe0820020800eb9419a09000a2ffe0000000000bbd1be7e0028bff80000000003ab8061e6c0028bff800000000038ec72ba800a2ffe0000000000e9d1dbe60028bff80000000003e68062e720028bff80000000003d387798800a2ffe0000000000e0065e280028bff82080082001be566db800a2ffe0000000000e6c1d9ac0028bff80000000002ffc5f4a800a2ffe0000000000e6f18b780028bff8380380488380380488afae805ce3e7a191d67e2c) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P29 : WideCovered band 9775480 10838872 := wide_block_sound band profiles_RelativeWidePack6815_P29 9775480 10838872 (wideData 16 0x36f904ca0e80125ffc0820020800f00ecda000497ff0000000000aaac0e99be00497ff0000000000bba00eefac00497ff0000000000cc380efcac00497ff00000000009b340f1de000497ff0208008201ba42db2d00125ffc0000000002b8e02ba1b80125ffc0000000002b8f01c2af00125ffc0000000003a5e01e66c00125ffc0000000004bfb01de6c00125ffc0000000006f4f019ecd00125ffc000000000070d6012a800125ffc0000000000fd8280f6a7300497ff08200208005af0941ab5db400497ff0390390488390390488c970e068bcef4192db7dec) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P29 : WideCovered band 10838873 11730750 := wide_block_sound band profiles_RelativeWidePack6815_P29 10838873 11730750 (wideData 13 0x12f74222bf400497ff00000000013bf4227cae00497ff0208008200af3c1ebc2600497ff00000000010d241bfbf000497ff00000000010e6c1be87000497ff0000000000ea341be9e200497ff02080082009e64176e2400497ff0000000000cfa0161f7c00497ff0000000000deac16aab200497ff0000000000ef6417497e00497ff02080082004828136be200497ff0000000000c92c12fbac00497ff03c03c04883c03c04890fe4b08bf5c64194e77d6c) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7339967 9226631 11730750 c0_RelativeWidePack6815_P29 (wide_covered_join band 9226632 9775479 11730750 c1_RelativeWidePack6815_P29 (wide_covered_join band 9775480 10838872 11730750 c2_RelativeWidePack6815_P29 c3_RelativeWidePack6815_P29)))
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
private def profiles_RelativeWidePack6815_P29 : ℕ → Profile
  | 0 => ⟨8268,2,2540⟩
  | 1 => ⟨2984,24,635⟩
  | 2 => ⟨42768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P29 : WideCovered band 7471038 9171092 := wide_block_sound band profiles_RelativeWidePack6815_P29 7471038 9171092 (wideData 16 0x16fe188200028f8b800000000068385f58800a3e2e0000000001b9818a240028f8b8000000000a8f5661c000a3e2e0820020801244b9e800a3e2e000000000168f17d680028f8b800000000059e842fa000a3e2e00000000017bf108e60028f8b80000000006db03f3a800a3e2e0000000001fa80f87c0028f8b80000000009b303e2e000a3e2e0820020807a1a6d2b7d239c20a3e2e000000000068fe81aeef40028f8b8208008200deffb05c64b340049f0f071c014501afe6a0a979bf20849f0f03803804902f82f849028f8061c6a010af8a7a) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P29 : WideCovered band 9171093 9726211 := wide_block_sound band profiles_RelativeWidePack6815_P29 9171093 9726211 (wideData 16 0x13580183ca800a3e2e00000000013d80186ef000a3e2c000000000166c018a7b800a3e2e0820020801a4c5fe760028f8b80000000004b20060c260028f8b800000000048b86e38800a3e2e000000000129c1babe0028f8b80000000004c746f6d000a3e2e00000000013b81c92e0028f8b80000000005aac7a28800a3e2e0000000005a00648240028f8b82080082003fbd6a2d000a3e2e0000000000ffc169e40028f8b800000000049f45a8a800a3e2e000000000131e16af60028f8b8380380490380380490dee0e05bb1834111c7c876) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P29 : WideCovered band 9726212 10593586 := wide_block_sound band profiles_RelativeWidePack6815_P29 9726212 10593586 (wideData 16 0xfbec0e9cee0049f0f0000000000eee00ab8ae0049f0f000000000119300a4ea20049f0f000000000189bc0e6d3a0049f0f0000000000edb5078d320049f0f0208008200a9f85b5a80127c3c0000000005749019a1a80127c3c0000000006aba01aeabc0127c3c1860061803abe019f29ec0049f0f000000000059ec06ac740028f8b800000000058b0066f2e0028f8b82080082003df1066ee80028f8b80000000003fe87e9f800a3e2e000000000123a1fc240028f8b80000000004e28065ee80028f8b8390390490390390490fb62c05f63ca2112cf8a34) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P29 : WideCovered band 10593587 11703826 := wide_block_sound band profiles_RelativeWidePack6815_P29 10593587 11703826 (wideData 16 0x178fc1ec9f80049f0f00000000017a301e9d780049f0f0208008200ebbc1f1a240049f0f000000000138a817cc6c0049f0f00000000013a6817ab2a0049f0f0000000001693c1b6eea0049f0f02080082007aec167d3a0049f0f000000000119ec161d7c0049f0f00000000011cf413fdae0049f0f00000000011abc133cae0049f0f02080082005ce4163b300049f0f0000000000dff00f2fa40049f0f0000000000ed2c0f0f600049f0f0000000001282c12cda60049f0f0000000000bdb40f1e780049f0f03c03c04903c03c049148b2807ef587e114aba920) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P29 : WideCovered band 11703827 11911995 := wide_block_sound band profiles_RelativeWidePack6815_P29 11703827 11911995 (wideData 3 0x1caac2699bc0049f0e8208008201297c235b760049f0f03d83d84903d83d8491cc60d0ad39da0116bb2ca0) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7471038 9171092 11911995 c0_RelativeWidePack6815_P29 (wide_covered_join band 9171093 9726211 11911995 c1_RelativeWidePack6815_P29 (wide_covered_join band 9726212 10593586 11911995 c2_RelativeWidePack6815_P29 (wide_covered_join band 10593587 11703826 11911995 c3_RelativeWidePack6815_P29 c4_RelativeWidePack6815_P29))))
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
private def profiles_RelativeWidePack6815_P29 : ℕ → Profile
  | 0 => ⟨4134,1,1270⟩
  | 1 => ⟨16536,4,5080⟩
  | 2 => ⟨2984,24,635⟩
  | 3 => ⟨43018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P29 : WideCovered band 7602109 9110848 := wide_block_sound band profiles_RelativeWidePack6815_P29 7602109 9110848 (wideData 16 0x1fa914b2c002930f80000000008fa45319000a4c3e0000000002adc14e6a002930f80000000007da8565f800a4c3e000000000279f55e7a002930f82080082008ced539c800a4c3e0000000001f9c0c8f6002930f80000000008fa826df000a4c3e082002080133aadd41b68c719420a4c3e0000000000ecda1801871aa7e0012987c0820020804f08201aae7de0012987a000000000230aac0b1af0a0012987c000000000170fbc0748fbc8012987c1450051404ffbfc1aaa31e0212987c1c70071c00a190197bf024649f00e40e41260e40e4126078814c6000fca8ab8) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P29 : WideCovered band 9110849 9672240 := wide_block_sound band profiles_RelativeWidePack6815_P29 9110849 9672240 (wideData 16 0x1a191fe22002930f80000000006ba0060be8002930f80000000005b78061b36002930f820800820088f17fce800a4c3e000000000160f19cbe002930f80000000005aa4679f000a4c3e00000000017591a8f0002930f800000000068b06b0a800a4c3e0000000001b2e1b86a002930f800000000079bc6f78000a4c3e000000000164a1ac6e002930f8000000000983d5b5e000a4c3e082002080074d169b2002930f80000000005e2052aa800a4c3e0000000001a9a14a6c002930f83803804983803804990a2af05aacaae191ba793e) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P29 : WideCovered band 9672241 10338892 := wide_block_sound band profiles_RelativeWidePack6815_P29 9672241 10338892 (wideData 16 0x1e8247f5f8012987c000000000069ea4727a4012987c186006180269067f3be8012987c00000000012cf01af3a800a4c3e0820020800aab419b88000a4c3e000000000169f018e8a800a4c3e00000000016fa018f39000a4c3e000000000175d01920f000a4c3e00000000017d901932a000a4c3e0000000001a6801967b000a4c3e0000000001b0b019a29800a4c3e0820020801a0e4196f8000a4c3c000000000160a1eaa8002930f80000000005824731f000a4c3e000000000160f1ae22002930f83903904983903904992970a05dfbee8192c2fcfe) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P29 : WideCovered band 10338893 11461675 := wide_block_sound band profiles_RelativeWidePack6815_P29 10338893 11461675 (wideData 16 0x16eb41758e6004a61f00000000017a3c173f26004a61f00000000018864174962004a61f020800820099a4171938004a61f0000000001292c120da4004a61f0000000001396c122cf6004a61f00000000015b3012dd32004a61f000000000178b812fc78004a61e820800820019b50f7cf2004a61f00000000012a380ebbec004a61f00000000013f640eaa38004a61f000000000139280a7de2004a61f0000000001a8700e5fa4004a61f0208008200fb310b4e6e004a61f000000000139a407cbb2004a61f03b83b84983b83b84996ca8e07bb5e62193eea9b4) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P29 : WideCovered band 11461676 12093240 := wide_block_sound band profiles_RelativeWidePack6815_P29 11461676 12093240 (wideData 9 0x668302a7b24004a61e82080082017f38269d74004a61f0000000000186de08fe8e8012987c000000000061ae023afb6004a61f02080082015fac2368fc004a61f0000000001bafc1e5a6e004a61f0000000001bbfc1e2c60004a61f00000000018e701a2f70004a61f03d83d84983d83d8499ee2ca09c6db3a195ffb932) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7602109 9110848 12093240 c0_RelativeWidePack6815_P29 (wide_covered_join band 9110849 9672240 12093240 c1_RelativeWidePack6815_P29 (wide_covered_join band 9672241 10338892 12093240 c2_RelativeWidePack6815_P29 (wide_covered_join band 10338893 11461675 12093240 c3_RelativeWidePack6815_P29 c4_RelativeWidePack6815_P29))))
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
private def profiles_RelativeWidePack6815_P29 : ℕ → Profile
  | 0 => ⟨16536,4,5080⟩
  | 1 => ⟨2984,24,635⟩
  | 2 => ⟨43018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P29 : WideCovered band 7733180 9081380 := wide_block_sound band profiles_RelativeWidePack6815_P29 7733180 9081380 (wideData 16 0x2adb15874002969b8000000000c92056bd000a5a6e000000000368b0aaf6002969b80000000008920566c800a5a6e00000000022ba55fb4002969b800000000058281738800a5a6e0000000002bb855d3e002969b04100104004e36aa5067fbbf63082969b80000000003b6ffe0739babc8012acbc082002080566f7417cd38b0012acbc000000000271e3c0ade2e88012acbc0000000001a89280728b9b0012acbc000000000132f3c063cf7c8012acbc0820020800a7d6063daf2004ab2f071c01c7010ce5904b7d96e084ab2f02f82f84a02f82f84a04ab4079e6200feb4cb6) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P29 : WideCovered band 9081381 9649043 := wide_block_sound band profiles_RelativeWidePack6815_P29 9081381 9649043 (wideData 16 0x1b7f1aaec002969b800000000088b0062870002969b80000000003de10639e8002969b8208008201ff57d62002969b80000000006a306b28800a5a6e0000000001b5a1af70002969b80000000006abc52cd000a5a6c0000000001f6a1bcbc002969b80000000008b6c72a8000a5a6e00000000022be14eb8002969b80000000004c5df72002969b82080082009b69767e000a5a6e0000000001a0c0ebf0002969b80000000007b38564b000a5a6e000000000225f15a26002969b83803804a03803804a12cb0a059f2c3e111b2eaf6) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P29 : WideCovered band 9649044 10287664 := wide_block_sound band profiles_RelativeWidePack6815_P29 9649044 10287664 (wideData 16 0x1ab2f018bddc012acbc1860061804bbe01a7186e004ab2f00000000007f2806ca6a002969b80000000003c2906da72002969b82080082004f3c7b9d800a5a6e0000000001af80192cf800a5a6e0000000001b6a0193ae000a5a6c0000000001a6f1f86a002969b80000000007a20065f20002969b80000000007d20066db2002969b80000000005a2c060c78002969b82080082005ef5064f6e002969b800000000069387eaf000a5a6e000000000176a19cba002969b80000000006de0060832002969b83903904a03903904a14ef0b05d358f0112be38b4) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P29 : WideCovered band 10287665 11422991 := wide_block_sound band profiles_RelativeWidePack6815_P29 10287665 11422991 (wideData 16 0x6658058fc80012acbc000000000763c05fad80012acbc0000000006bae058acc8012acbc0820020801b7a04e2db0012acbc000000000634d04df3a8012acba0000000005b3a03f26c0012acbc000000000621f03eb0e8012acbc0000000001a9904ef7d0012acbc082002080439d02ef4b0012acbc000000000532d02defd8012acbc00000000067ff03bb998012acbc0000000006a9e02b3a90012acbc0000000006f9b02df480012acbc0820020804f1b42baaa0012acbc0000000005b4c17e2e004ab2f03b83b84a03b83b84a19dbfe07b2fb70113e27d7c) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P29 : WideCovered band 11422992 12274485 := wide_block_sound band profiles_RelativeWidePack6815_P29 11422992 12274485 (wideData 12 0x82002080065c6c2f5b20004ab2e80000000001ce4d0c87bc8012acbc00000000006def42b3a66004ab2f02080082001828b0aa33b8012acbc000000000069928270b60004ab2f0000000000193ee08ab090012acbc000000000064fa422692a004ab2f02080082018ff8234aea004ab2f0000000001e97c1b2e68004ab2e8000000001eaf01afc32004ab2f000000000018b2907b3ec8012acbc0f60f61280f60f61280638a2809a7fbfe115f718fa) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7733180 9081380 12274485 c0_RelativeWidePack6815_P29 (wide_covered_join band 9081381 9649043 12274485 c1_RelativeWidePack6815_P29 (wide_covered_join band 9649044 10287664 12274485 c2_RelativeWidePack6815_P29 (wide_covered_join band 10287665 11422991 12274485 c3_RelativeWidePack6815_P29 c4_RelativeWidePack6815_P29))))
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
private def profiles_RelativeWidePack6815_P29 : ℕ → Profile
  | 0 => ⟨16536,4,5080⟩
  | 1 => ⟨2984,24,635⟩
  | 2 => ⟨43268,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P29 : WideCovered band 7864251 9012120 := wide_block_sound band profiles_RelativeWidePack6815_P29 7864251 9012120 (wideData 16 0xfff03b2a000a687c0000000004a6c119800a687e0000000005edd059ed0029a1f80000000001877c03ee00029a1f80000000001bb9d19b370029a1f8410010400683783d06b8249e90829a1f800000000049ffdac7e68e5e0012c8fc0820020806a48e41aac3df0012c8fc0000000002e09380adf6b88012c8fc0000000002698600a1e6ba0012c8fc00000000013c8a0060cf7f8012c8fc0820020800a6e205abc32004b23e80000000001e25d0abecb8012c8fc00000000006db6c1b4938004b23f0514014500fc38c03eafcec084b23f02f02f04a82f02f04a84ee807997200fc70ae4) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P29 : WideCovered band 9012121 9586055 := wide_block_sound band profiles_RelativeWidePack6815_P29 9012121 9586055 (wideData 16 0x272f01822b000a687c00000000026df198a00029a1f80000000001fa10629240029a1f82080082006ef566b9800a687e0000000001fcd1986c0029a1f80000000007cbc4a6d000a687e000000000229911e200029a1f8000000000a9ec671b800a687e0000000002ab911aa80029a1f8000000000d8606af9000a687e00000000037c81186e0029a1f80000000003a214a18000a687e0000000002eec5ba380029a1f8208008200c37d9800a687e0000000002f1a10eb20029a1f83803804a83803804a94aaaa0592ccfe111a27eee) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P29 : WideCovered band 9586056 10159990 := wide_block_sound band profiles_RelativeWidePack6815_P29 9586056 10159990 (wideData 16 0x7e70063b300029a1f0000000000986c06acfc0029a1f80000000008c6c064caa0029a1f80000000007829065a220029a1f82080082006d34063aa20029a1f80000000006ee87688000a687e0000000002208018f8a000a687e0000000001f0b1dea80029a1f80000000008c60062da60029a1f80000000008e300619700029a1f80000000002dfc7ec9800a687e082002080176f41928b000a687e0000000001b3d188600029a1f80000000007eb87afd800a687e0000000001ede18a280029a1f83903904a83903904a97833805bf8fb4112ae8eac) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P29 : WideCovered band 10159991 11236119 := wide_block_sound band profiles_RelativeWidePack6815_P29 10159991 11236119 (wideData 16 0x1f83c13bb20004b23f00000000013fe413d9a8004b23f0208008200cb7c0fe87e004b23f00000000019f240f19ae004b23f000000000199380b8d32004b23f0000000001ffb00f0ae2004b23f00000000005fac0f0bbe004b23f02080082009df80b28b0004b23e8000000001bf200a2b74004b23f00000000001874c01db4c8012c8fc000000000065e3446da4012c8fc0000000000a0a3c46ca4012c8fc0000000000f7d280fde65004b23f08200208003da5941c79b34004b23f00000000007a24062d720029a1f83a03a04a83a03a04a99f31906832bfa113ba9e6a) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P29 : WideCovered band 11236120 12383989 := wide_block_sound band profiles_RelativeWidePack6815_P29 11236120 12383989 (wideData 16 0x1ffdc0d93988012c8fc000000000078f782ef9a0004b23f02080082001a6e80bb6080012c8fc000000000072e202a79f8004b23f00000000001ca8b0a828a8012c8fc00000000006dfb827bc6e004b23f0208008201ebe8227af4004b23f00000000001966b078a6e0012c8fa000000000068ca81f5d68004b23f02080082017fac1f7e78004b23f00000000001877a06a6688012c8fc0000000000629e41a7968004b23f000000000018e4f069b5e8012c8fc08200208033ae05d6280012c8fc0000000006b8b04bf6d8012c8fc0f40f412a0f40f412a065a2dd08d35e64115ca5d68) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P29 : WideCovered band 12383990 12455730 := wide_block_sound band profiles_RelativeWidePack6815_P29 12383990 12455730 (wideData 1 0xfc0fc12a0fc0fc12a079ca7b0d820962117e27ce4) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7864251 9012120 12455730 c0_RelativeWidePack6815_P29 (wide_covered_join band 9012121 9586055 12455730 c1_RelativeWidePack6815_P29 (wide_covered_join band 9586056 10159990 12455730 c2_RelativeWidePack6815_P29 (wide_covered_join band 10159991 11236119 12455730 c3_RelativeWidePack6815_P29 (wide_covered_join band 11236120 12383989 12455730 c4_RelativeWidePack6815_P29 c5_RelativeWidePack6815_P29)))))
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
end MergedPart1
section MergedPart2
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R180
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨9,61,3810,4117,21629505182317249⟩
private def profiles_RelativeWidePack6815_P30 : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨43518,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P30 : WideCovered band 7995322 8883764 := wide_block_sound band profiles_RelativeWidePack6815_P30 7995322 8883764 (wideData 16 0x5de01a0c80063b680000000001b7a09ee40018ed982080082006dbfcf906ba289e10818eda00000000001aefee02298a49000a6eae0000000000f58a7f17f7cdba004b74f020800820199a9d05bf1be8004b74f0000000000ec71d02f35d64004b74f00000000006eefc01aa4b22004b74e8000000000592eb1e8bd80012dd3c0820020800aee2c5b8b3a004b74f00000000002eafa10928d8012dd3c00000000006cd3c13e8f6004b74f0000000001fbfc0bbd3b004b74f02080082004979b01abcc76004b74f0000000000edb807b8760029bab82d82d84b02d82d84b0bb78f02bfaef000faa6da0) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P30 : WideCovered band 8883765 9409576 := wide_block_sound band profiles_RelativeWidePack6815_P30 8883765 9409576 (wideData 16 0x1a1a56fec0029bab80000000007db15ef8800a6eae082002080266f0ecfa0029bab8000000000b970366b800a6eae0000000003a4915c700029bab8000000000f86c2e6f000a6eae0000000004a1d09a2a0029bab80000000016ae81acf000a6eac00000000073ba02aa20029bab800000000019e9d049fb0029bab8000000001ed281fcf000a6eae0000020800a5eb47a8cc00a6eae1040020801a4d752e8fe00029bab80000000004f78222f00063b66000000000166d07e7c0018eda02f82f84b02f82f84b15d26e04e70a2c090feac2e) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P30 : WideCovered band 9409577 9989783 := wide_block_sound band profiles_RelativeWidePack6815_P30 9409577 9989783 (wideData 16 0x2080082009af1063fe40029bab80000000007de46f3a800a6eae000000000261e018a4c800a6eae00000000023281c8ec0029bab800000000098bc72bb800a6eae00000000027791cd700029bab8000000000ac24765a000a6eae0000000000e1d1de200029bab02080082009df9065cb40029bab800000000088705a8a000a6eae000000000233c168fc0029bab80000000009a705a0a800a6eae0000000002a4e15f3e0029bab8000000000b9ec57bc000a6eae00000000037da1f87c0029bab83903904b03903904b17d67d05a629f4092830f3e) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P30 : WideCovered band 9989784 10751304 := wide_block_sound band profiles_RelativeWidePack6815_P30 9989784 10751304 (wideData 16 0x69ce806df6e004b74f00000000001e2c912962004b74f00000000002eacc01ae998012dd3c0000000001a5830134d2f004b74f08200208007a7e841c66d74004b74f00000000009978067c240029bab8000000000ac7406eeaa0029bab80000000009fa4068e3c0029bab0000000000cd01a70d800a6eae0820020807bc064b6a0029bab800000000088bc0618be0029bab80000000008b30061a6e0029bab80000000009df006897c0029bab800000000099a40629ec0029bab80000000009da0062dfe0029bab83a03a04b03a03a04b1b83da05dea9e20938fe8fa) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P30 : WideCovered band 10751305 11911718 := wide_block_sound band profiles_RelativeWidePack6815_P30 10751305 11911718 (wideData 16 0x82002080730c08a24d0012dd3c000000000067f301b38f2004b74f00000000001a2be06bfcd0012dd3c00000000006aae01f08e4004b74f02080082010aa816dba6004b74f0000000000186fc0587ac0012dd3c000000000067a6817edb2004b74e80000000001933e0582bc8012dd3c0820020800e0a04a7ee0012dd3c000000000061afc134d72004b74f0000000001eff80f5e24004b74f00000000001879903cb2f0012dd3c082002080071e44d65a8012dd3c0000000006a4d02bafd8012dd3c00000000073990296898012dd3a0f20f212c0f20f212c063aeaf07da59fe094d34a6c) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P30 : WideCovered band 11911719 12636975 := wide_block_sound band profiles_RelativeWidePack6815_P30 11911719 12636975 (wideData 10 0x2c65f0f86590012dd3a0000000000b5f303fd9be004b74f02080082001ebfc0deb9d0012dd3c00000000007eeac2eda30004b74f000000000028f2f0ca6690012dd3a00000000007cd382b8d76004b74f020800820019a8b09f2f88012dd3c000000000076ab0274e32004b74f00000000001c3b908b63a8012dd3a0fa0fa12c0fa0fa12c072af8c0aaa7de8096eeede8) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 7995322 8883764 12636975 c0_RelativeWidePack6815_P30 (wide_covered_join band 8883765 9409576 12636975 c1_RelativeWidePack6815_P30 (wide_covered_join band 9409577 9989783 12636975 c2_RelativeWidePack6815_P30 (wide_covered_join band 9989784 10751304 12636975 c3_RelativeWidePack6815_P30 (wide_covered_join band 10751305 11911718 12636975 c4_RelativeWidePack6815_P30 c5_RelativeWidePack6815_P30)))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 9)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 9≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤61)
    (hT0 : 3810≤T) (hT1 : T≤4117) (hnu : 7995322≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤21629505182317249 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R180

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R181
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨9,62,3753,4086,25699543428999619⟩
private def profiles_RelativeWidePack6815_P30 : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨43768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P30 : WideCovered band 8126393 8932801 := wide_block_sound band profiles_RelativeWidePack6815_P30 8126393 8932801 (wideData 16 0x2ce52a6900063e6e0820020800bc94aae20018f9c000000000068a417c880063e6e0000000001b0e05d760018f9c0000000000787816df00063e6e0820820821a1df7e418eb87ecc2063e700000000001e7c245fcdf00029f2f80000000003f3fb305e7ae5e8012f97c082002080061a74e06c7ac62004be5e8000000000ae72901f6cb34004be5f00000000009f34c01e2a97c004be5f000000000058ee81abe0f0012f97c0820020800eaee46e296c004be5f00000000001d6eb078a9c0012f97c000000000063ee4071bfe004be5f02e02e04b02e02e04b13860b03f3ebfa00fd2f86c) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P30 : WideCovered band 8932802 9372659 := wide_block_sound band profiles_RelativeWidePack6815_P30 8932802 9372659 (wideData 16 0x57580f9f80029f2f80000000015a7c37bc000a7cbe0000000001f3c0be7e0029f2f0000000000eef8169c000a7cbe00000000006a978474ac00a7cbe0000000000738a43f68400a7cbe0000020800f4ca0073bf30029f2f84100082007ea1e4cf758000a7cbe0000000001b4f099be0018f9b8000000000793c268d80063e700000000001f6d09ab20018f9b80000000005ca426da00063e70000000000065c49c2c0018f9b80000000001b7d274800063e6e000000000077f49e300018f9b83803804b83803804b978f4c04e2a86e0918aad72) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P30 : WideCovered band 9372660 9959138 := wide_block_sound band profiles_RelativeWidePack6815_P30 9372660 9959138 (wideData 16 0x1a8b0187ff000a7cbe0000000002758418e1e000a7cbe0820020801ed81ae300029f2f00000000009d3867fe000a7cbe0000000002aae1a9200029f2f8000000000b9686aac000a7cbe000000000326a1ad2c0029f2f8000000000dbf86e2f000a7cbe0000000002279139260029f2f80000000006e316bc9000a7cbe0820020801b5d5bc260029f2f8000000000aea04b9a800a7cbe0000000002ff912aa60029f2f8000000000dbbc478d000a7cbe0000000003edb118f80029f2f83903904b83903904b999739059b3c6a091fa9ca4) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P30 : WideCovered band 9959139 10545616 := wide_block_sound band profiles_RelativeWidePack6815_P30 9959139 10545616 (wideData 16 0x2e9901b2bf000a7cbe0000000002bb8019f29800a7cbe0820020801e6a41b78c000a7cbc00000000026de01965e800a7cbe000000000277b0196e8000a7cbe0000000002a2d019799000a7cbe0000000002aff019a7a800a7cbe0000000002bfe019ba9800a7cbe0000000002f2c019f2a800a7cbe0000000001a7e41a319000a7cbe08200208013bf01872f800a7cbc000000000269e1fdf80029f2f800000000099687308000a7cbe000000000276d1cf7c0029f2f8000000000aef0060cb40029f2f83a03a04b83a03a04b9cf30b05cea9fa0938a3862) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P30 : WideCovered band 10545617 11718573 := wide_block_sound band profiles_RelativeWidePack6815_P30 10545617 11718573 (wideData 16 0x1af9f069a2c8012f97c00000000006dbf81a5e2e004be5e8208008200cea0176f6c004be5f00000000001938e04e7ea8012f97c00000000006486c12992c004be5f000000000019a7a0493bc8012f97a00000000032be04dbbf0012f97c0820020805ba803ce488012f97c0000000000639b00e9f6c004be5f000000000019f1803967d8012f97a000000000068d24079866004be5f00000000001e67a02aed90012f97c0000000001b3f428a5e0012f97c000000000327d0192bf0012f97c0000000000ffe6c076b33004be5f03d03d04b83d03d04b9fea9d07cf0972094a248bc) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P30 : WideCovered band 11718574 12818220 := wide_block_sound band profiles_RelativeWidePack6815_P30 11718574 12818220 (wideData 15 0x3b34912ba7b0012f97a0000000000e8ca4474a62004be5f020800820028a2d0e9b6b8012f97c0000000000b38ec37bcbe004be5f00000000002c60e0db31e0012f97a0000000000a9d64360e60004be5f02080082001d2da0aebfe8012f97c0000000000a0a382abd72004be5f00000000001e6cd08fb0e8012f97a0820020800688f4276be2004be5f00000000001cfbf088ebe8012f97c0000000000748601ff8ec004be5f00000000001d38f07f3bf0012f97c0820020805fba078f9f8012f97c0f80f812e0f80f812e072abfd09b36938096bf7836) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8126393 8932801 12818220 c0_RelativeWidePack6815_P30 (wide_covered_join band 8932802 9372659 12818220 c1_RelativeWidePack6815_P30 (wide_covered_join band 9372660 9959138 12818220 c2_RelativeWidePack6815_P30 (wide_covered_join band 9959139 10545616 12818220 c3_RelativeWidePack6815_P30 (wide_covered_join band 10545617 11718573 12818220 c4_RelativeWidePack6815_P30 c5_RelativeWidePack6815_P30)))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 9)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 9≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤62)
    (hT0 : 3753≤T) (hT1 : T≤4086) (hnu : 8126393≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤25699543428999619 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R181

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R182
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨9,63,3697,4055,25060987511787660⟩
private def profiles_RelativeWidePack6815_P30 : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨43768,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P30 : WideCovered band 8257464 8961355 := wide_block_sound band profiles_RelativeWidePack6815_P30 8257464 8961355 (wideData 16 0x2b3d321a80064976000000000060c06efc001925e000000000019b01b3e000649760000000000fed4d862001925e0000000001ce06d72001925d800000000018ec1adc000649780820020801f0c07cb0001925d82084082105921fe96eb9228420649760000000001ec9e05ffbec002a2bb80000000003877bf443483dc80130dbc08200208077cb7016ed35d80130dbc0000000003a2aa40aa97ad00130dbc0000000001b49ac060fa9d80130dbc0000000001f0fa4065bf6880130dbc082002080064a2036a8f0004c36f02e02e04b02e02e04b1882dd049edf3a00ff30caa) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P30 : WideCovered band 8961356 9405918 := wide_block_sound band profiles_RelativeWidePack6815_P30 8961356 9405918 (wideData 16 0x528910ab4002a2bb80000000018ba03e7a000a8aee000000000729b12d400a8aee0000000000609202678000a8aee000000000564904e3a002a2bb80000000001f77f1ccff002a2bb80000082002bb4d1cbe3002a2bb841000820079b2a4cb62b800a8aec0000000001a8e07b6c001925d80000000006da41e9f800649780000000001fae0b8f0001925d80000000007dfc1e888006497800000000022ca078b4001925d80000000007b382f0900064978000000000062c0783c001925d83803804c03803804c18c3ab04dbeff0091922eae) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P30 : WideCovered band 9405919 9998668 := wide_block_sound band profiles_RelativeWidePack6815_P30 9405919 9998668 (wideData 16 0x329d1f832002a2bb8000000000d8bc7b0a800a8aee000000000224841920b000a8aee0820020804b96fd9000a8aee0000000002a8b189bc002a2bb8000000000bbf46bf9800a8aee0000000002ebb159a0002a2bb8000000000d9ec672f000a8aec0000000003bfa1bdfc002a2bb8000000000f9e84bff800a8aee0000000000f2f5ccb8002a2bb80000000008ae177db000a8aee0820020800e9b0fdfc002a2bb8000000000db644e0a800a8aee0000000003e3d12ca0002a2bb83903904c03903904c1bc7ef05962c7a09282ba68) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P30 : WideCovered band 9998669 10628464 := wide_block_sound band profiles_RelativeWidePack6815_P30 9998669 10628464 (wideData 16 0x20800820026ede9074ff8a00130dba000000000333d01ba5b800a8aee0000000002f9f019f6c000a8aee0000000003e106fde2002a2bb82080082004aac069a72002a2bb80000000009d340609be002a2bb8000000000b964066e2c002a2bb8000000000bcf8067a28002a2bb0000000000af34060ee4002a2bb8000000000ce3c068bbc002a2bb80000000002824069874002a2bb82080082003a3d060ea6002a2bb8000000000aa7c060cb6002a2bb8000000000ac387ec8800a8aee0000000002add1bfea002a2bb83a03a04c03a03a04c1fbe3d05ca2976093931824) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P30 : WideCovered band 10628465 11813965 := wide_block_sound band profiles_RelativeWidePack6815_P30 10628465 11813965 (wideData 16 0x208008201ac701e0cb6004c36e80000000001b25b05cfad80130dbc00000000006dbe0170e7a004c36f0000000000192dc06cf1980130dbc082002080574a04bf6e00130dba000000000065fac123ca2004c36f00000000001baae0587ad00130dbc00000000006caa80fee60004c36f02080082008bed0f8b28004c36e800000000019f7803d2ad00130dbc000000000065f640abebe004c36f00000000001affa01fa4a80130dbc00000000007fa7c0be8f8004c36f00000000002b6f813972004c36f00000000003feb901c23bc0130dbc0f40f41300f40f4130060eb6b07d3092a094b67b7c) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P30 : WideCovered band 11813966 12999465 := wide_block_sound band profiles_RelativeWidePack6815_P30 11813966 12999465 (wideData 16 0x58aeb19d22b00130dba0820020800efba0538c6a004c36f00000000003cf3d11fbcb00130dbc0000000000f7bf84b1d64004c36f00000000003926e10cb8c00130dba0820020800ab934370baa004c36f00000000002e3a80dbecd00130dbc0000000000b7a28363cec004c36f02080082001db8c0bb77e00130dba0000000000a3a7827d9a8004c36f00000000002a2690acebd80130dbc0000000000a1e7826bae2004c36f0208008200186fc089a1b80130dba00000000007bab822e93c004c36f00000000001d73f07a36880130dbc0fa0fa1300fa0fa130077eadc09cfaee0096d72ef6) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8257464 8961355 12999465 c0_RelativeWidePack6815_P30 (wide_covered_join band 8961356 9405918 12999465 c1_RelativeWidePack6815_P30 (wide_covered_join band 9405919 9998668 12999465 c2_RelativeWidePack6815_P30 (wide_covered_join band 9998669 10628464 12999465 c3_RelativeWidePack6815_P30 (wide_covered_join band 10628465 11813965 12999465 c4_RelativeWidePack6815_P30 c5_RelativeWidePack6815_P30)))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 9)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 9≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤63)
    (hT0 : 3697≤T) (hT1 : T≤4055) (hnu : 8257464≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤25060987511787660 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R182

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R183
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨9,64,3643,4023,24179780214681943⟩
private def profiles_RelativeWidePack6815_P30 : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨44018,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P30 : WideCovered band 8388535 8987556 := wide_block_sound band profiles_RelativeWidePack6815_P30 8388535 8987556 (wideData 16 0xbbec173800064c7e00000000032db039e8001931f8000000000dde4069e80064c7e000000000425e03fe2001932800000000012c780e9800064c7e00000000052f804c7b00193280000000200d9fc5ae001931f8000000000f8a86f500193280000000001cde4332f40064c7e10418408612aaf1b54c60975081932800000000017c37d449eff3d002a63f80000000003b6e97846c931e001329fc0820020805608780f4f34e001329fa00000000026fd6006d82ec001329fc000000000276aec06e8a4c801329fc0ba0ba12c0ba0ba12c061b24d05ca2cf60109328e8) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P30 : WideCovered band 8987557 9324506 := wide_block_sound band profiles_RelativeWidePack6815_P30 8987557 9324506 (wideData 16 0x20800f5cf806afab002a63f841000820089f694db70f000a98fc000000000238d0ad6a001931f80000000005bfc2ba880064ca0000000000072a06bfc001931f800000000018e12e0880064ca000000000006eb4b9e2001931f80000000001c701a8c80064ca00000000000a0f4bc2a001931f80000000002d652fdd80064ca008200208006bc0a826001931f80000000006efc0e7c80064ca0000000000223c06de8001931f80000000008e341b1e00064ca0000000000238a01fb0001931f83803804c83803804c9a92ca04d7ca78091976b28) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P30 : WideCovered band 9324507 9923528 := wide_block_sound band profiles_RelativeWidePack6815_P30 9324507 9923528 (wideData 16 0x3a9917fb2002a63f8000000000efb0060fe6002a63f0000000000382162ec000a98fe0000000001bab5df20002a63f82080082006f285e6c800a98fe00000000033890ff20002a63f8000000000fe3c5f48800a98fe00000000042290e97c002a63f80000000014ae05e39800a98fe00000000057cc0bdf2002a63f0000000001abf0268e000a98fe0000000000f7d14d7a002a63f80000000011dac0e4b800a98fe00000000022f910e64002a63f80000000001a26d0be31002a63f83983984c83983984c99be2e05927d60091eed872) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P30 : WideCovered band 9923529 10522550 := wide_block_sound band profiles_RelativeWidePack6815_P30 9923529 10522550 (wideData 16 0x373d01b25f800a98fe000000000339f019759000a98fc0000000002e4901b74b800a98fe0000000001e99419e7f000a98fe08200208023a91f8ea002a63f8000000000c8e8064f64002a63f8000000000bab87b19800a98fe000000000369f0197ab000a98fe00000000033681f8fc002a63f8000000000dc6c7ecb000a98fc0000000000aab41a27f000a98fe0820020800ef85f8aa002a63f8000000000bf2c7bbd000a98fe0000000002e8c188f6002a63f8000000000c8645faf000a98fe0e80e81320e80e8132060bead05b6cb7a092fff82e) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P30 : WideCovered band 10522551 11533400 := wide_block_sound band profiles_RelativeWidePack6815_P30 10522551 11533400 (wideData 16 0x74d78165a32004ca7f02080082002af013efe6004ca7f00000000001a76903e3ac001329fa00000000006cab40eef64004ca7f00000000001b2ba02aa8a801329fc00000000007bf200e2fb0004ca7f00000000015e280b9864004ca7e8000000000a8210a9930004ca7f02080082001d61813ca4004ca7f030c00c300cda9808b6fac01329fc208008200228965078bed8801329fa0000000002bbf01d319800a98fe082002080126e41b21a800a98fe0000000002f0b019bcf800a98fe000000000326801a389800a98fe0ec0ec1320ec0ec132064fb2805fb5876094930fea) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P30 : WideCovered band 11533401 12731444 := wide_block_sound band profiles_RelativeWidePack6815_P30 11533401 12731444 (wideData 16 0x3ba4c0fcfeb801329fc0000000000eac783e2be2004ca7f020800820028a4c0ccf09001329fa0000000000adae02b1dfe004ca7f00000000002d3580bc799001329fc082002080076c782be9ba004ca7f00000000002929f0996ba001329fa0000000000a496823fa38004ca7f000000000028bae08c71f801329fc0820020806fc8079a3a801329fc000000000077cfc1bfa62004ca7e80000000001e35c06f2c9001329fc00000000007ada01bbce4004ca7f02080082010a641a1bec004ca7f00000000001a60904a73f801329fa0f80f81320f80f8132075caab08d7c9e4096930b6c) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P30 : WideCovered band 12731445 13180710 := wide_block_sound band profiles_RelativeWidePack6815_P30 12731445 13180710 (wideData 6 0x6a63a1dc6fa001329fa08200208012eb3c62ee7c004ca7f00000000004e62816a3cf001329fc00000000012d82c52aff6004ca7f02080082003962e11fab8801329fa1201201321201201320b78e4e0dcf0b2c098b74ae4) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8388535 8987556 13180710 c0_RelativeWidePack6815_P30 (wide_covered_join band 8987557 9324506 13180710 c1_RelativeWidePack6815_P30 (wide_covered_join band 9324507 9923528 13180710 c2_RelativeWidePack6815_P30 (wide_covered_join band 9923529 10522550 13180710 c3_RelativeWidePack6815_P30 (wide_covered_join band 10522551 11533400 13180710 c4_RelativeWidePack6815_P30 (wide_covered_join band 11533401 12731444 13180710 c5_RelativeWidePack6815_P30 c6_RelativeWidePack6815_P30))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 9)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 9≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤64)
    (hT0 : 3643≤T) (hT1 : T≤4023) (hnu : 8388535≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤24179780214681943 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R183

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R184
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨9,65,3591,3991,23939258742771510⟩
private def profiles_RelativeWidePack6815_P30 : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨44268,250,10158⟩
  | 2 => ⟨25549,195,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P30 : WideCovered band 8519606 9011407 := wide_block_sound band profiles_RelativeWidePack6815_P30 8519606 9011407 (wideData 16 0x16e781a0cc0064fa600000000076f909ba100193ea0000000001a8b00e8ac0064fa60000000000788bc5f8ec0064fa808200200022a82ac41a7de61dc3064fa600000000013bb7813297200193ea00000000003daea05a3eac0064fa60000000000a88744adbb700193ea00000002007f28a3006ada2bee08193e98000000000ac700b98404af904108102207aa0cb9061abbbbf092be40000000000fbafab129278a4002a7cb00000000015f6ad43db5af9002a7cb82080082002c32d6832cf2ed80133e3c000000000560cec0e0e23b80133e3c0ba0ba12c0ba0ba12c075cbd9088a393e010b33d26) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P30 : WideCovered band 9011408 9314054 := wide_block_sound band profiles_RelativeWidePack6815_P30 9011408 9314054 (wideData 16 0x2080082004d241fcf00064fa60000000001eab06cac00193ea00000000007e781abb00064fa600000000022c80692400193ea0000000000983c17bb80064fa60000000002ae9098ac00193ea0000000000aef81aaa00064fa60000000002f7f058aa00193ea0000000000cff8134980064fa60000000003b080492000193ea0000000000ef780efb80064fa6000000000225902dbc00193e980000000009d30078a00064fa60000020802f1e12b00064fa80000030003a580182b00193e983883884d03883804d18e35d04da2e2c0919e5ae6) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P30 : WideCovered band 9314055 9843686 := wide_block_sound band profiles_RelativeWidePack6815_P30 9314055 9843686 (wideData 16 0x12de44e3d000a9f2e000000000570f129fc002a7cb80000000010c60467a800a9f2e0000000000fca12db4002a7cb00000000001d656ace800a9f2e0000000001f280dd6c002a7cb8000000000bdbc2aaa800a9f2e00000000052ba04aaa002a7cb80000000001a3dd089fb002a7cb80080000003a3dc01af0b400a9f2e0000020801bacb80b5a37002a7cb8408008200bb7ff4f9f0f800a9f2c0000000004ed2afe80064fa60000000006e92b3c00064fa800000000006594ae2e00193e983903904d03903904d1dce9a04e33a6c091e74bb4) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P30 : WideCovered band 9843687 10448980 := wide_block_sound band profiles_RelativeWidePack6815_P30 9843687 10448980 (wideData 16 0x3b09019a9f800a9f2e0000000003f6901a339800a9f2e0000000000f9c019379800a9f2e0000000001e0d419709800a9f2c0820020802eda1cba0002a7cb8000000000caf0726a000a9f2e000000000363a1c968002a7cb8000000000fcf00648b2002a7cb8000000000f9bc738d000a9f2e000000000433d1d87a002a7cb80000000002ee976ea800a9f2e00000000016cc5e872002a7cb02080082006b286229800a9f2e0000000003e2e1c8b8002a7cb8000000000f82c5398800a9f2e0e80e81340e80e81340618aad05a65bee092ee3eba) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P30 : WideCovered band 10448981 11243427 := wide_block_sound band profiles_RelativeWidePack6815_P30 10448981 11243427 (wideData 16 0x82002080771c01ef9980133e3a00000000007bbf40acde4004cf8f00000000002864a028a5004cf8f00000000002f79b02ab39c0133e3c186006180062930075cfbb80133e3a0820020801bab01b28e800a9f2e00000000033ea01a6eb800a9f2e00000000036a901a73f000a9f2c000000000378801a7bc800a9f2e0000000003a8f01aa88800a9f2e00000000042fa01cadd000a9f2e000000000062941af8a000a9f2c0820020800b7b019e6b000a9f2e000000000325c018b6f000a9f2e000000000334d018bad000a9f2e0ec0ec1340ec0ec134065ee2805e38e34094822876) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P30 : WideCovered band 11243428 12454015 := wide_block_sound band profiles_RelativeWidePack6815_P30 11243428 12454015 (wideData 16 0x2ba6a09e79f80133e3a0000000000b6bb42bb8e2004cf8f02080082001b62b09a2ed00133e3c00000000007ece81f0ae2004cf8f000000000029b1d08be3f00133e3a0000000000a092c1e7ab8004cf8f02080082018ff81bc8e0004cf8f00000000001e36806aebf80133e3c000000000076dac176dfc004cf8e80000000001defd05ae2d80133e3c0000000003f0a05a7b900133e3c08200208006be2c160af8004cf8f00000000001bb2b03de9e80133e3a000000000072e2c0efc26004cf8f000000000028bac04d3cd80133e3c0f80f81340f80f8134071bbae08829a78095cbbce2) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P30 : WideCovered band 12454016 13361955 := wide_block_sound band profiles_RelativeWidePack6815_P30 12454016 13361955 (wideData 12 0x820020801e9ee0064afed80133e3a0000000001a7cf86ee8a0004cf8f00000000005eb7a19c3dc80133e3a000000000175d38637c32004cf8f0208008200483bf159e2880133e3a000000000127bfc4a69f4004cf8f000000000048a3f11aa6c00133e3c0820020800e7c7846f962004cf8f000000000039a890db73d80133e3a0000000000e3cb033d9be004cf8f00000000003afd90dffbb80133e3c1201201341201201340acef390bbafba8097f3883a) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8519606 9011407 13361955 c0_RelativeWidePack6815_P30 (wide_covered_join band 9011408 9314054 13361955 c1_RelativeWidePack6815_P30 (wide_covered_join band 9314055 9843686 13361955 c2_RelativeWidePack6815_P30 (wide_covered_join band 9843687 10448980 13361955 c3_RelativeWidePack6815_P30 (wide_covered_join band 10448981 11243427 13361955 c4_RelativeWidePack6815_P30 (wide_covered_join band 11243428 12454015 13361955 c5_RelativeWidePack6815_P30 c6_RelativeWidePack6815_P30))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 9)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 9≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤65)
    (hT0 : 3591≤T) (hT1 : T≤3991) (hnu : 8519606≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤23939258742771510 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R184

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R185
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨9,66,3497,3507,25879962036737552⟩
private def profiles_RelativeWidePack6815_P30 : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨25596,196,5079⟩
  | 2 => ⟨25648,193,5079⟩
  | 3 => ⟨25694,190,5079⟩
  | 4 => ⟨44518,250,10158⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P30 : WideCovered band 8650677 8975571 := wide_block_sound band profiles_RelativeWidePack6815_P30 8650677 8975571 (wideData 16 0x5a10fcb7ca40065ab00000000000b8cbc570efac00065aae000000000273e199b9f004b5982080082005d24a5abedf23092d680c30030c01b4c3c6b39e4f03065aae000000000475f069b18404b5a02080082006f30a5a9a8835092d680c30030c0173d3e5b99fb883065aae0000000001acd3d1a492cb404b5a02080082003c3ac83a39f824b5a000000000038b0123c6c012d6610428410a6eca41b318e2092d680000000000a1fb42fa922f80065ab0000000000078a342a2afcb800aad3e00000000013ee41a33aab002ab4f82f02f04b02f02f04b02ea1810db38ac010d35964) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P30 : WideCovered band 8975572 9281354 := wide_block_sound band profiles_RelativeWidePack6815_P30 8975572 9281354 (wideData 16 0x4601b9800065ab00000000004bc62d00196ab80000000016a1a940065aae0000000006f00a3a80065aae000000000060d0782f00196ac00000000001aa40e900196ab80000000001d703effc0065ab00000000000aa80997700196ab80000000003a64063b7700196ac00000000002ea1c419b9c23ec2065aae0820020800fbbe107efb8fc2065ab00000000002e9901bbaf2400196ab80000000004d340a69fd00196ac00000000003f603ecc7100196ab80000000002f7c063828e40065ab00e20e21360e20e21361a7be406dd7bb6611193fdf4) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P30 : WideCovered band 9281355 9606248 := wide_block_sound band profiles_RelativeWidePack6815_P30 9281355 9606248 (wideData 16 0x4100104013e663bdc2c002ab4f8000000000ab0e8a800196ab8000000000ac09b3000196ab82080082001d613a4b00065aae00000000017417e980065ab00000000001a8269c80065aae0000000001a4170b80065ab00000000001bc1e5900065aae0000000001ec1bd800065ab00000000001f4130e80065aae000000000260234a00065ab00000000002600f8b00065aae0000000002bc226f80065ab00000000002e40b7a80065aae0000000003681f4e80065ab00e40e41360e40e413656ec04d79de0211df4fe2) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P30 : WideCovered band 9606249 10217813 := wide_block_sound band profiles_RelativeWidePack6815_P30 9606249 10217813 (wideData 16 0x208008201c85ed38002ab4f8000000000b918cf6002ab4f0000000000c818afc002ab4f8000000000da18938002ab4f8000000000dc10c6a002ab4f80000000010814fb0002ab4f80000000013816d34002ab4f80000000016a16a38002ab4f8000000001af15f3e002ab4f8000000000187856dc800aad3c00000000006e954eea002ab4f82080082011e4aca4002ab4f80000000014e07926002ab4f80000000019a038ec002ab4f0000000000182016fcc00aad3e0e80e81360e80e81365afb05920ea6212b34eee) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P30 : WideCovered band 10217814 10829379 := wide_block_sound band profiles_RelativeWidePack6815_P30 10217814 10829379 (wideData 16 0xdc01bbfa800aad3e0820020802f5068b64002ab4f0000000000af019b58000aad3e0000000002e4066f38002ab4f8000000000bf019e89800aad3e000000000324067e22002ab4f8000000000d801a2d8800aad3e00000000037c069a28002ab4f82080082010a41937d800aad3e0000000002a47b3c800aad3c0000000002a06a7b800aad3e0000000002f0060828002ab4f8000000000cc018298000aad3e00000000036c060da0002ab4f8000000000ed01868e800aad3e0ec0ec1360ec0ec1366f9b05b6cce6213c7faa8) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P30 : WideCovered band 10829380 11861396 := wide_block_sound band profiles_RelativeWidePack6815_P30 10829380 11861396 (wideData 16 0x8200208016816debe004d69f00000000001ae813e97a004d69f00000000001a340f8d2e004d69e80000000001c7812dc66004d69f00000000001eb4131d62004d69f0208008201db438e5b80135a7c00000000006cb02cf5b00135a7a000000000073d01db1f00135a7c00000000007ea14937004d69f00000000003a3c06db7b004d69f08200208016841de8dbe004d69e8000000000bc01b7fa000aad3e0000000002f806ea2a002ab4f8000000000ca01bb3e800aad3c00000000033406f932002ab4f83c03c04d83c03c04d81828905ffbbe0214de9e64) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P30 : WideCovered band 11861397 13084527 := wide_block_sound band profiles_RelativeWidePack6815_P30 11861397 13084527 (wideData 16 0x121815921b00135a7c0820020800b5b11e2f880135a7c0000000000e290fe7dd00135a7a0000000000bae0eb26980135a7c0820020800a3b0ec39c80135a7c0000000000adb0c974e00135a7c0000000000ac80be6aa00135a7a0000000000abc0bc26f80135a7c082002080060e08dbde00135a7c00000000007cd09836b00135a7c00000000007d808ebcd00135a7a00000000007e908e20c00135a7c08200208052c1e4ee8004d69e80000000001afc174f2a004d69f00000000001cf01b4fa4004d69e83f03f04d83f03f04d81c27d09822834216e348e4) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P30 : WideCovered band 13084528 13543200 := wide_block_sound band profiles_RelativeWidePack6815_P30 13084528 13543200 (wideData 6 0x2080082006e2c069826e80135a7a0000000001aec018b9ee0004d69f00000000005fb07ffaa6004d69e82080082004a646b8c7c004d69f00000000004b785f1970004d69e84904904d84904904d82d36e0f928ea62198e983a) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8650677 8975571 13543200 c0_RelativeWidePack6815_P30 (wide_covered_join band 8975572 9281354 13543200 c1_RelativeWidePack6815_P30 (wide_covered_join band 9281355 9606248 13543200 c2_RelativeWidePack6815_P30 (wide_covered_join band 9606249 10217813 13543200 c3_RelativeWidePack6815_P30 (wide_covered_join band 10217814 10829379 13543200 c4_RelativeWidePack6815_P30 (wide_covered_join band 10829380 11861396 13543200 c5_RelativeWidePack6815_P30 (wide_covered_join band 11861397 13084527 13543200 c6_RelativeWidePack6815_P30 c7_RelativeWidePack6815_P30)))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 9)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 9≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤66)
    (hT0 : 3497≤T) (hT1 : T≤3507) (hnu : 8650677≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤25879962036737552 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R185
end MergedPart2
section MergedPart3
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R186
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨9,66,3536,3958,27350167341865496⟩
private def profiles_RelativeWidePack6815_P31 : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨25596,196,5079⟩
  | 2 => ⟨25648,193,5079⟩
  | 3 => ⟨44518,250,10158⟩
  | 4 => ⟨26750,142,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P31 : WideCovered band 8650677 8937348 := wide_block_sound band profiles_RelativeWidePack6815_P31 8650677 8937348 (wideData 16 0x98aad59e72a804b59800000000038efe44a309804b5a00000000010b750a6a7c012d660000000000f3a305ac8404b5a0000000000acb8f05921dc04b5a00000000017a24b0cc218404b5a00000082001c6ef286ba9ef012d660000000006b59a607d8a0ac04b5a000000c300ae7cfbd177d6a9c04b5a02080082004d3997a67cf23092d68000000000122828129c72012d6610428410a0648f2d41abbdac092d680000000000b6fede0bfa4db600196ac00000000002aa6be42a5e73c800aad3e0000000001b1aa5068f3ff400aad3e0bc0bc12c0bc0bc12c0f6dec810f22d2e010d35964) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P31 : WideCovered band 8937349 9243131 := wide_block_sound band profiles_RelativeWidePack6815_P31 8937349 9243131 (wideData 16 0x2fda11b80065aae0000000002a6a03e3800196ab80000082013e74160fc0065ab00000000003ad902be200196ab8000000000183390c9f700196ac0000000001c8a8135b40065aae0000030000a0830760d40065ab00020000000a7bf06bba40065aae080002000230ee6a41a64d2cfc2065ab00000000003bca6406fc3cb80065aae0000000001a3fe407d9a500196ac00000000005939d0f93dec0065aae0000000000fbeb8062eb1d40065ab00000000000a1eb40a2c75ac0065aae00000000073fd43f2f9e500196ac03883884d83883884d8897cfa4074861a381118b58b6) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P31 : WideCovered band 9243132 9548914 := wide_block_sound band profiles_RelativeWidePack6815_P31 9243132 9548914 (wideData 16 0xdb4a86200196ab82080082005aa42bd880065aae0000000001e5a06a3c00196ac00000000008af4275f00065aae000000000223b05f2e00196ac000000000098a81f2c00065aae000000000277a07aee00196ac0000000000a87c13fd00065aae0000000002fba0997a00196ac0000000000bfec12a880065aae0000000003a6908efe00196ac0000000000a8600ed800065aae0000000000f2a08bb800196ac00000000008a380a5b00065aae000000000135c07eaa00196ac03903904d83903904d9cbbe904db9c7e191d6aaa4) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P31 : WideCovered band 9548915 10141368 := wide_block_sound band profiles_RelativeWidePack6815_P31 9548915 10141368 (wideData 16 0x3fcd198ea002ab4f80000000011b6463ec000aad3e000000000478f11af4002ab4f80000000015a2c57df000aad3e00000000032ac17e72002ab4f8000000000186c5f49000aad3e0000000004705f1b800aad3e0000000000b95efa000aad3c082002080365910bac002ab4f80000000016ff42e2c800aad3e0000000006ea908b30002ab4f8000000000186ef04d3c002ab4f00000000001aa4b03c69002ab4f80000000001daba19e3f002ab4f820800820049fcd4bce7b000aad3e0e60e61360e60e61360609a6904eb39b01929ffc72) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P31 : WideCovered band 10141369 10752934 := wide_block_sound band profiles_RelativeWidePack6815_P31 10141369 10752934 (wideData 16 0xe9e4067aa2002ab4f8000000000ee34067cb4002ab4f8000000000fb78067fe0002ab4f800000000109b8068c20002ab4f8000000000dc240699ae002ab4f80000000006be106a8e8002ab4f82080082006e74063dfa002ab4f8000000000dba47e7b000aad3c000000000365a1aebe002ab4f8000000000fa64060dba002ab4f80000000010abc061866002ab4f80000000011d28061c24002ab4f80000000002d2c062968002ab4f80000000005ea90638a8002ab4f82080082006eb873ea000aad3e0ea0ea1360ea0ea136065932a05b62e64193b6a82c) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P31 : WideCovered band 10752935 11708504 := wide_block_sound band profiles_RelativeWidePack6815_P31 10752935 11708504 (wideData 16 0x1d74903ee3d80135a7a0000000000a1bf4130ca2004d69f0208008200ce79133e3a004d69f00000000001cf2e038bb800135a7c00000000007ab740b6afa004d69e80000000002923b01e76c80135a7c0000000000b286442bb40135a7c00000000012aa6806786b004d69f0820020801d8710779ebf80135a7a0000000003e5b01bb5e000aad3e0000000003f3b01bbfa800aad3e000000000423a01bebd000aad3c000000000436901bfda000aad3e000000000334801aa4f800aad3e0000000001b6c41bf9e000aad3e0f00f01360f00f013606aae6f05fe0b60194cb4be8) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P31 : WideCovered band 11708505 12931635 := wide_block_sound band profiles_RelativeWidePack6815_P31 11708505 12931635 (wideData 16 0x486ad0fffcf00135a7a0000000000f7db03b1de6004d69f02080082002e38e0ed3cf00135a7c0000000000e686c32aaf4004d69f00000000003929e0bf7ec80135a7a0000000000e3d2c2f4ea6004d69f02080082001ae2f08e3dc00135a7c0000000000affe8264b34004d69f00000000002c2cc08fb3c80135a7a000000000076a3c23be78004d69f02080082001db5e079a3880135a7a000000000079e3c177c76004d69f000000000028fbe06e22c80135a7a000000000069eb01b7bbc004d69f0208008200192fb05ba4f80135a7c0fa0fa1360fa0fa13607d96bc08dbabbc196be9bec) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P31 : WideCovered band 12931636 13543200 := wide_block_sound band profiles_RelativeWidePack6815_P31 12931636 13543200 (wideData 8 0xe38038e001c61e751ffcaff02135a7a0000000002309ec0639adc00135a7c0000000001fba38060abde80135a7a082002080174ea06e0f66004d69f00000000005ebec17e79f80135a7a000000000172c305b39bc004d69f00000000005aa3c15afcf00135a7c1241241361241241360e4ea4f0df6ef2c198e7eb62) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8650677 8937348 13543200 c0_RelativeWidePack6815_P31 (wide_covered_join band 8937349 9243131 13543200 c1_RelativeWidePack6815_P31 (wide_covered_join band 9243132 9548914 13543200 c2_RelativeWidePack6815_P31 (wide_covered_join band 9548915 10141368 13543200 c3_RelativeWidePack6815_P31 (wide_covered_join band 10141369 10752934 13543200 c4_RelativeWidePack6815_P31 (wide_covered_join band 10752935 11708504 13543200 c5_RelativeWidePack6815_P31 (wide_covered_join band 11708505 12931635 13543200 c6_RelativeWidePack6815_P31 c7_RelativeWidePack6815_P31)))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 9)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 9≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤66)
    (hT0 : 3536≤T) (hT1 : T≤3958) (hnu : 8650677≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤27350167341865496 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R186

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R187
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨9,67,3448,3923,27280708727050568⟩
private def profiles_RelativeWidePack6815_P31 : ℕ → Profile
  | 0 => ⟨2984,24,635⟩
  | 1 => ⟨25596,196,5079⟩
  | 2 => ⟨25648,193,5079⟩
  | 3 => ⟨25694,190,5079⟩
  | 4 => ⟨44518,250,10158⟩
  | 5 => ⟨26750,142,5079⟩
  | 6 => ⟨26818,141,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P31 : WideCovered band 8781748 8994130 := wide_block_sound band profiles_RelativeWidePack6815_P31 8781748 8994130 (wideData 16 0x2ce1d42fb287d001976e0000000000b9abf01fe48af001976d80000000003fe9c245358bfb00065db80000000002b5ef00e4d404bba8000000000cdefa55a20c804bbb00000000008e37b03e69bc04bbb00000000010cefa08d34dc04bbb0000000001f8f38118ec8404bba80000082001e7c8e87f8ee9012eec0000000000added1bbd38012eec0000000000abd71bc2fb0b69012eec082000000134c39bc4f21d33092eea000000000121b280af96a012eec0000000001b68f833ef70012eec10430410c67ff350e99b6c824bbb02f02f04b02f02f04b098bda6c062eb3de0010eaba34) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P31 : WideCovered band 8994131 9303049 := wide_block_sound band profiles_RelativeWidePack6815_P31 8994131 9303049 (wideData 16 0x987c0ffc80065db80000000003e7f03ae9001976d8000000000cdec077e80065db80000000003e2b0d880065db60000000804a5c01a79001976e00000000016bac0f4ec0065db60000000007a5c08c35001976e00000000001c79f16cf5001976d80000003005c67a3506183faaf081976e00000000011c2ee02c78ff7001976d8000000001daa0f05f3c971001976e02080082005b33c7d066af5a02065db60000000003aedf0063bf9a00065db60000000000f6af4479a69001976d80000000001d3ba019348e7001976e03883884e03883884e09d7f97c06dc6feae1119a4afa) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P31 : WideCovered band 9303050 9631275 := wide_block_sound band profiles_RelativeWidePack6815_P31 9303050 9631275 (wideData 16 0x40801040088a1d4dbba9000abb6e0000000006e02eb800065db60000000005342f0800065db800000000033c2f5d80065db60000000000e02fd980065db80000000000acb07ebc001976d82080082002be427cd00065db8000000000273f07ab4001976d8000000000aa3c1e4f00065db80000000002e0e06fa4001976d8000000000bf381b6f80065db80000000002fbd01fa6001976d8000000000e87c17e880065db60000000003ef805c7a001976d80000000011938164900065db80e40e41380e40e4138060c66d04d2cdb0211e3fde8) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P31 : WideCovered band 9631276 10249112 := wide_block_sound band profiles_RelativeWidePack6815_P31 9631276 10249112 (wideData 16 0x39e90639ba002aedb82080082001cfd062df2002aedb8000000000fbe847ce000abb6e0000000004bab198fa002aedb800000000149705b99000abb6e00000000056af11c32002aedb8000000001a8a4621f000abb6c000000000534b0ed64002aedb80000000006e7c52cb800abb6e00000000017ed16a3a002aedb80000000012bbc169d800abb6c0000000002e1d12be4002aedb8000000000ebec42e9800abb6e002000000076d344a5cc00abb6e00000000007b82c22cfc00abb6c0ea0e81380ea0ea138060cac8058f2f3e212ba6c24) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P31 : WideCovered band 10249113 10866949 := wide_block_sound band profiles_RelativeWidePack6815_P31 10249113 10866949 (wideData 16 0x4aed01a7db800abb6e0000000000f9c41c3f8800abb6e082002080224d01af4b000abb6e0000000003bc801860e800abb6e000000000468a01a20a800abb6e0000000004a1c01a2ee000abb6e000000000460d01869c800abb6c000000000521d01a6fe800abb6e0000000000fc841aaee800abb6e0820020804f1061bb6002aedb800000000108e0060f2c002aedb00000000010fe40618b6002aedb800000000108ec675f800abb6e0000000004e880186f8000abb6e00000000053ae018a0a800abb6c0ec0ec1380ec0ec138069eb4f05b24e6c213cfd9be) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P31 : WideCovered band 10866950 11948164 := wide_block_sound band profiles_RelativeWidePack6815_P31 10866950 11948164 (wideData 16 0x2ae5d05ef2900136ebc08200208022ff05b6ee00136eba00000000007aea8126862004dbaf00000000002a2ba05974800136ebc0000000000a59b80f88a4004dbaf00000000001f76803b6db00136eba08200208037be44c74b80136ebc00000000007b8a4073ef2004dbaf000000000029a8b158a0004dbaf00000000003abff01930b80136eba0000000001308200f5eef004dbaf082002080098bd07adb1900136eba000000000475a01be3b800abb6e000000000471901b60a800abb6e000000000470a01ae09000abb6c0f00f01380f00f0138070c3d805fe2fa2214e73f78) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P31 : WideCovered band 11948165 13183838 := wide_block_sound band profiles_RelativeWidePack6815_P31 11948165 13183838 (wideData 16 0x1a5fe05758ec004dbaf00000000005f22914b3e800136eba082002080136a34528c76004dbaf00000000004c7080fca2e80136eba00000000012cce83bbd3e004dbaf00000000004a6ff0f83a900136eba0820020800b9d78337a66004dbaf00000000003b30c0b8bcc00136ebc0000000000ebaa42b7fb8004dbaf02080082002a3ad0bbe7e00136eba0000000000b5e6022c920004dbaf00000000002d78a08928e80136eba0000000000e1e2c268ee2004dbaf0208008201ff201e6a3e004dbae800000000029719068eac00136ebc0fc0fc1380fc0fc1380aad7d909968ab4216f7f8e4) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P31 : WideCovered band 13183839 13724445 := wide_block_sound band profiles_RelativeWidePack6815_P31 13183839 13724445 (wideData 7 0xce77e18ba39c2136eba30c00c30036eb651a5d74d82136ebc0820020802beaa006beb4880136eba0000000002ae8ec065c66d80136ebc00000000023b92c7f0fb8004dbae800000000089e2e1d921880136ebc126126138126126138126ba1910838d6e219a6cc38) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8781748 8994130 13724445 c0_RelativeWidePack6815_P31 (wide_covered_join band 8994131 9303049 13724445 c1_RelativeWidePack6815_P31 (wide_covered_join band 9303050 9631275 13724445 c2_RelativeWidePack6815_P31 (wide_covered_join band 9631276 10249112 13724445 c3_RelativeWidePack6815_P31 (wide_covered_join band 10249113 10866949 13724445 c4_RelativeWidePack6815_P31 (wide_covered_join band 10866950 11948164 13724445 c5_RelativeWidePack6815_P31 (wide_covered_join band 11948165 13183838 13724445 c6_RelativeWidePack6815_P31 c7_RelativeWidePack6815_P31)))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 9)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 9≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤67)
    (hT0 : 3448≤T) (hT1 : T≤3923) (hnu : 8781748≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤27280708727050568 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R187

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R188
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨9,68,3400,3888,27343798499367341⟩
private def profiles_RelativeWidePack6815_P31 : ℕ → Profile
  | 0 => ⟨25648,193,5079⟩
  | 1 => ⟨25694,190,5079⟩
  | 2 => ⟨25784,188,5079⟩
  | 3 => ⟨44768,250,10158⟩
  | 4 => ⟨26818,141,5079⟩
  | 5 => ⟨26809,139,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0_RelativeWidePack6815_P31 : WideCovered band 8912819 9185867 := wide_block_sound band profiles_RelativeWidePack6815_P31 8912819 9185867 (wideData 16 0x10cbae188ff8800668be00000000026e86c7609fb0019a380000000000afb3801ebcd310019a2f8000000000eee6903e369e70019a3800000000001b24fe80fea2ffc00668be08200208017bce9b418b9eaa0819a380000000000bf7cb15aafc800668be0000000000e494193ec350019a3800000000009f6ce02d22e400668be000000000264bb04f6f750019a38000000000099b4d449be8610019a2f80000000004970db04fce6f9800668e00000000002e5f683bef3c01386e0000000002aabfc0a3bf60138700000000002ec924134aab0138700e20e213a0e20e213a135a35d1dbe6ca6011832f34) (by decide +kernel)
private theorem c1_RelativeWidePack6815_P31 : WideCovered band 9185868 9497921 := wide_block_sound band profiles_RelativeWidePack6815_P31 9185868 9497921 (wideData 16 0x98780ef9000668be0000000002ab902d300019a380000000000c8a0071b800668be000000000228907e3a0019a38000000000108bc5ff0019a2f80000000013e2c0bca400668e000000208063c905e650019a2f80000000001829909ef50019a2f800000c001ca280abdc00668be0020000000799e85bdf400668e00000000000b6eec066ae10019a2f800c0003001fefbed73dd719420668e00000000000a3a3ca84b65f730019a2f82080082007c28bef0aeea3c020668e00000000001fcab00acb640019a2f83903904e83903904e87f6fab8063c66d30091c7b9f4) (by decide +kernel)
private theorem c2_RelativeWidePack6815_P31 : WideCovered band 9497922 9887989 := wide_block_sound band profiles_RelativeWidePack6815_P31 9497922 9887989 (wideData 16 0x1b20b06d37002b25f80000000001f66e01938002b25f0300000000d96cf06a22cc00ac97e102002080468b2547ef72002b25f800000000028b542cc000668be0820020801f8807ea20019a380000000000997c1e4a000668be000000000277b06f280019a380000000000aaf41b48800668be000000000323b0abe80019a380000000000bfac1a6d800668be00000000033dc05f280019a380000000000e87416fa800668be0000000003ebf0582a0019a3800000000007a60279a800668be0e60e613a0e60e613a062d74b04d72b7219293cde0) (by decide +kernel)
private theorem c3_RelativeWidePack6815_P31 : WideCovered band 9887990 10512098 := wide_block_sound band profiles_RelativeWidePack6815_P31 9887990 10512098 (wideData 16 0x3a3f019ee9800ac97e0000000003657e2d800ac97c0820020800f4941a378800ac97e00000000042eb16db6002b25f80000000011d2c57fe000ac97e00000000056b91df38002b25f8000000001593053ec800ac97e0000000006a281e82a002b25f8000000000fcec4f8e000ac97e0000000001eac12c60002b25f000000000018f07a88800ac97e000000000239910cb8002b25f82080082002a68778b800ac97e00000000063ac07930002b25f0000000001d8a40eee000ac97e0ea0ea13a0ea0ea13a066bb3d05927ae8192f7cd68) (by decide +kernel)
private theorem c4_RelativeWidePack6815_P31 : WideCovered band 10512099 11136207 := wide_block_sound band profiles_RelativeWidePack6815_P31 10512099 11136207 (wideData 16 0x13a3806e962002b25f800000000168a4076af2002b25f00000000008b3c06f8f0002b25f82080082002f41d72e000ac97e00000000042fe0197ef000ac97e000000000460a0197ca800ac97e0000000004f3f01b6bb800ac97e0000000004aec019a88800ac97e00000000056fe01bb1a800ac97e00000000017cb019e5e800ac97c0000000000bcb419f5e800ac97e08200208036ca019f0c800ac97e00000000042ce1ebfa002b25f80000000013a30065fa0002b25f00000000012af87aff000ac97e0ee0ee13a0ee0ee13a06daffa05c308be1948ffd22) (by decide +kernel)
private theorem c5_RelativeWidePack6815_P31 : WideCovered band 11136208 12345418 := wide_block_sound band profiles_RelativeWidePack6815_P31 11136208 12345418 (wideData 16 0x2af5c06cabd00138afa0000000000b78301f282e004e2bf00000000002e77f07ba7e00138afc0820020806fba079baf80138afc0000000000a7dec174a74004e2be8000000000282ed049b0e00138afc0000000000afff0167ce0004e2be80000000001db6f05923c80138afc0820020802eda04b3ea80138afa0000000000a4bf80e7e38004e2bf0000000000287ec01962c00138afc0000000000bf878078cb2004e2bf000000000048a1b0c93c004e2be80000000006d2ef02cf7fc0138afc2080082000e9ef107cf69e00138afa0f20f213a0f20f213a074cfac0696ed24195aa2cbc) (by decide +kernel)
private theorem c6_RelativeWidePack6815_P31 : WideCovered band 12345419 13593636 := wide_block_sound band profiles_RelativeWidePack6815_P31 12345419 13593636 (wideData 16 0xbdf7801a2fc2a004e2be82080082008c65b01872dea004e2bf00000000008cffe1dbaac00138afc00000000022197c6e8e7a004e2bf00000000007c7cf19be3d80138afa082002080160abc53ed26004e2bf00000000005a60d11b31f80138afa000000000172a684aacfa004e2bf02080082003ea4d10cb9c80138afa00000000012bc2c3a3cec004e2bf000000000049ffb0dc77b00138afc0000000000f6ca42f3e7c004e2bf02080082002a3ee0b920900138afa0000000000eb9342a7f60004e2bf00000000003ae9c0a827a80138afa12012013a12012013a0b6c35c0a969f30197da8c30) (by decide +kernel)
private theorem c7_RelativeWidePack6815_P31 : WideCovered band 13593637 13905690 := wide_block_sound band profiles_RelativeWidePack6815_P31 13593637 13905690 (wideData 4 0xa820e018b3837004e2be80000000009beaf44b27bb5084e2bf0e38038e0019faf69178db1b02138afa12812813a12812813a17987ab14fb7eee19a8aeba4) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 8912819 9185867 13905690 c0_RelativeWidePack6815_P31 (wide_covered_join band 9185868 9497921 13905690 c1_RelativeWidePack6815_P31 (wide_covered_join band 9497922 9887989 13905690 c2_RelativeWidePack6815_P31 (wide_covered_join band 9887990 10512098 13905690 c3_RelativeWidePack6815_P31 (wide_covered_join band 10512099 11136207 13905690 c4_RelativeWidePack6815_P31 (wide_covered_join band 11136208 12345418 13905690 c5_RelativeWidePack6815_P31 (wide_covered_join band 12345419 13593636 13905690 c6_RelativeWidePack6815_P31 c7_RelativeWidePack6815_P31)))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 9)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 9≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤68)
    (hT0 : 3400≤T) (hT1 : T≤3888) (hnu : 8912819≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤27343798499367341 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R188
end MergedPart3
