import ProximityPrize.SubmissionLower.RelativeWidePack6815_P00
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P01
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P02
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P03
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P04
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P05
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P06
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P07
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P08
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P09
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P10
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P11
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P12
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P13
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P14
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P15
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P16
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P17
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P18
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P19
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P20
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P21
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P22
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P23
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P24
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P25
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P26
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P27
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P28
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P29
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P30
import ProximityPrize.SubmissionLower.RelativeWidePack6815_P31
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

namespace ProximityPrize.SubmissionLower.RelativeCompact6815_R189
open RelativeWideBlocks6815 RelativeCertificate6815 RelativeCompactBlocks6815
noncomputable section
def band : Band := ⟨9,69,3354,3721,28585969548690279⟩
private def profiles : ℕ → Profile
  | 0 => ⟨25694,190,5079⟩
  | 1 => ⟨25784,188,5079⟩
  | 2 => ⟨25870,186,5079⟩
  | 3 => ⟨25819,185,5079⟩
  | 4 => ⟨45018,250,10158⟩
  | 5 => ⟨26818,141,5079⟩
  | 6 => ⟨26884,140,5079⟩
  | 7 => ⟨26872,138,5079⟩
  | _ => ⟨0,0,0⟩
private theorem c0 : WideCovered band 9043890 9319682 := wide_block_sound band profiles 9043890 9319682 (wideData 16 0x3becfc4af9bb0019af98000000001cca9d16964e80066be8000000000067da3802b2493d0019af982080082004ca19b5074b3ce42066be800000000012fba00aaaab0019af980000000009f3e917aaaa00066be80000000001248204f4de70019af98000000000af30d08e7cd00066be80000000001339b80788b1ec0066be60000000003b0d247b99a90019afa00000000014c74f02a7987b0019af98208008200bf6e94fc6a8780019afa000000000019a19048eb0139f20000000000a9fa0170b2a0139f4000000000064df40718fd0139f40e20e213c0e20e213c12d97de18decb7e011a338b6) (by decide +kernel)
private theorem c1 : WideCovered band 9319683 9634872 := wide_block_sound band profiles 9319683 9634872 (wideData 16 0x4e2c1efd00066be6000000000320e1c940066be80000000001ebb05ef40019af980000000009e740ffd80066be800000208053dc068770019af980000000010aa05fc0019afa000000000019b8910e3d0019af9800000000018fcf09eb70019af9800000c0002d77a01aa4d40066be60000000000ecfe806fc790019afa02080080003fbbcf9534d33a42066be60000000000e1eb412babf0019afa00000000012c6da44af6db10819af9800000000049e5d41f2bafd0819afa00000000009f3dc058b0a80066be60e60e613c0e60e613c137ee4d1fd74972091ea0fea) (by decide +kernel)
private theorem c2 : WideCovered band 9634873 9989461 := wide_block_sound band profiles 9634873 9989461 (wideData 16 0x28a5f13df1002b3eb04100104005dbdb4cca8b000acfae0000000001e490ab240019af980000000006e701b5e00066be80000000001fda0a9b60019af980000000007fe81fdb00066be80000000002338089ee0019af980000000009ca027de00066be800000000026eb05b200019af98000000000b8e4274800066be80000000002e5d04cb00019af98000000000d9bc268900066be80000000001b7c07a240019af980000000005b6013ef80066be80000000000eab08bfe0019af983a03a04f03a03a04f1a8bbc04dad86a212b68cb6) (by decide +kernel)
private theorem c3 : WideCovered band 9989462 10619842 := wide_block_sound band profiles 9989462 10619842 (wideData 16 0x820020802baa1cca6002b3eb0000000000ddb86e4a800acfae0000000003b781ae30002b3eb8000000000ffb46abf800acfae000000000471819fe8002b3eb80000000013c68672a000acfae00000000016fa0192de000acfae00000000006c859e7c002b3eb800000000028b166ff000acfac08200208023ae13af4002b3eb80000000011ff837eb000acfae00000000053390bde4002b3eb800000000189282379800acfac0000000007f0e12d7a002b3eb80000000001931e0183a002b3eb83b03b04f03b03b04f1baa7a0596bcec213923cf8) (by decide +kernel)
private theorem c4 : WideCovered band 10619843 11250222 := wide_block_sound band profiles 10619843 11250222 (wideData 16 0x1d2c075bee002b3eb02080082004de8070a78002b3eb8000000000f8ec071cbc002b3eb8000000000e9f806bb38002b3eb8000000000ee2806bc6a002b3eb0000000000fb2806beec002b3eb800000000108f806ca32002b3eb8000000000bc41b3da800acfae082002080063d01b66f000acfac000000000378d019b4d800acfae000000000376a018ecb000acfae0000000003ad8018edf000acfae0000000003e8b018f28000acfac000000000429f018f9a800acfae0000000001bcc01926b800acfae0f00f013c0f00f013c062aa2805c3bf36214ab2eb2) (by decide +kernel)
private theorem c5 : WideCovered band 11250223 12432187 := wide_block_sound band profiles 11250223 12432187 (wideData 16 0xa6d2c1fed24004e7cf00000000001e2f807e62b00139f3c082002080065a781f3b64004e7cf00000000001e71c05e29b00139f3a00000000007c9f4170cac004e7cf000000000028a5b06ab5a00139f3a08200208007dd4586ed80139f3c0000000000728380ee8fc004e7ce80000000001de2c02f63a80139f3c0000000000aaef80fffaa004e7cf00000000002cb3b01b61a80139f3c0000000000f6d20433cc0139f3a0000000001a192066efc0139f3c208008200136df907e938c80139f3a000000000424801d2ec800acfae0f40f413c0f40f413c067f79a069aab20215c6286a) (by decide +kernel)
private theorem c6 : WideCovered band 12432188 13692948 := wide_block_sound band profiles 12432188 13692948 (wideData 16 0x2080082007ffdd01a61bea004e7cf00000000008af3b01978cee004e7ce800000000078b2f1fd2c800139f3c08200208016ba6c728da6004e7ce80000000005b78a1882bc00139f3c000000000168d745e5d3e004e7ce80000000004decd14bbfb00139f3c0820020800bd97043bf66004e7ce8000000000483cf11aafd00139f3c0000000000f1ca83bbb32004e7cf020800820029b3a0dc2cf80139f3c0000000000e392833cfb6004e7ce80000000002e2190b82c980139f3c0000000000b7ef42b697a004e7ce8208008200196cc098e6b80139f3c12012013c12012013c0a2faac0aa2287c217ef3c30) (by decide +kernel)
private theorem c7 : WideCovered band 13692949 14086935 := wide_block_sound band profiles 13692949 14086935 (wideData 5 0x1b39e006dbe6cc0139f3a082002080066fece43fb8ce7084e7cf0000000000dfbef07e31b02139f3a30c00c300420aad13bbb3a02139f3c12a12a13c12a12a13c130c31915ca5d2621aa31fa2) (by decide +kernel)
theorem covered : WideCovered band (minimumWeight band) (tail band) := (wide_covered_join band 9043890 9319682 14086935 c0 (wide_covered_join band 9319683 9634872 14086935 c1 (wide_covered_join band 9634873 9989461 14086935 c2 (wide_covered_join band 9989462 10619842 14086935 c3 (wide_covered_join band 10619843 11250222 14086935 c4 (wide_covered_join band 11250223 12432187 14086935 c5 (wide_covered_join band 12432188 13692948 14086935 c6 c7)))))))
open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K
theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 9)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 9≤wt RCN156.residualSWeights F.val) (hB : wt RCN156.residualYSWeights F.val≤69)
    (hT0 : 3354≤T) (hT1 : T≤3721) (hnu : 9043890≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤28585969548690279 :=
  RelativeWideBlocks6815.regular_count K I band covered (by decide) F hbox hcode htotal
    hslope hB hT0 hT1 hnu nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCompact6815_R189
