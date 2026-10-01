import ProximityPrize.SubmissionLower.MergedWidePack6815_0
import ProximityPrize.SubmissionLower.MergedWidePack6815_1
import ProximityPrize.SubmissionLower.MergedWidePack6815_2
import ProximityPrize.SubmissionLower.MergedWidePack6815_3
import ProximityPrize.SubmissionLower.MergedWidePack6815_4
import ProximityPrize.SubmissionLower.MergedWidePack6815_5
import ProximityPrize.SubmissionLower.MergedWidePack6815_6
import ProximityPrize.SubmissionLower.MergedWidePack6815_7
set_option Elab.async false
section MergedPart0
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
end MergedPart0
section MergedPart1
namespace ProximityPrize.SubmissionLower.RelativeCertifiedOffers6815
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
open RelativeCertificate6815 MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
def offer (i : Fin 190) : Band := ![
  ⟨10,49,4336,4362,8672446898194066⟩,
  ⟨10,50,4257,4336,19532329570198181⟩,
  ⟨10,51,4181,4310,11453932412571267⟩,
  ⟨10,52,4107,4284,11559364790206579⟩,
  ⟨10,53,4036,4257,11933826726466278⟩,
  ⟨10,54,3968,4230,12128527754247205⟩,
  ⟨10,55,3901,4203,12617051697948470⟩,
  ⟨10,56,3837,4175,13324851088604044⟩,
  ⟨10,57,3775,4147,25491065119051915⟩,
  ⟨10,58,3714,4118,26809193959670747⟩,
  ⟨10,59,3656,4088,22659965433996529⟩,
  ⟨10,60,3599,4058,27139337404664886⟩,
  ⟨10,61,3502,3507,27072996365050479⟩,
  ⟨10,61,3539,4028,28225868518720469⟩,
  ⟨10,62,3450,3996,28652606475617611⟩,
  ⟨10,63,3399,3965,28343111664229959⟩,
  ⟨10,64,3349,3932,30476358836534067⟩,
  ⟨10,65,3301,3899,29721485741079288⟩,
  ⟨10,66,3254,3865,29906389501753189⟩,
  ⟨10,67,3208,3773,31386533365713811⟩,
  ⟨10,68,3164,3341,30456977089708927⟩,
  ⟨11,46,4298,4349,9161968566745543⟩,
  ⟨11,47,4215,4324,9396426721297806⟩,
  ⟨11,48,4136,4299,9718602346092229⟩,
  ⟨11,49,4059,4274,10022184552707145⟩,
  ⟨11,50,3985,4248,10347035358042453⟩,
  ⟨11,51,3913,4221,10696288606516687⟩,
  ⟨11,52,3844,4195,18367611252260895⟩,
  ⟨11,53,3777,4168,18931392792254785⟩,
  ⟨11,54,3713,4140,47233173434858079⟩,
  ⟨11,55,3750,4112,31300588805895278⟩,
  ⟨11,56,3750,4084,30760068026545820⟩,
  ⟨11,57,3750,4055,31518451869895687⟩,
  ⟨11,58,3725,3749,44481302807416666⟩,
  ⟨11,58,3750,4025,31563107902589997⟩,
  ⟨11,59,3381,3995,31335780865062296⟩,
  ⟨11,60,3328,3964,34167255524904513⟩,
  ⟨11,61,3277,3933,33040284130127184⟩,
  ⟨11,62,3228,3901,33967310682341084⟩,
  ⟨11,63,3180,3869,33197636390103700⟩,
  ⟨11,64,3126,3835,33315626530704906⟩,
  ⟨11,65,3047,3060,33039857377540443⟩,
  ⟨11,65,3081,3742,34751473937064351⟩,
  ⟨11,66,3003,3315,33234960734882178⟩,
  ⟨12,43,4299,4332,10715462655907075⟩,
  ⟨12,44,4211,4307,10533886751814008⟩,
  ⟨12,45,4126,4283,10754170668401988⟩,
  ⟨12,46,4045,4258,10869489292214083⟩,
  ⟨12,47,3967,4232,11213222976545203⟩,
  ⟨12,48,3891,4207,11789476443686914⟩,
  ⟨12,49,3818,4181,12230720626527430⟩,
  ⟨12,50,3748,4154,12796396664129853⟩,
  ⟨12,51,3750,4127,13432903748946315⟩,
  ⟨12,52,3750,4100,14549765614214376⟩,
  ⟨12,53,3750,4072,15470866214668980⟩,
  ⟨12,54,3750,4044,16637266735017309⟩,
  ⟨12,55,3745,4016,18053925307937435⟩,
  ⟨12,55,3750,3750,45102344705691751⟩,
  ⟨12,55,3750,4016,18053925307937435⟩,
  ⟨12,56,3750,3986,48380458494993476⟩,
  ⟨12,57,3750,3957,48477054844277678⟩,
  ⟨12,58,3775,3799,26607527287751936⟩,
  ⟨12,58,3800,3927,27475578361168162⟩,
  ⟨12,59,3775,3799,34628034442325721⟩,
  ⟨12,59,3800,3896,35481562939619314⟩,
  ⟨12,60,3123,3864,35902639268830326⟩,
  ⟨12,61,3042,3060,34574696920306571⟩,
  ⟨12,61,3076,3832,35330885142100680⟩,
  ⟨12,62,2996,3782,37147108242527887⟩,
  ⟨12,63,2952,3562,36868785416021803⟩,
  ⟨12,64,2908,3156,35450090341639341⟩,
  ⟨13,41,4243,4285,10156415819839458⟩,
  ⟨13,42,4152,4261,10303233022929419⟩,
  ⟨13,43,4065,4236,39514795961645534⟩,
  ⟨13,44,3981,4211,20393197249711410⟩,
  ⟨13,45,3901,4186,30990128545803256⟩,
  ⟨13,46,3823,4160,33078420730379481⟩,
  ⟨13,47,3749,4134,33852173757673895⟩,
  ⟨13,48,3720,4108,34880795038857114⟩,
  ⟨13,49,3720,4082,35504637214351113⟩,
  ⟨13,50,3720,4054,35424324682627447⟩,
  ⟨13,51,3720,4027,36052282855491302⟩,
  ⟨13,52,3720,3999,37279216348883173⟩,
  ⟨13,53,3720,3971,37260553836215299⟩,
  ⟨13,53,3750,3971,37326754903242029⟩,
  ⟨13,54,3720,3942,37329975288252481⟩,
  ⟨13,54,3750,3942,37910004887150554⟩,
  ⟨13,55,3700,3912,49009564034460501⟩,
  ⟨13,56,3700,3882,49074482642422725⟩,
  ⟨13,57,3700,3749,47824769168565689⟩,
  ⟨13,57,3750,3852,40214889553166861⟩,
  ⟨13,58,3685,3699,75297964709973231⟩,
  ⟨13,58,3700,3821,49220799040818505⟩,
  ⟨13,58,3750,3821,40052327279034927⟩,
  ⟨13,59,3600,3624,40141123639256505⟩,
  ⟨13,59,3625,3649,40165473124689310⟩,
  ⟨13,59,3650,3679,40105796070187079⟩,
  ⟨13,59,3680,3699,40206179082406598⟩,
  ⟨13,59,3700,3800,39695267836752096⟩,
  ⟨13,60,2919,3575,38255819477949332⟩,
  ⟨13,61,2874,3206,37312307900315654⟩,
  ⟨13,62,2819,2823,38815202157991226⟩,
  ⟨14,39,4214,4232,41106997183793118⟩,
  ⟨14,40,4119,4208,41397517565572656⟩,
  ⟨14,41,4029,4184,42361603806778530⟩,
  ⟨14,42,3942,4159,35155338583529093⟩,
  ⟨14,43,3858,4134,26771686375167705⟩,
  ⟨14,44,3778,4108,26873055909500298⟩,
  ⟨14,45,3701,4082,36438587149587604⟩,
  ⟨14,46,3627,4056,37856582925706924⟩,
  ⟨14,47,3556,4030,37897432295958080⟩,
  ⟨14,48,3450,4003,38516234506464694⟩,
  ⟨14,49,3385,3975,37117781852782506⟩,
  ⟨14,50,3322,3947,41152445620654065⟩,
  ⟨14,51,3262,3919,40480744290400122⟩,
  ⟨14,52,3204,3890,40349761222960038⟩,
  ⟨14,53,3143,3861,41397716831306615⟩,
  ⟨14,54,3056,3060,42096227797001112⟩,
  ⟨14,54,3089,3831,41085953600229339⟩,
  ⟨14,55,3004,3790,42207355888324424⟩,
  ⟨14,56,2954,3606,42424075804590334⟩,
  ⟨14,57,2905,3284,41467633654348955⟩,
  ⟨14,58,2858,2951,39232103858335220⟩,
  ⟨15,38,4112,4149,44477316085996391⟩,
  ⟨15,39,4017,4125,42555913051436406⟩,
  ⟨15,40,3926,4100,44105931060905556⟩,
  ⟨15,41,3839,4075,30833963291952495⟩,
  ⟨15,42,3755,4049,31088676933195465⟩,
  ⟨15,43,3675,4023,32307587669057266⟩,
  ⟨15,44,3598,3997,32830673985121336⟩,
  ⟨15,45,3487,3507,30952282164398925⟩,
  ⟨15,45,3512,3971,33760984407698038⟩,
  ⟨15,46,3417,3944,40441970920258437⟩,
  ⟨15,47,3350,3916,38257049879827671⟩,
  ⟨15,48,3285,3888,44081636532876497⟩,
  ⟨15,49,3223,3860,43084007545634496⟩,
  ⟨15,50,3163,3825,44229008218871759⟩,
  ⟨15,51,3101,3598,43767135969273455⟩,
  ⟨15,52,3013,3310,43532346559267973⟩,
  ⟨15,53,2960,3015,41932601061619585⟩,
  ⟨16,37,4029,4058,12658818582334196⟩,
  ⟨16,38,3933,4033,12576171010368727⟩,
  ⟨16,39,3841,4008,13230930021958327⟩,
  ⟨16,40,3754,3982,17488788244871693⟩,
  ⟨16,41,3670,3956,17619782869255014⟩,
  ⟨16,42,3589,3930,17946072568172132⟩,
  ⟨16,43,3474,3903,30411606095906251⟩,
  ⟨16,44,3402,3815,30005041600743961⟩,
  ⟨16,45,3332,3560,42650136169644217⟩,
  ⟨16,46,3264,3300,45454847903335488⟩,
  ⟨17,18,4257,4372,1424574087666458⟩,
  ⟨18,18,3938,4249,726207447517077⟩,
  ⟨18,19,3806,4199,1445814988581091⟩,
  ⟨18,19,4200,4250,1462590739470564⟩,
  ⟨19,19,3536,3730,5361476641883917⟩,
  ⟨19,20,3423,3529,8208778260150074⟩,
  ⟨7,68,4061,4062,15999661226366636⟩,
  ⟨7,69,4006,4028,19715458798791055⟩,
  ⟨7,70,3952,3993,15543604759030708⟩,
  ⟨7,71,3900,3956,20579247171543260⟩,
  ⟨8,59,4251,4260,9462236964409540⟩,
  ⟨8,60,4186,4231,9776950651964709⟩,
  ⟨8,61,4122,4202,16497012708230383⟩,
  ⟨8,62,4060,4172,18813173729294498⟩,
  ⟨8,63,4001,4141,20393803666031911⟩,
  ⟨8,64,3942,4110,21185938132043500⟩,
  ⟨8,65,3886,4078,21572164528332008⟩,
  ⟨8,66,3831,4045,22033923174676894⟩,
  ⟨8,67,3777,4012,21418250682550398⟩,
  ⟨8,68,3725,3978,20947737827292686⟩,
  ⟨8,69,3675,3943,24202393185243491⟩,
  ⟨8,70,3625,3879,24157628611101568⟩,
  ⟨9,53,4337,4342,9615460244502145⟩,
  ⟨9,54,4264,4316,9814159154075436⟩,
  ⟨9,55,4192,4289,10175228031504137⟩,
  ⟨9,56,4124,4261,10313480134692771⟩,
  ⟨9,57,4057,4234,10699101648235230⟩,
  ⟨9,58,3992,4205,24266187225847908⟩,
  ⟨9,59,3930,4176,21875831038933556⟩,
  ⟨9,60,3869,4147,22482227536500631⟩,
  ⟨9,61,3810,4117,21629505182317249⟩,
  ⟨9,62,3753,4086,25699543428999619⟩,
  ⟨9,63,3697,4055,25060987511787660⟩,
  ⟨9,64,3643,4023,24179780214681943⟩,
  ⟨9,65,3591,3991,23939258742771510⟩,
  ⟨9,66,3497,3507,25879962036737552⟩,
  ⟨9,66,3536,3958,27350167341865496⟩,
  ⟨9,67,3448,3923,27280708727050568⟩,
  ⟨9,68,3400,3888,27343798499367341⟩,
  ⟨9,69,3354,3721,28585969548690279⟩] i
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K

theorem regular_count (i : Fin 190) {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T (offer i).R)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : (offer i).R≤wt RCN156.residualSWeights F.val)
    (hB : wt RCN156.residualYSWeights F.val≤(offer i).B)
    (hT0 : (offer i).T0≤T) (hT1 : T≤(offer i).T1) (hnu : minimumWeight (offer i)≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181245≤
      ((Finset.univ : Finset I).filter (fun j => (selected gamma).eval (nodes j)=u0 j+gamma*u1 j)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80899) :
    (RCN140.regularSeeds H selected Gamma F).card≤(offer i).count := by
  fin_cases i
  · exact RelativeCompact6815_R000.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R001.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R002.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R003.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R004.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R005.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R006.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R007.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R008.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R009.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R010.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R011.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R012.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R013.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R014.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R015.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R016.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R017.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R018.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R019.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R020.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R021.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R022.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R023.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R024.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R025.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R026.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R027.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R028.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R029.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R030.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R031.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R032.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R033.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R034.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R035.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R036.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R037.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R038.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R039.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R040.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R041.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R042.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R043.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R044.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R045.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R046.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R047.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R048.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R049.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R050.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R051.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R052.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R053.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R054.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R055.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R056.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R057.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R058.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R059.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R060.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R061.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R062.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R063.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R064.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R065.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R066.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R067.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R068.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R069.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R070.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R071.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R072.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R073.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R074.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R075.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R076.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R077.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R078.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R079.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R080.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R081.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R082.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R083.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R084.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R085.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R086.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R087.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R088.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R089.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R090.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R091.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R092.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R093.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R094.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R095.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R096.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R097.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R098.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R099.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R100.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R101.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R102.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R103.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R104.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R105.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R106.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R107.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R108.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R109.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R110.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R111.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R112.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R113.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R114.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R115.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R116.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R117.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R118.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R119.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R120.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R121.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R122.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R123.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R124.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R125.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R126.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R127.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R128.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R129.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R130.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R131.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R132.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R133.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R134.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R135.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R136.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R137.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R138.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R139.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R140.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R141.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R142.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R143.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R144.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R145.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R146.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R147.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R148.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R149.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R150.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R151.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R152.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R153.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R154.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R155.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R156.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R157.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R158.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R159.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R160.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R161.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R162.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R163.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R164.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R165.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R166.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R167.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R168.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R169.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R170.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R171.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R172.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R173.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R174.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R175.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R176.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R177.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R178.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R179.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R180.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R181.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R182.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R183.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R184.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R185.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R186.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R187.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R188.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCompact6815_R189.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
end
end ProximityPrize.SubmissionLower.RelativeCertifiedOffers6815
end MergedPart1
