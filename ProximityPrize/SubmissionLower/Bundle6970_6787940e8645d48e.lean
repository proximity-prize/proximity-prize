import ProximityPrize.SubmissionLower.R6970Height2313MainReuse
import ProximityPrize.SubmissionLower.R6970Height2313Helper
import ProximityPrize.SubmissionLower.R6970Height2313MainHeads
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0628
import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.R6970Height2313MainFast
import ProximityPrize.SubmissionLower.R6970Height2308MainFree
import ProximityPrize.SubmissionLower.R6970Height2308MainHeads
import ProximityPrize.SubmissionLower.Z6969Pack0633
import ProximityPrize.SubmissionLower.Z6969Pack0634
import ProximityPrize.SubmissionLower.Z6969Pack0700
import ProximityPrize.SubmissionLower.Z6969Pack0711

section Pack_R6970Height2313MainPlans00

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal0
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HighQuadraticFinal0.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree1_0, Research6970.Height2308.MainFree.bankfree8_0, Research6970.Height2308.MainFree.bankfree14_0, Research6970.Height2308.MainFree.bankfree21_0, Research6970.Height2308.MainFree.bankfree30_1, Research6970.Height2308.MainFree.bankfree41_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree48_0, Research6970.Height2308.MainFree.bankfree58_0, Research6970.Height2308.MainFree.bankfree73_0, Research6970.Height2308.MainFree.bankfree82_0, Research6970.Height2308.MainFree.bankfree74_2, Research6970.Height2308.MainFree.bankfree111_0, Research6970.Height2308.MainFree.bankfree140_0, Research6970.Height2308.MainFree.bankfree145_0, Research6970.Height2308.MainFree.bankfree119_0, Research6970.Height2308.MainFree.bankfree198_0, Research6970.Height2308.MainFree.bankfree208_0, Research6970.Height2308.MainFree.bankfree181_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1204
    historyValues := [![14004, 175443, 816732, 4580943],
    ![23965/2, 591885/4, 1339841/2, 7354501/2],
    ![17372/3, 71266, 630208, 3356224],
    ![7059/2, 690393/16, 1047415/3, 17079461/9],
    ![15956/9, 803011/36, 3608103/16, 20170609/16],
    ![73046/81, 323683/27, 2210573/18, 26092415/36],
    ![73648/121, 1240512/121, 5605394/49, 26092415/36],
    ![73648/121, 1240512/121, 5605394/49, 21664085/36],
    ![73648/121, 1044370/121, 4700275/49, 412164],
    ![232688/441, 1158034/147, 155909/2, 412164],
    ![232688/441, 1158034/147, 155909/2, 412164],
    ![5584/11, 1158034/147, 307241/4, 412164],
    ![5584/11, 1051562/147, 7084233/98, 6963766/25],
    ![5584/11, 1051562/147, 7084233/98, 6963766/25],
    ![1645901/3362, 21408217/3362, 47876388/841, 6963766/25],
    ![1333371/3362, 21408217/3362, 47876388/841, 6963766/25],
    ![1333371/3362, 360118/63, 7104536/147, 96648561/400],
    ![1333371/3362, 30262925/5476, 7104536/147, 76887965/324],
    ![953281/2738, 30262925/5476, 7104536/147, 76887965/324],
    ![930251/2738, 30262925/5476, 7104536/147, 76887965/324],
    ![459746/1369, 30262925/5476, 7104536/147, 76887965/324]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 2 308378 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 8683, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1204⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free1_0
    · exact Research6970.Height2308.MainFree.free8_0
    · exact Research6970.Height2308.MainFree.free14_0
    · exact Research6970.Height2308.MainFree.free21_0
    · exact Research6970.Height2308.MainFree.free30_1
    · exact Research6970.Height2308.MainFree.free41_0
    · exact Research6970.Height2308.MainFree.free42_2
    · exact Research6970.Height2308.MainFree.free48_0
    · exact Research6970.Height2308.MainFree.free58_0
    · exact Research6970.Height2308.MainFree.free73_0
    · exact Research6970.Height2308.MainFree.free82_0
    · exact Research6970.Height2308.MainFree.free74_2
    · exact Research6970.Height2308.MainFree.free111_0
    · exact Research6970.Height2308.MainFree.free140_0
    · exact Research6970.Height2308.MainFree.free145_0
    · exact Research6970.Height2308.MainFree.free119_0
    · exact Research6970.Height2308.MainFree.free198_0
    · exact Research6970.Height2308.MainFree.free208_0
    · exact Research6970.Height2308.MainFree.free181_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨3338437096912429/6134542498791424, 2679091908545334764547751/3117546748282808393793536, [366057858,366057846,366057843,366057847,366057848,366057847,366057849,366057849,160052710,160297750,160297724,160052944,70418531,84012716,74005743,101728725,112501519,112501519,127742692,199147846,239909310], [942769,942769,942769,942769,942769,942769,942769,942769,2398505,2394433,2394434,2398502,5689921,4741267,5404965,3879696,3489386,3489386,3045500,1879817,1530375], ![127348659934200,1600215831540,236985936740,4152369340], 207043339815863562⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal0

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal1
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HighQuadraticFinal1.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree1_0, Research6970.Height2308.MainFree.bankfree8_0, Research6970.Height2308.MainFree.bankfree14_0, Research6970.Height2308.MainFree.bankfree21_0, Research6970.Height2308.MainFree.bankfree31_1, Research6970.Height2308.MainFree.bankfree41_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree48_0, Research6970.Height2308.MainFree.bankfree58_0, Research6970.Height2308.MainFree.bankfree73_0, Research6970.Height2308.MainFree.bankfree82_0, Research6970.Height2308.MainFree.bankfree74_2, Research6970.Height2308.MainFree.bankfree111_0, Research6970.Height2308.MainFree.bankfree140_0, Research6970.Height2308.MainFree.bankfree145_0, Research6970.Height2308.MainFree.bankfree119_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree209_0, Research6970.Height2308.MainFree.bankfree181_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1203
    historyValues := [![14019, 174909, 815264, 4552297],
    ![23965/2, 588105/4, 1331309/2, 7263025/2],
    ![17372/3, 70810, 630208, 3356224],
    ![7059/2, 685965/16, 1040683/3, 16867025/9],
    ![32167/18, 789095/36, 446389/2, 19473825/16],
    ![73046/81, 321775/27, 2197505/18, 25767875/36],
    ![73648/121, 1234680/121, 5579258/49, 25767875/36],
    ![73648/121, 1234680/121, 5579258/49, 21394625/36],
    ![73648/121, 1036810/121, 4666471/49, 412164],
    ![232688/441, 1152058/147, 7599041/98, 412164],
    ![232688/441, 1152058/147, 7599041/98, 412164],
    ![5584/11, 1152058/147, 307241/4, 412164],
    ![5584/11, 1043570/147, 7030773/98, 275086],
    ![5584/11, 1043570/147, 7030773/98, 275086],
    ![1645901/3362, 21278617/3362, 47586516/841, 275086],
    ![1333371/3362, 21278617/3362, 47586516/841, 275086],
    ![1333371/3362, 2517920/441, 7071040/147, 478690800/2209],
    ![1333371/3362, 30091775/5476, 7071040/147, 478690800/2209],
    ![953281/2738, 30091775/5476, 7071040/147, 478690800/2209],
    ![930251/2738, 30091775/5476, 7071040/147, 478690800/2209],
    ![459746/1369, 30091775/5476, 7071040/147, 478690800/2209]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 3 308364 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 8575, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1203⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free1_0
    · exact Research6970.Height2308.MainFree.free8_0
    · exact Research6970.Height2308.MainFree.free14_0
    · exact Research6970.Height2308.MainFree.free21_0
    · exact Research6970.Height2308.MainFree.free31_1
    · exact Research6970.Height2308.MainFree.free41_0
    · exact Research6970.Height2308.MainFree.free42_2
    · exact Research6970.Height2308.MainFree.free48_0
    · exact Research6970.Height2308.MainFree.free58_0
    · exact Research6970.Height2308.MainFree.free73_0
    · exact Research6970.Height2308.MainFree.free82_0
    · exact Research6970.Height2308.MainFree.free74_2
    · exact Research6970.Height2308.MainFree.free111_0
    · exact Research6970.Height2308.MainFree.free140_0
    · exact Research6970.Height2308.MainFree.free145_0
    · exact Research6970.Height2308.MainFree.free119_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free209_0
    · exact Research6970.Height2308.MainFree.free181_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨333469734160183/611587075342336, 2160009568910302987396909/2478878269302169906708480, [364103023,364103014,364103009,364103009,364103012,364103012,364103013,364103013,164256829,164260239,164256911,164260230,62468665,83291576,73678539,100980922,112061675,112061675,127339827,198744982,239601592], [948124,948124,948124,948124,948124,948124,948124,948124,2328642,2328586,2328641,2328586,6440452,4784066,5430957,3911241,3504647,3504647,3056756,1884673,1532904], ![127185317065440,1600547729408,236506528580,4170529930], 205653275143690100⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal1

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal2
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HighQuadraticFinal2.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree1_0, Research6970.Height2308.MainFree.bankfree8_0, Research6970.Height2308.MainFree.bankfree14_0, Research6970.Height2308.MainFree.bankfree22_0, Research6970.Height2308.MainFree.bankfree32_0, Research6970.Height2308.MainFree.bankfree41_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree48_0, Research6970.Height2308.MainFree.bankfree58_0, Research6970.Height2308.MainFree.bankfree73_0, Research6970.Height2308.MainFree.bankfree82_0, Research6970.Height2308.MainFree.bankfree74_2, Research6970.Height2308.MainFree.bankfree111_0, Research6970.Height2308.MainFree.bankfree140_0, Research6970.Height2308.MainFree.bankfree145_0, Research6970.Height2308.MainFree.bankfree120_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree210_0, Research6970.Height2308.MainFree.bankfree181_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1202
    historyValues := [![14037, 174542, 813217, 4526064],
    ![23965/2, 584325/4, 1322777/2, 7171549/2],
    ![17372/3, 70354, 630208, 3356224],
    ![28537/8, 342707/8, 1027003/3, 16425980/9],
    ![16211/9, 780619/36, 3558177/16, 19059217/16],
    ![73046/81, 319867/27, 2184437/18, 25443335/36],
    ![73648/121, 1228848/121, 5553122/49, 25443335/36],
    ![73648/121, 1228848/121, 5553122/49, 21125165/36],
    ![73648/121, 1029250/121, 4632667/49, 412164],
    ![232688/441, 163726/21, 7558541/98, 412164],
    ![232688/441, 163726/21, 7558541/98, 412164],
    ![5584/11, 163726/21, 307241/4, 412164],
    ![5584/11, 1035578/147, 996759/14, 6790534/25],
    ![5584/11, 1035578/147, 996759/14, 6790534/25],
    ![1645901/3362, 21149017/3362, 47296644/841, 6790534/25],
    ![668847/1681, 21149017/3362, 47296644/841, 6790534/25],
    ![668847/1681, 2499488/441, 7071040/147, 5410276/25],
    ![668847/1681, 807317/148, 134517957/2809, 5410276/25],
    ![953281/2738, 807317/148, 134517957/2809, 5410276/25],
    ![930251/2738, 807317/148, 134517957/2809, 5410276/25],
    ![459746/1369, 807317/148, 134517957/2809, 5410276/25]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 4 308344 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 8467, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1202⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free1_0
    · exact Research6970.Height2308.MainFree.free8_0
    · exact Research6970.Height2308.MainFree.free14_0
    · exact Research6970.Height2308.MainFree.free22_0
    · exact Research6970.Height2308.MainFree.free32_0
    · exact Research6970.Height2308.MainFree.free41_0
    · exact Research6970.Height2308.MainFree.free42_2
    · exact Research6970.Height2308.MainFree.free48_0
    · exact Research6970.Height2308.MainFree.free58_0
    · exact Research6970.Height2308.MainFree.free73_0
    · exact Research6970.Height2308.MainFree.free82_0
    · exact Research6970.Height2308.MainFree.free74_2
    · exact Research6970.Height2308.MainFree.free111_0
    · exact Research6970.Height2308.MainFree.free140_0
    · exact Research6970.Height2308.MainFree.free145_0
    · exact Research6970.Height2308.MainFree.free120_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free210_0
    · exact Research6970.Height2308.MainFree.free181_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨2224407668413747/4068692199473152, 4841453294542413588759113/5485526020211947209752576, [362172453,362172443,362172442,362172443,362172443,362172444,362172444,362172444,166390512,166446079,166446068,166390769,70820441,82570391,70992635,100298446,110921009,110921009,126914930,198320085,239276328], [953412,953412,953412,953412,953412,953412,953412,953412,2293185,2292262,2292262,2293181,5657995,4826868,5644316,3940030,3544224,3544224,3068627,1889794,1535576], ![127012660428960,1600897913472,236000901150,4217626560], 204296174130165856⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal2

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal3
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HighQuadraticFinal3.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree1_0, Research6970.Height2308.MainFree.bankfree8_0, Research6970.Height2308.MainFree.bankfree14_0, Research6970.Height2308.MainFree.bankfree23_0, Research6970.Height2308.MainFree.bankfree32_0, Research6970.Height2308.MainFree.bankfree41_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree48_0, Research6970.Height2308.MainFree.bankfree58_0, Research6970.Height2308.MainFree.bankfree73_0, Research6970.Height2308.MainFree.bankfree82_0, Research6970.Height2308.MainFree.bankfree74_2, Research6970.Height2308.MainFree.bankfree111_0, Research6970.Height2308.MainFree.bankfree140_0, Research6970.Height2308.MainFree.bankfree145_0, Research6970.Height2308.MainFree.bankfree120_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree210_0, Research6970.Height2308.MainFree.bankfree182_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1201
    historyValues := [![14048, 174090, 811643, 4501057],
    ![23965/2, 580545/4, 1314245/2, 7080073/2],
    ![17372/3, 69898, 630208, 3356224],
    ![3599, 84281/2, 1018594/3, 15890459/9],
    ![16211/9, 775543/36, 3534957/16, 18816109/16],
    ![73046/81, 317959/27, 2171369/18, 25118795/36],
    ![73648/121, 1223016/121, 5526986/49, 25118795/36],
    ![73648/121, 1223016/121, 5526986/49, 20855705/36],
    ![73648/121, 1021690/121, 4598863/49, 412164],
    ![232688/441, 1140106/147, 7518041/98, 412164],
    ![232688/441, 1140106/147, 7518041/98, 412164],
    ![5584/11, 1140106/147, 7518041/98, 412164],
    ![5584/11, 146798/21, 6923853/98, 6703918/25],
    ![5584/11, 146798/21, 6923853/98, 6703918/25],
    ![1645901/3362, 21019417/3362, 47006772/841, 6703918/25],
    ![668847/1681, 21019417/3362, 47006772/841, 6703918/25],
    ![668847/1681, 2481056/441, 7071040/147, 5410276/25],
    ![668847/1681, 29658293/5476, 133567665/2809, 5410276/25],
    ![957173/2738, 29658293/5476, 133567665/2809, 5410276/25],
    ![930251/2738, 29658293/5476, 133567665/2809, 5410276/25],
    ![459746/1369, 29658293/5476, 133567665/2809, 5410276/25]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 5 308319 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 8359, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1201⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free1_0
    · exact Research6970.Height2308.MainFree.free8_0
    · exact Research6970.Height2308.MainFree.free14_0
    · exact Research6970.Height2308.MainFree.free23_0
    · exact Research6970.Height2308.MainFree.free32_0
    · exact Research6970.Height2308.MainFree.free41_0
    · exact Research6970.Height2308.MainFree.free42_2
    · exact Research6970.Height2308.MainFree.free48_0
    · exact Research6970.Height2308.MainFree.free58_0
    · exact Research6970.Height2308.MainFree.free73_0
    · exact Research6970.Height2308.MainFree.free82_0
    · exact Research6970.Height2308.MainFree.free74_2
    · exact Research6970.Height2308.MainFree.free111_0
    · exact Research6970.Height2308.MainFree.free140_0
    · exact Research6970.Height2308.MainFree.free145_0
    · exact Research6970.Height2308.MainFree.free120_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free210_0
    · exact Research6970.Height2308.MainFree.free182_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨6671613783439697/12174467501391872, 21980918330230441731357205/24557183792209728737640448, [360208722,360208710,360208710,360208712,360208712,360208711,360208711,360208711,164792762,164925113,164925104,164792818,82129874,81849229,74108143,99549813,111138755,111138755,126540521,197754027,238844457], [958791,958791,958791,958791,958791,958791,958791,958791,2319736,2317537,2317537,2319736,4853012,4869668,5396831,3971610,3536669,3536669,3079088,1896616,1539125], ![126783414664740,1601363529288,235327292130,4208636110], 202895309936412639⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal3

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal4
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HighQuadraticFinal4.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree1_0, Research6970.Height2308.MainFree.bankfree8_0, Research6970.Height2308.MainFree.bankfree14_0, Research6970.Height2308.MainFree.bankfree23_0, Research6970.Height2308.MainFree.bankfree26_0, Research6970.Height2308.MainFree.bankfree38_0, Research6970.Height2308.MainFree.bankfree49_0, Research6970.Height2308.MainFree.bankfree62_0, Research6970.Height2308.MainFree.bankfree73_0, Research6970.Height2308.MainFree.bankfree82_0, Research6970.Height2308.MainFree.bankfree74_2, Research6970.Height2308.MainFree.bankfree116_1, Research6970.Height2308.MainFree.bankfree168_0, Research6970.Height2308.MainFree.bankfree148_0, Research6970.Height2308.MainFree.bankfree120_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree210_0, Research6970.Height2308.MainFree.bankfree182_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1200
    historyValues := [![14287, 173007, 805383, 4361325],
    ![23965/2, 576835/4, 1305871/2, 6990291/2],
    ![17372/3, 625054/9, 630208, 3356224],
    ![3599, 167449/4, 3035642/9, 1743217],
    ![60658/25, 721492/25, 211854, 1110916],
    ![69802/49, 818023/49, 3701582/25, 19279008/25],
    ![20312/25, 967517/100, 760463/8, 7991929/16],
    ![20312/25, 967517/100, 760463/8, 7991929/16],
    ![232688/441, 3402722/441, 7478291/98, 7991929/16],
    ![232688/441, 3402722/441, 7478291/98, 49253904/121],
    ![5584/11, 3402722/441, 7478291/98, 49253904/121],
    ![5584/11, 149571/22, 4782364/75, 6728946/25],
    ![5584/11, 149571/22, 4782364/75, 5075595/22],
    ![5584/11, 10062884/1681, 45189724/841, 5075595/22],
    ![668847/1681, 10062884/1681, 45189724/841, 5075595/22],
    ![668847/1681, 7388896/1323, 7071040/147, 5410276/25],
    ![668847/1681, 29449791/5476, 132634971/2809, 5410276/25],
    ![957173/2738, 29449791/5476, 132634971/2809, 5410276/25],
    ![930251/2738, 29449791/5476, 132634971/2809, 5410276/25],
    ![459746/1369, 29449791/5476, 132634971/2809, 5410276/25]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 6 308288 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 8253, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1200⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free1_0
    · exact Research6970.Height2308.MainFree.free8_0
    · exact Research6970.Height2308.MainFree.free14_0
    · exact Research6970.Height2308.MainFree.free23_0
    · exact Research6970.Height2308.MainFree.free26_0
    · exact Research6970.Height2308.MainFree.free38_0
    · exact Research6970.Height2308.MainFree.free49_0
    · exact Research6970.Height2308.MainFree.free62_0
    · exact Research6970.Height2308.MainFree.free73_0
    · exact Research6970.Height2308.MainFree.free82_0
    · exact Research6970.Height2308.MainFree.free74_2
    · exact Research6970.Height2308.MainFree.free116_1
    · exact Research6970.Height2308.MainFree.free168_0
    · exact Research6970.Height2308.MainFree.free148_0
    · exact Research6970.Height2308.MainFree.free120_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free210_0
    · exact Research6970.Height2308.MainFree.free182_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨6614710613592011/12098731545460736, 42733113064976007223590415/48505198667061186604826624, [358975935,358975923,358975922,358975924,358975926,358975924,160834826,160834826,161438852,161438843,161395733,119658634,76489521,69206119,96132861,109771408,109771408,125984946,197198451,238420582], [962168,962168,962168,962168,962168,962168,2385508,2385508,2375471,2375471,2376187,3271366,5225648,5793506,4115749,3584111,3584111,3094611,1903312,1542609], ![126558413337240,1601820900668,234666156690,4265092090], 201193435478441901⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal4

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal5
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HighQuadraticFinal5.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree1_0, Research6970.Height2308.MainFree.bankfree8_0, Research6970.Height2308.MainFree.bankfree14_0, Research6970.Height2308.MainFree.bankfree20_0, Research6970.Height2308.MainFree.bankfree25_0, Research6970.Height2308.MainFree.bankfree32_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree53_0, Research6970.Height2308.MainFree.bankfree62_0, Research6970.Height2308.MainFree.bankfree82_0, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree116_0, Research6970.Height2308.MainFree.bankfree121_0, Research6970.Height2308.MainFree.bankfree148_0, Research6970.Height2308.MainFree.bankfree210_0, Research6970.Height2308.MainFree.bankfree182_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1199
    historyValues := [![14265, 172047, 800629, 4211405],
    ![23965/2, 573125/4, 1297497/2, 6900509/2],
    ![17372/3, 621026/9, 630208, 3356224],
    ![28151/8, 669607/16, 1013090/3, 5360726/3],
    ![60148/25, 721418/25, 211365, 4558225/4],
    ![16211/9, 255193/12, 211365, 4558225/4],
    ![18775/16, 859655/64, 132886, 651249],
    ![86978/121, 1010838/121, 4544483/49, 23455213/49],
    ![86978/121, 1010838/121, 4544483/49, 23455213/49],
    ![86978/121, 1010838/121, 459536/5, 48621296/121],
    ![127905/242, 1818007/242, 549021/8, 48621296/121],
    ![127905/242, 3114392/441, 549021/8, 11422094/45],
    ![672960/1681, 3114392/441, 549021/8, 11422094/45],
    ![672960/1681, 9992076/1681, 44874692/841, 11422094/45],
    ![672960/1681, 29241289/5476, 131702277/2809, 35186893/162],
    ![957173/2738, 29241289/5476, 131702277/2809, 35186893/162],
    ![930251/2738, 29241289/5476, 131702277/2809, 35186893/162],
    ![459746/1369, 29241289/5476, 131702277/2809, 35186893/162]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 7 308251 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 8147, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1199⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free1_0
    · exact Research6970.Height2308.MainFree.free8_0
    · exact Research6970.Height2308.MainFree.free14_0
    · exact Research6970.Height2308.MainFree.free20_0
    · exact Research6970.Height2308.MainFree.free25_0
    · exact Research6970.Height2308.MainFree.free32_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free53_0
    · exact Research6970.Height2308.MainFree.free62_0
    · exact Research6970.Height2308.MainFree.free82_0
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free116_0
    · exact Research6970.Height2308.MainFree.free121_0
    · exact Research6970.Height2308.MainFree.free148_0
    · exact Research6970.Height2308.MainFree.free210_0
    · exact Research6970.Height2308.MainFree.free182_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨13910112036681716008558291489/25449942429939773052039462912, 34686436/39230919, [355896179,355896166,355896166,355896165,355896171,355896169,355896173,183338938,183338932,183338929,183338930,80896190,77453226,111376035,109875656,125429370,196642876,237996708], [970604,970604,970604,970604,970604,970604,970604,2070353,2070353,2070353,2070353,4926230,5159126,3528437,3580494,3110134,1910008,1546092], ![126333412540560,1602277744512,234005022440,4260787860], 199315016586196559⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal5

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal6
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HighQuadraticFinal6.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree4_0, Research6970.Height2308.MainFree.bankfree8_0, Research6970.Height2308.MainFree.bankfree14_0, Research6970.Height2308.MainFree.bankfree23_0, Research6970.Height2308.MainFree.bankfree32_0, Research6970.Height2308.MainFree.bankfree41_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree48_0, Research6970.Height2308.MainFree.bankfree61_0, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree85_0, Research6970.Height2308.MainFree.bankfree74_2, Research6970.Height2308.MainFree.bankfree115_0, Research6970.Height2308.MainFree.bankfree144_0, Research6970.Height2308.MainFree.bankfree148_0, Research6970.Height2308.MainFree.bankfree120_0, Research6970.Height2308.MainFree.bankfree198_0, Research6970.Height2308.MainFree.bankfree210_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1198
    historyValues := [![14457, 171734, 803499, 4288737],
    ![23965/2, 284725/2, 644601, 3405787],
    ![17372/3, 617036/9, 630208, 3356224],
    ![3599, 330467/8, 2995552/9, 15287842/9],
    ![16211/9, 21129, 1733401/8, 9051271/8],
    ![73046/81, 937076/81, 355502/3, 12083105/18],
    ![73648/121, 1205898/121, 5450272/49, 12083105/18],
    ![73648/121, 1205898/121, 5450272/49, 10032395/18],
    ![73648/121, 1003122/121, 4503696/49, 1615441/4],
    ![127905/242, 904436/121, 549021/8, 1615441/4],
    ![127905/242, 904436/121, 549021/8, 46965280/121],
    ![5584/11, 904436/121, 549021/8, 46965280/121],
    ![5584/11, 3054620/441, 549021/8, 12559936/49],
    ![5584/11, 100537/15, 2997664/49, 28541058/121],
    ![5584/11, 9921936/1681, 44562632/841, 28541058/121],
    ![668847/1681, 9921936/1681, 44562632/841, 28541058/121],
    ![668847/1681, 2416984/441, 6522824/135, 118591353/529],
    ![668847/1681, 14517377/2738, 130778382/2809, 17366699/81],
    ![479479/1369, 14517377/2738, 130778382/2809, 17366699/81],
    ![930251/2738, 14517377/2738, 130778382/2809, 17366699/81],
    ![459746/1369, 14517377/2738, 130778382/2809, 17366699/81]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 8 308209 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 8042, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1198⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free4_0
    · exact Research6970.Height2308.MainFree.free8_0
    · exact Research6970.Height2308.MainFree.free14_0
    · exact Research6970.Height2308.MainFree.free23_0
    · exact Research6970.Height2308.MainFree.free32_0
    · exact Research6970.Height2308.MainFree.free41_0
    · exact Research6970.Height2308.MainFree.free42_2
    · exact Research6970.Height2308.MainFree.free48_0
    · exact Research6970.Height2308.MainFree.free61_0
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free85_0
    · exact Research6970.Height2308.MainFree.free74_2
    · exact Research6970.Height2308.MainFree.free115_0
    · exact Research6970.Height2308.MainFree.free144_0
    · exact Research6970.Height2308.MainFree.free148_0
    · exact Research6970.Height2308.MainFree.free120_0
    · exact Research6970.Height2308.MainFree.free198_0
    · exact Research6970.Height2308.MainFree.free210_0
    · exact Research6970.Height2308.MainFree.free183_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨437830372677059/800647238647808, 2853205065781095271415317/3186267884731718424330240, [356241892,356241878,356241877,356241880,356241883,356241881,356241881,356241881,168579677,169026046,169026037,168579809,118747237,74761675,74594654,94565711,108370946,108370946,124966933,196092542,237576833], [969657,969657,969657,969657,969657,969657,969657,969657,2256806,2249389,2249389,2256804,3296830,5344917,5358184,4182945,3632702,3632702,3123054,1916641,1549542], ![126110534493060,1602730204012,233350124980,4322915380], 198956628845468958⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal6

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal7
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HighQuadraticFinal7.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree2_0, Research6970.Height2308.MainFree.bankfree8_0, Research6970.Height2308.MainFree.bankfree14_0, Research6970.Height2308.MainFree.bankfree23_0, Research6970.Height2308.MainFree.bankfree25_0, Research6970.Height2308.MainFree.bankfree32_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree53_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree73_0, Research6970.Height2308.MainFree.bankfree95_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree121_0, Research6970.Height2308.MainFree.bankfree152_0, Research6970.Height2308.MainFree.bankfree198_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree210_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1197
    historyValues := [![14393, 170383, 797274, 4162771],
    ![23965/2, 565775/4, 1280907/2, 6722639/2],
    ![17372/3, 613046/9, 630208, 3356224],
    ![3599, 164131/4, 2975602/9, 15088237/9],
    ![60148/25, 712178/25, 211365, 4558225/4],
    ![16211/9, 251903/12, 211365, 17866187/16],
    ![18775/16, 848105/64, 132886, 651249],
    ![86978/121, 997398/121, 4484633/49, 22850623/49],
    ![86978/121, 997398/121, 4484633/49, 22850623/49],
    ![232688/441, 3350266/441, 7359791/98, 22850623/49],
    ![232688/441, 3350266/441, 7359791/98, 24771377/72],
    ![232688/441, 825164/121, 1611486/25, 6286104/25],
    ![672960/1681, 825164/121, 1611486/25, 6286104/25],
    ![672960/1681, 9883632/1681, 44306624/841, 203536428/841],
    ![672960/1681, 2399974/441, 6477296/135, 234085941/1058],
    ![479479/1369, 2399974/441, 6477296/135, 234085941/1058],
    ![479479/1369, 28828219/5476, 129854487/2809, 3426201/16],
    ![930251/2738, 28828219/5476, 129854487/2809, 3426201/16],
    ![459746/1369, 28828219/5476, 129854487/2809, 3426201/16]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 9 308161 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 7937, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1197⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free2_0
    · exact Research6970.Height2308.MainFree.free8_0
    · exact Research6970.Height2308.MainFree.free14_0
    · exact Research6970.Height2308.MainFree.free23_0
    · exact Research6970.Height2308.MainFree.free25_0
    · exact Research6970.Height2308.MainFree.free32_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free53_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free73_0
    · exact Research6970.Height2308.MainFree.free95_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free121_0
    · exact Research6970.Height2308.MainFree.free152_0
    · exact Research6970.Height2308.MainFree.free198_0
    · exact Research6970.Height2308.MainFree.free183_0
    · exact Research6970.Height2308.MainFree.free210_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨3266259888288359/5957615473393664, 5333638632093648025972783/5880625852053468806643712, [352344387,352344376,352344373,352344381,352344377,352344378,352344380,159389323,159389323,159548176,159548165,80604896,82992655,94038766,103561997,103561997,124416599,195542207,237156957], [980333,980333,980333,980333,980333,980333,980333,2409529,2409529,2406890,2406890,4943518,4801807,4209503,3802362,3802362,3138430,1923274,1552993], ![125887655914740,1603183191048,232695226330,4524810780], 196203000038806670⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal7

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.NormalSeedOne0
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.NormalSeedOne0.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree4_0, Research6970.Height2308.MainFree.bankfree9_0, Research6970.Height2308.MainFree.bankfree17_0, Research6970.Height2308.MainFree.bankfree23_0, Research6970.Height2308.MainFree.bankfree26_0, Research6970.Height2308.MainFree.bankfree32_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree112_0, Research6970.Height2308.MainFree.bankfree108_1, Research6970.Height2308.MainFree.bankfree120_0, Research6970.Height2308.MainFree.bankfree150_0, Research6970.Height2308.MainFree.bankfree210_0, Research6970.Height2308.MainFree.bankfree181_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1205
    historyValues := [![14807, 172218, 806583, 4111124],
    ![12303, 148157, 1339097/2, 3569958],
    ![53398/9, 642467/9, 620224, 3104644],
    ![3599, 173119/4, 3138242/9, 1857277],
    ![60658/25, 745252/25, 3394769/16, 4633911/4],
    ![16211/9, 795941/36, 3394769/16, 4633911/4],
    ![18775/16, 895185/64, 132886, 651249],
    ![89110/121, 1042785/121, 675018/7, 480249],
    ![89110/121, 1042785/121, 3034277/36, 3518177/8],
    ![127905/242, 1874209/242, 3107834/45, 3518177/8],
    ![127905/242, 3201698/441, 3107834/45, 6979688/25],
    ![73733/150, 3201698/441, 3107834/45, 6979688/25],
    ![668847/1681, 3201698/441, 3107834/45, 6979688/25],
    ![668847/1681, 10433920/1681, 46854692/841, 6400327/25],
    ![668847/1681, 30511971/5476, 775569/16, 123343236/529],
    ![953281/2738, 30511971/5476, 775569/16, 123343236/529],
    ![930251/2738, 30511971/5476, 775569/16, 123343236/529],
    ![459746/1369, 30511971/5476, 775569/16, 123343236/529]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 1 308385 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 8793, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1205⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free4_0
    · exact Research6970.Height2308.MainFree.free9_0
    · exact Research6970.Height2308.MainFree.free17_0
    · exact Research6970.Height2308.MainFree.free23_0
    · exact Research6970.Height2308.MainFree.free26_0
    · exact Research6970.Height2308.MainFree.free32_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free74_1
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free112_0
    · exact Research6970.Height2308.MainFree.free108_1
    · exact Research6970.Height2308.MainFree.free120_0
    · exact Research6970.Height2308.MainFree.free150_0
    · exact Research6970.Height2308.MainFree.free210_0
    · exact Research6970.Height2308.MainFree.free181_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨6375960101800823/12043555488923648, 18072912067122200878664075/24031896617247440411557888, [370992297,370992289,370992283,370992282,370992289,370992286,370992291,157144976,157144976,157144976,115270357,90725721,91317966,116945039,115567675,128104377,199509531,240187261], [929253,929253,929253,929253,929253,929253,929253,2446825,2446825,2446825,3393974,4376484,4346635,3347183,3385667,3035395,1875458,1528091], ![127496201884020,1599916229744,237416341890,4028943730], 208527570578726428⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.NormalSeedOne0

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons0
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuadraticSingletons0.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree4_0, Research6970.Height2308.MainFree.bankfree9_0, Research6970.Height2308.MainFree.bankfree17_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree30_0, Research6970.Height2308.MainFree.bankfree40_0, Research6970.Height2308.MainFree.bankfree49_0, Research6970.Height2308.MainFree.bankfree58_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree98_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree126_0, Research6970.Height2308.MainFree.bankfree153_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree186_0, Research6970.Height2308.MainFree.bankfree176_0, Research6970.Height2308.MainFree.bankfree170_0, Research6970.Height2308.MainFree.bankfree212_0] i
    head := Research6970.Height2308.MainHeads.src1187
    historyValues := [![15035, 166332, 773046, 3739923],
    ![12303, 131444, 594340, 2816016],
    ![53398/9, 570044/9, 594340, 2816016],
    ![29433/8, 152847/4, 307512, 1419568],
    ![63824/25, 659022/25, 409431/2, 3837681/4],
    ![72196/49, 746198/49, 3363076/25, 15446472/25],
    ![20312/25, 444907/50, 760463/8, 7991929/16],
    ![95350/121, 922080/121, 593352/7, 17811648/49],
    ![95350/121, 922080/121, 673387/9, 12967201/36],
    ![127905/242, 3106784/441, 549021/8, 12967201/36],
    ![127905/242, 3106784/441, 549021/8, 10686361/36],
    ![127905/242, 761100/121, 505197/8, 5493312/25],
    ![1358449/3362, 761100/121, 505197/8, 5493312/25],
    ![1358449/3362, 9206520/1681, 4946427/98, 177533856/841],
    ![1358449/3362, 6714592/1323, 30179456/675, 43021696/225],
    ![967337/2738, 6714592/1323, 30179456/675, 43021696/225],
    ![938035/2738, 6714592/1323, 30179456/675, 43021696/225],
    ![462287/1369, 6714592/1323, 30179456/675, 43021696/225],
    ![462287/1369, 6720049/1369, 27788632/625, 117462244/625]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 19 307353 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6936, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1187⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free4_0
    · exact Research6970.Height2308.MainFree.free9_0
    · exact Research6970.Height2308.MainFree.free17_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free30_0
    · exact Research6970.Height2308.MainFree.free40_0
    · exact Research6970.Height2308.MainFree.free49_0
    · exact Research6970.Height2308.MainFree.free58_0
    · exact Research6970.Height2308.MainFree.free74_1
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free98_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free126_0
    · exact Research6970.Height2308.MainFree.free153_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free186_0
    · exact Research6970.Height2308.MainFree.free176_0
    · exact Research6970.Height2308.MainFree.free170_0
    · exact Research6970.Height2308.MainFree.free212_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨814134152394304508178559829/1482910498843343853765787648, 70812277/75758704, [335832444,335832430,335832436,335832429,335832437,335832436,335832435,146597493,146597493,146597493,146597493,73063241,73063241,88080818,101033294,107795672,142692522,101057369,235384386], [1025562,1025562,1025562,1025562,1025562,1025562,1025562,2623942,2623942,2623942,2623942,5479834,5479834,4509790,3909032,3652662,2709514,3908016,1567559], ![124946739776520,1605093992004,211845947400,4651748080], 183780510689114235⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons0

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.RepricedHelperCases0
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.RepricedHelperCases0.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree31_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree66_0, Research6970.Height2308.MainFree.bankfree91_0, Research6970.Height2308.MainFree.bankfree116_1, Research6970.Height2308.MainFree.bankfree168_0, Research6970.Height2308.MainFree.bankfree130_0, Research6970.Height2308.MainFree.bankfree166_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree181_0, Research6970.Height2308.MainFree.bankfree214_0, Research6970.Height2308.MainFree.bankfree170_0] i
    head := Research6970.Height2308.MainHeads.src1426
    historyValues := [![16062, 158811, 733583, 3220418],
    ![25417/2, 449957/4, 522144, 2414916],
    ![54680/9, 490690/9, 522144, 8560805/4],
    ![29433/8, 529043/16, 2396098/9, 3082894/3],
    ![64334/25, 564257/25, 204686, 3728761/4],
    ![17323/9, 67099/4, 2719279/16, 5136483/8],
    ![18775/16, 687725/64, 3109199/25, 12155841/25],
    ![89110/121, 797605/121, 516594/7, 7683984/25],
    ![89110/121, 797605/121, 516594/7, 7683984/25],
    ![259130/441, 811508/147, 449295/8, 42969718/169],
    ![259130/441, 1263905/242, 2736757/49, 18422049/98],
    ![259130/441, 1263905/242, 2736757/49, 168100],
    ![1374849/3362, 1263905/242, 2736757/49, 168100],
    ![1374849/3362, 7877504/1681, 4414757/98, 37100281/225],
    ![1374849/3362, 5734112/1323, 21213120/529, 280292304/1849],
    ![953281/2738, 5734112/1323, 21213120/529, 280292304/1849],
    ![953281/2738, 22964599/5476, 103417132/2601, 184978661/1250],
    ![462287/1369, 22964599/5476, 103417132/2601, 184978661/1250]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 41 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5021, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1426⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free31_0
    · exact Research6970.Height2308.MainFree.free37_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free66_0
    · exact Research6970.Height2308.MainFree.free91_0
    · exact Research6970.Height2308.MainFree.free116_1
    · exact Research6970.Height2308.MainFree.free168_0
    · exact Research6970.Height2308.MainFree.free130_0
    · exact Research6970.Height2308.MainFree.free166_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free181_0
    · exact Research6970.Height2308.MainFree.free214_0
    · exact Research6970.Height2308.MainFree.free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨2836275939195664553812633851/5341495839482162077617356800, 67476573/71891330, [300960634,300960626,300960626,300960627,300960626,300960628,300960626,149346748,149346748,149346748,100320209,66831781,66834179,76861113,90652879,89326314,134194079,228805017], [1184800,1184800,1184800,1184800,1184800,1184800,1184800,2576414,2576414,2576414,3939112,6008563,6008346,5199998,4380156,4447016,2895745,1621625], ![121454279123940,1612186658328,205924515300,5303997960], 161584784843901085⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.RepricedHelperCases0

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.RepricedHelperCases1
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.RepricedHelperCases1.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree31_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree112_0, Research6970.Height2308.MainFree.bankfree92_0, Research6970.Height2308.MainFree.bankfree168_0, Research6970.Height2308.MainFree.bankfree129_0, Research6970.Height2308.MainFree.bankfree161_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree181_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree170_0] i
    head := Research6970.Height2308.MainHeads.src1683
    historyValues := [![15806, 160907, 745839, 3268604],
    ![25417/2, 233063/2, 529158, 2414916],
    ![54680/9, 169390/3, 529158, 4652945/2],
    ![29433/8, 273917/8, 2480876/9, 3351212/3],
    ![64334/25, 584796/25, 204686, 3728761/4],
    ![17323/9, 104363/6, 1409239/8, 2791767/4],
    ![18775/16, 44485/4, 3217138/25, 13213818/25],
    ![89110/121, 826010/121, 534948/7, 2161368/7],
    ![89110/121, 826010/121, 673387/9, 2161368/7],
    ![308092/441, 815996/147, 225929/4, 797449/4],
    ![65315/96, 815996/147, 225929/4, 797449/4],
    ![65315/96, 815996/147, 225929/4, 168100],
    ![813/2, 815996/147, 225929/4, 168100],
    ![813/2, 8156496/1681, 2289995/49, 168100],
    ![813/2, 661984/147, 5026803/121, 86564416/529],
    ![953281/2738, 661984/147, 5026803/121, 86564416/529],
    ![953281/2738, 5975137/1369, 6947158/169, 117462244/729],
    ![462287/1369, 5975137/1369, 6947158/169, 117462244/729]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 5 26 643299 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5458, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1683⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free31_0
    · exact Research6970.Height2308.MainFree.free37_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free74_1
    · exact Research6970.Height2308.MainFree.free112_0
    · exact Research6970.Height2308.MainFree.free92_0
    · exact Research6970.Height2308.MainFree.free168_0
    · exact Research6970.Height2308.MainFree.free129_0
    · exact Research6970.Height2308.MainFree.free161_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free181_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨92207304476513370630812727/172545857884596941470121984, 34256214/36546209, [309927792,309927779,309927781,309927782,309927783,309927782,309927781,154674004,154674012,103309256,103309255,68340273,60649430,79698389,92936141,92936131,136517159,230578537], [1138950,1138950,1138950,1138950,1138950,1138950,1138950,2487887,2487887,3813024,3813024,5871930,6640813,5004148,4265077,4265077,2844838,1607051], ![122395699010340,1610274727328,207520683300,5104230960], 167273041340145566⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 18 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.RepricedHelperCases1
end Pack_R6970Height2313MainPlans00

section Pack_R6970Height2313MainPlans01

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal10
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HighQuadraticFinal10.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree4_0, Research6970.Height2308.MainFree.bankfree9_0, Research6970.Height2308.MainFree.bankfree17_0, Research6970.Height2308.MainFree.bankfree23_0, Research6970.Height2308.MainFree.bankfree25_0, Research6970.Height2308.MainFree.bankfree32_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree116_1, Research6970.Height2308.MainFree.bankfree168_0, Research6970.Height2308.MainFree.bankfree125_0, Research6970.Height2308.MainFree.bankfree150_0, Research6970.Height2308.MainFree.bankfree198_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree210_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1194
    historyValues := [![14914, 168785, 788464, 3905558],
    ![12303, 137663, 1244651/2, 3096562],
    ![53398/9, 596993/9, 620224, 3096562],
    ![3599, 40219, 324078, 14498927/9],
    ![60148/25, 698538/25, 211365, 4558225/4],
    ![16211/9, 741139/36, 3377577/16, 17168377/16],
    ![18775/16, 831055/64, 132886, 651249],
    ![89110/121, 966995/121, 626046/7, 3020292/7],
    ![89110/121, 966995/121, 312915/4, 27464827/72],
    ![127905/242, 3227018/441, 549021/8, 27464827/72],
    ![127905/242, 1571413/242, 2737708/45, 18655642/75],
    ![127905/242, 1571413/242, 2737708/45, 4690605/22],
    ![677069/1681, 1571413/242, 2737708/45, 4690605/22],
    ![677069/1681, 9641040/1681, 43324044/841, 4690605/22],
    ![677069/1681, 2349754/441, 1268576/27, 4690605/22],
    ![479479/1369, 2349754/441, 1268576/27, 4690605/22],
    ![479479/1369, 28218449/5476, 127126797/2809, 592938234/2809],
    ![930251/2738, 28218449/5476, 127126797/2809, 592938234/2809],
    ![459746/1369, 28218449/5476, 127126797/2809, 592938234/2809]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 12 307983 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 7627, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1194⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free4_0
    · exact Research6970.Height2308.MainFree.free9_0
    · exact Research6970.Height2308.MainFree.free17_0
    · exact Research6970.Height2308.MainFree.free23_0
    · exact Research6970.Height2308.MainFree.free25_0
    · exact Research6970.Height2308.MainFree.free32_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free74_1
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free116_1
    · exact Research6970.Height2308.MainFree.free168_0
    · exact Research6970.Height2308.MainFree.free125_0
    · exact Research6970.Height2308.MainFree.free150_0
    · exact Research6970.Height2308.MainFree.free198_0
    · exact Research6970.Height2308.MainFree.free183_0
    · exact Research6970.Height2308.MainFree.free210_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨359211268250889/655748900061184, 128262785597950158195079/142489790661501768433664, [349396528,349396520,349396520,349396513,349396520,349396519,349396519,148286135,148286135,148286135,116465504,74775366,74775294,91693024,103997062,103997062,122791802,193917411,235917325], [988408,988408,988408,988408,988408,988408,988408,2594039,2594039,2594039,3360581,5343972,5343977,4327731,3784460,3784460,3183826,1942857,1563179], ![125229634456500,1604519172080,230761719090,4503507400], 192986959859305942⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal10

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal11
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HighQuadraticFinal11.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree4_0, Research6970.Height2308.MainFree.bankfree9_0, Research6970.Height2308.MainFree.bankfree17_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree32_0, Research6970.Height2308.MainFree.bankfree41_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree48_0, Research6970.Height2308.MainFree.bankfree61_0, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree85_0, Research6970.Height2308.MainFree.bankfree74_2, Research6970.Height2308.MainFree.bankfree113_0, Research6970.Height2308.MainFree.bankfree140_0, Research6970.Height2308.MainFree.bankfree150_0, Research6970.Height2308.MainFree.bankfree120_0, Research6970.Height2308.MainFree.bankfree198_0, Research6970.Height2308.MainFree.bankfree210_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1193
    historyValues := [![14668, 169514, 791117, 4131855],
    ![12303, 136754, 618235, 3055556],
    ![53398/9, 593054/9, 618235, 3055556],
    ![29433/8, 318379/8, 2882068/9, 4620964/3],
    ![16211/9, 61366/3, 1677931/8, 8470513/8],
    ![73046/81, 909728/81, 115032, 11307815/18],
    ![73648/121, 107094/11, 5325400/49, 11307815/18],
    ![73648/121, 107094/11, 5325400/49, 9388685/18],
    ![73648/121, 966486/121, 4340640/49, 19131092/49],
    ![127905/242, 458492/63, 549021/8, 19131092/49],
    ![127905/242, 458492/63, 549021/8, 43951840/121],
    ![5584/11, 458492/63, 549021/8, 43951840/121],
    ![5584/11, 1550049/242, 2684504/45, 18769844/75],
    ![5584/11, 1550049/242, 2684504/45, 18769844/75],
    ![5584/11, 9572360/1681, 43018216/841, 197211304/841],
    ![668847/1681, 9572360/1681, 43018216/841, 197211304/841],
    ![668847/1681, 2333392/441, 31495432/675, 10738729/49],
    ![668847/1681, 14009891/2738, 126238098/2809, 11039364/53],
    ![479479/1369, 14009891/2738, 126238098/2809, 11039364/53],
    ![930251/2738, 14009891/2738, 126238098/2809, 11039364/53],
    ![459746/1369, 14009891/2738, 126238098/2809, 11039364/53]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 13 307912 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 7526, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1193⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free4_0
    · exact Research6970.Height2308.MainFree.free9_0
    · exact Research6970.Height2308.MainFree.free17_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free32_0
    · exact Research6970.Height2308.MainFree.free41_0
    · exact Research6970.Height2308.MainFree.free42_2
    · exact Research6970.Height2308.MainFree.free48_0
    · exact Research6970.Height2308.MainFree.free61_0
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free85_0
    · exact Research6970.Height2308.MainFree.free74_2
    · exact Research6970.Height2308.MainFree.free113_0
    · exact Research6970.Height2308.MainFree.free140_0
    · exact Research6970.Height2308.MainFree.free150_0
    · exact Research6970.Height2308.MainFree.free120_0
    · exact Research6970.Height2308.MainFree.free198_0
    · exact Research6970.Height2308.MainFree.free210_0
    · exact Research6970.Height2308.MainFree.free183_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨14709198566406501967655798235/26655422074099957269532377088, 622312863/665331079, [346928686,346928676,346928672,346928675,346928676,346928680,346928675,346928675,166759996,166760033,166774686,166774663,82086581,86732151,66747656,90709582,103280892,103280892,122262433,193388042,235513445], [995168,995168,995168,995168,995168,995168,995168,995168,2287045,2287045,2286801,2286802,4855582,4579871,6016183,4377298,3814220,3814220,3198617,1949237,1566498], ![125015246874900,1604954621740,230131769980,4538921800], 192112846612014290⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal11

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal12
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HighQuadraticFinal12.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree4_0, Research6970.Height2308.MainFree.bankfree9_0, Research6970.Height2308.MainFree.bankfree17_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree32_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree53_0, Research6970.Height2308.MainFree.bankfree62_0, Research6970.Height2308.MainFree.bankfree72_0, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree104_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree168_0, Research6970.Height2308.MainFree.bankfree125_0, Research6970.Height2308.MainFree.bankfree150_0, Research6970.Height2308.MainFree.bankfree198_0, Research6970.Height2308.MainFree.bankfree181_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1192
    historyValues := [![14880, 167759, 780412, 3853767],
    ![12303, 135845, 1228289/2, 3014550],
    ![53398/9, 589115/9, 1228289/2, 3014550],
    ![29433/8, 632415/16, 954158/3, 1519650],
    ![16211/9, 731645/36, 3334147/16, 16713675/16],
    ![18775/16, 819945/64, 132886, 651249],
    ![86978/121, 964630/121, 4338713/49, 21376575/49],
    ![86978/121, 964630/121, 4338713/49, 21376575/49],
    ![86978/121, 964630/121, 4338713/49, 847935/2],
    ![127905/242, 3191870/441, 549021/8, 20745450/49],
    ![127905/242, 3191870/441, 549021/8, 50148450/169],
    ![127905/242, 72036/11, 505197/8, 235224],
    ![127905/242, 72036/11, 505197/8, 415125/2],
    ![677069/1681, 72036/11, 505197/8, 415125/2],
    ![677069/1681, 9503680/1681, 42712388/841, 415125/2],
    ![677069/1681, 2317030/441, 10425488/225, 415125/2],
    ![953281/2738, 2317030/441, 10425488/225, 415125/2],
    ![953281/2738, 6966505/1369, 125200502/2809, 563305050/2809],
    ![930251/2738, 6966505/1369, 125200502/2809, 563305050/2809],
    ![459746/1369, 6966505/1369, 125200502/2809, 563305050/2809]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 14 307836 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 7425, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1192⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free4_0
    · exact Research6970.Height2308.MainFree.free9_0
    · exact Research6970.Height2308.MainFree.free17_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free32_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free53_0
    · exact Research6970.Height2308.MainFree.free62_0
    · exact Research6970.Height2308.MainFree.free72_0
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free104_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free168_0
    · exact Research6970.Height2308.MainFree.free125_0
    · exact Research6970.Height2308.MainFree.free150_0
    · exact Research6970.Height2308.MainFree.free198_0
    · exact Research6970.Height2308.MainFree.free181_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨71936452771157/130352559423488, 77974837983847885887329/84457649672192828375040, [344144958,344144949,344144943,344144948,344144947,344144948,147650610,147650610,147650610,147650610,147650610,114714977,74408631,70673573,90167867,101577311,101453735,121424996,192830151,235088788], [1002793,1002793,1002793,1002793,1002793,1002793,2604600,2604600,2604600,2604600,2604600,3412587,5372961,5669661,4404601,3886083,3891296,3222015,1955961,1569988], ![124789830446160,1605412609952,229467879690,4630642240], 189365558264559232⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal12

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal13
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HighQuadraticFinal13.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree4_0, Research6970.Height2308.MainFree.bankfree9_0, Research6970.Height2308.MainFree.bankfree17_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree32_0, Research6970.Height2308.MainFree.bankfree41_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree48_0, Research6970.Height2308.MainFree.bankfree61_0, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree85_0, Research6970.Height2308.MainFree.bankfree74_2, Research6970.Height2308.MainFree.bankfree113_0, Research6970.Height2308.MainFree.bankfree140_0, Research6970.Height2308.MainFree.bankfree150_0, Research6970.Height2308.MainFree.bankfree121_0, Research6970.Height2308.MainFree.bankfree198_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1191
    historyValues := [![14668, 168911, 787700, 4100901],
    ![12303, 134945, 1220189/2, 2973950],
    ![53398/9, 585215/9, 1220189/2, 2973950],
    ![29433/8, 628115/16, 2843074/9, 4497550/3],
    ![16211/9, 242315/12, 3312647/16, 16488575/16],
    ![73046/81, 899075/81, 682085/6, 22011625/36],
    ![73648/121, 1167180/121, 5276758/49, 22011625/36],
    ![73648/121, 1167180/121, 215255/2, 18275875/36],
    ![73648/121, 86565/11, 4277124/49, 18620150/49],
    ![127905/242, 3174470/441, 549021/8, 18620150/49],
    ![127905/242, 3174470/441, 549021/8, 42778000/121],
    ![5584/11, 3174470/441, 549021/8, 42778000/121],
    ![5584/11, 1527135/242, 475107/8, 730742/3],
    ![5584/11, 1527135/242, 475107/8, 730742/3],
    ![5584/11, 9435680/1681, 4959107/98, 191944300/841],
    ![672960/1681, 9435680/1681, 4959107/98, 191944300/841],
    ![672960/1681, 328690/63, 31059664/675, 1920322/9],
    ![672960/1681, 6916105/1369, 27788632/625, 555718450/2809],
    ![479479/1369, 6916105/1369, 27788632/625, 555718450/2809],
    ![930251/2738, 6916105/1369, 27788632/625, 555718450/2809],
    ![459746/1369, 6916105/1369, 27788632/625, 555718450/2809]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 15 307754 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 7325, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1191⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free4_0
    · exact Research6970.Height2308.MainFree.free9_0
    · exact Research6970.Height2308.MainFree.free17_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free32_0
    · exact Research6970.Height2308.MainFree.free41_0
    · exact Research6970.Height2308.MainFree.free42_2
    · exact Research6970.Height2308.MainFree.free48_0
    · exact Research6970.Height2308.MainFree.free61_0
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free85_0
    · exact Research6970.Height2308.MainFree.free74_2
    · exact Research6970.Height2308.MainFree.free113_0
    · exact Research6970.Height2308.MainFree.free140_0
    · exact Research6970.Height2308.MainFree.free150_0
    · exact Research6970.Height2308.MainFree.free121_0
    · exact Research6970.Height2308.MainFree.free198_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free183_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨13538525383284102435951140967/24634621679870739771836858368, 72235689/77194796, [343036522,343036509,343036508,343036508,343036511,343036512,343036512,343036514,168329041,168586492,168586482,168329140,81353571,85759061,72515807,90178749,104272537,104272537,121419229,192544838,234869437], [1005829,1005829,1005829,1005829,1005829,1005829,1005829,1005829,2260971,2256693,2256693,2260970,4899085,4637623,5523321,4404052,3774902,3774902,3222176,1959400,1571790], ![124673394548340,1605648798908,229128357220,4492133380], 189595994992171645⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal13

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal14
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HighQuadraticFinal14.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree4_0, Research6970.Height2308.MainFree.bankfree9_0, Research6970.Height2308.MainFree.bankfree17_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree32_0, Research6970.Height2308.MainFree.bankfree41_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree48_0, Research6970.Height2308.MainFree.bankfree61_0, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree85_0, Research6970.Height2308.MainFree.bankfree74_2, Research6970.Height2308.MainFree.bankfree113_0, Research6970.Height2308.MainFree.bankfree140_0, Research6970.Height2308.MainFree.bankfree150_0, Research6970.Height2308.MainFree.bankfree121_0, Research6970.Height2308.MainFree.bankfree198_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1190
    historyValues := [![14668, 168614, 786017, 4085655],
    ![12303, 134054, 606085, 2933756],
    ![53398/9, 581354/9, 606085, 2933756],
    ![29433/8, 311929/8, 2823868/9, 4436764/3],
    ![16211/9, 60191/3, 1645681/8, 8132863/8],
    ![73046/81, 893828/81, 339046/3, 10857065/18],
    ![73648/121, 1161834/121, 107200, 10857065/18],
    ![73648/121, 1161834/121, 106896, 9014435/18],
    ![73648/121, 85926/11, 4245840/49, 18368492/49],
    ![127905/242, 3157244/441, 549021/8, 18368492/49],
    ![127905/242, 3157244/441, 549021/8, 42199840/121],
    ![5584/11, 3157244/441, 549021/8, 42199840/121],
    ![5584/11, 1515849/242, 475107/8, 18021644/75],
    ![5584/11, 1515849/242, 475107/8, 18021644/75],
    ![5584/11, 9368360/1681, 4959107/98, 189350104/841],
    ![672960/1681, 9368360/1681, 4959107/98, 189350104/841],
    ![672960/1681, 2284792/441, 30845032/675, 47359204/225],
    ![672960/1681, 6866209/1369, 27788632/625, 548207716/2809],
    ![479479/1369, 6866209/1369, 27788632/625, 548207716/2809],
    ![930251/2738, 6866209/1369, 27788632/625, 548207716/2809],
    ![459746/1369, 6866209/1369, 27788632/625, 548207716/2809]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 16 307664 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 7226, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1190⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free4_0
    · exact Research6970.Height2308.MainFree.free9_0
    · exact Research6970.Height2308.MainFree.free17_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free32_0
    · exact Research6970.Height2308.MainFree.free41_0
    · exact Research6970.Height2308.MainFree.free42_2
    · exact Research6970.Height2308.MainFree.free48_0
    · exact Research6970.Height2308.MainFree.free61_0
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free85_0
    · exact Research6970.Height2308.MainFree.free74_2
    · exact Research6970.Height2308.MainFree.free113_0
    · exact Research6970.Height2308.MainFree.free140_0
    · exact Research6970.Height2308.MainFree.free150_0
    · exact Research6970.Height2308.MainFree.free121_0
    · exact Research6970.Height2308.MainFree.free198_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free183_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨1681431236952440102229765915/3066183216062285722047217664, 72070755/77029862, [341119486,341119472,341119475,341119474,341119478,341119476,341119480,341119480,166697714,166697715,167139897,167139871,70496896,85279829,72423544,89102031,102348134,102348134,121265642,192391250,234749745], [1011080,1011080,1011080,1011080,1011080,1011080,1011080,1011080,2288080,2288080,2280732,2280733,5683696,4666065,5530650,4458320,3853567,3853567,3226467,1961251,1572774], ![124609859640900,1605778057260,228945587500,4585744730], 188447957577977858⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal14

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal15
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HighQuadraticFinal15.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree4_0, Research6970.Height2308.MainFree.bankfree9_0, Research6970.Height2308.MainFree.bankfree17_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree30_0, Research6970.Height2308.MainFree.bankfree40_0, Research6970.Height2308.MainFree.bankfree50_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree62_0, Research6970.Height2308.MainFree.bankfree82_0, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree74_2, Research6970.Height2308.MainFree.bankfree116_1, Research6970.Height2308.MainFree.bankfree110_0, Research6970.Height2308.MainFree.bankfree168_0, Research6970.Height2308.MainFree.bankfree125_0, Research6970.Height2308.MainFree.bankfree153_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree181_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1189
    historyValues := [![14987, 166703, 773936, 3781978],
    ![12303, 133172, 602116, 2893968],
    ![53398/9, 577532/9, 602116, 2893968],
    ![29433/8, 154911/4, 934952/3, 1458864],
    ![63824/25, 668046/25, 409431/2, 3837681/4],
    ![72196/49, 756374/49, 681716/5, 15874056/25],
    ![81850/81, 281450/27, 317467/3, 485298],
    ![89110/121, 84960/11, 605088/7, 2822688/7],
    ![89110/121, 84960/11, 605088/7, 2822688/7],
    ![89110/121, 84960/11, 605088/7, 8904256/25],
    ![127905/242, 3140192/441, 549021/8, 8904256/25],
    ![5584/11, 3140192/441, 549021/8, 8904256/25],
    ![5584/11, 1512531/242, 964947/16, 5811696/25],
    ![5584/11, 1499577/242, 946157/16, 5811696/25],
    ![5584/11, 1499577/242, 946157/16, 203401],
    ![677069/1681, 1499577/242, 946157/16, 203401],
    ![677069/1681, 9340920/1681, 4946427/98, 203401],
    ![677069/1681, 6812896/1323, 30617216/675, 86564416/441],
    ![953281/2738, 6812896/1323, 30617216/675, 86564416/441],
    ![953281/2738, 6816817/1369, 27788632/625, 540772848/2809],
    ![930251/2738, 6816817/1369, 27788632/625, 540772848/2809],
    ![459746/1369, 6816817/1369, 27788632/625, 540772848/2809]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 17 307566 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 7128, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1189⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free4_0
    · exact Research6970.Height2308.MainFree.free9_0
    · exact Research6970.Height2308.MainFree.free17_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free30_0
    · exact Research6970.Height2308.MainFree.free40_0
    · exact Research6970.Height2308.MainFree.free50_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free62_0
    · exact Research6970.Height2308.MainFree.free82_0
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free74_2
    · exact Research6970.Height2308.MainFree.free116_1
    · exact Research6970.Height2308.MainFree.free110_0
    · exact Research6970.Height2308.MainFree.free168_0
    · exact Research6970.Height2308.MainFree.free125_0
    · exact Research6970.Height2308.MainFree.free153_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free181_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨820443742599915328727939487/1486326975110295392973488128, 70899497/75845924, [338751662,338751648,338751647,338751650,338751651,338751653,338751651,166211253,166211265,166211265,166211255,166211258,94700938,112917212,69859222,66617076,88780240,99974908,99749563,120834060,192239214,234631262], [1017566,1017566,1017566,1017566,1017566,1017566,1017566,2296164,2296164,2296164,2296164,2296164,4176153,3474963,5734350,6028010,4474539,3953678,3963184,3238525,1963083,1573748], ![124546966494840,1605905977768,228764664660,4716188960], 185877151894941172⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal15

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal16
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HighQuadraticFinal16.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree4_0, Research6970.Height2308.MainFree.bankfree9_0, Research6970.Height2308.MainFree.bankfree17_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree32_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree98_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree168_0, Research6970.Height2308.MainFree.bankfree126_0, Research6970.Height2308.MainFree.bankfree153_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree185_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree175_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1188
    historyValues := [![14990, 166686, 777168, 3792363],
    ![12303, 132299, 1196375/2, 2854586],
    ![53398/9, 573749/9, 1196375/2, 2854586],
    ![29433/8, 615473/16, 2786038/9, 4317034/3],
    ![16211/9, 237709/12, 3249437/16, 15826781/16],
    ![18775/16, 798275/64, 132886, 651249],
    ![89110/121, 928255/121, 601014/7, 2784276/7],
    ![89110/121, 928255/121, 2704783/36, 12967201/36],
    ![127905/242, 3123314/441, 549021/8, 12967201/36],
    ![127905/242, 3123314/441, 549021/8, 10686361/36],
    ![127905/242, 767180/121, 505197/8, 5568552/25],
    ![127905/242, 767180/121, 9134644/147, 203401],
    ![1358449/3362, 767180/121, 9134644/147, 203401],
    ![1358449/3362, 9273020/1681, 4946427/98, 203401],
    ![1358449/3362, 966176/189, 30396056/675, 130832848/675],
    ![966147/2738, 966176/189, 30396056/675, 130832848/675],
    ![966147/2738, 182917/37, 27788632/625, 533413846/2809],
    ![466774/1369, 182917/37, 27788632/625, 533413846/2809],
    ![459746/1369, 182917/37, 27788632/625, 533413846/2809]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 18 307462 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 7031, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1188⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free4_0
    · exact Research6970.Height2308.MainFree.free9_0
    · exact Research6970.Height2308.MainFree.free17_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free32_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free74_1
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free98_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free168_0
    · exact Research6970.Height2308.MainFree.free126_0
    · exact Research6970.Height2308.MainFree.free153_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free185_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free175_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨424460191910207339367567689/773557074932619049487564800, 71216233/76162660, [337858222,337858208,337858207,337858214,337858212,337858213,153553760,153553770,153553768,153553770,112619400,72387476,69720100,88454019,101419477,101419477,113842007,192508173,234513987], [1020013,1020013,1020013,1020013,1020013,1020013,2506503,2506503,2506503,2506503,3485296,5533515,5746952,4490981,3892741,3892741,3442876,1959842,1574711], ![124484714579340,1606032026328,229084725870,4632361790], 185643825429255101⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal16

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal8
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HighQuadraticFinal8.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree2_0, Research6970.Height2308.MainFree.bankfree8_0, Research6970.Height2308.MainFree.bankfree14_0, Research6970.Height2308.MainFree.bankfree23_0, Research6970.Height2308.MainFree.bankfree26_0, Research6970.Height2308.MainFree.bankfree32_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree95_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree121_0, Research6970.Height2308.MainFree.bankfree152_0, Research6970.Height2308.MainFree.bankfree198_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree210_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1196
    historyValues := [![14458, 169726, 795308, 4125936],
    ![23965/2, 562135/4, 1272691/2, 6634551/2],
    ![17372/3, 609094/9, 630208, 6634551/2],
    ![3599, 163039/4, 2955842/9, 4963511/3],
    ![60658/25, 703012/25, 211854, 1110916],
    ![16211/9, 750821/36, 211854, 17632083/16],
    ![18775/16, 842385/64, 132886, 651249],
    ![89110/121, 980385/121, 634698/7, 443124],
    ![89110/121, 980385/121, 634698/7, 443124],
    ![127905/242, 3262862/441, 549021/8, 443124],
    ![127905/242, 3262862/441, 549021/8, 8148931/24],
    ![127905/242, 818508/121, 1598382/25, 6203736/25],
    ![672960/1681, 818508/121, 1598382/25, 6203736/25],
    ![672960/1681, 9811248/1681, 43985472/841, 200869452/841],
    ![672960/1681, 2383126/441, 10720336/225, 10738729/49],
    ![479479/1369, 2383126/441, 10720336/225, 10738729/49],
    ![479479/1369, 28623651/5476, 128939391/2809, 3426201/16],
    ![930251/2738, 28623651/5476, 128939391/2809, 3426201/16],
    ![459746/1369, 28623651/5476, 128939391/2809, 3426201/16]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 10 308107 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 7833, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1196⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free2_0
    · exact Research6970.Height2308.MainFree.free8_0
    · exact Research6970.Height2308.MainFree.free14_0
    · exact Research6970.Height2308.MainFree.free23_0
    · exact Research6970.Height2308.MainFree.free26_0
    · exact Research6970.Height2308.MainFree.free32_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free95_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free121_0
    · exact Research6970.Height2308.MainFree.free152_0
    · exact Research6970.Height2308.MainFree.free198_0
    · exact Research6970.Height2308.MainFree.free183_0
    · exact Research6970.Height2308.MainFree.free210_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨3256406128086617/5934642932744192, 42697589108585681639524525/46682895610912052099416064, [350626926,350626912,350626914,350626913,350626919,350626918,350626918,150587650,150587650,150587650,150587650,80404135,81784538,93243913,104780313,104780313,123871506,194997114,236741081], [985037,985037,985037,985037,985037,985037,985037,2555793,2555793,2555793,2555793,4955433,4873508,4249565,3757284,3757284,3153660,1929844,1556410], ![125666900616420,1603631266204,232046565660,4471167960], 194839863990158561⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal8

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal9
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HighQuadraticFinal9.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree4_0, Research6970.Height2308.MainFree.bankfree9_0, Research6970.Height2308.MainFree.bankfree17_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree32_0, Research6970.Height2308.MainFree.bankfree41_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree48_0, Research6970.Height2308.MainFree.bankfree61_0, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree85_0, Research6970.Height2308.MainFree.bankfree74_2, Research6970.Height2308.MainFree.bankfree113_0, Research6970.Height2308.MainFree.bankfree144_0, Research6970.Height2308.MainFree.bankfree150_0, Research6970.Height2308.MainFree.bankfree120_0, Research6970.Height2308.MainFree.bankfree198_0, Research6970.Height2308.MainFree.bankfree210_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1195
    historyValues := [![14668, 170212, 794829, 4160343],
    ![12303, 138590, 626497, 3138380],
    ![53398/9, 601010/9, 620224, 3104644],
    ![29433/8, 322765/8, 2921644/9, 4746220/3],
    ![16211/9, 62165/3, 1699861/8, 8700115/8],
    ![73046/81, 920540/81, 349210/3, 11614325/18],
    ![73648/121, 1189050/121, 767824/7, 11614325/18],
    ![73648/121, 1189050/121, 767824/7, 9643175/18],
    ![73648/121, 980970/121, 4405104/49, 19649660/49],
    ![127905/242, 3244940/441, 549021/8, 19649660/49],
    ![127905/242, 3244940/441, 549021/8, 45143200/121],
    ![5584/11, 3244940/441, 549021/8, 45143200/121],
    ![5584/11, 1573305/242, 13629784/225, 3855724/15],
    ![5584/11, 1573305/242, 2928608/49, 27433770/121],
    ![5584/11, 9711080/1681, 43635928/841, 27433770/121],
    ![668847/1681, 9711080/1681, 43635928/841, 27433770/121],
    ![668847/1681, 2366440/441, 31937704/675, 10738729/49],
    ![668847/1681, 14210525/2738, 128033094/2809, 600945660/2809],
    ![479479/1369, 14210525/2738, 128033094/2809, 600945660/2809],
    ![930251/2738, 14210525/2738, 128033094/2809, 600945660/2809],
    ![459746/1369, 14210525/2738, 128033094/2809, 600945660/2809]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 11 308048 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 7730, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1195⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free4_0
    · exact Research6970.Height2308.MainFree.free9_0
    · exact Research6970.Height2308.MainFree.free17_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free32_0
    · exact Research6970.Height2308.MainFree.free41_0
    · exact Research6970.Height2308.MainFree.free42_2
    · exact Research6970.Height2308.MainFree.free48_0
    · exact Research6970.Height2308.MainFree.free61_0
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free85_0
    · exact Research6970.Height2308.MainFree.free74_2
    · exact Research6970.Height2308.MainFree.free113_0
    · exact Research6970.Height2308.MainFree.free144_0
    · exact Research6970.Height2308.MainFree.free150_0
    · exact Research6970.Height2308.MainFree.free120_0
    · exact Research6970.Height2308.MainFree.free198_0
    · exact Research6970.Height2308.MainFree.free210_0
    · exact Research6970.Height2308.MainFree.free183_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨6541524309096211/11903272637956096, 42897578329959389782200113/46950624019037407101845504, [350972194,350972186,350972181,350972181,350972184,350972187,350972183,350972185,167868209,167913612,167913601,167868382,116990722,74761617,67445828,92243852,105482202,105482202,123331654,194457263,236329203], [984092,984092,984092,984092,984092,984092,984092,984092,2268629,2267875,2267875,2268627,3345907,5344921,5952946,4299969,3732931,3732931,3168743,1936350,1559795], ![125448267536460,1604075484552,231404142970,4442187890], 194786695741022914⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticFinal9

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticUpper0
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HighQuadraticUpper0.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree31_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree88_0, Research6970.Height2308.MainFree.bankfree87_1, Research6970.Height2308.MainFree.bankfree127_0, Research6970.Height2308.MainFree.bankfree131_0, Research6970.Height2308.MainFree.bankfree166_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree189_0, Research6970.Height2308.MainFree.bankfree176_0, Research6970.Height2308.MainFree.bankfree170_0, Research6970.Height2308.MainFree.bankfree214_0] i
    head := Research6970.Height2308.MainHeads.src1165
    historyValues := [![15955, 159089, 734000, 3234624],
    ![25417/2, 455285/4, 522144, 2414916],
    ![54680/9, 496450/9, 522144, 8806325/4],
    ![29433/8, 535235/16, 2424034/9, 3171310/3],
    ![64334/25, 22841, 204686, 3728761/4],
    ![17323/9, 67915/4, 2751967/16, 5283795/8],
    ![18775/16, 695645/64, 3144767/25, 2500893/5],
    ![89110/121, 806965/121, 522642/7, 7683984/25],
    ![89110/121, 806965/121, 522642/7, 7683984/25],
    ![89110/121, 806965/121, 522642/7, 1479256/5],
    ![27491/49, 287341/49, 1882881/32, 3749790/13],
    ![27491/49, 642313/121, 2795491/49, 9338320/49],
    ![689574/1681, 642313/121, 2795491/49, 9338320/49],
    ![689574/1681, 7984640/1681, 4473941/98, 37100281/225],
    ![689574/1681, 5807840/1323, 9803091/242, 288330960/1849],
    ![490994/1369, 5807840/1323, 9803091/242, 288330960/1849],
    ![938035/2738, 5807840/1323, 9803091/242, 288330960/1849],
    ![462287/1369, 5807840/1323, 9803091/242, 288330960/1849],
    ![462287/1369, 23263975/5476, 104751724/2601, 110796676/729]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 41 296085 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5165, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1165⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free31_0
    · exact Research6970.Height2308.MainFree.free37_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free88_0
    · exact Research6970.Height2308.MainFree.free87_1
    · exact Research6970.Height2308.MainFree.free127_0
    · exact Research6970.Height2308.MainFree.free131_0
    · exact Research6970.Height2308.MainFree.free166_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free189_0
    · exact Research6970.Height2308.MainFree.free176_0
    · exact Research6970.Height2308.MainFree.free170_0
    · exact Research6970.Height2308.MainFree.free214_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨2851242877190322787658920695/5347570218972454787787784192, 67458255/71932196, [302959153,302959145,302959140,302959144,302959147,302959145,302959142,163046899,163046899,163046889,163046889,74214941,74214949,76434883,87566734,100410403,134804368,100000000,229446351], [1174582,1174582,1174582,1174582,1174582,1174582,1174582,2348749,2348749,2348749,2348749,5388347,5388347,5229420,4535701,3935308,2882371,3952620,1616355], ![121794712037820,1611495377784,206501715900,5397484190], 162750104356990720⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticUpper0

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticUpper1
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HighQuadraticUpper1.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree31_0, Research6970.Height2308.MainFree.bankfree43_0, Research6970.Height2308.MainFree.bankfree50_0, Research6970.Height2308.MainFree.bankfree53_0, Research6970.Height2308.MainFree.bankfree58_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree82_0, Research6970.Height2308.MainFree.bankfree76_0, Research6970.Height2308.MainFree.bankfree106_0, Research6970.Height2308.MainFree.bankfree138_0, Research6970.Height2308.MainFree.bankfree161_0, Research6970.Height2308.MainFree.bankfree126_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree214_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1164
    historyValues := [![15974, 156343, 719337, 3110269],
    ![25417/2, 108706, 522144, 2414916],
    ![54680/9, 158110/3, 522144, 1965865],
    ![29433/8, 31966, 2316752/9, 2831768/3],
    ![64334/25, 545034/25, 204686, 3728761/4],
    ![73988/49, 616418/49, 1054568/9, 4669921/9],
    ![81850/81, 231130/27, 783200/9, 6007401/16],
    ![86978/121, 784598/121, 3537008/49, 8288641/25],
    ![86978/121, 759400/121, 489436/7, 6594624/25],
    ![86978/121, 759400/121, 489436/7, 6594624/25],
    ![86978/121, 759400/121, 489436/7, 6594624/25],
    ![230860/361, 2245360/361, 66312, 6594624/25],
    ![230860/361, 272121/50, 9813072/169, 765625/4],
    ![230860/361, 272121/50, 9813072/169, 765625/4],
    ![965824/1681, 7554144/1681, 396896/9, 115853440/729],
    ![1358449/3362, 7554144/1681, 396896/9, 115853440/729],
    ![1358449/3362, 613856/147, 21213120/529, 21455024/147],
    ![1358449/3362, 5528572/1369, 33208840/867, 27699169/196],
    ![479479/1369, 5528572/1369, 33208840/867, 27699169/196],
    ![930251/2738, 5528572/1369, 33208840/867, 27699169/196],
    ![459746/1369, 5528572/1369, 33208840/867, 27699169/196]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 51 292947 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 4612, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1164⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free31_0
    · exact Research6970.Height2308.MainFree.free43_0
    · exact Research6970.Height2308.MainFree.free50_0
    · exact Research6970.Height2308.MainFree.free53_0
    · exact Research6970.Height2308.MainFree.free58_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free82_0
    · exact Research6970.Height2308.MainFree.free76_0
    · exact Research6970.Height2308.MainFree.free106_0
    · exact Research6970.Height2308.MainFree.free138_0
    · exact Research6970.Height2308.MainFree.free161_0
    · exact Research6970.Height2308.MainFree.free126_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free214_0
    · exact Research6970.Height2308.MainFree.free183_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨992780973161038004660010505/1886712158631994451800621056, 6077155/6474051, [290077864,290077849,290077851,290077853,290077857,290077857,290077855,290077856,160331157,160331150,160331147,160331152,68797757,80165575,56051186,77797652,90224839,90224839,109819387,180944996,225998193], [1240446,1240446,1240446,1240446,1240446,1240446,1240446,1240446,2393878,2393878,2393878,2393878,5830493,4971899,7200807,5135351,4401729,4401729,3582447,2099206,1644690], ![119964360808260,1615212411612,215324545240,5238058020], 155298512893227463⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 19 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HighQuadraticUpper1

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons1
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuadraticSingletons1.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree4_0, Research6970.Height2308.MainFree.bankfree9_0, Research6970.Height2308.MainFree.bankfree17_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree30_0, Research6970.Height2308.MainFree.bankfree40_0, Research6970.Height2308.MainFree.bankfree49_0, Research6970.Height2308.MainFree.bankfree58_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree98_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree126_0, Research6970.Height2308.MainFree.bankfree153_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree186_0, Research6970.Height2308.MainFree.bankfree175_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1186
    historyValues := [![15035, 166047, 771431, 3724533],
    ![12303, 130589, 1180985/2, 2777446],
    ![53398/9, 566339/9, 1180985/2, 2777446],
    ![29433/8, 607303/16, 2749178/9, 4200374/3],
    ![63824/25, 654557/25, 409431/2, 3837681/4],
    ![72196/49, 741163/49, 3340561/25, 15234907/25],
    ![20312/25, 884209/100, 760463/8, 7991929/16],
    ![95350/121, 915430/121, 4123729/49, 17567688/49],
    ![95350/121, 915430/121, 673387/9, 17567688/49],
    ![127905/242, 3090254/441, 549021/8, 17567688/49],
    ![127905/242, 3090254/441, 549021/8, 10686361/36],
    ![127905/242, 755020/121, 505197/8, 5418072/25],
    ![1358449/3362, 755020/121, 505197/8, 5418072/25],
    ![1358449/3362, 9140020/1681, 4946427/98, 40947201/196],
    ![1358449/3362, 2221984/441, 29962856/675, 127297328/675],
    ![967337/2738, 2221984/441, 29962856/675, 127297328/675],
    ![466774/1369, 2221984/441, 29962856/675, 127297328/675],
    ![459746/1369, 2221984/441, 29962856/675, 127297328/675]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 20 307237 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6841, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1186⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free4_0
    · exact Research6970.Height2308.MainFree.free9_0
    · exact Research6970.Height2308.MainFree.free17_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free30_0
    · exact Research6970.Height2308.MainFree.free40_0
    · exact Research6970.Height2308.MainFree.free49_0
    · exact Research6970.Height2308.MainFree.free58_0
    · exact Research6970.Height2308.MainFree.free74_1
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free98_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free126_0
    · exact Research6970.Height2308.MainFree.free153_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free186_0
    · exact Research6970.Height2308.MainFree.free175_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨25886428421500623726515157863/47255071257210962912032587776, 70654007/75600434, [333957999,333957984,333957989,333957992,333957992,333957991,333957990,148015701,148015701,148256961,148256950,72430119,72430106,90010241,104062727,114204776,192821551,234760187], [1030697,1030697,1030697,1030697,1030697,1030697,1030697,2598533,2598533,2594524,2594524,5530127,5530128,4412545,3782182,3430290,1956065,1572688], ![124615402463340,1605766698268,229457645690,4500796580], 183445601278128886⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons1
end Pack_R6970Height2313MainPlans01

section Pack_R6970Height2313MainPlans02

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons10
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuadraticSingletons10.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree29_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree95_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree126_0, Research6970.Height2308.MainFree.bankfree161_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree181_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree170_0] i
    head := Research6970.Height2308.MainHeads.src1177
    historyValues := [![15517, 162160, 752625, 3443689],
    ![25417/2, 121915, 553602, 2414916],
    ![54680/9, 59050, 553602, 2414916],
    ![29433/8, 143215/4, 2593784/9, 3708560/3],
    ![63052/25, 122922/5, 206024, 3924361/4],
    ![17323/9, 54655/3, 184412, 772365],
    ![18775/16, 371885/32, 132886, 2924568/5],
    ![89110/121, 863840/121, 559392/7, 2391840/7],
    ![89110/121, 863840/121, 673387/9, 2391840/7],
    ![127905/242, 2950880/441, 3343828/49, 2391840/7],
    ![127905/242, 2950880/441, 3343828/49, 9740641/36],
    ![127905/242, 703756/121, 3088044/49, 793881/4],
    ![1358449/3362, 703756/121, 3088044/49, 793881/4],
    ![1358449/3362, 8570880/1681, 2404940/49, 9482800/49],
    ![1358449/3362, 2085280/441, 5275608/121, 21073560/121],
    ![953281/2738, 2085280/441, 5275608/121, 21073560/121],
    ![953281/2738, 6268465/1369, 14096439/338, 29365561/169],
    ![462287/1369, 6268465/1369, 14096439/338, 29365561/169]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 29 305932 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6040, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1177⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free29_0
    · exact Research6970.Height2308.MainFree.free37_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free74_1
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free95_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free126_0
    · exact Research6970.Height2308.MainFree.free161_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free181_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨1520425277357315361635450613/2811199082245287223154180096, 34473783/36878723, [319289250,319289238,319289235,319289241,319289241,319289239,319289239,146060883,146060883,146060883,146060883,72694192,73937726,83121573,96184995,96035997,138131686,231820379], [1091083,1091083,1091083,1091083,1091083,1091083,1091083,2635701,2635701,2635701,2635701,5509150,5410368,4794156,4113550,4119836,2809458,1596846], ![123054893580780,1608935918356,208638341100,4902604840], 172664375411521441⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons10

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons11
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuadraticSingletons11.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree31_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree98_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree129_0, Research6970.Height2308.MainFree.bankfree161_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1176
    historyValues := [![15531, 161888, 751108, 3426055],
    ![25417/2, 242313/2, 550158, 2414916],
    ![54680/9, 528170/9, 550158, 2414916],
    ![29433/8, 284667/8, 859292/3, 1219404],
    ![64334/25, 608296/25, 204686, 3728761/4],
    ![17323/9, 108613/6, 1465989/8, 3047517/4],
    ![18775/16, 184815/16, 132886, 14424318/25],
    ![89110/121, 858510/121, 555948/7, 2359368/7],
    ![89110/121, 858510/121, 673387/9, 2359368/7],
    ![127905/242, 419516/63, 3327715/49, 2359368/7],
    ![127905/242, 419516/63, 3327715/49, 1082039/4],
    ![127905/242, 698508/121, 3064797/49, 793881/4],
    ![813/2, 698508/121, 3064797/49, 793881/4],
    ![813/2, 8512496/1681, 2388745/49, 9354060/49],
    ![813/2, 6213856/1323, 5240553/121, 20787462/121],
    ![479479/1369, 6213856/1323, 5240553/121, 20787462/121],
    ![479479/1369, 168301/37, 28008911/676, 20787462/121],
    ![930251/2738, 168301/37, 28008911/676, 20787462/121],
    ![459746/1369, 168301/37, 28008911/676, 20787462/121]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 30 305757 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5958, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1176⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free31_0
    · exact Research6970.Height2308.MainFree.free37_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free74_1
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free98_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free129_0
    · exact Research6970.Height2308.MainFree.free161_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free183_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨57590892147614199612974719/106662017523334414514257920, 6883129/7360878, [317678634,317678620,317678625,317678623,317678623,317678624,317678624,139680939,139680939,140586909,140586909,72666610,72666645,82547437,93148460,93062905,115694548,186820157,230491059], [1099319,1099319,1099319,1099319,1099319,1099319,1099319,2775508,2775508,2755656,2755656,5511341,5511339,4828230,4254376,4258688,3382122,2028396,1607770], ![122349263938380,1610369109156,222315986830,5067838720], 171942557005340942⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons11

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons12
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuadraticSingletons12.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree30_0, Research6970.Height2308.MainFree.bankfree40_0, Research6970.Height2308.MainFree.bankfree50_0, Research6970.Height2308.MainFree.bankfree57_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree96_0, Research6970.Height2308.MainFree.bankfree92_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree129_0, Research6970.Height2308.MainFree.bankfree161_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1175
    historyValues := [![15740, 161523, 749049, 3341936],
    ![25417/2, 481629/4, 546756, 2414916],
    ![54680/9, 524930/9, 546756, 2414916],
    ![29433/8, 565851/16, 854054/3, 1202826],
    ![63824/25, 609249/25, 409431/2, 3837681/4],
    ![72196/49, 690071/49, 3112093/25, 4959529/9],
    ![81850/81, 256430/27, 1157695/12, 1600503/4],
    ![81850/81, 256430/27, 1157695/12, 1600503/4],
    ![228296/289, 2211676/289, 673387/9, 42326154/121],
    ![228296/289, 569068/81, 5121253/72, 2159471/8],
    ![65315/96, 569068/81, 5121253/72, 2159471/8],
    ![65315/96, 693324/121, 6083667/98, 793881/4],
    ![813/2, 693324/121, 6083667/98, 793881/4],
    ![813/2, 8454824/1681, 4745495/98, 9226890/49],
    ![813/2, 6172384/1323, 10411851/242, 20504853/121],
    ![479479/1369, 6172384/1323, 10411851/242, 20504853/121],
    ![479479/1369, 6186313/1369, 55654375/1352, 20504853/121],
    ![930251/2738, 6186313/1369, 55654375/1352, 20504853/121],
    ![459746/1369, 6186313/1369, 55654375/1352, 20504853/121]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 31 305576 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5877, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1175⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free30_0
    · exact Research6970.Height2308.MainFree.free40_0
    · exact Research6970.Height2308.MainFree.free50_0
    · exact Research6970.Height2308.MainFree.free57_0
    · exact Research6970.Height2308.MainFree.free74_1
    · exact Research6970.Height2308.MainFree.free96_0
    · exact Research6970.Height2308.MainFree.free92_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free129_0
    · exact Research6970.Height2308.MainFree.free161_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free183_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨6017757034439586398797209269/11138194088237299946614685696, 68661503/73406998, [317079156,317079146,317079148,317079145,317079145,317079147,145491417,145491417,145491417,103936859,104728046,74761878,75679515,81892948,92675813,92591054,115248988,186374596,230151189], [1102384,1102384,1102384,1102384,1102384,1102384,2648180,2648180,2648180,3786549,3759098,5344903,5281561,4867074,4278198,4282470,3394571,2033766,1610563], ![122168854144980,1610735556336,221785769240,5096139300], 171480886728168772⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons12

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons13
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuadraticSingletons13.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree31_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree98_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree130_0, Research6970.Height2308.MainFree.bankfree161_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree186_0, Research6970.Height2308.MainFree.bankfree175_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1174
    historyValues := [![15531, 161405, 748371, 3399973],
    ![25417/2, 478669/4, 543396, 2414916],
    ![54680/9, 57970, 543396, 2414916],
    ![29433/8, 562411/16, 2546642/9, 3559358/3],
    ![64334/25, 600729/25, 204686, 3728761/4],
    ![17323/9, 214489/12, 2895431/16, 5930331/8],
    ![18775/16, 730405/64, 3300871/25, 14034537/25],
    ![89110/121, 77095/11, 549186/7, 2295612/7],
    ![89110/121, 77095/11, 673387/9, 2295612/7],
    ![127905/242, 415514/63, 6592157/98, 2295612/7],
    ![127905/242, 415514/63, 6592157/98, 18950393/72],
    ![127905/242, 62564/11, 6038307/98, 793881/4],
    ![1374849/3362, 62564/11, 6038307/98, 793881/4],
    ![1374849/3362, 8397864/1681, 4713895/98, 9101290/49],
    ![1374849/3362, 6145993/1369, 6947158/169, 25870306/153],
    ![967337/2738, 6145993/1369, 6947158/169, 25870306/153],
    ![466774/1369, 6145993/1369, 6947158/169, 25870306/153],
    ![459746/1369, 6145993/1369, 6947158/169, 25870306/153]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 32 305390 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5797, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1174⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free31_0
    · exact Research6970.Height2308.MainFree.free37_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free74_1
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free98_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free130_0
    · exact Research6970.Height2308.MainFree.free161_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free186_0
    · exact Research6970.Height2308.MainFree.free175_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨122058082288231851418754877/226898772353732255773884416, 68626659/73340554, [314422087,314422072,314422074,314422078,314422077,314422077,314422077,145623026,145623026,145623026,145623026,68904784,68904773,94886554,94153661,107985282,186602058,230003137], [1115970,1115970,1115970,1115970,1115970,1115970,1115970,2645296,2645296,2645296,2645296,5820799,5820800,4168323,4203713,3646084,2031025,1611780], ![122090265182340,1610895361508,222056449020,5002418470], 170249472518389240⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons13

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons14
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuadraticSingletons14.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree31_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree115_0, Research6970.Height2308.MainFree.bankfree168_0, Research6970.Height2308.MainFree.bankfree129_0, Research6970.Height2308.MainFree.bankfree152_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1173
    historyValues := [![15531, 161710, 749804, 3390103],
    ![25417/2, 475783/4, 540120, 2414916],
    ![54680/9, 172870/3, 540120, 2414916],
    ![29433/8, 559057/16, 2531510/9, 3511466/3],
    ![64334/25, 597063/25, 204686, 3728761/4],
    ![17323/9, 213163/12, 2877725/16, 5850537/8],
    ![18775/16, 726115/64, 656321/5, 13845699/25],
    ![89110/121, 842975/121, 545910/7, 323532],
    ![89110/121, 842975/121, 673387/9, 323532],
    ![127905/242, 2895026/441, 6561503/98, 323532],
    ![127905/242, 840110/147, 2832048/49, 1447724/7],
    ![127905/242, 840110/147, 2832048/49, 3684670/21],
    ![813/2, 840110/147, 2832048/49, 3684670/21],
    ![813/2, 8339904/1681, 2341090/49, 3684670/21],
    ![813/2, 6106681/1369, 6947158/169, 433877654/2601],
    ![479479/1369, 6106681/1369, 6947158/169, 433877654/2601],
    ![930251/2738, 6106681/1369, 6947158/169, 433877654/2601],
    ![459746/1369, 6106681/1369, 6947158/169, 433877654/2601]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 33 305197 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5719, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1173⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free31_0
    · exact Research6970.Height2308.MainFree.free37_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free74_1
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free115_0
    · exact Research6970.Height2308.MainFree.free168_0
    · exact Research6970.Height2308.MainFree.free129_0
    · exact Research6970.Height2308.MainFree.free152_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free183_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨5987624742520836296823163611/11160658712404600478347821056, 17199702/18370247, [313637889,313637877,313637875,313637879,313637879,313637878,313637879,146977963,146977956,146977956,104545966,65932416,62362787,94035274,93039338,114935996,186061605,229908834], [1119980,1119980,1119980,1119980,1119980,1119980,1119980,2615778,2615778,2615778,3765415,6090024,6451299,4209679,4259876,3404919,2037539,1612555], ![122040207263880,1610997055956,221413309950,5069252440], 169957248956828978⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons14

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons15
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuadraticSingletons15.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree31_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree96_0, Research6970.Height2308.MainFree.bankfree92_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree129_0, Research6970.Height2308.MainFree.bankfree161_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree186_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1172
    historyValues := [![15692, 160833, 745742, 3317079],
    ![25417/2, 472971/4, 536928, 2414916],
    ![54680/9, 515570/9, 536928, 9621315/4],
    ![29433/8, 555789/16, 838922/3, 1154934],
    ![64334/25, 593491/25, 204686, 3728761/4],
    ![17323/9, 211871/12, 2860473/16, 5772789/8],
    ![18775/16, 721935/64, 3262833/25, 13661703/25],
    ![89110/121, 76185/11, 542718/7, 2234628/7],
    ![89110/121, 76185/11, 673387/9, 2234628/7],
    ![89110/121, 557602/81, 5018995/72, 2073489/8],
    ![65315/96, 557602/81, 5018995/72, 2073489/8],
    ![65315/96, 61668/11, 5950989/98, 793881/4],
    ![813/2, 61668/11, 5950989/98, 793881/4],
    ![813/2, 8288216/1681, 4653065/98, 8859510/49],
    ![813/2, 6068377/1369, 6947158/169, 47567982/289],
    ![967337/2738, 6068377/1369, 6947158/169, 47567982/289],
    ![930251/2738, 6068377/1369, 6947158/169, 47567982/289],
    ![459746/1369, 6068377/1369, 6947158/169, 47567982/289]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 34 304999 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5643, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1172⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free31_0
    · exact Research6970.Height2308.MainFree.free37_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free74_1
    · exact Research6970.Height2308.MainFree.free96_0
    · exact Research6970.Height2308.MainFree.free92_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free129_0
    · exact Research6970.Height2308.MainFree.free161_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free186_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨185165143898462516014295613/345001960124991716466884608, 68429847/73082912, [312147562,312147551,312147550,312147553,312147551,312147552,312147556,161661171,161661171,94698106,119393845,74934606,79965569,93335904,92433240,115230687,185943699,229816950], [1127600,1127600,1127600,1127600,1127600,1127600,1127600,2371776,2371776,4176272,3278764,5332980,4985705,4244928,4290424,3395082,2038960,1613310], ![121991433399000,1611096078000,221273001810,5105604560], 168926674507487509⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons15

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons16
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuadraticSingletons16.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree31_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree81_0, Research6970.Height2308.MainFree.bankfree115_0, Research6970.Height2308.MainFree.bankfree168_0, Research6970.Height2308.MainFree.bankfree129_0, Research6970.Height2308.MainFree.bankfree161_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree181_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree170_0] i
    head := Research6970.Height2308.MainHeads.src1171
    historyValues := [![15597, 161237, 747473, 3363875],
    ![25417/2, 117549, 533778, 2414916],
    ![54680/9, 512570/9, 533778, 2373360],
    ![29433/8, 138141/4, 278024, 1139584],
    ![64334/25, 589966/25, 204686, 3728761/4],
    ![17323/9, 52649/3, 355431/2, 712008],
    ![18775/16, 358905/32, 3244308/25, 13480128/25],
    ![89110/121, 833160/121, 539568/7, 2204928/7],
    ![89110/121, 833160/121, 673387/9, 2204928/7],
    ![235552/441, 972544/147, 66642, 2204928/7],
    ![235552/441, 2485600/441, 57008, 9866496/49],
    ![235552/441, 2485600/441, 57008, 8370560/49],
    ![813/2, 2485600/441, 57008, 8370560/49],
    ![813/2, 8234816/1681, 2311720/49, 8370560/49],
    ![813/2, 859168/189, 5073828/121, 86564416/529],
    ![953281/2738, 859168/189, 5073828/121, 86564416/529],
    ![953281/2738, 6030577/1369, 6947158/169, 140807296/867],
    ![462287/1369, 6030577/1369, 6947158/169, 140807296/867]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 35 304795 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5568, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1171⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free31_0
    · exact Research6970.Height2308.MainFree.free37_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free74_1
    · exact Research6970.Height2308.MainFree.free81_0
    · exact Research6970.Height2308.MainFree.free115_0
    · exact Research6970.Height2308.MainFree.free168_0
    · exact Research6970.Height2308.MainFree.free129_0
    · exact Research6970.Height2308.MainFree.free161_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free181_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨169473757315547678093137071/316896399208637347004416000, 6862911/7325255, [310979180,310979166,310979166,310979172,310979172,310979171,310979169,155580504,155580504,155580504,103720329,65560125,61940025,80478391,93578008,93359553,136687812,230711528], [1133574,1133574,1133574,1133574,1133574,1133574,1133574,2472823,2472823,2472823,3795683,6123745,6494609,4951026,4232726,4243737,2841098,1605958], ![122466293292960,1610131283512,207640375200,5050047030], 168021204424629889⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons16

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons17
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuadraticSingletons17.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree35_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree53_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree61_0, Research6970.Height2308.MainFree.bankfree69_0, Research6970.Height2308.MainFree.bankfree72_0, Research6970.Height2308.MainFree.bankfree95_0, Research6970.Height2308.MainFree.bankfree115_0, Research6970.Height2308.MainFree.bankfree92_0, Research6970.Height2308.MainFree.bankfree140_0, Research6970.Height2308.MainFree.bankfree130_0, Research6970.Height2308.MainFree.bankfree164_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree186_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1170
    historyValues := [![15582, 161044, 741665, 3390238],
    ![25417/2, 467495/4, 530712, 2414916],
    ![54680/9, 509650/9, 530712, 9368975/4],
    ![29433/8, 549425/16, 2488054/9, 3373930/3],
    ![5710/3, 156620/9, 1419569/8, 11369155/16],
    ![18775/16, 713795/64, 3226277/25, 2660679/5],
    ![86978/121, 841110/121, 3788663/49, 8288641/25],
    ![73648/121, 841110/121, 3788663/49, 8288641/25],
    ![73648/121, 822285/121, 3698844/49, 1995470/7],
    ![73648/121, 822285/121, 70756, 1995470/7],
    ![73648/121, 822285/121, 70756, 1995470/7],
    ![73648/121, 822285/121, 70756, 9740641/36],
    ![73648/121, 2468810/441, 56704, 1391020/7],
    ![73648/121, 2468810/441, 56704, 1391020/7],
    ![73648/121, 2468810/441, 56704, 1391020/7],
    ![1374849/3362, 2468810/441, 56704, 1391020/7],
    ![1374849/3362, 8195960/1681, 2300800/49, 2421725/14],
    ![1374849/3362, 5993785/1369, 6947158/169, 117462244/729],
    ![967337/2738, 5993785/1369, 6947158/169, 117462244/729],
    ![930251/2738, 5993785/1369, 6947158/169, 117462244/729],
    ![459746/1369, 5993785/1369, 6947158/169, 117462244/729]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 36 304585 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5495, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1170⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free35_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free53_0
    · exact Research6970.Height2308.MainFree.free42_2
    · exact Research6970.Height2308.MainFree.free61_0
    · exact Research6970.Height2308.MainFree.free69_0
    · exact Research6970.Height2308.MainFree.free72_0
    · exact Research6970.Height2308.MainFree.free95_0
    · exact Research6970.Height2308.MainFree.free115_0
    · exact Research6970.Height2308.MainFree.free92_0
    · exact Research6970.Height2308.MainFree.free140_0
    · exact Research6970.Height2308.MainFree.free130_0
    · exact Research6970.Height2308.MainFree.free164_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free186_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨2927782241631864486565236015/5459840063855525903030812672, 34040883/36341683, [308654628,308654614,308654618,308654618,308654619,308654619,308654619,308654622,164015964,164015956,164015967,164015967,68392490,82066779,75238644,75238655,92534711,92534711,115001081,185714093,229638016], [1145460,1145460,1145460,1145460,1145460,1145460,1145460,1145460,2332645,2332645,2332645,2332645,5867201,4856757,5311993,5311993,4285309,4285309,3402661,2041727,1614780], ![121896451653120,1611288764144,220999770670,5099517710], 167057641148850990⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons17

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons18
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuadraticSingletons18.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree35_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree53_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree61_0, Research6970.Height2308.MainFree.bankfree69_0, Research6970.Height2308.MainFree.bankfree72_0, Research6970.Height2308.MainFree.bankfree95_0, Research6970.Height2308.MainFree.bankfree115_0, Research6970.Height2308.MainFree.bankfree92_0, Research6970.Height2308.MainFree.bankfree140_0, Research6970.Height2308.MainFree.bankfree130_0, Research6970.Height2308.MainFree.bankfree164_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree186_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1169
    historyValues := [![15582, 160993, 741359, 3387620],
    ![25417/2, 464831/4, 527688, 2414916],
    ![54680/9, 506770/9, 527688, 9246215/4],
    ![29433/8, 546329/16, 2474086/9, 3329722/3],
    ![5710/3, 155720/9, 1411433/8, 11220187/16],
    ![18775/16, 709835/64, 3208493/25, 13129083/25],
    ![86978/121, 836502/121, 3768143/49, 8288641/25],
    ![73648/121, 836502/121, 3768143/49, 8288641/25],
    ![73648/121, 817173/121, 525156/7, 13785266/49],
    ![73648/121, 817173/121, 70756, 13785266/49],
    ![73648/121, 817173/121, 70756, 13785266/49],
    ![73648/121, 817173/121, 70756, 9740641/36],
    ![73648/121, 2452250/441, 56704, 196249],
    ![73648/121, 2452250/441, 56704, 196249],
    ![73648/121, 2452250/441, 56704, 196249],
    ![1374849/3362, 2452250/441, 56704, 196249],
    ![1374849/3362, 8143544/1681, 326608/7, 16729955/98],
    ![1374849/3362, 5957497/1369, 6947158/169, 117462244/729],
    ![967337/2738, 5957497/1369, 6947158/169, 117462244/729],
    ![930251/2738, 5957497/1369, 6947158/169, 117462244/729],
    ![459746/1369, 5957497/1369, 6947158/169, 117462244/729]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 37 304368 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5423, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1169⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free35_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free53_0
    · exact Research6970.Height2308.MainFree.free42_2
    · exact Research6970.Height2308.MainFree.free61_0
    · exact Research6970.Height2308.MainFree.free69_0
    · exact Research6970.Height2308.MainFree.free72_0
    · exact Research6970.Height2308.MainFree.free95_0
    · exact Research6970.Height2308.MainFree.free115_0
    · exact Research6970.Height2308.MainFree.free92_0
    · exact Research6970.Height2308.MainFree.free140_0
    · exact Research6970.Height2308.MainFree.free130_0
    · exact Research6970.Height2308.MainFree.free164_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free186_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨3336393951049111996659394791/6234669379468142925685194752, 4862919/5189527, [307450002,307449987,307449992,307449992,307449992,307449993,307449993,307449992,163074421,163074431,163074429,163074431,81726301,81725991,78254338,79006931,92074998,92074998,114889381,185602393,229550967], [1151619,1151619,1151619,1151619,1151619,1151619,1151619,1151619,2348291,2348291,2348291,2348291,4876964,4876983,5103827,5051878,4308479,4308479,3406536,2043073,1615495], ![121850244302940,1611382431528,220866847670,5127090010], 166467098416661409⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons18

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons19
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuadraticSingletons19.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree35_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree53_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree61_0, Research6970.Height2308.MainFree.bankfree69_0, Research6970.Height2308.MainFree.bankfree72_0, Research6970.Height2308.MainFree.bankfree95_0, Research6970.Height2308.MainFree.bankfree112_0, Research6970.Height2308.MainFree.bankfree138_0, Research6970.Height2308.MainFree.bankfree144_0, Research6970.Height2308.MainFree.bankfree126_0, Research6970.Height2308.MainFree.bankfree164_0, Research6970.Height2308.MainFree.bankfree214_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1168
    historyValues := [![15843, 160387, 738742, 3357192],
    ![25417/2, 462241/4, 524748, 2414916],
    ![54680/9, 167990/3, 524748, 9126865/4],
    ![29433/8, 543319/16, 2460506/9, 3286742/3],
    ![5710/3, 17205, 1403523/8, 11075357/16],
    ![18775/16, 705985/64, 3191203/25, 12959613/25],
    ![86978/121, 832022/121, 3748193/49, 8288641/25],
    ![73648/121, 832022/121, 3748193/49, 8288641/25],
    ![73648/121, 812203/121, 521996/7, 13607326/49],
    ![73648/121, 812203/121, 70756, 13607326/49],
    ![73648/121, 812203/121, 70756, 13607326/49],
    ![73648/121, 812203/121, 70756, 9740641/36],
    ![73648/121, 269362/49, 225929/4, 797449/4],
    ![73648/121, 269362/49, 225929/4, 797449/4],
    ![73648/121, 160739/30, 6284096/121, 22391824/121],
    ![1358449/3362, 160739/30, 6284096/121, 22391824/121],
    ![1358449/3362, 8092584/1681, 324588/7, 1522756/9],
    ![1358449/3362, 23654827/5476, 35498036/867, 110796676/729],
    ![479479/1369, 23654827/5476, 35498036/867, 110796676/729],
    ![930251/2738, 23654827/5476, 35498036/867, 110796676/729],
    ![459746/1369, 23654827/5476, 35498036/867, 110796676/729]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 38 304146 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5353, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1168⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free35_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free53_0
    · exact Research6970.Height2308.MainFree.free42_2
    · exact Research6970.Height2308.MainFree.free61_0
    · exact Research6970.Height2308.MainFree.free69_0
    · exact Research6970.Height2308.MainFree.free72_0
    · exact Research6970.Height2308.MainFree.free95_0
    · exact Research6970.Height2308.MainFree.free112_0
    · exact Research6970.Height2308.MainFree.free138_0
    · exact Research6970.Height2308.MainFree.free144_0
    · exact Research6970.Height2308.MainFree.free126_0
    · exact Research6970.Height2308.MainFree.free164_0
    · exact Research6970.Height2308.MainFree.free214_0
    · exact Research6970.Height2308.MainFree.free183_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨138170857514407226290564865/257947098992175861221818368, 403885/430934, [306946693,306946678,306946685,306946684,306946682,306946686,306946686,306946686,162314360,162314353,162314364,162314364,81623716,81623716,65503315,77678603,91187458,91187458,114146927,185272536,229298395], [1154193,1154193,1154193,1154193,1154193,1154193,1154193,1154193,2360922,2360922,2360922,2360922,4883052,4883052,6129565,5143569,4353212,4353212,3432297,2047049,1617571], ![121716174033900,1611654967400,220474317840,5180322280], 165776837361615108⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons19

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons2
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuadraticSingletons2.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree5_0, Research6970.Height2308.MainFree.bankfree9_0, Research6970.Height2308.MainFree.bankfree17_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree30_0, Research6970.Height2308.MainFree.bankfree40_0, Research6970.Height2308.MainFree.bankfree49_0, Research6970.Height2308.MainFree.bankfree58_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree98_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree126_0, Research6970.Height2308.MainFree.bankfree161_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree162_0, Research6970.Height2308.MainFree.bankfree178_0, Research6970.Height2308.MainFree.bankfree170_0, Research6970.Height2308.MainFree.bankfree213_0] i
    head := Research6970.Height2308.MainHeads.src1185
    historyValues := [![15071, 165477, 770161, 3696313],
    ![12303, 129743, 1173371/2, 2739282],
    ![53398/9, 562673/9, 1173371/2, 2739282],
    ![29433/8, 603261/16, 303438, 1380886],
    ![63824/25, 650139/25, 409431/2, 3837681/4],
    ![72196/49, 736181/49, 3318283/25, 15025569/25],
    ![20312/25, 878663/100, 760463/8, 7991929/16],
    ![95350/121, 908850/121, 584901/7, 17326296/49],
    ![95350/121, 908850/121, 673387/9, 17326296/49],
    ![127905/242, 3073898/441, 549021/8, 17326296/49],
    ![127905/242, 3073898/441, 549021/8, 10686361/36],
    ![127905/242, 749004/121, 505197/8, 5343624/25],
    ![1358449/3362, 749004/121, 505197/8, 5343624/25],
    ![1358449/3362, 9074264/1681, 2480600/49, 169484640/841],
    ![1358449/3362, 6617824/1323, 29748536/675, 41849392/225],
    ![484796/1323, 6617824/1323, 29748536/675, 41849392/225],
    ![471856/1369, 6617824/1323, 29748536/675, 41849392/225],
    ![462287/1369, 6617824/1323, 29748536/675, 41849392/225],
    ![462287/1369, 6624793/1369, 59558065/1352, 41849392/225]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 21 307116 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6747, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1185⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free5_0
    · exact Research6970.Height2308.MainFree.free9_0
    · exact Research6970.Height2308.MainFree.free17_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free30_0
    · exact Research6970.Height2308.MainFree.free40_0
    · exact Research6970.Height2308.MainFree.free49_0
    · exact Research6970.Height2308.MainFree.free58_0
    · exact Research6970.Height2308.MainFree.free74_1
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free98_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free126_0
    · exact Research6970.Height2308.MainFree.free161_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free162_0
    · exact Research6970.Height2308.MainFree.free178_0
    · exact Research6970.Height2308.MainFree.free170_0
    · exact Research6970.Height2308.MainFree.free213_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨6430310107558893913653346769/11774902131595189923295002624, 35257387/37737987, [332228561,332228549,332228551,332228555,332228553,332228551,332228550,150340264,150340264,150382187,150382180,72493931,72493931,87492190,87490355,102009534,142036745,101901537,234786894], [1035434,1035434,1035434,1035434,1035434,1035434,1035434,2559904,2559904,2559208,2559208,5525058,5525058,4539458,4539550,3867851,2723884,3872406,1572469], ![124629579073080,1605738154476,211308204600,4630341000], 181470976353951804⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons2

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons20
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuadraticSingletons20.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree35_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree53_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree61_0, Research6970.Height2308.MainFree.bankfree69_0, Research6970.Height2308.MainFree.bankfree72_0, Research6970.Height2308.MainFree.bankfree95_0, Research6970.Height2308.MainFree.bankfree112_0, Research6970.Height2308.MainFree.bankfree138_0, Research6970.Height2308.MainFree.bankfree144_0, Research6970.Height2308.MainFree.bankfree126_0, Research6970.Height2308.MainFree.bankfree165_0, Research6970.Height2308.MainFree.bankfree214_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1167
    historyValues := [![15843, 160115, 737450, 3346856],
    ![25417/2, 459725/4, 522144, 2414916],
    ![54680/9, 501250/9, 522144, 9010925/4],
    ![29433/8, 540395/16, 2447314/9, 3244990/3],
    ![5710/3, 153995/9, 1395839/8, 10934665/16],
    ![18775/16, 702245/64, 3174407/25, 2558997/5],
    ![86978/121, 827670/121, 3728813/49, 8288641/25],
    ![73648/121, 827670/121, 3728813/49, 8288641/25],
    ![73648/121, 807375/121, 3632484/49, 1919210/7],
    ![73648/121, 807375/121, 70756, 1919210/7],
    ![73648/121, 807375/121, 70756, 1919210/7],
    ![73648/121, 807375/121, 70756, 9740641/36],
    ![73648/121, 2408890/441, 225929/4, 797449/4],
    ![73648/121, 2408890/441, 225929/4, 797449/4],
    ![73648/121, 159719/30, 6284096/121, 22391824/121],
    ![1358449/3362, 159719/30, 6284096/121, 22391824/121],
    ![1358449/3362, 8059460/1681, 2257029/49, 37982569/225],
    ![1358449/3362, 23513455/5476, 105863884/2601, 110796676/729],
    ![479479/1369, 23513455/5476, 105863884/2601, 110796676/729],
    ![930251/2738, 23513455/5476, 105863884/2601, 110796676/729],
    ![459746/1369, 23513455/5476, 105863884/2601, 110796676/729]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 39 303918 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5285, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1167⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free35_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free53_0
    · exact Research6970.Height2308.MainFree.free42_2
    · exact Research6970.Height2308.MainFree.free61_0
    · exact Research6970.Height2308.MainFree.free69_0
    · exact Research6970.Height2308.MainFree.free72_0
    · exact Research6970.Height2308.MainFree.free95_0
    · exact Research6970.Height2308.MainFree.free112_0
    · exact Research6970.Height2308.MainFree.free138_0
    · exact Research6970.Height2308.MainFree.free144_0
    · exact Research6970.Height2308.MainFree.free126_0
    · exact Research6970.Height2308.MainFree.free165_0
    · exact Research6970.Height2308.MainFree.free214_0
    · exact Research6970.Height2308.MainFree.free183_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨1443184800395227187932148079/2698979148571090650499383296, 33878119/36135148, [305485985,305485973,305485970,305485974,305485978,305485979,305485976,305485975,164154612,164154611,164154621,164154621,82815444,82815444,65404433,78338597,92139005,92139005,113749798,184875407,228995542], [1161662,1161662,1161662,1161662,1161662,1161662,1161662,1161662,2330341,2330341,2330341,2330341,4812324,4812324,6139695,5098011,4305253,4305253,3446076,2051835,1620060], ![121555413604440,1611981609128,220001734330,5123251070], 164906474103127295⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons20
end Pack_R6970Height2313MainPlans02

section Pack_R6970Height2313MainPlans03

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons0
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons0.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree1_0, Research6970.Height2308.MainFree.bankfree8_0, Research6970.Height2308.MainFree.bankfree14_0, Research6970.Height2308.MainFree.bankfree23_0, Research6970.Height2308.MainFree.bankfree26_0, Research6970.Height2308.MainFree.bankfree32_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree95_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree121_0, Research6970.Height2308.MainFree.bankfree150_0, Research6970.Height2308.MainFree.bankfree210_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1389
    historyValues := [![14353, 171235, 797567, 4201542],
    ![23965/2, 283745/2, 642389, 3382071],
    ![17372/3, 614908/9, 630208, 3356224],
    ![3599, 329291/8, 2984912/9, 5060462/3],
    ![60658/25, 709744/25, 211854, 1110916],
    ![16211/9, 189503/9, 211854, 1110916],
    ![18775/16, 53175/4, 132886, 651249],
    ![89110/121, 90030/11, 641124/7, 3162456/7],
    ![89110/121, 90030/11, 641124/7, 3162456/7],
    ![127905/242, 82000/11, 549021/8, 3162456/7],
    ![127905/242, 82000/11, 549021/8, 4154051/12],
    ![127905/242, 75300/11, 323532/5, 6324912/25],
    ![672960/1681, 75300/11, 323532/5, 6324912/25],
    ![672960/1681, 9885160/1681, 44411096/841, 209265144/841],
    ![672960/1681, 390873/74, 130285638/2809, 3426201/16],
    ![479479/1369, 390873/74, 130285638/2809, 3426201/16],
    ![930251/2738, 390873/74, 130285638/2809, 3426201/16],
    ![459746/1369, 390873/74, 130285638/2809, 3426201/16]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 4 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 7986, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1389⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free1_0
    · exact Research6970.Height2308.MainFree.free8_0
    · exact Research6970.Height2308.MainFree.free14_0
    · exact Research6970.Height2308.MainFree.free23_0
    · exact Research6970.Height2308.MainFree.free26_0
    · exact Research6970.Height2308.MainFree.free32_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free95_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free121_0
    · exact Research6970.Height2308.MainFree.free150_0
    · exact Research6970.Height2308.MainFree.free210_0
    · exact Research6970.Height2308.MainFree.free183_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨6577610796657997/11974812696051712, 42943347685097589205905769/47516677408525604184129536, [353292918,353292908,353292905,353292911,353292909,353292909,353292907,172941279,172941274,172941290,172941280,82487924,83025611,110000858,108772278,124673421,195799030,237352899], [977735,977735,977735,977735,977735,977735,977735,2195670,2195670,2195670,2195670,4831762,4799851,3576150,3618778,3131255,1920179,1551382], ![125991665847180,1602971513556,233000845700,4306345820], 197190437998631632⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons0

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons1
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons1.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree2_0, Research6970.Height2308.MainFree.bankfree8_0, Research6970.Height2308.MainFree.bankfree14_0, Research6970.Height2308.MainFree.bankfree23_0, Research6970.Height2308.MainFree.bankfree25_0, Research6970.Height2308.MainFree.bankfree32_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree73_0, Research6970.Height2308.MainFree.bankfree95_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree121_0, Research6970.Height2308.MainFree.bankfree152_0, Research6970.Height2308.MainFree.bankfree198_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree210_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1390
    historyValues := [![14419, 170059, 796650, 4143084],
    ![23965/2, 282065/2, 638597, 3341415],
    ![17372/3, 611260/9, 630208, 3341415],
    ![3599, 327275/8, 2966672/9, 4999630/3],
    ![60148/25, 142022/5, 211365, 4558225/4],
    ![16211/9, 188375/9, 211365, 8880195/8],
    ![18775/16, 52845/4, 132886, 651249],
    ![89110/121, 984090/121, 637092/7, 3124440/7],
    ![89110/121, 984090/121, 637092/7, 3124440/7],
    ![232688/441, 3342464/441, 3671083/49, 3124440/7],
    ![232688/441, 3342464/441, 3671083/49, 4104115/12],
    ![232688/441, 822156/121, 1605564/25, 1249776/5],
    ![672960/1681, 822156/121, 1605564/25, 1249776/5],
    ![672960/1681, 9850920/1681, 44161488/841, 202331160/841],
    ![672960/1681, 2392360/441, 3587176/75, 116349885/529],
    ![479479/1369, 2392360/441, 3587176/75, 116349885/529],
    ![479479/1369, 14367885/2738, 129440934/2809, 3426201/16],
    ![930251/2738, 14367885/2738, 129440934/2809, 3426201/16],
    ![459746/1369, 14367885/2738, 129440934/2809, 3426201/16]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 5 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 7890, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1390⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free2_0
    · exact Research6970.Height2308.MainFree.free8_0
    · exact Research6970.Height2308.MainFree.free14_0
    · exact Research6970.Height2308.MainFree.free23_0
    · exact Research6970.Height2308.MainFree.free25_0
    · exact Research6970.Height2308.MainFree.free32_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free73_0
    · exact Research6970.Height2308.MainFree.free95_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free121_0
    · exact Research6970.Height2308.MainFree.free152_0
    · exact Research6970.Height2308.MainFree.free198_0
    · exact Research6970.Height2308.MainFree.free183_0
    · exact Research6970.Height2308.MainFree.free210_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨326083138347755/594628654923776, 213488353393236631158637/234331282928250533183488, [351571928,351571921,351571920,351571917,351571922,351571917,351571919,148209004,148209011,148209011,148209009,80404085,82644606,93679551,101887254,101887243,124170259,195295867,236969013], [982449,982449,982449,982449,982449,982449,982449,2595321,2595321,2595321,2595321,4955436,4822464,4227608,3873009,3873009,3145313,1926243,1554537], ![125787891480660,1603385569032,232402081730,4608880710], 195602722614783229⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons1

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons10
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons10.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree4_0, Research6970.Height2308.MainFree.bankfree9_0, Research6970.Height2308.MainFree.bankfree17_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree32_0, Research6970.Height2308.MainFree.bankfree41_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree48_0, Research6970.Height2308.MainFree.bankfree58_0, Research6970.Height2308.MainFree.bankfree73_0, Research6970.Height2308.MainFree.bankfree74_0, Research6970.Height2308.MainFree.bankfree74_2, Research6970.Height2308.MainFree.bankfree104_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree150_0, Research6970.Height2308.MainFree.bankfree121_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1399
    historyValues := [![14634, 168180, 783590, 4072408],
    ![12303, 132488, 599038, 2863112],
    ![53398/9, 574568/9, 599038, 2863112],
    ![29433/8, 77047/2, 2790112/9, 4329928/3],
    ![16211/9, 39673/2, 203372, 3968513/4],
    ![73046/81, 884606/81, 335537/3, 5297815/9],
    ![73648/121, 1152438/121, 5210692/49, 5297815/9],
    ![73648/121, 1152438/121, 316831/3, 4398685/9],
    ![73648/121, 930200/121, 4189772/49, 18109536/49],
    ![232688/441, 3203356/441, 501994/7, 18109536/49],
    ![232688/441, 3203356/441, 501994/7, 18109536/49],
    ![5584/11, 3203356/441, 501994/7, 18109536/49],
    ![5584/11, 2614996/361, 11730136/169, 47629208/169],
    ![5584/11, 768524/121, 505197/8, 5585184/25],
    ![5584/11, 9250040/1681, 4959107/98, 184790608/841],
    ![672960/1681, 9250040/1681, 4959107/98, 184790608/841],
    ![672960/1681, 967712/189, 30443936/675, 131223616/675],
    ![672960/1681, 6778513/1369, 27788632/625, 535007032/2809],
    ![479479/1369, 6778513/1369, 27788632/625, 535007032/2809],
    ![930251/2738, 6778513/1369, 27788632/625, 535007032/2809],
    ![459746/1369, 6778513/1369, 27788632/625, 535007032/2809]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 14 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 7052, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1399⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free4_0
    · exact Research6970.Height2308.MainFree.free9_0
    · exact Research6970.Height2308.MainFree.free17_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free32_0
    · exact Research6970.Height2308.MainFree.free41_0
    · exact Research6970.Height2308.MainFree.free42_2
    · exact Research6970.Height2308.MainFree.free48_0
    · exact Research6970.Height2308.MainFree.free58_0
    · exact Research6970.Height2308.MainFree.free73_0
    · exact Research6970.Height2308.MainFree.free74_0
    · exact Research6970.Height2308.MainFree.free74_2
    · exact Research6970.Height2308.MainFree.free104_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free150_0
    · exact Research6970.Height2308.MainFree.free121_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free183_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨831779333152600365053155221/1523638734923979788614893568, 71832909/76792016, [337653628,337653616,337653614,337653613,337653617,337653617,337653617,337653620,166883298,166965237,166965231,166883337,166965229,74761592,71417432,88842587,102844584,102844584,120995699,192121308,234539377], [1020574,1020574,1020574,1020574,1020574,1020574,1020574,1020574,2284996,2283635,2283635,2284996,2283635,5344923,5610572,4471396,3832625,3832625,3234009,1964504,1574503], ![124498192099140,1606004996528,228624356520,4560823920], 186440638652758997⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons10

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons11
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons11.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree4_0, Research6970.Height2308.MainFree.bankfree9_0, Research6970.Height2308.MainFree.bankfree17_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree30_0, Research6970.Height2308.MainFree.bankfree40_0, Research6970.Height2308.MainFree.bankfree49_0, Research6970.Height2308.MainFree.bankfree58_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree98_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree126_0, Research6970.Height2308.MainFree.bankfree153_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree184_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1400
    historyValues := [![15035, 166413, 773505, 3744297],
    ![12303, 131687, 1190867/2, 2826978],
    ![53398/9, 571097/9, 1190867/2, 2826978],
    ![29433/8, 612549/16, 308094, 1425094],
    ![63824/25, 660291/25, 409431/2, 3837681/4],
    ![72196/49, 747629/49, 134779, 15506601/25],
    ![20312/25, 891407/100, 760463/8, 7991929/16],
    ![95350/121, 923970/121, 4161915/49, 17880984/49],
    ![95350/121, 923970/121, 673387/9, 12967201/36],
    ![127905/242, 3111482/441, 549021/8, 12967201/36],
    ![127905/242, 3111482/441, 549021/8, 10686361/36],
    ![127905/242, 69348/11, 505197/8, 5514696/25],
    ![1358449/3362, 69348/11, 505197/8, 5514696/25],
    ![1358449/3362, 9225420/1681, 4946427/98, 178224948/841],
    ![1358449/3362, 6728416/1323, 30241016/675, 43189168/225],
    ![481425/1369, 6728416/1323, 30241016/675, 43189168/225],
    ![481425/1369, 6733657/1369, 27788632/625, 528254958/2809],
    ![930251/2738, 6733657/1369, 27788632/625, 528254958/2809],
    ![459746/1369, 6733657/1369, 27788632/625, 528254958/2809]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 15 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6963, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1400⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free4_0
    · exact Research6970.Height2308.MainFree.free9_0
    · exact Research6970.Height2308.MainFree.free17_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free30_0
    · exact Research6970.Height2308.MainFree.free40_0
    · exact Research6970.Height2308.MainFree.free49_0
    · exact Research6970.Height2308.MainFree.free58_0
    · exact Research6970.Height2308.MainFree.free74_1
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free98_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free126_0
    · exact Research6970.Height2308.MainFree.free153_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free184_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨26099504437264991651809700893/47509503628842118422846242816, 70857259/75803686, [336365181,336365168,336365167,336365171,336365172,336365174,336365171,146408066,146408066,146408066,146408066,73161143,73161145,88186887,101257802,101257802,121049274,191983234,234431775], [1024103,1024103,1024103,1024103,1024103,1024103,1024103,2628093,2628093,2628093,2628093,5472057,5472057,4504444,3899561,3899561,3232512,1966169,1575387], ![124441074805500,1606120876440,228460048460,4640477590], 184553006150400765⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons11

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons21
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuadraticSingletons21.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree35_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree53_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree61_0, Research6970.Height2308.MainFree.bankfree69_0, Research6970.Height2308.MainFree.bankfree72_0, Research6970.Height2308.MainFree.bankfree95_0, Research6970.Height2308.MainFree.bankfree112_0, Research6970.Height2308.MainFree.bankfree138_0, Research6970.Height2308.MainFree.bankfree144_0, Research6970.Height2308.MainFree.bankfree131_0, Research6970.Height2308.MainFree.bankfree164_0, Research6970.Height2308.MainFree.bankfree214_0, Research6970.Height2308.MainFree.bankfree186_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1166
    historyValues := [![15843, 159851, 736196, 3336824],
    ![25417/2, 457283/4, 522144, 2414916],
    ![54680/9, 498610/9, 522144, 8898395/4],
    ![29433/8, 537557/16, 2434510/9, 3204466/3],
    ![5710/3, 153170/9, 1388381/8, 10798111/16],
    ![18775/16, 698615/64, 631621/5, 12635199/25],
    ![86978/121, 823446/121, 3710003/49, 8288641/25],
    ![73648/121, 823446/121, 3710003/49, 8288641/25],
    ![73648/121, 802689/121, 3611628/49, 13266698/49],
    ![73648/121, 802689/121, 70756, 13266698/49],
    ![73648/121, 802689/121, 70756, 13266698/49],
    ![73648/121, 802689/121, 70756, 32576998/121],
    ![73648/121, 2393974/441, 225929/4, 797449/4],
    ![73648/121, 2393974/441, 225929/4, 797449/4],
    ![73648/121, 158729/30, 6284096/121, 22391824/121],
    ![689574/1681, 158729/30, 6284096/121, 22391824/121],
    ![689574/1681, 7995032/1681, 2245048/49, 1522756/9],
    ![689574/1681, 23376241/5476, 105252196/2601, 110796676/729],
    ![967337/2738, 23376241/5476, 105252196/2601, 110796676/729],
    ![930251/2738, 23376241/5476, 105252196/2601, 110796676/729],
    ![459746/1369, 23376241/5476, 105252196/2601, 110796676/729]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 40 303684 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5219, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1166⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free35_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free53_0
    · exact Research6970.Height2308.MainFree.free42_2
    · exact Research6970.Height2308.MainFree.free61_0
    · exact Research6970.Height2308.MainFree.free69_0
    · exact Research6970.Height2308.MainFree.free72_0
    · exact Research6970.Height2308.MainFree.free95_0
    · exact Research6970.Height2308.MainFree.free112_0
    · exact Research6970.Height2308.MainFree.free138_0
    · exact Research6970.Height2308.MainFree.free144_0
    · exact Research6970.Height2308.MainFree.free131_0
    · exact Research6970.Height2308.MainFree.free164_0
    · exact Research6970.Height2308.MainFree.free214_0
    · exact Research6970.Height2308.MainFree.free186_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨1640878558973476060323401847/3074066281618408916358529024, 16914327/18036851, [304068239,304068224,304068224,304068233,304068232,304068229,304068230,304068232,163030851,163030851,163030851,163030853,82917013,82917013,73546344,73546367,91205513,91205513,113776946,184489958,228701597], [1168911,1168911,1168911,1168911,1168911,1168911,1168911,1168911,2349015,2349015,2349015,2349015,4806296,4806296,5441458,5441457,4352302,4352302,3445134,2056481,1622475], ![121399381719540,1612298224048,219543050020,5179239380], 164045756533694842⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons21

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons3
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuadraticSingletons3.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree5_0, Research6970.Height2308.MainFree.bankfree9_0, Research6970.Height2308.MainFree.bankfree17_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree30_0, Research6970.Height2308.MainFree.bankfree40_0, Research6970.Height2308.MainFree.bankfree49_0, Research6970.Height2308.MainFree.bankfree58_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree98_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree126_0, Research6970.Height2308.MainFree.bankfree161_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree160_0, Research6970.Height2308.MainFree.bankfree177_0, Research6970.Height2308.MainFree.bankfree170_0] i
    head := Research6970.Height2308.MainHeads.src1184
    historyValues := [![15071, 165198, 768580, 3681247],
    ![12303, 128906, 582919, 2701524],
    ![53398/9, 559046/9, 582919, 2701524],
    ![29433/8, 299631/8, 904300/3, 1361852],
    ![63824/25, 645768/25, 409431/2, 3837681/4],
    ![72196/49, 731252/49, 3296242/25, 14818458/25],
    ![20312/25, 218294/25, 760463/8, 7991929/16],
    ![95350/121, 902340/121, 4065198/49, 17087472/49],
    ![95350/121, 902340/121, 673387/9, 17087472/49],
    ![127905/242, 3057716/441, 549021/8, 17087472/49],
    ![127905/242, 3057716/441, 549021/8, 10686361/36],
    ![127905/242, 743052/121, 505197/8, 5269968/25],
    ![1358449/3362, 743052/121, 505197/8, 5269968/25],
    ![1358449/3362, 9008048/1681, 2480600/49, 9859600/49],
    ![1358449/3362, 6570208/1323, 5303280/121, 41272544/225],
    ![482572/1323, 6570208/1323, 5303280/121, 41272544/225],
    ![469910/1369, 6570208/1323, 5303280/121, 41272544/225],
    ![462287/1369, 6570208/1323, 5303280/121, 41272544/225]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 22 306989 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6654, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1184⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free5_0
    · exact Research6970.Height2308.MainFree.free9_0
    · exact Research6970.Height2308.MainFree.free17_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free30_0
    · exact Research6970.Height2308.MainFree.free40_0
    · exact Research6970.Height2308.MainFree.free49_0
    · exact Research6970.Height2308.MainFree.free58_0
    · exact Research6970.Height2308.MainFree.free74_1
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free98_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free126_0
    · exact Research6970.Height2308.MainFree.free161_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free160_0
    · exact Research6970.Height2308.MainFree.free177_0
    · exact Research6970.Height2308.MainFree.free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨3194931535664982872105790439/5863304213026587592466890752, 17589959/18830259, [330390230,330390217,330390222,330390220,330390220,330390220,330390220,161882079,161882079,162174493,162174483,72565321,72565310,87124449,86436716,105370284,141313182,235003192], [1040470,1040470,1040470,1040470,1040470,1040470,1040470,2368105,2368105,2363246,2363246,5519387,5519388,4557992,4597405,3736815,2739740,1570691], ![124744394377440,1605504679148,211502872800,4689353100], 180542060612061125⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons3

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons4
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuadraticSingletons4.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree5_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree30_0, Research6970.Height2308.MainFree.bankfree40_0, Research6970.Height2308.MainFree.bankfree49_0, Research6970.Height2308.MainFree.bankfree58_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree98_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree126_0, Research6970.Height2308.MainFree.bankfree153_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree180_0, Research6970.Height2308.MainFree.bankfree170_0] i
    head := Research6970.Height2308.MainHeads.src1183
    historyValues := [![15269, 164303, 765663, 3600292],
    ![25417/2, 507011/4, 575568, 5099451/2],
    ![54680/9, 552370/9, 575568, 5099451/2],
    ![29433/8, 595349/16, 2695246/9, 4029682/3],
    ![63824/25, 641491/25, 409431/2, 3837681/4],
    ![72196/49, 726429/49, 130987, 14615801/25],
    ![20312/25, 867807/100, 760463/8, 7991929/16],
    ![95350/121, 895970/121, 4036715/49, 16853784/49],
    ![95350/121, 895970/121, 673387/9, 16853784/49],
    ![127905/242, 3041882/441, 549021/8, 16853784/49],
    ![127905/242, 3041882/441, 549021/8, 10686361/36],
    ![127905/242, 737228/121, 505197/8, 5197896/25],
    ![1358449/3362, 737228/121, 505197/8, 5197896/25],
    ![1358449/3362, 8945420/1681, 4946427/98, 5197896/25],
    ![1358449/3362, 6523616/1323, 5303280/121, 122124304/675],
    ![1358449/3362, 6532057/1369, 58732457/1352, 122124304/675],
    ![476343/1369, 6532057/1369, 58732457/1352, 122124304/675],
    ![462287/1369, 6532057/1369, 58732457/1352, 122124304/675]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 23 306855 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6563, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1183⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free5_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free30_0
    · exact Research6970.Height2308.MainFree.free40_0
    · exact Research6970.Height2308.MainFree.free49_0
    · exact Research6970.Height2308.MainFree.free58_0
    · exact Research6970.Height2308.MainFree.free74_1
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free98_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free126_0
    · exact Research6970.Height2308.MainFree.free153_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free180_0
    · exact Research6970.Height2308.MainFree.free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨3621883274145231020955623043/6650151613365219551294259200, 70088743/75035170, [329283563,329283549,329283549,329283548,329283553,329283555,329283552,150704272,150704272,150704287,150704287,71634678,68220569,86615503,96210179,96512784,140965382,234014845], [1043501,1043501,1043501,1043501,1043501,1043501,1043501,2553855,2553855,2553855,2553855,5593314,5882773,4586794,4112488,4099723,2747362,1578813], ![124219760022900,1606570267640,210613360500,4893860720], 179300890716402766⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons4

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons5
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuadraticSingletons5.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree5_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree29_0, Research6970.Height2308.MainFree.bankfree35_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree95_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree126_0, Research6970.Height2308.MainFree.bankfree153_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree180_0, Research6970.Height2308.MainFree.bankfree170_0] i
    head := Research6970.Height2308.MainHeads.src1182
    historyValues := [![15221, 163740, 761926, 3621041],
    ![25417/2, 125911, 571746, 2514372],
    ![54680/9, 60970, 571746, 2514372],
    ![29433/8, 147859/4, 2677592/9, 3973808/3],
    ![63052/25, 634482/25, 206024, 3924361/4],
    ![5710/3, 112555/6, 764985/4, 1673821/2],
    ![18775/16, 383765/32, 132886, 15668712/25],
    ![89110/121, 891920/121, 577536/7, 2562912/7],
    ![89110/121, 891920/121, 577536/7, 2562912/7],
    ![127905/242, 3026048/441, 549021/8, 2562912/7],
    ![127905/242, 3026048/441, 549021/8, 2524889/9],
    ![127905/242, 731404/121, 505197/8, 5125824/25],
    ![1358449/3362, 731404/121, 505197/8, 5125824/25],
    ![1358449/3362, 8881720/1681, 4946427/98, 5125824/25],
    ![1358449/3362, 2159008/441, 5303280/121, 21641104/121],
    ![1358449/3362, 6486193/1369, 14581035/338, 21641104/121],
    ![476343/1369, 6486193/1369, 14581035/338, 21641104/121],
    ![462287/1369, 6486193/1369, 14581035/338, 21641104/121]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 24 306716 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6472, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1182⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free5_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free29_0
    · exact Research6970.Height2308.MainFree.free35_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free95_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free126_0
    · exact Research6970.Height2308.MainFree.free153_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free180_0
    · exact Research6970.Height2308.MainFree.free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨261114357947598195114347591/480185045713223177245556736, 23240839/24889648, [326609212,326609201,326609202,326609206,326609203,326609204,326609201,147888909,147888909,147937692,147937681,71518743,68284463,86258008,95794473,96012216,140464813,233633016], [1053655,1053655,1053655,1053655,1053655,1053655,1053655,2600640,2600640,2599830,2599830,5602524,5876986,4608011,4130024,4120839,2758331,1581951], ![124017077553120,1606982054364,210269714400,4914728560], 177614528055986383⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons5

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons6
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuadraticSingletons6.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree5_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree29_0, Research6970.Height2308.MainFree.bankfree35_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree95_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree126_0, Research6970.Height2308.MainFree.bankfree149_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree181_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree170_0] i
    head := Research6970.Height2308.MainHeads.src1181
    historyValues := [![15221, 163473, 760413, 3606623],
    ![25417/2, 500351/4, 568008, 4959591/2],
    ![54680/9, 545170/9, 568008, 4959591/2],
    ![29433/8, 587609/16, 2660326/9, 3919162/3],
    ![63052/25, 630388/25, 206024, 3924361/4],
    ![5710/3, 167720/9, 1519913/8, 13206427/16],
    ![18775/16, 762635/64, 132886, 15453243/25],
    ![89110/121, 886135/121, 573798/7, 2527668/7],
    ![89110/121, 886135/121, 573798/7, 2527668/7],
    ![127905/242, 3010562/441, 549021/8, 2527668/7],
    ![127905/242, 3010562/441, 549021/8, 19921343/72],
    ![127905/242, 725708/121, 505197/8, 5055336/25],
    ![1358449/3362, 725708/121, 505197/8, 5055336/25],
    ![1358449/3362, 26979/5, 98841/2, 5055336/25],
    ![1358449/3362, 6431456/1323, 5303280/121, 21641104/121],
    ![953281/2738, 6431456/1323, 5303280/121, 21641104/121],
    ![953281/2738, 6441337/1369, 57924797/1352, 21641104/121],
    ![462287/1369, 6441337/1369, 57924797/1352, 21641104/121]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 25 306571 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6383, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1181⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free5_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free29_0
    · exact Research6970.Height2308.MainFree.free35_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free95_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free126_0
    · exact Research6970.Height2308.MainFree.free149_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free181_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨508753705810113972925262113/937038136980452449294745600, 1421989/1520830, [324836599,324836589,324836587,324836591,324836589,324836588,324836589,140278105,140278105,140880848,140880838,71405388,67700389,85373226,97016510,97011883,140018443,233259579], [1062719,1062719,1062719,1062719,1062719,1062719,1062719,2762422,2762422,2749214,2749214,5611528,5929889,4660522,4078474,4078669,2768113,1585020], ![123818849724780,1607384773836,209933621100,4853616110], 176523981370473639⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons6

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons7
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuadraticSingletons7.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree5_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree29_0, Research6970.Height2308.MainFree.bankfree35_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree95_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree126_0, Research6970.Height2308.MainFree.bankfree149_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree180_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree170_0] i
    head := Research6970.Height2308.MainHeads.src1180
    historyValues := [![15221, 163212, 758934, 3592529],
    ![25417/2, 124283, 564354, 2445996],
    ![54680/9, 541690/9, 564354, 2445996],
    ![29433/8, 145967/4, 2643448/9, 3865744/3],
    ![63052/25, 626386/25, 206024, 3924361/4],
    ![5710/3, 333265/18, 755041/4, 1628303/2],
    ![18775/16, 378925/32, 132886, 15242616/25],
    ![89110/121, 880480/121, 570144/7, 2493216/7],
    ![89110/121, 880480/121, 570144/7, 2493216/7],
    ![127905/242, 2995424/441, 549021/8, 2493216/7],
    ![127905/242, 2995424/441, 549021/8, 2456227/9],
    ![127905/242, 720140/121, 505197/8, 4986432/25],
    ![1358449/3362, 720140/121, 505197/8, 4986432/25],
    ![1358449/3362, 214353/40, 2405205/49, 4986432/25],
    ![1358449/3362, 912416/189, 5303280/121, 21641104/121],
    ![476343/1369, 912416/189, 5303280/121, 21641104/121],
    ![476343/1369, 6397489/1369, 14383607/338, 29853271/169],
    ![462287/1369, 6397489/1369, 14383607/338, 29853271/169]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 26 306420 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6296, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1180⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free5_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free29_0
    · exact Research6970.Height2308.MainFree.free35_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free95_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free126_0
    · exact Research6970.Height2308.MainFree.free149_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free180_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨774537757851980960321860331/1429263576082354072717361152, 34782659/37187864, [323103820,323103810,323103806,323103814,323103813,323103811,323103810,147212644,147212644,147238577,147238580,71294620,67448968,84687372,97210807,97210796,139496682,232894534], [1071579,1071579,1071579,1071579,1071579,1071579,1071579,2611878,2611878,2611448,2611447,5620327,5952661,4701227,4070278,4070278,2779546,1588019], ![123625076537880,1607777895236,209605080600,4843630820], 175455828269489928⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons7

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons8
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuadraticSingletons8.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree5_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree29_0, Research6970.Height2308.MainFree.bankfree35_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree98_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree129_0, Research6970.Height2308.MainFree.bankfree151_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree186_0, Research6970.Height2308.MainFree.bankfree175_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1179
    historyValues := [![15271, 162872, 759006, 3547980],
    ![25417/2, 493913/4, 560700, 2414916],
    ![54680/9, 538210/9, 560700, 2414916],
    ![29433/8, 580127/16, 2626570/9, 3812326/3],
    ![63052/25, 622384/25, 206024, 3924361/4],
    ![5710/3, 165545/9, 1500251/8, 12846421/16],
    ![18775/16, 753065/64, 132886, 15031989/25],
    ![89110/121, 874825/121, 566490/7, 351252],
    ![89110/121, 874825/121, 673387/9, 351252],
    ![127905/242, 2980286/441, 549021/8, 351252],
    ![127905/242, 2980286/441, 549021/8, 20297221/72],
    ![127905/242, 714572/121, 505197/8, 793881/4],
    ![813/2, 714572/121, 505197/8, 793881/4],
    ![813/2, 2129177/400, 2389886/49, 2752361/14],
    ![813/2, 6353641/1369, 57144059/1352, 235525997/1352],
    ![967337/2738, 6353641/1369, 57144059/1352, 235525997/1352],
    ![466774/1369, 6353641/1369, 57144059/1352, 235525997/1352],
    ![459746/1369, 6353641/1369, 57144059/1352, 235525997/1352]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 27 306263 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6209, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1179⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free5_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free29_0
    · exact Research6970.Height2308.MainFree.free35_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free74_1
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free98_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free129_0
    · exact Research6970.Height2308.MainFree.free151_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free186_0
    · exact Research6970.Height2308.MainFree.free175_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨193062524164125687060518511/357383694111013068385288192, 17400753/18595696, [321897603,321897577,321897579,321897577,321897582,321897596,321897596,147258439,147258439,147258439,147258439,70288966,70288961,98138678,96967884,110003513,188620289,231544235], [1077746,1077747,1077747,1077747,1077747,1077746,1077746,2611117,2611117,2611117,2611117,5700213,5700213,4031137,4080525,3576058,2006700,1599115], ![122908310822700,1609233492040,224458143910,4855824750], 175246945709977463⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons8

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons9
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuadraticSingletons9.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree29_0, Research6970.Height2308.MainFree.bankfree35_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree95_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree126_0, Research6970.Height2308.MainFree.bankfree161_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree181_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree170_0] i
    head := Research6970.Height2308.MainHeads.src1178
    historyValues := [![15513, 162395, 754153, 3459618],
    ![25417/2, 122692, 557130, 2414916],
    ![54680/9, 178270/3, 557130, 2414916],
    ![29433/8, 72059/2, 2610080/9, 3760136/3],
    ![63052/25, 618474/25, 206024, 3924361/4],
    ![5710/3, 109655/6, 745323/4, 3167639/4],
    ![18775/16, 374195/32, 132886, 14826204/25],
    ![89110/121, 869300/121, 562920/7, 2425104/7],
    ![89110/121, 869300/121, 673387/9, 2425104/7],
    ![127905/242, 2965496/441, 3360334/49, 2425104/7],
    ![127905/242, 2965496/441, 3360334/49, 9740641/36],
    ![127905/242, 709132/121, 505197/8, 793881/4],
    ![1358449/3362, 709132/121, 505197/8, 793881/4],
    ![1358449/3362, 8630688/1681, 2421530/49, 9614680/49],
    ![1358449/3362, 699872/147, 5303280/121, 21366636/121],
    ![953281/2738, 699872/147, 5303280/121, 21366636/121],
    ![953281/2738, 6310801/1369, 7095333/169, 29365561/169],
    ![462287/1369, 6310801/1369, 7095333/169, 29365561/169]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 2 28 306100 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6124, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1178⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free29_0
    · exact Research6970.Height2308.MainFree.free35_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free74_1
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free95_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free126_0
    · exact Research6970.Height2308.MainFree.free161_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free181_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨135928372105763245378445273/250900034372917491447889920, 6906413/7390719, [320969412,320969401,320969397,320969401,320969401,320969406,320969404,137255130,137255130,137255149,137255149,71075552,72107371,83799073,96594129,96020727,138593749,232172836], [1082492,1082493,1082493,1082493,1082493,1082492,1082492,2828666,2828666,2828666,2828666,5637729,5555765,4753947,4096292,4120480,2799333,1593950], ![123241984805520,1608556132424,208955552400,4903371200], 173691312514922538⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuadraticSingletons9
end Pack_R6970Height2313MainPlans03

section Pack_R6970Height2313MainPlans04

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons12
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons12.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree5_0, Research6970.Height2308.MainFree.bankfree12_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree30_0, Research6970.Height2308.MainFree.bankfree40_0, Research6970.Height2308.MainFree.bankfree49_0, Research6970.Height2308.MainFree.bankfree58_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree98_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree126_0, Research6970.Height2308.MainFree.bankfree153_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree184_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree175_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1401
    historyValues := [![15236, 165482, 770547, 3661901],
    ![25247/2, 130267, 588088, 5392653/2],
    ![54680/9, 188270/3, 588088, 5392653/2],
    ![29433/8, 304361/8, 2755580/9, 4220636/3],
    ![63824/25, 656108/25, 409431/2, 3837681/4],
    ![72196/49, 742912/49, 3348382/25, 15308398/25],
    ![20312/25, 221539/25, 760463/8, 7991929/16],
    ![95350/121, 917740/121, 4134058/49, 2521776/7],
    ![95350/121, 917740/121, 673387/9, 12967201/36],
    ![127905/242, 3095996/441, 549021/8, 12967201/36],
    ![127905/242, 3095996/441, 549021/8, 10686361/36],
    ![127905/242, 757132/121, 505197/8, 5444208/25],
    ![1358449/3362, 757132/121, 505197/8, 5444208/25],
    ![1358449/3362, 9163120/1681, 4946427/98, 175946904/841],
    ![1358449/3362, 2227616/441, 30038096/675, 127911392/675],
    ![481425/1369, 2227616/441, 30038096/675, 127911392/675],
    ![481425/1369, 6688801/1369, 27788632/625, 117462244/625],
    ![466774/1369, 6688801/1369, 27788632/625, 117462244/625],
    ![459746/1369, 6688801/1369, 27788632/625, 117462244/625]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 16 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6874, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1401⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free5_0
    · exact Research6970.Height2308.MainFree.free12_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free30_0
    · exact Research6970.Height2308.MainFree.free40_0
    · exact Research6970.Height2308.MainFree.free49_0
    · exact Research6970.Height2308.MainFree.free58_0
    · exact Research6970.Height2308.MainFree.free74_1
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free98_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free126_0
    · exact Research6970.Height2308.MainFree.free153_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free184_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free175_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨3236248415646315752123580075/5893354038559351241399861248, 70567375/75513802, [335345418,335345406,335345403,335345409,335345408,335345412,335345409,157797712,157797712,157797712,157797712,72894855,72894855,87837251,100803762,100803762,113461597,192264604,234324173], [1026896,1026896,1026896,1026896,1026896,1026896,1026896,2435978,2435978,2435978,2435978,5493210,5493210,4522066,3918714,3918714,3456075,1962777,1576271], ![124383957511860,1606236756352,228794878760,4663269660], 183608525148863876⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons12

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons13
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons13.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree5_0, Research6970.Height2308.MainFree.bankfree9_0, Research6970.Height2308.MainFree.bankfree17_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree34_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree85_0, Research6970.Height2308.MainFree.bankfree105_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree168_0, Research6970.Height2308.MainFree.bankfree126_0, Research6970.Height2308.MainFree.bankfree153_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree180_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree170_0] i
    head := Research6970.Height2308.MainHeads.src1402
    historyValues := [![15038, 165369, 768919, 3755420],
    ![12303, 130103, 1176611/2, 2755522],
    ![53398/9, 564233/9, 1176611/2, 2755522],
    ![29433/8, 604981/16, 2738702/9, 4167218/3],
    ![33449/18, 696193/36, 196528, 14517393/16],
    ![18775/16, 784855/64, 132886, 651249],
    ![89110/121, 82945/11, 590766/7, 2687652/7],
    ![89110/121, 82945/11, 590766/7, 2687652/7],
    ![127905/242, 3080858/441, 549021/8, 2687652/7],
    ![127905/242, 3080858/441, 549021/8, 341056],
    ![127905/242, 3080858/441, 11593480/169, 45119976/169],
    ![127905/242, 68324/11, 505197/8, 5375304/25],
    ![127905/242, 68324/11, 1276924/21, 203401],
    ![1358449/3362, 68324/11, 1276924/21, 203401],
    ![1358449/3362, 9102220/1681, 4946427/98, 203401],
    ![1358449/3362, 2212768/441, 29839736/675, 126292496/675],
    ![476343/1369, 2212768/441, 29839736/675, 126292496/675],
    ![476343/1369, 6644953/1369, 59737545/1352, 126292496/675],
    ![462287/1369, 6644953/1369, 59737545/1352, 126292496/675]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 17 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6787, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1402⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free5_0
    · exact Research6970.Height2308.MainFree.free9_0
    · exact Research6970.Height2308.MainFree.free17_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free34_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free85_0
    · exact Research6970.Height2308.MainFree.free105_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free168_0
    · exact Research6970.Height2308.MainFree.free126_0
    · exact Research6970.Height2308.MainFree.free153_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free180_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨8560819799244091908532752685/15649273686222371734419406848, 23469277/25118086, [332331274,332331260,332331260,332331262,332331263,332331265,147083265,147083265,147301323,147092033,147301314,110777082,70653416,69311542,87495474,100261939,100261939,142197549,234954731], [1035153,1035153,1035153,1035153,1035153,1035153,2614028,2614028,2610405,2613883,2610405,3549218,5671262,5783957,4539292,3941570,3941570,2720361,1571089], ![124718670309420,1605556799584,211459257900,4690468300], 181540424998796173⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons13

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons14
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons14.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree5_0, Research6970.Height2308.MainFree.bankfree9_0, Research6970.Height2308.MainFree.bankfree17_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree30_0, Research6970.Height2308.MainFree.bankfree40_0, Research6970.Height2308.MainFree.bankfree49_0, Research6970.Height2308.MainFree.bankfree58_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree98_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree126_0, Research6970.Height2308.MainFree.bankfree161_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree186_0, Research6970.Height2308.MainFree.bankfree176_0, Research6970.Height2308.MainFree.bankfree170_0] i
    head := Research6970.Height2308.MainHeads.src1403
    historyValues := [![15071, 165336, 769362, 3688699],
    ![12303, 129320, 584782, 2720200],
    ![53398/9, 560840/9, 584782, 2720200],
    ![29433/8, 75155/2, 2721824/9, 4113800/3],
    ![63824/25, 129586/5, 409431/2, 3837681/4],
    ![72196/49, 733690/49, 3307144/25, 596836],
    ![20312/25, 87589/10, 760463/8, 7991929/16],
    ![95350/121, 905560/121, 4079596/49, 17205600/49],
    ![95350/121, 905560/121, 673387/9, 17205600/49],
    ![127905/242, 437960/63, 549021/8, 17205600/49],
    ![127905/242, 437960/63, 549021/8, 10686361/36],
    ![127905/242, 745996/121, 505197/8, 212256],
    ![1358449/3362, 745996/121, 505197/8, 212256],
    ![1358449/3362, 9040800/1681, 2480600/49, 9859600/49],
    ![1358449/3362, 732640/147, 29641376/675, 4986944/27],
    ![967337/2738, 732640/147, 29641376/675, 4986944/27],
    ![938035/2738, 732640/147, 29641376/675, 4986944/27],
    ![462287/1369, 732640/147, 29641376/675, 4986944/27]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 18 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6700, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1403⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free5_0
    · exact Research6970.Height2308.MainFree.free9_0
    · exact Research6970.Height2308.MainFree.free17_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free30_0
    · exact Research6970.Height2308.MainFree.free40_0
    · exact Research6970.Height2308.MainFree.free49_0
    · exact Research6970.Height2308.MainFree.free58_0
    · exact Research6970.Height2308.MainFree.free74_1
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free98_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free126_0
    · exact Research6970.Height2308.MainFree.free161_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free186_0
    · exact Research6970.Height2308.MainFree.free176_0
    · exact Research6970.Height2308.MainFree.free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨801232180145655845692652481/1468810403963657128826109952, 8804559/9424709, [331299512,331299498,331299497,331299502,331299502,331299503,331299503,150135724,150135724,150135724,150135724,74253337,74253337,87306340,100202807,106462184,141359034,235137604], [1037979,1037979,1037979,1037979,1037979,1037979,1037979,2563303,2563303,2563303,2563303,5385297,5385297,4548825,3944065,3698930,2738736,1569587], ![124815742955280,1605360062876,211623843600,4693437350], 181067378337810176⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons14

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons15
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons15.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree5_0, Research6970.Height2308.MainFree.bankfree12_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree34_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree64_0, Research6970.Height2308.MainFree.bankfree86_0, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree95_0, Research6970.Height2308.MainFree.bankfree116_1, Research6970.Height2308.MainFree.bankfree140_0, Research6970.Height2308.MainFree.bankfree126_0, Research6970.Height2308.MainFree.bankfree161_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree180_0, Research6970.Height2308.MainFree.bankfree170_0] i
    head := Research6970.Height2308.MainHeads.src1404
    historyValues := [![15201, 164288, 763504, 3629908],
    ![25247/2, 127862, 577298, 5188683/2],
    ![54680/9, 554410/9, 577298, 5188683/2],
    ![29433/8, 298771/8, 2705140/9, 4060996/3],
    ![33449/18, 171929/9, 776597/4, 7073673/8],
    ![18775/16, 193835/16, 132886, 16012494/25],
    ![89110/121, 901150/121, 583500/7, 2619144/7],
    ![89110/121, 901150/121, 583500/7, 2619144/7],
    ![243156/361, 2510092/361, 11343680/169, 313600],
    ![127905/242, 3050756/441, 11343680/169, 313600],
    ![127905/242, 3050756/441, 11343680/169, 10321147/36],
    ![127905/242, 11999/2, 964947/16, 16177844/75],
    ![127905/242, 11999/2, 964947/16, 16177844/75],
    ![1358449/3362, 11999/2, 964947/16, 16177844/75],
    ![1358449/3362, 8979568/1681, 2480600/49, 9859600/49],
    ![1358449/3362, 6549728/1323, 5303280/121, 123073312/675],
    ![1358449/3362, 6557761/1369, 29480647/676, 123073312/675],
    ![476343/1369, 6557761/1369, 29480647/676, 123073312/675],
    ![462287/1369, 6557761/1369, 29480647/676, 123073312/675]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 19 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6614, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1404⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free5_0
    · exact Research6970.Height2308.MainFree.free12_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free34_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free64_0
    · exact Research6970.Height2308.MainFree.free86_0
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free95_0
    · exact Research6970.Height2308.MainFree.free116_1
    · exact Research6970.Height2308.MainFree.free140_0
    · exact Research6970.Height2308.MainFree.free126_0
    · exact Research6970.Height2308.MainFree.free161_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free180_0
    · exact Research6970.Height2308.MainFree.free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨1053292666270168661975995519/1928704364844366472283160576, 17465597/18705897, [329236470,329236459,329236455,329236455,329236461,329236462,146815805,146815805,146815805,146815826,146815826,54346243,70838847,70838856,86966275,96474719,96793323,141245920,234228837], [1043630,1043630,1043630,1043630,1043630,1043630,2619158,2619158,2619158,2619158,2619158,7433698,5656532,5656532,4565976,4101329,4087889,2741214,1577055], ![124333351256340,1606339835808,210805953300,4880581510], 179247631019359913⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 20 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons15

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons16
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons16.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree5_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree30_0, Research6970.Height2308.MainFree.bankfree40_0, Research6970.Height2308.MainFree.bankfree49_0, Research6970.Height2308.MainFree.bankfree58_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree98_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree126_0, Research6970.Height2308.MainFree.bankfree153_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree180_0, Research6970.Height2308.MainFree.bankfree170_0] i
    head := Research6970.Height2308.MainHeads.src1405
    historyValues := [![15269, 164201, 765085, 3594784],
    ![25417/2, 505753/4, 574140, 5073033/2],
    ![54680/9, 183670/3, 574140, 5073033/2],
    ![29433/8, 593887/16, 2688650/9, 4008806/3],
    ![63824/25, 639893/25, 409431/2, 3837681/4],
    ![72196/49, 724627/49, 3266617/25, 14540083/25],
    ![20312/25, 865801/100, 760463/8, 7991929/16],
    ![95350/121, 893590/121, 4026073/49, 16766472/49],
    ![95350/121, 893590/121, 673387/9, 16766472/49],
    ![127905/242, 3035966/441, 549021/8, 16766472/49],
    ![127905/242, 3035966/441, 549021/8, 21343301/72],
    ![127905/242, 735052/121, 505197/8, 5170968/25],
    ![1358449/3362, 735052/121, 505197/8, 5170968/25],
    ![1358449/3362, 8921620/1681, 4946427/98, 5170968/25],
    ![1358449/3362, 722912/147, 5303280/121, 121491632/675],
    ![1358449/3362, 6514921/1369, 58579899/1352, 121491632/675],
    ![476343/1369, 6514921/1369, 58579899/1352, 121491632/675],
    ![462287/1369, 6514921/1369, 58579899/1352, 121491632/675]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 20 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6529, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1405⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free5_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free30_0
    · exact Research6970.Height2308.MainFree.free40_0
    · exact Research6970.Height2308.MainFree.free49_0
    · exact Research6970.Height2308.MainFree.free58_0
    · exact Research6970.Height2308.MainFree.free74_1
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free98_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free126_0
    · exact Research6970.Height2308.MainFree.free153_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free180_0
    · exact Research6970.Height2308.MainFree.free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨1405224112921381448557617733/2582266949513366493013737472, 23344033/24992842, [328604753,328604742,328604742,328604738,328604746,328604744,328604743,149848501,149848501,149969379,149969369,71591373,68122313,86481931,96077909,96325759,140778356,233872183], [1045360,1045360,1045360,1045360,1045360,1045360,1045360,2568076,2568076,2566068,2566068,5596754,5891672,4594722,4118068,4107612,2751460,1579985], ![124144032180060,1606723886672,210484964700,4900500920], 178880789426928843⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons16

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons17
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons17.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree5_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree29_0, Research6970.Height2308.MainFree.bankfree35_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree95_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree126_0, Research6970.Height2308.MainFree.bankfree149_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree180_0, Research6970.Height2308.MainFree.bankfree170_0] i
    head := Research6970.Height2308.MainHeads.src1406
    historyValues := [![15221, 163659, 761467, 3616667],
    ![25417/2, 502645/4, 570612, 5007765/2],
    ![54680/9, 60850, 570612, 5007765/2],
    ![29433/8, 590275/16, 2672354/9, 3957230/3],
    ![63052/25, 126648/5, 206024, 3924361/4],
    ![5710/3, 56165/3, 1526919/8, 13334705/16],
    ![18775/16, 766045/64, 132886, 3120669/5],
    ![89110/121, 890165/121, 576402/7, 2552220/7],
    ![89110/121, 890165/121, 576402/7, 2552220/7],
    ![127905/242, 3021350/441, 549021/8, 2552220/7],
    ![127905/242, 3021350/441, 549021/8, 20114845/72],
    ![127905/242, 729676/121, 505197/8, 1020888/5],
    ![1358449/3362, 729676/121, 505197/8, 1020888/5],
    ![1358449/3362, 108443/20, 4866583/98, 1020888/5],
    ![1358449/3362, 2154400/441, 5303280/121, 21641104/121],
    ![1358449/3362, 6472585/1369, 58202991/1352, 21641104/121],
    ![476343/1369, 6472585/1369, 58202991/1352, 21641104/121],
    ![462287/1369, 6472585/1369, 58202991/1352, 21641104/121]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 21 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6445, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1406⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free5_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free29_0
    · exact Research6970.Height2308.MainFree.free35_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free95_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free126_0
    · exact Research6970.Height2308.MainFree.free149_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free180_0
    · exact Research6970.Height2308.MainFree.free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨510847140032092367685344735/939637566691164566927179776, 69757379/74623962, [326071453,326071439,326071440,326071440,326071447,326071445,326071443,146034644,146034644,146034644,146034644,71484395,67879562,85861989,95685823,95863696,140316293,233519726], [1056405,1056405,1056405,1056405,1056405,1056405,1056405,2636276,2636276,2636276,2636276,5605252,5913660,4631515,4134607,4127104,2761586,1582882], ![123956940955320,1607104203424,210167753400,4920182330], 177283910810516652⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons17

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons18
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons18.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree5_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree29_0, Research6970.Height2308.MainFree.bankfree35_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree95_0, Research6970.Height2308.MainFree.bankfree92_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree126_0, Research6970.Height2308.MainFree.bankfree149_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree180_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree170_0] i
    head := Research6970.Height2308.MainHeads.src1407
    historyValues := [![15369, 163303, 760842, 3516707],
    ![25417/2, 499611/4, 567168, 4944051/2],
    ![54680/9, 544370/9, 567168, 4944051/2],
    ![29433/8, 586749/16, 885482/3, 1302294],
    ![63052/25, 629468/25, 206024, 3924361/4],
    ![5710/3, 167470/9, 1517653/8, 13165047/16],
    ![18775/16, 761535/64, 132886, 15404823/25],
    ![89110/121, 884835/121, 572958/7, 359964],
    ![89110/121, 884835/121, 572958/7, 359964],
    ![89110/121, 884835/121, 452545/6, 2206547/8],
    ![65315/96, 884835/121, 73953, 2206547/8],
    ![65315/96, 724428/121, 505197/8, 5039496/25],
    ![1358449/3362, 724428/121, 505197/8, 5039496/25],
    ![1358449/3362, 53873/10, 4835669/98, 5039496/25],
    ![1358449/3362, 6421216/1323, 5303280/121, 21641104/121],
    ![476343/1369, 6421216/1323, 5303280/121, 21641104/121],
    ![476343/1369, 6431257/1369, 57835057/1352, 241367679/1352],
    ![462287/1369, 6431257/1369, 57835057/1352, 241367679/1352]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 22 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6363, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1407⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free5_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free29_0
    · exact Research6970.Height2308.MainFree.free35_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free95_0
    · exact Research6970.Height2308.MainFree.free92_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free126_0
    · exact Research6970.Height2308.MainFree.free149_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free180_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨6239994360600748112825903689/11491672626678442415416672256, 69727043/74562712, [325444493,325444482,325444481,325444482,325444482,325444484,325444487,162722240,162722237,103936859,78611255,75407853,67642591,85215555,97320072,97320058,139865232,233175661], [1059611,1059611,1059611,1059611,1059611,1059611,1059611,2354144,2354144,3786549,5079190,5300313,5935124,4669880,4065669,4065669,2771470,1585709], ![123774304372020,1607474922104,209858094900,4838146110], 176844592166994453⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons18

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons19
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons19.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree5_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree29_0, Research6970.Height2308.MainFree.bankfree35_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree95_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree126_0, Research6970.Height2308.MainFree.bankfree149_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree180_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree170_0] i
    head := Research6970.Height2308.MainHeads.src1408
    historyValues := [![15221, 163167, 758679, 3590099],
    ![25417/2, 496577/4, 563724, 4880337/2],
    ![54680/9, 541090/9, 563724, 4880337/2],
    ![29433/8, 583223/16, 2640538/9, 3856534/3],
    ![63052/25, 625696/25, 206024, 3924361/4],
    ![5710/3, 166445/9, 1508387/8, 12995389/16],
    ![18775/16, 757025/64, 132886, 15206301/25],
    ![89110/121, 79955/11, 569514/7, 2487276/7],
    ![89110/121, 79955/11, 569514/7, 2487276/7],
    ![127905/242, 2992814/441, 549021/8, 2487276/7],
    ![127905/242, 2992814/441, 549021/8, 19603001/72],
    ![127905/242, 65380/11, 505197/8, 4974552/25],
    ![1358449/3362, 65380/11, 505197/8, 4974552/25],
    ![1358449/3362, 107049/20, 4804755/98, 4974552/25],
    ![1358449/3362, 6379232/1323, 5303280/121, 21641104/121],
    ![476343/1369, 6379232/1323, 5303280/121, 21641104/121],
    ![476343/1369, 6389929/1369, 57467123/1352, 238257173/1352],
    ![462287/1369, 6389929/1369, 57467123/1352, 238257173/1352]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 23 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6281, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1408⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free5_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free29_0
    · exact Research6970.Height2308.MainFree.free35_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free95_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free126_0
    · exact Research6970.Height2308.MainFree.free149_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free180_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨386882089900293006252056863/714151640857687617895202816, 69545983/74350738, [322805065,322805043,322805040,322805040,322805043,322805059,322805054,147166730,147166730,147389004,147388997,71275475,67405620,84569121,97186345,97186337,139414170,232831595], [1073106,1073107,1073107,1073107,1073107,1073106,1073107,2612641,2612641,2608948,2608948,5621848,5956587,4708245,4071310,4071310,2781354,1588537], ![123591667257900,1607846168320,209548435500,4844858900], 175272559172184006⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons19

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons2
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons2.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree4_0, Research6970.Height2308.MainFree.bankfree9_0, Research6970.Height2308.MainFree.bankfree17_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree32_0, Research6970.Height2308.MainFree.bankfree41_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree48_0, Research6970.Height2308.MainFree.bankfree61_0, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree85_0, Research6970.Height2308.MainFree.bankfree74_2, Research6970.Height2308.MainFree.bankfree113_0, Research6970.Height2308.MainFree.bankfree144_0, Research6970.Height2308.MainFree.bankfree150_0, Research6970.Height2308.MainFree.bankfree120_0, Research6970.Height2308.MainFree.bankfree198_0, Research6970.Height2308.MainFree.bankfree210_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1391
    historyValues := [![14668, 170404, 795917, 4170071],
    ![12303, 139166, 629089, 3164364],
    ![53398/9, 603506/9, 620224, 3104644],
    ![29433/8, 324141/8, 978020/3, 1595172],
    ![16211/9, 187247/9, 1706741/8, 8772147/8],
    ![73046/81, 923932/81, 1051502/9, 1301165/2],
    ![73648/121, 1192506/121, 5390256/49, 1301165/2],
    ![73648/121, 1192506/121, 5390256/49, 1080335/2],
    ![73648/121, 985514/121, 4425328/49, 1615441/4],
    ![127905/242, 3256076/441, 549021/8, 1615441/4],
    ![127905/242, 3256076/441, 549021/8, 45516960/121],
    ![5584/11, 3256076/441, 549021/8, 45516960/121],
    ![5584/11, 143691/22, 4564936/75, 6479412/25],
    ![5584/11, 143691/22, 8828320/147, 27660906/121],
    ![5584/11, 9754600/1681, 43829720/841, 27660906/121],
    ![668847/1681, 9754600/1681, 43829720/841, 27660906/121],
    ![668847/1681, 339544/63, 10692152/225, 10738729/49],
    ![668847/1681, 14273469/2738, 128596230/2809, 3426201/16],
    ![479479/1369, 14273469/2738, 128596230/2809, 3426201/16],
    ![930251/2738, 14273469/2738, 128596230/2809, 3426201/16],
    ![459746/1369, 14273469/2738, 128596230/2809, 3426201/16]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 6 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 7794, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1391⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free4_0
    · exact Research6970.Height2308.MainFree.free9_0
    · exact Research6970.Height2308.MainFree.free17_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free32_0
    · exact Research6970.Height2308.MainFree.free41_0
    · exact Research6970.Height2308.MainFree.free42_2
    · exact Research6970.Height2308.MainFree.free48_0
    · exact Research6970.Height2308.MainFree.free61_0
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free85_0
    · exact Research6970.Height2308.MainFree.free74_2
    · exact Research6970.Height2308.MainFree.free113_0
    · exact Research6970.Height2308.MainFree.free144_0
    · exact Research6970.Height2308.MainFree.free150_0
    · exact Research6970.Height2308.MainFree.free120_0
    · exact Research6970.Height2308.MainFree.free198_0
    · exact Research6970.Height2308.MainFree.free210_0
    · exact Research6970.Height2308.MainFree.free183_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨1307203698597239/2383339902205952, 8519146537490736679053083/9411320844048445871226880, [352211490,352211478,352211475,352211480,352211480,352211480,352211484,352211484,166983613,166983885,167617911,167617903,117403824,74761605,67664862,92725192,106547183,106547183,123667096,194792705,236585127], [980697,980697,980697,980697,980697,980697,980697,980697,2283329,2283325,2272789,2272789,3334365,5344922,5933106,4275709,3695980,3695980,3159371,1932308,1557692], ![125584117114140,1603799624508,231803318950,4398216200], 195628252467906838⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons2

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons20
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons20.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree29_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree98_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree129_0, Research6970.Height2308.MainFree.bankfree151_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree186_0, Research6970.Height2308.MainFree.bankfree175_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1409
    historyValues := [![15517, 162640, 755351, 3469609],
    ![25417/2, 123395, 560322, 2414916],
    ![54680/9, 537850/9, 560322, 2414916],
    ![29433/8, 144935/4, 2624824/9, 3806800/3],
    ![63052/25, 124394/5, 206024, 3924361/4],
    ![17323/9, 18445, 186682, 792825],
    ![18775/16, 376285/32, 132886, 600408],
    ![89110/121, 874240/121, 566112/7, 2455200/7],
    ![89110/121, 874240/121, 673387/9, 2455200/7],
    ![127905/242, 2978720/441, 549021/8, 2455200/7],
    ![127905/242, 2978720/441, 549021/8, 2533475/9],
    ![127905/242, 713996/121, 505197/8, 793881/4],
    ![813/2, 713996/121, 505197/8, 793881/4],
    ![813/2, 106381/20, 2388158/49, 9628609/49],
    ![813/2, 6349105/1369, 14275919/338, 29398075/169],
    ![967337/2738, 6349105/1369, 14275919/338, 29398075/169],
    ![466774/1369, 6349105/1369, 14275919/338, 29398075/169],
    ![459746/1369, 6349105/1369, 14275919/338, 29398075/169]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 24 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6200, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1409⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free29_0
    · exact Research6970.Height2308.MainFree.free37_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free74_1
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free98_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free129_0
    · exact Research6970.Height2308.MainFree.free151_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free186_0
    · exact Research6970.Height2308.MainFree.free175_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨1537762868383081521606443549/2831600175775383373424623616, 34624139/37012297, [322524350,322524340,322524338,322524338,322524341,322524340,322524339,146915014,146915014,146923529,146923521,70258476,70258459,98054702,96937676,109954007,188570782,231506471], [1074542,1074542,1074542,1074542,1074542,1074542,1074542,2616984,2616984,2616798,2616798,5702635,5702636,4034679,4081800,3577776,2007297,1599426], ![122888264936220,1609274560084,224399230580,4857342000], 175157854329372076⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons20

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons21
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons21.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree29_0, Research6970.Height2308.MainFree.bankfree35_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree95_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree126_0, Research6970.Height2308.MainFree.bankfree161_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree180_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree170_0] i
    head := Research6970.Height2308.MainHeads.src1410
    historyValues := [![15513, 162383, 754085, 3458970],
    ![25417/2, 122655, 556962, 2414916],
    ![54680/9, 534650/9, 556962, 2414916],
    ![29433/8, 144075/4, 869768/3, 1252560],
    ![63052/25, 123658/5, 206024, 3924361/4],
    ![5710/3, 328865/18, 745097/4, 1582785/2],
    ![18775/16, 374085/32, 132886, 2963304/5],
    ![89110/121, 869040/121, 562752/7, 2423520/7],
    ![89110/121, 869040/121, 673387/9, 2423520/7],
    ![127905/242, 2964800/441, 3359548/49, 2423520/7],
    ![127905/242, 2964800/441, 3359548/49, 9740641/36],
    ![127905/242, 708876/121, 505197/8, 793881/4],
    ![1358449/3362, 708876/121, 505197/8, 793881/4],
    ![1358449/3362, 8627840/1681, 345820/7, 9608400/49],
    ![1358449/3362, 6296800/1323, 5303280/121, 21352680/121],
    ![476343/1369, 6296800/1323, 5303280/121, 21352680/121],
    ![476343/1369, 6308785/1369, 14186179/338, 29365561/169],
    ![462287/1369, 6308785/1369, 14186179/338, 29365561/169]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 25 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6120, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1410⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free29_0
    · exact Research6970.Height2308.MainFree.free35_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free74_1
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free95_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free126_0
    · exact Research6970.Height2308.MainFree.free161_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free180_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨873589182842114865297942669/1612637939155871095017439232, 4932789/5278609, [320888576,320888562,320888562,320888566,320888567,320888565,320888565,147357911,147357911,147357911,147357911,71070417,74573936,83766815,96923784,96794715,138528550,232156052], [1082906,1082906,1082906,1082906,1082906,1082906,1082906,2609464,2609464,2609464,2609464,5638137,5359830,4755861,4082386,4087830,2800761,1594088], ![123233075522640,1608574266928,208940446800,4864517700], 173639312706496468⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons21

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons22
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons22.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree29_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree95_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree126_0, Research6970.Height2308.MainFree.bankfree161_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree181_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree170_0] i
    head := Research6970.Height2308.MainHeads.src1411
    historyValues := [![15467, 162245, 751114, 3474468],
    ![25417/2, 243867/2, 553686, 2414916],
    ![54680/9, 531530/9, 553686, 2414916],
    ![29433/8, 286473/8, 864724/3, 1236596],
    ![63052/25, 614702/25, 206024, 3924361/4],
    ![17323/9, 109327/6, 1475523/8, 3090483/4],
    ![18775/16, 92985/8, 132886, 14627682/25],
    ![89110/121, 863970/121, 559476/7, 2392632/7],
    ![89110/121, 863970/121, 559476/7, 2392632/7],
    ![127905/242, 421604/63, 3344221/49, 2392632/7],
    ![127905/242, 421604/63, 3344221/49, 9740641/36],
    ![127905/242, 703884/121, 3088611/49, 793881/4],
    ![1358449/3362, 703884/121, 3088611/49, 793881/4],
    ![1358449/3362, 8572304/1681, 2405335/49, 9485940/49],
    ![1358449/3362, 6256864/1323, 5276463/121, 21080538/121],
    ![953281/2738, 6256864/1323, 5276463/121, 21080538/121],
    ![953281/2738, 6269473/1369, 28197365/676, 29365561/169],
    ![462287/1369, 6269473/1369, 28197365/676, 29365561/169]] }

theorem valid : plan.Valid := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact Research6970.Height2313.ZGen.Hist.history_step_of_fast plan (by decide +kernel)

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 26 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6042, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1411⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free29_0
    · exact Research6970.Height2308.MainFree.free37_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free95_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free126_0
    · exact Research6970.Height2308.MainFree.free161_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free181_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨144408508061262866614578473/266659304000992540599779328, 34399349/36804684, [318812484,318812476,318812470,318812473,318812476,318812475,318812477,146095382,146095382,146095382,146095382,72609482,73983717,83137707,96196665,95184785,138142688,231828771], [1093521,1093521,1093521,1093521,1093521,1093521,1093521,2634945,2634945,2634945,2634945,5515879,5406715,4793198,4113058,4155743,2809217,1596777], ![123059348222220,1608926851104,208645893900,4945334170], 172403003560186324⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have bounds : RatesAB price plan := by decide +kernel
    intro i
    refine ⟨(bounds i).1, (bounds i).2, ?_⟩
    fin_cases i
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 4 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons22
end Pack_R6970Height2313MainPlans04
