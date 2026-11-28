import ProximityPrize.SubmissionLower.R6970Height2313MainReuse
import ProximityPrize.SubmissionLower.R6970Height2313Helper
import ProximityPrize.SubmissionLower.R6970Height2313MainHeads
import ProximityPrize.SubmissionLower.Z6969Pack0711
import ProximityPrize.SubmissionLower.R6970Height2313MainFast
import ProximityPrize.SubmissionLower.R6970Height2308MainFree
import ProximityPrize.SubmissionLower.R6970Height2308MainHeads
import ProximityPrize.SubmissionLower.Z6969Pack0720

section Pack_R6970Height2313MainPlans05

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons23
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons23.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree31_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree98_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree129_0, Research6970.Height2308.MainFree.bankfree161_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1412
    historyValues := [![15531, 161906, 751210, 3427027],
    ![25417/2, 121212, 550410, 2414916],
    ![54680/9, 528410/9, 550410, 2414916],
    ![29433/8, 71199/2, 286560, 1220632],
    ![64334/25, 608578/25, 204686, 3728761/4],
    ![17323/9, 54332/3, 733335/4, 1525293/2],
    ![18775/16, 369795/32, 132886, 14438844/25],
    ![89110/121, 858900/121, 556200/7, 337392],
    ![89110/121, 858900/121, 673387/9, 337392],
    ![127905/242, 2937656/441, 3328894/49, 337392],
    ![127905/242, 2937656/441, 3328894/49, 1624693/6],
    ![127905/242, 698892/121, 3066498/49, 793881/4],
    ![813/2, 698892/121, 3066498/49, 793881/4],
    ![813/2, 8516768/1681, 2389930/49, 1337640/7],
    ![813/2, 6216928/1323, 5243118/121, 20808396/121],
    ![479479/1369, 6216928/1323, 5243118/121, 20808396/121],
    ![479479/1369, 6230161/1369, 7005593/169, 20808396/121],
    ![930251/2738, 6230161/1369, 7005593/169, 20808396/121],
    ![459746/1369, 6230161/1369, 7005593/169, 20808396/121]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 27 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5964, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1412⟩⟩
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
  ⟨504126242632408860556403957/933546150991012788072087552, 17209729/18404694, [317799996,317799987,317799984,317799984,317799989,317799985,317799986,146460226,146460226,146587288,146587278,72749997,72750215,82595918,93183471,93162524,115727553,186853162,230516234], [1098698,1098698,1098698,1098698,1098698,1098698,1098698,2626950,2626950,2624166,2624166,5504717,5504700,4825353,4252611,4253667,3381200,2027998,1607563], ![122362627331880,1610341904116,222355262780,5061863730], 172016750406055884⟩

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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons23

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons24
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons24.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree31_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree109_0, Research6970.Height2308.MainFree.bankfree140_0, Research6970.Height2308.MainFree.bankfree129_0, Research6970.Height2308.MainFree.bankfree161_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree186_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1413
    historyValues := [![15531, 161751, 749942, 3409787],
    ![25417/2, 120509, 547218, 2414916],
    ![54680/9, 525370/9, 547218, 2414916],
    ![29433/8, 141581/4, 2564296/9, 3615232/3],
    ![64334/25, 605006/25, 204686, 3728761/4],
    ![17323/9, 18003, 364511/2, 752928],
    ![18775/16, 367705/32, 132886, 14254848/25],
    ![89110/121, 853960/121, 553008/7, 2331648/7],
    ![89110/121, 853960/121, 673387/9, 2331648/7],
    ![127905/242, 417776/63, 3313960/49, 2331648/7],
    ![127905/242, 2526284/441, 2838670/49, 10760320/49],
    ![127905/242, 2526284/441, 2838670/49, 5924800/27],
    ![813/2, 2526284/441, 2838670/49, 5924800/27],
    ![813/2, 8462656/1681, 2374920/49, 9244160/49],
    ![813/2, 6191857/1369, 13925933/338, 446699008/2601],
    ![967337/2738, 6191857/1369, 13925933/338, 446699008/2601],
    ![930251/2738, 6191857/1369, 13925933/338, 446699008/2601],
    ![459746/1369, 6191857/1369, 13925933/338, 446699008/2601]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 28 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5888, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1413⟩⟩
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
    · exact Research6970.Height2308.MainFree.free109_0
    · exact Research6970.Height2308.MainFree.free140_0
    · exact Research6970.Height2308.MainFree.free129_0
    · exact Research6970.Height2308.MainFree.free161_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free186_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨376248395889605895355183163/697797954719507149871906816, 4296542/4593407, [316310770,316310759,316310758,316310758,316310759,316310760,316310760,146522197,146522197,146522197,105436923,76492433,79260932,95645468,94633016,115722093,186435105,230197345], [1106313,1106313,1106313,1106313,1106313,1106313,1106313,2625592,2625592,2625592,3734502,5225447,5034345,4136309,4179553,3381352,2033037,1610184], ![122193354672900,1610685951860,221857774950,4973668070], 171352730009461398⟩

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
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons24

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons25
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons25.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree31_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree98_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree129_0, Research6970.Height2308.MainFree.bankfree161_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree181_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1414
    historyValues := [![15531, 161453, 748643, 3402565],
    ![25417/2, 479261/4, 544068, 2414916],
    ![54680/9, 522370/9, 544068, 2414916],
    ![29433/8, 563099/16, 2549746/9, 3569182/3],
    ![64334/25, 601481/25, 204686, 3728761/4],
    ![17323/9, 71587/4, 2899063/16, 5946699/8],
    ![18775/16, 731285/64, 3304823/25, 14073273/25],
    ![89110/121, 849085/121, 549858/7, 2301948/7],
    ![89110/121, 849085/121, 673387/9, 2301948/7],
    ![127905/242, 2911382/441, 942635/14, 2301948/7],
    ![127905/242, 2911382/441, 942635/14, 19002697/72],
    ![127905/242, 689228/121, 6047379/98, 793881/4],
    ![813/2, 689228/121, 6047379/98, 793881/4],
    ![813/2, 8409256/1681, 4720215/98, 9126410/49],
    ![813/2, 877088/189, 10357131/242, 20281557/121],
    ![953281/2738, 877088/189, 10357131/242, 20281557/121],
    ![953281/2738, 6154057/1369, 6947158/169, 20281557/121],
    ![930251/2738, 6154057/1369, 6947158/169, 20281557/121],
    ![459746/1369, 6154057/1369, 6947158/169, 20281557/121]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 29 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5813, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1414⟩⟩
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
    · exact Research6970.Height2308.MainFree.free181_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨4789931751627107192683864653/8900898504862451792839966720, 13729399/14673442, [314745719,314745707,314745705,314745709,314745709,314745711,314745710,146501753,146501753,146524829,146524818,71624204,71624226,82061246,95007621,95007611,114802282,186207436,230022481], [1114315,1114315,1114315,1114315,1114315,1114315,1114315,2626040,2626040,2625535,2625535,5594146,5594145,4857085,4163216,4163216,3409558,2035781,1611621], ![122100533364420,1610874486824,221586848840,4954227040], 170221573717731045⟩

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
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons25

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons26
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons26.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree31_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree115_0, Research6970.Height2308.MainFree.bankfree168_0, Research6970.Height2308.MainFree.bankfree94_0, Research6970.Height2308.MainFree.bankfree152_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree170_0] i
    head := Research6970.Height2308.MainHeads.src1415
    historyValues := [![15531, 161773, 750161, 3393631],
    ![25417/2, 119140, 541002, 2414916],
    ![54680/9, 173150/3, 541002, 2414916],
    ![29433/8, 69995/2, 2535584/9, 3524360/3],
    ![64334/25, 23922, 204686, 3728761/4],
    ![17323/9, 53380/3, 720623/4, 1468005/2],
    ![18775/16, 363635/32, 3286792/25, 2779308/5],
    ![89110/121, 844340/121, 546792/7, 324720],
    ![89110/121, 844340/121, 673387/9, 324720],
    ![127905/242, 2898680/441, 3284878/49, 324720],
    ![127905/242, 841720/147, 2837424/49, 1453040/7],
    ![127905/242, 841720/147, 2837424/49, 3698200/21],
    ![66257/150, 841720/147, 2837424/49, 3698200/21],
    ![66257/150, 8354520/1681, 2345143/49, 3698200/21],
    ![66257/150, 2034080/441, 5147358/121, 20026860/121],
    ![479479/1369, 2034080/441, 5147358/121, 20026860/121],
    ![479479/1369, 6117265/1369, 6947158/169, 20026860/121],
    ![462287/1369, 6117265/1369, 6947158/169, 20026860/121]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 30 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5740, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1415⟩⟩
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
    · exact Research6970.Height2308.MainFree.free94_0
    · exact Research6970.Height2308.MainFree.free152_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free183_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨5996266329960322876595523819/11171288938575656973709082624, 34412844/36757987, [314062656,314062641,314062643,314062647,314062645,314062647,314062646,146704139,146704139,146704139,104687544,94406371,63306521,81981403,93766297,93422871,137366794,230919478], [1117808,1117808,1117808,1117808,1117808,1117808,1117808,2621605,2621605,2621605,3760503,4190976,6354617,4861824,4223236,4240545,2826220,1604249], ![122576677311960,1609907019932,207827530200,5046248550], 169880502208721329⟩

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
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons26

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons27
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons27.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree31_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree115_0, Research6970.Height2308.MainFree.bankfree168_0, Research6970.Height2308.MainFree.bankfree130_0, Research6970.Height2308.MainFree.bankfree161_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree186_0, Research6970.Height2308.MainFree.bankfree175_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1416
    historyValues := [![15531, 161554, 748920, 3381367],
    ![25417/2, 473859/4, 537936, 2414916],
    ![54680/9, 516530/9, 537936, 2414916],
    ![29433/8, 556821/16, 280158, 1159846],
    ![64334/25, 594619/25, 204686, 3728761/4],
    ![17323/9, 212279/12, 2865921/16, 5797341/8],
    ![18775/16, 723255/64, 3268761/25, 13719807/25],
    ![89110/121, 839595/121, 543726/7, 2244132/7],
    ![89110/121, 839595/121, 673387/9, 2244132/7],
    ![127905/242, 2885978/441, 6541067/98, 2244132/7],
    ![127905/242, 2508370/441, 2818736/49, 10041924/49],
    ![127905/242, 2508370/441, 2818736/49, 8519390/49],
    ![1374849/3362, 2508370/441, 2818736/49, 8519390/49],
    ![1374849/3362, 8305304/1681, 4662545/98, 8519390/49],
    ![1374849/3362, 6080473/1369, 6947158/169, 143310874/867],
    ![967337/2738, 6080473/1369, 6947158/169, 143310874/867],
    ![466774/1369, 6080473/1369, 6947158/169, 143310874/867],
    ![459746/1369, 6080473/1369, 6947158/169, 143310874/867]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 31 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5667, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1416⟩⟩
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
    · exact Research6970.Height2308.MainFree.free130_0
    · exact Research6970.Height2308.MainFree.free161_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free186_0
    · exact Research6970.Height2308.MainFree.free175_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨186444642423294708117596075/347948688296959517516234752, 68731811/73394356, [312586085,312586071,312586074,312586075,312586076,312586076,312586074,134365878,134365874,134365874,104195353,64794437,62083452,93658853,92600980,107783601,186400377,229845966], [1125358,1125358,1125358,1125358,1125358,1125358,1125358,2891980,2891980,2891980,3777580,6202187,6479916,4228651,4281969,3653081,2033456,1613071], ![122006835672120,1611064500564,221816448630,5095543110], 169405439260082286⟩

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
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 17 _
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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons27

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons28
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons28.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree32_0, Research6970.Height2308.MainFree.bankfree41_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree48_0, Research6970.Height2308.MainFree.bankfree58_0, Research6970.Height2308.MainFree.bankfree77_0, Research6970.Height2308.MainFree.bankfree82_0, Research6970.Height2308.MainFree.bankfree75_0, Research6970.Height2308.MainFree.bankfree104_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree144_0, Research6970.Height2308.MainFree.bankfree129_0, Research6970.Height2308.MainFree.bankfree161_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1417
    historyValues := [![15206, 162357, 753101, 3641328],
    ![25417/2, 117808, 534954, 2414916],
    ![54680/9, 171230/3, 534954, 2385295],
    ![29433/8, 69221/2, 2507648/9, 3435944/3],
    ![16211/9, 322841/18, 183807, 3149149/4],
    ![73046/81, 269146/27, 918523/9, 9030025/16],
    ![73648/121, 1073814/121, 4858340/49, 9030025/16],
    ![73648/121, 1073814/121, 853669/9, 6225025/16],
    ![73648/121, 828280/121, 3734044/49, 14370528/49],
    ![235552/441, 2922280/441, 66642, 14370528/49],
    ![235552/441, 2922280/441, 66642, 14370528/49],
    ![11191/21, 137792/21, 64809, 14370528/49],
    ![11191/21, 121692/19, 445764/7, 11404129/49],
    ![11191/21, 675340/121, 2962170/49, 793881/4],
    ![11191/21, 82192/15, 6284096/121, 22391824/121],
    ![813/2, 82192/15, 6284096/121, 22391824/121],
    ![813/2, 8254752/1681, 2317250/49, 8785720/49],
    ![813/2, 6044689/1369, 6947158/169, 424546136/2601],
    ![479479/1369, 6044689/1369, 6947158/169, 424546136/2601],
    ![930251/2738, 6044689/1369, 6947158/169, 424546136/2601],
    ![459746/1369, 6044689/1369, 6947158/169, 424546136/2601]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 32 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5596, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1417⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free32_0
    · exact Research6970.Height2308.MainFree.free41_0
    · exact Research6970.Height2308.MainFree.free42_2
    · exact Research6970.Height2308.MainFree.free48_0
    · exact Research6970.Height2308.MainFree.free58_0
    · exact Research6970.Height2308.MainFree.free77_0
    · exact Research6970.Height2308.MainFree.free82_0
    · exact Research6970.Height2308.MainFree.free75_0
    · exact Research6970.Height2308.MainFree.free104_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free144_0
    · exact Research6970.Height2308.MainFree.free129_0
    · exact Research6970.Height2308.MainFree.free161_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free183_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨32923051151206517653583267/61862771435208872652439552, 2660369/2838619, [310858860,310858846,310858845,310858850,310858850,310858850,311291865,311291858,155645916,156416943,156416937,156416937,156416932,104277956,71899884,77178426,92892842,91934712,114745175,185870784,229760126], [1134189,1134189,1134189,1134189,1134189,1134189,1131975,1131975,2471736,2458924,2458924,2458924,2458924,3774714,5572247,5178095,4267259,4315550,3411540,2039838,1613777], ![121961270083320,1611157360924,221186232960,5135504500], 169180618614246110⟩

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
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons28

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons29
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons29.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree32_0, Research6970.Height2308.MainFree.bankfree41_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree48_0, Research6970.Height2308.MainFree.bankfree58_0, Research6970.Height2308.MainFree.bankfree81_0, Research6970.Height2308.MainFree.bankfree82_0, Research6970.Height2308.MainFree.bankfree75_0, Research6970.Height2308.MainFree.bankfree99_0, Research6970.Height2308.MainFree.bankfree127_0, Research6970.Height2308.MainFree.bankfree144_0, Research6970.Height2308.MainFree.bankfree126_0, Research6970.Height2308.MainFree.bankfree161_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1418
    historyValues := [![15206, 162239, 752454, 3637072],
    ![25417/2, 234321/2, 532014, 2414916],
    ![54680/9, 510890/9, 532014, 4710915/2],
    ![29433/8, 275379/8, 831356/3, 1130988],
    ![16211/9, 160598/9, 1462931/8, 6219513/8],
    ![73046/81, 803728/81, 914288/9, 9030025/16],
    ![73648/121, 1070034/121, 4841400/49, 9030025/16],
    ![73648/121, 1070034/121, 849014/9, 6225025/16],
    ![73648/121, 823380/121, 3712134/49, 14190768/49],
    ![235552/441, 970220/147, 66642, 14190768/49],
    ![235552/441, 970220/147, 66642, 14190768/49],
    ![11191/21, 45744/7, 64809, 14190768/49],
    ![11191/21, 45744/7, 64809, 498875/2],
    ![11191/21, 60394/11, 2893322/49, 9991008/49],
    ![11191/21, 81667/15, 6284096/121, 22391824/121],
    ![1358449/3362, 81667/15, 6284096/121, 22391824/121],
    ![1358449/3362, 8204912/1681, 2303425/49, 8675820/49],
    ![1358449/3362, 6009409/1369, 6947158/169, 46581724/289],
    ![479479/1369, 6009409/1369, 6947158/169, 46581724/289],
    ![930251/2738, 6009409/1369, 6947158/169, 46581724/289],
    ![459746/1369, 6009409/1369, 6947158/169, 46581724/289]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 33 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5526, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1418⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free32_0
    · exact Research6970.Height2308.MainFree.free41_0
    · exact Research6970.Height2308.MainFree.free42_2
    · exact Research6970.Height2308.MainFree.free48_0
    · exact Research6970.Height2308.MainFree.free58_0
    · exact Research6970.Height2308.MainFree.free81_0
    · exact Research6970.Height2308.MainFree.free82_0
    · exact Research6970.Height2308.MainFree.free75_0
    · exact Research6970.Height2308.MainFree.free99_0
    · exact Research6970.Height2308.MainFree.free127_0
    · exact Research6970.Height2308.MainFree.free144_0
    · exact Research6970.Height2308.MainFree.free126_0
    · exact Research6970.Height2308.MainFree.free161_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free183_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨1492683316154353860592356435/2809921795002521605545918464, 34566919/36870344, [309613414,309613406,309613404,309613403,309613403,309613405,309613403,309613404,154806693,154986068,154986060,155188320,155188309,106617680,66625500,77178426,92138574,91004130,114636578,185762186,229675495], [1140557,1140557,1140557,1140557,1140557,1140557,1140557,1140557,2485682,2482702,2482702,2479341,2479341,3693534,6027247,5178095,4305275,4362452,3415308,2041147,1614472], ![121916346255900,1611248352620,221057001340,5191317880], 168552219882869822⟩

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
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons29

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons3
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons3.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree4_0, Research6970.Height2308.MainFree.bankfree9_0, Research6970.Height2308.MainFree.bankfree17_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree32_0, Research6970.Height2308.MainFree.bankfree41_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree48_0, Research6970.Height2308.MainFree.bankfree61_0, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree85_0, Research6970.Height2308.MainFree.bankfree74_2, Research6970.Height2308.MainFree.bankfree113_0, Research6970.Height2308.MainFree.bankfree144_0, Research6970.Height2308.MainFree.bankfree150_0, Research6970.Height2308.MainFree.bankfree120_0, Research6970.Height2308.MainFree.bankfree198_0, Research6970.Height2308.MainFree.bankfree210_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1392
    historyValues := [![14668, 170119, 794302, 4155631],
    ![12303, 138311, 1250483/2, 3125794],
    ![53398/9, 599801/9, 620224, 3104644],
    ![29433/8, 644197/16, 2915630/9, 4727186/3],
    ![16211/9, 744523/36, 3393057/16, 17330449/16],
    ![73046/81, 306299/27, 2091509/18, 23135495/36],
    ![73648/121, 1187376/121, 5367266/49, 23135495/36],
    ![73648/121, 1187376/121, 5367266/49, 19209005/36],
    ![73648/121, 8089, 4395308/49, 19570858/49],
    ![127905/242, 3239546/441, 549021/8, 19570858/49],
    ![127905/242, 3239546/441, 549021/8, 44962160/121],
    ![5584/11, 3239546/441, 549021/8, 44962160/121],
    ![5584/11, 1569771/242, 13598288/225, 19201306/75],
    ![5584/11, 1569771/242, 8765240/147, 27323751/121],
    ![5584/11, 9690000/1681, 43542060/841, 27323751/121],
    ![668847/1681, 9690000/1681, 43542060/841, 27323751/121],
    ![668847/1681, 2361418/441, 31870496/675, 10738729/49],
    ![668847/1681, 28360073/5476, 127760325/2809, 598535658/2809],
    ![479479/1369, 28360073/5476, 127760325/2809, 598535658/2809],
    ![930251/2738, 28360073/5476, 127760325/2809, 598535658/2809],
    ![459746/1369, 28360073/5476, 127760325/2809, 598535658/2809]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 7 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 7699, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1392⟩⟩
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
  ⟨327209559438725/594838449815552, 26902197884891173465179/29312083006944909983744, [350371910,350371898,350371901,350371904,350371900,350371901,350371899,350371899,170456405,170501411,170566824,170566802,116790633,74761631,67339733,92010703,104957162,104957162,123169174,194294783,236205240], [985736,985736,985736,985736,985736,985736,985736,985736,2225619,2225077,2224288,2224289,3351497,5344920,5962555,4311720,3751148,3751148,3173283,1938309,1560813], ![125382465496800,1604208764820,231210791770,4463866120], 194382297857021034⟩

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
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons3

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons30
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons30.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree35_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree53_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree61_0, Research6970.Height2308.MainFree.bankfree69_0, Research6970.Height2308.MainFree.bankfree72_0, Research6970.Height2308.MainFree.bankfree95_0, Research6970.Height2308.MainFree.bankfree115_0, Research6970.Height2308.MainFree.bankfree92_0, Research6970.Height2308.MainFree.bankfree140_0, Research6970.Height2308.MainFree.bankfree130_0, Research6970.Height2308.MainFree.bankfree164_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree186_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1419
    historyValues := [![15582, 160993, 741359, 3387620],
    ![25417/2, 233063/2, 529158, 2414916],
    ![54680/9, 169390/3, 529158, 4652945/2],
    ![29433/8, 273917/8, 2480876/9, 3351212/3],
    ![5710/3, 104105/6, 353847/2, 5646301/8],
    ![18775/16, 44485/4, 3217138/25, 13213818/25],
    ![86978/121, 838742/121, 3778118/49, 8288641/25],
    ![73648/121, 838742/121, 3778118/49, 8288641/25],
    ![73648/121, 819658/121, 75248, 13874236/49],
    ![73648/121, 819658/121, 70756, 13874236/49],
    ![73648/121, 819658/121, 70756, 13874236/49],
    ![73648/121, 819658/121, 70756, 9740641/36],
    ![73648/121, 820100/147, 56704, 9671576/49],
    ![73648/121, 820100/147, 56704, 9671576/49],
    ![73648/121, 820100/147, 56704, 9671576/49],
    ![1374849/3362, 820100/147, 56704, 9671576/49],
    ![1374849/3362, 8169024/1681, 327618/7, 8418965/49],
    ![1374849/3362, 5975137/1369, 6947158/169, 117462244/729],
    ![967337/2738, 5975137/1369, 6947158/169, 117462244/729],
    ![930251/2738, 5975137/1369, 6947158/169, 117462244/729],
    ![459746/1369, 5975137/1369, 6947158/169, 117462244/729]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 34 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5458, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1419⟩⟩
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
  ⟨1669974814066804288230037583/3117334689734071462842597376, 4861909/5189527, [307995372,307995360,307995361,307995364,307995362,307995363,307995363,307995362,164100698,164100699,164100699,164100689,81970807,57118686,75330723,75330747,91797385,91580920,114943680,185656692,229593283], [1148831,1148831,1148831,1148831,1148831,1148831,1148831,1148831,2331237,2331237,2331237,2331237,4862453,7063765,5305637,5305636,4322471,4333382,3404652,2042419,1615148], ![121872706482060,1611337202732,220931463480,5156724580], 166724783056331123⟩

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
    · exact Pricing.height_from_critical Band.near _ 19 _
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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons30

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons31
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons31.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree35_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree53_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree61_0, Research6970.Height2308.MainFree.bankfree69_0, Research6970.Height2308.MainFree.bankfree72_0, Research6970.Height2308.MainFree.bankfree95_0, Research6970.Height2308.MainFree.bankfree112_0, Research6970.Height2308.MainFree.bankfree138_0, Research6970.Height2308.MainFree.bankfree144_0, Research6970.Height2308.MainFree.bankfree126_0, Research6970.Height2308.MainFree.bankfree164_0, Research6970.Height2308.MainFree.bankfree214_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1420
    historyValues := [![15843, 160539, 739464, 3362968],
    ![25417/2, 463647/4, 526344, 2414916],
    ![54680/9, 505490/9, 526344, 9191655/4],
    ![29433/8, 544953/16, 822626/3, 1103358],
    ![5710/3, 155320/9, 1407817/8, 11153979/16],
    ![18775/16, 708075/64, 3200589/25, 13051611/25],
    ![86978/121, 834454/121, 3759023/49, 8288641/25],
    ![73648/121, 834454/121, 3759023/49, 8288641/25],
    ![73648/121, 814901/121, 3665980/49, 13703922/49],
    ![73648/121, 814901/121, 70756, 13703922/49],
    ![73648/121, 814901/121, 70756, 13703922/49],
    ![73648/121, 814901/121, 70756, 9740641/36],
    ![73648/121, 2432846/441, 225929/4, 797449/4],
    ![73648/121, 2432846/441, 225929/4, 797449/4],
    ![73648/121, 161309/30, 6284096/121, 22391824/121],
    ![1358449/3362, 161309/30, 6284096/121, 22391824/121],
    ![1358449/3362, 8120248/1681, 2279792/49, 16631235/98],
    ![1358449/3362, 23733829/5476, 6285076/153, 44135518/289],
    ![479479/1369, 23733829/5476, 6285076/153, 44135518/289],
    ![930251/2738, 23733829/5476, 6285076/153, 44135518/289],
    ![459746/1369, 23733829/5476, 6285076/153, 44135518/289]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 35 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5391, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1420⟩⟩
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
  ⟨11640513122548731267870719055/21709929912578796560110845952, 16977021/18116917, [307762971,307762961,307762963,307762961,307762962,307762965,307762964,307762965,162801361,162801366,162801370,162801370,81625940,81625940,66166250,78780736,92791491,92791491,114368852,185494461,229467636], [1150019,1150019,1150019,1150019,1150019,1150019,1150019,1150019,2352829,2352829,2352829,2352829,4882920,4882920,6068844,5067491,4272367,4272367,3424597,2044374,1616180], ![121806010541520,1611472384224,220738408590,5084116730], 166270027133692844⟩

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
    · exact Pricing.height_from_critical Band.near _ 16 _
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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons31

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons32
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons32.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree31_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree88_0, Research6970.Height2308.MainFree.bankfree87_1, Research6970.Height2308.MainFree.bankfree127_0, Research6970.Height2308.MainFree.bankfree130_0, Research6970.Height2308.MainFree.bankfree166_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree181_0, Research6970.Height2308.MainFree.bankfree214_0, Research6970.Height2308.MainFree.bankfree170_0] i
    head := Research6970.Height2308.MainHeads.src1421
    historyValues := [![15955, 159733, 737059, 3261028],
    ![25417/2, 230621/2, 523614, 2414916],
    ![54680/9, 167630/3, 523614, 4540415/2],
    ![29433/8, 271079/8, 2455268/9, 3270164/3],
    ![64334/25, 578592/25, 204686, 3728761/4],
    ![17323/9, 103241/6, 1394257/8, 2724249/4],
    ![18775/16, 176125/16, 3184534/25, 12894246/25],
    ![89110/121, 817430/121, 529404/7, 7683984/25],
    ![89110/121, 817430/121, 529404/7, 7683984/25],
    ![89110/121, 817430/121, 529404/7, 7626832/25],
    ![27491/49, 290561/49, 2884071/49, 3866676/13],
    ![27491/49, 652134/121, 2839122/49, 9629408/49],
    ![1374849/3362, 652134/121, 2839122/49, 9629408/49],
    ![1374849/3362, 8104424/1681, 2270056/49, 16220333/98],
    ![1374849/3362, 1963424/441, 4970373/121, 297318624/1849],
    ![953281/2738, 1963424/441, 4970373/121, 297318624/1849],
    ![953281/2738, 11799347/2738, 35414624/867, 110796676/729],
    ![462287/1369, 11799347/2738, 35414624/867, 110796676/729]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 36 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5326, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1421⟩⟩
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
    · exact Research6970.Height2308.MainFree.free130_0
    · exact Research6970.Height2308.MainFree.free166_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free181_0
    · exact Research6970.Height2308.MainFree.free214_0
    · exact Research6970.Height2308.MainFree.free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨5774676047440738243013150723/10784471552874467127607689216, 33845933/36115989, [306435626,306435618,306435615,306435618,306435617,306435616,306435618,162133747,162133755,162133755,162133749,75510086,75510088,78840451,92312963,91758567,135975320,230163399], [1156806,1156806,1156806,1156806,1156806,1156806,1156806,2363923,2363923,2363923,2363923,5293256,5293256,5063370,4296486,4324428,2856712,1610463], ![122175335457180,1610722571976,207147059100,5164637400], 164862388454139067⟩

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
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons32

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons33
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons33.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree31_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree88_0, Research6970.Height2308.MainFree.bankfree87_1, Research6970.Height2308.MainFree.bankfree127_0, Research6970.Height2308.MainFree.bankfree94_0, Research6970.Height2308.MainFree.bankfree165_0, Research6970.Height2308.MainFree.bankfree190_0, Research6970.Height2308.MainFree.bankfree214_0, Research6970.Height2308.MainFree.bankfree176_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1422
    historyValues := [![15955, 159477, 735843, 3250532],
    ![25417/2, 229437/2, 522144, 2414916],
    ![54680/9, 500330/9, 522144, 4485855/2],
    ![29433/8, 269703/8, 271428, 1076956],
    ![64334/25, 575584/25, 204686, 3728761/4],
    ![17323/9, 102697/6, 1386993/8, 2691513/4],
    ![18775/16, 175245/16, 3168726/25, 12739302/25],
    ![89110/121, 813270/121, 526716/7, 7683984/25],
    ![89110/121, 813270/121, 526716/7, 7683984/25],
    ![89110/121, 813270/121, 526716/7, 7535184/25],
    ![27491/49, 289281/49, 1882881/32, 3820212/13],
    ![27491/49, 58930/11, 2821778/49, 9513696/49],
    ![66257/150, 58930/11, 2821778/49, 9513696/49],
    ![66257/150, 8042624/1681, 45967, 37982569/225],
    ![983773/2738, 8042624/1681, 45967, 37982569/225],
    ![983773/2738, 11732819/2738, 105650720/2601, 110796676/729],
    ![938035/2738, 11732819/2738, 105650720/2601, 110796676/729],
    ![459746/1369, 11732819/2738, 105650720/2601, 110796676/729]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 37 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5262, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1422⟩⟩
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
    · exact Research6970.Height2308.MainFree.free94_0
    · exact Research6970.Height2308.MainFree.free165_0
    · exact Research6970.Height2308.MainFree.free190_0
    · exact Research6970.Height2308.MainFree.free214_0
    · exact Research6970.Height2308.MainFree.free176_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨5330460158620856448699413/9971165638903475457228800, 689878/735845, [305053674,305053665,305053664,305053663,305053663,305053666,305053663,162947115,162947122,162947122,162947114,98121618,84941222,91132380,90896204,100162017,185731363,228893107], [1163872,1163872,1163872,1163872,1163872,1163872,1163872,2350407,2350407,2350407,2350407,4031857,4686161,4355988,4367892,3945786,2041519,1620901], ![121501039057740,1612091632208,221020321970,5197791480], 164581096655086584⟩

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
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons33
end Pack_R6970Height2313MainPlans05

section Pack_R6970Height2313MainPlans06

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons34
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons34.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree31_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree64_0, Research6970.Height2308.MainFree.bankfree72_0, Research6970.Height2308.MainFree.bankfree76_0, Research6970.Height2308.MainFree.bankfree97_0, Research6970.Height2308.MainFree.bankfree116_1, Research6970.Height2308.MainFree.bankfree86_1, Research6970.Height2308.MainFree.bankfree140_0, Research6970.Height2308.MainFree.bankfree166_0, Research6970.Height2308.MainFree.bankfree191_0, Research6970.Height2308.MainFree.bankfree214_0, Research6970.Height2308.MainFree.bankfree174_0] i
    head := Research6970.Height2308.MainHeads.src1423
    historyValues := [![15922, 158513, 730871, 3226916],
    ![25417/2, 456543/4, 522144, 2414916],
    ![54680/9, 497810/9, 522144, 8864295/4],
    ![29433/8, 536697/16, 270070, 1064062],
    ![64334/25, 572623/25, 204686, 3728761/4],
    ![17323/9, 204323/12, 2759685/16, 5318577/8],
    ![18775/16, 697515/64, 630633/5, 12586779/25],
    ![89110/121, 809175/121, 524070/7, 7683984/25],
    ![89110/121, 809175/121, 524070/7, 7683984/25],
    ![89110/121, 809175/121, 524070/7, 7683984/25],
    ![230860/361, 2345150/361, 66312, 7683984/25],
    ![230860/361, 2345150/361, 66312, 1426259/6],
    ![230860/361, 1284909/242, 397653/7, 19075131/98],
    ![27432/49, 1284909/242, 397653/7, 19075131/98],
    ![27432/49, 1284909/242, 397653/7, 19075131/98],
    ![27432/49, 8009936/1681, 4487915/98, 37100281/225],
    ![987665/2738, 8009936/1681, 4487915/98, 37100281/225],
    ![987665/2738, 23334661/5476, 105066836/2601, 110796676/729],
    ![930251/2738, 23334661/5476, 105066836/2601, 110796676/729]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 38 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5199, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1423⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free31_0
    · exact Research6970.Height2308.MainFree.free37_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free64_0
    · exact Research6970.Height2308.MainFree.free72_0
    · exact Research6970.Height2308.MainFree.free76_0
    · exact Research6970.Height2308.MainFree.free97_0
    · exact Research6970.Height2308.MainFree.free116_1
    · exact Research6970.Height2308.MainFree.free86_1
    · exact Research6970.Height2308.MainFree.free140_0
    · exact Research6970.Height2308.MainFree.free166_0
    · exact Research6970.Height2308.MainFree.free191_0
    · exact Research6970.Height2308.MainFree.free214_0
    · exact Research6970.Height2308.MainFree.free174_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨11329149876863519063484454959/21208299002634114520494112768, 67137639/71625554, [302451374,302451362,302451364,302451363,302451364,302451364,302451368,150169904,150169904,150169904,150344858,150344852,48388627,62568867,82641608,94949887,94190277,114661130,230698386], [1177178,1177178,1177178,1177178,1177178,1177178,1177178,2562735,2562735,2562735,2559828,2559828,8371825,6430187,4822641,4165651,4201867,3414456,1606066], ![122459317256520,1610145453744,207628547400,5000221730], 163072682395436521⟩

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
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 22 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons34

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons35
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons35.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree35_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree53_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree61_0, Research6970.Height2308.MainFree.bankfree69_0, Research6970.Height2308.MainFree.bankfree72_0, Research6970.Height2308.MainFree.bankfree95_0, Research6970.Height2308.MainFree.bankfree113_0, Research6970.Height2308.MainFree.bankfree138_0, Research6970.Height2308.MainFree.bankfree144_0, Research6970.Height2308.MainFree.bankfree131_0, Research6970.Height2308.MainFree.bankfree164_0, Research6970.Height2308.MainFree.bankfree214_0, Research6970.Height2308.MainFree.bankfree186_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1424
    historyValues := [![15843, 159540, 734683, 3324512],
    ![25417/2, 227143/2, 522144, 2414916],
    ![54680/9, 495370/9, 522144, 4380145/2],
    ![29433/8, 267037/8, 2418796/9, 3154732/3],
    ![5710/3, 304315/18, 344807/2, 5315261/8],
    ![18775/16, 43385/4, 3138098/25, 12439098/25],
    ![86978/121, 818262/121, 3686918/49, 8288641/25],
    ![73648/121, 818262/121, 3686918/49, 8288641/25],
    ![73648/121, 796938/121, 3586032/49, 1865828/7],
    ![73648/121, 796938/121, 70756, 1865828/7],
    ![73648/121, 796938/121, 70756, 1865828/7],
    ![73648/121, 796938/121, 70756, 32071396/121],
    ![73648/121, 1277817/242, 2749078/49, 1372947/7],
    ![73648/121, 1277817/242, 2749078/49, 1372947/7],
    ![73648/121, 78757/15, 6284096/121, 9117381/50],
    ![689574/1681, 78757/15, 6284096/121, 9117381/50],
    ![689574/1681, 7936064/1681, 2228686/49, 1522756/9],
    ![689574/1681, 11603921/2738, 104501488/2601, 94644529/625],
    ![967337/2738, 11603921/2738, 104501488/2601, 94644529/625],
    ![930251/2738, 11603921/2738, 104501488/2601, 94644529/625],
    ![459746/1369, 11603921/2738, 104501488/2601, 94644529/625]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 39 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5138, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1424⟩⟩
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
    · exact Research6970.Height2308.MainFree.free113_0
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
  ⟨11414722099949306940883211687/21430107358781509381600051200, 33770879/35999565, [302340524,302340516,302340509,302340517,302340515,302340515,302340514,302340514,162182287,162182304,162182304,162182286,84803697,84803697,70728482,70728502,92038513,92038511,113303895,184016907,228340846], [1177745,1177745,1177745,1177745,1177745,1177745,1177745,1177745,2363117,2363116,2363116,2363117,4694323,4694323,5665299,5665298,4310318,4310318,3461547,2062182,1625440], ![121207887873720,1612687399064,218980119330,5129278420], 163009394624167048⟩

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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons35

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons36
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons36.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree35_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree53_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree58_0, Research6970.Height2308.MainFree.bankfree69_0, Research6970.Height2308.MainFree.bankfree71_0, Research6970.Height2308.MainFree.bankfree88_0, Research6970.Height2308.MainFree.bankfree105_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree144_0, Research6970.Height2308.MainFree.bankfree131_0, Research6970.Height2308.MainFree.bankfree165_0, Research6970.Height2308.MainFree.bankfree214_0, Research6970.Height2308.MainFree.bankfree186_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1425
    historyValues := [![15843, 159322, 733624, 3316070],
    ![25417/2, 452103/4, 522144, 2414916],
    ![54680/9, 493010/9, 522144, 8659695/4],
    ![29433/8, 531537/16, 802450/3, 1039502],
    ![5710/3, 151420/9, 1372561/8, 10508451/16],
    ![18775/16, 690915/64, 124941, 12296259/25],
    ![86978/121, 814486/121, 3670103/49, 8288641/25],
    ![73648/121, 814486/121, 3670103/49, 8288641/25],
    ![73648/121, 792090/121, 3572223/49, 13042872/49],
    ![73648/121, 792090/121, 70756, 13042872/49],
    ![73648/121, 792090/121, 70756, 13042872/49],
    ![73648/121, 792090/121, 70756, 13042872/49],
    ![73648/121, 2217066/361, 452064/7, 11048976/49],
    ![73648/121, 642252/121, 5631201/98, 9050778/49],
    ![73648/121, 156629/30, 6284096/121, 18025371/100],
    ![689574/1681, 156629/30, 6284096/121, 18025371/100],
    ![689574/1681, 7908668/1681, 2215417/49, 37982569/225],
    ![689574/1681, 23085181/5476, 103954676/2601, 187115439/1250],
    ![967337/2738, 23085181/5476, 103954676/2601, 187115439/1250],
    ![930251/2738, 23085181/5476, 103954676/2601, 187115439/1250],
    ![459746/1369, 23085181/5476, 103954676/2601, 187115439/1250]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 40 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5079, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1425⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free35_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free53_0
    · exact Research6970.Height2308.MainFree.free42_2
    · exact Research6970.Height2308.MainFree.free58_0
    · exact Research6970.Height2308.MainFree.free69_0
    · exact Research6970.Height2308.MainFree.free71_0
    · exact Research6970.Height2308.MainFree.free88_0
    · exact Research6970.Height2308.MainFree.free105_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free144_0
    · exact Research6970.Height2308.MainFree.free131_0
    · exact Research6970.Height2308.MainFree.free165_0
    · exact Research6970.Height2308.MainFree.free214_0
    · exact Research6970.Height2308.MainFree.free186_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨5682072421920991786271201789/10684185855232383724705284096, 33732257/35947674, [301094521,301094506,301094507,301094511,301094513,301094515,301094510,301094511,161464252,161464242,161464249,161464242,161464244,94698343,67884699,67884706,91459813,91459813,112959327,183672339,228078077], [1184116,1184116,1184116,1184116,1184116,1184116,1184116,1184116,2375049,2375049,2375049,2375049,2375049,4176262,5913194,5913194,4339485,4339485,3473502,2066335,1627599], ![121068404833140,1612970506048,218570083410,5163987150], 162255485756116098⟩

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
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons36

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons4
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons4.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree4_0, Research6970.Height2308.MainFree.bankfree9_0, Research6970.Height2308.MainFree.bankfree17_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree32_0, Research6970.Height2308.MainFree.bankfree41_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree48_0, Research6970.Height2308.MainFree.bankfree61_0, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree85_0, Research6970.Height2308.MainFree.bankfree74_2, Research6970.Height2308.MainFree.bankfree113_0, Research6970.Height2308.MainFree.bankfree140_0, Research6970.Height2308.MainFree.bankfree150_0, Research6970.Height2308.MainFree.bankfree120_0, Research6970.Height2308.MainFree.bankfree198_0, Research6970.Height2308.MainFree.bankfree210_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1393
    historyValues := [![14668, 169748, 792443, 4143867],
    ![12303, 137456, 621394, 3087224],
    ![53398/9, 596096/9, 620224, 3087224],
    ![29433/8, 40007, 2897200/9, 4668856/3],
    ![16211/9, 123343/6, 421579/2, 4279151/4],
    ![73046/81, 913862/81, 346669/3, 5712505/9],
    ![73648/121, 1182246/121, 763468/7, 5712505/9],
    ![73648/121, 1182246/121, 763468/7, 4742995/9],
    ![73648/121, 972024/121, 4365288/49, 19329368/49],
    ![127905/242, 3223016/441, 549021/8, 19329368/49],
    ![127905/242, 3223016/441, 549021/8, 44407360/121],
    ![5584/11, 3223016/441, 549021/8, 44407360/121],
    ![5584/11, 1558941/242, 13501768/225, 18964376/75],
    ![5584/11, 1558941/242, 13501768/225, 18964376/75],
    ![5584/11, 9625400/1681, 43254400/841, 199255216/841],
    ![668847/1681, 9625400/1681, 43254400/841, 199255216/841],
    ![668847/1681, 2346028/441, 31664536/675, 10738729/49],
    ![668847/1681, 7043302/1369, 126924420/2809, 591150168/2809],
    ![479479/1369, 7043302/1369, 126924420/2809, 591150168/2809],
    ![930251/2738, 7043302/1369, 126924420/2809, 591150168/2809],
    ![459746/1369, 7043302/1369, 126924420/2809, 591150168/2809]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 8 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 7604, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1393⟩⟩
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
  ⟨727530484207937/1318980484595712, 4825156115489952246600425/5188333162394040164941824, [348439078,348439068,348439065,348439066,348439069,348439070,348439071,348439071,170456285,171075549,171075539,170652381,82087383,86967607,67014604,91296214,103747401,103747401,122671253,193796862,235825352], [991030,991030,991030,991030,991030,991030,991030,991030,2225621,2218157,2218157,2223257,4855534,4565897,5992004,4347731,3794541,3794541,3187195,1944310,1563935], ![125180813348640,1604618432668,230618265780,4515503790], 193126598693164391⟩

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
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons4

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons5
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons5.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree4_0, Research6970.Height2308.MainFree.bankfree9_0, Research6970.Height2308.MainFree.bankfree17_0, Research6970.Height2308.MainFree.bankfree23_0, Research6970.Height2308.MainFree.bankfree26_0, Research6970.Height2308.MainFree.bankfree32_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree98_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree125_0, Research6970.Height2308.MainFree.bankfree152_0, Research6970.Height2308.MainFree.bankfree198_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree210_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1394
    historyValues := [![14923, 167803, 783678, 3875144],
    ![12303, 136619, 1235255/2, 3049466],
    ![53398/9, 592469/9, 1235255/2, 3049466],
    ![3599, 79829/2, 2894662/9, 14278411/9],
    ![60658/25, 688844/25, 211854, 1110916],
    ![16211/9, 81743/4, 3352637/16, 16907261/16],
    ![18775/16, 824675/64, 132886, 651249],
    ![89110/121, 959455/121, 621174/7, 424908],
    ![89110/121, 959455/121, 2794543/36, 27047111/72],
    ![127905/242, 3206834/441, 549021/8, 27047111/72],
    ![127905/242, 3206834/441, 549021/8, 10686361/36],
    ![127905/242, 797900/121, 505197/8, 5948712/25],
    ![677069/1681, 797900/121, 505197/8, 5948712/25],
    ![677069/1681, 9587136/1681, 42991136/841, 6641796/29],
    ![677069/1681, 2330962/441, 31462912/675, 49227094/225],
    ![479479/1369, 2330962/441, 31462912/675, 49227094/225],
    ![479479/1369, 27990277/5476, 126106113/2809, 583920162/2809],
    ![930251/2738, 27990277/5476, 126106113/2809, 583920162/2809],
    ![459746/1369, 27990277/5476, 126106113/2809, 583920162/2809]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 9 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 7511, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1394⟩⟩
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
    · exact Research6970.Height2308.MainFree.free98_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free125_0
    · exact Research6970.Height2308.MainFree.free152_0
    · exact Research6970.Height2308.MainFree.free198_0
    · exact Research6970.Height2308.MainFree.free183_0
    · exact Research6970.Height2308.MainFree.free210_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨3221993721217109/5867403669929984, 10388166572061748558944965/11407764396602309438603264, [346329319,346329304,346329310,346329309,346329308,346329309,346329310,147358091,147358091,147358103,147358103,74702350,74702727,90893101,103067420,103067420,122183814,193309423,235453463], [996809,996809,996809,996809,996809,996809,996809,2609461,2609461,2609461,2609461,5349629,5349599,4368048,3823225,3823225,3200813,1950185,1566991], ![124983407229660,1605019335112,230038213370,4549637750], 190824372281853550⟩

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
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons5

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons6
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons6.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree4_0, Research6970.Height2308.MainFree.bankfree9_0, Research6970.Height2308.MainFree.bankfree17_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree32_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree53_0, Research6970.Height2308.MainFree.bankfree62_0, Research6970.Height2308.MainFree.bankfree82_0, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree116_1, Research6970.Height2308.MainFree.bankfree110_0, Research6970.Height2308.MainFree.bankfree168_0, Research6970.Height2308.MainFree.bankfree121_0, Research6970.Height2308.MainFree.bankfree150_0, Research6970.Height2308.MainFree.bankfree198_0, Research6970.Height2308.MainFree.bankfree179_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree170_0] i
    head := Research6970.Height2308.MainHeads.src1395
    historyValues := [![14880, 168115, 782310, 3851304],
    ![12303, 135773, 1227641/2, 3011302],
    ![53398/9, 588803/9, 1227641/2, 3011302],
    ![29433/8, 632071/16, 2860922/9, 4554038/3],
    ![16211/9, 731269/36, 3332427/16, 16695667/16],
    ![18775/16, 819505/64, 132886, 651249],
    ![86978/121, 964118/121, 4336433/49, 21353543/49],
    ![86978/121, 964118/121, 4336433/49, 21353543/49],
    ![86978/121, 964118/121, 4336433/49, 44264656/121],
    ![127905/242, 3190478/441, 549021/8, 44264656/121],
    ![127905/242, 140603/22, 964947/16, 18141982/75],
    ![127905/242, 765539/121, 946157/16, 18141982/75],
    ![127905/242, 765539/121, 946157/16, 4561455/22],
    ![672960/1681, 765539/121, 946157/16, 4561455/22],
    ![672960/1681, 9498240/1681, 42688164/841, 4561455/22],
    ![672960/1681, 2315734/441, 6251824/135, 4561455/22],
    ![945497/2738, 2315734/441, 6251824/135, 4561455/22],
    ![945497/2738, 6962473/1369, 125128710/2809, 562698122/2809],
    ![462287/1369, 6962473/1369, 125128710/2809, 562698122/2809]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 10 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 7417, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1395⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free4_0
    · exact Research6970.Height2308.MainFree.free9_0
    · exact Research6970.Height2308.MainFree.free17_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free32_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free53_0
    · exact Research6970.Height2308.MainFree.free62_0
    · exact Research6970.Height2308.MainFree.free82_0
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free116_1
    · exact Research6970.Height2308.MainFree.free110_0
    · exact Research6970.Height2308.MainFree.free168_0
    · exact Research6970.Height2308.MainFree.free121_0
    · exact Research6970.Height2308.MainFree.free150_0
    · exact Research6970.Height2308.MainFree.free198_0
    · exact Research6970.Height2308.MainFree.free179_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨1623197953099513/2939156502151168, 331916687078217314173369/357819531919720599519232, [344562890,344562879,344562878,344562881,344562880,344562879,150469884,150469884,150469864,150469860,92897403,114854287,74761617,69755332,91927760,106941114,106941105,143082686,236041369], [1001648,1001648,1001648,1001648,1001648,1001648,2557750,2557750,2557751,2557751,4267029,3407754,5344921,5743760,4315900,3682312,3682313,2700964,1562160], ![125295479492580,1604385626996,212437232100,4402218000], 189298626326417504⟩

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
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
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
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons6

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons7
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons7.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree4_0, Research6970.Height2308.MainFree.bankfree9_0, Research6970.Height2308.MainFree.bankfree17_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree32_0, Research6970.Height2308.MainFree.bankfree41_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree48_0, Research6970.Height2308.MainFree.bankfree61_0, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree85_0, Research6970.Height2308.MainFree.bankfree74_2, Research6970.Height2308.MainFree.bankfree113_0, Research6970.Height2308.MainFree.bankfree140_0, Research6970.Height2308.MainFree.bankfree150_0, Research6970.Height2308.MainFree.bankfree120_0, Research6970.Height2308.MainFree.bankfree198_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1396
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
    ![668847/1681, 9435680/1681, 4959107/98, 191944300/841],
    ![668847/1681, 328690/63, 31059664/675, 1920322/9],
    ![668847/1681, 6916105/1369, 27788632/625, 555718450/2809],
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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 11 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 7325, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1396⟩⟩
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
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free183_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨13538525383284102435951140967/24634621679870739771836858368, 72235689/77194796, [343036522,343036509,343036508,343036509,343036511,343036512,343036512,343036514,169532092,169596365,169532204,169596344,80220871,85759061,67225139,89376946,102457987,102457987,121419229,192544838,234869437], [1005829,1005829,1005829,1005829,1005829,1005829,1005829,1005829,2240979,2239911,2240978,2239912,4968082,4637623,5972935,4444464,3848933,3848933,3222176,1959400,1571790], ![124673394548340,1605648798908,229128357220,4580230270], 189595743673694270⟩

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
    · exact Pricing.height_from_critical Band.near _ 14 _
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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons7

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons8
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons8.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree4_0, Research6970.Height2308.MainFree.bankfree9_0, Research6970.Height2308.MainFree.bankfree17_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree32_0, Research6970.Height2308.MainFree.bankfree41_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree48_0, Research6970.Height2308.MainFree.bankfree61_0, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree85_0, Research6970.Height2308.MainFree.bankfree74_2, Research6970.Height2308.MainFree.bankfree113_0, Research6970.Height2308.MainFree.bankfree140_0, Research6970.Height2308.MainFree.bankfree150_0, Research6970.Height2308.MainFree.bankfree120_0, Research6970.Height2308.MainFree.bankfree198_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1397
    historyValues := [![14668, 168635, 786136, 4086733],
    ![12303, 134117, 1212737/2, 2936598],
    ![53398/9, 581627/9, 1212737/2, 2936598],
    ![29433/8, 624159/16, 313914, 1480354],
    ![16211/9, 722621/36, 3292867/16, 16281483/16],
    ![73046/81, 894199/81, 2035123/18, 7245055/12],
    ![73648/121, 1162212/121, 750642/7, 7245055/12],
    ![73648/121, 1162212/121, 1925059/18, 6015445/12],
    ![73648/121, 945683/121, 4248052/49, 18386286/49],
    ![127905/242, 3158462/441, 549021/8, 18386286/49],
    ![127905/242, 3158462/441, 549021/8, 42240720/121],
    ![5584/11, 3158462/441, 549021/8, 42240720/121],
    ![5584/11, 137877/22, 475107/8, 6013034/25],
    ![5584/11, 137877/22, 475107/8, 6013034/25],
    ![5584/11, 9373120/1681, 4959107/98, 189533532/841],
    ![668847/1681, 9373120/1681, 4959107/98, 189533532/841],
    ![668847/1681, 2285926/441, 3428912/75, 15801694/75],
    ![668847/1681, 6869737/1369, 27788632/625, 548738778/2809],
    ![479479/1369, 6869737/1369, 27788632/625, 548738778/2809],
    ![930251/2738, 6869737/1369, 27788632/625, 548738778/2809],
    ![459746/1369, 6869737/1369, 27788632/625, 548738778/2809]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 12 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 7233, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1397⟩⟩
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
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free183_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨4485866679119709304081289591/8178964536148736332127010816, 72082417/77041524, [341255034,341255025,341255022,341255019,341255025,341255028,341255027,341255024,167678532,167678598,167724103,167724094,65013774,85313713,66089517,89022889,102308023,102308023,121276501,192402110,234758208], [1010709,1010709,1010709,1010709,1010709,1010709,1010709,1010709,2271781,2271780,2271024,2271024,6179717,4664054,6075795,4462309,3855259,3855259,3226164,1961120,1572704], ![124614351970560,1605768692352,228958510900,4587758210], 188522111557552367⟩

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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons8

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons9
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.CubicSingletons9.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree4_0, Research6970.Height2308.MainFree.bankfree9_0, Research6970.Height2308.MainFree.bankfree17_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree32_0, Research6970.Height2308.MainFree.bankfree41_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree48_0, Research6970.Height2308.MainFree.bankfree61_0, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree85_0, Research6970.Height2308.MainFree.bankfree74_2, Research6970.Height2308.MainFree.bankfree113_0, Research6970.Height2308.MainFree.bankfree140_0, Research6970.Height2308.MainFree.bankfree150_0, Research6970.Height2308.MainFree.bankfree120_0, Research6970.Height2308.MainFree.bankfree198_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1398
    historyValues := [![14668, 168362, 784589, 4072719],
    ![12303, 133298, 602683, 2899652],
    ![53398/9, 578078/9, 602683, 2899652],
    ![29433/8, 310123/8, 2807572/9, 4385188/3],
    ![16211/9, 19954, 1636651/8, 8038321/8],
    ![73046/81, 889376/81, 337352/3, 10730855/18],
    ![73648/121, 1157298/121, 747496/7, 10730855/18],
    ![73648/121, 1157298/121, 318826/3, 8909645/18],
    ![73648/121, 939222/121, 4219296/49, 18154964/49],
    ![127905/242, 3142628/441, 549021/8, 18154964/49],
    ![127905/242, 3142628/441, 549021/8, 41709280/121],
    ![5584/11, 3142628/441, 549021/8, 41709280/121],
    ![5584/11, 1506273/242, 475107/8, 17812148/75],
    ![5584/11, 1506273/242, 475107/8, 17812148/75],
    ![5584/11, 9311240/1681, 4959107/98, 187148968/841],
    ![668847/1681, 9311240/1681, 4959107/98, 187148968/841],
    ![668847/1681, 2271184/441, 6132584/135, 46808668/225],
    ![668847/1681, 184429/37, 27788632/625, 541834972/2809],
    ![479479/1369, 184429/37, 27788632/625, 541834972/2809],
    ![930251/2738, 184429/37, 27788632/625, 541834972/2809],
    ![459746/1369, 184429/37, 27788632/625, 541834972/2809]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 13 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 7142, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1398⟩⟩
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
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free183_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨209027031978269634161328693/381881544959196457562963968, 71930811/76889918, [339492910,339492897,339492902,339492901,339492902,339492902,339492899,339492902,167963288,167963321,168198531,168198524,81915988,84873167,66000875,88672680,102667050,102667050,121135325,192260933,234648188], [1015536,1015536,1015536,1015536,1015536,1015536,1015536,1015536,2267049,2267049,2263140,2263140,4865706,4690200,6083823,4479960,3840114,3840114,3230108,1962822,1573609], ![124555951154160,1605887778772,228790510270,4569735660], 187463557172465874⟩

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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.CubicSingletons9

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases0
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HigherHelperCases0.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree3_0, Research6970.Height2308.MainFree.bankfree10_0, Research6970.Height2308.MainFree.bankfree16_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree33_1, Research6970.Height2308.MainFree.bankfree42_1, Research6970.Height2308.MainFree.bankfree52_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree83_1, Research6970.Height2308.MainFree.bankfree93_0, Research6970.Height2308.MainFree.bankfree89_2, Research6970.Height2308.MainFree.bankfree123_0, Research6970.Height2308.MainFree.bankfree168_0, Research6970.Height2308.MainFree.bankfree122_0, Research6970.Height2308.MainFree.bankfree147_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree158_0, Research6970.Height2308.MainFree.bankfree211_0, Research6970.Height2308.MainFree.bankfree171_0] i
    head := Research6970.Height2308.MainHeads.src1387
    historyValues := [![14758, 171536, 797572, 4127973],
    ![24861/2, 285259/2, 1301693/2, 6634817/2],
    ![53228/9, 208424/3, 622650, 3164841],
    ![29433/8, 334547/8, 3027956/9, 5082692/3],
    ![5468/3, 42843/2, 871419/4, 9101661/8],
    ![36739/32, 436771/32, 1209338/9, 6295081/9],
    ![86206/121, 1016214/121, 4597472/49, 24088980/49],
    ![86206/121, 1016214/121, 4597472/49, 24088980/49],
    ![63754/121, 919069/121, 68816, 23310848/49],
    ![63754/121, 919069/121, 68816, 350464],
    ![63754/121, 919069/121, 68816, 350464],
    ![63754/121, 827920/121, 14461064/225, 12052768/45],
    ![63754/121, 827920/121, 14461064/225, 2545485/11],
    ![82583/200, 827920/121, 14461064/225, 2545485/11],
    ![82583/200, 154646/25, 9531732/169, 2545485/11],
    ![82583/200, 2467232/441, 7071040/147, 5410276/25],
    ![481736/1323, 2467232/441, 7071040/147, 5410276/25],
    ![481736/1323, 29241660/5329, 2263775/48, 216225],
    ![1835316/5329, 29241660/5329, 2263775/48, 216225]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 1 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 8278, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1387⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free3_0
    · exact Research6970.Height2308.MainFree.free10_0
    · exact Research6970.Height2308.MainFree.free16_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free33_1
    · exact Research6970.Height2308.MainFree.free42_1
    · exact Research6970.Height2308.MainFree.free52_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free83_1
    · exact Research6970.Height2308.MainFree.free93_0
    · exact Research6970.Height2308.MainFree.free89_2
    · exact Research6970.Height2308.MainFree.free123_0
    · exact Research6970.Height2308.MainFree.free168_0
    · exact Research6970.Height2308.MainFree.free122_0
    · exact Research6970.Height2308.MainFree.free147_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free158_0
    · exact Research6970.Height2308.MainFree.free211_0
    · exact Research6970.Height2308.MainFree.free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨1080105672957269/1999310352809984, 68251366983130365782983/82784504540286326472704, [361018636,361018625,361018624,361018621,361018626,361018628,188866023,188865995,188866033,125910693,87998777,125910693,77627443,73853283,100380713,94048835,109091251,140831124,243281220], [956572,956572,956572,956572,956572,956572,2003738,2003739,2003738,3096685,4513925,3096685,5147100,5417076,3936560,4208996,3607710,2750304,1502666], ![129138537200400,1596580692600,218953098000,4293175920], 202948841893251291⟩

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
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases0

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases1
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HigherHelperCases1.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree3_0, Research6970.Height2308.MainFree.bankfree10_0, Research6970.Height2308.MainFree.bankfree16_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree28_0, Research6970.Height2308.MainFree.bankfree33_1, Research6970.Height2308.MainFree.bankfree42_1, Research6970.Height2308.MainFree.bankfree52_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree83_1, Research6970.Height2308.MainFree.bankfree83_0, Research6970.Height2308.MainFree.bankfree123_0, Research6970.Height2308.MainFree.bankfree122_0, Research6970.Height2308.MainFree.bankfree147_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree158_0, Research6970.Height2308.MainFree.bankfree211_0, Research6970.Height2308.MainFree.bankfree171_0] i
    head := Research6970.Height2308.MainHeads.src1388
    historyValues := [![14883, 170924, 794679, 4049119],
    ![24861/2, 283495/2, 646804, 3278135],
    ![53228/9, 69050, 622650, 3164841],
    ![29433/8, 41555, 3008944/9, 5022520/3],
    ![62542/25, 28726, 412255/2, 4112495/4],
    ![5468/3, 127745/6, 412255/2, 4112495/4],
    ![36739/32, 434125/32, 1209338/9, 6295081/9],
    ![86206/121, 1010040/121, 4569640/49, 23803800/49],
    ![86206/121, 1010040/121, 4569640/49, 23803800/49],
    ![63754/121, 914806/121, 68816, 23034880/49],
    ![63754/121, 914806/121, 68816, 2264224/5],
    ![63754/121, 822040/121, 574256/9, 2382016/9],
    ![82583/200, 822040/121, 574256/9, 2382016/9],
    ![82583/200, 245797/40, 2757029/49, 210160560/841],
    ![82583/200, 7351520/1323, 7071040/147, 114160080/529],
    ![481736/1323, 7351520/1323, 7071040/147, 114160080/529],
    ![481736/1323, 29046150/5329, 2263775/48, 114160080/529],
    ![1835316/5329, 29046150/5329, 2263775/48, 114160080/529]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 3 2 385979 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 8180, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1388⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free3_0
    · exact Research6970.Height2308.MainFree.free10_0
    · exact Research6970.Height2308.MainFree.free16_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free28_0
    · exact Research6970.Height2308.MainFree.free33_1
    · exact Research6970.Height2308.MainFree.free42_1
    · exact Research6970.Height2308.MainFree.free52_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free83_1
    · exact Research6970.Height2308.MainFree.free83_0
    · exact Research6970.Height2308.MainFree.free123_0
    · exact Research6970.Height2308.MainFree.free122_0
    · exact Research6970.Height2308.MainFree.free147_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free158_0
    · exact Research6970.Height2308.MainFree.free211_0
    · exact Research6970.Height2308.MainFree.free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨430496775135251/796870930595840, 2602450273544889886270663/3156282261017653149696000, [359734618,359734603,359734605,359734603,359734611,359734609,359734610,162477587,162477587,162477587,162477587,78759745,78759759,99852554,90024959,103831948,140676521,243160737], [960090,960090,960090,960090,960090,960090,960090,2358209,2358209,2358209,2358209,5068940,5068939,3958840,4411804,3790975,2753692,1503656], ![129074582414340,1596710538228,218844663300,4511260250], 201714061481876775⟩

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
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases1

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases2
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HigherHelperCases2.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree3_0, Research6970.Height2308.MainFree.bankfree10_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree33_1, Research6970.Height2308.MainFree.bankfree42_1, Research6970.Height2308.MainFree.bankfree52_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree83_0, Research6970.Height2308.MainFree.bankfree83_1, Research6970.Height2308.MainFree.bankfree123_0, Research6970.Height2308.MainFree.bankfree198_0, Research6970.Height2308.MainFree.bankfree158_0, Research6970.Height2308.MainFree.bankfree171_0] i
    head := Research6970.Height2308.MainHeads.src1544
    historyValues := [![15077, 170689, 792514, 3922223],
    ![24861/2, 273379/2, 1247243/2, 6105827/2],
    ![29433/8, 320357/8, 2899916/9, 4677452/3],
    ![5468/3, 41083/2, 835779/4, 8375991/8],
    ![36739/32, 418951/32, 1209338/9, 6295081/9],
    ![86206/121, 974634/121, 4410032/49, 22168380/49],
    ![86206/121, 974634/121, 4410032/49, 22168380/49],
    ![86206/121, 974634/121, 4410032/49, 10543312/25],
    ![63754/121, 462916/63, 68816, 10543312/25],
    ![63754/121, 788320/121, 13756184/225, 11091808/45],
    ![661132/1323, 2348296/441, 31694888/675, 10738729/49],
    ![481736/1323, 2348296/441, 31694888/675, 10738729/49],
    ![1835316/5329, 2348296/441, 31694888/675, 10738729/49]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 4 1 514639 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 7618, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1544⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free3_0
    · exact Research6970.Height2308.MainFree.free10_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free33_1
    · exact Research6970.Height2308.MainFree.free42_1
    · exact Research6970.Height2308.MainFree.free52_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free83_0
    · exact Research6970.Height2308.MainFree.free83_1
    · exact Research6970.Height2308.MainFree.free123_0
    · exact Research6970.Height2308.MainFree.free198_0
    · exact Research6970.Height2308.MainFree.free158_0
    · exact Research6970.Height2308.MainFree.free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨3244556750581/5909222785024, 10474089852906370864239/11686668040536787517440, [352338744,352338730,352338734,352338733,352338736,149881516,149881516,149881515,149881516,109976905,108615557,139901201,242562180], [980348,980348,980348,980348,980348,2567528,2567528,2567528,2567528,3576981,3624215,2770682,1508575], ![128756856387600,1597355980620,218305962000,3696699300], 198097594579239747⟩

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
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases2
end Pack_R6970Height2313MainPlans06

section Pack_R6970Height2313MainPlans07

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases3
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HigherHelperCases3.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree3_0, Research6970.Height2308.MainFree.bankfree10_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree33_1, Research6970.Height2308.MainFree.bankfree42_1, Research6970.Height2308.MainFree.bankfree52_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree83_0, Research6970.Height2308.MainFree.bankfree83_1, Research6970.Height2308.MainFree.bankfree123_0, Research6970.Height2308.MainFree.bankfree198_0, Research6970.Height2308.MainFree.bankfree158_0, Research6970.Height2308.MainFree.bankfree171_0] i
    head := Research6970.Height2308.MainHeads.src1545
    historyValues := [![15077, 170440, 791103, 3908528],
    ![24861/2, 271885/2, 2480791/4, 12078605/4],
    ![29433/8, 637145/16, 2883814/9, 4626490/3],
    ![5468/3, 122585/6, 831297/4, 16569465/16],
    ![36739/32, 208355/16, 1209338/9, 6295081/9],
    ![86206/121, 969405/121, 4386460/49, 21926850/49],
    ![86206/121, 969405/121, 4386460/49, 21926850/49],
    ![86206/121, 969405/121, 4386460/49, 2085688/5],
    ![63754/121, 3225970/441, 68816, 2085688/5],
    ![63754/121, 783340/121, 2733508/45, 2194192/9],
    ![661132/1323, 47650/9, 31514944/675, 10738729/49],
    ![481736/1323, 47650/9, 31514944/675, 10738729/49],
    ![1835316/5329, 47650/9, 31514944/675, 10738729/49]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 4 2 514639 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 7535, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1545⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free3_0
    · exact Research6970.Height2308.MainFree.free10_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free33_1
    · exact Research6970.Height2308.MainFree.free42_1
    · exact Research6970.Height2308.MainFree.free52_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free83_0
    · exact Research6970.Height2308.MainFree.free83_1
    · exact Research6970.Height2308.MainFree.free123_0
    · exact Research6970.Height2308.MainFree.free198_0
    · exact Research6970.Height2308.MainFree.free158_0
    · exact Research6970.Height2308.MainFree.free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨6561663601457647/11919217049731072, 42722811373091949581929505/47076488809242879743492096, [350697585,350697573,350697576,350697575,350697574,149242601,149242599,149242597,149242602,109163998,107701110,139455482,242222126], [984844,984844,984844,984844,984844,2578145,2578145,2578145,2578145,3605186,3655943,2780449,1511369], ![128576348923320,1597722354364,217999913400,3729061860], 196982722869994981⟩

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
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases3

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases4
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HigherHelperCases4.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree3_0, Research6970.Height2308.MainFree.bankfree10_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree33_1, Research6970.Height2308.MainFree.bankfree42_1, Research6970.Height2308.MainFree.bankfree52_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree93_0, Research6970.Height2308.MainFree.bankfree83_1, Research6970.Height2308.MainFree.bankfree139_0, Research6970.Height2308.MainFree.bankfree158_0, Research6970.Height2308.MainFree.bankfree198_0, Research6970.Height2308.MainFree.bankfree171_0] i
    head := Research6970.Height2308.MainHeads.src1546
    historyValues := [![15150, 170170, 788959, 3840908],
    ![24861/2, 268933/2, 2453731/4, 11815713/4],
    ![29433/8, 630093/16, 950666/3, 1508598],
    ![5468/3, 121273/6, 822441/4, 16208829/16],
    ![36739/32, 206141/16, 1209338/9, 6295081/9],
    ![86206/121, 959073/121, 4339884/49, 3064230/7],
    ![86206/121, 959073/121, 4339884/49, 3064230/7],
    ![86206/121, 959073/121, 4339884/49, 350464],
    ![63754/121, 3197434/441, 68816, 350464],
    ![63754/121, 939331/150, 8436640/147, 5987809/25],
    ![481736/1323, 939331/150, 8436640/147, 5987809/25],
    ![481736/1323, 2308282/441, 10386464/225, 5367726/25],
    ![1835316/5329, 2308282/441, 10386464/225, 5367726/25]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 4 4 514639 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 7371, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1546⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free3_0
    · exact Research6970.Height2308.MainFree.free10_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free33_1
    · exact Research6970.Height2308.MainFree.free42_1
    · exact Research6970.Height2308.MainFree.free52_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free93_0
    · exact Research6970.Height2308.MainFree.free83_1
    · exact Research6970.Height2308.MainFree.free139_0
    · exact Research6970.Height2308.MainFree.free158_0
    · exact Research6970.Height2308.MainFree.free198_0
    · exact Research6970.Height2308.MainFree.free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨6565068090175447/11900335509471232, 43146682960325928363169221/46927456776550193096032256, [348236020,348235996,348235997,348235997,348235998,148462587,148462585,95114114,116412927,107815064,106989428,138574785,241550213], [991586,991587,991587,991587,991587,2591107,2591107,4158724,3362050,3651990,3680636,2799748,1516891], ![128219684064660,1598446980112,217395191700,3754248720], 195295376443709794⟩

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
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases4

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases5
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HigherHelperCases5.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree3_0, Research6970.Height2308.MainFree.bankfree10_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree36_0, Research6970.Height2308.MainFree.bankfree42_1, Research6970.Height2308.MainFree.bankfree52_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree93_0, Research6970.Height2308.MainFree.bankfree83_1, Research6970.Height2308.MainFree.bankfree139_0, Research6970.Height2308.MainFree.bankfree158_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree171_0] i
    head := Research6970.Height2308.MainHeads.src1547
    historyValues := [![15194, 168801, 781598, 3755737],
    ![24861/2, 261679/2, 596809, 2792426],
    ![29433/8, 153191/4, 2773816/9, 4278352/3],
    ![5710/3, 350065/18, 793009/4, 1802099/2],
    ![36739/32, 401401/32, 1209338/9, 17482712/25],
    ![86206/121, 933684/121, 4225432/49, 20276880/49],
    ![86206/121, 933684/121, 4225432/49, 20276880/49],
    ![86206/121, 933684/121, 4225432/49, 41250560/121],
    ![63754/121, 3127312/441, 68816, 41250560/121],
    ![63754/121, 455359/75, 8181944/147, 34101392/147],
    ![481736/1323, 455359/75, 8181944/147, 34101392/147],
    ![481736/1323, 961568/189, 30252416/675, 129660544/675],
    ![1835316/5329, 961568/189, 30252416/675, 129660544/675]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 4 9 514639 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6968, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1547⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free3_0
    · exact Research6970.Height2308.MainFree.free10_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free36_0
    · exact Research6970.Height2308.MainFree.free42_1
    · exact Research6970.Height2308.MainFree.free52_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free93_0
    · exact Research6970.Height2308.MainFree.free83_1
    · exact Research6970.Height2308.MainFree.free139_0
    · exact Research6970.Height2308.MainFree.free158_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨156063788637254600086823191/284231620810146195701760000, 13339157/14361900, [340361654,340361641,340361646,340361645,340361644,145358624,145358625,83927935,116145602,105358784,104683599,136358308,239859680], [1013156,1013156,1013156,1013156,1013156,2651090,2651090,4746299,3369519,3737214,3760640,2848319,1530783], ![127322315337600,1600269421180,215873712000,3835852800], 190027214322089938⟩

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
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases5

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases6
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HigherHelperCases6.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree3_0, Research6970.Height2308.MainFree.bankfree10_0, Research6970.Height2308.MainFree.bankfree19_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree50_0, Research6970.Height2308.MainFree.bankfree63_0, Research6970.Height2308.MainFree.bankfree108_0, Research6970.Height2308.MainFree.bankfree83_1, Research6970.Height2308.MainFree.bankfree167_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree171_0] i
    head := Research6970.Height2308.MainHeads.src1548
    historyValues := [![15594, 166557, 771329, 3587766],
    ![24861/2, 252013/2, 2298631/4, 10308893/4],
    ![6218, 545701/9, 2298631/4, 10308893/4],
    ![29433/8, 589673/16, 2669638/9, 3948634/3],
    ![17323/9, 75089/4, 3039349/16, 6578913/8],
    ![81850/81, 89170/9, 3622111/36, 5254127/12],
    ![81850/81, 89170/9, 3622111/36, 5254127/12],
    ![77032/121, 712464/121, 470085/8, 15093225/64],
    ![63754/121, 712464/121, 470085/8, 15093225/64],
    ![505124/1323, 712464/121, 470085/8, 15093225/64],
    ![505124/1323, 6456032/1323, 5303280/121, 21641104/121],
    ![1835316/5329, 6456032/1323, 5303280/121, 21641104/121]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 4 16 514639 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6431, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1548⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free3_0
    · exact Research6970.Height2308.MainFree.free10_0
    · exact Research6970.Height2308.MainFree.free19_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free37_0
    · exact Research6970.Height2308.MainFree.free50_0
    · exact Research6970.Height2308.MainFree.free63_0
    · exact Research6970.Height2308.MainFree.free108_0
    · exact Research6970.Height2308.MainFree.free83_1
    · exact Research6970.Height2308.MainFree.free167_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨47614831336743796447233943/87648563662375727153545216, 518233/560968, [331678258,331678245,331678245,331678248,331678249,167341101,167341090,155408013,101534448,100222282,137294813,238286533], [1036941,1036941,1036941,1036941,1036941,2277389,2277389,2475690,3887892,3943243,2827797,1543710], ![126487257447060,1601965116572,214457879700,4022107860], 184400085680053845⟩

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
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases6

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuarticIntervals0
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuarticIntervals0.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree30_0, Research6970.Height2308.MainFree.bankfree40_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree68_0, Research6970.Height2308.MainFree.bankfree90_0, Research6970.Height2308.MainFree.bankfree84_0, Research6970.Height2308.MainFree.bankfree127_0, Research6970.Height2308.MainFree.bankfree152_0, Research6970.Height2308.MainFree.bankfree168_0, Research6970.Height2308.MainFree.bankfree125_0, Research6970.Height2308.MainFree.bankfree188_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree177_0, Research6970.Height2308.MainFree.bankfree173_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1549
    historyValues := [![15674, 161869, 746287, 3351664],
    ![25417/2, 476079/4, 540456, 2414916],
    ![54680/9, 518930/9, 540456, 2414916],
    ![29433/8, 559401/16, 844354/3, 1172126],
    ![63824/25, 602199/25, 409431/2, 3837681/4],
    ![72196/49, 682121/49, 3076543/25, 4959529/9],
    ![89110/121, 843495/121, 546246/7, 2267892/7],
    ![89110/121, 843495/121, 546246/7, 2267892/7],
    ![254956/361, 2329576/361, 3073290/49, 13579225/49],
    ![127905/242, 2329576/361, 3073290/49, 13579225/49],
    ![127905/242, 676595/121, 2947793/49, 204304],
    ![127905/242, 8345472/1681, 334662/7, 36715797/196],
    ![127905/242, 8345472/1681, 334662/7, 8609590/49],
    ![677069/1681, 8345472/1681, 334662/7, 8609590/49],
    ![977501/2738, 8345472/1681, 334662/7, 8609590/49],
    ![977501/2738, 6110713/1369, 6947158/169, 144828194/867],
    ![469910/1369, 6110713/1369, 6947158/169, 144828194/867],
    ![927871/2738, 6110713/1369, 6947158/169, 144828194/867],
    ![459746/1369, 6110713/1369, 6947158/169, 144828194/867]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 4 26 514639 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5727, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1549⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free30_0
    · exact Research6970.Height2308.MainFree.free40_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free68_0
    · exact Research6970.Height2308.MainFree.free90_0
    · exact Research6970.Height2308.MainFree.free84_0
    · exact Research6970.Height2308.MainFree.free127_0
    · exact Research6970.Height2308.MainFree.free152_0
    · exact Research6970.Height2308.MainFree.free168_0
    · exact Research6970.Height2308.MainFree.free125_0
    · exact Research6970.Height2308.MainFree.free188_0
    · exact Research6970.Height2308.MainFree.free212_0
    · exact Research6970.Height2308.MainFree.free177_0
    · exact Research6970.Height2308.MainFree.free173_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨1136362463800057277671869355/2105943824869563373279248384, 1629787/1741341, [314078926,314078917,314078914,314078917,314078917,314078919,149310401,149310401,149399283,149399262,78519725,93450520,60294637,93960261,93468242,99328950,120844256,185771233,229918506], [1117725,1117725,1117725,1117725,1117725,1117725,2577018,2577018,2575541,2575542,5085508,4239152,6681631,4213460,4238258,3980927,3238240,2041038,1612475], ![122045341354920,1610986353204,221067767270,5043527020], 169825141962550026⟩

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
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 18 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuarticIntervals0

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuarticIntervals1
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuarticIntervals1.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree35_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree53_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree61_0, Research6970.Height2308.MainFree.bankfree69_0, Research6970.Height2308.MainFree.bankfree72_0, Research6970.Height2308.MainFree.bankfree95_0, Research6970.Height2308.MainFree.bankfree115_0, Research6970.Height2308.MainFree.bankfree92_0, Research6970.Height2308.MainFree.bankfree140_0, Research6970.Height2308.MainFree.bankfree130_0, Research6970.Height2308.MainFree.bankfree164_0, Research6970.Height2308.MainFree.bankfree212_0, Research6970.Height2308.MainFree.bankfree186_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1550
    historyValues := [![15582, 160993, 741359, 3387620],
    ![25417/2, 116661, 529746, 2414916],
    ![54680/9, 508730/9, 529746, 2332440],
    ![29433/8, 137109/4, 827864/3, 1119936],
    ![5710/3, 312665/18, 708485/4, 707598],
    ![18775/16, 356265/32, 3220596/25, 13247712/25],
    ![86978/121, 839638/121, 3782108/49, 8288641/25],
    ![73648/121, 839638/121, 3782108/49, 8288641/25],
    ![73648/121, 820652/121, 527368/7, 13909824/49],
    ![73648/121, 820652/121, 70756, 13909824/49],
    ![73648/121, 820652/121, 70756, 13909824/49],
    ![73648/121, 820652/121, 70756, 9740641/36],
    ![73648/121, 2463520/441, 56704, 9696384/49],
    ![73648/121, 2463520/441, 56704, 9696384/49],
    ![73648/121, 2463520/441, 56704, 9696384/49],
    ![1374849/3362, 2463520/441, 56704, 9696384/49],
    ![1374849/3362, 8179216/1681, 328022/7, 8440560/49],
    ![1374849/3362, 5982193/1369, 6947158/169, 117462244/729],
    ![967337/2738, 5982193/1369, 6947158/169, 117462244/729],
    ![930251/2738, 5982193/1369, 6947158/169, 117462244/729],
    ![459746/1369, 5982193/1369, 6947158/169, 117462244/729]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 4 30 514639 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5472, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1550⟩⟩
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
  ⟨835342815279747879980489855/1558667344867035731421298688, 4861505/5189527, [308213520,308213512,308213509,308213509,308213513,308213509,308213510,308213514,163955773,163955773,163955773,163955752,61878332,81498679,79388189,81728827,91931691,91608080,114965399,185678411,229610209], [1147715,1147715,1147715,1147715,1147715,1147715,1147715,1147715,2333645,2333645,2333645,2333646,6500929,4890473,5025560,4876814,4315702,4332013,3403899,2042157,1615008], ![121881691141380,1611318472916,220957309090,5155095470], 166823640164196181⟩

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
    · exact Pricing.height_from_critical Band.near _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuarticIntervals1

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuarticIntervals2
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuarticIntervals2.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree31_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree69_0, Research6970.Height2308.MainFree.bankfree82_0, Research6970.Height2308.MainFree.bankfree104_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree114_0, Research6970.Height2308.MainFree.bankfree168_0, Research6970.Height2308.MainFree.bankfree131_0, Research6970.Height2308.MainFree.bankfree161_0, Research6970.Height2308.MainFree.bankfree214_0, Research6970.Height2308.MainFree.bankfree190_0, Research6970.Height2308.MainFree.bankfree179_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1551
    historyValues := [![15935, 159051, 733992, 3288918],
    ![25417/2, 228919/2, 522144, 2414916],
    ![54680/9, 499210/9, 522144, 4461985/2],
    ![29433/8, 269101/8, 2437420/9, 3213676/3],
    ![64334/25, 574268/25, 204686, 3728761/4],
    ![17323/9, 34153/2, 1383815/8, 2677191/4],
    ![18775/16, 43715/4, 632362/5, 12671514/25],
    ![89110/121, 811450/121, 525540/7, 7683984/25],
    ![89110/121, 811450/121, 525540/7, 7683984/25],
    ![221468/361, 811450/121, 70756, 7683984/25],
    ![221468/361, 811450/121, 70756, 7683984/25],
    ![221468/361, 2236852/361, 445764/7, 11404129/49],
    ![221468/361, 652172/121, 2859543/49, 9326988/49],
    ![221468/361, 1288021/242, 2774535/49, 9326988/49],
    ![221468/361, 1288021/242, 2774535/49, 168100],
    ![689574/1681, 1288021/242, 2774535/49, 168100],
    ![689574/1681, 7997008/1681, 2245755/49, 168100],
    ![689574/1681, 11703713/2738, 105391216/2601, 110796676/729],
    ![983773/2738, 11703713/2738, 105391216/2601, 110796676/729],
    ![945497/2738, 11703713/2738, 105391216/2601, 110796676/729],
    ![930251/2738, 11703713/2738, 105391216/2601, 110796676/729],
    ![459746/1369, 11703713/2738, 105391216/2601, 110796676/729]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 4 34 514639 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5234, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1551⟩⟩
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
    · exact Research6970.Height2308.MainFree.free69_0
    · exact Research6970.Height2308.MainFree.free82_0
    · exact Research6970.Height2308.MainFree.free104_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free114_0
    · exact Research6970.Height2308.MainFree.free168_0
    · exact Research6970.Height2308.MainFree.free131_0
    · exact Research6970.Height2308.MainFree.free161_0
    · exact Research6970.Height2308.MainFree.free214_0
    · exact Research6970.Height2308.MainFree.free190_0
    · exact Research6970.Height2308.MainFree.free179_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨2856661624375231611400464809/5347453651637172762446921728, 33719951/35965706, [303931132,303931123,303931121,303931123,303931122,303931125,303931121,131327241,131327240,131327241,131327241,131327244,71951626,101310369,64357273,59908386,89616507,88686852,92891111,112789108,184577560,228768403], [1169612,1169612,1169612,1169612,1169612,1169612,1169612,2958567,2958567,2958567,2958567,2958567,5568137,3897344,6246972,6726067,4432390,4479246,4267347,3479408,2055425,1621926], ![121434843680460,1612226194772,219647296400,5330302740], 163501961294318886⟩

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
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 18 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuarticIntervals2

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuarticIntervals3
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuarticIntervals3.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree35_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree53_0, Research6970.Height2308.MainFree.bankfree42_2, Research6970.Height2308.MainFree.bankfree61_0, Research6970.Height2308.MainFree.bankfree69_0, Research6970.Height2308.MainFree.bankfree72_0, Research6970.Height2308.MainFree.bankfree95_0, Research6970.Height2308.MainFree.bankfree113_0, Research6970.Height2308.MainFree.bankfree138_0, Research6970.Height2308.MainFree.bankfree144_0, Research6970.Height2308.MainFree.bankfree131_0, Research6970.Height2308.MainFree.bankfree164_0, Research6970.Height2308.MainFree.bankfree214_0, Research6970.Height2308.MainFree.bankfree186_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1552
    historyValues := [![15843, 159040, 732308, 3305512],
    ![25417/2, 449661/4, 522144, 2414916],
    ![54680/9, 490370/9, 522144, 8547165/4],
    ![29433/8, 528699/16, 798182/3, 1025994],
    ![5710/3, 150595/9, 1365103/8, 10371897/16],
    ![18775/16, 687285/64, 3107223/25, 12136473/25],
    ![86978/121, 810262/121, 3651293/49, 8288641/25],
    ![73648/121, 810262/121, 3651293/49, 8288641/25],
    ![73648/121, 788063/121, 3546532/49, 12743046/49],
    ![73648/121, 788063/121, 70756, 12743046/49],
    ![73648/121, 788063/121, 70756, 12743046/49],
    ![73648/121, 788063/121, 70756, 31291146/121],
    ![73648/121, 1263567/242, 2717328/49, 18753633/98],
    ![73648/121, 1263567/242, 2717328/49, 18753633/98],
    ![73648/121, 155639/30, 6284096/121, 17791137/100],
    ![689574/1681, 155639/30, 6284096/121, 17791137/100],
    ![689574/1681, 7845064/1681, 2203436/49, 1522756/9],
    ![689574/1681, 22947967/5476, 103342988/2601, 184683933/1250],
    ![967337/2738, 22947967/5476, 103342988/2601, 184683933/1250],
    ![930251/2738, 22947967/5476, 103342988/2601, 184683933/1250],
    ![459746/1369, 22947967/5476, 103342988/2601, 184683933/1250]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 4 38 514639 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5013, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1552⟩⟩
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
    · exact Research6970.Height2308.MainFree.free113_0
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
  ⟨2825796705721880581152235903/5322944509191549332016332800, 16839877/17941595, [299655399,299655385,299655389,299655389,299655389,299655390,299655390,299655389,161065100,161065111,161065111,161065104,82042913,82042913,71900299,71900308,91595604,91595604,112573878,183286890,227784132], [1191474,1191474,1191474,1191474,1191474,1191474,1191474,1191474,2381682,2381682,2381682,2381682,4858173,4858173,5572214,5572214,4332641,4332641,3486876,2070981,1630014], ![120912372948240,1613287120968,218111399100,5155842790], 161406519219114950⟩

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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuarticIntervals3

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuarticIntervals4
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuarticIntervals4.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree31_0, Research6970.Height2308.MainFree.bankfree39_0, Research6970.Height2308.MainFree.bankfree46_0, Research6970.Height2308.MainFree.bankfree55_0, Research6970.Height2308.MainFree.bankfree53_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree82_0, Research6970.Height2308.MainFree.bankfree87_1, Research6970.Height2308.MainFree.bankfree105_0, Research6970.Height2308.MainFree.bankfree137_0, Research6970.Height2308.MainFree.bankfree144_0, Research6970.Height2308.MainFree.bankfree131_0, Research6970.Height2308.MainFree.bankfree164_0, Research6970.Height2308.MainFree.bankfree214_0, Research6970.Height2308.MainFree.bankfree186_0, Research6970.Height2308.MainFree.bankfree175_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1553
    historyValues := [![16058, 157174, 723342, 3145470],
    ![25417/2, 444037/4, 522144, 2414916],
    ![54680/9, 53810, 522144, 8288005/4],
    ![29433/8, 522163/16, 2365058/9, 2984654/3],
    ![64334/25, 556737/25, 204686, 3728761/4],
    ![11819/6, 49256/3, 2668893/16, 4836695/8],
    ![2483/2, 166407/16, 3015986/25, 10971277/25],
    ![22791/25, 739807/100, 182091/2, 986783/3],
    ![86978/121, 800534/121, 3607973/49, 986783/3],
    ![86978/121, 800534/121, 3607973/49, 986783/3],
    ![86978/121, 800534/121, 3607973/49, 7252612/25],
    ![27491/49, 281261/49, 1882881/32, 2474329/9],
    ![27491/49, 281261/49, 1882881/32, 1346497/6],
    ![27491/49, 628300/121, 5507595/98, 8662302/49],
    ![27491/49, 153359/30, 2580303/50, 17251689/100],
    ![689574/1681, 153359/30, 2580303/50, 17251689/100],
    ![689574/1681, 7734408/1681, 2172732/49, 119969480/729],
    ![689574/1681, 22631959/5476, 11326028/289, 179084101/1250],
    ![967337/2738, 22631959/5476, 11326028/289, 179084101/1250],
    ![466774/1369, 22631959/5476, 11326028/289, 179084101/1250],
    ![459746/1369, 22631959/5476, 11326028/289, 179084101/1250]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 4 41 514639 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 4861, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1553⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free31_0
    · exact Research6970.Height2308.MainFree.free39_0
    · exact Research6970.Height2308.MainFree.free46_0
    · exact Research6970.Height2308.MainFree.free55_0
    · exact Research6970.Height2308.MainFree.free53_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free82_0
    · exact Research6970.Height2308.MainFree.free87_1
    · exact Research6970.Height2308.MainFree.free105_0
    · exact Research6970.Height2308.MainFree.free137_0
    · exact Research6970.Height2308.MainFree.free144_0
    · exact Research6970.Height2308.MainFree.free131_0
    · exact Research6970.Height2308.MainFree.free164_0
    · exact Research6970.Height2308.MainFree.free214_0
    · exact Research6970.Height2308.MainFree.free186_0
    · exact Research6970.Height2308.MainFree.free175_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨1377858263674740128527610885/2596700016082100126234968064, 8317781/8860964, [295644826,295644815,295644813,295644815,295644815,295644816,295644815,220000000,147345394,147345394,147345394,147345394,147345394,94698391,67626407,75779345,86987111,86987111,104201858,182818634,227107168], [1211981,1211981,1211981,1211981,1211981,1211981,1211981,1693981,2609672,2609672,2609672,2609672,2609672,4176260,5936589,5274670,4564914,4564914,3777355,2076624,1635577], ![120553026917760,1614016922852,217554174460,5432247660], 158458841164242643⟩

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
    · exact Pricing.height_from_critical Band.near _ 5 _
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
    · exact Pricing.height_from_critical Band.near _ 16 _
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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuarticIntervals4

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuarticIntervals5
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuarticIntervals5.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree31_0, Research6970.Height2308.MainFree.bankfree43_0, Research6970.Height2308.MainFree.bankfree50_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree61_0, Research6970.Height2308.MainFree.bankfree70_0, Research6970.Height2308.MainFree.bankfree85_0, Research6970.Height2308.MainFree.bankfree76_0, Research6970.Height2308.MainFree.bankfree113_0, Research6970.Height2308.MainFree.bankfree140_0, Research6970.Height2308.MainFree.bankfree165_0, Research6970.Height2308.MainFree.bankfree126_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree216_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1554
    historyValues := [![16029, 156378, 720958, 3105011],
    ![25417/2, 437155/4, 522144, 2414916],
    ![54680/9, 158950/3, 522144, 7970875/4],
    ![29433/8, 514165/16, 2328974/9, 2870450/3],
    ![64334/25, 109599/5, 204686, 3728761/4],
    ![73988/49, 619820/49, 1054568/9, 4669921/9],
    ![81850/81, 232390/27, 3149747/36, 6007401/16],
    ![89110/121, 70465/11, 502062/7, 7683984/25],
    ![89110/121, 764065/121, 3439724/49, 6461764/25],
    ![89110/121, 764065/121, 3439724/49, 6461764/25],
    ![89110/121, 764065/121, 3439724/49, 6461764/25],
    ![230860/361, 2256070/361, 66312, 6461764/25],
    ![230860/361, 1225035/242, 2631476/49, 17489175/98],
    ![230860/361, 1225035/242, 2631476/49, 17489175/98],
    ![990104/1681, 7612940/1681, 9959408/225, 115248100/729],
    ![1358449/3362, 7612940/1681, 9959408/225, 115248100/729],
    ![1358449/3362, 617440/147, 21213120/529, 21748100/147],
    ![1358449/3362, 11137805/2738, 100027886/2601, 107308881/784],
    ![479479/1369, 11137805/2738, 100027886/2601, 107308881/784],
    ![930251/2738, 11137805/2738, 100027886/2601, 107308881/784],
    ![459746/1369, 11137805/2738, 100027886/2601, 107308881/784]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 4 45 514639 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 4675, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1554⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free31_0
    · exact Research6970.Height2308.MainFree.free43_0
    · exact Research6970.Height2308.MainFree.free50_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free61_0
    · exact Research6970.Height2308.MainFree.free70_0
    · exact Research6970.Height2308.MainFree.free85_0
    · exact Research6970.Height2308.MainFree.free76_0
    · exact Research6970.Height2308.MainFree.free113_0
    · exact Research6970.Height2308.MainFree.free140_0
    · exact Research6970.Height2308.MainFree.free165_0
    · exact Research6970.Height2308.MainFree.free126_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free216_0
    · exact Research6970.Height2308.MainFree.free183_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨1559965743957101419351786517/2961289049265720357027840000, 9516037/10138500, [291637991,291637980,291637981,291637984,291637980,291637982,291637981,291637984,160263664,160263664,160263654,160263656,85867206,80131834,56630436,78092084,90570467,90570467,110127163,181252771,226233820], [1232469,1232469,1232469,1232469,1232469,1232469,1232469,1232469,2395000,2395000,2395000,2395000,4631205,4974228,7126445,5115027,4384309,4384309,3571768,2095497,1642754], ![120089436332400,1614958543160,215690797490,5217327710], 156033384922717541⟩

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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuarticIntervals5

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuarticIntervals6
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuarticIntervals6.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree35_0, Research6970.Height2308.MainFree.bankfree44_0, Research6970.Height2308.MainFree.bankfree51_0, Research6970.Height2308.MainFree.bankfree47_0, Research6970.Height2308.MainFree.bankfree56_0, Research6970.Height2308.MainFree.bankfree67_0, Research6970.Height2308.MainFree.bankfree72_0, Research6970.Height2308.MainFree.bankfree97_0, Research6970.Height2308.MainFree.bankfree116_1, Research6970.Height2308.MainFree.bankfree140_0, Research6970.Height2308.MainFree.bankfree161_0, Research6970.Height2308.MainFree.bankfree128_0, Research6970.Height2308.MainFree.bankfree206_0, Research6970.Height2308.MainFree.bankfree214_0, Research6970.Height2308.MainFree.bankfree186_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1555
    historyValues := [![15974, 156424, 719499, 3138201],
    ![25417/2, 431013/4, 522144, 2414916],
    ![54680/9, 470210/9, 522144, 7687845/4],
    ![29433/8, 507027/16, 765590/3, 922842],
    ![5710/3, 144295/9, 1308151/8, 9329121/16],
    ![18775/16, 659565/64, 596547/5, 10916289/25],
    ![20312/25, 746621/100, 3395365/36, 1416327/4],
    ![80398/121, 76251/11, 3791244/49, 1416327/4],
    ![80398/121, 753121/121, 485783/7, 270400],
    ![80398/121, 753121/121, 485783/7, 270400],
    ![80398/121, 753121/121, 485783/7, 270400],
    ![80398/121, 1006031/162, 4520875/72, 10837264/49],
    ![80398/121, 1203489/242, 2602101/49, 16543521/98],
    ![80398/121, 1203489/242, 2602101/49, 16543521/98],
    ![965824/1681, 7480808/1681, 396896/9, 4195040/27],
    ![33263/82, 7480808/1681, 396896/9, 4195040/27],
    ![33263/82, 1823120/441, 73886562/1849, 1916325/14],
    ![33263/82, 21900151/5476, 27872848/729, 1916325/14],
    ![967337/2738, 21900151/5476, 27872848/729, 1916325/14],
    ![930251/2738, 21900151/5476, 27872848/729, 1916325/14],
    ![459746/1369, 21900151/5476, 27872848/729, 1916325/14]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 4 49 514639 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 4509, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1555⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free35_0
    · exact Research6970.Height2308.MainFree.free44_0
    · exact Research6970.Height2308.MainFree.free51_0
    · exact Research6970.Height2308.MainFree.free47_0
    · exact Research6970.Height2308.MainFree.free56_0
    · exact Research6970.Height2308.MainFree.free67_0
    · exact Research6970.Height2308.MainFree.free72_0
    · exact Research6970.Height2308.MainFree.free97_0
    · exact Research6970.Height2308.MainFree.free116_1
    · exact Research6970.Height2308.MainFree.free140_0
    · exact Research6970.Height2308.MainFree.free161_0
    · exact Research6970.Height2308.MainFree.free128_0
    · exact Research6970.Height2308.MainFree.free206_0
    · exact Research6970.Height2308.MainFree.free214_0
    · exact Research6970.Height2308.MainFree.free186_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨247429154994942617264007475/471890513739498520539561984, 6078613/6475509, [288508844,288508830,288508833,288508838,288508834,288508836,288508836,288508837,159930499,159930509,159930509,159930508,57583779,76092506,55483619,78268318,90777367,90777367,109985324,180698336,225807853], [1248468,1248468,1248468,1248468,1248468,1248468,1248468,1248468,2400536,2400536,2400536,2400536,7004058,5253053,7273670,5102862,4373881,4373881,3576689,2102179,1646255], ![119863324529460,1615418068352,215031019840,5204919240], 154567440282229879⟩

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
    · exact Pricing.height_from_critical Band.near _ 19 _
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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuarticIntervals6

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.QuarticIntervals7
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.QuarticIntervals7.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree19_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree31_0, Research6970.Height2308.MainFree.bankfree43_0, Research6970.Height2308.MainFree.bankfree50_0, Research6970.Height2308.MainFree.bankfree54_0, Research6970.Height2308.MainFree.bankfree61_0, Research6970.Height2308.MainFree.bankfree70_0, Research6970.Height2308.MainFree.bankfree87_0, Research6970.Height2308.MainFree.bankfree95_0, Research6970.Height2308.MainFree.bankfree116_1, Research6970.Height2308.MainFree.bankfree140_0, Research6970.Height2308.MainFree.bankfree165_0, Research6970.Height2308.MainFree.bankfree129_0, Research6970.Height2308.MainFree.bankfree206_0, Research6970.Height2308.MainFree.bankfree214_0, Research6970.Height2308.MainFree.bankfree186_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1556
    historyValues := [![16235, 154978, 714657, 3040387],
    ![25417/2, 106412, 522144, 2414916],
    ![6218, 460954/9, 520931, 1809969],
    ![29433/8, 62599/2, 2268640/9, 2679496/3],
    ![64334/25, 533378/25, 204686, 2679496/3],
    ![73988/49, 603026/49, 1054568/9, 4669921/9],
    ![81850/81, 25130/3, 766522/9, 6007401/16],
    ![89110/121, 754900/121, 489000/7, 7683984/25],
    ![89110/121, 741984/121, 3341448/49, 6461764/25],
    ![89110/121, 741984/121, 3341448/49, 6461764/25],
    ![244020/361, 2113220/361, 445170/7, 15249025/64],
    ![244020/361, 2113220/361, 445170/7, 27240088/121],
    ![244020/361, 1186379/242, 2563966/49, 1495729/9],
    ![244020/361, 1186379/242, 2563966/49, 1495729/9],
    ![990104/1681, 7385288/1681, 9959408/225, 37982569/256],
    ![813/2, 7385288/1681, 9959408/225, 37982569/256],
    ![813/2, 1797020/441, 72839952/1849, 927350/7],
    ![813/2, 5399674/1369, 27872848/729, 927350/7],
    ![967337/2738, 5399674/1369, 27872848/729, 927350/7],
    ![930251/2738, 5399674/1369, 27872848/729, 927350/7],
    ![459746/1369, 5399674/1369, 27872848/729, 927350/7]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 4 53 514639 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 4364, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1556⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free19_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free31_0
    · exact Research6970.Height2308.MainFree.free43_0
    · exact Research6970.Height2308.MainFree.free50_0
    · exact Research6970.Height2308.MainFree.free54_0
    · exact Research6970.Height2308.MainFree.free61_0
    · exact Research6970.Height2308.MainFree.free70_0
    · exact Research6970.Height2308.MainFree.free87_0
    · exact Research6970.Height2308.MainFree.free95_0
    · exact Research6970.Height2308.MainFree.free116_1
    · exact Research6970.Height2308.MainFree.free140_0
    · exact Research6970.Height2308.MainFree.free165_0
    · exact Research6970.Height2308.MainFree.free129_0
    · exact Research6970.Height2308.MainFree.free206_0
    · exact Research6970.Height2308.MainFree.free214_0
    · exact Research6970.Height2308.MainFree.free186_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨1105772415678294011262428851/2116184343916539302785843200, 150838867/160798275, [285637986,285637971,285637971,285637980,285637976,285637977,285637977,285637980,158632433,158632422,158632434,158632428,55719909,73659088,55019727,79369878,92070494,92070494,109753343,180466355,225627068], [1263148,1263148,1263148,1263148,1263148,1263148,1263148,1263148,2422107,2422107,2422107,2422107,7243336,5432502,7337769,5026824,4308706,4308706,3584738,2104975,1647740], ![119767360235760,1615612638112,214754962450,5127360480], 152673261082951935⟩

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
    · exact Pricing.height_from_critical Band.near _ 19 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 20 _
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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.QuarticIntervals7
end Pack_R6970Height2313MainPlans07

section Pack_R6970Height2313MainPlans08

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases10
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HigherHelperCases10.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree3_0, Research6970.Height2308.MainFree.bankfree10_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree50_0, Research6970.Height2308.MainFree.bankfree63_0, Research6970.Height2308.MainFree.bankfree89_0, Research6970.Height2308.MainFree.bankfree123_0, Research6970.Height2308.MainFree.bankfree83_1, Research6970.Height2308.MainFree.bankfree147_0, Research6970.Height2308.MainFree.bankfree158_0, Research6970.Height2308.MainFree.bankfree211_0, Research6970.Height2308.MainFree.bankfree171_0] i
    head := Research6970.Height2308.MainHeads.src1681
    historyValues := [![15642, 167302, 772275, 3602574],
    ![24861/2, 253381/2, 2311171/4, 10430721/4],
    ![29433/8, 592941/16, 894794/3, 1331766],
    ![17323/9, 226559/12, 3056601/16, 6656661/8],
    ![81850/81, 269030/27, 1214185/12, 1772073/4],
    ![81850/81, 269030/27, 1214185/12, 1772073/4],
    ![250848/361, 2472968/361, 11154856/169, 48828528/169],
    ![83994/121, 721660/121, 121485/2, 1052688/5],
    ![63754/121, 721660/121, 121485/2, 1052688/5],
    ![63754/121, 2178579/400, 4893375/98, 1052688/5],
    ![481736/1323, 2178579/400, 4893375/98, 1052688/5],
    ![481736/1323, 25708515/5329, 1086612/25, 4575321/25],
    ![1835316/5329, 25708515/5329, 1086612/25, 4575321/25]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 5 9 643299 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6507, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1681⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free3_0
    · exact Research6970.Height2308.MainFree.free10_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free37_0
    · exact Research6970.Height2308.MainFree.free50_0
    · exact Research6970.Height2308.MainFree.free63_0
    · exact Research6970.Height2308.MainFree.free89_0
    · exact Research6970.Height2308.MainFree.free123_0
    · exact Research6970.Height2308.MainFree.free83_1
    · exact Research6970.Height2308.MainFree.free147_0
    · exact Research6970.Height2308.MainFree.free158_0
    · exact Research6970.Height2308.MainFree.free211_0
    · exact Research6970.Height2308.MainFree.free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨12979755116368435991027911357/23679264161928833068032851968, 70789771/75683146, [333785048,333785037,333785037,333785037,148366608,148366595,148366598,36867133,69380738,97259636,103853873,133637204,237776168], [1031170,1031170,1031170,1031170,2592702,2592702,2592702,11049685,5777689,4068218,3790050,2907948,1547904], ![126216345497760,1602515336992,213998551200,4510159500], 184837419050251676⟩

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
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 29 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases10

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases11
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HigherHelperCases11.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree3_0, Research6970.Height2308.MainFree.bankfree10_0, Research6970.Height2308.MainFree.bankfree19_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree28_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree42_1, Research6970.Height2308.MainFree.bankfree52_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree83_1, Research6970.Height2308.MainFree.bankfree83_0, Research6970.Height2308.MainFree.bankfree123_0, Research6970.Height2308.MainFree.bankfree122_0, Research6970.Height2308.MainFree.bankfree159_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree187_0, Research6970.Height2308.MainFree.bankfree230_0, Research6970.Height2308.MainFree.bankfree172_0, Research6970.Height2308.MainFree.bankfree171_0] i
    head := Research6970.Height2308.MainHeads.src1682
    historyValues := [![14998, 164156, 757388, 3648636],
    ![24861/2, 245191/2, 559024, 2569609],
    ![6218, 530162/9, 559024, 2510067],
    ![29433/8, 35836, 2596112/9, 3715928/3],
    ![62542/25, 620262/25, 412255/2, 4044121/4],
    ![17323/9, 54706/3, 738329/4, 1547799/2],
    ![36739/32, 376669/32, 1209338/9, 15184468/25],
    ![86206/121, 875976/121, 3965288/49, 17611320/49],
    ![86206/121, 875976/121, 3965288/49, 17611320/49],
    ![63754/121, 2967928/441, 3357118/49, 17611320/49],
    ![63754/121, 2967928/441, 3357118/49, 8375968/25],
    ![63754/121, 694360/121, 121485/2, 207025],
    ![82583/200, 694360/121, 121485/2, 207025],
    ![82583/200, 1051841/200, 48872, 37319881/196],
    ![82583/200, 695776/147, 5280738/121, 21115428/121],
    ![1969478/5329, 695776/147, 5280738/121, 21115428/121],
    ![1969478/5329, 703195/153, 1120355/27, 106946405/648],
    ![1876266/5329, 703195/153, 1120355/27, 106946405/648],
    ![1835316/5329, 703195/153, 1120355/27, 106946405/648]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 5 16 643299 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6052, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1682⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free3_0
    · exact Research6970.Height2308.MainFree.free10_0
    · exact Research6970.Height2308.MainFree.free19_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free28_0
    · exact Research6970.Height2308.MainFree.free37_0
    · exact Research6970.Height2308.MainFree.free42_1
    · exact Research6970.Height2308.MainFree.free52_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free83_1
    · exact Research6970.Height2308.MainFree.free83_0
    · exact Research6970.Height2308.MainFree.free123_0
    · exact Research6970.Height2308.MainFree.free122_0
    · exact Research6970.Height2308.MainFree.free159_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free187_0
    · exact Research6970.Height2308.MainFree.free230_0
    · exact Research6970.Height2308.MainFree.free172_0
    · exact Research6970.Height2308.MainFree.free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨62650787648836418574217527/116199715001433268368179200, 354259/378695, [318345768,318345754,318345759,318345754,318345759,318345759,318345759,147449259,147449259,147449259,147449259,71628170,71628170,83839458,89372841,125052696,101015628,128295347,235253826], [1095908,1095908,1095908,1095908,1095908,1095908,1095908,2607946,2607946,2607946,2607946,5593831,5593831,4751550,4444671,3120658,3909777,3030059,1568632], ![124877435917320,1605234802824,212589583200,5305118600], 174999212510599329⟩

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
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases11

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases12
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HigherHelperCases12.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree3_0, Research6970.Height2308.MainFree.bankfree10_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree50_0, Research6970.Height2308.MainFree.bankfree63_0, Research6970.Height2308.MainFree.bankfree89_0, Research6970.Height2308.MainFree.bankfree123_0, Research6970.Height2308.MainFree.bankfree83_1, Research6970.Height2308.MainFree.bankfree147_0, Research6970.Height2308.MainFree.bankfree158_0, Research6970.Height2308.MainFree.bankfree211_0, Research6970.Height2308.MainFree.bankfree171_0] i
    head := Research6970.Height2308.MainHeads.src1760
    historyValues := [![15642, 167506, 773431, 3613182],
    ![24861/2, 254605/2, 2322391/4, 10539725/4],
    ![29433/8, 595865/16, 2697574/9, 4037050/3],
    ![17323/9, 75905/4, 3072037/16, 6726225/8],
    ![81850/81, 90130/9, 3660847/36, 5371775/12],
    ![81850/81, 90130/9, 3660847/36, 5371775/12],
    ![250848/361, 2485480/361, 862376/13, 49338800/169],
    ![83994/121, 725740/121, 121485/2, 1914640/9],
    ![63754/121, 725740/121, 121485/2, 1914640/9],
    ![63754/121, 437987/80, 4918603/98, 1914640/9],
    ![481736/1323, 437987/80, 4918603/98, 1914640/9],
    ![481736/1323, 25844175/5329, 1086612/25, 4575321/25],
    ![1835316/5329, 25844175/5329, 1086612/25, 4575321/25]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 6 1 771959 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6575, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1760⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free3_0
    · exact Research6970.Height2308.MainFree.free10_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free37_0
    · exact Research6970.Height2308.MainFree.free50_0
    · exact Research6970.Height2308.MainFree.free63_0
    · exact Research6970.Height2308.MainFree.free89_0
    · exact Research6970.Height2308.MainFree.free123_0
    · exact Research6970.Height2308.MainFree.free83_1
    · exact Research6970.Height2308.MainFree.free147_0
    · exact Research6970.Height2308.MainFree.free158_0
    · exact Research6970.Height2308.MainFree.free211_0
    · exact Research6970.Height2308.MainFree.free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨13038465661217352995195566523/23750206884513400387836837888, 70877831/75796434, [335168032,335168022,335168023,335168024,148797997,148798002,148797997,37002137,69605103,97624758,103936835,133744479,237859768], [1027382,1027382,1027382,1027382,2585533,2585533,2585533,11008932,5757367,4052816,3786550,2905597,1547217], ![126260722049760,1602425206052,214073791200,4505994500], 185651605562935747⟩

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
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 29 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases12

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases13
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HigherHelperCases13.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree3_0, Research6970.Height2308.MainFree.bankfree10_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree36_0, Research6970.Height2308.MainFree.bankfree42_1, Research6970.Height2308.MainFree.bankfree52_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree93_0, Research6970.Height2308.MainFree.bankfree83_1, Research6970.Height2308.MainFree.bankfree139_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree158_0, Research6970.Height2308.MainFree.bankfree171_0] i
    head := Research6970.Height2308.MainHeads.src1761
    historyValues := [![15194, 167445, 773914, 3684773],
    ![24861/2, 253543/2, 578164, 2611287],
    ![29433/8, 37083, 895376/3, 1333608],
    ![5710/3, 338765/18, 767471/4, 3370401/4],
    ![36739/32, 389197/32, 1209338/9, 16348644/25],
    ![86206/121, 905208/121, 4097064/49, 18961560/49],
    ![86206/121, 905208/121, 4097064/49, 18961560/49],
    ![86206/121, 905208/121, 4097064/49, 38574720/121],
    ![63754/121, 3048664/441, 68816, 38574720/121],
    ![63754/121, 439313/75, 1128040/21, 10629768/49],
    ![695824/1323, 6499552/1323, 5303280/121, 13472192/75],
    ![481736/1323, 6499552/1323, 5303280/121, 13472192/75],
    ![1835316/5329, 6499552/1323, 5303280/121, 13472192/75]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 6 2 771959 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6516, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1761⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free3_0
    · exact Research6970.Height2308.MainFree.free10_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free36_0
    · exact Research6970.Height2308.MainFree.free42_1
    · exact Research6970.Height2308.MainFree.free52_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free93_0
    · exact Research6970.Height2308.MainFree.free83_1
    · exact Research6970.Height2308.MainFree.free139_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free158_0
    · exact Research6970.Height2308.MainFree.free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨346383640315250037466197533/636961060929677186499084288, 3781049/4063059, [331371374,331371360,331371364,331371363,331371363,133659424,138047274,61731567,91366025,96547220,94443752,134443516,238394560], [1037782,1037782,1037782,1037782,1037782,2907461,2811308,6516318,4344212,4098270,4189092,2890279,1542822], ![126544600339200,1601848509080,214555104000,4272873840], 184302456056903272⟩

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
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 18 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases13

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases14
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HigherHelperCases14.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree3_0, Research6970.Height2308.MainFree.bankfree10_0, Research6970.Height2308.MainFree.bankfree19_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree50_0, Research6970.Height2308.MainFree.bankfree63_0, Research6970.Height2308.MainFree.bankfree108_0, Research6970.Height2308.MainFree.bankfree83_1, Research6970.Height2308.MainFree.bankfree167_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree171_0] i
    head := Research6970.Height2308.MainHeads.src1762
    historyValues := [![15594, 166458, 770768, 3581958],
    ![24861/2, 251419/2, 1146593/2, 2569609],
    ![6218, 544348/9, 1146593/2, 2569609],
    ![29433/8, 294127/8, 2663236/9, 3928372/3],
    ![17323/9, 37451/2, 1515929/8, 3272577/4],
    ![81850/81, 29650/3, 1806617/18, 2613583/6],
    ![81850/81, 29650/3, 1806617/18, 2613583/6],
    ![77032/121, 710682/121, 470085/8, 15093225/64],
    ![63754/121, 710682/121, 470085/8, 15093225/64],
    ![505124/1323, 710682/121, 470085/8, 15093225/64],
    ![505124/1323, 6439136/1323, 5303280/121, 21641104/121],
    ![1835316/5329, 6439136/1323, 5303280/121, 21641104/121]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 6 4 771959 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6398, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1762⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free3_0
    · exact Research6970.Height2308.MainFree.free10_0
    · exact Research6970.Height2308.MainFree.free19_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free37_0
    · exact Research6970.Height2308.MainFree.free50_0
    · exact Research6970.Height2308.MainFree.free63_0
    · exact Research6970.Height2308.MainFree.free108_0
    · exact Research6970.Height2308.MainFree.free83_1
    · exact Research6970.Height2308.MainFree.free167_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨6169697408219817238985/11366378433098559782912, 1345/1456, [331008688,331008673,331008675,331008677,331008680,166979883,166979862,155436578,101376928,100127842,137240996,238244593], [1038775,1038775,1038775,1038775,1038775,2283391,2283392,2475215,3894536,3947227,2828976,1544055], ![126464994856260,1602010518512,214420133700,4026171540], 184015403740928453⟩

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
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases14

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases15
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HigherHelperCases15.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree3_0, Research6970.Height2308.MainFree.bankfree10_0, Research6970.Height2308.MainFree.bankfree19_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree28_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree42_1, Research6970.Height2308.MainFree.bankfree52_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree83_1, Research6970.Height2308.MainFree.bankfree83_0, Research6970.Height2308.MainFree.bankfree123_0, Research6970.Height2308.MainFree.bankfree122_0, Research6970.Height2308.MainFree.bankfree159_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree158_0, Research6970.Height2308.MainFree.bankfree230_0, Research6970.Height2308.MainFree.bankfree172_0, Research6970.Height2308.MainFree.bankfree171_0] i
    head := Research6970.Height2308.MainHeads.src1763
    historyValues := [![14998, 164330, 758374, 3658206],
    ![24861/2, 246235/2, 1122833/2, 2569609],
    ![6218, 532540/9, 1122833/2, 5068245/2],
    ![29433/8, 287935/8, 2607364/9, 3751540/3],
    ![62542/25, 124586/5, 412255/2, 4044121/4],
    ![17323/9, 36635/2, 1483241/8, 3125265/4],
    ![36739/32, 378235/32, 1209338/9, 3065998/5],
    ![86206/121, 879630/121, 3981760/49, 17780100/49],
    ![86206/121, 879630/121, 3981760/49, 17780100/49],
    ![63754/121, 2978020/441, 3368457/49, 17780100/49],
    ![63754/121, 2978020/441, 3368457/49, 1691248/5],
    ![63754/121, 63440/11, 121485/2, 207025],
    ![82583/200, 63440/11, 121485/2, 207025],
    ![82583/200, 211389/40, 48872, 18662995/98],
    ![82583/200, 6291680/1323, 5303280/121, 21317790/121],
    ![481736/1323, 6291680/1323, 5303280/121, 21317790/121],
    ![481736/1323, 12011300/2601, 54030935/1296, 215942675/1296],
    ![1876266/5329, 12011300/2601, 54030935/1296, 215942675/1296],
    ![1835316/5329, 12011300/2601, 54030935/1296, 215942675/1296]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 6 9 771959 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6110, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1763⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free3_0
    · exact Research6970.Height2308.MainFree.free10_0
    · exact Research6970.Height2308.MainFree.free19_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free28_0
    · exact Research6970.Height2308.MainFree.free37_0
    · exact Research6970.Height2308.MainFree.free42_1
    · exact Research6970.Height2308.MainFree.free52_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free83_1
    · exact Research6970.Height2308.MainFree.free83_0
    · exact Research6970.Height2308.MainFree.free123_0
    · exact Research6970.Height2308.MainFree.free122_0
    · exact Research6970.Height2308.MainFree.free159_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free158_0
    · exact Research6970.Height2308.MainFree.free230_0
    · exact Research6970.Height2308.MainFree.free172_0
    · exact Research6970.Height2308.MainFree.free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨3494484459707177915734811/6472358812532867139108864, 88688/94797, [319488020,319488009,319488006,319488010,319488010,319488009,319488014,147088921,147088921,147088921,147088921,69987966,69987966,84075331,82772404,125385676,100864919,128620799,235502091], [1090067,1090067,1090067,1090067,1090067,1090067,1090067,2613934,2613934,2613934,2613934,5724123,5724123,4737551,4814879,3111354,3916135,3020966,1566592], ![125009219944620,1604967232284,213155649200,5289301800], 175694852512635945⟩

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
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases15

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases16
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HigherHelperCases16.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree3_0, Research6970.Height2308.MainFree.bankfree10_0, Research6970.Height2308.MainFree.bankfree19_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree33_0, Research6970.Height2308.MainFree.bankfree42_0, Research6970.Height2308.MainFree.bankfree55_0, Research6970.Height2308.MainFree.bankfree72_0, Research6970.Height2308.MainFree.bankfree108_0, Research6970.Height2308.MainFree.bankfree103_1, Research6970.Height2308.MainFree.bankfree124_0, Research6970.Height2308.MainFree.bankfree159_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree187_0, Research6970.Height2308.MainFree.bankfree230_0, Research6970.Height2308.MainFree.bankfree172_0, Research6970.Height2308.MainFree.bankfree171_0] i
    head := Research6970.Height2308.MainHeads.src1764
    historyValues := [![15707, 163477, 756529, 3411284],
    ![24861/2, 239323/2, 1091153/2, 2569609],
    ![6218, 516796/9, 1091153/2, 4749717/2],
    ![29433/8, 279679/8, 2532868/9, 3515764/3],
    ![65616/25, 595808/25, 203904, 891136],
    ![73478/49, 679804/49, 3062926/25, 4752400/9],
    ![22791/25, 398881/50, 182091/2, 370881],
    ![22791/25, 398881/50, 432268/5, 1634773/5],
    ![77032/121, 674394/121, 470085/8, 226995],
    ![77032/121, 674394/121, 470085/8, 226995],
    ![41419/100, 674394/121, 470085/8, 226995],
    ![41419/100, 1023153/200, 48872, 37319881/196],
    ![41419/100, 6095072/1323, 5141373/121, 19978014/121],
    ![1969478/5329, 6095072/1323, 5141373/121, 19978014/121],
    ![1969478/5329, 11634020/2601, 49507774/1225, 809484620/5041],
    ![1876266/5329, 11634020/2601, 49507774/1225, 809484620/5041],
    ![1835316/5329, 11634020/2601, 49507774/1225, 809484620/5041]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 6 16 771959 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5726, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1764⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free3_0
    · exact Research6970.Height2308.MainFree.free10_0
    · exact Research6970.Height2308.MainFree.free19_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free33_0
    · exact Research6970.Height2308.MainFree.free42_0
    · exact Research6970.Height2308.MainFree.free55_0
    · exact Research6970.Height2308.MainFree.free72_0
    · exact Research6970.Height2308.MainFree.free108_0
    · exact Research6970.Height2308.MainFree.free103_1
    · exact Research6970.Height2308.MainFree.free124_0
    · exact Research6970.Height2308.MainFree.free159_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free187_0
    · exact Research6970.Height2308.MainFree.free230_0
    · exact Research6970.Height2308.MainFree.free172_0
    · exact Research6970.Height2308.MainFree.free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨124508116731338597840343073/231872573551758165691858944, 707659/756531, [316961366,316961358,316961357,316961358,316961357,316961356,159978133,159978122,56282923,72387305,72387317,82557496,86579413,121130359,99211360,126491079,233877316], [1102986,1102986,1102986,1102986,1102986,1102986,2399745,2399745,7171058,5533528,5533527,4827633,4588936,3230247,3985888,3080470,1579943], ![124146756879120,1606718449004,210489584400,5491419900], 173615961268630210⟩

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
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 19 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases16

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases7
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HigherHelperCases7.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree3_0, Research6970.Height2308.MainFree.bankfree10_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree50_0, Research6970.Height2308.MainFree.bankfree63_0, Research6970.Height2308.MainFree.bankfree89_0, Research6970.Height2308.MainFree.bankfree123_0, Research6970.Height2308.MainFree.bankfree83_1, Research6970.Height2308.MainFree.bankfree147_0, Research6970.Height2308.MainFree.bankfree198_0, Research6970.Height2308.MainFree.bankfree158_0, Research6970.Height2308.MainFree.bankfree171_0] i
    head := Research6970.Height2308.MainHeads.src1678
    historyValues := [![15642, 168955, 781642, 3688530],
    ![24861/2, 263299/2, 1201043/2, 5656987/2],
    ![29433/8, 308317/8, 2791276/9, 4333612/3],
    ![17323/9, 39321/2, 1590839/8, 3610167/4],
    ![81850/81, 93350/9, 1895387/18, 2883193/6],
    ![81850/81, 93350/9, 1895387/18, 2883193/6],
    ![250848/361, 2574352/361, 11608880/169, 52963232/169],
    ![83994/121, 754720/121, 121485/2, 10276448/45],
    ![63754/121, 754720/121, 121485/2, 10276448/45],
    ![63754/121, 567649/100, 2548898/49, 10276448/45],
    ![661132/1323, 2257576/441, 30480808/675, 46258132/225],
    ![481736/1323, 2257576/441, 30480808/675, 46258132/225],
    ![1835316/5329, 2257576/441, 30480808/675, 46258132/225]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 5 1 643299 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 7058, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1678⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free3_0
    · exact Research6970.Height2308.MainFree.free10_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free37_0
    · exact Research6970.Height2308.MainFree.free50_0
    · exact Research6970.Height2308.MainFree.free63_0
    · exact Research6970.Height2308.MainFree.free89_0
    · exact Research6970.Height2308.MainFree.free123_0
    · exact Research6970.Height2308.MainFree.free83_1
    · exact Research6970.Height2308.MainFree.free147_0
    · exact Research6970.Height2308.MainFree.free198_0
    · exact Research6970.Height2308.MainFree.free158_0
    · exact Research6970.Height2308.MainFree.free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨409061855934607/738460536143872, 2687071996220532643054929/2891233531462290124046336, [344991286,344991274,344991273,344991277,148821767,148821767,148821767,94646905,71199683,95875022,94574267,136893943,240267841], [1000474,1000474,1000474,1000474,2585138,2585138,2585138,4178853,5627869,4126626,4182514,2836581,1527429], ![127538975359620,1599829451624,216241056900,4266164280], 191802716027750924⟩

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
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases7

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases8
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HigherHelperCases8.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree3_0, Research6970.Height2308.MainFree.bankfree10_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree36_0, Research6970.Height2308.MainFree.bankfree42_1, Research6970.Height2308.MainFree.bankfree52_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree93_0, Research6970.Height2308.MainFree.bankfree83_1, Research6970.Height2308.MainFree.bankfree139_0, Research6970.Height2308.MainFree.bankfree198_0, Research6970.Height2308.MainFree.bankfree158_0, Research6970.Height2308.MainFree.bankfree171_0] i
    head := Research6970.Height2308.MainHeads.src1679
    historyValues := [![15194, 168858, 781921, 3758720],
    ![24861/2, 262021/2, 2390371/4, 11200161/4],
    ![29433/8, 613581/16, 925834/3, 1430006],
    ![5710/3, 175270/9, 1588165/8, 14456103/16],
    ![36739/32, 200957/16, 1209338/9, 6295081/9],
    ![86206/121, 934881/121, 604404/7, 20332170/49],
    ![86206/121, 934881/121, 604404/7, 20332170/49],
    ![86206/121, 934881/121, 604404/7, 41363040/121],
    ![63754/121, 3130618/441, 68816, 41363040/121],
    ![63754/121, 912067/150, 8193952/147, 11398126/49],
    ![661132/1323, 2246074/441, 2021792/45, 15264266/75],
    ![481736/1323, 2246074/441, 2021792/45, 15264266/75],
    ![1835316/5329, 2246074/441, 2021792/45, 15264266/75]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 5 2 643299 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6987, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1679⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free3_0
    · exact Research6970.Height2308.MainFree.free10_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free36_0
    · exact Research6970.Height2308.MainFree.free42_1
    · exact Research6970.Height2308.MainFree.free52_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free93_0
    · exact Research6970.Height2308.MainFree.free83_1
    · exact Research6970.Height2308.MainFree.free139_0
    · exact Research6970.Height2308.MainFree.free198_0
    · exact Research6970.Height2308.MainFree.free158_0
    · exact Research6970.Height2308.MainFree.free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨80002513217531430760964185051/145646893849328577908161118208, 106748729/114942681, [340739564,340739553,340739549,340739557,340739557,145513202,145513202,72503796,106925608,100906957,99340597,136512665,239976951], [1012121,1012121,1012121,1012121,1012121,2647703,2647703,5524275,3682850,3914361,3980436,2844937,1529819], ![127384565129820,1600142828664,215979255900,4060044720], 190180267756326115⟩

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
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases8

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases9
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HigherHelperCases9.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree3_0, Research6970.Height2308.MainFree.bankfree10_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree50_0, Research6970.Height2308.MainFree.bankfree63_0, Research6970.Height2308.MainFree.bankfree89_0, Research6970.Height2308.MainFree.bankfree123_0, Research6970.Height2308.MainFree.bankfree83_1, Research6970.Height2308.MainFree.bankfree147_0, Research6970.Height2308.MainFree.bankfree158_0, Research6970.Height2308.MainFree.bankfree211_0, Research6970.Height2308.MainFree.bankfree171_0] i
    head := Research6970.Height2308.MainHeads.src1680
    historyValues := [![15642, 168325, 778072, 3655770],
    ![24861/2, 259519/2, 591859, 2744336],
    ![29433/8, 151901/4, 2750536/9, 4204672/3],
    ![17323/9, 19363, 391751/2, 875688],
    ![81850/81, 30650/3, 933571/9, 1398704/3],
    ![81850/81, 30650/3, 933571/9, 1398704/3],
    ![250848/361, 2535712/361, 879680/13, 51387392/169],
    ![83994/121, 742120/121, 121485/2, 9970688/45],
    ![63754/121, 742120/121, 121485/2, 9970688/45],
    ![63754/121, 1117763/200, 2509943/49, 9970688/45],
    ![481736/1323, 1117763/200, 2509943/49, 9970688/45],
    ![481736/1323, 26388810/5329, 29668625/676, 32042220/169],
    ![1835316/5329, 26388810/5329, 29668625/676, 32042220/169]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 5 4 643299 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6848, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1680⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free3_0
    · exact Research6970.Height2308.MainFree.free10_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free37_0
    · exact Research6970.Height2308.MainFree.free50_0
    · exact Research6970.Height2308.MainFree.free63_0
    · exact Research6970.Height2308.MainFree.free89_0
    · exact Research6970.Height2308.MainFree.free123_0
    · exact Research6970.Height2308.MainFree.free83_1
    · exact Research6970.Height2308.MainFree.free147_0
    · exact Research6970.Height2308.MainFree.free158_0
    · exact Research6970.Height2308.MainFree.free211_0
    · exact Research6970.Height2308.MainFree.free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨1659394225004092215466398553/3004511151444804173036519424, 35615683/38125626, [340720306,340720298,340720294,340720298,149070477,149070477,149070477,40779823,70506343,99090615,103493640,134679741,238577017], [1012173,1012173,1012173,1012173,2581005,2581005,2581005,9969182,5682945,3990981,3805246,2885102,1541323], ![126641452163940,1601651998688,214719315300,4528242740], 189071922795611895⟩

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
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 26 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
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


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases9

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.MarkedExitCandidates0
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.MarkedExitCandidates0.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree3_0, Research6970.Height2308.MainFree.bankfree10_0, Research6970.Height2308.MainFree.bankfree19_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree50_0, Research6970.Height2308.MainFree.bankfree63_0, Research6970.Height2308.MainFree.bankfree108_0, Research6970.Height2308.MainFree.bankfree139_0, Research6970.Height2308.MainFree.bankfree167_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree171_0] i
    head := Research6970.Height2308.MainHeads.src1765
    historyValues := [![16077, 161977, 745746, 3362737],
    ![24861/2, 230287/2, 528990, 2569609],
    ![6218, 496214/9, 528990, 2166654],
    ![29433/8, 134443/4, 2435480/9, 3207536/3],
    ![17323/9, 51187/3, 172835, 668019],
    ![81850/81, 243370/27, 824357/9, 6007401/16],
    ![81850/81, 243370/27, 824357/9, 30393232/81],
    ![77032/121, 647286/121, 2763818/49, 1449660/7],
    ![77032/121, 131149/25, 6186016/121, 4793673/25],
    ![505124/1323, 131149/25, 6186016/121, 4793673/25],
    ![505124/1323, 216224/49, 447888/11, 291624576/1849],
    ![1835316/5329, 216224/49, 447888/11, 291624576/1849]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 6 26 771959 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5224, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1765⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free3_0
    · exact Research6970.Height2308.MainFree.free10_0
    · exact Research6970.Height2308.MainFree.free19_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free37_0
    · exact Research6970.Height2308.MainFree.free50_0
    · exact Research6970.Height2308.MainFree.free63_0
    · exact Research6970.Height2308.MainFree.free108_0
    · exact Research6970.Height2308.MainFree.free139_0
    · exact Research6970.Height2308.MainFree.free167_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨453600920441584414356815477/851952755104195056931176448, 21012373/22558877, [308273222,308273213,308273212,308273216,308273212,147271199,147271196,115564816,91049460,90096752,131623533,233952048], [1147410,1147410,1147410,1147410,1147410,2610905,2610905,3385746,4360168,4408185,2952075,1579329], ![124186426119360,1606637945412,210556843200,4496348700], 169317173336309819⟩

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
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.MarkedExitCandidates0

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.RepricedHelperCases2
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.RepricedHelperCases2.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree6_0, Research6970.Height2308.MainFree.bankfree13_0, Research6970.Height2308.MainFree.bankfree18_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree31_0, Research6970.Height2308.MainFree.bankfree39_0, Research6970.Height2308.MainFree.bankfree46_0, Research6970.Height2308.MainFree.bankfree55_0, Research6970.Height2308.MainFree.bankfree53_0, Research6970.Height2308.MainFree.bankfree74_1, Research6970.Height2308.MainFree.bankfree98_0, Research6970.Height2308.MainFree.bankfree91_0, Research6970.Height2308.MainFree.bankfree138_0, Research6970.Height2308.MainFree.bankfree118_0, Research6970.Height2308.MainFree.bankfree168_0, Research6970.Height2308.MainFree.bankfree131_0, Research6970.Height2308.MainFree.bankfree153_0, Research6970.Height2308.MainFree.bankfree216_0, Research6970.Height2308.MainFree.bankfree183_0, Research6970.Height2308.MainFree.bankfree174_0, Research6970.Height2308.MainFree.bankfree169_0] i
    head := Research6970.Height2308.MainHeads.src1684
    historyValues := [![16206, 156992, 723179, 3096281],
    ![25417/2, 109705, 522144, 2414916],
    ![54680/9, 159550/3, 522144, 2011900],
    ![29433/8, 129025/4, 2337704/9, 2898080/3],
    ![64334/25, 110022/5, 204686, 3728761/4],
    ![11819/6, 16215, 329505/2, 587050],
    ![2483/2, 328725/32, 2979044/25, 2130608/5],
    ![22791/25, 36518/5, 182091/2, 958160/3],
    ![86978/121, 791510/121, 72812, 958160/3],
    ![86978/121, 791510/121, 72812, 33993440/121],
    ![86978/121, 513865/81, 1154837/18, 218089],
    ![259130/441, 2377334/441, 449295/8, 218089],
    ![259130/441, 2377334/441, 449295/8, 3397515/16],
    ![259130/441, 1228021/242, 2659182/49, 8654120/49],
    ![259130/441, 1228021/242, 2659182/49, 159654],
    ![689574/1681, 1228021/242, 2659182/49, 159654],
    ![689574/1681, 7655320/1681, 1099206/25, 159654],
    ![689574/1681, 11185685/2738, 100451876/2601, 17113068/125],
    ![479479/1369, 11185685/2738, 100451876/2601, 17113068/125],
    ![930251/2738, 11185685/2738, 100451876/2601, 17113068/125],
    ![459746/1369, 11185685/2738, 100451876/2601, 17113068/125]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 5 41 643299 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 4720, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1684⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free6_0
    · exact Research6970.Height2308.MainFree.free13_0
    · exact Research6970.Height2308.MainFree.free18_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free31_0
    · exact Research6970.Height2308.MainFree.free39_0
    · exact Research6970.Height2308.MainFree.free46_0
    · exact Research6970.Height2308.MainFree.free55_0
    · exact Research6970.Height2308.MainFree.free53_0
    · exact Research6970.Height2308.MainFree.free74_1
    · exact Research6970.Height2308.MainFree.free98_0
    · exact Research6970.Height2308.MainFree.free91_0
    · exact Research6970.Height2308.MainFree.free138_0
    · exact Research6970.Height2308.MainFree.free118_0
    · exact Research6970.Height2308.MainFree.free168_0
    · exact Research6970.Height2308.MainFree.free131_0
    · exact Research6970.Height2308.MainFree.free153_0
    · exact Research6970.Height2308.MainFree.free216_0
    · exact Research6970.Height2308.MainFree.free183_0
    · exact Research6970.Height2308.MainFree.free174_0
    · exact Research6970.Height2308.MainFree.free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨13769569641326105796418551/26484998522825834688544768, 650369/723181, [293941934,293941920,293941922,293941928,293941924,293941924,293941924,220000000,187124487,187124478,147276174,124749658,90899666,124749658,61759568,57531987,85073073,85190357,110394836,181520445,226437958], [1220688,1220688,1220688,1220688,1220688,1220688,1220688,1693981,2024728,2024728,2610823,3129124,4367717,3129124,6513096,7010707,4678336,4671376,3562481,2092271,1641077], ![120197796865560,1614738747212,216009329550,5567219840], 157739278237434058⟩

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
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 18 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 19 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.RepricedHelperCases2
end Pack_R6970Height2313MainPlans08

section Pack_R6970Height2313MainPlans09

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases17
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HigherHelperCases17.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree3_0, Research6970.Height2308.MainFree.bankfree10_0, Research6970.Height2308.MainFree.bankfree19_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree28_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree42_1, Research6970.Height2308.MainFree.bankfree52_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree83_1, Research6970.Height2308.MainFree.bankfree83_0, Research6970.Height2308.MainFree.bankfree123_0, Research6970.Height2308.MainFree.bankfree122_0, Research6970.Height2308.MainFree.bankfree159_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree158_0, Research6970.Height2308.MainFree.bankfree230_0, Research6970.Height2308.MainFree.bankfree172_0, Research6970.Height2308.MainFree.bankfree171_0] i
    head := Research6970.Height2308.MainHeads.src1767
    historyValues := [![14998, 164468, 759156, 3665796],
    ![24861/2, 247063/2, 563314, 2569609],
    ![6218, 178142/3, 563314, 2553201],
    ![29433/8, 72231/2, 872096/3, 1259928],
    ![62542/25, 625046/25, 412255/2, 4044121/4],
    ![17323/9, 55148/3, 744231/4, 1574397/2],
    ![36739/32, 379477/32, 1209338/9, 15445404/25],
    ![86206/121, 882528/121, 3994824/49, 17913960/49],
    ![86206/121, 882528/121, 3994824/49, 17913960/49],
    ![63754/121, 2986024/441, 68816, 17913960/49],
    ![63754/121, 2986024/441, 68816, 8519904/25],
    ![63754/121, 700600/121, 121485/2, 207025],
    ![82583/200, 700600/121, 121485/2, 207025],
    ![82583/200, 1060993/200, 48872, 9401751/49],
    ![82583/200, 902176/189, 5303280/121, 21478284/121],
    ![481736/1323, 902176/189, 5303280/121, 21478284/121],
    ![481736/1323, 12056495/2601, 13558075/324, 1343015/8],
    ![1876266/5329, 12056495/2601, 13558075/324, 1343015/8],
    ![1835316/5329, 12056495/2601, 13558075/324, 1343015/8]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 7 1 900619 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6156, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1767⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free3_0
    · exact Research6970.Height2308.MainFree.free10_0
    · exact Research6970.Height2308.MainFree.free19_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free28_0
    · exact Research6970.Height2308.MainFree.free37_0
    · exact Research6970.Height2308.MainFree.free42_1
    · exact Research6970.Height2308.MainFree.free52_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free83_1
    · exact Research6970.Height2308.MainFree.free83_0
    · exact Research6970.Height2308.MainFree.free123_0
    · exact Research6970.Height2308.MainFree.free122_0
    · exact Research6970.Height2308.MainFree.free159_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free158_0
    · exact Research6970.Height2308.MainFree.free230_0
    · exact Research6970.Height2308.MainFree.free172_0
    · exact Research6970.Height2308.MainFree.free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨31549579355147112279386739/58371422850171723463000064, 355143/379579, [320393944,320393929,320393930,320393931,320393934,320393933,320393933,147237738,147237738,147237738,147237738,70138104,70138104,84262403,82836705,125660340,101123037,128878917,235698990], [1085435,1085435,1085435,1085435,1085435,1085435,1085435,2611461,2611461,2611461,2611461,5712197,5712197,4726449,4811063,3103680,3905246,3013754,1564973], ![125113737871800,1604754451020,213622578000,5276256000], 176238389291430090⟩

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
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases17

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases18
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HigherHelperCases18.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree3_0, Research6970.Height2308.MainFree.bankfree10_0, Research6970.Height2308.MainFree.bankfree19_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree28_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree42_1, Research6970.Height2308.MainFree.bankfree52_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree83_1, Research6970.Height2308.MainFree.bankfree83_0, Research6970.Height2308.MainFree.bankfree123_0, Research6970.Height2308.MainFree.bankfree122_0, Research6970.Height2308.MainFree.bankfree159_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree158_0, Research6970.Height2308.MainFree.bankfree230_0, Research6970.Height2308.MainFree.bankfree172_0, Research6970.Height2308.MainFree.bankfree171_0] i
    head := Research6970.Height2308.MainHeads.src1768
    historyValues := [![14998, 164318, 758306, 3657546],
    ![24861/2, 246163/2, 1122503/2, 2569609],
    ![6218, 532376/9, 1122503/2, 5064927/2],
    ![29433/8, 287849/8, 2606588/9, 3749084/3],
    ![62542/25, 622746/25, 412255/2, 4044121/4],
    ![17323/9, 109871/6, 1482787/8, 3123219/4],
    ![36739/32, 378127/32, 1209338/9, 15319954/25],
    ![86206/121, 879378/121, 3980624/49, 17768460/49],
    ![86206/121, 879378/121, 3980624/49, 17768460/49],
    ![63754/121, 425332/63, 3367675/49, 17768460/49],
    ![63754/121, 425332/63, 3367675/49, 8450704/25],
    ![63754/121, 697600/121, 121485/2, 207025],
    ![82583/200, 697600/121, 121485/2, 207025],
    ![82583/200, 1056593/200, 48872, 37319881/196],
    ![82583/200, 698848/147, 5303280/121, 21303834/121],
    ![481736/1323, 698848/147, 5303280/121, 21303834/121],
    ![481736/1323, 12007370/2601, 18004475/432, 215801305/1296],
    ![1876266/5329, 12007370/2601, 18004475/432, 215801305/1296],
    ![1835316/5329, 12007370/2601, 18004475/432, 215801305/1296]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 7 2 900619 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6106, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1768⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free3_0
    · exact Research6970.Height2308.MainFree.free10_0
    · exact Research6970.Height2308.MainFree.free19_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free28_0
    · exact Research6970.Height2308.MainFree.free37_0
    · exact Research6970.Height2308.MainFree.free42_1
    · exact Research6970.Height2308.MainFree.free52_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free83_1
    · exact Research6970.Height2308.MainFree.free83_0
    · exact Research6970.Height2308.MainFree.free123_0
    · exact Research6970.Height2308.MainFree.free122_0
    · exact Research6970.Height2308.MainFree.free159_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free158_0
    · exact Research6970.Height2308.MainFree.free230_0
    · exact Research6970.Height2308.MainFree.free172_0
    · exact Research6970.Height2308.MainFree.free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨15720868505108992608401457/29120391777499537821663232, 177359/189577, [319409244,319409231,319409234,319409235,319409234,319409236,319409235,154901291,154901291,154901291,154901291,69984932,69984932,84059064,82766813,125361792,100842474,128598354,235484969], [1090470,1090470,1090470,1090470,1090470,1090470,1090470,2484110,2484110,2484110,2484110,5724364,5724364,4738517,4815211,3112022,3917081,3021593,1566732], ![125000131244580,1604985318436,213115046400,5290437400], 175652619142141780⟩

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
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases18

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases19
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HigherHelperCases19.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree3_0, Research6970.Height2308.MainFree.bankfree10_0, Research6970.Height2308.MainFree.bankfree19_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree28_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree42_1, Research6970.Height2308.MainFree.bankfree52_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree83_1, Research6970.Height2308.MainFree.bankfree83_0, Research6970.Height2308.MainFree.bankfree123_0, Research6970.Height2308.MainFree.bankfree122_0, Research6970.Height2308.MainFree.bankfree159_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree158_0, Research6970.Height2308.MainFree.bankfree230_0, Research6970.Height2308.MainFree.bankfree171_0] i
    head := Research6970.Height2308.MainHeads.src1769
    historyValues := [![14998, 164021, 756623, 3641211],
    ![24861/2, 244381/2, 2228671/4, 2569609],
    ![6218, 528317/9, 2228671/4, 9965613/4],
    ![29433/8, 571441/16, 2587382/9, 3688298/3],
    ![62542/25, 618192/25, 412255/2, 4044121/4],
    ![17323/9, 218059/12, 2943101/16, 6145161/8],
    ![36739/32, 187727/16, 1209338/9, 15071563/25],
    ![86206/121, 873141/121, 564644/7, 17480370/49],
    ![86206/121, 873141/121, 564644/7, 17480370/49],
    ![63754/121, 2960098/441, 956663/14, 17480370/49],
    ![63754/121, 2960098/441, 956663/14, 8313688/25],
    ![63754/121, 691660/121, 121485/2, 207025],
    ![82583/200, 691660/121, 121485/2, 207025],
    ![82583/200, 1047881/200, 48872, 37319881/196],
    ![82583/200, 231072/49, 10523001/242, 20958423/121],
    ![481736/1323, 231072/49, 10523001/242, 20958423/121],
    ![481736/1323, 23820205/5202, 35720035/864, 424604795/2592],
    ![1835316/5329, 23820205/5202, 35720035/864, 424604795/2592]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 7 4 900619 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 6007, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1769⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free3_0
    · exact Research6970.Height2308.MainFree.free10_0
    · exact Research6970.Height2308.MainFree.free19_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free28_0
    · exact Research6970.Height2308.MainFree.free37_0
    · exact Research6970.Height2308.MainFree.free42_1
    · exact Research6970.Height2308.MainFree.free52_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free83_1
    · exact Research6970.Height2308.MainFree.free83_0
    · exact Research6970.Height2308.MainFree.free123_0
    · exact Research6970.Height2308.MainFree.free122_0
    · exact Research6970.Height2308.MainFree.free159_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free158_0
    · exact Research6970.Height2308.MainFree.free230_0
    · exact Research6970.Height2308.MainFree.free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨499656659395899176666938581/927720792373071773696000000, 707753/756625, [317459538,317459524,317459523,317459527,317459531,317459528,317459527,147055704,147055704,147070971,147070962,74439385,75521512,83656454,82276235,124183680,130078854,235061207], [1100439,1100439,1100439,1100439,1100439,1100439,1100439,2614486,2614486,2614233,2614233,5370518,5292468,4762411,4844326,3144938,2985924,1570215], ![124775189899740,1605442530088,211555086300,5346394600], 174575240218984196⟩

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
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases19

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases20
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HigherHelperCases20.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree3_0, Research6970.Height2308.MainFree.bankfree10_0, Research6970.Height2308.MainFree.bankfree19_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree33_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree42_1, Research6970.Height2308.MainFree.bankfree52_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree83_1, Research6970.Height2308.MainFree.bankfree83_0, Research6970.Height2308.MainFree.bankfree123_0, Research6970.Height2308.MainFree.bankfree124_0, Research6970.Height2308.MainFree.bankfree159_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree187_0, Research6970.Height2308.MainFree.bankfree230_0, Research6970.Height2308.MainFree.bankfree172_0, Research6970.Height2308.MainFree.bankfree171_0] i
    head := Research6970.Height2308.MainHeads.src1770
    historyValues := [![15027, 163213, 752327, 3590197],
    ![24861/2, 240025/2, 2188741/4, 2569609],
    ![6218, 518395/9, 2188741/4, 9564135/4],
    ![29433/8, 561035/16, 2540434/9, 3539710/3],
    ![65616/25, 119536/5, 203904, 891136],
    ![17323/9, 71315/4, 2888167/16, 5897595/8],
    ![36739/32, 46115/4, 3326313/25, 2892877/5],
    ![86206/121, 857895/121, 3883780/49, 16776150/49],
    ![86206/121, 857895/121, 3883780/49, 16776150/49],
    ![63754/121, 2917990/441, 6602019/98, 16776150/49],
    ![63754/121, 2917990/441, 6602019/98, 1595752/5],
    ![63754/121, 677140/121, 2944295/49, 207025],
    ![41419/100, 677140/121, 2944295/49, 207025],
    ![41419/100, 205317/40, 48872, 37319881/196],
    ![41419/100, 6115040/1323, 10316091/242, 20114085/121],
    ![1969478/5329, 6115040/1323, 10316091/242, 20114085/121],
    ![1969478/5329, 23344675/5202, 105041395/2592, 814998050/5041],
    ![1876266/5329, 23344675/5202, 105041395/2592, 814998050/5041],
    ![1835316/5329, 23344675/5202, 105041395/2592, 814998050/5041]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 7 9 900619 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5765, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1770⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free3_0
    · exact Research6970.Height2308.MainFree.free10_0
    · exact Research6970.Height2308.MainFree.free19_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free33_0
    · exact Research6970.Height2308.MainFree.free37_0
    · exact Research6970.Height2308.MainFree.free42_1
    · exact Research6970.Height2308.MainFree.free52_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free83_1
    · exact Research6970.Height2308.MainFree.free83_0
    · exact Research6970.Height2308.MainFree.free123_0
    · exact Research6970.Height2308.MainFree.free124_0
    · exact Research6970.Height2308.MainFree.free159_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free187_0
    · exact Research6970.Height2308.MainFree.free230_0
    · exact Research6970.Height2308.MainFree.free172_0
    · exact Research6970.Height2308.MainFree.free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨245605339952164774559563039/458607894577941540795056128, 703457/752329, [312780471,312780459,312780458,312780463,312780460,312780462,312780460,145516653,145516653,145648650,145648641,69998704,69998704,82716403,87396348,122892878,99405197,126684916,234025344], [1124364,1124364,1124364,1124364,1124364,1124364,1124364,2647627,2647627,2644735,2644735,5723270,5723270,4818202,4544288,3181002,3977711,3075054,1578727], ![124225333102080,1606559095836,210622809600,5407703400], 171559667871238835⟩

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
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases20

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases21
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HigherHelperCases21.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree3_0, Research6970.Height2308.MainFree.bankfree10_0, Research6970.Height2308.MainFree.bankfree19_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree33_0, Research6970.Height2308.MainFree.bankfree42_0, Research6970.Height2308.MainFree.bankfree55_0, Research6970.Height2308.MainFree.bankfree72_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree123_0, Research6970.Height2308.MainFree.bankfree89_1, Research6970.Height2308.MainFree.bankfree168_0, Research6970.Height2308.MainFree.bankfree124_0, Research6970.Height2308.MainFree.bankfree147_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree211_0, Research6970.Height2308.MainFree.bankfree187_0, Research6970.Height2308.MainFree.bankfree172_0, Research6970.Height2308.MainFree.bankfree171_0] i
    head := Research6970.Height2308.MainHeads.src1771
    historyValues := [![15818, 161969, 745087, 3331112],
    ![24861/2, 234211/2, 1067723/2, 2569609],
    ![6218, 56128, 1067723/2, 4514139/2],
    ![29433/8, 273573/8, 275308, 1113796],
    ![65616/25, 582176/25, 203904, 891136],
    ![73478/49, 94924/7, 2994482/25, 4752400/9],
    ![22791/25, 389367/50, 182091/2, 368242],
    ![22791/25, 389367/50, 84508, 326041],
    ![53313/64, 389367/50, 9418828/121, 326041],
    ![83994/121, 657760/121, 2858054/49, 1414920/7],
    ![66872/121, 657760/121, 2858054/49, 1414920/7],
    ![66872/121, 657760/121, 2858054/49, 168100],
    ![41419/100, 657760/121, 2858054/49, 168100],
    ![41419/100, 500181/100, 340419/7, 168100],
    ![41419/100, 849952/189, 5019963/121, 86564416/529],
    ![41419/100, 23583840/5329, 11797240/289, 40741533/250],
    ![1969478/5329, 23583840/5329, 11797240/289, 40741533/250],
    ![1876266/5329, 23583840/5329, 11797240/289, 40741533/250],
    ![1835316/5329, 23583840/5329, 11797240/289, 40741533/250]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 7 16 900619 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5442, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1771⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free3_0
    · exact Research6970.Height2308.MainFree.free10_0
    · exact Research6970.Height2308.MainFree.free19_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free33_0
    · exact Research6970.Height2308.MainFree.free42_0
    · exact Research6970.Height2308.MainFree.free55_0
    · exact Research6970.Height2308.MainFree.free72_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free123_0
    · exact Research6970.Height2308.MainFree.free89_1
    · exact Research6970.Height2308.MainFree.free168_0
    · exact Research6970.Height2308.MainFree.free124_0
    · exact Research6970.Height2308.MainFree.free147_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free211_0
    · exact Research6970.Height2308.MainFree.free187_0
    · exact Research6970.Height2308.MainFree.free172_0
    · exact Research6970.Height2308.MainFree.free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨46880791567728254336874845/87465697463093362848956416, 1625068/1738541, [310251684,310251672,310251669,310251675,310251676,310251675,147136167,147136160,147136160,71548375,103417224,64949990,61768846,81194582,93577248,93577248,99495487,126775205,234087613], [1137294,1137294,1137294,1137294,1137294,1137294,2613149,2613149,2613149,5600170,3808469,6186251,6512146,4908521,4232764,4232764,3973902,3072531,1578215], ![124258386732660,1606491807392,210678851700,5036989160], 169187994779698835⟩

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
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
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
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases21

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases22
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.HigherHelperCases22.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree3_0, Research6970.Height2308.MainFree.bankfree11_0, Research6970.Height2308.MainFree.bankfree19_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree33_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree45_0, Research6970.Height2308.MainFree.bankfree61_0, Research6970.Height2308.MainFree.bankfree72_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree89_1, Research6970.Height2308.MainFree.bankfree103_0, Research6970.Height2308.MainFree.bankfree123_0, Research6970.Height2308.MainFree.bankfree140_0, Research6970.Height2308.MainFree.bankfree168_0, Research6970.Height2308.MainFree.bankfree122_0, Research6970.Height2308.MainFree.bankfree159_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree172_0, Research6970.Height2308.MainFree.bankfree171_0] i
    head := Research6970.Height2308.MainHeads.src1772
    historyValues := [![15754, 159764, 730207, 3285640],
    ![12581, 227133/2, 521400, 2496400],
    ![6218, 487768/9, 521400, 4162431/2],
    ![29433/8, 264457/8, 2395516/9, 3081052/3],
    ![65616/25, 561824/25, 203904, 891136],
    ![17323/9, 33541/2, 1359299/8, 2566707/4],
    ![38747/32, 42601/4, 3071016/25, 11676886/25],
    ![96462/121, 788418/121, 3548112/49, 12755756/49],
    ![96462/121, 788418/121, 3548112/49, 12755756/49],
    ![96462/121, 788418/121, 3548112/49, 12755756/49],
    ![66872/121, 2586592/441, 2922020/49, 12755756/49],
    ![66872/121, 2586592/441, 2922020/49, 11505664/49],
    ![66872/121, 632320/121, 2744846/49, 1304680/7],
    ![66872/121, 632320/121, 2744846/49, 1304680/7],
    ![66872/121, 632320/121, 2744846/49, 168100],
    ![82583/200, 632320/121, 2744846/49, 168100],
    ![82583/200, 960849/200, 1281520/27, 168100],
    ![82583/200, 5732576/1323, 21213120/529, 280124832/1849],
    ![1876266/5329, 5732576/1323, 21213120/529, 280124832/1849],
    ![1835316/5329, 5732576/1323, 21213120/529, 280124832/1849]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 7 26 900619 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 5018, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1772⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free3_0
    · exact Research6970.Height2308.MainFree.free11_0
    · exact Research6970.Height2308.MainFree.free19_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free33_0
    · exact Research6970.Height2308.MainFree.free37_0
    · exact Research6970.Height2308.MainFree.free45_0
    · exact Research6970.Height2308.MainFree.free61_0
    · exact Research6970.Height2308.MainFree.free72_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free89_1
    · exact Research6970.Height2308.MainFree.free103_0
    · exact Research6970.Height2308.MainFree.free123_0
    · exact Research6970.Height2308.MainFree.free140_0
    · exact Research6970.Height2308.MainFree.free168_0
    · exact Research6970.Height2308.MainFree.free122_0
    · exact Research6970.Height2308.MainFree.free159_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free172_0
    · exact Research6970.Height2308.MainFree.free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨2069602058200270884589228075/3888327107591471668849016832, 18434123/19715643, [299366690,299366678,299366678,299366681,299366682,299366683,299366681,107111453,101254559,98605925,102371117,102204296,103691739,103691739,64599118,67236324,94029996,109067791,125527812,233135234], [1192951,1192951,1192951,1192951,1192951,1192951,1192951,3676402,3899698,4011427,3852598,3859635,3796889,3796889,6222196,5971922,4209945,3608524,3107383,1586041], ![123752844911880,1607518392076,209821710600,4294143900], 163064843156012539⟩

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
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 16 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.HigherHelperCases22

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.MarkedExitCandidates1
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.MarkedExitCandidates1.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree3_0, Research6970.Height2308.MainFree.bankfree11_0, Research6970.Height2308.MainFree.bankfree19_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree33_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree45_0, Research6970.Height2308.MainFree.bankfree55_0, Research6970.Height2308.MainFree.bankfree72_0, Research6970.Height2308.MainFree.bankfree65_0, Research6970.Height2308.MainFree.bankfree123_0, Research6970.Height2308.MainFree.bankfree168_0, Research6970.Height2308.MainFree.bankfree136_0, Research6970.Height2308.MainFree.bankfree159_0, Research6970.Height2308.MainFree.bankfree199_0, Research6970.Height2308.MainFree.bankfree167_0, Research6970.Height2308.MainFree.bankfree230_0, Research6970.Height2308.MainFree.bankfree172_0, Research6970.Height2308.MainFree.bankfree171_0] i
    head := Research6970.Height2308.MainHeads.src1766
    historyValues := [![15982, 158666, 726464, 3171938],
    ![12581, 438615/4, 521400, 2496400],
    ![6218, 470425/9, 521400, 7623105/4],
    ![29433/8, 510725/16, 2313454/9, 2821330/3],
    ![65616/25, 108304/5, 203904, 891136],
    ![17323/9, 64685/4, 2622577/16, 4700685/8],
    ![38747/32, 657505/64, 2963574/25, 2138513/5],
    ![22791/25, 144397/20, 3254497/36, 932785/3],
    ![22791/25, 144397/20, 84508, 932785/3],
    ![53313/64, 144397/20, 8824234/121, 932785/3],
    ![83994/121, 606940/121, 2631905/49, 1194700/7],
    ![83994/121, 606940/121, 2631905/49, 1243407/8],
    ![86507/200, 606940/121, 2631905/49, 1243407/8],
    ![86507/200, 36945/8, 3697168/81, 1243407/8],
    ![86507/200, 788000/189, 21213120/529, 21375940/147],
    ![505124/1323, 788000/189, 21213120/529, 21375940/147],
    ![505124/1323, 21045625/5202, 24753887/648, 199854769/1444],
    ![1876266/5329, 21045625/5202, 24753887/648, 199854769/1444],
    ![1835316/5329, 21045625/5202, 24753887/648, 199854769/1444]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 6 41 771959 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 4595, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1766⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free3_0
    · exact Research6970.Height2308.MainFree.free11_0
    · exact Research6970.Height2308.MainFree.free19_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free33_0
    · exact Research6970.Height2308.MainFree.free37_0
    · exact Research6970.Height2308.MainFree.free45_0
    · exact Research6970.Height2308.MainFree.free55_0
    · exact Research6970.Height2308.MainFree.free72_0
    · exact Research6970.Height2308.MainFree.free65_0
    · exact Research6970.Height2308.MainFree.free123_0
    · exact Research6970.Height2308.MainFree.free168_0
    · exact Research6970.Height2308.MainFree.free136_0
    · exact Research6970.Height2308.MainFree.free159_0
    · exact Research6970.Height2308.MainFree.free199_0
    · exact Research6970.Height2308.MainFree.free167_0
    · exact Research6970.Height2308.MainFree.free230_0
    · exact Research6970.Height2308.MainFree.free172_0
    · exact Research6970.Height2308.MainFree.free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨6074146828492302812829579241/11545700073555176676283908096, 27573289/29421873, [292453102,292453087,292453094,292453087,292453094,292453093,292453094,127648162,127648153,127648158,97484361,61361762,56552997,75162588,72880497,118347785,95843678,122056021,230481655], [1228301,1228301,1228301,1228301,1228301,1228301,1228301,3048141,3048141,3048141,4058738,6558862,7136387,5317243,5494351,3307991,4127948,3204384,1607847], ![122344272107100,1610379099560,207433489500,5623584700], 158780599951849963⟩

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
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 18 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 19 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.MarkedExitCandidates1

namespace Research6970.Height2313.Lower6960.Prefix6969MainCases.MarkedExitCandidates2
open Research6970.Height2313.Lower6960.Prefix6969Main
open Research6970.Height2313.Lower6960.Prefix6969Helper (helperBank)
open _root_.Lower6960
open _root_.Research6969

def plan : Plan :=
  { Plan.fromStock _root_.Lower6960.Prefix6969MainCases.MarkedExitCandidates2.plan with
    bank := fun i => ![Research6970.Height2308.MainFree.bankfree3_0, Research6970.Height2308.MainFree.bankfree11_0, Research6970.Height2308.MainFree.bankfree19_0, Research6970.Height2308.MainFree.bankfree24_0, Research6970.Height2308.MainFree.bankfree37_0, Research6970.Height2308.MainFree.bankfree50_0, Research6970.Height2308.MainFree.bankfree63_0, Research6970.Height2308.MainFree.bankfree89_0, Research6970.Height2308.MainFree.bankfree123_0, Research6970.Height2308.MainFree.bankfree167_0, Research6970.Height2308.MainFree.bankfree215_0, Research6970.Height2308.MainFree.bankfree171_0] i
    head := Research6970.Height2308.MainHeads.src1773
    historyValues := [![16003, 159006, 727117, 3210159],
    ![12581, 434471/4, 521400, 2496400],
    ![6218, 465833/9, 521400, 7437297/4],
    ![29433/8, 505909/16, 2291726/9, 2752562/3],
    ![17323/9, 192151/12, 2597153/16, 4586109/8],
    ![81850/81, 228550/27, 3098099/36, 6007401/16],
    ![81850/81, 228550/27, 3098099/36, 8462281/25],
    ![250848/361, 2100552/361, 441664/7, 2102527/9],
    ![83994/121, 600220/121, 2602001/49, 1165580/7],
    ![505124/1323, 600220/121, 2602001/49, 1165580/7],
    ![505124/1323, 21591570/5329, 97192767/2500, 45874539/343],
    ![1835316/5329, 21591570/5329, 97192767/2500, 45874539/343]] }

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

theorem sources : plan.Sources 2308 (Band.near).last Research6970.Height2313.Lower6960.Prefix6969Helper.helperBank 128659 7 41 900619 := by
  refine ⟨?_, _root_.Research6969.TransitionBanks.rank154 4483, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ⟨_, Research6970.Height2308.MainHeads.coversrc1773⟩⟩
  · intro i; fin_cases i
    · exact Research6970.Height2308.MainFree.free3_0
    · exact Research6970.Height2308.MainFree.free11_0
    · exact Research6970.Height2308.MainFree.free19_0
    · exact Research6970.Height2308.MainFree.free24_0
    · exact Research6970.Height2308.MainFree.free37_0
    · exact Research6970.Height2308.MainFree.free50_0
    · exact Research6970.Height2308.MainFree.free63_0
    · exact Research6970.Height2308.MainFree.free89_0
    · exact Research6970.Height2308.MainFree.free123_0
    · exact Research6970.Height2308.MainFree.free167_0
    · exact Research6970.Height2308.MainFree.free215_0
    · exact Research6970.Height2308.MainFree.free171_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨5480491487269706269079384795/10495496578283952072431763456, 33026830/35628831, [291072951,291072938,291072943,291072942,291072944,152076781,152076790,152076786,90753072,96076310,127912599,231110462], [1235358,1235358,1235358,1235358,1235358,2531047,2531047,2531047,4375106,4118135,3040753,1602680], ![122678055438840,1609701354808,207999415800,4900580650], 159933798502267639⟩

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
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2313.Lower6960.Prefix6969MainCases.MarkedExitCandidates2
end Pack_R6970Height2313MainPlans09
