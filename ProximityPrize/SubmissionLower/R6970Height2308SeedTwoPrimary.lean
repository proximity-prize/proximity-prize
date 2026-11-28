import ProximityPrize.SubmissionLower.Bundle6970_ca24722f727e540c
import ProximityPrize.SubmissionLower.Bundle6970_ca24722f727e540c
import ProximityPrize.SubmissionLower.Bundle6970_ca24722f727e540c
import ProximityPrize.SubmissionLower.Bundle6970_ca24722f727e540c
import ProximityPrize.SubmissionLower.Bundle6970_ca24722f727e540c
import ProximityPrize.SubmissionLower.Bundle6970_ca24722f727e540c
import ProximityPrize.SubmissionLower.Bundle6970_ca24722f727e540c
import ProximityPrize.SubmissionLower.Bundle6970_ca24722f727e540c
import ProximityPrize.SubmissionLower.R6970Height2313MainFast
import ProximityPrize.SubmissionLower.Z6969FastTri

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2308.SeedTwoPrimary
open Research6970.Height2313.Lower6960.Prefix6969Main
open _root_.Lower6960
open _root_.Research6969
open _root_.Research6969.PhysicalWindow

def head : Request :=
  ⟨_root_.Research6969.TransitionBanks.bank154 9716,12,3,2,437037,3⟩

private theorem headAt2308 : (Triangular head) 2308 2308 :=
  triangular_of_fast _ _ _ (by decide +kernel)
private theorem headAt2309 : (Triangular head) 2309 2309 :=
  triangular_of_fast _ _ _ (by decide +kernel)
private theorem headAt2310 : (Triangular head) 2310 2310 :=
  triangular_of_fast _ _ _ (by decide +kernel)
private theorem headAt2311 : (Triangular head) 2311 2311 :=
  triangular_of_fast _ _ _ (by decide +kernel)
private theorem headAt2312 : (Triangular head) 2312 2312 :=
  triangular_of_fast _ _ _ (by decide +kernel)
private theorem headAt2313 : (Triangular head) 2313 2313 :=
  triangular_of_fast _ _ _ (by decide +kernel)

private theorem headCover : (Cover (Triangular head) 2313 2308 [2308, 2309, 2310, 2311, 2312, 2313]) :=
  ⟨by decide, by decide, headAt2308, by decide, by decide, headAt2309, by decide, by decide, headAt2310, by decide, by decide, headAt2311, by decide, by decide, headAt2312, by decide, by decide, headAt2313, rfl⟩

def plan : Plan where
  last := 21
  reserve i := ![0, 1, 2, 3, 5, 9, 12, 9, 12, 20, 16, 23, 21, 37, 36, 64, 77, 103, 25, 27, 25, 116] i
  bank i := ![bank0, bank1, bank2, bank3, bank4, bank5, bank6, bank7, bank8, bank9, bank10, bank11, bank12, bank13, bank14, bank15, bank16, bank17, bank18, bank19, bank20, bank21] i
  head := head
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 10, 12, 14, 13]
  historyValues := [![14018, 177162, 826288, 4667203],
    ![23965/2, 313935/2, 710531, 4112297],
    ![17372/3, 680648/9, 630208, 3356224],
    ![3599, 365621/8, 3313612/9, 18470116/9],
    ![16211/9, 46629/2, 478339/2, 5067001/4],
    ![40369/50, 264266/25, 4781568/49, 3950248/7],
    ![86978/169, 1273094/169, 436734/5, 3950248/7],
    ![86978/169, 1273094/169, 436734/5, 3413092/7],
    ![86978/169, 1228408/169, 1943136/25, 26893888/81],
    ![86978/169, 1228408/169, 1943136/25, 26893888/81],
    ![86978/169, 1228408/169, 1943136/25, 26893888/81],
    ![233764/529, 1228408/169, 1943136/25, 26893888/81],
    ![233764/529, 1228408/169, 5352016/75, 2203103/8],
    ![233764/529, 15556157/2738, 8662359/169, 34210801/144],
    ![42665/108, 15556157/2738, 8662359/169, 34210801/144],
    ![588235/1922, 15556157/2738, 8662359/169, 34210801/144],
    ![588235/1922, 7007394/1369, 125825736/2809, 8151025/36],
    ![2809786/9801, 7007394/1369, 125825736/2809, 8151025/36],
    ![2809786/9801, 7007394/1369, 125825736/2809, 8151025/36],
    ![2809786/9801, 7007394/1369, 125825736/2809, 8151025/36],
    ![2809786/9801, 7007394/1369, 125825736/2809, 8151025/36],
    ![2809786/9801, 6726800/1369, 68453019/1600, 72199009/324]]

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


theorem sources (U : ℕ) (hU : 9716 ≤ U) :
    plan.Sources 2308 (Band.near).last (_root_.Research6969.TransitionBanks.bank154 U) 128659 2 2 308378 := by
  refine {
    free := ?_
    rank := _root_.Research6969.TransitionBanks.rank154 9716
    width := ?_
    reserve_fit := by decide
    narrow := by decide
    seed_small := by decide
    same_m := rfl
    same_ord := rfl
    same_slope := rfl
    seed_le := hU
    reserve_le := by decide
    level := by decide
    slope := by decide
    weight := by decide
    seed := by decide
    extra_fit := by decide
    degree := by decide
    physical := ⟨_, headCover⟩ }
  · intro i; fin_cases i
    · exact free0
    · exact free1
    · exact free2
    · exact free3
    · exact free4
    · exact free5
    · exact free6
    · exact free7
    · exact free8
    · exact free9
    · exact free10
    · exact free11
    · exact free12
    · exact free13
    · exact free14
    · exact free15
    · exact free16
    · exact free17
    · exact free18
    · exact free19
    · exact free20
    · exact free21
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨3266691256554373/6194648735285248, 4594348983061954369380465/6357874940319421222617088, [383319372, 331706675, 208925266, 125071314, 72194820, 30797143, 26305018, 26305018, 45179075, 45179075, 45179075, 43765109, 62401398, 49282215, 80255229, 90645249, 136724321, 34658132, 50062690, 29988916, 121335945, 206818672], [895486, 1036864, 1784988, 3120137, 5548819, 13265642, 15563750, 15563750, 8981106, 8981106, 8981106, 9275323, 6447343, 8217456, 4965711, 4380540, 2840298, 11766561, 8082628, 13628099, 3224503, 1802300], ![109783487471040, 1635889404848, 186136804800, 4933489590], 204148195790182006⟩

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
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 35 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 41 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 41 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 24 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 24 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 24 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 25 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 22 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 12 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 31 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 22 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 36 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 9 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2308.SeedTwoPrimary

