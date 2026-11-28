import ProximityPrize.SubmissionLower.Bundle6970_7770307a6db1e05b
import ProximityPrize.SubmissionLower.Bundle6970_7770307a6db1e05b
import ProximityPrize.SubmissionLower.Bundle6970_7770307a6db1e05b
import ProximityPrize.SubmissionLower.Bundle6970_7770307a6db1e05b
import ProximityPrize.SubmissionLower.Bundle6970_7770307a6db1e05b
import ProximityPrize.SubmissionLower.Bundle6970_7770307a6db1e05b
import ProximityPrize.SubmissionLower.R6970Height2313MainFast
import ProximityPrize.SubmissionLower.Z6969FastTri

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2308.SeedOnePrimary
open Research6970.Height2313.Lower6960.Prefix6969Main
open _root_.Lower6960
open _root_.Research6969
open _root_.Research6969.PhysicalWindow

def head : Request :=
  ⟨_root_.Research6969.TransitionBanks.bank154 9838,12,3,2,437044,2⟩

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
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 16, 21, 21, 32, 51, 50, 90, 103, 103, 5] i
  bank i := ![bank0, bank1, bank2, bank3, bank4, bank5, bank6, bank7, bank8, bank9, bank10, bank11, bank12, bank13, bank14, bank15, bank16, bank17] i
  head := head
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![14235, 177506, 825552, 4513999],
    ![23965/2, 158035, 715350, 8327867/2],
    ![17372/3, 228428/3, 630208, 3356224],
    ![28151/8, 369469/8, 372644, 6473404/3],
    ![60148/25, 795822/25, 224759, 10502065/8],
    ![16211/9, 211264/9, 224759, 5067001/4],
    ![18775/16, 238165/16, 132886, 1323211/2],
    ![86978/121, 1119062/121, 820515/8, 8288641/16],
    ![86978/121, 1119062/121, 3229019/36, 1480619/3],
    ![64151/121, 3915559/484, 5447588/75, 109221476/225],
    ![64151/121, 1828895/242, 15876028/225, 9085393/32],
    ![240939/512, 3654081/512, 7906054/121, 9085393/32],
    ![588122/1875, 3654081/512, 7906054/121, 9085393/32],
    ![588122/1875, 13038752/2401, 58618216/1225, 958441/4],
    ![588122/1875, 188840888/37845, 42576912/961, 448903021/2048],
    ![210851/726, 188840888/37845, 42576912/961, 448903021/2048],
    ![5606713/19602, 188840888/37845, 42576912/961, 448903021/2048],
    ![5606713/19602, 188840888/37845, 42576912/961, 448903021/2048]]

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


theorem sources (U : ℕ) (hU : 9838 ≤ U) :
    plan.Sources 2308 (Band.near).last (_root_.Research6969.TransitionBanks.bank154 U) 128659 2 1 308385 := by
  refine {
    free := ?_
    rank := _root_.Research6969.TransitionBanks.rank154 9838
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
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨360969211098403/689630775083008, 484849945960485586581989/709176585499974654492672, [387246382, 334630405, 209941824, 125770715, 81041865, 70060669, 43095857, 60150646, 55775050, 44867785, 65281902, 80273560, 73959665, 101428609, 114937938, 137895240, 26305018, 208090159], [884730, 1028855, 1776635, 3100596, 4917585, 5718348, 9425035, 6698196, 7236257, 9045228, 6152248, 4964446, 5408626, 3892356, 3404852, 2814639, 15563750, 1791851], ![110458418200380, 1634518429976, 187537526400, 4631903640], 206634423404165233⟩

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
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 25 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 18 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 19 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 24 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 17 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 15 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 11 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 41 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Research6970.Height2308.SeedOnePrimary

