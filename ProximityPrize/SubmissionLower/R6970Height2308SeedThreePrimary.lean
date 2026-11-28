import ProximityPrize.SubmissionLower.R6970Height2308SeedTwoPrimary
import ProximityPrize.SubmissionLower.R6970Height2313MainFast
import ProximityPrize.SubmissionLower.Z6969FastTri

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2308.SeedThreePrimary
open Research6970.Height2313.Lower6960.Prefix6969Main
open _root_.Lower6960
open _root_.Research6969
open _root_.Research6969.PhysicalWindow

def head : Request :=
  ⟨_root_.Research6969.TransitionBanks.bank154 9594,12,3,2,437023,4⟩

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
  bank i := ![Research6970.Height2308.SeedTwoPrimary.bank0, Research6970.Height2308.SeedTwoPrimary.bank1, Research6970.Height2308.SeedTwoPrimary.bank2, Research6970.Height2308.SeedTwoPrimary.bank3, Research6970.Height2308.SeedTwoPrimary.bank4, Research6970.Height2308.SeedTwoPrimary.bank5, Research6970.Height2308.SeedTwoPrimary.bank6, Research6970.Height2308.SeedTwoPrimary.bank7, Research6970.Height2308.SeedTwoPrimary.bank8, Research6970.Height2308.SeedTwoPrimary.bank9, Research6970.Height2308.SeedTwoPrimary.bank10, Research6970.Height2308.SeedTwoPrimary.bank11, Research6970.Height2308.SeedTwoPrimary.bank12, Research6970.Height2308.SeedTwoPrimary.bank13, Research6970.Height2308.SeedTwoPrimary.bank14, Research6970.Height2308.SeedTwoPrimary.bank15, Research6970.Height2308.SeedTwoPrimary.bank16, Research6970.Height2308.SeedTwoPrimary.bank17, Research6970.Height2308.SeedTwoPrimary.bank18, Research6970.Height2308.SeedTwoPrimary.bank19, Research6970.Height2308.SeedTwoPrimary.bank20, Research6970.Height2308.SeedTwoPrimary.bank21] i
  head := head
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 10, 12, 14, 13]
  historyValues := [![14018, 176796, 824580, 4648537],
    ![23965/2, 155900, 705712, 8121321/2],
    ![17372/3, 676012/9, 630208, 3356224],
    ![3599, 363059/8, 3290432/9, 2026466],
    ![16211/9, 208397/9, 1900241/8, 5067001/4],
    ![40369/50, 524933/50, 4749116/49, 27304524/49],
    ![86978/169, 1265286/169, 436734/5, 27304524/49],
    ![86978/169, 1265286/169, 436734/5, 23591646/49],
    ![86978/169, 1218892/169, 1943136/25, 2950688/9],
    ![86978/169, 1218892/169, 1943136/25, 2950688/9],
    ![86978/169, 1218892/169, 1943136/25, 2950688/9],
    ![233764/529, 1218892/169, 1943136/25, 2950688/9],
    ![233764/529, 1218892/169, 15924776/225, 4350879/16],
    ![233764/529, 15437573/2738, 8596113/169, 34210801/144],
    ![42665/108, 15437573/2738, 8596113/169, 34210801/144],
    ![588235/1922, 15437573/2738, 8596113/169, 34210801/144],
    ![588235/1922, 6955971/1369, 124910004/2809, 6086860/27],
    ![2809786/9801, 6955971/1369, 124910004/2809, 6086860/27],
    ![2809786/9801, 6955971/1369, 124910004/2809, 6086860/27],
    ![2809786/9801, 6955971/1369, 124910004/2809, 6086860/27],
    ![2809786/9801, 6955971/1369, 124910004/2809, 6086860/27],
    ![2809786/9801, 6678610/1369, 135928269/3200, 72199009/324]]

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


theorem sources (U : ℕ) (hU : 9594 ≤ U) :
    plan.Sources 2308 (Band.near).last (_root_.Research6969.TransitionBanks.bank154 U) 128659 2 3 308364 := by
  refine {
    free := ?_
    rank := _root_.Research6969.TransitionBanks.rank154 9594
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
    · exact Research6970.Height2308.SeedTwoPrimary.free0
    · exact Research6970.Height2308.SeedTwoPrimary.free1
    · exact Research6970.Height2308.SeedTwoPrimary.free2
    · exact Research6970.Height2308.SeedTwoPrimary.free3
    · exact Research6970.Height2308.SeedTwoPrimary.free4
    · exact Research6970.Height2308.SeedTwoPrimary.free5
    · exact Research6970.Height2308.SeedTwoPrimary.free6
    · exact Research6970.Height2308.SeedTwoPrimary.free7
    · exact Research6970.Height2308.SeedTwoPrimary.free8
    · exact Research6970.Height2308.SeedTwoPrimary.free9
    · exact Research6970.Height2308.SeedTwoPrimary.free10
    · exact Research6970.Height2308.SeedTwoPrimary.free11
    · exact Research6970.Height2308.SeedTwoPrimary.free12
    · exact Research6970.Height2308.SeedTwoPrimary.free13
    · exact Research6970.Height2308.SeedTwoPrimary.free14
    · exact Research6970.Height2308.SeedTwoPrimary.free15
    · exact Research6970.Height2308.SeedTwoPrimary.free16
    · exact Research6970.Height2308.SeedTwoPrimary.free17
    · exact Research6970.Height2308.SeedTwoPrimary.free18
    · exact Research6970.Height2308.SeedTwoPrimary.free19
    · exact Research6970.Height2308.SeedTwoPrimary.free20
    · exact Research6970.Height2308.SeedTwoPrimary.free21
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing :=
  ⟨3270857999921527/6181851246886912, 9337228786227734231711581/12663265364600944235380736, [381098484, 328782945, 207908708, 124001601, 71600492, 30542722, 26305018, 26305018, 44985702, 44985702, 44985702, 43589491, 61840421, 48842348, 79791675, 89864953, 136100062, 34502067, 49828593, 29832851, 120318874, 206428075], [901570, 1044872, 1793342, 3150025, 5596030, 13377844, 15563750, 15563750, 9020939, 9020939, 9020939, 9314609, 6504813, 8293444, 4997709, 4419868, 2853978, 11820453, 8123069, 13700944, 3252919, 1805509], ![109576150771500, 1636310085680, 185785267500, 4976966070], 202542552327794479⟩

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


end Research6970.Height2308.SeedThreePrimary

