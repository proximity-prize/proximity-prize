import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Lower6960.Prefix6969MainCases.NativeLight2308
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks



def head : Research6969.PhysicalWindow.Request := ⟨bank154 9078,10,3,2,385978,2⟩

def plan : Plan where
  last := 19
  reserve i := ![0, 10, 1, 8, 21, 8, 20, 41, 21, 10, 5, 25, 14, 41, 3, 65, 76, 2, 76, 76] i
  bank i := ![bank2 1526, bank61 2550, bank8 1693, bank41 3006, bank113 3744, bank48 2495, bank73 5732, bank145 8026, bank74 6640, bank42 4592, bank32 2251, bank140 4025, bank85 2922, bank119 45346, bank23 1901, bank198 9892, bank180 68470, bank14 1832, bank212 10890, bank174 186283] i
  head := head
  introIndices := [2, 17, 14, 10, 3, 9, 5, 1, 6, 8, 12, 4, 11, 7]
  historyValues := [![14052, 175255, 820306, 4594557],
    ![96292/121, 1078038/121, 4828170/49, 1625625/4],
    ![96292/121, 1078038/121, 4828170/49, 1625625/4],
    ![96292/121, 1078038/121, 4828170/49, 1625625/4],
    ![80264/121, 863766/121, 4989224/75, 14017536/49],
    ![80264/121, 863766/121, 4989224/75, 14017536/49],
    ![77324/147, 863766/121, 4989224/75, 14017536/49],
    ![1640767/3362, 10960467/1681, 49113328/841, 14017536/49],
    ![1640767/3362, 10960467/1681, 49113328/841, 14017536/49],
    ![1640767/3362, 10960467/1681, 49113328/841, 14017536/49],
    ![1640767/3362, 10960467/1681, 49113328/841, 14017536/49],
    ![1640767/3362, 10960467/1681, 49113328/841, 14017536/49],
    ![1640767/3362, 10960467/1681, 49113328/841, 14017536/49],
    ![1330489/3362, 10960467/1681, 49113328/841, 14017536/49],
    ![1330489/3362, 10960467/1681, 49113328/841, 14017536/49],
    ![1330489/3362, 7757032/1323, 26147679/529, 6115729/25],
    ![25627/74, 7757032/1323, 26147679/529, 6115729/25],
    ![25627/74, 7757032/1323, 26147679/529, 6115729/25],
    ![25627/74, 15598401/2738, 771375/16, 1143828/5],
    ![462882/1369, 15598401/2738, 771375/16, 1143828/5]]

theorem valid : plan.Valid := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · intro i; fin_cases i <;> exact ⟨by decide, by decide, by decide, by decide +kernel⟩
  · intro i; fin_cases i <;> exact ⟨by decide, by decide, by decide, by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact ZGen.Hist.history_step_of_fast plan (by decide +kernel)

def price : Pricing :=
  ⟨33491/62500, 50183/62500, [372637083, 372617508, 372617508, 156044588, 372545443, 186245409, 81662839, 193906467, 387916908, 387916908, 129321324, 193906467, 77679346, 628724665, 104808429, 110759048, 775578214, 110815051, 146022656, 241704257],
    [925427, 925480, 925480, 2466923, 925678, 2036819, 4884317, 1944416, 883542, 883542, 3004730, 1944416, 5147297, 478756, 3759069, 3552452, 317734, 3550508, 2638476, 1516738], ![128301453700740, 1598871645148, 217533831300, 4227417880], 210466372169575511⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i; refine ⟨(hAB i).1, (hAB i).2, ?_⟩; fin_cases i
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 7 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 13 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 3 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 6 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 14 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 2 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 2 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 10 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 8 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · exact Pricing.height_from_critical Band.near _ 5 _
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel


end Lower6960.Prefix6969MainCases.NativeLight2308
