import ProximityPrize.SubmissionLower.R6970PhysicalCoverCompact
import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.Z6969FastCeil
import ProximityPrize.SubmissionLower.Z6969Pack0734
import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.Z6969Pack0575
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0596
import ProximityPrize.SubmissionLower.Z6969Pack0599
import ProximityPrize.SubmissionLower.Z6969Pack0605
import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969Pack0720
import ProximityPrize.SubmissionLower.Z6969Pack0724
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice

set_option Elab.async false

-- merged module Z6969Pack0735
section Merged_Z6969Pack0735

-- Source: Research6969.PrefixMiddleSaved107
section Z6969Source1868
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved107
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle107.price Lower6960.Prefix6969RescueData.Middle107.price :=
  ⟨335, 4070, 319, 6713, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle107.plan Lower6960.Prefix6969RescueData.Middle107.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 11 11 :=
  ⟨Lower6960.Prefix6969MainCases.Middle107.plan, Lower6960.Prefix6969MainCases.Middle107.price, Lower6960.Prefix6969MainCases.Middle107.valid, Lower6960.Prefix6969MainCases.Middle107.priced, Lower6960.Prefix6969MainCases.Middle107.sources,
   Lower6960.Prefix6969RescueData.Middle107.plan, Lower6960.Prefix6969RescueData.Middle107.price, Lower6960.Prefix6969RescueData.Middle107.sources, Lower6960.Prefix6969RescueData.Middle107.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved107
end Z6969Source1868

-- Source: Research6969.PrefixMainDataMiddle108
section Z6969Source1869
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle108
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 16, 21, 21, 30, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1096, bank9 1210, bank17 1319, bank23 1429, bank25 1577, bank32 1683, bank44 1848, bank54 2149, bank74 2799, bank84 3942, bank116 3050, bank168 3916, bank125 11583, bank150 5281, bank198 7884, bank183 20877, bank210 8954, bank174 26788, bank169 29097] i
  head := src2754
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  historyValues := [![14908, 127570, 595343, 2239868],
    ![12303, 104138, 941477/2, 3543485/2],
    ![53398/9, 452653/9, 464288, 1739761],
    ![3599, 122231/4, 2216018/9, 8369653/9],
    ![60148/25, 525798/25, 156123, 2486929/4],
    ![16211/9, 561389/36, 156123, 9857331/16],
    ![18775/16, 636295/64, 304304/3, 379456],
    ![89110/121, 746035/121, 482998/7, 1798099/7],
    ![89110/121, 746035/121, 4345489/72, 1821527/8],
    ![63754/121, 646023/121, 770661/16, 1821527/8],
    ![63754/121, 624638/121, 770661/16, 1429108/9],
    ![63754/121, 624638/121, 770661/16, 3833764/25],
    ![675632/1681, 624638/121, 770661/16, 3833764/25],
    ![675632/1681, 7550412/1681, 3987155/98, 123723268/841],
    ![675632/1681, 5515348/1323, 24812302/675, 3420488/25],
    ![954471/2738, 5515348/1323, 24812302/675, 3420488/25],
    ![954471/2738, 5533745/1369, 35816, 367105046/2809],
    ![462882/1369, 5533745/1369, 35816, 367105046/2809],
    ![459151/1369, 5533745/1369, 35816, 367105046/2809]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 12 257027 := by
  refine ⟨?_, rank154 5857, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2754⟩⟩
  · intro i; fin_cases i
    · exact free4_1
    · exact free9_1
    · exact free17_1
    · exact free23_1
    · exact free25_1
    · exact free32_1
    · exact free44_1
    · exact free54_1
    · exact free74_4
    · exact free84_1
    · exact free116_3
    · exact free168_1
    · exact free125_1
    · exact free150_1
    · exact free198_1
    · exact free183_1
    · exact free210_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [265321606, 344269577, 345619771, 344389332, 346583922, 346431214, 345948067, 148276282, 148286168, 148015580, 115204231, 72174725, 70938634, 90466687, 104163548, 103997084, 100000000, 100000000, 223541451], [1369529, 1004285, 1000580, 1003956, 997934, 998353, 999679, 2598949, 2598784, 2603289, 3402033, 5560568, 5658939, 4397570, 3785596, 3791383, 3959851, 3959851, 1667924],
  ![118660273019820, 1619276361984, 201187305900, 4711149310], 146532938624704315⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,3,3,3,3,3,3,7,7,7,9,15,15,12,10,10,11,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 5533745/1369, 35816, 367105046/2809] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle108
end Z6969Source1869

-- Source: Research6969.PhysicalChecks124
section Z6969Source1870
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1984 : Request := ⟨⟨⟨1750,2442,527,53516⟩,161065121873920,975196209190⟩,4,2,1,257027,12⟩
theorem cover1984 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1984) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src1985 : Request := ⟨⟨⟨2100,2930,632,61439⟩,278060332482560,2019119590628⟩,6,2,1,257027,12⟩
theorem cover1985 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1985) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src1986 : Request := ⟨⟨⟨2600,3628,783,70770⟩,527755772952576,4745819470168⟩,8,2,1,257027,12⟩
theorem cover1986 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1986) 2557 2412 [2413, 2419, 2434, 2474, 2557] := triangleCover (by decide +kernel)
def src1987 : Request := ⟨⟨⟨3200,4465,947,84025⟩,970564165959680,10735676910569⟩,10,2,1,257027,12⟩
theorem cover1987 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1987) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src1988 : Request := ⟨⟨⟨3200,4465,963,89293⟩,983050615259136,10877088344236⟩,13,2,1,257027,12⟩
theorem cover1988 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1988) 2557 2412 [2413, 2418, 2431, 2465, 2555, 2557] := triangleCover (by decide +kernel)
def src1989 : Request := ⟨⟨⟨3950,5512,1189,114895⟩,1848744952463360,25255771038451⟩,20,2,1,257027,12⟩
theorem cover1989 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1989) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
def src1990 : Request := ⟨⟨⟨5700,7954,1716,143638⟩,5553838907981824,109473260530676⟩,25,2,1,257027,12⟩
theorem cover1990 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1990) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src1991 : Request := ⟨⟨⟨1750,2442,527,39229⟩,161065121873920,975196209190⟩,0,2,1,257027,13⟩
theorem cover1991 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1991) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src1992 : Request := ⟨⟨⟨1750,2442,527,41270⟩,161065121873920,975196209190⟩,1,2,1,257027,13⟩
theorem cover1992 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1992) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src1993 : Request := ⟨⟨⟨1750,2442,527,43549⟩,161065121873920,975196209190⟩,2,2,1,257027,13⟩
theorem cover1993 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1993) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src1994 : Request := ⟨⟨⟨2100,2930,632,51200⟩,278060332482560,2019119590628⟩,4,2,1,257027,13⟩
theorem cover1994 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1994) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src1995 : Request := ⟨⟨⟨2100,2930,632,56297⟩,278060332482560,2019119590628⟩,6,2,1,257027,13⟩
theorem cover1995 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1995) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src1996 : Request := ⟨⟨⟨3200,4465,963,74910⟩,983050615259136,10877088344236⟩,10,2,1,257027,13⟩
theorem cover1996 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1996) 2557 2412 [2413, 2418, 2431, 2466, 2557] := triangleCover (by decide +kernel)
def src1997 : Request := ⟨⟨⟨2600,3628,783,79976⟩,527755772952576,4745819470168⟩,13,2,1,257027,13⟩
theorem cover1997 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1997) 2557 2412 [2413, 2419, 2434, 2474, 2557] := triangleCover (by decide +kernel)
def src1998 : Request := ⟨⟨⟨3950,5512,1189,95294⟩,1848744952463360,25255771038451⟩,16,2,1,257027,13⟩
theorem cover1998 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1998) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
def src1999 : Request := ⟨⟨⟨4800,6698,1445,112220⟩,3317023033262080,55058665830093⟩,20,2,1,257027,13⟩
theorem cover1999 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1999) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1870

-- Source: Research6969.PrefixRescueDataMiddle108
section Z6969Source1871
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle108
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,12⟩
  bank i := ![bank245 42716, bank245 44972, bank245 47490, bank245 50317, bank245 53516, bank252 61439, bank270 70770, bank302 84025, bank303 89293, bank315 114895, bank347 143638] i
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 10, 13, 20, 25] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257027
  seedFloor := 12

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank245 42716
    · exact rank245 44972
    · exact rank245 47490
    · exact rank245 50317
    · exact rank245 53516
    · exact rank252 61439
    · exact rank270 70770
    · exact rank302 84025
    · exact rank303 89293
    · exact rank315 114895
    · exact rank347 143638
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1980⟩
    · exact ⟨_, cover1981⟩
    · exact ⟨_, cover1982⟩
    · exact ⟨_, cover1983⟩
    · exact ⟨_, cover1984⟩
    · exact ⟨_, cover1985⟩
    · exact ⟨_, cover1986⟩
    · exact ⟨_, cover1987⟩
    · exact ⟨_, cover1988⟩
    · exact ⟨_, cover1989⟩
    · exact ⟨_, cover1990⟩

def price : EarlyPrice := ⟨2, 12, 10, 95/100, 80/100, ![671736465334, 85151619408, 8025033588, 668764668], 5080077187272802⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![6701/21, 129163/21, 295934/21, 459580/7] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle108
end Z6969Source1871

-- Source: Research6969.PrefixMiddleSaved108
section Z6969Source1872
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved108
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle108.price Lower6960.Prefix6969RescueData.Middle108.price :=
  ⟨335, 4042, 319, 6150, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle108.plan Lower6960.Prefix6969RescueData.Middle108.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 12 12 :=
  ⟨Lower6960.Prefix6969MainCases.Middle108.plan, Lower6960.Prefix6969MainCases.Middle108.price, Lower6960.Prefix6969MainCases.Middle108.valid, Lower6960.Prefix6969MainCases.Middle108.priced, Lower6960.Prefix6969MainCases.Middle108.sources,
   Lower6960.Prefix6969RescueData.Middle108.plan, Lower6960.Prefix6969RescueData.Middle108.price, Lower6960.Prefix6969RescueData.Middle108.sources, Lower6960.Prefix6969RescueData.Middle108.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved108
end Z6969Source1872

-- Source: Research6969.PrefixMainDataMiddle109
section Z6969Source1873
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle109
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 21, 14, 21, 21, 25, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1096, bank9 1210, bank17 1319, bank24 1404, bank32 1683, bank41 2155, bank42 2862, bank48 1930, bank61 2044, bank84 3942, bank85 2394, bank74 4330, bank113 3080, bank140 3403, bank150 5281, bank120 12477, bank198 7884, bank210 8954, bank183 20877, bank174 26788, bank169 29097] i
  head := src2755
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![14548, 127543, 593219, 2291479],
    ![12303, 103436, 935159/2, 3496295/2],
    ![53398/9, 449611/9, 464288, 1739761],
    ![29433/8, 487177/16, 2205014/9, 901524],
    ![16211/9, 557723/36, 2541761/16, 9726057/16],
    ![24292/27, 672637/81, 3056399/36, 12453745/36],
    ![73478/121, 798606/121, 3602203/49, 16539498/49],
    ![73478/121, 798606/121, 3602203/49, 5576735/18],
    ![73478/121, 757789/121, 485479/7, 1687468/7],
    ![63754/121, 642630/121, 770661/16, 11390409/49],
    ![63754/121, 642630/121, 770661/16, 5731236/25],
    ![61324/121, 642630/121, 770661/16, 5731236/25],
    ![61324/121, 614303/121, 770661/16, 7119728/45],
    ![61324/121, 614303/121, 770661/16, 7119728/45],
    ![61324/121, 7497684/1681, 3987155/98, 122075596/841],
    ![667406/1681, 7497684/1681, 3987155/98, 122075596/841],
    ![667406/1681, 5477596/1323, 24643978/675, 3374936/25],
    ![667406/1681, 5495525/1369, 35816, 362216162/2809],
    ![954471/2738, 5495525/1369, 35816, 362216162/2809],
    ![462882/1369, 5495525/1369, 35816, 362216162/2809],
    ![459151/1369, 5495525/1369, 35816, 362216162/2809]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 13 257027 := by
  refine ⟨?_, rank154 5779, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2755⟩⟩
  · intro i; fin_cases i
    · exact free4_1
    · exact free9_1
    · exact free17_1
    · exact free24_1
    · exact free32_1
    · exact free41_1
    · exact free42_6
    · exact free48_1
    · exact free61_1
    · exact free84_1
    · exact free85_1
    · exact free74_5
    · exact free113_1
    · exact free140_1
    · exact free150_1
    · exact free120_1
    · exact free198_1
    · exact free210_1
    · exact free183_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [261701008, 341189021, 341626312, 343212877, 341490189, 341440659, 342758902, 341873686, 166176893, 166760033, 166774755, 166775386, 82086581, 85399035, 66322186, 77178426, 103422350, 103280909, 125956610, 100000000, 223449768], [1388076, 1012739, 1011539, 1007185, 1011912, 1012048, 1008431, 1010860, 2300937, 2291229, 2290983, 2290973, 4864464, 4667513, 6065796, 5187567, 3815220, 3821197, 3101065, 3959851, 1668679],
  ![118611605849760, 1619375513292, 201104791200, 5290113720], 144579219568006333⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,3,3,3,3,3,3,3,7,7,7,7,13,13,16,14,11,11,9,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 5495525/1369, 35816, 362216162/2809] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle109
end Z6969Source1873

-- Source: Research6969.PhysicalChecks125
section Z6969Source1874
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2000 : Request := ⟨⟨⟨3950,5512,1169,125722⟩,1824966114017280,24923274283249⟩,25,2,1,257027,13⟩
theorem cover2000 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2000) 2557 2412 [2413, 2419, 2434, 2474, 2557] := triangleCover (by decide +kernel)
def src2001 : Request := ⟨⟨⟨1450,2023,436,33087⟩,91566841790464,459151377566⟩,0,2,1,257027,14⟩
theorem cover2001 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2001) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src2002 : Request := ⟨⟨⟨2100,2931,632,41397⟩,278060332482560,2021337557218⟩,1,2,1,257027,14⟩
theorem cover2002 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2002) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src2003 : Request := ⟨⟨⟨2100,2930,632,42950⟩,278060332482560,2019119590628⟩,2,2,1,257027,14⟩
theorem cover2003 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2003) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src2004 : Request := ⟨⟨⟨1750,2442,518,43607⟩,158964379549696,962176592398⟩,3,2,1,257027,14⟩
theorem cover2004 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2004) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src2005 : Request := ⟨⟨⟨2100,2930,622,46347⟩,274699477319680,1994139134137⟩,3,2,1,257027,14⟩
theorem cover2005 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2005) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2006 : Request := ⟨⟨⟨2600,3628,770,57223⟩,521059839508480,4684185417862⟩,6,2,1,257027,14⟩
theorem cover2006 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2006) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src2007 : Request := ⟨⟨⟨2600,3628,783,63914⟩,527755772952576,4745819470168⟩,10,2,1,257027,14⟩
theorem cover2007 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2007) 2557 2412 [2413, 2419, 2434, 2474, 2557] := triangleCover (by decide +kernel)
def src2008 : Request := ⟨⟨⟨3200,4465,963,68431⟩,983050615259136,10877088344236⟩,10,2,1,257027,14⟩
theorem cover2008 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2008) 2557 2412 [2413, 2418, 2431, 2466, 2557] := triangleCover (by decide +kernel)
def src2009 : Request := ⟨⟨⟨3950,5512,1189,81362⟩,1848744952463360,25255771038451⟩,13,2,1,257027,14⟩
theorem cover2009 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2009) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
def src2010 : Request := ⟨⟨⟨5700,7954,1716,120521⟩,5553838907981824,109473260530676⟩,25,2,1,257027,14⟩
theorem cover2010 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2010) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2011 : Request := ⟨⟨⟨5700,7954,1716,135167⟩,5553838907981824,109473260530676⟩,32,2,1,257027,14⟩
theorem cover2011 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2011) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2012 : Request := ⟨⟨⟨1450,2023,436,30024⟩,91566841790464,459151377566⟩,0,2,1,257027,15⟩
theorem cover2012 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2012) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src2013 : Request := ⟨⟨⟨1750,2442,518,35725⟩,158964379549696,962176592398⟩,1,2,1,257027,15⟩
theorem cover2013 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2013) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src2014 : Request := ⟨⟨⟨1750,2442,527,38063⟩,161065121873920,975196209190⟩,3,2,1,257027,15⟩
theorem cover2014 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2014) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2015 : Request := ⟨⟨⟨2100,2930,632,40676⟩,278060332482560,2019119590628⟩,3,2,1,257027,15⟩
theorem cover2015 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2015) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1874

-- Source: Research6969.PrefixRescueDataMiddle109
section Z6969Source1875
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle109
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,2,1,13⟩
  bank i := ![bank245 39229, bank245 41270, bank245 43549, bank252 51200, bank252 56297, bank303 74910, bank315 95294, bank270 79976, bank332 112220, bank314 125722] i
  reserve i := ![0, 1, 2, 4, 6, 10, 16, 13, 20, 25] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257027
  seedFloor := 13

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank245 39229
    · exact rank245 41270
    · exact rank245 43549
    · exact rank252 51200
    · exact rank252 56297
    · exact rank303 74910
    · exact rank315 95294
    · exact rank270 79976
    · exact rank332 112220
    · exact rank314 125722
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1991⟩
    · exact ⟨_, cover1992⟩
    · exact ⟨_, cover1993⟩
    · exact ⟨_, cover1994⟩
    · exact ⟨_, cover1995⟩
    · exact ⟨_, cover1996⟩
    · exact ⟨_, cover1998⟩
    · exact ⟨_, cover1997⟩
    · exact ⟨_, cover1999⟩
    · exact ⟨_, cover2000⟩

def price : EarlyPrice := ⟨2, 13, 9, 90/100, 80/100, ![636946374376, 70999730650, 7320815060, 563149735], 4611549499170341⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![6681/26, 140919/26, 161550/13, 62861] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle109
end Z6969Source1875

-- Source: Research6969.PrefixMiddleSaved109
section Z6969Source1876
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved109
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle109.price Lower6960.Prefix6969RescueData.Middle109.price :=
  ⟨335, 4014, 256, 5419, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle109.plan Lower6960.Prefix6969RescueData.Middle109.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 13 13 :=
  ⟨Lower6960.Prefix6969MainCases.Middle109.plan, Lower6960.Prefix6969MainCases.Middle109.price, Lower6960.Prefix6969MainCases.Middle109.valid, Lower6960.Prefix6969MainCases.Middle109.priced, Lower6960.Prefix6969MainCases.Middle109.sources,
   Lower6960.Prefix6969RescueData.Middle109.plan, Lower6960.Prefix6969RescueData.Middle109.price, Lower6960.Prefix6969RescueData.Middle109.sources, Lower6960.Prefix6969RescueData.Middle109.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved109
end Z6969Source1876

-- Source: Research6969.PrefixMainDataMiddle110
section Z6969Source1877
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle110
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 19
  reserve i := ![0, 1, 2, 3, 5, 7, 10, 14, 13, 21, 18, 21, 30, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1096, bank9 1210, bank17 1319, bank24 1404, bank32 1683, bank44 1848, bank53 2196, bank62 2724, bank72 2320, bank84 3942, bank104 2782, bank137 3019, bank168 3916, bank125 11583, bank150 5281, bank198 7884, bank181 21723, bank212 8810, bank174 26788, bank169 29097] i
  head := src2756
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![14876, 127051, 591950, 2219868],
    ![12303, 102743, 464461, 1724855],
    ![53398/9, 446608/9, 464288, 1724855],
    ![29433/8, 241933/8, 2190076/9, 889512],
    ![16211/9, 138526/9, 1262603/8, 4798233/8],
    ![18775/16, 313885/32, 304304/3, 379456],
    ![86808/121, 738248/121, 3314680/49, 12521592/49],
    ![86808/121, 738248/121, 3314680/49, 12521592/49],
    ![86808/121, 738248/121, 3314680/49, 12521592/49],
    ![63754/121, 1278561/242, 770661/16, 11238642/49],
    ![63754/121, 1278561/242, 770661/16, 2440456/13],
    ![63754/121, 633619/121, 770661/16, 34428676/225],
    ![63754/121, 633619/121, 770661/16, 22329032/147],
    ![675632/1681, 633619/121, 770661/16, 22329032/147],
    ![675632/1681, 7445632/1681, 3987155/98, 120449048/841],
    ![675632/1681, 5440328/1323, 24477812/675, 3329968/25],
    ![474397/1369, 5440328/1323, 24477812/675, 3329968/25],
    ![474397/1369, 10969609/2738, 179724/5, 351642340/2809],
    ![462882/1369, 10969609/2738, 179724/5, 351642340/2809],
    ![459151/1369, 10969609/2738, 179724/5, 351642340/2809]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 14 257027 := by
  refine ⟨?_, rank154 5702, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2756⟩⟩
  · intro i; fin_cases i
    · exact free4_1
    · exact free9_1
    · exact free17_1
    · exact free24_1
    · exact free32_1
    · exact free44_1
    · exact free53_1
    · exact free62_1
    · exact free72_1
    · exact free84_1
    · exact free104_1
    · exact free137_1
    · exact free168_1
    · exact free125_1
    · exact free150_1
    · exact free198_1
    · exact free181_1
    · exact free212_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [261939154, 341116563, 341144819, 341682580, 340027131, 339521361, 147288481, 147223286, 147650649, 147775109, 147178201, 113894694, 69679481, 70300188, 89071748, 98001018, 101453735, 100000000, 100000000, 223539971], [1386856, 1012938, 1012860, 1011384, 1015927, 1017315, 2615394, 2616479, 2609364, 2607292, 2617230, 3447343, 5761150, 5709747, 4468005, 4044329, 3898415, 3959851, 3959851, 1667937],
  ![118659487406220, 1619277871504, 201185973900, 4811655520], 144239907794968962⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,3,3,3,3,3,7,7,7,7,7,10,16,15,12,11,11,11,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 10969609/2738, 179724/5, 351642340/2809] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle110
end Z6969Source1877

-- Source: Research6969.PrefixRescueDataMiddle110
section Z6969Source1878
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle110
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,14⟩
  bank i := ![bank236 33087, bank255 41397, bank252 42950, bank251 46347, bank244 43607, bank269 57223, bank303 68431, bank270 63914, bank315 81362, bank347 120521, bank347 135167] i
  reserve i := ![0, 1, 2, 3, 3, 6, 10, 10, 13, 25, 32] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257027
  seedFloor := 14

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank236 33087
    · exact rank255 41397
    · exact rank252 42950
    · exact rank251 46347
    · exact rank244 43607
    · exact rank269 57223
    · exact rank303 68431
    · exact rank270 63914
    · exact rank315 81362
    · exact rank347 120521
    · exact rank347 135167
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2001⟩
    · exact ⟨_, cover2002⟩
    · exact ⟨_, cover2003⟩
    · exact ⟨_, cover2005⟩
    · exact ⟨_, cover2004⟩
    · exact ⟨_, cover2006⟩
    · exact ⟨_, cover2008⟩
    · exact ⟨_, cover2007⟩
    · exact ⟨_, cover2009⟩
    · exact ⟨_, cover2010⟩
    · exact ⟨_, cover2011⟩

def price : EarlyPrice := ⟨2, 14, 10, 90/100, 80/100, ![737474396008, 86712366453, 9362537184, 668764668], 3948871354074851⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![9670/33, 159191/33, 127230/11, 1892338/33] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle110
end Z6969Source1878

-- Source: Research6969.PrefixMiddleSaved110
section Z6969Source1879
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved110
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle110.price Lower6960.Prefix6969RescueData.Middle110.price :=
  ⟨335, 4006, 293, 4823, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle110.plan Lower6960.Prefix6969RescueData.Middle110.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 14 14 :=
  ⟨Lower6960.Prefix6969MainCases.Middle110.plan, Lower6960.Prefix6969MainCases.Middle110.price, Lower6960.Prefix6969MainCases.Middle110.valid, Lower6960.Prefix6969MainCases.Middle110.priced, Lower6960.Prefix6969MainCases.Middle110.sources,
   Lower6960.Prefix6969RescueData.Middle110.plan, Lower6960.Prefix6969RescueData.Middle110.price, Lower6960.Prefix6969RescueData.Middle110.sources, Lower6960.Prefix6969RescueData.Middle110.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved110
end Z6969Source1879

end Merged_Z6969Pack0735

-- merged module Z6969Pack0736
section Merged_Z6969Pack0736

-- Source: Research6969.PrefixMainDataMiddle111
section Z6969Source1880
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle111
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 21, 14, 21, 21, 25, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1096, bank9 1210, bank17 1319, bank24 1404, bank32 1683, bank41 2155, bank42 2862, bank48 1930, bank61 2044, bank84 3942, bank85 2394, bank74 4330, bank113 3080, bank140 3403, bank150 5281, bank121 11999, bank198 7884, bank212 8810, bank183 20877, bank174 26788, bank169 29097] i
  head := src2757
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![14548, 127081, 590755, 2272229],
    ![12303, 102050, 922685/2, 3403125/2],
    ![53398/9, 443605/9, 922685/2, 3403125/2],
    ![29433/8, 480555/16, 241682, 877500],
    ![16211/9, 61165/4, 2508651/16, 9466875/16],
    ![24292/27, 664475/81, 3019285/36, 1346875/4],
    ![73478/121, 790290/121, 3565089/49, 16098750/49],
    ![73478/121, 790290/121, 3565089/49, 603125/2],
    ![73478/121, 746855/121, 478549/7, 1642500/7],
    ![63754/121, 635931/121, 770661/16, 11086875/49],
    ![63754/121, 635931/121, 770661/16, 11086875/49],
    ![61324/121, 635931/121, 770661/16, 11086875/49],
    ![61324/121, 605525/121, 770661/16, 154000],
    ![61324/121, 605525/121, 770661/16, 154000],
    ![61324/121, 7393580/1681, 3987155/98, 27888961/196],
    ![671521/1681, 7393580/1681, 3987155/98, 27888961/196],
    ![671521/1681, 600340/147, 2701294/75, 131400],
    ![671521/1681, 21784525/5476, 179724/5, 3104644/25],
    ![954471/2738, 21784525/5476, 179724/5, 3104644/25],
    ![462882/1369, 21784525/5476, 179724/5, 3104644/25],
    ![459151/1369, 21784525/5476, 179724/5, 3104644/25]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 15 257027 := by
  refine ⟨?_, rank154 5625, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2757⟩⟩
  · intro i; fin_cases i
    · exact free4_1
    · exact free9_1
    · exact free17_1
    · exact free24_1
    · exact free32_1
    · exact free41_1
    · exact free42_6
    · exact free48_1
    · exact free61_1
    · exact free84_1
    · exact free85_1
    · exact free74_5
    · exact free113_1
    · exact free140_1
    · exact free150_1
    · exact free121_1
    · exact free198_1
    · exact free212_1
    · exact free183_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [258763612, 339238879, 338727720, 339254986, 337514555, 338518759, 338852278, 339179408, 168294376, 168699440, 168586567, 168329140, 81353571, 84522780, 72515807, 90245608, 104272541, 104306061, 125185301, 100000000, 223447201], [1403122, 1018090, 1019493, 1018046, 1022822, 1020067, 1019151, 1018254, 2265685, 2258941, 2260820, 2265106, 4908047, 4719613, 5533425, 4408733, 3781808, 3780643, 3122655, 3959851, 1668700],
  ![118610243234820, 1619378230484, 201102480900, 4711149310], 142722933199075344⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,3,3,3,3,3,3,3,7,7,7,7,13,13,15,12,10,10,9,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 21784525/5476, 179724/5, 3104644/25] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle111
end Z6969Source1880

-- Source: Research6969.PhysicalChecks126
section Z6969Source1881
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2016 : Request := ⟨⟨⟨1750,2442,527,40354⟩,161065121873920,975196209190⟩,4,2,1,257027,15⟩
theorem cover2016 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2016) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2017 : Request := ⟨⟨⟨2100,2930,622,44172⟩,274699477319680,1994139134137⟩,4,2,1,257027,15⟩
theorem cover2017 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2017) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2018 : Request := ⟨⟨⟨2600,3628,783,53712⟩,527755772952576,4745819470168⟩,8,2,1,257027,15⟩
theorem cover2018 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2018) 2557 2412 [2413, 2419, 2434, 2474, 2557] := triangleCover (by decide +kernel)
def src2019 : Request := ⟨⟨⟨3200,4465,947,65024⟩,970564165959680,10735676910569⟩,10,2,1,257027,15⟩
theorem cover2019 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2019) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src2020 : Request := ⟨⟨⟨3200,4465,963,67734⟩,983050615259136,10877088344236⟩,13,2,1,257027,15⟩
theorem cover2020 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2020) 2557 2412 [2413, 2418, 2431, 2466, 2557] := triangleCover (by decide +kernel)
def src2021 : Request := ⟨⟨⟨4800,6698,1445,93190⟩,3317023033262080,55058665830093⟩,20,2,1,257027,15⟩
theorem cover2021 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2021) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2022 : Request := ⟨⟨⟨5700,7954,1716,122556⟩,5553838907981824,109473260530676⟩,32,2,1,257027,15⟩
theorem cover2022 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2022) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2023 : Request := ⟨⟨⟨1450,2023,436,27107⟩,91566841790464,459151377566⟩,0,2,1,257027,16⟩
theorem cover2023 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2023) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src2024 : Request := ⟨⟨⟨1750,2442,527,30952⟩,161065121873920,975196209190⟩,1,2,1,257027,16⟩
theorem cover2024 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2024) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2025 : Request := ⟨⟨⟨2100,2930,632,35406⟩,278060332482560,2019119590628⟩,2,2,1,257027,16⟩
theorem cover2025 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2025) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src2026 : Request := ⟨⟨⟨2100,2930,632,36802⟩,278060332482560,2019119590628⟩,3,2,1,257027,16⟩
theorem cover2026 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2026) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src2027 : Request := ⟨⟨⟨1750,2442,527,36291⟩,161065121873920,975196209190⟩,4,2,1,257027,16⟩
theorem cover2027 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2027) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2028 : Request := ⟨⟨⟨2100,2930,632,38329⟩,278060332482560,2019119590628⟩,4,2,1,257027,16⟩
theorem cover2028 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2028) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src2029 : Request := ⟨⟨⟨2600,3628,783,48484⟩,527755772952576,4745819470168⟩,8,2,1,257027,16⟩
theorem cover2029 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2029) 2557 2412 [2413, 2419, 2434, 2474, 2557] := triangleCover (by decide +kernel)
def src2030 : Request := ⟨⟨⟨3200,4465,947,59160⟩,970564165959680,10735676910569⟩,10,2,1,257027,16⟩
theorem cover2030 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2030) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src2031 : Request := ⟨⟨⟨3200,4465,963,61113⟩,983050615259136,10877088344236⟩,13,2,1,257027,16⟩
theorem cover2031 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2031) 2557 2412 [2413, 2418, 2431, 2466, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1881

-- Source: Research6969.PrefixRescueDataMiddle111
section Z6969Source1882
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle111
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,15⟩
  bank i := ![bank236 30024, bank244 35725, bank252 40676, bank245 38063, bank251 44172, bank245 40354, bank270 53712, bank302 65024, bank303 67734, bank332 93190, bank347 122556] i
  reserve i := ![0, 1, 3, 3, 4, 4, 8, 10, 13, 20, 32] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257027
  seedFloor := 15

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank236 30024
    · exact rank244 35725
    · exact rank252 40676
    · exact rank245 38063
    · exact rank251 44172
    · exact rank245 40354
    · exact rank270 53712
    · exact rank302 65024
    · exact rank303 67734
    · exact rank332 93190
    · exact rank347 122556
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2012⟩
    · exact ⟨_, cover2013⟩
    · exact ⟨_, cover2015⟩
    · exact ⟨_, cover2014⟩
    · exact ⟨_, cover2017⟩
    · exact ⟨_, cover2016⟩
    · exact ⟨_, cover2018⟩
    · exact ⟨_, cover2019⟩
    · exact ⟨_, cover2020⟩
    · exact ⟨_, cover2021⟩
    · exact ⟨_, cover2022⟩

def price : EarlyPrice := ⟨2, 15, 10, 90/100, 80/100, ![716430511440, 84228618108, 10031289840, 668764668], 3587476732607930⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![9670/33, 49432/11, 121474/11, 612780/11] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle111
end Z6969Source1882

-- Source: Research6969.PrefixMiddleSaved111
section Z6969Source1883
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved111
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle111.price Lower6960.Prefix6969RescueData.Middle111.price :=
  ⟨335, 3978, 293, 4493, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle111.plan Lower6960.Prefix6969RescueData.Middle111.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 15 15 :=
  ⟨Lower6960.Prefix6969MainCases.Middle111.plan, Lower6960.Prefix6969MainCases.Middle111.price, Lower6960.Prefix6969MainCases.Middle111.valid, Lower6960.Prefix6969MainCases.Middle111.priced, Lower6960.Prefix6969MainCases.Middle111.sources,
   Lower6960.Prefix6969RescueData.Middle111.plan, Lower6960.Prefix6969RescueData.Middle111.price, Lower6960.Prefix6969RescueData.Middle111.sources, Lower6960.Prefix6969RescueData.Middle111.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved111
end Z6969Source1883

-- Source: Research6969.PrefixMainDataMiddle112
section Z6969Source1884
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle112
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 21, 14, 21, 21, 25, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1096, bank9 1210, bank17 1319, bank24 1404, bank32 1683, bank41 2155, bank42 2862, bank48 1930, bank61 2044, bank84 3942, bank85 2394, bank74 4330, bank113 3080, bank140 3403, bank150 5281, bank121 11999, bank198 7884, bank212 8810, bank183 20877, bank174 26788, bank169 29097] i
  head := src2758
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![14548, 126856, 589555, 2262854],
    ![12303, 101375, 458305, 1678875],
    ![53398/9, 440680/9, 458305, 1678875],
    ![29433/8, 238665/8, 720196/3, 865800],
    ![16211/9, 45580/3, 1246263/8, 4670325/8],
    ![24292/27, 660500/81, 1500605/18, 1993375/6],
    ![73478/121, 786240/121, 3547014/49, 8191044/25],
    ![73478/121, 786240/121, 3547014/49, 892625/3],
    ![73478/121, 741530/121, 67882, 1620600/7],
    ![63754/121, 1265337/242, 770661/16, 10939050/49],
    ![63754/121, 1265337/242, 770661/16, 10939050/49],
    ![61324/121, 1265337/242, 770661/16, 10939050/49],
    ![61324/121, 601250/121, 770661/16, 455840/3],
    ![61324/121, 601250/121, 770661/16, 455840/3],
    ![61324/121, 7342880/1681, 3987155/98, 27888961/196],
    ![671521/1681, 7342880/1681, 3987155/98, 27888961/196],
    ![671521/1681, 255560/63, 8049932/225, 129648],
    ![671521/1681, 10816925/2738, 8049932/225, 3104644/25],
    ![954471/2738, 10816925/2738, 8049932/225, 3104644/25],
    ![462882/1369, 10816925/2738, 8049932/225, 3104644/25],
    ![459151/1369, 10816925/2738, 8049932/225, 3104644/25]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 16 257027 := by
  refine ⟨?_, rank154 5550, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2758⟩⟩
  · intro i; fin_cases i
    · exact free4_1
    · exact free9_1
    · exact free17_1
    · exact free24_1
    · exact free32_1
    · exact free41_1
    · exact free42_6
    · exact free48_1
    · exact free61_1
    · exact free84_1
    · exact free85_1
    · exact free74_5
    · exact free113_1
    · exact free140_1
    · exact free150_1
    · exact free121_1
    · exact free198_1
    · exact free212_1
    · exact free183_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [257333062, 337181060, 336004369, 336741499, 336916566, 336411906, 336906862, 335970315, 166673743, 166697715, 167188636, 167139984, 70496896, 83794317, 72423544, 77178426, 102348147, 102432460, 125035338, 100000000, 223206248], [1410450, 1023737, 1026967, 1024944, 1024463, 1025848, 1024490, 1027060, 2292665, 2292266, 2284093, 2284903, 5694093, 4762926, 5540767, 5187567, 3860616, 3857053, 3126852, 3959851, 1670684],
  ![118482340563360, 1619640087712, 200885623200, 5290113720], 141638259695205493⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,3,3,3,3,3,3,3,7,7,7,7,15,13,15,14,11,11,9,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 10816925/2738, 8049932/225, 3104644/25] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle112
end Z6969Source1884

-- Source: Research6969.PhysicalChecks127
section Z6969Source1885
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2032 : Request := ⟨⟨⟨4800,6698,1445,84326⟩,3317023033262080,55058665830093⟩,20,2,1,257027,16⟩
theorem cover2032 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2032) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
def src2033 : Request := ⟨⟨⟨5700,7954,1716,110524⟩,5553838907981824,109473260530676⟩,32,2,1,257027,16⟩
theorem cover2033 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2033) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2034 : Request := ⟨⟨⟨1750,2442,527,26666⟩,161065121873920,975196209190⟩,0,2,1,257027,17⟩
theorem cover2034 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2034) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2035 : Request := ⟨⟨⟨1750,2442,527,27882⟩,161065121873920,975196209190⟩,1,2,1,257027,17⟩
theorem cover2035 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2035) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2036 : Request := ⟨⟨⟨1750,2442,527,29236⟩,161065121873920,975196209190⟩,2,2,1,257027,17⟩
theorem cover2036 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2036) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2037 : Request := ⟨⟨⟨1750,2442,527,30751⟩,161065121873920,975196209190⟩,3,2,1,257027,17⟩
theorem cover2037 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2037) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2038 : Request := ⟨⟨⟨1750,2442,527,32462⟩,161065121873920,975196209190⟩,4,2,1,257027,17⟩
theorem cover2038 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2038) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2039 : Request := ⟨⟨⟨2100,2930,632,37512⟩,278060332482560,2019119590628⟩,6,2,1,257027,17⟩
theorem cover2039 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2039) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src2040 : Request := ⟨⟨⟨2600,3628,783,43576⟩,527755772952576,4745819470168⟩,8,2,1,257027,17⟩
theorem cover2040 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2040) 2557 2412 [2413, 2419, 2434, 2474, 2557] := triangleCover (by decide +kernel)
def src2041 : Request := ⟨⟨⟨3200,4465,963,50738⟩,983050615259136,10877088344236⟩,10,2,1,257027,17⟩
theorem cover2041 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2041) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src2042 : Request := ⟨⟨⟨3200,4465,963,54890⟩,983050615259136,10877088344236⟩,13,2,1,257027,17⟩
theorem cover2042 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2042) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src2043 : Request := ⟨⟨⟨4800,6698,1445,76023⟩,3317023033262080,55058665830093⟩,20,2,1,257027,17⟩
theorem cover2043 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2043) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
def src2044 : Request := ⟨⟨⟨5700,7954,1716,99208⟩,5553838907981824,109473260530676⟩,32,2,1,257027,17⟩
theorem cover2044 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2044) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2045 : Request := ⟨⟨⟨1450,2023,436,21842⟩,91566841790464,459151377566⟩,0,2,1,257027,18⟩
theorem cover2045 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2045) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src2046 : Request := ⟨⟨⟨1750,2442,527,25059⟩,161065121873920,975196209190⟩,1,2,1,257027,18⟩
theorem cover2046 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2046) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2047 : Request := ⟨⟨⟨1750,2442,527,26202⟩,161065121873920,975196209190⟩,2,2,1,257027,18⟩
theorem cover2047 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2047) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1885

-- Source: Research6969.PrefixRescueDataMiddle112
section Z6969Source1886
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle112
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,16⟩
  bank i := ![bank236 27107, bank245 30952, bank252 35406, bank252 36802, bank252 38329, bank245 36291, bank270 48484, bank302 59160, bank303 61113, bank332 84326, bank347 110524] i
  reserve i := ![0, 1, 2, 3, 4, 4, 8, 10, 13, 20, 32] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257027
  seedFloor := 16

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank236 27107
    · exact rank245 30952
    · exact rank252 35406
    · exact rank252 36802
    · exact rank252 38329
    · exact rank245 36291
    · exact rank270 48484
    · exact rank302 59160
    · exact rank303 61113
    · exact rank332 84326
    · exact rank347 110524
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2023⟩
    · exact ⟨_, cover2024⟩
    · exact ⟨_, cover2025⟩
    · exact ⟨_, cover2026⟩
    · exact ⟨_, cover2028⟩
    · exact ⟨_, cover2027⟩
    · exact ⟨_, cover2029⟩
    · exact ⟨_, cover2030⟩
    · exact ⟨_, cover2031⟩
    · exact ⟨_, cover2032⟩
    · exact ⟨_, cover2033⟩

def price : EarlyPrice := ⟨2, 16, 10, 90/100, 80/100, ![689167538944, 81970519380, 10700042496, 668764668], 3339438776006538⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![9670/33, 137980/33, 116104/11, 1768384/33] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle112
end Z6969Source1886

-- Source: Research6969.PrefixMiddleSaved112
section Z6969Source1887
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved112
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle112.price Lower6960.Prefix6969RescueData.Middle112.price :=
  ⟨335, 3950, 293, 4181, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle112.plan Lower6960.Prefix6969RescueData.Middle112.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 16 16 :=
  ⟨Lower6960.Prefix6969MainCases.Middle112.plan, Lower6960.Prefix6969MainCases.Middle112.price, Lower6960.Prefix6969MainCases.Middle112.valid, Lower6960.Prefix6969MainCases.Middle112.priced, Lower6960.Prefix6969MainCases.Middle112.sources,
   Lower6960.Prefix6969RescueData.Middle112.plan, Lower6960.Prefix6969RescueData.Middle112.price, Lower6960.Prefix6969RescueData.Middle112.sources, Lower6960.Prefix6969RescueData.Middle112.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved112
end Z6969Source1887

-- Source: Research6969.PrefixMainDataMiddle113
section Z6969Source1888
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle113
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 21
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 10, 14, 14, 21, 21, 21, 21, 30, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1096, bank9 1210, bank17 1319, bank24 1404, bank30 1501, bank40 1714, bank50 1914, bank54 2149, bank62 2724, bank82 2422, bank84 3942, bank74 4330, bank116 3050, bank110 3137, bank168 3916, bank125 11583, bank153 5200, bank199 7608, bank181 21723, bank212 8810, bank174 26788, bank169 29097] i
  head := src2759
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
  historyValues := [![14899, 126432, 586118, 2173732],
    ![12303, 100700, 910535/2, 3312375/2],
    ![53398/9, 437755/9, 910535/2, 3312375/2],
    ![29433/8, 474105/16, 715346/3, 854100],
    ![63824/25, 102499/5, 313709/2, 2253001/4],
    ![72196/49, 581555/49, 2620783/25, 375366],
    ![81680/81, 217960/27, 81803, 582175/2],
    ![89110/121, 721205/121, 466954/7, 1680825/7],
    ![89110/121, 721205/121, 466954/7, 1680825/7],
    ![89110/121, 721205/121, 466954/7, 5866084/25],
    ![63754/121, 254770/49, 770661/16, 10791225/49],
    ![61324/121, 254770/49, 770661/16, 10791225/49],
    ![61324/121, 602100/121, 770661/16, 445300/3],
    ![61324/121, 2369925/484, 1540267/32, 445300/3],
    ![61324/121, 2369925/484, 1540267/32, 7146700/49],
    ![675632/1681, 2369925/484, 1540267/32, 7146700/49],
    ![675632/1681, 7346600/1681, 1999400/49, 6760000/49],
    ![675632/1681, 1792990/441, 2690978/75, 370256/3],
    ![474397/1369, 1792990/441, 2690978/75, 370256/3],
    ![474397/1369, 21483175/5476, 96473615/2704, 370256/3],
    ![462882/1369, 21483175/5476, 96473615/2704, 370256/3],
    ![459151/1369, 21483175/5476, 96473615/2704, 370256/3]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 17 257027 := by
  refine ⟨?_, rank154 5475, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2759⟩⟩
  · intro i; fin_cases i
    · exact free4_1
    · exact free9_1
    · exact free17_1
    · exact free24_1
    · exact free30_2
    · exact free40_1
    · exact free50_1
    · exact free54_1
    · exact free62_1
    · exact free82_1
    · exact free84_1
    · exact free74_5
    · exact free116_3
    · exact free110_1
    · exact free168_1
    · exact free125_1
    · exact free153_1
    · exact free199_1
    · exact free181_1
    · exact free212_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [257324149, 334603366, 335761934, 334961960, 335691360, 333549253, 334702775, 165881465, 166211283, 163411391, 160886776, 161032276, 94700938, 112102856, 69956224, 65970644, 70609117, 94670181, 99749563, 100000000, 100000000, 233740661], [1410496, 1030811, 1027632, 1029827, 1027825, 1033704, 1030538, 2305855, 2300364, 2346977, 2389007, 2386585, 4183792, 3509627, 5737121, 6097696, 5685162, 4185322, 3970434, 3959851, 3959851, 1583958],
  ![124074217672020, 1608209821084, 210366594900, 5797545360], 143154114778056291⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,3,3,3,3,3,3,7,7,7,7,7,11,10,15,16,15,12,11,11,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 21483175/5476, 96473615/2704, 370256/3] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle113
end Z6969Source1888

-- Source: Research6969.PrefixRescueDataMiddle113
section Z6969Source1889
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle113
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,17⟩
  bank i := ![bank245 26666, bank245 27882, bank245 29236, bank245 30751, bank245 32462, bank252 37512, bank270 43576, bank303 50738, bank303 54890, bank332 76023, bank347 99208] i
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 10, 13, 20, 32] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257027
  seedFloor := 17

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank245 26666
    · exact rank245 27882
    · exact rank245 29236
    · exact rank245 30751
    · exact rank245 32462
    · exact rank252 37512
    · exact rank270 43576
    · exact rank303 50738
    · exact rank303 54890
    · exact rank332 76023
    · exact rank347 99208
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2034⟩
    · exact ⟨_, cover2035⟩
    · exact ⟨_, cover2036⟩
    · exact ⟨_, cover2037⟩
    · exact ⟨_, cover2038⟩
    · exact ⟨_, cover2039⟩
    · exact ⟨_, cover2040⟩
    · exact ⟨_, cover2041⟩
    · exact ⟨_, cover2042⟩
    · exact ⟨_, cover2043⟩
    · exact ⟨_, cover2044⟩

def price : EarlyPrice := ⟨2, 17, 10, 90/100, 80/100, ![657269964568, 79991456082, 11368793436, 668764668], 3623068548895788⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![9670/33, 128380/33, 333634/33, 1686536/33] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle113
end Z6969Source1889

-- Source: Research6969.PrefixMiddleSaved113
section Z6969Source1890
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved113
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle113.price Lower6960.Prefix6969RescueData.Middle113.price :=
  ⟨335, 3923, 293, 3890, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle113.plan Lower6960.Prefix6969RescueData.Middle113.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 17 17 :=
  ⟨Lower6960.Prefix6969MainCases.Middle113.plan, Lower6960.Prefix6969MainCases.Middle113.price, Lower6960.Prefix6969MainCases.Middle113.valid, Lower6960.Prefix6969MainCases.Middle113.priced, Lower6960.Prefix6969MainCases.Middle113.sources,
   Lower6960.Prefix6969RescueData.Middle113.plan, Lower6960.Prefix6969RescueData.Middle113.price, Lower6960.Prefix6969RescueData.Middle113.sources, Lower6960.Prefix6969RescueData.Middle113.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved113
end Z6969Source1890

-- Source: Research6969.PrefixMainDataMiddle114
section Z6969Source1891
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle114
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 5, 7, 10, 16, 21, 17, 21, 30, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1096, bank9 1210, bank17 1319, bank24 1404, bank32 1683, bank44 1848, bank54 2149, bank74 2799, bank84 3942, bank98 2688, bank137 3019, bank168 3916, bank126 11206, bank153 5200, bank199 7608, bank185 19986, bank212 8810, bank175 25973, bank169 29097] i
  head := src2760
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  historyValues := [![14984, 126323, 588416, 2176071],
    ![12303, 100043, 452311, 1634105],
    ![53398/9, 434908/9, 452311, 1634105],
    ![29433/8, 235483/8, 2131876/9, 842712],
    ![16211/9, 135001/9, 1230353/8, 4545783/8],
    ![18775/16, 305635/32, 304304/3, 379456],
    ![89110/121, 716460/121, 463888/7, 1658414/7],
    ![89110/121, 716460/121, 116003/2, 870489/4],
    ![63754/121, 760076/147, 770661/16, 10647342/49],
    ![63754/121, 760076/147, 770661/16, 200704],
    ![63754/121, 614419/121, 770661/16, 32617276/225],
    ![63754/121, 614419/121, 770661/16, 21154232/147],
    ![1355575/3362, 614419/121, 770661/16, 21154232/147],
    ![1355575/3362, 7295792/1681, 1999400/49, 6760000/49],
    ![1355575/3362, 1780580/441, 4332756/121, 27398944/225],
    ![480830/1369, 1780580/441, 4332756/121, 27398944/225],
    ![480830/1369, 10668259/2738, 3685465/104, 27398944/225],
    ![929061/2738, 10668259/2738, 3685465/104, 27398944/225],
    ![459151/1369, 10668259/2738, 3685465/104, 27398944/225]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 18 257027 := by
  refine ⟨?_, rank154 5402, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2760⟩⟩
  · intro i; fin_cases i
    · exact free4_1
    · exact free9_1
    · exact free17_1
    · exact free24_1
    · exact free32_1
    · exact free44_1
    · exact free54_1
    · exact free74_4
    · exact free84_1
    · exact free98_1
    · exact free137_1
    · exact free168_1
    · exact free126_1
    · exact free153_1
    · exact free199_1
    · exact free185_1
    · exact free212_1
    · exact free175_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [257020734, 332883294, 335134975, 333149596, 332571944, 333193919, 153760756, 153553789, 153521054, 153410196, 111163540, 69894504, 69720100, 70365464, 101419491, 101477070, 100000000, 100000000, 233626203], [1412050, 1035531, 1029352, 1034801, 1036386, 1034679, 2507642, 2511088, 2511633, 2513479, 3542278, 5742032, 5757464, 5704553, 3899862, 3897429, 3959851, 3959851, 1584901],
  ![124013461076460, 1608333973452, 210263582700, 5817318060], 142689457004723201⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,3,3,3,3,3,7,7,7,7,10,15,16,15,11,11,11,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 10668259/2738, 3685465/104, 27398944/225] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle114
end Z6969Source1891

end Merged_Z6969Pack0736

-- merged module Z6969Pack0737
section Merged_Z6969Pack0737

-- Source: Research6969.PrefixRescueDataMiddle114
section Z6969Source1892
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle114
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,18⟩
  bank i := ![bank236 21842, bank245 25059, bank245 26202, bank252 29839, bank252 30948, bank245 28917, bank270 39053, bank303 45637, bank303 49146, bank347 88754, bank332 84978] i
  reserve i := ![0, 1, 2, 3, 4, 4, 8, 10, 13, 32, 32] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257027
  seedFloor := 18

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank236 21842
    · exact rank245 25059
    · exact rank245 26202
    · exact rank252 29839
    · exact rank252 30948
    · exact rank245 28917
    · exact rank270 39053
    · exact rank303 45637
    · exact rank303 49146
    · exact rank347 88754
    · exact rank332 84978
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2045⟩
    · exact ⟨_, cover2046⟩
    · exact ⟨_, cover2047⟩
    · exact ⟨_, cover2048⟩
    · exact ⟨_, cover2050⟩
    · exact ⟨_, cover2049⟩
    · exact ⟨_, cover2051⟩
    · exact ⟨_, cover2052⟩
    · exact ⟨_, cover2053⟩
    · exact ⟨_, cover2055⟩
    · exact ⟨_, cover2054⟩

def price : EarlyPrice := ⟨2, 18, 10, 85/100, 80/100, ![622599280798, 78348340248, 12037546092, 668764668], 2835358220432591⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![8143/33, 36996/11, 96840/11, 509868/11] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle114
end Z6969Source1892

-- Source: Research6969.PrefixMiddleSaved114
section Z6969Source1893
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved114
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle114.price Lower6960.Prefix6969RescueData.Middle114.price :=
  ⟨335, 3896, 246, 3363, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle114.plan Lower6960.Prefix6969RescueData.Middle114.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 18 18 :=
  ⟨Lower6960.Prefix6969MainCases.Middle114.plan, Lower6960.Prefix6969MainCases.Middle114.price, Lower6960.Prefix6969MainCases.Middle114.valid, Lower6960.Prefix6969MainCases.Middle114.priced, Lower6960.Prefix6969MainCases.Middle114.sources,
   Lower6960.Prefix6969RescueData.Middle114.plan, Lower6960.Prefix6969RescueData.Middle114.price, Lower6960.Prefix6969RescueData.Middle114.sources, Lower6960.Prefix6969RescueData.Middle114.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved114
end Z6969Source1893

-- Source: Research6969.PrefixMainDataMiddle115
section Z6969Source1894
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle115
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 16, 21, 20, 30, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank4 1096, bank9 1210, bank17 1319, bank23 1429, bank26 1570, bank32 1683, bank44 1848, bank54 2149, bank74 2799, bank84 3942, bank112 2964, bank108 5498, bank120 12477, bank150 5281, bank210 8954, bank181 21723, bank174 26788, bank169 29097] i
  head := src2743
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![14801, 130330, 608327, 2374494],
    ![12303, 112337, 507634, 2047320],
    ![53398/9, 488182/9, 464288, 1739761],
    ![3599, 263593/8, 2389108/9, 1074608],
    ![60658/25, 564692/25, 321551/2, 664110],
    ![16211/9, 33567/2, 321551/2, 664110],
    ![18775/16, 10725, 304304/3, 379456],
    ![89110/121, 805250/121, 521260/7, 4618201/16],
    ![89110/121, 805250/121, 130147/2, 263106],
    ![63754/121, 1371303/242, 1264336/25, 3884841/16],
    ![63754/121, 1371303/242, 1264336/25, 8785296/49],
    ![24521/50, 416401/75, 1264336/25, 8785296/49],
    ![667406/1681, 416401/75, 1264336/25, 8785296/49],
    ![667406/1681, 8166248/1681, 36747088/841, 27888961/169],
    ![667406/1681, 5980135/1369, 107607416/2809, 11783464/81],
    ![474397/1369, 5980135/1369, 107607416/2809, 11783464/81],
    ![462882/1369, 5980135/1369, 107607416/2809, 11783464/81],
    ![459151/1369, 5980135/1369, 107607416/2809, 11783464/81]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 1 257027 := by
  refine ⟨?_, rank154 6768, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2743⟩⟩
  · intro i; fin_cases i
    · exact free4_1
    · exact free9_1
    · exact free17_1
    · exact free23_1
    · exact free26_1
    · exact free32_1
    · exact free44_1
    · exact free54_1
    · exact free74_4
    · exact free84_1
    · exact free112_1
    · exact free108_3
    · exact free120_1
    · exact free150_1
    · exact free210_1
    · exact free181_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨50/100, 60/100, [282047418, 366604032, 367389972, 366835848, 366362383, 367250716, 367115638, 156881649, 157144991, 157199284, 115270357, 87300349, 86969492, 91277614, 115567675, 131707753, 100000000, 226855144], [1283851, 942995, 940838, 942359, 943658, 941220, 941591, 2455685, 2451301, 2450397, 3400182, 4557449, 4574155, 4356624, 3391860, 2955626, 3959851, 1640644],
  ![120419247538080, 1615680945116, 204169629600, 5183200890], 157785489057495442⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,3,3,3,3,3,3,7,7,7,9,12,12,12,9,8,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 5980135/1369, 107607416/2809, 11783464/81] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle115
end Z6969Source1894

-- Source: Research6969.PrefixRescueDataMiddle115
section Z6969Source1895
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle115
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,1⟩
  bank i := ![bank245 84533, bank245 89172, bank245 94349, bank251 105447, bank252 110668, bank252 122234, bank270 152484, bank303 161404, bank315 191357, bank315 205621, bank302 177211] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 10, 13, 16, 13] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257027
  seedFloor := 1

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank245 84533
    · exact rank245 89172
    · exact rank245 94349
    · exact rank251 105447
    · exact rank252 110668
    · exact rank252 122234
    · exact rank270 152484
    · exact rank303 161404
    · exact rank315 191357
    · exact rank315 205621
    · exact rank302 177211
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1862⟩
    · exact ⟨_, cover1863⟩
    · exact ⟨_, cover1864⟩
    · exact ⟨_, cover1865⟩
    · exact ⟨_, cover1866⟩
    · exact ⟨_, cover1867⟩
    · exact ⟨_, cover1868⟩
    · exact ⟨_, cover1869⟩
    · exact ⟨_, cover1871⟩
    · exact ⟨_, cover1872⟩
    · exact ⟨_, cover1870⟩

def price : EarlyPrice := ⟨2, 1, 10, 100/100, 80/100, ![80134616120, 81819992543, 463377080, 463380647], 9243679971048177⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![2706/7, 206810/17, 416754/17, 205621/17] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle115
end Z6969Source1895

-- Source: Research6969.PrefixMiddleSaved115
section Z6969Source1896
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved115
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle115.price Lower6960.Prefix6969RescueData.Middle115.price :=
  ⟨335, 4368, 386, 12165, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle115.plan Lower6960.Prefix6969RescueData.Middle115.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 1 1 :=
  ⟨Lower6960.Prefix6969MainCases.Middle115.plan, Lower6960.Prefix6969MainCases.Middle115.price, Lower6960.Prefix6969MainCases.Middle115.valid, Lower6960.Prefix6969MainCases.Middle115.priced, Lower6960.Prefix6969MainCases.Middle115.sources,
   Lower6960.Prefix6969RescueData.Middle115.plan, Lower6960.Prefix6969RescueData.Middle115.price, Lower6960.Prefix6969RescueData.Middle115.sources, Lower6960.Prefix6969RescueData.Middle115.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved115
end Z6969Source1896

-- Source: Research6969.PrefixMiddleSelect2
section Z6969Source1897
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer
set_option maxHeartbeats 8000000

theorem choose2 (j : Fin 56) :
    ∃ l u : ℕ, l≤j.val+1 ∧ j.val+1≤u ∧ Nonempty (Case 2 l u) := by
  fin_cases j
  · exact ⟨1, 1, by decide, by decide, ⟨Saved115.data⟩⟩
  · exact ⟨2, 2, by decide, by decide, ⟨Saved98.data⟩⟩
  · exact ⟨3, 3, by decide, by decide, ⟨Saved99.data⟩⟩
  · exact ⟨4, 4, by decide, by decide, ⟨Saved100.data⟩⟩
  · exact ⟨5, 5, by decide, by decide, ⟨Saved101.data⟩⟩
  · exact ⟨6, 6, by decide, by decide, ⟨Saved102.data⟩⟩
  · exact ⟨7, 7, by decide, by decide, ⟨Saved103.data⟩⟩
  · exact ⟨8, 8, by decide, by decide, ⟨Saved104.data⟩⟩
  · exact ⟨9, 9, by decide, by decide, ⟨Saved105.data⟩⟩
  · exact ⟨10, 10, by decide, by decide, ⟨Saved106.data⟩⟩
  · exact ⟨11, 11, by decide, by decide, ⟨Saved107.data⟩⟩
  · exact ⟨12, 12, by decide, by decide, ⟨Saved108.data⟩⟩
  · exact ⟨13, 13, by decide, by decide, ⟨Saved109.data⟩⟩
  · exact ⟨14, 14, by decide, by decide, ⟨Saved110.data⟩⟩
  · exact ⟨15, 15, by decide, by decide, ⟨Saved111.data⟩⟩
  · exact ⟨16, 16, by decide, by decide, ⟨Saved112.data⟩⟩
  · exact ⟨17, 17, by decide, by decide, ⟨Saved113.data⟩⟩
  · exact ⟨18, 18, by decide, by decide, ⟨Saved114.data⟩⟩
  · exact ⟨19, 19, by decide, by decide, ⟨Saved76.data⟩⟩
  · exact ⟨20, 20, by decide, by decide, ⟨Saved77.data⟩⟩
  · exact ⟨21, 21, by decide, by decide, ⟨Saved78.data⟩⟩
  · exact ⟨22, 22, by decide, by decide, ⟨Saved79.data⟩⟩
  · exact ⟨23, 23, by decide, by decide, ⟨Saved80.data⟩⟩
  · exact ⟨24, 24, by decide, by decide, ⟨Saved81.data⟩⟩
  · exact ⟨25, 25, by decide, by decide, ⟨Saved82.data⟩⟩
  · exact ⟨26, 26, by decide, by decide, ⟨Saved83.data⟩⟩
  · exact ⟨27, 27, by decide, by decide, ⟨Saved84.data⟩⟩
  · exact ⟨28, 28, by decide, by decide, ⟨Saved85.data⟩⟩
  · exact ⟨29, 29, by decide, by decide, ⟨Saved86.data⟩⟩
  · exact ⟨30, 30, by decide, by decide, ⟨Saved87.data⟩⟩
  · exact ⟨31, 31, by decide, by decide, ⟨Saved88.data⟩⟩
  · exact ⟨32, 32, by decide, by decide, ⟨Saved89.data⟩⟩
  · exact ⟨33, 33, by decide, by decide, ⟨Saved90.data⟩⟩
  · exact ⟨34, 34, by decide, by decide, ⟨Saved91.data⟩⟩
  · exact ⟨35, 35, by decide, by decide, ⟨Saved92.data⟩⟩
  · exact ⟨36, 36, by decide, by decide, ⟨Saved93.data⟩⟩
  · exact ⟨37, 37, by decide, by decide, ⟨Saved94.data⟩⟩
  · exact ⟨38, 38, by decide, by decide, ⟨Saved95.data⟩⟩
  · exact ⟨39, 39, by decide, by decide, ⟨Saved96.data⟩⟩
  · exact ⟨40, 40, by decide, by decide, ⟨Saved97.data⟩⟩
  · exact ⟨41, 50, by decide, by decide, ⟨Saved74.data⟩⟩
  · exact ⟨41, 50, by decide, by decide, ⟨Saved74.data⟩⟩
  · exact ⟨41, 50, by decide, by decide, ⟨Saved74.data⟩⟩
  · exact ⟨41, 50, by decide, by decide, ⟨Saved74.data⟩⟩
  · exact ⟨41, 50, by decide, by decide, ⟨Saved74.data⟩⟩
  · exact ⟨41, 50, by decide, by decide, ⟨Saved74.data⟩⟩
  · exact ⟨41, 50, by decide, by decide, ⟨Saved74.data⟩⟩
  · exact ⟨41, 50, by decide, by decide, ⟨Saved74.data⟩⟩
  · exact ⟨41, 50, by decide, by decide, ⟨Saved74.data⟩⟩
  · exact ⟨41, 50, by decide, by decide, ⟨Saved74.data⟩⟩
  · exact ⟨51, 56, by decide, by decide, ⟨Saved75.data⟩⟩
  · exact ⟨51, 56, by decide, by decide, ⟨Saved75.data⟩⟩
  · exact ⟨51, 56, by decide, by decide, ⟨Saved75.data⟩⟩
  · exact ⟨51, 56, by decide, by decide, ⟨Saved75.data⟩⟩
  · exact ⟨51, 56, by decide, by decide, ⟨Saved75.data⟩⟩
  · exact ⟨51, 56, by decide, by decide, ⟨Saved75.data⟩⟩

end Lower6960.Prefix6969MiddleTransfer
end Z6969Source1897

-- Source: Research6969.PhysicalChecks182
section Z6969Source1898
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2912 : Request := ⟨⟨⟨6900,9621,2174,51153⟩,10196763128627200,242895948111878⟩,245,4,1,514055,49⟩
theorem cover2912 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2912) 2557 2412 [2413, 2418, 2431, 2464, 2550, 2557] := triangleCover (by decide +kernel)
def src2913 : Request := ⟨⟨⟨275,383,87,1930⟩,658033868800,625236061⟩,0,4,1,514055,53⟩
theorem cover2913 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2913) 2557 2412 [2421, 2455, 2557] := triangleCover (by decide +kernel)
def src2914 : Request := ⟨⟨⟨325,453,98,2243⟩,1045036793856,1174588250⟩,1,4,1,514055,53⟩
theorem cover2914 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2914) 2557 2412 [2419, 2446, 2534, 2557] := triangleCover (by decide +kernel)
def src2915 : Request := ⟨⟨⟨325,453,98,2387⟩,1045036793856,1174588250⟩,2,4,1,514055,53⟩
theorem cover2915 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2915) 2557 2412 [2419, 2445, 2530, 2557] := triangleCover (by decide +kernel)
def src2916 : Request := ⟨⟨⟨325,453,102,2468⟩,1076928184320,1211360939⟩,3,4,1,514055,53⟩
theorem cover2916 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2916) 2557 2412 [2419, 2445, 2529, 2557] := triangleCover (by decide +kernel)
def src2917 : Request := ⟨⟨⟨400,558,123,2767⟩,1971918995456,2734096379⟩,4,4,1,514055,53⟩
theorem cover2917 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2917) 2557 2412 [2418, 2439, 2504, 2557] := triangleCover (by decide +kernel)
def src2918 : Request := ⟨⟨⟨400,558,123,3079⟩,1971918995456,2734096379⟩,6,4,1,514055,53⟩
theorem cover2918 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2918) 2557 2412 [2418, 2439, 2504, 2557] := triangleCover (by decide +kernel)
def src2919 : Request := ⟨⟨⟨470,655,148,3423⟩,3250957582336,5279398867⟩,8,4,1,514055,53⟩
theorem cover2919 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2919) 2557 2412 [2417, 2435, 2489, 2557] := triangleCover (by decide +kernel)
def src2920 : Request := ⟨⟨⟨690,962,212,5025⟩,10065769922560,23997864317⟩,16,4,1,514055,53⟩
theorem cover2920 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2920) 2557 2412 [2415, 2427, 2461, 2557] := triangleCover (by decide +kernel)
def src2921 : Request := ⟨⟨⟨1000,1394,307,8064⟩,30557599170560,105471636407⟩,32,4,1,514055,53⟩
theorem cover2921 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2921) 2557 2412 [2414, 2423, 2447, 2513, 2557] := triangleCover (by decide +kernel)
def src2922 : Request := ⟨⟨⟨1450,2022,457,11316⟩,94890063298560,475487789910⟩,50,4,1,514055,53⟩
theorem cover2922 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2922) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src2923 : Request := ⟨⟨⟨4800,6692,1512,37604⟩,3433136573644800,56871238465897⟩,190,4,1,514055,53⟩
theorem cover2923 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2923) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2924 : Request := ⟨⟨⟨556,772,170,6321⟩,5255817068544,9968090926⟩,10,4,2,514054,2⟩
theorem cover2924 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2924) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
def src2925 : Request := ⟨⟨⟨556,772,170,6247⟩,5255817068544,9968090926⟩,10,4,2,514054,3⟩
theorem cover2925 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2925) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
def src2926 : Request := ⟨⟨⟨556,772,170,6099⟩,5255817068544,9968090926⟩,10,4,2,514054,5⟩
theorem cover2926 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2926) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
def src2927 : Request := ⟨⟨⟨556,772,170,6027⟩,5255817068544,9968090926⟩,10,4,2,514054,6⟩
theorem cover2927 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2927) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1898

-- Source: Research6969.PrefixMainDataMiddle0
section Z6969Source1899
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle0
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 5, 7, 10, 15, 21, 15, 25, 21, 30, 40, 40, 65, 65, 75, 75] i
  bank i := ![bank3 1102, bank10 1206, bank16 1326, bank24 1404, bank33 1655, bank42 1886, bank52 2212, bank65 2772, bank83 3955, bank93 2467, bank89 5201, bank123 3043, bank168 3916, bank122 10626, bank147 5174, bank199 7608, bank158 18445, bank211 8704, bank171 27879] i
  head := src2924
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![14755, 129567, 600942, 2346791],
    ![24861/2, 108144, 1973997/4, 3811563/2],
    ![53228/9, 157313/3, 464100, 1758276],
    ![29433/8, 510483/16, 770054/3, 986076],
    ![5468/3, 292379/18, 660749/4, 10461255/16],
    ![36739/32, 330977/32, 909052/9, 3556996/9],
    ![86036/121, 774263/121, 499501/7, 285348],
    ![86036/121, 774263/121, 499501/7, 285348],
    ![254619/484, 2669989/484, 441476/9, 15642025/64],
    ![254619/484, 2669989/484, 441476/9, 6086089/25],
    ![254619/484, 2669989/484, 441476/9, 6086089/25],
    ![254619/484, 656173/121, 441476/9, 12823202/75],
    ![254619/484, 656173/121, 441476/9, 1687707/11],
    ![41249/100, 656173/121, 441476/9, 1687707/11],
    ![41249/100, 964433/200, 2167967/49, 1687707/11],
    ![41249/100, 1936810/441, 193674/5, 72135252/529],
    ![480716/1323, 1936810/441, 193674/5, 72135252/529],
    ![480716/1323, 22923908/5329, 103097365/2704, 72135252/529],
    ![1826342/5329, 22923908/5329, 103097365/2704, 72135252/529]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 3 1 385541 := by
  refine ⟨?_, rank154 6321, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2924⟩⟩
  · intro i; fin_cases i
    · exact free3_1
    · exact free10_1
    · exact free16_1
    · exact free24_1
    · exact free33_3
    · exact free42_4
    · exact free52_1
    · exact free65_1
    · exact free83_3
    · exact free93_1
    · exact free89_5
    · exact free123_1
    · exact free168_1
    · exact free122_1
    · exact free147_1
    · exact free199_1
    · exact free158_1
    · exact free211_1
    · exact free171_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 80/100, [273425829, 356396580, 357398106, 357571189, 357751774, 358365782, 188859074, 188866086, 188900511, 125852357, 87998777, 125917758, 76864796, 73151109, 78190865, 94048835, 109203280, 147731751, 230363174], [1328015, 971006, 968258, 967783, 967287, 965602, 2007488, 2007403, 2006988, 3103983, 4522183, 3102152, 5209256, 5482866, 5117553, 4216695, 3610416, 2608014, 1611764],
  ![122281380022680, 1611874418956, 207326856600, 5218715760], 155045151953900526⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,3,3,3,3,3,6,6,6,9,12,9,14,15,14,12,10,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 22923908/5329, 103097365/2704, 72135252/529] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle0
end Z6969Source1899

-- Source: Research6969.PhysicalChecks145
section Z6969Source1900
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2320 : Request := ⟨⟨⟨1200,1674,355,38163⟩,51296765214720,212765123946⟩,4,3,1,385541,1⟩
theorem cover2320 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2320) 2557 2412 [2414, 2422, 2444, 2505, 2557] := triangleCover (by decide +kernel)
def src2321 : Request := ⟨⟨⟨1450,2023,436,43388⟩,91566841790464,459151377566⟩,6,3,1,385541,1⟩
theorem cover2321 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2321) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src2322 : Request := ⟨⟨⟨1750,2442,527,50201⟩,161065121873920,975196209190⟩,8,3,1,385541,1⟩
theorem cover2322 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2322) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2323 : Request := ⟨⟨⟨1750,2442,527,53481⟩,161065121873920,975196209190⟩,10,3,1,385541,1⟩
theorem cover2323 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2323) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2324 : Request := ⟨⟨⟨2100,2930,632,62415⟩,278060332482560,2019119590628⟩,13,3,1,385541,1⟩
theorem cover2324 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2324) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src2325 : Request := ⟨⟨⟨3200,4465,963,87335⟩,983050615259136,10877088344236⟩,20,3,1,385541,1⟩
theorem cover2325 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2325) 2557 2412 [2413, 2418, 2431, 2465, 2555, 2557] := triangleCover (by decide +kernel)
def src2326 : Request := ⟨⟨⟨5700,7953,1716,165034⟩,5553838907981824,109428971647179⟩,50,3,1,385541,1⟩
theorem cover2326 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2326) 2557 2412 [2413, 2418, 2431, 2465, 2553, 2557] := triangleCover (by decide +kernel)
def src2327 : Request := ⟨⟨⟨1000,1395,296,27818⟩,29722184515584,102755930405⟩,0,3,1,385541,2⟩
theorem cover2327 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2327) 2557 2412 [2415, 2426, 2456, 2540, 2557] := triangleCover (by decide +kernel)
def src2328 : Request := ⟨⟨⟨1000,1395,301,28739⟩,30103476895744,104105680031⟩,1,3,1,385541,2⟩
theorem cover2328 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2328) 2557 2412 [2414, 2423, 2447, 2513, 2557] := triangleCover (by decide +kernel)
def src2329 : Request := ⟨⟨⟨1000,1395,301,30442⟩,30103476895744,104105680031⟩,2,3,1,385541,2⟩
theorem cover2329 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2329) 2557 2412 [2414, 2423, 2447, 2513, 2557] := triangleCover (by decide +kernel)
def src2330 : Request := ⟨⟨⟨1200,1674,361,35783⟩,51955677528064,215563369662⟩,4,3,1,385541,2⟩
theorem cover2330 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2330) 2557 2412 [2414, 2422, 2444, 2504, 2557] := triangleCover (by decide +kernel)
def src2331 : Request := ⟨⟨⟨1450,2023,436,41688⟩,91566841790464,459151377566⟩,6,3,1,385541,2⟩
theorem cover2331 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2331) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src2332 : Request := ⟨⟨⟨1750,2442,527,51382⟩,161065121873920,975196209190⟩,10,3,1,385541,2⟩
theorem cover2332 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2332) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2333 : Request := ⟨⟨⟨2100,2930,622,61388⟩,274699477319680,1994139134137⟩,13,3,1,385541,2⟩
theorem cover2333 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2333) 2557 2412 [2414, 2422, 2443, 2499, 2557] := triangleCover (by decide +kernel)
def src2334 : Request := ⟨⟨⟨2600,3628,783,76682⟩,527755772952576,4745819470168⟩,20,3,1,385541,2⟩
theorem cover2334 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2334) 2557 2412 [2413, 2418, 2432, 2468, 2557] := triangleCover (by decide +kernel)
def src2335 : Request := ⟨⟨⟨3200,4465,963,91195⟩,983050615259136,10877088344236⟩,25,3,1,385541,2⟩
theorem cover2335 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2335) 2557 2412 [2413, 2418, 2431, 2465, 2555, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1900

-- Source: Research6969.PrefixRescueDataMiddle0
section Z6969Source1901
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle0
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,3,1,1⟩
  bank i := ![bank221 28329, bank221 29915, bank220 32425, bank226 38163, bank236 43388, bank245 53481, bank245 50201, bank252 62415, bank303 87335, bank345 165034] i
  reserve i := ![0, 1, 2, 4, 6, 10, 8, 13, 20, 50] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385541
  seedFloor := 1

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank221 28329
    · exact rank221 29915
    · exact rank220 32425
    · exact rank226 38163
    · exact rank236 43388
    · exact rank245 53481
    · exact rank245 50201
    · exact rank252 62415
    · exact rank303 87335
    · exact rank345 165034
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2317⟩
    · exact ⟨_, cover2318⟩
    · exact ⟨_, cover2319⟩
    · exact ⟨_, cover2320⟩
    · exact ⟨_, cover2321⟩
    · exact ⟨_, cover2323⟩
    · exact ⟨_, cover2322⟩
    · exact ⟨_, cover2324⟩
    · exact ⟨_, cover2325⟩
    · exact ⟨_, cover2326⟩

def price : EarlyPrice := ⟨3, 1, 9, 100/100, 80/100, ![64317050480, 131064619566, 668759520, 1337517324], 2226378109193430⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![3795/17, 166750/51, 167685/17, 165034/51] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle0
end Z6969Source1901

-- Source: Research6969.PrefixMiddleSaved0
section Z6969Source1902
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved0
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle0.price Lower6960.Prefix6969RescueData.Middle0.price :=
  ⟨342, 4301, 223, 3269, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle0.plan Lower6960.Prefix6969RescueData.Middle0.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 3 1 1 :=
  ⟨Lower6960.Prefix6969MainCases.Middle0.plan, Lower6960.Prefix6969MainCases.Middle0.price, Lower6960.Prefix6969MainCases.Middle0.valid, Lower6960.Prefix6969MainCases.Middle0.priced, Lower6960.Prefix6969MainCases.Middle0.sources,
   Lower6960.Prefix6969RescueData.Middle0.plan, Lower6960.Prefix6969RescueData.Middle0.price, Lower6960.Prefix6969RescueData.Middle0.sources, Lower6960.Prefix6969RescueData.Middle0.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved0
end Z6969Source1902

-- Source: Research6969.PrefixMainDataMiddle1
section Z6969Source1903
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle1
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 21, 13, 21, 40, 40, 65, 65, 75, 75] i
  bank i := ![bank3 1102, bank10 1206, bank16 1326, bank24 1404, bank28 1523, bank33 1655, bank42 1886, bank52 2212, bank65 2772, bank83 3955, bank83 2285, bank123 3043, bank122 10626, bank147 5174, bank199 7608, bank158 18445, bank211 8704, bank171 27879] i
  head := src2925
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![14880, 129226, 601532, 2310439],
    ![24861/2, 107478, 1961787/4, 3766941/2],
    ![53228/9, 52117, 464100, 1758276],
    ![29433/8, 507301/16, 2295806/9, 974532],
    ![62542/25, 546272/25, 312215/2, 9514181/16],
    ![5468/3, 290603/18, 312215/2, 9514181/16],
    ![36739/32, 328979/32, 909052/9, 3556996/9],
    ![86036/121, 769601/121, 3475565/49, 1974052/7],
    ![86036/121, 769601/121, 3475565/49, 1974052/7],
    ![254619/484, 2657113/484, 2195836/45, 15642025/64],
    ![254619/484, 2657113/484, 2195836/45, 15642025/64],
    ![254619/484, 651733/121, 2195836/45, 38019242/225],
    ![41249/100, 651733/121, 2195836/45, 38019242/225],
    ![41249/100, 958291/200, 2154277/49, 158404],
    ![41249/100, 13090/3, 25977418/675, 71290764/529],
    ![480716/1323, 13090/3, 25977418/675, 71290764/529],
    ![480716/1323, 22776796/5329, 102441059/2704, 71290764/529],
    ![1826342/5329, 22776796/5329, 102441059/2704, 71290764/529]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 3 2 385541 := by
  refine ⟨?_, rank154 6247, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2925⟩⟩
  · intro i; fin_cases i
    · exact free3_1
    · exact free10_1
    · exact free16_1
    · exact free24_1
    · exact free28_1
    · exact free33_3
    · exact free42_4
    · exact free52_1
    · exact free65_1
    · exact free83_3
    · exact free83_2
    · exact free123_1
    · exact free122_1
    · exact free147_1
    · exact free199_1
    · exact free158_1
    · exact free211_1
    · exact free171_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 80/100, [273009852, 357282902, 357279163, 357133150, 355390221, 356594952, 356888435, 162501166, 162477607, 162381925, 162428242, 78776582, 78759359, 77611820, 89848447, 103831948, 147236918, 230054071], [1330146, 968574, 968584, 968985, 973768, 970462, 969656, 2362131, 2362523, 2364116, 2363345, 5077049, 5078240, 5157596, 4428787, 3797910, 2616252, 1614309],
  ![122117301968220, 1612209730784, 207048663900, 5259550440], 154442091096104741⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [4,3,3,3,3,3,3,7,7,7,7,14,14,14,12,11,7,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![1826342/5329, 22776796/5329, 102441059/2704, 71290764/529] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle1
end Z6969Source1903

end Merged_Z6969Pack0737
