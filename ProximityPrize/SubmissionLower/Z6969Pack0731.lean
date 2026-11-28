import ProximityPrize.SubmissionLower.R6970PhysicalCoverCompact
import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.Z6969FastCeil
import ProximityPrize.SubmissionLower.Z6969Pack0730
import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969Pack0724
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.Z6969Pack0575
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.Z6969Pack0605
import ProximityPrize.SubmissionLower.Z6969Pack0624
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice

set_option Elab.async false

-- merged module Z6969Pack0731
section Merged_Z6969Pack0731

-- Source: Research6969.PrefixMiddleSaved94
section Z6969Source1820
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved94
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle94.price Lower6960.Prefix6969RescueData.Middle94.price :=
  ⟨335, 3469, 80, 888, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle94.plan Lower6960.Prefix6969RescueData.Middle94.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 37 37 :=
  ⟨Lower6960.Prefix6969MainCases.Middle94.plan, Lower6960.Prefix6969MainCases.Middle94.price, Lower6960.Prefix6969MainCases.Middle94.valid, Lower6960.Prefix6969MainCases.Middle94.priced, Lower6960.Prefix6969MainCases.Middle94.sources,
   Lower6960.Prefix6969RescueData.Middle94.plan, Lower6960.Prefix6969RescueData.Middle94.price, Lower6960.Prefix6969RescueData.Middle94.sources, Lower6960.Prefix6969RescueData.Middle94.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved94
end Z6969Source1820

-- Source: Research6969.PrefixMainDataMiddle95
section Z6969Source1821
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle95
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 7, 10, 10, 10, 18, 13, 16, 20, 23, 30, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank6 1073, bank13 1183, bank18 1295, bank24 1404, bank35 1600, bank44 1848, bank53 2196, bank42 2862, bank61 2044, bank69 3442, bank72 2320, bank95 2576, bank112 2964, bank138 3222, bank144 3940, bank126 11206, bank164 5088, bank214 8650, bank183 20877, bank174 26788, bank169 29097] i
  head := src2780
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![15734, 123048, 565887, 1952127],
    ![25417/2, 89035, 404299, 1399489],
    ![54680/9, 129250/3, 404299, 2713025/2],
    ![29433/8, 209425/8, 1896748/9, 653640],
    ![5710/3, 13375, 545535/4, 419000],
    ![18775/16, 272305/32, 2461586/25, 1548624/5],
    ![86808/121, 641480/121, 2885272/49, 4822416/25],
    ![73478/121, 641480/121, 2885272/49, 4822416/25],
    ![73478/121, 641480/121, 2885272/49, 1223480/7],
    ![73478/121, 97760/19, 2478240/49, 1223480/7],
    ![73478/121, 97760/19, 2478240/49, 1223480/7],
    ![73478/121, 97760/19, 2478240/49, 1223480/7],
    ![73478/121, 1954700/441, 187473/4, 549081/4],
    ![73478/121, 1954700/441, 187473/4, 549081/4],
    ![73478/121, 43137/10, 5240200/121, 247629/2],
    ![1355575/3362, 43137/10, 5240200/121, 247629/2],
    ![1355575/3362, 6493400/1681, 1824174/49, 2876416/25],
    ![1355575/3362, 4743795/1369, 85372210/2601, 507409/5],
    ![954471/2738, 4743795/1369, 85372210/2601, 507409/5],
    ![462882/1369, 4743795/1369, 85372210/2601, 507409/5],
    ![459151/1369, 4743795/1369, 85372210/2601, 507409/5]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 38 257027 := by
  refine ⟨?_, rank154 4190, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2780⟩⟩
  · intro i; fin_cases i
    · exact free6_1
    · exact free13_1
    · exact free18_1
    · exact free24_1
    · exact free35_1
    · exact free44_1
    · exact free53_1
    · exact free42_6
    · exact free61_1
    · exact free69_1
    · exact free72_1
    · exact free95_1
    · exact free112_1
    · exact free138_1
    · exact free144_1
    · exact free126_1
    · exact free164_1
    · exact free214_1
    · exact free183_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [236201146, 303758741, 303204053, 303101789, 304151149, 302401616, 303053190, 303857789, 162340771, 162283391, 162314381, 162215736, 81623961, 81623719, 64699093, 77678603, 91198772, 91187465, 118025740, 100000000, 218952652], [1563702, 1172634, 1175476, 1176000, 1170624, 1179586, 1176249, 1172127, 2364801, 2365756, 2365240, 2366883, 4891970, 4891985, 6223318, 5152978, 4360605, 4361175, 3323057, 3959851, 1705702],
  ![116224446734640, 1624255286648, 197057386800, 5188616580], 126067014706634511⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [5,4,4,4,4,4,4,4,7,7,7,7,13,13,17,14,12,12,9,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 4743795/1369, 85372210/2601, 507409/5] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle95
end Z6969Source1821

-- Source: Research6969.PhysicalChecks142
section Z6969Source1822
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2272 : Request := ⟨⟨⟨6900,9625,2118,48910⟩,9997036108906496,238335796784464⟩,145,2,1,257027,38⟩
theorem cover2272 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2272) 2557 2412 [2413, 2418, 2431, 2465, 2552, 2557] := triangleCover (by decide +kernel)
def src2273 : Request := ⟨⟨⟨470,655,144,3162⟩,3184589537280,5168862572⟩,0,2,1,257027,39⟩
theorem cover2273 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2273) 2557 2412 [2417, 2435, 2489, 2557] := triangleCover (by decide +kernel)
def src2274 : Request := ⟨⟨⟨560,781,176,3599⟩,5482316038144,10627925923⟩,1,2,1,257027,39⟩
theorem cover2274 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2274) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
def src2275 : Request := ⟨⟨⟨560,781,172,3784⟩,5388141854720,10440670587⟩,2,2,1,257027,39⟩
theorem cover2275 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2275) 2557 2412 [2416, 2431, 2474, 2557] := triangleCover (by decide +kernel)
def src2276 : Request := ⟨⟨⟨560,781,172,3948⟩,5388141854720,10440670587⟩,3,2,1,257027,39⟩
theorem cover2276 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2276) 2557 2412 [2416, 2431, 2474, 2557] := triangleCover (by decide +kernel)
def src2277 : Request := ⟨⟨⟨690,962,212,4536⟩,10065769922560,23997864317⟩,4,2,1,257027,39⟩
theorem cover2277 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2277) 2557 2412 [2415, 2427, 2461, 2557] := triangleCover (by decide +kernel)
def src2278 : Request := ⟨⟨⟨690,962,212,4847⟩,10065769922560,23997864317⟩,6,2,1,257027,39⟩
theorem cover2278 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2278) 2557 2412 [2415, 2427, 2461, 2557] := triangleCover (by decide +kernel)
def src2279 : Request := ⟨⟨⟨825,1151,260,5893⟩,17518948515840,50057971890⟩,10,2,1,257027,39⟩
theorem cover2279 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2279) 2557 2412 [2415, 2426, 2457, 2543, 2557] := triangleCover (by decide +kernel)
def src2280 : Request := ⟨⟨⟨1450,2022,445,10451⟩,92998964346880,465769321795⟩,25,2,1,257027,39⟩
theorem cover2280 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2280) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src2281 : Request := ⟨⟨⟨2100,2929,662,14755⟩,288013660979200,2090961110089⟩,40,2,1,257027,39⟩
theorem cover2281 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2281) 2557 2412 [2413, 2419, 2435, 2477, 2557] := triangleCover (by decide +kernel)
def src2282 : Request := ⟨⟨⟨3950,5510,1213,28414⟩,1877062482395136,25622281045803⟩,85,2,1,257027,39⟩
theorem cover2282 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2282) 2557 2412 [2413, 2418, 2431, 2465, 2554, 2557] := triangleCover (by decide +kernel)
def src2283 : Request := ⟨⟨⟨8300,11577,2548,59758⟩,17399709518790656,498847383098023⟩,190,2,1,257027,39⟩
theorem cover2283 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2283) 2557 2412 [2413, 2418, 2431, 2464, 2550, 2557] := triangleCover (by decide +kernel)
def src2284 : Request := ⟨⟨⟨470,655,144,3098⟩,3184589537280,5168862572⟩,0,2,1,257027,40⟩
theorem cover2284 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2284) 2557 2412 [2417, 2435, 2489, 2557] := triangleCover (by decide +kernel)
def src2285 : Request := ⟨⟨⟨470,655,144,3249⟩,3184589537280,5168862572⟩,1,2,1,257027,40⟩
theorem cover2285 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2285) 2557 2412 [2417, 2435, 2489, 2557] := triangleCover (by decide +kernel)
def src2286 : Request := ⟨⟨⟨560,781,169,3801⟩,5316921262080,10299257375⟩,2,2,1,257027,40⟩
theorem cover2286 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2286) 2557 2412 [2416, 2431, 2475, 2557] := triangleCover (by decide +kernel)
def src2287 : Request := ⟨⟨⟨560,781,176,3810⟩,5482316038144,10627925923⟩,3,2,1,257027,40⟩
theorem cover2287 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2287) 2557 2412 [2416, 2431, 2474, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1822

-- Source: Research6969.PrefixRescueDataMiddle95
section Z6969Source1823
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle95
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,38⟩
  bank i := ![bank142 3234, bank155 3813, bank156 3872, bank193 4489, bank192 4772, bank193 4974, bank204 5778, bank228 8362, bank243 11522, bank268 18408, bank353 48910] i
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 16, 25, 50, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257027
  seedFloor := 38

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank142 3234
    · exact rank155 3813
    · exact rank156 3872
    · exact rank193 4489
    · exact rank192 4772
    · exact rank193 4974
    · exact rank204 5778
    · exact rank228 8362
    · exact rank243 11522
    · exact rank268 18408
    · exact rank353 48910
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2262⟩
    · exact ⟨_, cover2263⟩
    · exact ⟨_, cover2264⟩
    · exact ⟨_, cover2265⟩
    · exact ⟨_, cover2266⟩
    · exact ⟨_, cover2267⟩
    · exact ⟨_, cover2268⟩
    · exact ⟨_, cover2269⟩
    · exact ⟨_, cover2270⟩
    · exact ⟨_, cover2271⟩
    · exact ⟨_, cover2272⟩

def price : EarlyPrice := ⟨2, 38, 10, 65/100, 60/100, ![724318020910, 130234023837, 31365887718, 825433314], 647187357276615⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![11743/146, 64697/73, 231785/73, 12730] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle95
end Z6969Source1823

-- Source: Research6969.PrefixMiddleSaved95
section Z6969Source1824
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved95
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle95.price Lower6960.Prefix6969RescueData.Middle95.price :=
  ⟨335, 3465, 80, 886, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle95.plan Lower6960.Prefix6969RescueData.Middle95.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 38 38 :=
  ⟨Lower6960.Prefix6969MainCases.Middle95.plan, Lower6960.Prefix6969MainCases.Middle95.price, Lower6960.Prefix6969MainCases.Middle95.valid, Lower6960.Prefix6969MainCases.Middle95.priced, Lower6960.Prefix6969MainCases.Middle95.sources,
   Lower6960.Prefix6969RescueData.Middle95.plan, Lower6960.Prefix6969RescueData.Middle95.price, Lower6960.Prefix6969RescueData.Middle95.sources, Lower6960.Prefix6969RescueData.Middle95.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved95
end Z6969Source1824

-- Source: Research6969.PrefixMainDataMiddle96
section Z6969Source1825
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle96
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 7, 10, 10, 10, 18, 13, 16, 20, 23, 30, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank6 1073, bank13 1183, bank18 1295, bank24 1404, bank35 1600, bank44 1848, bank53 2196, bank42 2862, bank61 2044, bank69 3442, bank72 2320, bank95 2576, bank112 2964, bank138 3222, bank144 3940, bank126 11206, bank165 5082, bank214 8650, bank183 20877, bank174 26788, bank169 29097] i
  head := src2781
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![15734, 122868, 565077, 1946412],
    ![25417/2, 354475/4, 402409, 1399489],
    ![54680/9, 128650/3, 402409, 5367775/4],
    ![29433/8, 416915/16, 1888018/9, 646620],
    ![5710/3, 26625/2, 1085985/8, 414500],
    ![18775/16, 542135/64, 2450471/25, 1531992/5],
    ![86808/121, 638600/121, 410356/7, 4822416/25],
    ![73478/121, 638600/121, 410356/7, 4822416/25],
    ![73478/121, 638600/121, 410356/7, 1210340/7],
    ![73478/121, 1850060/361, 2478240/49, 1210340/7],
    ![73478/121, 1850060/361, 2478240/49, 1210340/7],
    ![73478/121, 1850060/361, 2478240/49, 1210340/7],
    ![73478/121, 277790/63, 187473/4, 549081/4],
    ![73478/121, 277790/63, 187473/4, 549081/4],
    ![73478/121, 85827/20, 5240200/121, 489939/4],
    ![1355575/3362, 85827/20, 5240200/121, 489939/4],
    ![1355575/3362, 6473320/1681, 1813971/49, 2869636/25],
    ![1355575/3362, 4720485/1369, 84957355/2601, 1003919/10],
    ![954471/2738, 4720485/1369, 84957355/2601, 1003919/10],
    ![462882/1369, 4720485/1369, 84957355/2601, 1003919/10],
    ![459151/1369, 4720485/1369, 84957355/2601, 1003919/10]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 39 257027 := by
  refine ⟨?_, rank154 4145, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2781⟩⟩
  · intro i; fin_cases i
    · exact free6_1
    · exact free13_1
    · exact free18_1
    · exact free24_1
    · exact free35_1
    · exact free44_1
    · exact free53_1
    · exact free42_6
    · exact free61_1
    · exact free69_1
    · exact free72_1
    · exact free95_1
    · exact free112_1
    · exact free138_1
    · exact free144_1
    · exact free126_1
    · exact free165_1
    · exact free214_1
    · exact free183_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [235247056, 302213394, 301778032, 301687162, 303032913, 303021817, 302850678, 303316099, 164106333, 163824266, 164154650, 163965209, 82853478, 82815457, 64618140, 78338597, 92139058, 92139228, 117636314, 100000000, 218753186], [1571557, 1180551, 1182781, 1183246, 1176353, 1176409, 1177286, 1174902, 2335408, 2340104, 2334603, 2337757, 4818866, 4821127, 6231626, 5107337, 4313126, 4313118, 3333957, 3959851, 1707344],
  ![116118566192520, 1624471846744, 196877867400, 5131451360], 125395010031808548⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [5,4,4,4,4,4,4,4,7,7,7,7,13,13,17,14,12,12,9,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 4720485/1369, 84957355/2601, 1003919/10] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle96
end Z6969Source1825

-- Source: Research6969.PrefixRescueDataMiddle96
section Z6969Source1826
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle96
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,39⟩
  bank i := ![bank142 3162, bank157 3599, bank156 3784, bank156 3948, bank193 4536, bank193 4847, bank205 5893, bank233 10451, bank250 14755, bank310 28414, bank365 59758] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 25, 40, 85, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257027
  seedFloor := 39

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank142 3162
    · exact rank157 3599
    · exact rank156 3784
    · exact rank156 3948
    · exact rank193 4536
    · exact rank193 4847
    · exact rank205 5893
    · exact rank233 10451
    · exact rank250 14755
    · exact rank310 28414
    · exact rank365 59758
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2273⟩
    · exact ⟨_, cover2274⟩
    · exact ⟨_, cover2275⟩
    · exact ⟨_, cover2276⟩
    · exact ⟨_, cover2277⟩
    · exact ⟨_, cover2278⟩
    · exact ⟨_, cover2279⟩
    · exact ⟨_, cover2280⟩
    · exact ⟨_, cover2281⟩
    · exact ⟨_, cover2282⟩
    · exact ⟨_, cover2283⟩

def price : EarlyPrice := ⟨2, 39, 10, 65/100, 70/100, ![908256822328, 160520079598, 38726837968, 993014204], 693659521760253⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![14125/191, 159130/191, 571019/191, 2330562/191] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle96
end Z6969Source1826

-- Source: Research6969.PrefixMiddleSaved96
section Z6969Source1827
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved96
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle96.price Lower6960.Prefix6969RescueData.Middle96.price :=
  ⟨335, 3448, 73, 833, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle96.plan Lower6960.Prefix6969RescueData.Middle96.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 39 39 :=
  ⟨Lower6960.Prefix6969MainCases.Middle96.plan, Lower6960.Prefix6969MainCases.Middle96.price, Lower6960.Prefix6969MainCases.Middle96.valid, Lower6960.Prefix6969MainCases.Middle96.priced, Lower6960.Prefix6969MainCases.Middle96.sources,
   Lower6960.Prefix6969RescueData.Middle96.plan, Lower6960.Prefix6969RescueData.Middle96.price, Lower6960.Prefix6969RescueData.Middle96.sources, Lower6960.Prefix6969RescueData.Middle96.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved96
end Z6969Source1827

-- Source: Research6969.PrefixMainDataMiddle97
section Z6969Source1828
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.Middle97
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 7, 10, 10, 10, 18, 13, 16, 20, 23, 30, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank6 1073, bank13 1183, bank18 1295, bank24 1404, bank35 1600, bank44 1848, bank53 2196, bank42 2862, bank61 2044, bank69 3442, bank72 2320, bank95 2576, bank112 2964, bank138 3222, bank144 3940, bank131 10228, bank164 5088, bank214 8650, bank186 19684, bank174 26788, bank169 29097] i
  head := src2782
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![15734, 122692, 564285, 1940824],
    ![25417/2, 352847/4, 400561, 1399489],
    ![54680/9, 384190/9, 400561, 5310795/4],
    ![29433/8, 415023/16, 626494/3, 639756],
    ![5710/3, 238525/18, 1081013/8, 410100],
    ![18775/16, 539715/64, 2439603/25, 7578648/25],
    ![86808/121, 635784/121, 2859996/49, 4822416/25],
    ![73478/121, 635784/121, 2859996/49, 4822416/25],
    ![73478/121, 635784/121, 2859996/49, 1197492/7],
    ![73478/121, 1842844/361, 2478240/49, 1197492/7],
    ![73478/121, 1842844/361, 2478240/49, 1197492/7],
    ![73478/121, 1842844/361, 2478240/49, 1197492/7],
    ![73478/121, 214954/49, 187473/4, 549081/4],
    ![73478/121, 214954/49, 187473/4, 549081/4],
    ![73478/121, 1280849/300, 3461307/80, 2423691/20],
    ![688141/1681, 1280849/300, 3461307/80, 2423691/20],
    ![688141/1681, 156804/41, 1806285/49, 9273728/81],
    ![688141/1681, 4697693/1369, 84551719/2601, 4966311/50],
    ![481425/1369, 4697693/1369, 84551719/2601, 4966311/50],
    ![462882/1369, 4697693/1369, 84551719/2601, 4966311/50],
    ![459151/1369, 4697693/1369, 84551719/2601, 4966311/50]]

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

theorem sources : plan.Sources 2412 (Band.middle).last Prefix6969MiddleHelper.helperBank 128513 2 40 257027 := by
  refine ⟨?_, rank154 4101, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover2782⟩⟩
  · intro i; fin_cases i
    · exact free6_1
    · exact free13_1
    · exact free18_1
    · exact free24_1
    · exact free35_1
    · exact free44_1
    · exact free53_1
    · exact free42_6
    · exact free61_1
    · exact free69_1
    · exact free72_1
    · exact free95_1
    · exact free112_1
    · exact free138_1
    · exact free144_1
    · exact free131_1
    · exact free164_1
    · exact free214_1
    · exact free186_1
    · exact free174_1
    · exact free169_1
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [234314168, 300489820, 300942965, 300261180, 300261602, 299745169, 299600734, 303654353, 163068495, 163004800, 162716422, 163030870, 82910620, 82917016, 70700813, 70711883, 91245417, 91205570, 117258513, 100000000, 218558154], [1579237, 1189380, 1187058, 1190551, 1190549, 1193194, 1193934, 1173169, 2352686, 2353746, 2358547, 2353312, 4815469, 4815088, 5677865, 5676984, 4358249, 4360261, 3344532, 3959851, 1708950],
  ![116015039306280, 1624683327756, 196702338600, 5187528920], 124698690035665111⟩

theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.middle price plan [5,4,4,4,4,4,4,4,7,7,7,7,13,13,15,15,12,12,9,11,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 4697693/1369, 84551719/2601, 4966311/50] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.Middle97
end Z6969Source1828

-- Source: Research6969.PrefixRescueDataMiddle97
section Z6969Source1829
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.Middle97
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,40⟩
  bank i := ![bank142 3098, bank142 3249, bank155 3801, bank157 3810, bank156 4030, bank193 4737, bank205 5750, bank228 8655, bank267 17855, bank325 33870, bank375 72807] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 20, 50, 110, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 257027
  seedFloor := 40

theorem sources : plan.Sources 2412 (Band.middle).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank142 3098
    · exact rank142 3249
    · exact rank155 3801
    · exact rank157 3810
    · exact rank156 4030
    · exact rank193 4737
    · exact rank205 5750
    · exact rank228 8655
    · exact rank267 17855
    · exact rank325 33870
    · exact rank375 72807
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover2284⟩
    · exact ⟨_, cover2285⟩
    · exact ⟨_, cover2286⟩
    · exact ⟨_, cover2287⟩
    · exact ⟨_, cover2288⟩
    · exact ⟨_, cover2289⟩
    · exact ⟨_, cover2290⟩
    · exact ⟨_, cover2291⟩
    · exact ⟨_, cover2292⟩
    · exact ⟨_, cover2293⟩
    · exact ⟨_, cover2294⟩

def price : EarlyPrice := ⟨2, 40, 10, 65/100, 70/100, ![1134961530024, 197947701357, 47857100240, 1196449610], 768864232481867⟩
theorem priced : price.Valid plan Band.middle := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![8509/123, 195607/246, 351767/123, 485380/41] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.Middle97
end Z6969Source1829

-- Source: Research6969.PrefixMiddleSaved97
section Z6969Source1830
set_option autoImplicit true
namespace Lower6960.Prefix6969MiddleTransfer.Saved97
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def budget : Budget Lower6960.Prefix6969MainCases.Middle97.price Lower6960.Prefix6969RescueData.Middle97.price :=
  ⟨335, 3431, 69, 795, false⟩

theorem budget_checked : budget.Valid Lower6960.Prefix6969MainCases.Middle97.plan Lower6960.Prefix6969RescueData.Middle97.plan := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide, by decide, ?_, ?_⟩
  · intro yes
    cases yes
  · rw [Budget.extra, Budget.adjust]
    rw [Research6969.JointRouted.seedWeight_eq, Research6969.JointRouted.ordWeight_eq 133628 _ (by norm_num)]; decide +kernel

def data : Case 2 40 40 :=
  ⟨Lower6960.Prefix6969MainCases.Middle97.plan, Lower6960.Prefix6969MainCases.Middle97.price, Lower6960.Prefix6969MainCases.Middle97.valid, Lower6960.Prefix6969MainCases.Middle97.priced, Lower6960.Prefix6969MainCases.Middle97.sources,
   Lower6960.Prefix6969RescueData.Middle97.plan, Lower6960.Prefix6969RescueData.Middle97.price, Lower6960.Prefix6969RescueData.Middle97.sources, Lower6960.Prefix6969RescueData.Middle97.priced,
   rfl,rfl,rfl,rfl,budget,budget_checked⟩

end Lower6960.Prefix6969MiddleTransfer.Saved97
end Z6969Source1830

-- Source: Research6969.PhysicalChecks171
section Z6969Source1831
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src2736 : Request := ⟨⟨⟨560,781,172,3807⟩,5388141854720,10440670587⟩,4,3,1,385541,41⟩
theorem cover2736 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2736) 2557 2412 [2416, 2431, 2474, 2557] := triangleCover (by decide +kernel)
def src2737 : Request := ⟨⟨⟨560,781,176,4080⟩,5482316038144,10627925923⟩,6,3,1,385541,41⟩
theorem cover2737 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2737) 2557 2412 [2416, 2431, 2474, 2557] := triangleCover (by decide +kernel)
def src2738 : Request := ⟨⟨⟨690,962,217,5063⟩,10244384358400,24434817260⟩,10,3,1,385541,41⟩
theorem cover2738 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2738) 2557 2412 [2415, 2427, 2461, 2557] := triangleCover (by decide +kernel)
def src2739 : Request := ⟨⟨⟨1000,1395,307,6953⟩,30557599170560,105715278267⟩,16,3,1,385541,41⟩
theorem cover2739 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2739) 2557 2412 [2414, 2423, 2447, 2513, 2557] := triangleCover (by decide +kernel)
def src2740 : Request := ⟨⟨⟨1450,2022,457,10612⟩,94890063298560,475487789910⟩,32,3,1,385541,41⟩
theorem cover2740 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2740) 2557 2412 [2414, 2422, 2443, 2500, 2557] := triangleCover (by decide +kernel)
def src2741 : Request := ⟨⟨⟨2600,3626,798,19305⟩,535425056505856,4807957255301⟩,65,3,1,385541,41⟩
theorem cover2741 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2741) 2557 2412 [2413, 2419, 2434, 2474, 2557] := triangleCover (by decide +kernel)
def src2742 : Request := ⟨⟨⟨6900,9623,2174,50425⟩,10196763128627200,243058712908678⟩,190,3,1,385541,41⟩
theorem cover2742 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2742) 2557 2412 [2413, 2418, 2431, 2464, 2550, 2557] := triangleCover (by decide +kernel)
def src2743 : Request := ⟨⟨⟨556,772,170,6768⟩,5255817068544,9968090926⟩,10,3,2,385540,2⟩
theorem cover2743 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2743) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
def src2744 : Request := ⟨⟨⟨556,772,170,6682⟩,5255817068544,9968090926⟩,10,3,2,385540,3⟩
theorem cover2744 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2744) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
def src2745 : Request := ⟨⟨⟨556,772,170,6596⟩,5255817068544,9968090926⟩,10,3,2,385540,4⟩
theorem cover2745 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2745) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
def src2746 : Request := ⟨⟨⟨556,772,170,6511⟩,5255817068544,9968090926⟩,10,3,2,385540,5⟩
theorem cover2746 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2746) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
def src2747 : Request := ⟨⟨⟨556,772,170,6427⟩,5255817068544,9968090926⟩,10,3,2,385540,6⟩
theorem cover2747 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2747) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
def src2748 : Request := ⟨⟨⟨556,772,170,6343⟩,5255817068544,9968090926⟩,10,3,2,385540,7⟩
theorem cover2748 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2748) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
def src2749 : Request := ⟨⟨⟨556,772,170,6261⟩,5255817068544,9968090926⟩,10,3,2,385540,8⟩
theorem cover2749 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2749) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
def src2750 : Request := ⟨⟨⟨556,772,170,6178⟩,5255817068544,9968090926⟩,10,3,2,385540,9⟩
theorem cover2750 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2750) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
def src2751 : Request := ⟨⟨⟨556,772,170,6097⟩,5255817068544,9968090926⟩,10,3,2,385540,10⟩
theorem cover2751 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2751) 2557 2412 [2416, 2430, 2471, 2557] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source1831

end Merged_Z6969Pack0731
