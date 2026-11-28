import ProximityPrize.SubmissionLower.R6970Height2313Rescue
import ProximityPrize.SubmissionLower.R6970Height2313Sources

section Pack_R6970Height2313OrdinaryPlans00

set_option Elab.async false

namespace Research6970.Height2313

open _root_.Lower6960 _root_.Research6969

section Z6969Source0753
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuadraticSingletons0
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,19⟩
  bank i := ![Physical.src433.bank, Physical.src434.bank, Physical.src435.bank, Physical.src436.bank, Physical.src437.bank, Physical.src438.bank, Physical.src439.bank, Physical.src441.bank, Physical.src442.bank, Physical.src440.bank, Physical.src442.bank] i
  reserve i := ![0, 1, 3, 4, 8, 13, 32, 65, 65, 65, 65] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 307353
  seedFloor := 19

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank433
    · exact Physical.rank434
    · exact Physical.rank435
    · exact Physical.rank436
    · exact Physical.rank437
    · exact Physical.rank438
    · exact Physical.rank439
    · exact Physical.rank441
    · exact Physical.rank442
    · exact Physical.rank440
    · exact Physical.rank442
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover433⟩
    · exact ⟨_, Physical.cover434⟩
    · exact ⟨_, Physical.cover435⟩
    · exact ⟨_, Physical.cover436⟩
    · exact ⟨_, Physical.cover437⟩
    · exact ⟨_, Physical.cover438⟩
    · exact ⟨_, Physical.cover439⟩
    · exact ⟨_, Physical.cover441⟩
    · exact ⟨_, Physical.cover442⟩
    · exact ⟨_, Physical.cover440⟩
    · exact ⟨_, Physical.cover442⟩

def price : EarlyPrice := ⟨2, 19, 10, 12948618096103994374637355/15275167234430842565558272, 331765/411909, ![18255385864228, 1017766281532, 22252225660, 1171191000], 17652989435445939⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuadraticSingletons0
end Z6969Source0753


section Z6969Source0759
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.RepricedHelperCases0
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,56⟩
  bank i := ![Physical.src1123.bank, Physical.src1124.bank, Physical.src1125.bank, Physical.src1126.bank, Physical.src1127.bank, Physical.src1128.bank, Physical.src1129.bank, Physical.src1130.bank, Physical.src1131.bank, Physical.src1134.bank, Physical.src1135.bank] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 16, 32, 65, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 41

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1123
    · exact Physical.rank1124
    · exact Physical.rank1125
    · exact Physical.rank1126
    · exact Physical.rank1127
    · exact Physical.rank1128
    · exact Physical.rank1129
    · exact Physical.rank1130
    · exact Physical.rank1131
    · exact Physical.rank1134
    · exact Physical.rank1135
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1123⟩
    · exact ⟨_, Physical.cover1124⟩
    · exact ⟨_, Physical.cover1125⟩
    · exact ⟨_, Physical.cover1126⟩
    · exact ⟨_, Physical.cover1127⟩
    · exact ⟨_, Physical.cover1128⟩
    · exact ⟨_, Physical.cover1129⟩
    · exact ⟨_, Physical.cover1130⟩
    · exact ⟨_, Physical.cover1131⟩
    · exact ⟨_, Physical.cover1134⟩
    · exact ⟨_, Physical.cover1135⟩

def price : EarlyPrice := ⟨3, 56, 10, 477776671191143/759737234751488, 125130242636332799247229/191264967181896658190336, ![1771701315956, 225583372027, 47369712104, 1691791582], 1217068502238461⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.RepricedHelperCases0
end Z6969Source0759


section Z6969Source0765
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.RepricedHelperCases1
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,5,1,40⟩
  bank i := ![Physical.src1495.bank, Physical.src1496.bank, Physical.src1497.bank, Physical.src1498.bank, Physical.src1499.bank, Physical.src1500.bank, Physical.src1501.bank, Physical.src1502.bank, Physical.src1505.bank, Physical.src1504.bank, Physical.src1503.bank] i
  reserve i := ![0, 1, 3, 6, 13, 32, 85, 110, 190, 190, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 5
  slopeFloor := 1
  physicalFloor := 643299
  seedFloor := 26

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1495
    · exact Physical.rank1496
    · exact Physical.rank1497
    · exact Physical.rank1498
    · exact Physical.rank1499
    · exact Physical.rank1500
    · exact Physical.rank1501
    · exact Physical.rank1502
    · exact Physical.rank1505
    · exact Physical.rank1504
    · exact Physical.rank1503
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1495⟩
    · exact ⟨_, Physical.cover1496⟩
    · exact ⟨_, Physical.cover1497⟩
    · exact ⟨_, Physical.cover1498⟩
    · exact ⟨_, Physical.cover1499⟩
    · exact ⟨_, Physical.cover1500⟩
    · exact ⟨_, Physical.cover1501⟩
    · exact ⟨_, Physical.cover1502⟩
    · exact ⟨_, Physical.cover1505⟩
    · exact ⟨_, Physical.cover1504⟩
    · exact ⟨_, Physical.cover1503⟩

def price : EarlyPrice := ⟨5, 40, 10, 638806005110186125179081/956982965417427668566016, 129633/194408, ![6671136129408, 748078957476, 33835509888, 3383565772], 2198442696904781⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.RepricedHelperCases1
end Z6969Source0765


section Z6969Source1357
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HighQuadraticUpper0
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,50⟩
  bank i := ![Physical.src145.bank, Physical.src146.bank, Physical.src147.bank, Physical.src148.bank, Physical.src149.bank, Physical.src150.bank, Physical.src151.bank, Physical.src152.bank, Physical.src153.bank, Physical.src154.bank, Physical.src155.bank] i
  reserve i := ![0, 1, 2, 3, 4, 8, 16, 25, 40, 110, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 296085
  seedFloor := 41

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank145
    · exact Physical.rank146
    · exact Physical.rank147
    · exact Physical.rank148
    · exact Physical.rank149
    · exact Physical.rank150
    · exact Physical.rank151
    · exact Physical.rank152
    · exact Physical.rank153
    · exact Physical.rank154
    · exact Physical.rank155
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover145⟩
    · exact ⟨_, Physical.cover146⟩
    · exact ⟨_, Physical.cover147⟩
    · exact ⟨_, Physical.cover148⟩
    · exact ⟨_, Physical.cover149⟩
    · exact ⟨_, Physical.cover150⟩
    · exact ⟨_, Physical.cover151⟩
    · exact ⟨_, Physical.cover152⟩
    · exact ⟨_, Physical.cover153⟩
    · exact ⟨_, Physical.cover154⟩
    · exact ⟨_, Physical.cover155⟩

def price : EarlyPrice := ⟨2, 50, 10, 2757063905367609392135/4197135571673986105344, 1015/1656, ![2002037990212, 250112694722, 61282112850, 1225665000], 1198337445150958⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.HighQuadraticUpper0
end Z6969Source1357


section Z6969Source1360
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HighQuadraticUpper1
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,56⟩
  bank i := ![Physical.src128.bank, Physical.src129.bank, Physical.src130.bank, Physical.src131.bank, Physical.src132.bank, Physical.src133.bank, Physical.src134.bank, Physical.src135.bank, Physical.src136.bank, Physical.src137.bank, Physical.src138.bank] i
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 13, 25, 65, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 292947
  seedFloor := 51

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank128
    · exact Physical.rank129
    · exact Physical.rank130
    · exact Physical.rank131
    · exact Physical.rank132
    · exact Physical.rank133
    · exact Physical.rank134
    · exact Physical.rank135
    · exact Physical.rank136
    · exact Physical.rank137
    · exact Physical.rank138
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover128⟩
    · exact ⟨_, Physical.cover129⟩
    · exact ⟨_, Physical.cover130⟩
    · exact ⟨_, Physical.cover131⟩
    · exact ⟨_, Physical.cover132⟩
    · exact ⟨_, Physical.cover133⟩
    · exact ⟨_, Physical.cover134⟩
    · exact ⟨_, Physical.cover135⟩
    · exact ⟨_, Physical.cover136⟩
    · exact ⟨_, Physical.cover137⟩
    · exact ⟨_, Physical.cover138⟩

def price : EarlyPrice := ⟨2, 56, 10, 180599819074499/301020703883264, 8197578280062499103673/15013133451571730317312, ![1405250617628, 158749154564, 38131093000, 680925000], 692887821668901⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.HighQuadraticUpper1
end Z6969Source1360


section Z6969Source1364
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuadraticSingletons1
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,20⟩
  bank i := ![Physical.src414.bank, Physical.src415.bank, Physical.src416.bank, Physical.src417.bank, Physical.src418.bank, Physical.src419.bank, Physical.src420.bank, Physical.src422.bank, Physical.src421.bank, Physical.src423.bank, Physical.src424.bank] i
  reserve i := ![0, 1, 2, 3, 6, 10, 20, 40, 40, 65, 65] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 307237
  seedFloor := 20

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank414
    · exact Physical.rank415
    · exact Physical.rank416
    · exact Physical.rank417
    · exact Physical.rank418
    · exact Physical.rank419
    · exact Physical.rank420
    · exact Physical.rank422
    · exact Physical.rank421
    · exact Physical.rank423
    · exact Physical.rank424
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover414⟩
    · exact ⟨_, Physical.cover415⟩
    · exact ⟨_, Physical.cover416⟩
    · exact ⟨_, Physical.cover417⟩
    · exact ⟨_, Physical.cover418⟩
    · exact ⟨_, Physical.cover419⟩
    · exact ⟨_, Physical.cover420⟩
    · exact ⟨_, Physical.cover422⟩
    · exact ⟨_, Physical.cover421⟩
    · exact ⟨_, Physical.cover423⟩
    · exact ⟨_, Physical.cover424⟩

def price : EarlyPrice := ⟨2, 20, 10, 174297432205027/198850591588352, 274334/358281, ![15916553223578, 855778053416, 23423392580, 1171191000], 14595710439522512⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuadraticSingletons1
end Z6969Source1364


section Z6969Source1369
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuadraticSingletons10
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,29⟩
  bank i := ![Physical.src314.bank, Physical.src315.bank, Physical.src316.bank, Physical.src317.bank, Physical.src318.bank, Physical.src319.bank, Physical.src320.bank, Physical.src321.bank, Physical.src322.bank, Physical.src324.bank, Physical.src323.bank] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 25, 65, 110, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 305932
  seedFloor := 29

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank314
    · exact Physical.rank315
    · exact Physical.rank316
    · exact Physical.rank317
    · exact Physical.rank318
    · exact Physical.rank319
    · exact Physical.rank320
    · exact Physical.rank321
    · exact Physical.rank322
    · exact Physical.rank324
    · exact Physical.rank323
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover314⟩
    · exact ⟨_, Physical.cover315⟩
    · exact ⟨_, Physical.cover316⟩
    · exact ⟨_, Physical.cover317⟩
    · exact ⟨_, Physical.cover318⟩
    · exact ⟨_, Physical.cover319⟩
    · exact ⟨_, Physical.cover320⟩
    · exact ⟨_, Physical.cover321⟩
    · exact ⟨_, Physical.cover322⟩
    · exact ⟨_, Physical.cover324⟩
    · exact ⟨_, Physical.cover323⟩

def price : EarlyPrice := ⟨2, 29, 10, 179464334752055703812147/253073385932532568031232, 144031/212076, ![1653309265746, 167846927019, 34640937510, 1194537000], 1822914397815437⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuadraticSingletons10
end Z6969Source1369


section Z6969Source1372
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuadraticSingletons11
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,30⟩
  bank i := ![Physical.src301.bank, Physical.src302.bank, Physical.src303.bank, Physical.src304.bank, Physical.src305.bank, Physical.src306.bank, Physical.src307.bank, Physical.src308.bank, Physical.src309.bank, Physical.src311.bank, Physical.src310.bank] i
  reserve i := ![0, 1, 3, 4, 6, 10, 16, 32, 85, 145, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 305757
  seedFloor := 30

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank301
    · exact Physical.rank302
    · exact Physical.rank303
    · exact Physical.rank304
    · exact Physical.rank305
    · exact Physical.rank306
    · exact Physical.rank307
    · exact Physical.rank308
    · exact Physical.rank309
    · exact Physical.rank311
    · exact Physical.rank310
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover301⟩
    · exact ⟨_, Physical.cover302⟩
    · exact ⟨_, Physical.cover303⟩
    · exact ⟨_, Physical.cover304⟩
    · exact ⟨_, Physical.cover305⟩
    · exact ⟨_, Physical.cover306⟩
    · exact ⟨_, Physical.cover307⟩
    · exact ⟨_, Physical.cover308⟩
    · exact ⟨_, Physical.cover309⟩
    · exact ⟨_, Physical.cover311⟩
    · exact ⟨_, Physical.cover310⟩

def price : EarlyPrice := ⟨2, 30, 10, 468834005442233987220619/669692157154952436776960, 46873/64285, ![2164612923185, 205528334510, 37621386055, 1254069300], 1843722562944650⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuadraticSingletons11
end Z6969Source1372


section Z6969Source1376
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuadraticSingletons12
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,31⟩
  bank i := ![Physical.src289.bank, Physical.src290.bank, Physical.src291.bank, Physical.src290.bank, Physical.src292.bank, Physical.src293.bank, Physical.src294.bank, Physical.src295.bank, Physical.src296.bank, Physical.src297.bank, Physical.src298.bank] i
  reserve i := ![0, 1, 2, 1, 4, 6, 8, 10, 16, 40, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 305576
  seedFloor := 31

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank289
    · exact Physical.rank290
    · exact Physical.rank291
    · exact Physical.rank290
    · exact Physical.rank292
    · exact Physical.rank293
    · exact Physical.rank294
    · exact Physical.rank295
    · exact Physical.rank296
    · exact Physical.rank297
    · exact Physical.rank298
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover289⟩
    · exact ⟨_, Physical.cover290⟩
    · exact ⟨_, Physical.cover291⟩
    · exact ⟨_, Physical.cover290⟩
    · exact ⟨_, Physical.cover292⟩
    · exact ⟨_, Physical.cover293⟩
    · exact ⟨_, Physical.cover294⟩
    · exact ⟨_, Physical.cover295⟩
    · exact ⟨_, Physical.cover296⟩
    · exact ⟨_, Physical.cover297⟩
    · exact ⟨_, Physical.cover298⟩

def price : EarlyPrice := ⟨2, 31, 10, 244610562659713/355532409929728, 2710815717835095054767/4053466247368380776448, ![1551133387044, 180908858100, 37029965460, 1194537000], 1516980725951880⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuadraticSingletons12
end Z6969Source1376


section Z6969Source1380
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuadraticSingletons13
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,32⟩
  bank i := ![Physical.src278.bank, Physical.src279.bank, Physical.src280.bank, Physical.src281.bank, Physical.src282.bank, Physical.src283.bank, Physical.src284.bank, Physical.src285.bank, Physical.src286.bank, Physical.src288.bank, Physical.src287.bank] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 25, 65, 145, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 305390
  seedFloor := 32

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank278
    · exact Physical.rank279
    · exact Physical.rank280
    · exact Physical.rank281
    · exact Physical.rank282
    · exact Physical.rank283
    · exact Physical.rank284
    · exact Physical.rank285
    · exact Physical.rank286
    · exact Physical.rank288
    · exact Physical.rank287
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover278⟩
    · exact ⟨_, Physical.cover279⟩
    · exact ⟨_, Physical.cover280⟩
    · exact ⟨_, Physical.cover281⟩
    · exact ⟨_, Physical.cover282⟩
    · exact ⟨_, Physical.cover283⟩
    · exact ⟨_, Physical.cover284⟩
    · exact ⟨_, Physical.cover285⟩
    · exact ⟨_, Physical.cover286⟩
    · exact ⟨_, Physical.cover288⟩
    · exact ⟨_, Physical.cover287⟩

def price : EarlyPrice := ⟨2, 32, 10, 3102938333580265568075/4435040565641271508992, 5300/7641, ![1291240398526, 174847393342, 39220558650, 1225665000], 1374766969834707⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuadraticSingletons13
end Z6969Source1380


section Z6969Source1383
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuadraticSingletons14
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,33⟩
  bank i := ![Physical.src265.bank, Physical.src266.bank, Physical.src267.bank, Physical.src268.bank, Physical.src269.bank, Physical.src270.bank, Physical.src271.bank, Physical.src272.bank, Physical.src273.bank, Physical.src274.bank, Physical.src275.bank] i
  reserve i := ![0, 1, 2, 3, 4, 8, 10, 16, 25, 65, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 305197
  seedFloor := 33

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank265
    · exact Physical.rank266
    · exact Physical.rank267
    · exact Physical.rank268
    · exact Physical.rank269
    · exact Physical.rank270
    · exact Physical.rank271
    · exact Physical.rank272
    · exact Physical.rank273
    · exact Physical.rank274
    · exact Physical.rank275
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover265⟩
    · exact ⟨_, Physical.cover266⟩
    · exact ⟨_, Physical.cover267⟩
    · exact ⟨_, Physical.cover268⟩
    · exact ⟨_, Physical.cover269⟩
    · exact ⟨_, Physical.cover270⟩
    · exact ⟨_, Physical.cover271⟩
    · exact ⟨_, Physical.cover272⟩
    · exact ⟨_, Physical.cover273⟩
    · exact ⟨_, Physical.cover274⟩
    · exact ⟨_, Physical.cover275⟩

def price : EarlyPrice := ⟨2, 33, 10, 135395425109197/193780548370432, 51217/69275, ![1043717442304, 127826142088, 27195255552, 824113800], 1152127828199729⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuadraticSingletons14
end Z6969Source1383


section Z6969Source1387
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuadraticSingletons15
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,34⟩
  bank i := ![Physical.src254.bank, Physical.src255.bank, Physical.src256.bank, Physical.src257.bank, Physical.src258.bank, Physical.src259.bank, Physical.src260.bank, Physical.src261.bank, Physical.src262.bank, Physical.src263.bank, Physical.src264.bank] i
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 16, 25, 50, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 304999
  seedFloor := 34

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank254
    · exact Physical.rank255
    · exact Physical.rank256
    · exact Physical.rank257
    · exact Physical.rank258
    · exact Physical.rank259
    · exact Physical.rank260
    · exact Physical.rank261
    · exact Physical.rank262
    · exact Physical.rank263
    · exact Physical.rank264
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover254⟩
    · exact ⟨_, Physical.cover255⟩
    · exact ⟨_, Physical.cover256⟩
    · exact ⟨_, Physical.cover257⟩
    · exact ⟨_, Physical.cover258⟩
    · exact ⟨_, Physical.cover259⟩
    · exact ⟨_, Physical.cover260⟩
    · exact ⟨_, Physical.cover261⟩
    · exact ⟨_, Physical.cover262⟩
    · exact ⟨_, Physical.cover263⟩
    · exact ⟨_, Physical.cover264⟩

def price : EarlyPrice := ⟨2, 34, 10, 146962202169751/222155307483136, 23198/38121, ![1220892348928, 154495415184, 34594242940, 1017496500], 1098908191274566⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuadraticSingletons15
end Z6969Source1387


end Research6970.Height2313
end Pack_R6970Height2313OrdinaryPlans00

section Pack_R6970Height2313OrdinaryPlans01

set_option Elab.async false

namespace Research6970.Height2313

open _root_.Lower6960 _root_.Research6969

section Z6969Source1391
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuadraticSingletons16
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,35⟩
  bank i := ![Physical.src243.bank, Physical.src244.bank, Physical.src245.bank, Physical.src246.bank, Physical.src247.bank, Physical.src248.bank, Physical.src249.bank, Physical.src250.bank, Physical.src251.bank, Physical.src252.bank, Physical.src253.bank] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 16, 32, 65, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 304795
  seedFloor := 35

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank243
    · exact Physical.rank244
    · exact Physical.rank245
    · exact Physical.rank246
    · exact Physical.rank247
    · exact Physical.rank248
    · exact Physical.rank249
    · exact Physical.rank250
    · exact Physical.rank251
    · exact Physical.rank252
    · exact Physical.rank253
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover243⟩
    · exact ⟨_, Physical.cover244⟩
    · exact ⟨_, Physical.cover245⟩
    · exact ⟨_, Physical.cover246⟩
    · exact ⟨_, Physical.cover247⟩
    · exact ⟨_, Physical.cover248⟩
    · exact ⟨_, Physical.cover249⟩
    · exact ⟨_, Physical.cover250⟩
    · exact ⟨_, Physical.cover251⟩
    · exact ⟨_, Physical.cover252⟩
    · exact ⟨_, Physical.cover253⟩

def price : EarlyPrice := ⟨2, 35, 10, 6838771785691/10000223174656, 10971/16016, ![1613612705761, 194270619020, 42025916414, 1200762600], 1146877106994805⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuadraticSingletons16
end Z6969Source1391


section Z6969Source1394
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuadraticSingletons17
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,36⟩
  bank i := ![Physical.src232.bank, Physical.src233.bank, Physical.src234.bank, Physical.src235.bank, Physical.src236.bank, Physical.src237.bank, Physical.src238.bank, Physical.src239.bank, Physical.src240.bank, Physical.src241.bank, Physical.src242.bank] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 25, 40, 110, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 304585
  seedFloor := 36

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank232
    · exact Physical.rank233
    · exact Physical.rank234
    · exact Physical.rank235
    · exact Physical.rank236
    · exact Physical.rank237
    · exact Physical.rank238
    · exact Physical.rank239
    · exact Physical.rank240
    · exact Physical.rank241
    · exact Physical.rank242
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover232⟩
    · exact ⟨_, Physical.cover233⟩
    · exact ⟨_, Physical.cover234⟩
    · exact ⟨_, Physical.cover235⟩
    · exact ⟨_, Physical.cover236⟩
    · exact ⟨_, Physical.cover237⟩
    · exact ⟨_, Physical.cover238⟩
    · exact ⟨_, Physical.cover239⟩
    · exact ⟨_, Physical.cover240⟩
    · exact ⟨_, Physical.cover241⟩
    · exact ⟨_, Physical.cover242⟩

def price : EarlyPrice := ⟨2, 36, 10, 269448275519567/406023047217152, 2493241063571265070273/3414208166049046593536, ![1455362833800, 192715312224, 43114598676, 1197649800], 1084846164229191⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuadraticSingletons17
end Z6969Source1394


section Z6969Source1398
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuadraticSingletons18
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,37⟩
  bank i := ![Physical.src219.bank, Physical.src220.bank, Physical.src221.bank, Physical.src222.bank, Physical.src223.bank, Physical.src224.bank, Physical.src225.bank, Physical.src226.bank, Physical.src227.bank, Physical.src229.bank, Physical.src228.bank] i
  reserve i := ![0, 1, 2, 3, 4, 8, 16, 32, 110, 190, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 304368
  seedFloor := 37

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank219
    · exact Physical.rank220
    · exact Physical.rank221
    · exact Physical.rank222
    · exact Physical.rank223
    · exact Physical.rank224
    · exact Physical.rank225
    · exact Physical.rank226
    · exact Physical.rank227
    · exact Physical.rank229
    · exact Physical.rank228
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover219⟩
    · exact ⟨_, Physical.cover220⟩
    · exact ⟨_, Physical.cover221⟩
    · exact ⟨_, Physical.cover222⟩
    · exact ⟨_, Physical.cover223⟩
    · exact ⟨_, Physical.cover224⟩
    · exact ⟨_, Physical.cover225⟩
    · exact ⟨_, Physical.cover226⟩
    · exact ⟨_, Physical.cover227⟩
    · exact ⟨_, Physical.cover229⟩
    · exact ⟨_, Physical.cover228⟩

def price : EarlyPrice := ⟨2, 37, 10, 2027639264605141188930359/2992878995829525477064704, 62654/105267, ![1322269273598, 191219154900, 45348767100, 1225665000], 1000702415788310⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuadraticSingletons18
end Z6969Source1398


section Z6969Source1402
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuadraticSingletons19
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,38⟩
  bank i := ![Physical.src204.bank, Physical.src205.bank, Physical.src206.bank, Physical.src207.bank, Physical.src208.bank, Physical.src209.bank, Physical.src210.bank, Physical.src211.bank, Physical.src212.bank, Physical.src213.bank, Physical.src214.bank] i
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 16, 25, 50, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 304146
  seedFloor := 38

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank204
    · exact Physical.rank205
    · exact Physical.rank206
    · exact Physical.rank207
    · exact Physical.rank208
    · exact Physical.rank209
    · exact Physical.rank210
    · exact Physical.rank211
    · exact Physical.rank212
    · exact Physical.rank213
    · exact Physical.rank214
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover204⟩
    · exact ⟨_, Physical.cover205⟩
    · exact ⟨_, Physical.cover206⟩
    · exact ⟨_, Physical.cover207⟩
    · exact ⟨_, Physical.cover208⟩
    · exact ⟨_, Physical.cover209⟩
    · exact ⟨_, Physical.cover210⟩
    · exact ⟨_, Physical.cover211⟩
    · exact ⟨_, Physical.cover212⟩
    · exact ⟨_, Physical.cover213⟩
    · exact ⟨_, Physical.cover214⟩

def price : EarlyPrice := ⟨2, 38, 10, 61017529668342826949437/89556393873009354473472, 30569/51504, ![1072616056215, 138275936961, 31315746186, 824113800], 810266731372866⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuadraticSingletons19
end Z6969Source1402


section Z6969Source1405
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuadraticSingletons2
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,21⟩
  bank i := ![Physical.src403.bank, Physical.src404.bank, Physical.src405.bank, Physical.src407.bank, Physical.src406.bank, Physical.src408.bank, Physical.src409.bank, Physical.src410.bank, Physical.src411.bank, Physical.src412.bank, Physical.src413.bank] i
  reserve i := ![0, 1, 2, 4, 4, 8, 16, 32, 40, 65, 65] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 307116
  seedFloor := 21

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank403
    · exact Physical.rank404
    · exact Physical.rank405
    · exact Physical.rank407
    · exact Physical.rank406
    · exact Physical.rank408
    · exact Physical.rank409
    · exact Physical.rank410
    · exact Physical.rank411
    · exact Physical.rank412
    · exact Physical.rank413
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover403⟩
    · exact ⟨_, Physical.cover404⟩
    · exact ⟨_, Physical.cover405⟩
    · exact ⟨_, Physical.cover407⟩
    · exact ⟨_, Physical.cover406⟩
    · exact ⟨_, Physical.cover408⟩
    · exact ⟨_, Physical.cover409⟩
    · exact ⟨_, Physical.cover410⟩
    · exact ⟨_, Physical.cover411⟩
    · exact ⟨_, Physical.cover412⟩
    · exact ⟨_, Physical.cover413⟩

def price : EarlyPrice := ⟨2, 21, 10, 1275383277281203/1567622397165568, 108755/134499, ![13080107386506, 685806279202, 25084819570, 1194537000], 11925621900224605⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuadraticSingletons2
end Z6969Source1405


section Z6969Source1408
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuadraticSingletons20
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,39⟩
  bank i := ![Physical.src193.bank, Physical.src194.bank, Physical.src195.bank, Physical.src196.bank, Physical.src197.bank, Physical.src198.bank, Physical.src199.bank, Physical.src200.bank, Physical.src201.bank, Physical.src202.bank, Physical.src203.bank] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 25, 40, 85, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 303918
  seedFloor := 39

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank193
    · exact Physical.rank194
    · exact Physical.rank195
    · exact Physical.rank196
    · exact Physical.rank197
    · exact Physical.rank198
    · exact Physical.rank199
    · exact Physical.rank200
    · exact Physical.rank201
    · exact Physical.rank202
    · exact Physical.rank203
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover193⟩
    · exact ⟨_, Physical.cover194⟩
    · exact ⟨_, Physical.cover195⟩
    · exact ⟨_, Physical.cover196⟩
    · exact ⟨_, Physical.cover197⟩
    · exact ⟨_, Physical.cover198⟩
    · exact ⟨_, Physical.cover199⟩
    · exact ⟨_, Physical.cover200⟩
    · exact ⟨_, Physical.cover201⟩
    · exact ⟨_, Physical.cover202⟩
    · exact ⟨_, Physical.cover203⟩

def price : EarlyPrice := ⟨2, 39, 10, 163221454436231/243222211198976, 1206/1739, ![1392559702780, 172476167960, 38907725680, 997652400], 883279957779231⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuadraticSingletons20
end Z6969Source1408


section Z6969Source1411
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuadraticSingletons21
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,40⟩
  bank i := ![Physical.src176.bank, Physical.src177.bank, Physical.src178.bank, Physical.src179.bank, Physical.src180.bank, Physical.src181.bank, Physical.src182.bank, Physical.src183.bank, Physical.src184.bank, Physical.src185.bank, Physical.src186.bank] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 20, 50, 110, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 303684
  seedFloor := 40

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank176
    · exact Physical.rank177
    · exact Physical.rank178
    · exact Physical.rank179
    · exact Physical.rank180
    · exact Physical.rank181
    · exact Physical.rank182
    · exact Physical.rank183
    · exact Physical.rank184
    · exact Physical.rank185
    · exact Physical.rank186
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover176⟩
    · exact ⟨_, Physical.cover177⟩
    · exact ⟨_, Physical.cover178⟩
    · exact ⟨_, Physical.cover179⟩
    · exact ⟨_, Physical.cover180⟩
    · exact ⟨_, Physical.cover181⟩
    · exact ⟨_, Physical.cover182⟩
    · exact ⟨_, Physical.cover183⟩
    · exact ⟨_, Physical.cover184⟩
    · exact ⟨_, Physical.cover185⟩
    · exact ⟨_, Physical.cover186⟩

def price : EarlyPrice := ⟨2, 40, 10, 228083542999583/351161683017728, 3555997163054874105079/5107788000122663206912, ![1826479421760, 214715870244, 48029615232, 1200762600], 963190528588129⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuadraticSingletons21
end Z6969Source1411


section Z6969Source1415
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuadraticSingletons3
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,22⟩
  bank i := ![Physical.src392.bank, Physical.src393.bank, Physical.src394.bank, Physical.src395.bank, Physical.src396.bank, Physical.src397.bank, Physical.src398.bank, Physical.src399.bank, Physical.src402.bank, Physical.src400.bank, Physical.src401.bank] i
  reserve i := ![0, 1, 2, 4, 6, 10, 20, 50, 65, 65, 65] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 306989
  seedFloor := 22

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank392
    · exact Physical.rank393
    · exact Physical.rank394
    · exact Physical.rank395
    · exact Physical.rank396
    · exact Physical.rank397
    · exact Physical.rank398
    · exact Physical.rank399
    · exact Physical.rank402
    · exact Physical.rank400
    · exact Physical.rank401
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover392⟩
    · exact ⟨_, Physical.cover393⟩
    · exact ⟨_, Physical.cover394⟩
    · exact ⟨_, Physical.cover395⟩
    · exact ⟨_, Physical.cover396⟩
    · exact ⟨_, Physical.cover397⟩
    · exact ⟨_, Physical.cover398⟩
    · exact ⟨_, Physical.cover399⟩
    · exact ⟨_, Physical.cover402⟩
    · exact ⟨_, Physical.cover400⟩
    · exact ⟨_, Physical.cover401⟩

def price : EarlyPrice := ⟨2, 22, 10, 16174315993433/20210241241088, 80561/101150, ![9776905614864, 510342358488, 26039653848, 1183642200], 8879743767141528⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuadraticSingletons3
end Z6969Source1415


section Z6969Source1419
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuadraticSingletons4
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,23⟩
  bank i := ![Physical.src381.bank, Physical.src382.bank, Physical.src383.bank, Physical.src384.bank, Physical.src385.bank, Physical.src386.bank, Physical.src387.bank, Physical.src388.bank, Physical.src390.bank, Physical.src389.bank, Physical.src391.bank] i
  reserve i := ![0, 1, 3, 4, 6, 8, 13, 32, 65, 65, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 306855
  seedFloor := 23

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank381
    · exact Physical.rank382
    · exact Physical.rank383
    · exact Physical.rank384
    · exact Physical.rank385
    · exact Physical.rank386
    · exact Physical.rank387
    · exact Physical.rank388
    · exact Physical.rank390
    · exact Physical.rank389
    · exact Physical.rank391
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover381⟩
    · exact ⟨_, Physical.cover382⟩
    · exact ⟨_, Physical.cover383⟩
    · exact ⟨_, Physical.cover384⟩
    · exact ⟨_, Physical.cover385⟩
    · exact ⟨_, Physical.cover386⟩
    · exact ⟨_, Physical.cover387⟩
    · exact ⟨_, Physical.cover388⟩
    · exact ⟨_, Physical.cover390⟩
    · exact ⟨_, Physical.cover389⟩
    · exact ⟨_, Physical.cover391⟩

def price : EarlyPrice := ⟨2, 23, 10, 1070485255351580414906783/1348279848075788648710144, 83523/107926, ![47013056248594, 2129440022906, 27473850590, 1194537000], 20291819181167840⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuadraticSingletons4
end Z6969Source1419


section Z6969Source1422
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuadraticSingletons5
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,24⟩
  bank i := ![Physical.src371.bank, Physical.src372.bank, Physical.src373.bank, Physical.src374.bank, Physical.src375.bank, Physical.src376.bank, Physical.src377.bank, Physical.src378.bank, Physical.src379.bank, Physical.src380.bank, Physical.src378.bank] i
  reserve i := ![0, 1, 2, 4, 8, 13, 32, 65, 65, 85, 65] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 306716
  seedFloor := 24

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank371
    · exact Physical.rank372
    · exact Physical.rank373
    · exact Physical.rank374
    · exact Physical.rank375
    · exact Physical.rank376
    · exact Physical.rank377
    · exact Physical.rank378
    · exact Physical.rank379
    · exact Physical.rank380
    · exact Physical.rank378
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover371⟩
    · exact ⟨_, Physical.cover372⟩
    · exact ⟨_, Physical.cover373⟩
    · exact ⟨_, Physical.cover374⟩
    · exact ⟨_, Physical.cover375⟩
    · exact ⟨_, Physical.cover376⟩
    · exact ⟨_, Physical.cover377⟩
    · exact ⟨_, Physical.cover378⟩
    · exact ⟨_, Physical.cover379⟩
    · exact ⟨_, Physical.cover380⟩
    · exact ⟨_, Physical.cover378⟩

def price : EarlyPrice := ⟨2, 24, 10, 1561440628642951/2102704268640256, 54523/75170, ![10664248179771, 533419839102, 24484836438, 1020220200], 6819980618237811⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuadraticSingletons5
end Z6969Source1422


section Z6969Source1426
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuadraticSingletons6
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,25⟩
  bank i := ![Physical.src360.bank, Physical.src361.bank, Physical.src362.bank, Physical.src363.bank, Physical.src364.bank, Physical.src365.bank, Physical.src366.bank, Physical.src367.bank, Physical.src368.bank, Physical.src369.bank, Physical.src370.bank] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 20, 40, 85, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 306571
  seedFloor := 25

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank360
    · exact Physical.rank361
    · exact Physical.rank362
    · exact Physical.rank363
    · exact Physical.rank364
    · exact Physical.rank365
    · exact Physical.rank366
    · exact Physical.rank367
    · exact Physical.rank368
    · exact Physical.rank369
    · exact Physical.rank370
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover360⟩
    · exact ⟨_, Physical.cover361⟩
    · exact ⟨_, Physical.cover362⟩
    · exact ⟨_, Physical.cover363⟩
    · exact ⟨_, Physical.cover364⟩
    · exact ⟨_, Physical.cover365⟩
    · exact ⟨_, Physical.cover366⟩
    · exact ⟨_, Physical.cover367⟩
    · exact ⟨_, Physical.cover368⟩
    · exact ⟨_, Physical.cover369⟩
    · exact ⟨_, Physical.cover370⟩

def price : EarlyPrice := ⟨2, 25, 10, 145992439583713/188745470967808, 101114715243351319587207/129853712535703231922176, ![3015664366440, 213281524050, 29862878540, 1194537000], 3764546395184066⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuadraticSingletons6
end Z6969Source1426


section Z6969Source1430
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuadraticSingletons7
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,26⟩
  bank i := ![Physical.src349.bank, Physical.src351.bank, Physical.src352.bank, Physical.src350.bank, Physical.src353.bank, Physical.src354.bank, Physical.src355.bank, Physical.src356.bank, Physical.src359.bank, Physical.src358.bank, Physical.src357.bank] i
  reserve i := ![0, 1, 2, 1, 4, 8, 13, 40, 110, 85, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 306420
  seedFloor := 26

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank349
    · exact Physical.rank351
    · exact Physical.rank352
    · exact Physical.rank350
    · exact Physical.rank353
    · exact Physical.rank354
    · exact Physical.rank355
    · exact Physical.rank356
    · exact Physical.rank359
    · exact Physical.rank358
    · exact Physical.rank357
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover349⟩
    · exact ⟨_, Physical.cover351⟩
    · exact ⟨_, Physical.cover352⟩
    · exact ⟨_, Physical.cover350⟩
    · exact ⟨_, Physical.cover353⟩
    · exact ⟨_, Physical.cover354⟩
    · exact ⟨_, Physical.cover355⟩
    · exact ⟨_, Physical.cover356⟩
    · exact ⟨_, Physical.cover359⟩
    · exact ⟨_, Physical.cover358⟩
    · exact ⟨_, Physical.cover357⟩

def price : EarlyPrice := ⟨2, 26, 10, 3310112020726777395510531/4662955174793410814935040, 122361/169630, ![2671087634525, 218336292705, 32605205545, 1254069300], 3092137251141907⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuadraticSingletons7
end Z6969Source1430


end Research6970.Height2313
end Pack_R6970Height2313OrdinaryPlans01

section Pack_R6970Height2313OrdinaryPlans02

set_option Elab.async false

namespace Research6970.Height2313

open _root_.Lower6960 _root_.Research6969

section Z6969Source1433
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuadraticSingletons8
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,27⟩
  bank i := ![Physical.src336.bank, Physical.src337.bank, Physical.src338.bank, Physical.src339.bank, Physical.src340.bank, Physical.src341.bank, Physical.src342.bank, Physical.src343.bank, Physical.src344.bank, Physical.src345.bank, Physical.src346.bank] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 20, 32, 65, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 306263
  seedFloor := 27

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank336
    · exact Physical.rank337
    · exact Physical.rank338
    · exact Physical.rank339
    · exact Physical.rank340
    · exact Physical.rank341
    · exact Physical.rank342
    · exact Physical.rank343
    · exact Physical.rank344
    · exact Physical.rank345
    · exact Physical.rank346
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover336⟩
    · exact ⟨_, Physical.cover337⟩
    · exact ⟨_, Physical.cover338⟩
    · exact ⟨_, Physical.cover339⟩
    · exact ⟨_, Physical.cover340⟩
    · exact ⟨_, Physical.cover341⟩
    · exact ⟨_, Physical.cover342⟩
    · exact ⟨_, Physical.cover343⟩
    · exact ⟨_, Physical.cover344⟩
    · exact ⟨_, Physical.cover345⟩
    · exact ⟨_, Physical.cover346⟩

def price : EarlyPrice := ⟨2, 27, 10, 12099161710964701026762303/16039364520028609068400640, 225192/314605, ![1916320037377, 184971376557, 32251906490, 1194537000], 2418976636192664⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuadraticSingletons8
end Z6969Source1433


section Z6969Source1436
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuadraticSingletons9
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,28⟩
  bank i := ![Physical.src325.bank, Physical.src326.bank, Physical.src327.bank, Physical.src328.bank, Physical.src329.bank, Physical.src330.bank, Physical.src331.bank, Physical.src332.bank, Physical.src333.bank, Physical.src334.bank, Physical.src335.bank] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 16, 40, 65, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 306100
  seedFloor := 28

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank325
    · exact Physical.rank326
    · exact Physical.rank327
    · exact Physical.rank328
    · exact Physical.rank329
    · exact Physical.rank330
    · exact Physical.rank331
    · exact Physical.rank332
    · exact Physical.rank333
    · exact Physical.rank334
    · exact Physical.rank335
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover325⟩
    · exact ⟨_, Physical.cover326⟩
    · exact ⟨_, Physical.cover327⟩
    · exact ⟨_, Physical.cover328⟩
    · exact ⟨_, Physical.cover329⟩
    · exact ⟨_, Physical.cover330⟩
    · exact ⟨_, Physical.cover331⟩
    · exact ⟨_, Physical.cover332⟩
    · exact ⟨_, Physical.cover333⟩
    · exact ⟨_, Physical.cover334⟩
    · exact ⟨_, Physical.cover335⟩

def price : EarlyPrice := ⟨2, 28, 10, 67685978241651963799735/95949204800848646897664, 104501/143955, ![1454211208000, 170154372600, 33620735600, 1200762600], 2044109803419815⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuadraticSingletons9
end Z6969Source1436


section Z6969Source1442
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons0
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 9
  positive := by decide
  primeShape := ⟨0,3,1,4⟩
  bank i := ![Physical.src665.bank, Physical.src666.bank, Physical.src667.bank, Physical.src668.bank, Physical.src669.bank, Physical.src672.bank, Physical.src670.bank, Physical.src674.bank, Physical.src675.bank] i
  reserve i := ![0, 1, 6, 10, 16, 25, 20, 40, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 386273
  seedFloor := 4

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank665
    · exact Physical.rank666
    · exact Physical.rank667
    · exact Physical.rank668
    · exact Physical.rank669
    · exact Physical.rank672
    · exact Physical.rank670
    · exact Physical.rank674
    · exact Physical.rank675
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover665⟩
    · exact ⟨_, Physical.cover666⟩
    · exact ⟨_, Physical.cover667⟩
    · exact ⟨_, Physical.cover668⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover672⟩
    · exact ⟨_, Physical.cover670⟩
    · exact ⟨_, Physical.cover674⟩
    · exact ⟨_, Physical.cover675⟩

def price : EarlyPrice := ⟨3, 4, 8, 4099618046273429/4173309918838784, 533784/656447, ![1123251401250, 578561473655, 4684688750, 2342360930], 11635298150963924⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons0
end Z6969Source1442


section Z6969Source1446
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons1
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,5⟩
  bank i := ![Physical.src676.bank, Physical.src677.bank, Physical.src678.bank, Physical.src679.bank, Physical.src680.bank, Physical.src681.bank, Physical.src683.bank, Physical.src682.bank, Physical.src684.bank, Physical.src685.bank, Physical.src686.bank] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 8, 10, 25, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 386273
  seedFloor := 5

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank676
    · exact Physical.rank677
    · exact Physical.rank678
    · exact Physical.rank679
    · exact Physical.rank680
    · exact Physical.rank681
    · exact Physical.rank683
    · exact Physical.rank682
    · exact Physical.rank684
    · exact Physical.rank685
    · exact Physical.rank686
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover678⟩
    · exact ⟨_, Physical.cover679⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover681⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover684⟩
    · exact ⟨_, Physical.cover685⟩
    · exact ⟨_, Physical.cover686⟩

def price : EarlyPrice := ⟨3, 5, 10, 545585345161012401419983967/566081058828121304815632384, 1622639/1960233, ![966887868660, 407924721875, 5855858680, 2342360930], 10493473415005272⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons1
end Z6969Source1446


section Z6969Source1452
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons10
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,14⟩
  bank i := ![Physical.src777.bank, Physical.src778.bank, Physical.src779.bank, Physical.src780.bank, Physical.src781.bank, Physical.src782.bank, Physical.src784.bank, Physical.src783.bank, Physical.src787.bank, Physical.src788.bank, Physical.src789.bank] i
  reserve i := ![0, 1, 3, 6, 10, 13, 20, 20, 50, 85, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 386273
  seedFloor := 14

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank777
    · exact Physical.rank778
    · exact Physical.rank779
    · exact Physical.rank780
    · exact Physical.rank781
    · exact Physical.rank782
    · exact Physical.rank784
    · exact Physical.rank783
    · exact Physical.rank787
    · exact Physical.rank788
    · exact Physical.rank789
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover778⟩
    · exact ⟨_, Physical.cover779⟩
    · exact ⟨_, Physical.cover780⟩
    · exact ⟨_, Physical.cover781⟩
    · exact ⟨_, Physical.cover782⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover788⟩
    · exact ⟨_, Physical.cover789⟩

def price : EarlyPrice := ⟨3, 14, 10, 16306768187029/17819453620224, 197963/256851, ![4489993146520, 675370053640, 13607360396, 1943926114], 7612109216259726⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons10
end Z6969Source1452


section Z6969Source1455
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons11
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,15⟩
  bank i := ![Physical.src790.bank, Physical.src791.bank, Physical.src792.bank, Physical.src793.bank, Physical.src794.bank, Physical.src795.bank, Physical.src796.bank, Physical.src798.bank, Physical.src800.bank, Physical.src801.bank, Physical.src802.bank] i
  reserve i := ![0, 1, 2, 4, 8, 10, 16, 25, 50, 85, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 386273
  seedFloor := 15

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank790
    · exact Physical.rank791
    · exact Physical.rank792
    · exact Physical.rank793
    · exact Physical.rank794
    · exact Physical.rank795
    · exact Physical.rank796
    · exact Physical.rank798
    · exact Physical.rank800
    · exact Physical.rank801
    · exact Physical.rank802
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover791⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover794⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover801⟩
    · exact ⟨_, Physical.cover802⟩

def price : EarlyPrice := ⟨3, 15, 10, 29298068851997124155762885/32401502052857173071888384, 138166/173181, ![4299467922675, 609593268825, 17917732650, 2389052510], 7227456608946945⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons11
end Z6969Source1455


section Z6969Source1459
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons12
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 9
  positive := by decide
  primeShape := ⟨0,3,1,16⟩
  bank i := ![Physical.src803.bank, Physical.src804.bank, Physical.src805.bank, Physical.src806.bank, Physical.src808.bank, Physical.src810.bank, Physical.src811.bank, Physical.src812.bank, Physical.src813.bank] i
  reserve i := ![0, 1, 4, 10, 25, 40, 85, 110, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 386273
  seedFloor := 16

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank803
    · exact Physical.rank804
    · exact Physical.rank805
    · exact Physical.rank806
    · exact Physical.rank808
    · exact Physical.rank810
    · exact Physical.rank811
    · exact Physical.rank812
    · exact Physical.rank813
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover808⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover812⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩

def price : EarlyPrice := ⟨3, 16, 8, 285885074281429921976263/317739451003392428605440, 42407/59040, ![8214880043328, 1073765843412, 18937934496, 2367263106], 8741957710220074⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons12
end Z6969Source1459


section Z6969Source1463
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons13
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,17⟩
  bank i := ![Physical.src814.bank, Physical.src815.bank, Physical.src815.bank, Physical.src816.bank, Physical.src817.bank, Physical.src818.bank, Physical.src819.bank, Physical.src820.bank, Physical.src823.bank, Physical.src824.bank, Physical.src825.bank] i
  reserve i := ![0, 1, 1, 2, 4, 6, 10, 20, 40, 85, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 386273
  seedFloor := 17

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank814
    · exact Physical.rank815
    · exact Physical.rank815
    · exact Physical.rank816
    · exact Physical.rank817
    · exact Physical.rank818
    · exact Physical.rank819
    · exact Physical.rank820
    · exact Physical.rank823
    · exact Physical.rank824
    · exact Physical.rank825
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover817⟩
    · exact ⟨_, Physical.cover818⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover823⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover825⟩

def price : EarlyPrice := ⟨3, 17, 10, 78762326030429/89783472226304, 55789/71897, ![3927082760580, 503262483173, 20306760600, 2389052510], 5797801486894048⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons13
end Z6969Source1463


section Z6969Source1466
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons14
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,3,1,18⟩
  bank i := ![Physical.src826.bank, Physical.src827.bank, Physical.src828.bank, Physical.src829.bank, Physical.src830.bank, Physical.src833.bank, Physical.src835.bank, Physical.src834.bank, Physical.src836.bank, Physical.src835.bank] i
  reserve i := ![0, 1, 2, 4, 10, 32, 85, 65, 110, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 386273
  seedFloor := 18

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank826
    · exact Physical.rank827
    · exact Physical.rank828
    · exact Physical.rank829
    · exact Physical.rank830
    · exact Physical.rank833
    · exact Physical.rank835
    · exact Physical.rank834
    · exact Physical.rank836
    · exact Physical.rank835
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover826⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover830⟩
    · exact ⟨_, Physical.cover833⟩
    · exact ⟨_, Physical.cover835⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover836⟩
    · exact ⟨_, Physical.cover835⟩

def price : EarlyPrice := ⟨3, 18, 9, 442546978054753/527039733956608, 108577/150730, ![8063910029759, 948868918396, 17845358804, 1982835764], 7209963381940014⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons14
end Z6969Source1466


section Z6969Source1470
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons15
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,19⟩
  bank i := ![Physical.src837.bank, Physical.src838.bank, Physical.src839.bank, Physical.src840.bank, Physical.src841.bank, Physical.src842.bank, Physical.src844.bank, Physical.src846.bank, Physical.src847.bank, Physical.src849.bank, Physical.src848.bank] i
  reserve i := ![0, 1, 2, 4, 8, 16, 25, 40, 65, 110, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 386273
  seedFloor := 19

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank837
    · exact Physical.rank838
    · exact Physical.rank839
    · exact Physical.rank840
    · exact Physical.rank841
    · exact Physical.rank842
    · exact Physical.rank844
    · exact Physical.rank846
    · exact Physical.rank847
    · exact Physical.rank849
    · exact Physical.rank848
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover837⟩
    · exact ⟨_, Physical.cover838⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover841⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover847⟩
    · exact ⟨_, Physical.cover849⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩

def price : EarlyPrice := ⟨3, 19, 10, 183101320148801/215948875268096, 107368193502725913947219/139076261900842262593536, ![7539549368930, 849452012549, 15657878388, 1648212774], 6301476494136658⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons15
end Z6969Source1470


section Z6969Source1474
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons16
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,20⟩
  bank i := ![Physical.src850.bank, Physical.src851.bank, Physical.src852.bank, Physical.src853.bank, Physical.src854.bank, Physical.src855.bank, Physical.src857.bank, Physical.src859.bank, Physical.src860.bank, Physical.src861.bank, Physical.src862.bank] i
  reserve i := ![0, 1, 2, 4, 8, 16, 25, 40, 65, 110, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 386273
  seedFloor := 20

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank850
    · exact Physical.rank851
    · exact Physical.rank852
    · exact Physical.rank853
    · exact Physical.rank854
    · exact Physical.rank855
    · exact Physical.rank857
    · exact Physical.rank859
    · exact Physical.rank860
    · exact Physical.rank861
    · exact Physical.rank862
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover854⟩
    · exact ⟨_, Physical.cover855⟩
    · exact ⟨_, Physical.cover857⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover860⟩
    · exact ⟨_, Physical.cover861⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩

def price : EarlyPrice := ⟨3, 20, 10, 5468835896771/6612909817856, 6097641457285596190617/7883021423638487760896, ![6924382848838, 751189937565, 23547902308, 2354812018], 5777485312252742⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons16
end Z6969Source1474


section Z6969Source1477
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons17
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,21⟩
  bank i := ![Physical.src863.bank, Physical.src864.bank, Physical.src865.bank, Physical.src866.bank, Physical.src867.bank, Physical.src868.bank, Physical.src870.bank, Physical.src872.bank, Physical.src873.bank, Physical.src874.bank, Physical.src875.bank] i
  reserve i := ![0, 1, 2, 3, 4, 8, 25, 65, 110, 110, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 386273
  seedFloor := 21

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank863
    · exact Physical.rank864
    · exact Physical.rank865
    · exact Physical.rank866
    · exact Physical.rank867
    · exact Physical.rank868
    · exact Physical.rank870
    · exact Physical.rank872
    · exact Physical.rank873
    · exact Physical.rank874
    · exact Physical.rank875
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover868⟩
    · exact ⟨_, Physical.cover870⟩
    · exact ⟨_, Physical.cover872⟩
    · exact ⟨_, Physical.cover873⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover875⟩

def price : EarlyPrice := ⟨3, 21, 10, 4327341933858941117562919/5302229749823072358105088, 59231/80894, ![50721897376188, 4906389047597, 24725297726, 2354812018], 21085058683255992⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons17
end Z6969Source1477


end Research6970.Height2313
end Pack_R6970Height2313OrdinaryPlans02

section Pack_R6970Height2313OrdinaryPlans03

set_option Elab.async false

namespace Research6970.Height2313

open _root_.Lower6960 _root_.Research6969

section Z6969Source1481
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons18
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,22⟩
  bank i := ![Physical.src876.bank, Physical.src877.bank, Physical.src878.bank, Physical.src879.bank, Physical.src880.bank, Physical.src881.bank, Physical.src883.bank, Physical.src885.bank, Physical.src886.bank, Physical.src887.bank, Physical.src888.bank] i
  reserve i := ![0, 1, 2, 3, 4, 8, 25, 65, 110, 110, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 386273
  seedFloor := 22

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank876
    · exact Physical.rank877
    · exact Physical.rank878
    · exact Physical.rank879
    · exact Physical.rank880
    · exact Physical.rank881
    · exact Physical.rank883
    · exact Physical.rank885
    · exact Physical.rank886
    · exact Physical.rank887
    · exact Physical.rank888
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover881⟩
    · exact ⟨_, Physical.cover883⟩
    · exact ⟨_, Physical.cover885⟩
    · exact ⟨_, Physical.cover886⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover888⟩

def price : EarlyPrice := ⟨3, 22, 10, 634702895307217/805857145126912, 84878/115235, ![43429100752548, 4027428192703, 25902693144, 2354812018], 17130576950271923⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons18
end Z6969Source1481


section Z6969Source1486
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons19
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,23⟩
  bank i := ![Physical.src889.bank, Physical.src890.bank, Physical.src891.bank, Physical.src892.bank, Physical.src893.bank, Physical.src894.bank, Physical.src899.bank, Physical.src900.bank, Physical.src902.bank, Physical.src901.bank, Physical.src903.bank] i
  reserve i := ![0, 1, 2, 4, 8, 20, 50, 65, 110, 110, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 386273
  seedFloor := 23

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank889
    · exact Physical.rank890
    · exact Physical.rank891
    · exact Physical.rank892
    · exact Physical.rank893
    · exact Physical.rank894
    · exact Physical.rank899
    · exact Physical.rank900
    · exact Physical.rank902
    · exact Physical.rank901
    · exact Physical.rank903
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover894⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover900⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover901⟩
    · exact ⟨_, Physical.cover903⟩

def price : EarlyPrice := ⟨3, 23, 10, 4371346805871225472074963/5513918276640103265730560, 135527/184460, ![35338701201943, 3155854723958, 27473850590, 2389052510], 13168813258998821⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons19
end Z6969Source1486


section Z6969Source1490
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons2
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,6⟩
  bank i := ![Physical.src687.bank, Physical.src688.bank, Physical.src689.bank, Physical.src690.bank, Physical.src691.bank, Physical.src692.bank, Physical.src693.bank, Physical.src694.bank, Physical.src696.bank, Physical.src695.bank, Physical.src697.bank] i
  reserve i := ![0, 1, 2, 3, 4, 10, 20, 32, 50, 40, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 386273
  seedFloor := 6

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank687
    · exact Physical.rank688
    · exact Physical.rank689
    · exact Physical.rank690
    · exact Physical.rank691
    · exact Physical.rank692
    · exact Physical.rank693
    · exact Physical.rank694
    · exact Physical.rank696
    · exact Physical.rank695
    · exact Physical.rank697
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover687⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover692⟩
    · exact ⟨_, Physical.cover693⟩
    · exact ⟨_, Physical.cover694⟩
    · exact ⟨_, Physical.cover696⟩
    · exact ⟨_, Physical.cover695⟩
    · exact ⟨_, Physical.cover697⟩

def price : EarlyPrice := ⟨3, 6, 10, 415768508745067/428051510853632, 54843/67331, ![1173945671655, 412373646674, 5831733378, 1943926114], 9523638781079003⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons2
end Z6969Source1490


section Z6969Source1493
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons20
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,24⟩
  bank i := ![Physical.src904.bank, Physical.src905.bank, Physical.src906.bank, Physical.src907.bank, Physical.src908.bank, Physical.src909.bank, Physical.src914.bank, Physical.src915.bank, Physical.src917.bank, Physical.src918.bank, Physical.src916.bank] i
  reserve i := ![0, 1, 2, 4, 8, 20, 65, 110, 110, 145, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 386273
  seedFloor := 24

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank904
    · exact Physical.rank905
    · exact Physical.rank906
    · exact Physical.rank907
    · exact Physical.rank908
    · exact Physical.rank909
    · exact Physical.rank914
    · exact Physical.rank915
    · exact Physical.rank917
    · exact Physical.rank918
    · exact Physical.rank916
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover918⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩

def price : EarlyPrice := ⟨3, 24, 10, 507426941440477/694141365256192, 36419/49630, ![14428077407595, 1291390999130, 28668363030, 2389052510], 6285671603876149⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons20
end Z6969Source1493


section Z6969Source1497
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons21
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,25⟩
  bank i := ![Physical.src919.bank, Physical.src920.bank, Physical.src921.bank, Physical.src922.bank, Physical.src923.bank, Physical.src926.bank, Physical.src928.bank, Physical.src929.bank, Physical.src930.bank, Physical.src929.bank, Physical.src927.bank] i
  reserve i := ![0, 1, 4, 8, 20, 50, 110, 110, 145, 110, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 386273
  seedFloor := 25

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank919
    · exact Physical.rank920
    · exact Physical.rank921
    · exact Physical.rank922
    · exact Physical.rank923
    · exact Physical.rank926
    · exact Physical.rank928
    · exact Physical.rank929
    · exact Physical.rank930
    · exact Physical.rank929
    · exact Physical.rank927
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover928⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover930⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩

def price : EarlyPrice := ⟨3, 25, 10, 25306652693209/33392353607680, 14121/19100, ![9382702436184, 843373193666, 29862878540, 2389052510], 4455611757597307⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons21
end Z6969Source1497


section Z6969Source1501
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons22
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,26⟩
  bank i := ![Physical.src931.bank, Physical.src932.bank, Physical.src933.bank, Physical.src934.bank, Physical.src935.bank, Physical.src936.bank, Physical.src937.bank, Physical.src938.bank, Physical.src941.bank, Physical.src942.bank, Physical.src943.bank] i
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 20, 65, 145, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 386273
  seedFloor := 26

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank931
    · exact Physical.rank932
    · exact Physical.rank933
    · exact Physical.rank934
    · exact Physical.rank935
    · exact Physical.rank936
    · exact Physical.rank937
    · exact Physical.rank938
    · exact Physical.rank941
    · exact Physical.rank942
    · exact Physical.rank943
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover936⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover942⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩

def price : EarlyPrice := ⟨3, 26, 10, 109312514724599/144199022280704, 59107/82480, ![5024388324655, 479687415781, 31138325370, 2395278054], 2982228084686982⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons22
end Z6969Source1501


section Z6969Source1504
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons23
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,27⟩
  bank i := ![Physical.src944.bank, Physical.src945.bank, Physical.src946.bank, Physical.src947.bank, Physical.src948.bank, Physical.src949.bank, Physical.src950.bank, Physical.src951.bank, Physical.src954.bank, Physical.src955.bank, Physical.src956.bank] i
  reserve i := ![0, 1, 2, 4, 6, 8, 13, 32, 65, 145, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 386273
  seedFloor := 27

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank944
    · exact Physical.rank945
    · exact Physical.rank946
    · exact Physical.rank947
    · exact Physical.rank948
    · exact Physical.rank949
    · exact Physical.rank950
    · exact Physical.rank951
    · exact Physical.rank954
    · exact Physical.rank955
    · exact Physical.rank956
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover955⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩

def price : EarlyPrice := ⟨3, 27, 10, 793274305752091/1083101094608896, 55491/77440, ![2773821540745, 302246919239, 32251906490, 2389052510], 2152314020788253⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons23
end Z6969Source1504


section Z6969Source1508
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons24
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,28⟩
  bank i := ![Physical.src957.bank, Physical.src958.bank, Physical.src959.bank, Physical.src960.bank, Physical.src961.bank, Physical.src962.bank, Physical.src963.bank, Physical.src964.bank, Physical.src965.bank, Physical.src968.bank, Physical.src969.bank] i
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 13, 32, 145, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 28

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank957
    · exact Physical.rank958
    · exact Physical.rank959
    · exact Physical.rank960
    · exact Physical.rank961
    · exact Physical.rank962
    · exact Physical.rank963
    · exact Physical.rank964
    · exact Physical.rank965
    · exact Physical.rank968
    · exact Physical.rank969
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover957⟩
    · exact ⟨_, Physical.cover958⟩
    · exact ⟨_, Physical.cover959⟩
    · exact ⟨_, Physical.cover960⟩
    · exact ⟨_, Physical.cover961⟩
    · exact ⟨_, Physical.cover962⟩
    · exact ⟨_, Physical.cover963⟩
    · exact ⟨_, Physical.cover964⟩
    · exact ⟨_, Physical.cover965⟩
    · exact ⟨_, Physical.cover968⟩
    · exact ⟨_, Physical.cover969⟩

def price : EarlyPrice := ⟨3, 28, 10, 423441031275785758827321/569071495601818362707968, 38218/53003, ![2063023245200, 245749315466, 33446422000, 2389052510], 1877808752861352⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons24
end Z6969Source1508


section Z6969Source1512
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons25
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,29⟩
  bank i := ![Physical.src970.bank, Physical.src971.bank, Physical.src972.bank, Physical.src973.bank, Physical.src974.bank, Physical.src975.bank, Physical.src976.bank, Physical.src980.bank, Physical.src979.bank, Physical.src982.bank, Physical.src981.bank] i
  reserve i := ![0, 1, 2, 3, 6, 16, 32, 85, 85, 145, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 386273
  seedFloor := 29

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank970
    · exact Physical.rank971
    · exact Physical.rank972
    · exact Physical.rank973
    · exact Physical.rank974
    · exact Physical.rank975
    · exact Physical.rank976
    · exact Physical.rank980
    · exact Physical.rank979
    · exact Physical.rank982
    · exact Physical.rank981
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover979⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩

def price : EarlyPrice := ⟨3, 29, 10, 1547487664455187669294069/2113613942158218659627008, 17246/25537, ![1469610743706, 212881329029, 34640937510, 2389052510], 1589554554458369⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons25
end Z6969Source1512


section Z6969Source1515
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons26
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,30⟩
  bank i := ![Physical.src983.bank, Physical.src984.bank, Physical.src985.bank, Physical.src986.bank, Physical.src987.bank, Physical.src988.bank, Physical.src989.bank, Physical.src992.bank, Physical.src993.bank, Physical.src995.bank, Physical.src994.bank] i
  reserve i := ![0, 1, 2, 4, 6, 10, 25, 65, 85, 190, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 30

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank983
    · exact Physical.rank984
    · exact Physical.rank985
    · exact Physical.rank986
    · exact Physical.rank987
    · exact Physical.rank988
    · exact Physical.rank989
    · exact Physical.rank992
    · exact Physical.rank993
    · exact Physical.rank995
    · exact Physical.rank994
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover983⟩
    · exact ⟨_, Physical.cover984⟩
    · exact ⟨_, Physical.cover985⟩
    · exact ⟨_, Physical.cover986⟩
    · exact ⟨_, Physical.cover987⟩
    · exact ⟨_, Physical.cover988⟩
    · exact ⟨_, Physical.cover989⟩
    · exact ⟨_, Physical.cover992⟩
    · exact ⟨_, Physical.cover993⟩
    · exact ⟨_, Physical.cover995⟩
    · exact ⟨_, Physical.cover994⟩

def price : EarlyPrice := ⟨3, 30, 10, 1057336534749314294891331/1513829074133402244874240, 178936/246415, ![2212191194845, 274107174461, 36208979070, 2413954686], 1685401756593359⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons26
end Z6969Source1515


section Z6969Source1519
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons27
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,31⟩
  bank i := ![Physical.src996.bank, Physical.src997.bank, Physical.src998.bank, Physical.src999.bank, Physical.src1000.bank, Physical.src1001.bank, Physical.src1002.bank, Physical.src1003.bank, Physical.src1006.bank, Physical.src1008.bank, Physical.src1007.bank] i
  reserve i := ![0, 1, 2, 3, 6, 8, 16, 32, 65, 145, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 386273
  seedFloor := 31

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank996
    · exact Physical.rank997
    · exact Physical.rank998
    · exact Physical.rank999
    · exact Physical.rank1000
    · exact Physical.rank1001
    · exact Physical.rank1002
    · exact Physical.rank1003
    · exact Physical.rank1006
    · exact Physical.rank1008
    · exact Physical.rank1007
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover1007⟩

def price : EarlyPrice := ⟨3, 31, 10, 622745112039187/852536508547072, 32429/48764, ![1396415677938, 189013105462, 30733665144, 1982835764], 1278871587520948⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons27
end Z6969Source1519


section Z6969Source1523
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons28
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,32⟩
  bank i := ![Physical.src1009.bank, Physical.src1010.bank, Physical.src1011.bank, Physical.src1012.bank, Physical.src1013.bank, Physical.src1014.bank, Physical.src1015.bank, Physical.src1016.bank, Physical.src1019.bank, Physical.src1018.bank, Physical.src1017.bank] i
  reserve i := ![0, 1, 2, 4, 6, 10, 25, 65, 145, 110, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 32

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1009
    · exact Physical.rank1010
    · exact Physical.rank1011
    · exact Physical.rank1012
    · exact Physical.rank1013
    · exact Physical.rank1014
    · exact Physical.rank1015
    · exact Physical.rank1016
    · exact Physical.rank1019
    · exact Physical.rank1018
    · exact Physical.rank1017
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1009⟩
    · exact ⟨_, Physical.cover1010⟩
    · exact ⟨_, Physical.cover1011⟩
    · exact ⟨_, Physical.cover1012⟩
    · exact ⟨_, Physical.cover1013⟩
    · exact ⟨_, Physical.cover1014⟩
    · exact ⟨_, Physical.cover1015⟩
    · exact ⟨_, Physical.cover1016⟩
    · exact ⟨_, Physical.cover1019⟩
    · exact ⟨_, Physical.cover1018⟩
    · exact ⟨_, Physical.cover1017⟩

def price : EarlyPrice := ⟨3, 32, 10, 581904898351603/820228095213568, 8428/11729, ![1138940121254, 183173128229, 31725074108, 1982835764], 1182227745950883⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons28
end Z6969Source1523


end Research6970.Height2313
end Pack_R6970Height2313OrdinaryPlans03

section Pack_R6970Height2313OrdinaryPlans04

set_option Elab.async false

namespace Research6970.Height2313

open _root_.Lower6960 _root_.Research6969

section Z6969Source1526
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons29
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,33⟩
  bank i := ![Physical.src1020.bank, Physical.src1021.bank, Physical.src1022.bank, Physical.src1023.bank, Physical.src1024.bank, Physical.src1025.bank, Physical.src1026.bank, Physical.src1027.bank, Physical.src1030.bank, Physical.src1031.bank, Physical.src1032.bank] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 25, 65, 145, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 33

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1020
    · exact Physical.rank1021
    · exact Physical.rank1022
    · exact Physical.rank1023
    · exact Physical.rank1024
    · exact Physical.rank1025
    · exact Physical.rank1026
    · exact Physical.rank1027
    · exact Physical.rank1030
    · exact Physical.rank1031
    · exact Physical.rank1032
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1020⟩
    · exact ⟨_, Physical.cover1021⟩
    · exact ⟨_, Physical.cover1022⟩
    · exact ⟨_, Physical.cover1023⟩
    · exact ⟨_, Physical.cover1024⟩
    · exact ⟨_, Physical.cover1025⟩
    · exact ⟨_, Physical.cover1026⟩
    · exact ⟨_, Physical.cover1027⟩
    · exact ⟨_, Physical.cover1030⟩
    · exact ⟨_, Physical.cover1031⟩
    · exact ⟨_, Physical.cover1032⟩

def price : EarlyPrice := ⟨3, 33, 10, 571764876764183/816381855531008, 8539/11674, ![1486507049344, 229792078123, 39418996480, 2389052510], 1300537093371953⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons29
end Z6969Source1526


section Z6969Source1529
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons3
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 9
  positive := by decide
  primeShape := ⟨0,3,1,7⟩
  bank i := ![Physical.src698.bank, Physical.src699.bank, Physical.src700.bank, Physical.src701.bank, Physical.src702.bank, Physical.src703.bank, Physical.src704.bank, Physical.src705.bank, Physical.src706.bank] i
  reserve i := ![0, 2, 4, 10, 16, 25, 40, 65, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 386273
  seedFloor := 7

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank698
    · exact Physical.rank699
    · exact Physical.rank700
    · exact Physical.rank701
    · exact Physical.rank702
    · exact Physical.rank703
    · exact Physical.rank704
    · exact Physical.rank705
    · exact Physical.rank706
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover698⟩
    · exact ⟨_, Physical.cover699⟩
    · exact ⟨_, Physical.cover700⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover703⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover706⟩

def price : EarlyPrice := ⟨3, 7, 8, 594660187740209/616237528776704, 236981/290796, ![1716279977767, 520174693606, 8198195530, 2342360930], 9981756426606969⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons3
end Z6969Source1529


section Z6969Source1533
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons30
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,34⟩
  bank i := ![Physical.src1033.bank, Physical.src1034.bank, Physical.src1035.bank, Physical.src1036.bank, Physical.src1037.bank, Physical.src1038.bank, Physical.src1039.bank, Physical.src1040.bank, Physical.src1043.bank, Physical.src1045.bank, Physical.src1044.bank] i
  reserve i := ![0, 1, 2, 3, 4, 8, 20, 40, 110, 190, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 34

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1033
    · exact Physical.rank1034
    · exact Physical.rank1035
    · exact Physical.rank1036
    · exact Physical.rank1037
    · exact Physical.rank1038
    · exact Physical.rank1039
    · exact Physical.rank1040
    · exact Physical.rank1043
    · exact Physical.rank1045
    · exact Physical.rank1044
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1033⟩
    · exact ⟨_, Physical.cover1034⟩
    · exact ⟨_, Physical.cover1035⟩
    · exact ⟨_, Physical.cover1036⟩
    · exact ⟨_, Physical.cover1037⟩
    · exact ⟨_, Physical.cover1038⟩
    · exact ⟨_, Physical.cover1039⟩
    · exact ⟨_, Physical.cover1040⟩
    · exact ⟨_, Physical.cover1043⟩
    · exact ⟨_, Physical.cover1045⟩
    · exact ⟨_, Physical.cover1044⟩

def price : EarlyPrice := ⟨3, 34, 10, 16147761937093/24023700471808, 14953/21986, ![1360420257260, 223747027939, 40613508920, 2389052510], 1182411962147603⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons30
end Z6969Source1533


section Z6969Source1537
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons31
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,35⟩
  bank i := ![Physical.src1046.bank, Physical.src1047.bank, Physical.src1048.bank, Physical.src1049.bank, Physical.src1050.bank, Physical.src1051.bank, Physical.src1052.bank, Physical.src1053.bank, Physical.src1056.bank, Physical.src1057.bank, Physical.src1058.bank] i
  reserve i := ![0, 1, 2, 3, 4, 8, 16, 32, 65, 145, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 35

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1046
    · exact Physical.rank1047
    · exact Physical.rank1048
    · exact Physical.rank1049
    · exact Physical.rank1050
    · exact Physical.rank1051
    · exact Physical.rank1052
    · exact Physical.rank1053
    · exact Physical.rank1056
    · exact Physical.rank1057
    · exact Physical.rank1058
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1046⟩
    · exact ⟨_, Physical.cover1047⟩
    · exact ⟨_, Physical.cover1048⟩
    · exact ⟨_, Physical.cover1049⟩
    · exact ⟨_, Physical.cover1050⟩
    · exact ⟨_, Physical.cover1051⟩
    · exact ⟨_, Physical.cover1052⟩
    · exact ⟨_, Physical.cover1053⟩
    · exact ⟨_, Physical.cover1056⟩
    · exact ⟨_, Physical.cover1057⟩
    · exact ⟨_, Physical.cover1058⟩

def price : EarlyPrice := ⟨3, 35, 10, 78653878479452434516465/116631196957853658120192, 71929/117552, ![1576598304979, 212138929341, 35611721135, 2034974695], 1092319675896287⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons31
end Z6969Source1537


section Z6969Source1540
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons32
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,3,1,36⟩
  bank i := ![Physical.src1059.bank, Physical.src1060.bank, Physical.src1061.bank, Physical.src1062.bank, Physical.src1063.bank, Physical.src1064.bank, Physical.src1065.bank, Physical.src1066.bank, Physical.src1069.bank, Physical.src1070.bank] i
  reserve i := ![0, 1, 2, 3, 6, 8, 16, 40, 110, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 36

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1059
    · exact Physical.rank1060
    · exact Physical.rank1061
    · exact Physical.rank1062
    · exact Physical.rank1063
    · exact Physical.rank1064
    · exact Physical.rank1065
    · exact Physical.rank1066
    · exact Physical.rank1069
    · exact Physical.rank1070
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1059⟩
    · exact ⟨_, Physical.cover1060⟩
    · exact ⟨_, Physical.cover1061⟩
    · exact ⟨_, Physical.cover1062⟩
    · exact ⟨_, Physical.cover1063⟩
    · exact ⟨_, Physical.cover1064⟩
    · exact ⟨_, Physical.cover1065⟩
    · exact ⟨_, Physical.cover1066⟩
    · exact ⟨_, Physical.cover1069⟩
    · exact ⟨_, Physical.cover1070⟩

def price : EarlyPrice := ⟨3, 36, 9, 20079258400001/29100299780096, 4483/6658, ![1011638253924, 161131653768, 29667550356, 1648212774], 917462720961849⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons32
end Z6969Source1540


section Z6969Source1544
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons33
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,37⟩
  bank i := ![Physical.src1071.bank, Physical.src1072.bank, Physical.src1073.bank, Physical.src1074.bank, Physical.src1075.bank, Physical.src1076.bank, Physical.src1077.bank, Physical.src1078.bank, Physical.src1081.bank, Physical.src1082.bank, Physical.src1083.bank] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 25, 85, 190, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 37

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1071
    · exact Physical.rank1072
    · exact Physical.rank1073
    · exact Physical.rank1074
    · exact Physical.rank1075
    · exact Physical.rank1076
    · exact Physical.rank1077
    · exact Physical.rank1078
    · exact Physical.rank1081
    · exact Physical.rank1082
    · exact Physical.rank1083
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1071⟩
    · exact ⟨_, Physical.cover1072⟩
    · exact ⟨_, Physical.cover1073⟩
    · exact ⟨_, Physical.cover1074⟩
    · exact ⟨_, Physical.cover1075⟩
    · exact ⟨_, Physical.cover1076⟩
    · exact ⟨_, Physical.cover1077⟩
    · exact ⟨_, Physical.cover1078⟩
    · exact ⟨_, Physical.cover1081⟩
    · exact ⟨_, Physical.cover1082⟩
    · exact ⟨_, Physical.cover1083⟩

def price : EarlyPrice := ⟨3, 37, 10, 20291970315043/29563596832768, 643/890, ![1874358121064, 257691681936, 44197052380, 2389052510], 1147360411718556⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons33
end Z6969Source1544


section Z6969Source1548
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons34
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,38⟩
  bank i := ![Physical.src1084.bank, Physical.src1085.bank, Physical.src1086.bank, Physical.src1087.bank, Physical.src1088.bank, Physical.src1089.bank, Physical.src1090.bank, Physical.src1091.bank, Physical.src1094.bank, Physical.src1095.bank, Physical.src1096.bank] i
  reserve i := ![0, 1, 3, 4, 6, 10, 16, 32, 85, 145, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 38

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1084
    · exact Physical.rank1085
    · exact Physical.rank1086
    · exact Physical.rank1087
    · exact Physical.rank1088
    · exact Physical.rank1089
    · exact Physical.rank1090
    · exact Physical.rank1091
    · exact Physical.rank1094
    · exact Physical.rank1095
    · exact Physical.rank1096
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1084⟩
    · exact ⟨_, Physical.cover1085⟩
    · exact ⟨_, Physical.cover1086⟩
    · exact ⟨_, Physical.cover1087⟩
    · exact ⟨_, Physical.cover1088⟩
    · exact ⟨_, Physical.cover1089⟩
    · exact ⟨_, Physical.cover1090⟩
    · exact ⟨_, Physical.cover1091⟩
    · exact ⟨_, Physical.cover1094⟩
    · exact ⟨_, Physical.cover1095⟩
    · exact ⟨_, Physical.cover1096⟩

def price : EarlyPrice := ⟨3, 38, 10, 73207284670679/110631839596544, 15051012848170745308939/24334371007270018351104, ![1352491296798, 195783543997, 38664153105, 2034974695], 938246221073386⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons34
end Z6969Source1548


section Z6969Source1551
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons35
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,39⟩
  bank i := ![Physical.src1097.bank, Physical.src1098.bank, Physical.src1099.bank, Physical.src1100.bank, Physical.src1101.bank, Physical.src1102.bank, Physical.src1103.bank, Physical.src1106.bank, Physical.src1109.bank, Physical.src1108.bank, Physical.src1107.bank] i
  reserve i := ![0, 1, 2, 3, 4, 8, 25, 110, 245, 190, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 39

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1097
    · exact Physical.rank1098
    · exact Physical.rank1099
    · exact Physical.rank1100
    · exact Physical.rank1101
    · exact Physical.rank1102
    · exact Physical.rank1103
    · exact Physical.rank1106
    · exact Physical.rank1109
    · exact Physical.rank1108
    · exact Physical.rank1107
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1097⟩
    · exact ⟨_, Physical.cover1098⟩
    · exact ⟨_, Physical.cover1099⟩
    · exact ⟨_, Physical.cover1100⟩
    · exact ⟨_, Physical.cover1101⟩
    · exact ⟨_, Physical.cover1102⟩
    · exact ⟨_, Physical.cover1103⟩
    · exact ⟨_, Physical.cover1106⟩
    · exact ⟨_, Physical.cover1109⟩
    · exact ⟨_, Physical.cover1108⟩
    · exact ⟨_, Physical.cover1107⟩

def price : EarlyPrice := ⟨3, 39, 10, 204306776929337/321580603277312, 16556/27591, ![1561589794960, 243937832004, 47800053000, 2451307950], 1046299348056105⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons35
end Z6969Source1551


section Z6969Source1554
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons36
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,40⟩
  bank i := ![Physical.src1110.bank, Physical.src1111.bank, Physical.src1112.bank, Physical.src1113.bank, Physical.src1114.bank, Physical.src1115.bank, Physical.src1116.bank, Physical.src1117.bank, Physical.src1118.bank, Physical.src1121.bank, Physical.src1122.bank] i
  reserve i := ![0, 1, 2, 3, 4, 8, 13, 20, 40, 145, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 385979
  seedFloor := 40

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1110
    · exact Physical.rank1111
    · exact Physical.rank1112
    · exact Physical.rank1113
    · exact Physical.rank1114
    · exact Physical.rank1115
    · exact Physical.rank1116
    · exact Physical.rank1117
    · exact Physical.rank1118
    · exact Physical.rank1121
    · exact Physical.rank1122
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1110⟩
    · exact ⟨_, Physical.cover1111⟩
    · exact ⟨_, Physical.cover1112⟩
    · exact ⟨_, Physical.cover1113⟩
    · exact ⟨_, Physical.cover1114⟩
    · exact ⟨_, Physical.cover1115⟩
    · exact ⟨_, Physical.cover1116⟩
    · exact ⟨_, Physical.cover1117⟩
    · exact ⟨_, Physical.cover1118⟩
    · exact ⟨_, Physical.cover1121⟩
    · exact ⟨_, Physical.cover1122⟩

def price : EarlyPrice := ⟨3, 40, 10, 124575035913415625701507/187898163038044853108736, 64853/105504, ![1423674991488, 187118517170, 33835509888, 1691791582], 873687683284398⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons36
end Z6969Source1554


section Z6969Source1558
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons4
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,3,1,8⟩
  bank i := ![Physical.src707.bank, Physical.src708.bank, Physical.src709.bank, Physical.src710.bank, Physical.src711.bank, Physical.src712.bank, Physical.src714.bank, Physical.src713.bank, Physical.src715.bank, Physical.src716.bank] i
  reserve i := ![0, 1, 2, 4, 10, 16, 32, 32, 65, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 386273
  seedFloor := 8

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank707
    · exact Physical.rank708
    · exact Physical.rank709
    · exact Physical.rank710
    · exact Physical.rank711
    · exact Physical.rank712
    · exact Physical.rank714
    · exact Physical.rank713
    · exact Physical.rank715
    · exact Physical.rank716
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover708⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover712⟩
    · exact ⟨_, Physical.cover714⟩
    · exact ⟨_, Physical.cover713⟩
    · exact ⟨_, Physical.cover715⟩
    · exact ⟨_, Physical.cover716⟩

def price : EarlyPrice := ⟨3, 8, 9, 104834302863143/111471019163648, 240884/289311, ![1388652020028, 370308301857, 9369365460, 2342360930], 8867219286289252⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons4
end Z6969Source1558


section Z6969Source1561
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons5
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,9⟩
  bank i := ![Physical.src717.bank, Physical.src718.bank, Physical.src719.bank, Physical.src720.bank, Physical.src721.bank, Physical.src722.bank, Physical.src723.bank, Physical.src725.bank, Physical.src727.bank, Physical.src728.bank, Physical.src729.bank] i
  reserve i := ![0, 1, 2, 4, 6, 10, 16, 25, 40, 65, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 386273
  seedFloor := 9

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank717
    · exact Physical.rank718
    · exact Physical.rank719
    · exact Physical.rank720
    · exact Physical.rank721
    · exact Physical.rank722
    · exact Physical.rank723
    · exact Physical.rank725
    · exact Physical.rank727
    · exact Physical.rank728
    · exact Physical.rank729
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover718⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover727⟩
    · exact ⟨_, Physical.cover728⟩
    · exact ⟨_, Physical.cover729⟩

def price : EarlyPrice := ⟨3, 9, 10, 1063804334981413/1119185815994368, 1003554137149399578823019/1245186078588767953747968, ![2147772408353, 495622407115, 10540535390, 2342360930], 8787192329703230⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons5
end Z6969Source1561


section Z6969Source1565
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons6
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,3,1,10⟩
  bank i := ![Physical.src730.bank, Physical.src731.bank, Physical.src732.bank, Physical.src733.bank, Physical.src734.bank, Physical.src735.bank, Physical.src736.bank, Physical.src737.bank, Physical.src738.bank, Physical.src739.bank] i
  reserve i := ![0, 1, 2, 4, 8, 16, 32, 65, 85, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 386273
  seedFloor := 10

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank730
    · exact Physical.rank731
    · exact Physical.rank732
    · exact Physical.rank733
    · exact Physical.rank734
    · exact Physical.rank735
    · exact Physical.rank736
    · exact Physical.rank737
    · exact Physical.rank738
    · exact Physical.rank739
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover734⟩
    · exact ⟨_, Physical.cover735⟩
    · exact ⟨_, Physical.cover736⟩
    · exact ⟨_, Physical.cover737⟩
    · exact ⟨_, Physical.cover738⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩

def price : EarlyPrice := ⟨3, 10, 9, 102834899920315/111960540577792, 351067/432270, ![4137230823231, 851670549637, 11742829758, 2348586474], 10931403868289327⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons6
end Z6969Source1565


end Research6970.Height2313
end Pack_R6970Height2313OrdinaryPlans04

section Pack_R6970Height2313OrdinaryPlans05

set_option Elab.async false

namespace Research6970.Height2313

open _root_.Lower6960 _root_.Research6969

section Z6969Source1569
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons7
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,11⟩
  bank i := ![Physical.src740.bank, Physical.src741.bank, Physical.src742.bank, Physical.src743.bank, Physical.src744.bank, Physical.src745.bank, Physical.src746.bank, Physical.src747.bank, Physical.src750.bank, Physical.src748.bank, Physical.src749.bank] i
  reserve i := ![0, 1, 2, 4, 10, 16, 25, 40, 110, 85, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 386273
  seedFloor := 11

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank740
    · exact Physical.rank741
    · exact Physical.rank742
    · exact Physical.rank743
    · exact Physical.rank744
    · exact Physical.rank745
    · exact Physical.rank746
    · exact Physical.rank747
    · exact Physical.rank750
    · exact Physical.rank748
    · exact Physical.rank749
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover741⟩
    · exact ⟨_, Physical.cover742⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover747⟩
    · exact ⟨_, Physical.cover750⟩
    · exact ⟨_, Physical.cover748⟩
    · exact ⟨_, Physical.cover749⟩

def price : EarlyPrice := ⟨3, 11, 10, 283231293769073/303538242584576, 5720745505439882549025/7632651725984358465536, ![8947073450224, 1659064781394, 12882872240, 2342360930], 14461870963149186⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons7
end Z6969Source1569


section Z6969Source1572
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons8
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,12⟩
  bank i := ![Physical.src751.bank, Physical.src752.bank, Physical.src753.bank, Physical.src754.bank, Physical.src755.bank, Physical.src756.bank, Physical.src757.bank, Physical.src758.bank, Physical.src759.bank, Physical.src760.bank, Physical.src761.bank] i
  reserve i := ![0, 1, 2, 4, 8, 10, 16, 32, 65, 85, 85] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 386273
  seedFloor := 12

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank751
    · exact Physical.rank752
    · exact Physical.rank753
    · exact Physical.rank754
    · exact Physical.rank755
    · exact Physical.rank756
    · exact Physical.rank757
    · exact Physical.rank758
    · exact Physical.rank759
    · exact Physical.rank760
    · exact Physical.rank761
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover758⟩
    · exact ⟨_, Physical.cover759⟩
    · exact ⟨_, Physical.cover760⟩
    · exact ⟨_, Physical.cover761⟩

def price : EarlyPrice := ⟨3, 12, 10, 3381312064199997649102957/3779842350832107508989952, 1251277/1502611, ![4339855538277, 752357515573, 14054042170, 2342360930], 9330414569784417⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons8
end Z6969Source1572


section Z6969Source1575
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.CubicSingletons9
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,13⟩
  bank i := ![Physical.src762.bank, Physical.src763.bank, Physical.src764.bank, Physical.src765.bank, Physical.src766.bank, Physical.src767.bank, Physical.src768.bank, Physical.src772.bank, Physical.src774.bank, Physical.src775.bank, Physical.src776.bank] i
  reserve i := ![0, 1, 2, 3, 6, 10, 20, 32, 40, 85, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 386273
  seedFloor := 13

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank762
    · exact Physical.rank763
    · exact Physical.rank764
    · exact Physical.rank765
    · exact Physical.rank766
    · exact Physical.rank767
    · exact Physical.rank768
    · exact Physical.rank772
    · exact Physical.rank774
    · exact Physical.rank775
    · exact Physical.rank776
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover764⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover768⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover775⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩

def price : EarlyPrice := ⟨3, 13, 10, 40866712431495041994579233/44383594408341465687130112, 338929/437857, ![4569278363190, 734515083987, 15387074820, 2367263106], 8561430781605200⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.CubicSingletons9
end Z6969Source1575


section Z6969Source1579
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases0
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,3,1,1⟩
  bank i := ![Physical.src640.bank, Physical.src641.bank, Physical.src642.bank, Physical.src643.bank, Physical.src644.bank, Physical.src646.bank, Physical.src645.bank, Physical.src647.bank, Physical.src648.bank, Physical.src651.bank] i
  reserve i := ![0, 1, 2, 4, 6, 10, 8, 13, 20, 50] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 386273
  seedFloor := 1

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank640
    · exact Physical.rank641
    · exact Physical.rank642
    · exact Physical.rank643
    · exact Physical.rank644
    · exact Physical.rank646
    · exact Physical.rank645
    · exact Physical.rank647
    · exact Physical.rank648
    · exact Physical.rank651
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover640⟩
    · exact ⟨_, Physical.cover641⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover644⟩
    · exact ⟨_, Physical.cover646⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover647⟩
    · exact ⟨_, Physical.cover648⟩
    · exact ⟨_, Physical.cover651⟩

def price : EarlyPrice := ⟨3, 1, 9, 2320287954989047/2329492546650112, 297794/366421, ![149341654152, 301109722477, 667690452, 1335379188], 11075098983657405⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.HigherHelperCases0
end Z6969Source1579


section Z6969Source1582
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases1
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,3,1,3⟩
  bank i := ![Physical.src652.bank, Physical.src653.bank, Physical.src654.bank, Physical.src655.bank, Physical.src657.bank, Physical.src656.bank, Physical.src658.bank, Physical.src659.bank, Physical.src661.bank, Physical.src663.bank, Physical.src664.bank] i
  reserve i := ![0, 1, 2, 4, 10, 6, 13, 20, 25, 40, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 3
  slopeFloor := 1
  physicalFloor := 386273
  seedFloor := 2

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank652
    · exact Physical.rank653
    · exact Physical.rank654
    · exact Physical.rank655
    · exact Physical.rank657
    · exact Physical.rank656
    · exact Physical.rank658
    · exact Physical.rank659
    · exact Physical.rank661
    · exact Physical.rank663
    · exact Physical.rank664
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover653⟩
    · exact ⟨_, Physical.cover654⟩
    · exact ⟨_, Physical.cover655⟩
    · exact ⟨_, Physical.cover657⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover659⟩
    · exact ⟨_, Physical.cover661⟩
    · exact ⟨_, Physical.cover663⟩
    · exact ⟨_, Physical.cover664⟩

def price : EarlyPrice := ⟨3, 3, 10, 320220676290181/324168073609216, 580962/713867, ![923788933483, 628636296262, 3513521830, 2342360930], 13508539388765422⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.HigherHelperCases1
end Z6969Source1582


section Z6969Source1587
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases2
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,4,1,1⟩
  bank i := ![Physical.src1206.bank, Physical.src1207.bank, Physical.src1208.bank, Physical.src1210.bank, Physical.src1211.bank, Physical.src1209.bank, Physical.src1212.bank, Physical.src1213.bank, Physical.src1214.bank, Physical.src1217.bank, Physical.src1218.bank] i
  reserve i := ![0, 1, 2, 3, 6, 3, 10, 13, 25, 65, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 4
  slopeFloor := 1
  physicalFloor := 515031
  seedFloor := 1

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1206
    · exact Physical.rank1207
    · exact Physical.rank1208
    · exact Physical.rank1210
    · exact Physical.rank1211
    · exact Physical.rank1209
    · exact Physical.rank1212
    · exact Physical.rank1213
    · exact Physical.rank1214
    · exact Physical.rank1217
    · exact Physical.rank1218
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover1212⟩
    · exact ⟨_, Physical.cover1213⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover1217⟩
    · exact ⟨_, Physical.cover1218⟩

def price : EarlyPrice := ⟨4, 1, 10, 88159310106719/92799273795584, 21025/25213, ![104986152540, 317878178976, 981120374, 2472309630], 2769344246723246⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.HigherHelperCases2
end Z6969Source1587


section Z6969Source1591
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases3
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,4,1,3⟩
  bank i := ![Physical.src1219.bank, Physical.src1220.bank, Physical.src1221.bank, Physical.src1222.bank, Physical.src1223.bank, Physical.src1224.bank, Physical.src1225.bank, Physical.src1227.bank, Physical.src1229.bank, Physical.src1230.bank] i
  reserve i := ![0, 1, 3, 8, 13, 20, 32, 50, 85, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 4
  slopeFloor := 1
  physicalFloor := 515031
  seedFloor := 2

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1219
    · exact Physical.rank1220
    · exact Physical.rank1221
    · exact Physical.rank1222
    · exact Physical.rank1223
    · exact Physical.rank1224
    · exact Physical.rank1225
    · exact Physical.rank1227
    · exact Physical.rank1229
    · exact Physical.rank1230
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1219⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover1222⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover1224⟩
    · exact ⟨_, Physical.cover1225⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩

def price : EarlyPrice := ⟨4, 3, 9, 790074171108271/806171837464576, 165659/207504, ![399704546709, 412465969311, 3518190962, 3518196990], 2838359312697056⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.HigherHelperCases3
end Z6969Source1591


section Z6969Source1594
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases4
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,4,1,8⟩
  bank i := ![Physical.src1231.bank, Physical.src1232.bank, Physical.src1233.bank, Physical.src1234.bank, Physical.src1235.bank, Physical.src1236.bank, Physical.src1240.bank, Physical.src1238.bank, Physical.src1241.bank, Physical.src1242.bank] i
  reserve i := ![0, 1, 3, 10, 20, 32, 65, 50, 85, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 4
  slopeFloor := 1
  physicalFloor := 515031
  seedFloor := 4

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1231
    · exact Physical.rank1232
    · exact Physical.rank1233
    · exact Physical.rank1234
    · exact Physical.rank1235
    · exact Physical.rank1236
    · exact Physical.rank1240
    · exact Physical.rank1238
    · exact Physical.rank1241
    · exact Physical.rank1242
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover1232⟩
    · exact ⟨_, Physical.cover1233⟩
    · exact ⟨_, Physical.cover1234⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover1236⟩
    · exact ⟨_, Physical.cover1240⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover1241⟩
    · exact ⟨_, Physical.cover1242⟩

def price : EarlyPrice := ⟨4, 8, 9, 195355063389119/206088515354624, 85488478830147062273017/112591647784988261220352, ![3733785518190, 1411011335601, 9556130220, 3583564950], 5932357530467308⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.HigherHelperCases4
end Z6969Source1594


section Z6969Source1598
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases5
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,4,1,15⟩
  bank i := ![Physical.src1243.bank, Physical.src1244.bank, Physical.src1245.bank, Physical.src1247.bank, Physical.src1246.bank, Physical.src1248.bank, Physical.src1249.bank, Physical.src1250.bank, Physical.src1254.bank, Physical.src1253.bank, Physical.src1255.bank] i
  reserve i := ![0, 1, 2, 4, 4, 8, 16, 25, 85, 85, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 4
  slopeFloor := 1
  physicalFloor := 515031
  seedFloor := 9

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1243
    · exact Physical.rank1244
    · exact Physical.rank1245
    · exact Physical.rank1247
    · exact Physical.rank1246
    · exact Physical.rank1248
    · exact Physical.rank1249
    · exact Physical.rank1250
    · exact Physical.rank1254
    · exact Physical.rank1253
    · exact Physical.rank1255
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1243⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover1249⟩
    · exact ⟨_, Physical.cover1250⟩
    · exact ⟨_, Physical.cover1254⟩
    · exact ⟨_, Physical.cover1253⟩
    · exact ⟨_, Physical.cover1255⟩

def price : EarlyPrice := ⟨4, 15, 10, 634650699761993/713582358560768, 18445/22959, ![5708046837555, 1161931726560, 14871134460, 2974242180], 5167000516323300⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.HigherHelperCases5
end Z6969Source1598


section Z6969Source1603
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases6
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,4,1,25⟩
  bank i := ![Physical.src1258.bank, Physical.src1259.bank, Physical.src1260.bank, Physical.src1261.bank, Physical.src1262.bank, Physical.src1264.bank, Physical.src1263.bank, Physical.src1265.bank, Physical.src1266.bank, Physical.src1267.bank] i
  reserve i := ![0, 1, 4, 8, 20, 50, 50, 145, 190, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 4
  slopeFloor := 1
  physicalFloor := 515031
  seedFloor := 16

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1258
    · exact Physical.rank1259
    · exact Physical.rank1260
    · exact Physical.rank1261
    · exact Physical.rank1262
    · exact Physical.rank1264
    · exact Physical.rank1263
    · exact Physical.rank1265
    · exact Physical.rank1266
    · exact Physical.rank1267
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover1263⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover1266⟩
    · exact ⟨_, Physical.cover1267⟩

def price : EarlyPrice := ⟨4, 25, 9, 7135471118425248354499969/8753770194357534005919744, 53774/73497, ![47707689658288, 5813385035942, 24824125744, 2978911320], 15967783190128462⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.HigherHelperCases6
end Z6969Source1603


section Z6969Source1606
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuarticIntervals0
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,4,1,29⟩
  bank i := ![Physical.src1274.bank, Physical.src1275.bank, Physical.src1276.bank, Physical.src1277.bank, Physical.src1278.bank, Physical.src1279.bank, Physical.src1280.bank, Physical.src1282.bank, Physical.src1283.bank, Physical.src1282.bank, Physical.src1281.bank] i
  reserve i := ![0, 1, 2, 6, 16, 50, 85, 190, 245, 190, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 4
  slopeFloor := 1
  physicalFloor := 515031
  seedFloor := 26

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1274
    · exact Physical.rank1275
    · exact Physical.rank1276
    · exact Physical.rank1277
    · exact Physical.rank1278
    · exact Physical.rank1279
    · exact Physical.rank1280
    · exact Physical.rank1282
    · exact Physical.rank1283
    · exact Physical.rank1282
    · exact Physical.rank1281
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover1283⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩

def price : EarlyPrice := ⟨4, 29, 10, 205553836084343/277208983666688, 16168523138698766541061/25463799618006350299136, ![25146183765606, 2703201545181, 35543632950, 3676947750], 6462166323273275⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuarticIntervals0
end Z6969Source1606


section Z6969Source1610
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuarticIntervals1
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,4,1,33⟩
  bank i := ![Physical.src1286.bank, Physical.src1287.bank, Physical.src1288.bank, Physical.src1289.bank, Physical.src1290.bank, Physical.src1291.bank, Physical.src1292.bank, Physical.src1294.bank, Physical.src1293.bank, Physical.src1295.bank, Physical.src1296.bank] i
  reserve i := ![0, 1, 3, 6, 8, 16, 40, 110, 110, 190, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 4
  slopeFloor := 1
  physicalFloor := 515031
  seedFloor := 30

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1286
    · exact Physical.rank1287
    · exact Physical.rank1288
    · exact Physical.rank1289
    · exact Physical.rank1290
    · exact Physical.rank1291
    · exact Physical.rank1292
    · exact Physical.rank1294
    · exact Physical.rank1293
    · exact Physical.rank1295
    · exact Physical.rank1296
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover1293⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover1296⟩

def price : EarlyPrice := ⟨4, 33, 10, 65439026731387/95439192850432, 30281/43672, ![9219730914816, 954069248268, 32716483072, 2974242180], 2671174079020074⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuarticIntervals1
end Z6969Source1610


end Research6970.Height2313
end Pack_R6970Height2313OrdinaryPlans05

section Pack_R6970Height2313OrdinaryPlans06

set_option Elab.async false

namespace Research6970.Height2313

open _root_.Lower6960 _root_.Research6969

section Z6969Source1614
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuarticIntervals2
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,4,1,37⟩
  bank i := ![Physical.src1299.bank, Physical.src1300.bank, Physical.src1301.bank, Physical.src1302.bank, Physical.src1303.bank, Physical.src1304.bank, Physical.src1305.bank, Physical.src1306.bank, Physical.src1309.bank, Physical.src1308.bank, Physical.src1307.bank] i
  reserve i := ![0, 1, 2, 3, 4, 8, 25, 65, 245, 245, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 4
  slopeFloor := 1
  physicalFloor := 514639
  seedFloor := 34

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1299
    · exact Physical.rank1300
    · exact Physical.rank1301
    · exact Physical.rank1302
    · exact Physical.rank1303
    · exact Physical.rank1304
    · exact Physical.rank1305
    · exact Physical.rank1306
    · exact Physical.rank1309
    · exact Physical.rank1308
    · exact Physical.rank1307
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1299⟩
    · exact ⟨_, Physical.cover1300⟩
    · exact ⟨_, Physical.cover1301⟩
    · exact ⟨_, Physical.cover1302⟩
    · exact ⟨_, Physical.cover1303⟩
    · exact ⟨_, Physical.cover1304⟩
    · exact ⟨_, Physical.cover1305⟩
    · exact ⟨_, Physical.cover1306⟩
    · exact ⟨_, Physical.cover1309⟩
    · exact ⟨_, Physical.cover1308⟩
    · exact ⟨_, Physical.cover1307⟩

def price : EarlyPrice := ⟨4, 37, 10, 451378310882693570501139/645490645755468210765824, 108281/159664, ![2374936527678, 321670724707, 44197052380, 3583564950], 1329479325067766⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuarticIntervals2
end Z6969Source1614


section Z6969Source1617
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuarticIntervals3
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,4,1,40⟩
  bank i := ![Physical.src1310.bank, Physical.src1311.bank, Physical.src1312.bank, Physical.src1313.bank, Physical.src1314.bank, Physical.src1315.bank, Physical.src1316.bank, Physical.src1317.bank, Physical.src1318.bank, Physical.src1319.bank, Physical.src1320.bank] i
  reserve i := ![0, 1, 2, 4, 6, 10, 20, 40, 65, 145, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 4
  slopeFloor := 1
  physicalFloor := 514639
  seedFloor := 38

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1310
    · exact Physical.rank1311
    · exact Physical.rank1312
    · exact Physical.rank1313
    · exact Physical.rank1314
    · exact Physical.rank1315
    · exact Physical.rank1316
    · exact Physical.rank1317
    · exact Physical.rank1318
    · exact Physical.rank1319
    · exact Physical.rank1320
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1310⟩
    · exact ⟨_, Physical.cover1311⟩
    · exact ⟨_, Physical.cover1312⟩
    · exact ⟨_, Physical.cover1313⟩
    · exact ⟨_, Physical.cover1314⟩
    · exact ⟨_, Physical.cover1315⟩
    · exact ⟨_, Physical.cover1316⟩
    · exact ⟨_, Physical.cover1317⟩
    · exact ⟨_, Physical.cover1318⟩
    · exact ⟨_, Physical.cover1319⟩
    · exact ⟨_, Physical.cover1320⟩

def price : EarlyPrice := ⟨4, 40, 10, 207628664826943/308328559280128, 20771628925065468883475/31501853977810772688896, ![1601630474496, 259573824300, 40699106880, 3052450275], 1008957023947794⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuarticIntervals3
end Z6969Source1617


section Z6969Source1621
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuarticIntervals4
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,4,1,44⟩
  bank i := ![Physical.src1321.bank, Physical.src1322.bank, Physical.src1323.bank, Physical.src1324.bank, Physical.src1325.bank, Physical.src1326.bank, Physical.src1327.bank, Physical.src1330.bank, Physical.src1333.bank, Physical.src1332.bank, Physical.src1331.bank] i
  reserve i := ![0, 1, 2, 3, 4, 8, 16, 85, 245, 190, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 4
  slopeFloor := 1
  physicalFloor := 514639
  seedFloor := 41

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1321
    · exact Physical.rank1322
    · exact Physical.rank1323
    · exact Physical.rank1324
    · exact Physical.rank1325
    · exact Physical.rank1326
    · exact Physical.rank1327
    · exact Physical.rank1330
    · exact Physical.rank1333
    · exact Physical.rank1332
    · exact Physical.rank1331
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1321⟩
    · exact ⟨_, Physical.cover1322⟩
    · exact ⟨_, Physical.cover1323⟩
    · exact ⟨_, Physical.cover1324⟩
    · exact ⟨_, Physical.cover1325⟩
    · exact ⟨_, Physical.cover1326⟩
    · exact ⟨_, Physical.cover1327⟩
    · exact ⟨_, Physical.cover1330⟩
    · exact ⟨_, Physical.cover1333⟩
    · exact ⟨_, Physical.cover1332⟩
    · exact ⟨_, Physical.cover1331⟩

def price : EarlyPrice := ⟨4, 44, 10, 329992582573/498262867968, 22001/32832, ![1566042472342, 261319217331, 43621971484, 2974242180], 1002835157223128⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuarticIntervals4
end Z6969Source1621


section Z6969Source1625
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuarticIntervals5
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,4,1,48⟩
  bank i := ![Physical.src1334.bank, Physical.src1335.bank, Physical.src1336.bank, Physical.src1337.bank, Physical.src1338.bank, Physical.src1339.bank, Physical.src1340.bank, Physical.src1341.bank, Physical.src1342.bank, Physical.src1343.bank, Physical.src1344.bank] i
  reserve i := ![0, 1, 2, 3, 4, 6, 13, 32, 65, 190, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 4
  slopeFloor := 1
  physicalFloor := 514639
  seedFloor := 45

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1334
    · exact Physical.rank1335
    · exact Physical.rank1336
    · exact Physical.rank1337
    · exact Physical.rank1338
    · exact Physical.rank1339
    · exact Physical.rank1340
    · exact Physical.rank1341
    · exact Physical.rank1342
    · exact Physical.rank1343
    · exact Physical.rank1344
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1334⟩
    · exact ⟨_, Physical.cover1335⟩
    · exact ⟨_, Physical.cover1336⟩
    · exact ⟨_, Physical.cover1337⟩
    · exact ⟨_, Physical.cover1338⟩
    · exact ⟨_, Physical.cover1339⟩
    · exact ⟨_, Physical.cover1340⟩
    · exact ⟨_, Physical.cover1341⟩
    · exact ⟨_, Physical.cover1342⟩
    · exact ⟨_, Physical.cover1343⟩
    · exact ⟨_, Physical.cover1344⟩

def price : EarlyPrice := ⟨4, 48, 10, 22452619200893/35354809991168, 11085/16178, ![1708409953196, 245859781028, 40602610996, 2537677590], 901791226057692⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuarticIntervals5
end Z6969Source1625


section Z6969Source1628
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuarticIntervals6
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,4,1,52⟩
  bank i := ![Physical.src1345.bank, Physical.src1346.bank, Physical.src1347.bank, Physical.src1348.bank, Physical.src1349.bank, Physical.src1350.bank, Physical.src1351.bank, Physical.src1354.bank, Physical.src1357.bank, Physical.src1356.bank, Physical.src1355.bank] i
  reserve i := ![0, 1, 2, 4, 8, 16, 40, 110, 245, 190, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 4
  slopeFloor := 1
  physicalFloor := 514639
  seedFloor := 49

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1345
    · exact Physical.rank1346
    · exact Physical.rank1347
    · exact Physical.rank1348
    · exact Physical.rank1349
    · exact Physical.rank1350
    · exact Physical.rank1351
    · exact Physical.rank1354
    · exact Physical.rank1357
    · exact Physical.rank1356
    · exact Physical.rank1355
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1345⟩
    · exact ⟨_, Physical.cover1346⟩
    · exact ⟨_, Physical.cover1347⟩
    · exact ⟨_, Physical.cover1348⟩
    · exact ⟨_, Physical.cover1349⟩
    · exact ⟨_, Physical.cover1350⟩
    · exact ⟨_, Physical.cover1351⟩
    · exact ⟨_, Physical.cover1354⟩
    · exact ⟨_, Physical.cover1357⟩
    · exact ⟨_, Physical.cover1356⟩
    · exact ⟨_, Physical.cover1355⟩

def price : EarlyPrice := ⟨4, 52, 10, 59454035278367/89757247864832, 14096/23103, ![1462367892525, 235041705720, 43986161550, 2537677590], 840546290641692⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuarticIntervals6
end Z6969Source1628


section Z6969Source1631
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.QuarticIntervals7
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,4,1,56⟩
  bank i := ![Physical.src1358.bank, Physical.src1359.bank, Physical.src1360.bank, Physical.src1361.bank, Physical.src1362.bank, Physical.src1363.bank, Physical.src1364.bank, Physical.src1365.bank, Physical.src1366.bank, Physical.src1367.bank, Physical.src1368.bank] i
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 16, 32, 50, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 4
  slopeFloor := 1
  physicalFloor := 514639
  seedFloor := 53

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1358
    · exact Physical.rank1359
    · exact Physical.rank1360
    · exact Physical.rank1361
    · exact Physical.rank1362
    · exact Physical.rank1363
    · exact Physical.rank1364
    · exact Physical.rank1365
    · exact Physical.rank1366
    · exact Physical.rank1367
    · exact Physical.rank1368
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1358⟩
    · exact ⟨_, Physical.cover1359⟩
    · exact ⟨_, Physical.cover1360⟩
    · exact ⟨_, Physical.cover1361⟩
    · exact ⟨_, Physical.cover1362⟩
    · exact ⟨_, Physical.cover1363⟩
    · exact ⟨_, Physical.cover1364⟩
    · exact ⟨_, Physical.cover1365⟩
    · exact ⟨_, Physical.cover1366⟩
    · exact ⟨_, Physical.cover1367⟩
    · exact ⟨_, Physical.cover1368⟩

def price : EarlyPrice := ⟨4, 56, 10, 164026061413517/263887008038912, 13796/22641, ![1244359194364, 179530514345, 32945264352, 1764934920], 706908671806125⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.QuarticIntervals7
end Z6969Source1631


section Z6969Source1636
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases10
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,5,1,15⟩
  bank i := ![Physical.src1465.bank, Physical.src1466.bank, Physical.src1467.bank, Physical.src1468.bank, Physical.src1469.bank, Physical.src1470.bank, Physical.src1473.bank, Physical.src1475.bank, Physical.src1474.bank, Physical.src1475.bank] i
  reserve i := ![0, 1, 3, 8, 25, 40, 85, 245, 190, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 5
  slopeFloor := 1
  physicalFloor := 643299
  seedFloor := 9

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1465
    · exact Physical.rank1466
    · exact Physical.rank1467
    · exact Physical.rank1468
    · exact Physical.rank1469
    · exact Physical.rank1470
    · exact Physical.rank1473
    · exact Physical.rank1475
    · exact Physical.rank1474
    · exact Physical.rank1475
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1465⟩
    · exact ⟨_, Physical.cover1466⟩
    · exact ⟨_, Physical.cover1467⟩
    · exact ⟨_, Physical.cover1468⟩
    · exact ⟨_, Physical.cover1469⟩
    · exact ⟨_, Physical.cover1470⟩
    · exact ⟨_, Physical.cover1473⟩
    · exact ⟨_, Physical.cover1475⟩
    · exact ⟨_, Physical.cover1474⟩
    · exact ⟨_, Physical.cover1475⟩

def price : EarlyPrice := ⟨5, 15, 9, 700650059677183/811836299542528, 12372526266469390956091/16799725534384008200192, ![4999321719915, 1363646925586, 17917732650, 4778080460], 2974183999602261⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.HigherHelperCases10
end Z6969Source1636


section Z6969Source1639
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases11
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,5,1,25⟩
  bank i := ![Physical.src1478.bank, Physical.src1479.bank, Physical.src1480.bank, Physical.src1481.bank, Physical.src1482.bank, Physical.src1483.bank, Physical.src1484.bank, Physical.src1485.bank, Physical.src1486.bank, Physical.src1487.bank, Physical.src1488.bank] i
  reserve i := ![0, 1, 2, 4, 8, 16, 40, 85, 145, 190, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 5
  slopeFloor := 1
  physicalFloor := 643299
  seedFloor := 16

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1478
    · exact Physical.rank1479
    · exact Physical.rank1480
    · exact Physical.rank1481
    · exact Physical.rank1482
    · exact Physical.rank1483
    · exact Physical.rank1484
    · exact Physical.rank1485
    · exact Physical.rank1486
    · exact Physical.rank1487
    · exact Physical.rank1488
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1478⟩
    · exact ⟨_, Physical.cover1479⟩
    · exact ⟨_, Physical.cover1480⟩
    · exact ⟨_, Physical.cover1481⟩
    · exact ⟨_, Physical.cover1482⟩
    · exact ⟨_, Physical.cover1483⟩
    · exact ⟨_, Physical.cover1484⟩
    · exact ⟨_, Physical.cover1485⟩
    · exact ⟨_, Physical.cover1486⟩
    · exact ⟨_, Physical.cover1487⟩
    · exact ⟨_, Physical.cover1488⟩

def price : EarlyPrice := ⟨5, 25, 10, 63257559805863/83848025079808, 3526/4905, ![6505107678212, 1091578728184, 29862878540, 4778080460], 2741924216667929⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.HigherHelperCases11
end Z6969Source1639


section Z6969Source1642
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases7
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,5,1,1⟩
  bank i := ![Physical.src1427.bank, Physical.src1428.bank, Physical.src1429.bank, Physical.src1430.bank, Physical.src1431.bank, Physical.src1432.bank, Physical.src1433.bank, Physical.src1434.bank, Physical.src1435.bank, Physical.src1438.bank] i
  reserve i := ![0, 1, 2, 4, 8, 13, 25, 32, 40, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 5
  slopeFloor := 1
  physicalFloor := 643299
  seedFloor := 1

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1427
    · exact Physical.rank1428
    · exact Physical.rank1429
    · exact Physical.rank1430
    · exact Physical.rank1431
    · exact Physical.rank1432
    · exact Physical.rank1433
    · exact Physical.rank1434
    · exact Physical.rank1435
    · exact Physical.rank1438
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1427⟩
    · exact ⟨_, Physical.cover1428⟩
    · exact ⟨_, Physical.cover1429⟩
    · exact ⟨_, Physical.cover1430⟩
    · exact ⟨_, Physical.cover1431⟩
    · exact ⟨_, Physical.cover1432⟩
    · exact ⟨_, Physical.cover1433⟩
    · exact ⟨_, Physical.cover1434⟩
    · exact ⟨_, Physical.cover1435⟩
    · exact ⟨_, Physical.cover1438⟩

def price : EarlyPrice := ⟨5, 1, 9, 431078796559469/436338409078784, 9982/12479, ![91608997680, 369956909655, 978189858, 3912734292], 1196690241378392⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.HigherHelperCases7
end Z6969Source1642


section Z6969Source1646
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases8
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,5,1,3⟩
  bank i := ![Physical.src1439.bank, Physical.src1440.bank, Physical.src1441.bank, Physical.src1442.bank, Physical.src1443.bank, Physical.src1444.bank, Physical.src1445.bank, Physical.src1446.bank, Physical.src1447.bank, Physical.src1449.bank, Physical.src1451.bank] i
  reserve i := ![0, 1, 2, 3, 4, 8, 10, 25, 40, 65, 110] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 5
  slopeFloor := 1
  physicalFloor := 643299
  seedFloor := 2

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1439
    · exact Physical.rank1440
    · exact Physical.rank1441
    · exact Physical.rank1442
    · exact Physical.rank1443
    · exact Physical.rank1444
    · exact Physical.rank1445
    · exact Physical.rank1446
    · exact Physical.rank1447
    · exact Physical.rank1449
    · exact Physical.rank1451
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1439⟩
    · exact ⟨_, Physical.cover1440⟩
    · exact ⟨_, Physical.cover1441⟩
    · exact ⟨_, Physical.cover1442⟩
    · exact ⟨_, Physical.cover1443⟩
    · exact ⟨_, Physical.cover1444⟩
    · exact ⟨_, Physical.cover1445⟩
    · exact ⟨_, Physical.cover1446⟩
    · exact ⟨_, Physical.cover1447⟩
    · exact ⟨_, Physical.cover1449⟩
    · exact ⟨_, Physical.cover1451⟩

def price : EarlyPrice := ⟨5, 3, 10, 282210927773843/292943600549888, 38336/46079, ![171032639726, 230708524405, 2052083514, 2736112524], 1058796185340470⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.HigherHelperCases8
end Z6969Source1646


section Z6969Source1649
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases9
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,5,1,8⟩
  bank i := ![Physical.src1452.bank, Physical.src1453.bank, Physical.src1454.bank, Physical.src1455.bank, Physical.src1456.bank, Physical.src1457.bank, Physical.src1458.bank, Physical.src1459.bank, Physical.src1462.bank, Physical.src1463.bank, Physical.src1464.bank] i
  reserve i := ![0, 1, 2, 3, 4, 8, 16, 32, 85, 110, 190] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 5
  slopeFloor := 1
  physicalFloor := 643789
  seedFloor := 4

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1452
    · exact Physical.rank1453
    · exact Physical.rank1454
    · exact Physical.rank1455
    · exact Physical.rank1456
    · exact Physical.rank1457
    · exact Physical.rank1458
    · exact Physical.rank1459
    · exact Physical.rank1462
    · exact Physical.rank1463
    · exact Physical.rank1464
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover1456⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩

def price : EarlyPrice := ⟨5, 8, 10, 745756168574597/848690268864512, 87553/109224, ![821873890110, 421770621310, 7931276808, 3965651144], 1461039327890192⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.HigherHelperCases9
end Z6969Source1649


section Z6969Source1652
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.RepricedHelperCases2
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,5,1,56⟩
  bank i := ![Physical.src1510.bank, Physical.src1511.bank, Physical.src1512.bank, Physical.src1513.bank, Physical.src1514.bank, Physical.src1515.bank, Physical.src1516.bank, Physical.src1519.bank, Physical.src1521.bank, Physical.src1520.bank, Physical.src1519.bank] i
  reserve i := ![0, 1, 3, 6, 10, 32, 65, 145, 237, 190, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 5
  slopeFloor := 1
  physicalFloor := 643789
  seedFloor := 41

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1510
    · exact Physical.rank1511
    · exact Physical.rank1512
    · exact Physical.rank1513
    · exact Physical.rank1514
    · exact Physical.rank1515
    · exact Physical.rank1516
    · exact Physical.rank1519
    · exact Physical.rank1521
    · exact Physical.rank1520
    · exact Physical.rank1519
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover1521⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩

def price : EarlyPrice := ⟨5, 56, 10, 44809862592617762930887/73780518486195018137600, 12189/26990, ![7281252048928, 655990938956, 38218249784, 2729887012], 1817056158430414⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.RepricedHelperCases2
end Z6969Source1652


end Research6970.Height2313
end Pack_R6970Height2313OrdinaryPlans06

section Pack_R6970Height2313OrdinaryPlans07

set_option Elab.async false

namespace Research6970.Height2313

open _root_.Lower6960 _root_.Research6969

section Z6969Source1658
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases12
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,6,1,1⟩
  bank i := ![Physical.src1557.bank, Physical.src1558.bank, Physical.src1559.bank, Physical.src1560.bank, Physical.src1561.bank, Physical.src1562.bank, Physical.src1563.bank, Physical.src1564.bank, Physical.src1565.bank, Physical.src1568.bank, Physical.src1569.bank] i
  reserve i := ![0, 1, 2, 4, 8, 13, 20, 25, 40, 145, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 6
  slopeFloor := 1
  physicalFloor := 772547
  seedFloor := 1

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1557
    · exact Physical.rank1558
    · exact Physical.rank1559
    · exact Physical.rank1560
    · exact Physical.rank1561
    · exact Physical.rank1562
    · exact Physical.rank1563
    · exact Physical.rank1564
    · exact Physical.rank1565
    · exact Physical.rank1568
    · exact Physical.rank1569
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover1558⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover1560⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover1562⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩

def price : EarlyPrice := ⟨6, 1, 10, 539176990642637/546585624707072, 56273/70344, ![72154536777, 364282466330, 991419156, 4957060108], 674951070756829⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.HigherHelperCases12
end Z6969Source1658


section Z6969Source1661
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases13
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,6,1,3⟩
  bank i := ![Physical.src1570.bank, Physical.src1571.bank, Physical.src1572.bank, Physical.src1573.bank, Physical.src1574.bank, Physical.src1575.bank, Physical.src1576.bank, Physical.src1579.bank, Physical.src1577.bank, Physical.src1581.bank, Physical.src1582.bank] i
  reserve i := ![0, 1, 3, 6, 10, 16, 25, 65, 50, 145, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 6
  slopeFloor := 1
  physicalFloor := 771959
  seedFloor := 2

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1570
    · exact Physical.rank1571
    · exact Physical.rank1572
    · exact Physical.rank1573
    · exact Physical.rank1574
    · exact Physical.rank1575
    · exact Physical.rank1576
    · exact Physical.rank1579
    · exact Physical.rank1577
    · exact Physical.rank1581
    · exact Physical.rank1582
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1570⟩
    · exact ⟨_, Physical.cover1571⟩
    · exact ⟨_, Physical.cover1572⟩
    · exact ⟨_, Physical.cover1573⟩
    · exact ⟨_, Physical.cover1574⟩
    · exact ⟨_, Physical.cover1575⟩
    · exact ⟨_, Physical.cover1576⟩
    · exact ⟨_, Physical.cover1579⟩
    · exact ⟨_, Physical.cover1577⟩
    · exact ⟨_, Physical.cover1581⟩
    · exact ⟨_, Physical.cover1582⟩

def price : EarlyPrice := ⟨6, 3, 10, 59908561830197/61959424704512, 14345/18606, ![216462126803, 371307151352, 2974237084, 4957060108], 747992901978189⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.HigherHelperCases13
end Z6969Source1661


section Z6969Source1665
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases14
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,6,1,8⟩
  bank i := ![Physical.src1583.bank, Physical.src1584.bank, Physical.src1585.bank, Physical.src1586.bank, Physical.src1587.bank, Physical.src1588.bank, Physical.src1589.bank, Physical.src1590.bank, Physical.src1593.bank, Physical.src1592.bank, Physical.src1595.bank] i
  reserve i := ![0, 1, 2, 4, 6, 10, 16, 40, 85, 65, 145] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 6
  slopeFloor := 1
  physicalFloor := 771959
  seedFloor := 4

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1583
    · exact Physical.rank1584
    · exact Physical.rank1585
    · exact Physical.rank1586
    · exact Physical.rank1587
    · exact Physical.rank1588
    · exact Physical.rank1589
    · exact Physical.rank1590
    · exact Physical.rank1593
    · exact Physical.rank1592
    · exact Physical.rank1595
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1583⟩
    · exact ⟨_, Physical.cover1584⟩
    · exact ⟨_, Physical.cover1585⟩
    · exact ⟨_, Physical.cover1586⟩
    · exact ⟨_, Physical.cover1587⟩
    · exact ⟨_, Physical.cover1588⟩
    · exact ⟨_, Physical.cover1589⟩
    · exact ⟨_, Physical.cover1590⟩
    · exact ⟨_, Physical.cover1593⟩
    · exact ⟨_, Physical.cover1592⟩
    · exact ⟨_, Physical.cover1595⟩

def price : EarlyPrice := ⟨6, 8, 10, 26756061942193/29720943001600, 15581/18700, ![663176760792, 419404626172, 5447305500, 3404574250], 922803735530644⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.HigherHelperCases14
end Z6969Source1665


section Z6969Source1669
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases15
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,6,1,15⟩
  bank i := ![Physical.src1596.bank, Physical.src1597.bank, Physical.src1598.bank, Physical.src1599.bank, Physical.src1600.bank, Physical.src1601.bank, Physical.src1602.bank, Physical.src1603.bank, Physical.src1605.bank, Physical.src1607.bank, Physical.src1608.bank] i
  reserve i := ![0, 1, 3, 6, 10, 20, 40, 50, 85, 145, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 6
  slopeFloor := 1
  physicalFloor := 771959
  seedFloor := 9

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1596
    · exact Physical.rank1597
    · exact Physical.rank1598
    · exact Physical.rank1599
    · exact Physical.rank1600
    · exact Physical.rank1601
    · exact Physical.rank1602
    · exact Physical.rank1603
    · exact Physical.rank1605
    · exact Physical.rank1607
    · exact Physical.rank1608
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1596⟩
    · exact ⟨_, Physical.cover1597⟩
    · exact ⟨_, Physical.cover1598⟩
    · exact ⟨_, Physical.cover1599⟩
    · exact ⟨_, Physical.cover1600⟩
    · exact ⟨_, Physical.cover1601⟩
    · exact ⟨_, Physical.cover1602⟩
    · exact ⟨_, Physical.cover1603⟩
    · exact ⟨_, Physical.cover1605⟩
    · exact ⟨_, Physical.cover1607⟩
    · exact ⟨_, Physical.cover1608⟩

def price : EarlyPrice := ⟨6, 15, 10, 492252986270093/582460551200768, 45160/58303, ![4901690504355, 1664309491829, 10482165420, 3494065916], 2282994108276612⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.HigherHelperCases15
end Z6969Source1669


section Z6969Source1672
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases16
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,6,1,25⟩
  bank i := ![Physical.src1611.bank, Physical.src1612.bank, Physical.src1613.bank, Physical.src1614.bank, Physical.src1615.bank, Physical.src1616.bank, Physical.src1618.bank, Physical.src1617.bank, Physical.src1621.bank, Physical.src1619.bank, Physical.src1620.bank] i
  reserve i := ![0, 2, 4, 8, 20, 40, 85, 65, 245, 245, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 6
  slopeFloor := 1
  physicalFloor := 771959
  seedFloor := 16

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1611
    · exact Physical.rank1612
    · exact Physical.rank1613
    · exact Physical.rank1614
    · exact Physical.rank1615
    · exact Physical.rank1616
    · exact Physical.rank1618
    · exact Physical.rank1617
    · exact Physical.rank1621
    · exact Physical.rank1619
    · exact Physical.rank1620
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1611⟩
    · exact ⟨_, Physical.cover1612⟩
    · exact ⟨_, Physical.cover1613⟩
    · exact ⟨_, Physical.cover1614⟩
    · exact ⟨_, Physical.cover1615⟩
    · exact ⟨_, Physical.cover1616⟩
    · exact ⟨_, Physical.cover1618⟩
    · exact ⟨_, Physical.cover1617⟩
    · exact ⟨_, Physical.cover1621⟩
    · exact ⟨_, Physical.cover1619⟩
    · exact ⟨_, Physical.cover1620⟩

def price : EarlyPrice := ⟨6, 25, 10, 50403705873899/69197348470784, 5653/7916, ![7535124077470, 1557738457671, 25436947030, 5087406665], 2469108784260077⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.HigherHelperCases16
end Z6969Source1672


section Z6969Source1676
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.MarkedExitCandidates0
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,6,1,40⟩
  bank i := ![Physical.src1628.bank, Physical.src1629.bank, Physical.src1630.bank, Physical.src1631.bank, Physical.src1632.bank, Physical.src1633.bank, Physical.src1634.bank, Physical.src1635.bank, Physical.src1636.bank, Physical.src1638.bank, Physical.src1637.bank] i
  reserve i := ![0, 1, 4, 8, 16, 32, 50, 65, 85, 245, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 6
  slopeFloor := 1
  physicalFloor := 771959
  seedFloor := 26

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1628
    · exact Physical.rank1629
    · exact Physical.rank1630
    · exact Physical.rank1631
    · exact Physical.rank1632
    · exact Physical.rank1633
    · exact Physical.rank1634
    · exact Physical.rank1635
    · exact Physical.rank1636
    · exact Physical.rank1638
    · exact Physical.rank1637
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1628⟩
    · exact ⟨_, Physical.cover1629⟩
    · exact ⟨_, Physical.cover1630⟩
    · exact ⟨_, Physical.cover1631⟩
    · exact ⟨_, Physical.cover1632⟩
    · exact ⟨_, Physical.cover1633⟩
    · exact ⟨_, Physical.cover1634⟩
    · exact ⟨_, Physical.cover1635⟩
    · exact ⟨_, Physical.cover1636⟩
    · exact ⟨_, Physical.cover1638⟩
    · exact ⟨_, Physical.cover1637⟩

def price : EarlyPrice := ⟨6, 40, 10, 200600843561437/284516839063552, 34381590828488638379633/53648125586449421565952, ![8220099002496, 1108353992546, 32963942016, 4120507578], 2223097539616331⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.MarkedExitCandidates0
end Z6969Source1676


section Z6969Source1679
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.MarkedExitCandidates1
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,6,1,56⟩
  bank i := ![Physical.src1643.bank, Physical.src1644.bank, Physical.src1645.bank, Physical.src1646.bank, Physical.src1647.bank, Physical.src1648.bank, Physical.src1649.bank, Physical.src1650.bank, Physical.src1651.bank, Physical.src1654.bank, Physical.src1655.bank] i
  reserve i := ![0, 1, 2, 3, 6, 13, 40, 65, 65, 190, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 6
  slopeFloor := 1
  physicalFloor := 772547
  seedFloor := 41

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1643
    · exact Physical.rank1644
    · exact Physical.rank1645
    · exact Physical.rank1646
    · exact Physical.rank1647
    · exact Physical.rank1648
    · exact Physical.rank1649
    · exact Physical.rank1650
    · exact Physical.rank1651
    · exact Physical.rank1654
    · exact Physical.rank1655
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨_, Physical.cover1644⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩
    · exact ⟨[2308,2309,2310,2311,2312,2313], ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), ⟨by decide, by decide, _root_.Research6969.PhysicalWindow.triangular_of_fast _ _ _ (by decide +kernel), rfl⟩⟩⟩⟩⟩⟩⟩

def price : EarlyPrice := ⟨6, 56, 10, 182977965457373/280880394272768, 11125/16066, ![5040865127012, 563600590597, 32945264352, 2941552152], 1473346405253630⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.MarkedExitCandidates1
end Z6969Source1679


section Z6969Source1684
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases17
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,7,1,1⟩
  bank i := ![Physical.src1685.bank, Physical.src1686.bank, Physical.src1687.bank, Physical.src1688.bank, Physical.src1689.bank, Physical.src1690.bank, Physical.src1691.bank, Physical.src1692.bank, Physical.src1693.bank, Physical.src1694.bank, Physical.src1695.bank] i
  reserve i := ![0, 1, 2, 4, 8, 13, 20, 32, 50, 110, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 7
  slopeFloor := 1
  physicalFloor := 900619
  seedFloor := 1

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1685
    · exact Physical.rank1686
    · exact Physical.rank1687
    · exact Physical.rank1688
    · exact Physical.rank1689
    · exact Physical.rank1690
    · exact Physical.rank1691
    · exact Physical.rank1692
    · exact Physical.rank1693
    · exact Physical.rank1694
    · exact Physical.rank1695
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1685⟩
    · exact ⟨_, Physical.cover1686⟩
    · exact ⟨_, Physical.cover1687⟩
    · exact ⟨_, Physical.cover1688⟩
    · exact ⟨_, Physical.cover1689⟩
    · exact ⟨_, Physical.cover1690⟩
    · exact ⟨_, Physical.cover1691⟩
    · exact ⟨_, Physical.cover1692⟩
    · exact ⟨_, Physical.cover1693⟩
    · exact ⟨_, Physical.cover1694⟩
    · exact ⟨_, Physical.cover1695⟩

def price : EarlyPrice := ⟨7, 1, 10, 98597191615/100526718976, 7949/9936, ![50675215086, 307528899562, 1017488655, 6104882245], 430219887017309⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.HigherHelperCases17
end Z6969Source1684


section Z6969Source1689
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases18
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,7,1,3⟩
  bank i := ![Physical.src1696.bank, Physical.src1697.bank, Physical.src1698.bank, Physical.src1699.bank, Physical.src1700.bank, Physical.src1701.bank, Physical.src1702.bank, Physical.src1703.bank, Physical.src1704.bank, Physical.src1705.bank] i
  reserve i := ![0, 1, 3, 8, 13, 20, 50, 85, 145, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 7
  slopeFloor := 1
  physicalFloor := 900619
  seedFloor := 2

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1696
    · exact Physical.rank1697
    · exact Physical.rank1698
    · exact Physical.rank1699
    · exact Physical.rank1700
    · exact Physical.rank1701
    · exact Physical.rank1702
    · exact Physical.rank1703
    · exact Physical.rank1704
    · exact Physical.rank1705
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1696⟩
    · exact ⟨_, Physical.cover1697⟩
    · exact ⟨_, Physical.cover1698⟩
    · exact ⟨_, Physical.cover1699⟩
    · exact ⟨_, Physical.cover1700⟩
    · exact ⟨_, Physical.cover1701⟩
    · exact ⟨_, Physical.cover1702⟩
    · exact ⟨_, Physical.cover1703⟩
    · exact ⟨_, Physical.cover1704⟩
    · exact ⟨_, Physical.cover1705⟩

def price : EarlyPrice := ⟨7, 3, 9, 37819369768819/40000892698624, 41273/51480, ![152029272486, 312750910747, 2537673242, 5075339962], 483380265004276⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.HigherHelperCases18
end Z6969Source1689


section Z6969Source1692
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases19
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,7,1,8⟩
  bank i := ![Physical.src1706.bank, Physical.src1707.bank, Physical.src1708.bank, Physical.src1709.bank, Physical.src1710.bank, Physical.src1711.bank, Physical.src1712.bank, Physical.src1713.bank, Physical.src1715.bank, Physical.src1714.bank, Physical.src1716.bank] i
  reserve i := ![0, 1, 2, 4, 8, 20, 32, 40, 145, 145, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 7
  slopeFloor := 1
  physicalFloor := 900619
  seedFloor := 4

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1706
    · exact Physical.rank1707
    · exact Physical.rank1708
    · exact Physical.rank1709
    · exact Physical.rank1710
    · exact Physical.rank1711
    · exact Physical.rank1712
    · exact Physical.rank1713
    · exact Physical.rank1715
    · exact Physical.rank1714
    · exact Physical.rank1716
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1706⟩
    · exact ⟨_, Physical.cover1707⟩
    · exact ⟨_, Physical.cover1708⟩
    · exact ⟨_, Physical.cover1709⟩
    · exact ⟨_, Physical.cover1710⟩
    · exact ⟨_, Physical.cover1711⟩
    · exact ⟨_, Physical.cover1712⟩
    · exact ⟨_, Physical.cover1713⟩
    · exact ⟨_, Physical.cover1715⟩
    · exact ⟨_, Physical.cover1714⟩
    · exact ⟨_, Physical.cover1716⟩

def price : EarlyPrice := ⟨7, 8, 10, 7217424508937498372725315/8171912338142894644789248, 98470/122997, ![832914800172, 633468093132, 6592796028, 4944604434], 826197504156308⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.HigherHelperCases19
end Z6969Source1692


section Z6969Source1696
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases20
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 10
  positive := by decide
  primeShape := ⟨0,7,1,15⟩
  bank i := ![Physical.src1717.bank, Physical.src1718.bank, Physical.src1719.bank, Physical.src1720.bank, Physical.src1721.bank, Physical.src1723.bank, Physical.src1722.bank, Physical.src1725.bank, Physical.src1724.bank, Physical.src1726.bank] i
  reserve i := ![0, 1, 3, 8, 20, 65, 50, 190, 190, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 7
  slopeFloor := 1
  physicalFloor := 900619
  seedFloor := 9

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1717
    · exact Physical.rank1718
    · exact Physical.rank1719
    · exact Physical.rank1720
    · exact Physical.rank1721
    · exact Physical.rank1723
    · exact Physical.rank1722
    · exact Physical.rank1725
    · exact Physical.rank1724
    · exact Physical.rank1726
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1717⟩
    · exact ⟨_, Physical.cover1718⟩
    · exact ⟨_, Physical.cover1719⟩
    · exact ⟨_, Physical.cover1720⟩
    · exact ⟨_, Physical.cover1721⟩
    · exact ⟨_, Physical.cover1723⟩
    · exact ⟨_, Physical.cover1722⟩
    · exact ⟨_, Physical.cover1725⟩
    · exact ⟨_, Physical.cover1724⟩
    · exact ⟨_, Physical.cover1726⟩

def price : EarlyPrice := ⟨7, 15, 9, 5058437678093/6136500584448, 16945/25272, ![12317308936245, 4951983933993, 10213691250, 4085485250], 4215154100686744⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.HigherHelperCases20
end Z6969Source1696


section Z6969Source1700
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.HigherHelperCases21
open _root_.Research6969.PhysicalCatalogue _root_.Research6969.TransitionBanks
open Research6969.TransitionBanks
open Research6970.Height2313.Lower6960.Prefix6969Rescue
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,7,1,25⟩
  bank i := ![Physical.src1727.bank, Physical.src1728.bank, Physical.src1729.bank, Physical.src1730.bank, Physical.src1731.bank, Physical.src1732.bank, Physical.src1733.bank, Physical.src1734.bank, Physical.src1735.bank, Physical.src1736.bank, Physical.src1737.bank] i
  reserve i := ![0, 1, 2, 4, 8, 16, 40, 85, 145, 190, 245] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 7
  slopeFloor := 1
  physicalFloor := 900619
  seedFloor := 16

theorem sources : plan.Sources 2308 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact Physical.rank1727
    · exact Physical.rank1728
    · exact Physical.rank1729
    · exact Physical.rank1730
    · exact Physical.rank1731
    · exact Physical.rank1732
    · exact Physical.rank1733
    · exact Physical.rank1734
    · exact Physical.rank1735
    · exact Physical.rank1736
    · exact Physical.rank1737
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, Physical.cover1727⟩
    · exact ⟨_, Physical.cover1728⟩
    · exact ⟨_, Physical.cover1729⟩
    · exact ⟨_, Physical.cover1730⟩
    · exact ⟨_, Physical.cover1731⟩
    · exact ⟨_, Physical.cover1732⟩
    · exact ⟨_, Physical.cover1733⟩
    · exact ⟨_, Physical.cover1734⟩
    · exact ⟨_, Physical.cover1735⟩
    · exact ⟨_, Physical.cover1736⟩
    · exact ⟨_, Physical.cover1737⟩

def price : EarlyPrice := ⟨7, 25, 10, 6052217274973/8321864040448, 8248/11305, ![4645759259878, 1148709579611, 21147198028, 5075339962], 1626566585763846⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel


end Lower6960.Prefix6969RescueData.HigherHelperCases21
end Z6969Source1700


end Research6970.Height2313
end Pack_R6970Height2313OrdinaryPlans07
