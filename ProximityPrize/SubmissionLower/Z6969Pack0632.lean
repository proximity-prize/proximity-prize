import ProximityPrize.SubmissionLower.R6970PhysicalCoverCompact
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969Pack0612
import ProximityPrize.SubmissionLower.Z6969Pack0613
import ProximityPrize.SubmissionLower.Z6969Pack0614
import ProximityPrize.SubmissionLower.Z6969Pack0615
import ProximityPrize.SubmissionLower.Z6969Pack0616
import ProximityPrize.SubmissionLower.Z6969Pack0560
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.Z6969Pack0590
import ProximityPrize.SubmissionLower.Z6969Pack0575
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0599
import ProximityPrize.SubmissionLower.Z6969Pack0605
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.R6966ProofNearTerminalFacts
import ProximityPrize.SubmissionLower.Z6969Pack0556
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0596
import ProximityPrize.SubmissionLower.Z6969Pack0534
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969FastHist
import ProximityPrize.SubmissionLower.Z6969FastPrice
import ProximityPrize.SubmissionLower.Z6969FastCeil
import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound

set_option Elab.async false

-- merged module Z6969Pack0617
section Merged_Z6969Pack0617

-- Source: Research6969.PackedRanks357To359
section Z6969Source0737
set_option autoImplicit true
namespace Research6969.PackedRanks.PackedRanks357To359
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment9627_2118 : P1_7_1.groupedPoleMoment 9627 2118 ≤ 238495318333820 :=
  _root_.PoleAffine6970.certified 9627 2118 238495318333820 (by decide) (by decide +kernel)

theorem moment9628_2042 : P1_7_1.groupedPoleMoment 9628 2042 ≤ 231866079487253 :=
  _root_.PoleAffine6970.certified 9628 2042 231866079487253 (by decide) (by decide +kernel)

theorem moment9628_2077 : P1_7_1.groupedPoleMoment 9628 2077 ≤ 234966243278304 :=
  _root_.PoleAffine6970.certified 9628 2077 234966243278304 (by decide) (by decide +kernel)

end Research6969.PackedRanks.PackedRanks357To359

namespace Research6969.PackedRanks.PackedRanks357To359
open Research6969.TransitionBanks
theorem rank357 (u:ℕ) : P3_7_1.BankOK (bank357 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank357 u).shape (by change 2*2118≤6900;decide) (by change 6900+2118≤9627+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (6900-2*2118) 2118=6*9997036108906496:=by decide
  change 6*P1_7_1.nodeRows (bank357 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank357 u).shape=262144*P1_7_1_2.sixPerNode (6900-2*2118) 2118 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank357 u).shape=9997036108906496; omega, moment9627_2118,by change 9627<K1.p;decide⟩
theorem rank358 (u:ℕ) : P3_7_1.BankOK (bank358 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank358 u).shape (by change 2*2042≤6900;decide) (by change 6900+2042≤9628+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (6900-2*2042) 2042=6*9722458861731840:=by decide
  change 6*P1_7_1.nodeRows (bank358 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank358 u).shape=262144*P1_7_1_2.sixPerNode (6900-2*2042) 2042 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank358 u).shape=9722458861731840; omega, moment9628_2042,by change 9628<K1.p;decide⟩
theorem rank359 (u:ℕ) : P3_7_1.BankOK (bank359 u) := by
  have hn:=P1_7_1_2.six_nodeRows (bank359 u).shape (by change 2*2077≤6900;decide) (by change 6900+2077≤9628+1;decide)
  have plain:262144*P1_7_1_2.sixPerNode (6900-2*2077) 2077=6*9849424459857920:=by decide
  change 6*P1_7_1.nodeRows (bank359 u).shape=_ at hn
  change 6*P1_7_1.nodeRows (bank359 u).shape=262144*P1_7_1_2.sixPerNode (6900-2*2077) 2077 at hn
  rw [plain] at hn
  exact ⟨by change P1_7_1.nodeRows (bank359 u).shape=9849424459857920; omega, moment9628_2077,by change 9628<K1.p;decide⟩
end Research6969.PackedRanks.PackedRanks357To359
end Z6969Source0737

-- Source: Research6969.TransitionBankChecks19
section Z6969Source0738
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 0
namespace Research6969.TransitionBanks
open P1_7_1_3 (momentEstimate)
open P1_7_1_3_2 (moment_from_blocks)

theorem rank342 (u : ℕ) : P3_7_1.BankOK (bank342 u) :=
  PackedRanks.PackedRanks342To344.rank342 u
theorem rank343 (u : ℕ) : P3_7_1.BankOK (bank343 u) :=
  PackedRanks.PackedRanks342To344.rank343 u
theorem rank344 (u : ℕ) : P3_7_1.BankOK (bank344 u) :=
  PackedRanks.PackedRanks342To344.rank344 u
theorem rank345 (u : ℕ) : P3_7_1.BankOK (bank345 u) :=
  PackedRanks.PackedRanks345To347.rank345 u
theorem rank346 (u : ℕ) : P3_7_1.BankOK (bank346 u) :=
  PackedRanks.PackedRanks345To347.rank346 u
theorem rank347 (u : ℕ) : P3_7_1.BankOK (bank347 u) :=
  PackedRanks.PackedRanks345To347.rank347 u
theorem rank348 (u : ℕ) : P3_7_1.BankOK (bank348 u) :=
  PackedRanks.PackedRanks348To350.rank348 u
theorem rank349 (u : ℕ) : P3_7_1.BankOK (bank349 u) :=
  PackedRanks.PackedRanks348To350.rank349 u
theorem rank350 (u : ℕ) : P3_7_1.BankOK (bank350 u) :=
  PackedRanks.PackedRanks348To350.rank350 u
theorem rank351 (u : ℕ) : P3_7_1.BankOK (bank351 u) :=
  PackedRanks.PackedRanks351To353.rank351 u
theorem rank352 (u : ℕ) : P3_7_1.BankOK (bank352 u) :=
  PackedRanks.PackedRanks351To353.rank352 u
theorem rank353 (u : ℕ) : P3_7_1.BankOK (bank353 u) :=
  PackedRanks.PackedRanks351To353.rank353 u
theorem rank354 (u : ℕ) : P3_7_1.BankOK (bank354 u) :=
  PackedRanks.PackedRanks354To356.rank354 u
theorem rank355 (u : ℕ) : P3_7_1.BankOK (bank355 u) :=
  PackedRanks.PackedRanks354To356.rank355 u
theorem rank356 (u : ℕ) : P3_7_1.BankOK (bank356 u) :=
  PackedRanks.PackedRanks354To356.rank356 u
theorem rank357 (u : ℕ) : P3_7_1.BankOK (bank357 u) :=
  PackedRanks.PackedRanks357To359.rank357 u
theorem rank358 (u : ℕ) : P3_7_1.BankOK (bank358 u) :=
  PackedRanks.PackedRanks357To359.rank358 u
theorem rank359 (u : ℕ) : P3_7_1.BankOK (bank359 u) :=
  PackedRanks.PackedRanks357To359.rank359 u
end Research6969.TransitionBanks
end Z6969Source0738

end Merged_Z6969Pack0617

-- merged module Z6969Pack0629
section Merged_Z6969Pack0629

-- Source: Research6969.PhysicalChecks110
section Z6969Source0761
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1648 : Request := ⟨⟨⟨560,781,172,7715⟩,5388141854720,10440670587⟩,13,6,1,771959,41⟩
theorem cover1648 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1648) 2411 2314 [2331, 2388, 2411] := triangleCover (by decide +kernel)
def src1649 : Request := ⟨⟨⟨1200,1673,378,15636⟩,53798525730816,222977190790⟩,40,6,1,771959,41⟩
theorem cover1649 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1649) 2411 2314 [2316, 2325, 2351, 2411] := triangleCover (by decide +kernel)
def src1650 : Request := ⟨⟨⟨1450,2021,445,57109⟩,92998964346880,465028319332⟩,65,6,1,771959,41⟩
theorem cover1650 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1650) 2411 2314 [2317, 2329, 2363, 2411] := triangleCover (by decide +kernel)
def src1651 : Request := ⟨⟨⟨1750,2440,537,25043⟩,163381988556800,986966790957⟩,65,6,1,771959,41⟩
theorem cover1651 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1651) 2411 2314 [2317, 2329, 2363, 2411] := triangleCover (by decide +kernel)
def src1654 : Request := ⟨⟨⟨4800,6692,1474,64247⟩,3367547627110400,55757027345056⟩,190,6,1,771959,41⟩
theorem cover1654 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1654) 2411 2314 [2320, 2340, 2395, 2411] := triangleCover (by decide +kernel)
def src1655 : Request := ⟨⟨⟨4800,6690,1512,234698⟩,3433136573644800,56816483122989⟩,245,6,1,771959,41⟩
theorem cover1655 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1655) 2411 2314 [2315, 2321, 2337, 2381, 2411] := triangleCover (by decide +kernel)
def src1678 : Request := ⟨⟨⟨556,772,170,6982⟩,5255817068544,9968090926⟩,10,6,2,771958,2⟩
theorem cover1678 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1678) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1679 : Request := ⟨⟨⟨556,772,170,6912⟩,5255817068544,9968090926⟩,10,6,2,771958,3⟩
theorem cover1679 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1679) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1680 : Request := ⟨⟨⟨556,772,170,6775⟩,5255817068544,9968090926⟩,10,6,2,771958,5⟩
theorem cover1680 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1680) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1681 : Request := ⟨⟨⟨556,772,170,6438⟩,5255817068544,9968090926⟩,10,6,2,771958,10⟩
theorem cover1681 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1681) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1682 : Request := ⟨⟨⟨556,772,170,5988⟩,5255817068544,9968090926⟩,10,6,2,771958,17⟩
theorem cover1682 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1682) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1683 : Request := ⟨⟨⟨556,772,170,5401⟩,5255817068544,9968090926⟩,10,6,2,771958,27⟩
theorem cover1683 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1683) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1684 : Request := ⟨⟨⟨556,772,170,4675⟩,5255817068544,9968090926⟩,10,6,2,771958,42⟩
theorem cover1684 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1684) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1685 : Request := ⟨⟨⟨325,453,100,5419⟩,1061047500800,1193036697⟩,0,7,1,900619,1⟩
theorem cover1685 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1685) 2411 2314 [2327, 2377, 2411] := triangleCover (by decide +kernel)
def src1686 : Request := ⟨⟨⟨325,453,100,6096⟩,1061047500800,1193036697⟩,1,7,1,900619,1⟩
theorem cover1686 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1686) 2411 2314 [2339, 2411] := triangleCover (by decide +kernel)
def src1687 : Request := ⟨⟨⟨325,453,98,6858⟩,1045036793856,1174588250⟩,2,7,1,900619,1⟩
theorem cover1687 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1687) 2411 2314 [2322, 2354, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source0761

-- Source: Research6969.PrefixMainDataRepricedHelperCases1
section Z6969Source0762
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.RepricedHelperCases1
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 16, 20, 23, 30, 41, 41, 65, 76, 76, 76] i
  bank i := ![bank6 1414, bank13 1553, bank18 1703, bank24 1838, bank31 1925, bank37 2039, bank44 2409, bank54 2755, bank74 3583, bank112 3547, bank92 5432, bank168 4492, bank129 24535, bank161 6246, bank199 9241, bank181 61748, bank212 10770, bank170 227095] i
  head := src1683
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  historyValues := [![15718, 160398, 741099, 3248142],
    ![25417/2, 463847/4, 526571, 2411809],
    ![54680/9, 505550/9, 526571, 9197903/4],
    ![29433/8, 544703/16, 2466730/9, 9927038/9],
    ![64334/25, 581097/25, 204050, 3705625/4],
    ![17323/9, 622081/36, 2800135/16, 11012639/16],
    ![18775/16, 706585/64, 638759/5, 13011009/25],
    ![89110/121, 819415/121, 3714754/49, 14879755/49],
    ![89110/121, 819415/121, 1336459/18, 14879755/49],
    ![308092/441, 346658/63, 897391/16, 12581209/64],
    ![21715/32, 346658/63, 897391/16, 12581209/64],
    ![21715/32, 346658/63, 897391/16, 20178064/121],
    ![33263/82, 346658/63, 897391/16, 20178064/121],
    ![33263/82, 8071188/1681, 9072499/196, 20178064/121],
    ![33263/82, 842350/189, 39857373/968, 85396081/529],
    ![474397/1369, 842350/189, 39857373/968, 85396081/529],
    ![474397/1369, 23666909/5476, 6865875/169, 12888100/81],
    ![920087/2738, 23666909/5476, 6865875/169, 12888100/81]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 5 26 643299 := by
  refine ⟨?_, rank154 5401, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1683⟩⟩
  · intro i; fin_cases i
    · exact free6_0
    · exact free13_0
    · exact free18_0
    · exact free24_0
    · exact free31_0
    · exact free37_0
    · exact free44_0
    · exact free54_0
    · exact free74_1
    · exact free112_0
    · exact free92_0
    · exact free168_0
    · exact free129_0
    · exact free161_0
    · exact free199_0
    · exact free181_0
    · exact free212_0
    · exact free170_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 100/100, [307439344, 307367631, 307104066, 306257631, 306421857, 307258212, 307333763, 154634755, 154674012, 102741354, 102690242, 68038455, 60152741, 79698389, 92827353, 93049500, 145252944, 229135653], [1152520, 1152887, 1154236, 1158567, 1157726, 1153447, 1153060, 2490368, 2489715, 3839799, 3841957, 5903602, 6702876, 5007825, 4273698, 4262493, 2655356, 1620098],
  ![121629787325460, 1612271871252, 206222087700, 5106855420], 165375349914307733⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [4,4,4,4,4,4,4,7,7,11,11,16,18,14,12,12,8,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![920087/2738, 23666909/5476, 6865875/169, 12888100/81] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.RepricedHelperCases1
end Z6969Source0762

-- Source: Research6969.PhysicalChecks103
section Z6969Source0763
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1482 : Request := ⟨⟨⟨690,962,212,13899⟩,10065769922560,23997864317⟩,8,5,1,643299,16⟩
theorem cover1482 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1482) 2411 2314 [2326, 2366, 2411] := triangleCover (by decide +kernel)
def src1483 : Request := ⟨⟨⟨1000,1395,307,19788⟩,30557599170560,105715278267⟩,16,5,1,643299,16⟩
theorem cover1483 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1483) 2411 2314 [2324, 2356, 2411] := triangleCover (by decide +kernel)
def src1484 : Request := ⟨⟨⟨1750,2441,537,40111⟩,163381988556800,988269431527⟩,40,5,1,643299,16⟩
theorem cover1484 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1484) 2411 2314 [2324, 2355, 2411] := triangleCover (by decide +kernel)
def src1485 : Request := ⟨⟨⟨2600,3625,798,130242⟩,535425056505856,4803689494279⟩,85,5,1,643299,16⟩
theorem cover1485 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1485) 2411 2314 [2329, 2374, 2411] := triangleCover (by decide +kernel)
def src1486 : Request := ⟨⟨⟨5700,7950,1750,115771⟩,5637370734182400,110980791054694⟩,145,5,1,643299,16⟩
theorem cover1486 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1486) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src1487 : Request := ⟨⟨⟨4800,6692,1474,677451⟩,3367547627110400,55757027345056⟩,190,5,1,643299,16⟩
theorem cover1487 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1487) 2411 2314 [2317, 2328, 2358, 2411] := triangleCover (by decide +kernel)
def src1488 : Request := ⟨⟨⟨10000,13948,3070,185441⟩,30428373265940480,1050983571587703⟩,245,5,1,643299,16⟩
theorem cover1488 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1488) 2411 2314 [2318, 2332, 2371, 2411] := triangleCover (by decide +kernel)
def src1495 : Request := ⟨⟨⟨325,453,100,6096⟩,1061047500800,1193036697⟩,0,5,1,643299,26⟩
theorem cover1495 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1495) 2411 2314 [2327, 2377, 2411] := triangleCover (by decide +kernel)
def src1496 : Request := ⟨⟨⟨400,558,123,6096⟩,1971918995456,2734096379⟩,1,5,1,643299,26⟩
theorem cover1496 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1496) 2411 2314 [2331, 2392, 2411] := triangleCover (by decide +kernel)
def src1497 : Request := ⟨⟨⟨470,655,141,7715⟩,3134317133824,5085275599⟩,3,5,1,643299,26⟩
theorem cover1497 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1497) 2411 2314 [2333, 2399, 2411] := triangleCover (by decide +kernel)
def src1498 : Request := ⟨⟨⟨560,781,172,8679⟩,5388141854720,10440670587⟩,6,5,1,643299,26⟩
theorem cover1498 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1498) 2411 2314 [2321, 2346, 2411] := triangleCover (by decide +kernel)
def src1499 : Request := ⟨⟨⟨825,1151,253,12355⟩,17161575202816,49010625289⟩,13,5,1,643299,26⟩
theorem cover1499 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1499) 2411 2314 [2325, 2361, 2411] := triangleCover (by decide +kernel)
def src1500 : Request := ⟨⟨⟨1450,2022,445,22261⟩,92998964346880,465769321795⟩,32,5,1,643299,26⟩
theorem cover1500 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1500) 2411 2314 [2318, 2332, 2373, 2411] := triangleCover (by decide +kernel)
def src1501 : Request := ⟨⟨⟨3200,4463,982,50764⟩,997767489781760,11028049925768⟩,85,5,1,643299,26⟩
theorem cover1501 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1501) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src1502 : Request := ⟨⟨⟨3200,4462,982,102908⟩,997767489781760,11020095796464⟩,110,5,1,643299,26⟩
theorem cover1502 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1502) 2411 2314 [2316, 2325, 2350, 2411] := triangleCover (by decide +kernel)
def src1503 : Request := ⟨⟨⟨3950,5507,1244,164837⟩,1913299978158080,26084011577468⟩,145,5,1,643299,26⟩
theorem cover1503 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1503) 2411 2314 [2315, 2320, 2334, 2373, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source0763

-- Source: Research6969.PhysicalChecks104
section Z6969Source0764
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1504 : Request := ⟨⟨⟨4800,6692,1474,422931⟩,3367547627110400,55757027345056⟩,190,5,1,643299,26⟩
theorem cover1504 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1504) 2411 2314 [2318, 2332, 2371, 2411] := triangleCover (by decide +kernel)
def src1505 : Request := ⟨⟨⟨6900,9623,2174,102908⟩,10196763128627200,243058712908678⟩,190,5,1,643299,26⟩
theorem cover1505 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1505) 2411 2314 [2318, 2331, 2367, 2411] := triangleCover (by decide +kernel)
def src1510 : Request := ⟨⟨⟨275,383,84,3807⟩,640970915840,608607683⟩,0,5,1,643299,41⟩
theorem cover1510 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1510) 2411 2314 [2332, 2404, 2411] := triangleCover (by decide +kernel)
def src1511 : Request := ⟨⟨⟨325,453,100,3807⟩,1061047500800,1193036697⟩,1,5,1,643299,41⟩
theorem cover1511 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1511) 2411 2314 [2337, 2411] := triangleCover (by decide +kernel)
def src1512 : Request := ⟨⟨⟨400,558,123,4282⟩,1971918995456,2734096379⟩,3,5,1,643299,41⟩
theorem cover1512 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1512) 2411 2314 [2328, 2379, 2411] := triangleCover (by decide +kernel)
def src1513 : Request := ⟨⟨⟨470,655,144,5419⟩,3184589537280,5168862572⟩,6,5,1,643299,41⟩
theorem cover1513 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1513) 2411 2314 [2330, 2386, 2411] := triangleCover (by decide +kernel)
def src1514 : Request := ⟨⟨⟨560,781,172,6858⟩,5388141854720,10440670587⟩,10,5,1,643299,41⟩
theorem cover1514 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1514) 2411 2314 [2320, 2342, 2411] := triangleCover (by decide +kernel)
def src1515 : Request := ⟨⟨⟨1200,1673,368,13899⟩,52718727069696,218387554859⟩,32,5,1,643299,41⟩
theorem cover1515 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1515) 2411 2314 [2321, 2344, 2411] := triangleCover (by decide +kernel)
def src1516 : Request := ⟨⟨⟨2100,2928,645,25043⟩,282396798484480,2046887686018⟩,65,5,1,643299,41⟩
theorem cover1516 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1516) 2411 2314 [2320, 2340, 2397, 2411] := triangleCover (by decide +kernel)
def src1519 : Request := ⟨⟨⟨3950,5507,1244,57109⟩,1913299978158080,26084011577468⟩,145,5,1,643299,41⟩
theorem cover1519 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1519) 2411 2314 [2316, 2325, 2350, 2411] := triangleCover (by decide +kernel)
def src1520 : Request := ⟨⟨⟨5700,7948,1750,64247⟩,5637370734182400,110890906752819⟩,190,5,1,643299,41⟩
theorem cover1520 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1520) 2411 2314 [2315, 2320, 2334, 2373, 2411] := triangleCover (by decide +kernel)
def src1521 : Request := ⟨⟨⟨5620,7835,1720,334168⟩,5390441861611520,104477286568219⟩,237,5,1,643299,41⟩
theorem cover1521 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1521) 2411 2314 [2315, 2320, 2334, 2373, 2411] := triangleCover (by decide +kernel)
def src1544 : Request := ⟨⟨⟨556,772,170,7530⟩,5255817068544,9968090926⟩,10,5,2,643298,2⟩
theorem cover1544 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1544) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1545 : Request := ⟨⟨⟨556,772,170,7448⟩,5255817068544,9968090926⟩,10,5,2,643298,3⟩
theorem cover1545 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1545) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1546 : Request := ⟨⟨⟨556,772,170,7285⟩,5255817068544,9968090926⟩,10,5,2,643298,5⟩
theorem cover1546 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1546) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
def src1547 : Request := ⟨⟨⟨556,772,170,6888⟩,5255817068544,9968090926⟩,10,5,2,643298,10⟩
theorem cover1547 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1547) 2411 2314 [2318, 2334, 2385, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source0764

-- Source: Research6969.PrefixRescueDataRepricedHelperCases1
section Z6969Source0765
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueData.RepricedHelperCases1
open Research6969.PhysicalCatalogue
open Research6969.TransitionBanks
open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Main (Band)

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,5,1,40⟩
  bank i := ![bank101 6096, bank134 6096, bank141 7715, bank156 8679, bank204 12355, bank233 22261, bank297 50764, bank296 102908, bank352 102908, bank319 422931, bank307 164837] i
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

theorem sources : plan.Sources 2314 (Band.near).last := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank101 6096
    · exact rank134 6096
    · exact rank141 7715
    · exact rank156 8679
    · exact rank204 12355
    · exact rank233 22261
    · exact rank297 50764
    · exact rank296 102908
    · exact rank352 102908
    · exact rank319 422931
    · exact rank307 164837
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover1495⟩
    · exact ⟨_, cover1496⟩
    · exact ⟨_, cover1497⟩
    · exact ⟨_, cover1498⟩
    · exact ⟨_, cover1499⟩
    · exact ⟨_, cover1500⟩
    · exact ⟨_, cover1501⟩
    · exact ⟨_, cover1502⟩
    · exact ⟨_, cover1505⟩
    · exact ⟨_, cover1504⟩
    · exact ⟨_, cover1503⟩

def price : EarlyPrice := ⟨5, 40, 10, 70/100, 70/100, ![6585760573734, 739832052370, 33852906236, 3385304972], 2184734874597898⟩
theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

theorem final_cap : plan.history price.stop = ![12588/191, 189868/191, 899460/191, 4116320/191] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969RescueData.RepricedHelperCases1
end Z6969Source0765

-- Source: Research6969.PrefixNearSavedRepricedHelperCases1
section Z6969Source0766
set_option autoImplicit true
namespace Lower6960.Prefix6969Early.NearSavedRepricedHelperCases1
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

def terminalExit : Exit := ⟨336,4321,65,994,false⟩

theorem exit_checked : terminalExit.Valid Lower6960.Prefix6969MainCases.RepricedHelperCases1.plan Lower6960.Prefix6969RescueData.RepricedHelperCases1.plan Lower6960.Prefix6969RescueData.RepricedHelperCases1.price := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro yes
  cases yes

def data : NearCase 5 26 40 643299 :=
  ⟨Lower6960.Prefix6969MainCases.RepricedHelperCases1.plan, Lower6960.Prefix6969MainCases.RepricedHelperCases1.price, Lower6960.Prefix6969MainCases.RepricedHelperCases1.valid, Lower6960.Prefix6969MainCases.RepricedHelperCases1.priced, Lower6960.Prefix6969MainCases.RepricedHelperCases1.sources,
   Lower6960.Prefix6969RescueData.RepricedHelperCases1.plan, Lower6960.Prefix6969RescueData.RepricedHelperCases1.price, Lower6960.Prefix6969RescueData.RepricedHelperCases1.sources, Lower6960.Prefix6969RescueData.RepricedHelperCases1.priced,
   rfl,rfl,rfl,rfl,terminalExit,exit_checked⟩

theorem fee_exact : data.fee = 230390820158410918 := by
  rw [NearCase.fee.eq_1 data, Lower6960.Prefix6969Early.extra_eq data.exit Lower6960.Prefix6969Main.Band.near data.rp (by decide)]
  decide +kernel

end Lower6960.Prefix6969Early.NearSavedRepricedHelperCases1
end Z6969Source0766

-- Source: Research6969.PrefixNearUniform
section Z6969Source0767
set_option autoImplicit true
namespace Lower6960.Prefix6969Early
noncomputable section

open K1_14_1 (PoleData CRTLift)
open Far6969RescueGeometry (Model Family)

abbrev nearFee : ℕ := 234329630343844473
abbrev nearOrd : ℕ := 133994566145700
abbrev nearSeed : ℕ := 1590006772040
abbrev nearGrade : ℕ := 351
abbrev nearWidth : ℕ := 6143

theorem Packet.reprice {u del} {M : Model u del} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D}
    {fee ord seed e v fee' ord' seed' e' v' : ℕ}
    (P : Packet F Crt fee ord seed e v) (eg : e≤e') (vg : v≤v')
    (budget : fee+(ord'-ord)*e+(seed'-seed)*v≤fee') :
    Nonempty (Packet F Crt fee' ord' seed' e' v') := by
  have ordPrice := compensate ord' ord P.projected.natDegree e P.degree_cap
  have seedPrice := compensate seed' seed (K1_14_4.seedDegree P.projected) v P.seed_cap
  have paid := P.bill
  exact ⟨⟨P.paid,P.parents,P.projected,P.project,P.geo,P.terminal,
    P.degree_cap.trans eg,P.seed_cap.trans vg,by omega,P.cover⟩⟩

def NearCase.uniform {a l u w : ℕ} (c : NearCase a l u w) : Prop :=
  c.exit.mDegree≤nearGrade ∧ c.exit.mWidth≤nearWidth ∧
    c.fee+(nearOrd-c.mp.retainedCredit 0)*c.exit.mDegree+
      (nearSeed-(c.mp.retainedCredit 1+c.mp.retainedCredit 2))*c.exit.mWidth≤nearFee

def UniformAllowed (a u : ℕ) : Prop :=
  (a=2 → 20≤u) ∧ (a=3 → u≤40) ∧ (a=5 → u≤25 ∨ 41≤u)

instance (a u : ℕ) : Decidable (UniformAllowed a u) := by
  unfold UniformAllowed
  infer_instance

end
end Lower6960.Prefix6969Early
end Z6969Source0767

-- Source: Research6969.PrefixRescueNormal
section Z6969Source0768
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace Lower6960.Prefix6969Rescue
noncomputable section

open Finset Polynomial
open K1 (K p)
open K1_14 (Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (UsesSeed toJet)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (Surface Parent)
open P1_7_4 (massQ Mass)
open Far6969RescueGeometry (Model Family OnSurface word)
open Research6966

structure NormalPrice where
  seed : ℕ
  tau : ℚ
  scale : ℚ
  credit : Fin 4 → ℕ
  fee : ℕ

namespace NormalPrice

def calculatedFee (x : NormalPrice) (plan : Plan) : ℕ :=
  Invoice.eventFee plan plan.count plan.normalShape plan.history 2 x.seed x.tau x.scale

def running (x : NormalPrice) (plan : Plan) : Mass :=
  Invoice.eventRunning plan plan.count plan.normalShape 2 x.seed x.tau x.scale

structure Valid (x : NormalPrice) (plan : Plan) : Prop where
  seed_pos : 0 < x.seed
  char : 3*x.seed < p
  graph_shape : plan.primeShape = graphShape 2 x.seed
  slope_floor : plan.slopeFloor = 1
  tau_nonneg : 0 ≤ x.tau
  tau_le_one : x.tau ≤ 1
  rank_small : Invoice.rankB plan < p
  exact_fee : x.calculatedFee plan ≤ x.fee
  retained : ∀ k, (x.credit k : ℚ) ≤ x.running plan k

end NormalPrice

/-- Run the full slope-one rescue schedule, including the proper terminal-bank cut. -/
theorem normal_prefix {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D}
    {plan : Plan} {x : NormalPrice}
    (S : plan.Sources 2314 2411) (cert : x.Valid plan)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G plan.primeShape)
    (degree : plan.degree ≤ jetDegree G) (seed : plan.seedFloor ≤ seedDegree G)
    (physical : plan.physicalFloor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw)
    (roots : ∀ γ∈Γ, jetAt G (M.label γ) (F.scalar γ) = 0) :
    ∃ (R : Run F Crt G plan) (B : Book R) (Q : Finset Surface),
      B.final = R.terminal ∧
      (Invoice.paid B).card + Invoice.charge B x.credit ≤ x.fee ∧
      (∀ k, massQ B.final k ≤ plan.history (plan.count-1) k) ∧
      (∀ q∈Q, Parent q ∧ Prefix6969Wide.SurfacePass Crt (word M) q ∧
        G∈q.asIdeal ∧ ∃ J∈B.final, q.asIdeal=J.comap toJet) ∧
      ∀ γ∈Γ, γ∈Invoice.paid B ∨
        (regular G (M.label γ) (F.scalar γ) ∧ ∃ q∈Q, OnSurface F q γ) := by
  obtain ⟨R⟩ := S.run F Crt lo hi noPole residues phys prime
    (le_of_eq (cert.slope_floor.trans slope.symm)) seeded caps degree seed physical
  have geomCaps : RowCaps G (graphShape 2 x.seed) := cert.graph_shape ▸ caps
  obtain ⟨event⟩ := Invoice.normal_event R (le_refl 2) cert.seed_pos prime slope geomCaps cert.char hi roots
    cert.tau_nonneg cert.tau_le_one cert.rank_small x.credit noPole residues cert.exact_fee cert.retained
  let B := event.book
  obtain ⟨surfaces, geom, marked⟩ := Invoice.Book.surfaces B
  refine ⟨R, B, surfaces, event.final, event.count, ?_, ?_, ?_⟩
  · intro k
    show massQ event.book.final k ≤ _
    rw [event.final]
    exact Invoice.Run.mass_terminal R k
  · intro q hq
    obtain ⟨parent, J, mem, origin⟩ := geom q hq
    obtain ⟨pass, inIdeal⟩ := Invoice.Book.terminal_parent B event.final mem origin
    exact ⟨parent, pass, inIdeal, J, mem, origin⟩
  · intro γ mem
    rcases Invoice.Book.paid_or_regular B mem (roots γ mem) with paid | ⟨reg, survivor⟩
    · exact Or.inl paid
    · exact Or.inr ⟨reg, marked γ mem survivor⟩


end
end Lower6960.Prefix6969Rescue
end Z6969Source0768

-- Source: Research6969.TransitionClassification
section Z6969Source0769
set_option autoImplicit true
namespace Research6969.TransitionClassification
noncomputable section
open Finset Polynomial
open K1 (p)
open K1_14 (L Shape Equation)
open K1_14_1 (PoleData CRTLift)
open K1_14_3 (Surface Parent ProjectedProduct SeedField)
open Research6966
open scoped Classical
set_option maxHeartbeats 1600000
set_option maxRecDepth 12000
abbrev agreement : ℕ:=179730
def grade (b:Fin 8):ℕ:=![22,23,25,28,33,41,50,64] b
def content (b:Fin 8):ℕ:=![9,9,9,9,9,9,10,12] b
def maxGraph (b:Fin 8):ℕ:=![6,6,5,4,4,3,3,2] b

theorem prices (b:Fin 8) {h:ℕ} (lo:2314≤h) (hi:h≤2557) :
    (∀a,maxGraph b<a → a≤content b →
      PadeCutoff.excluded agreement h (grade b) a (grade b-content b+a)
        SpreadCatalogue.shape SpreadCatalogue.box SpreadCatalogue.nodes SpreadCatalogue.moment) ∧
    (∀a,grade b+1-(grade b+1)/2≤a → a≤grade b-content b →
      PadeCutoff.excluded agreement h (grade b) a (grade b)
        SpreadCatalogue.shape SpreadCatalogue.box SpreadCatalogue.nodes SpreadCatalogue.moment) := by
  fin_cases b
  · exact ⟨fun _=>SpreadCatalogue.partial22 lo hi,fun _=>SpreadCatalogue.full22 lo hi⟩
  · exact ⟨fun _=>SpreadCatalogue.partial23 lo hi,fun _=>SpreadCatalogue.full23 lo hi⟩
  · exact ⟨fun _=>SpreadCatalogue.partial25 lo hi,fun _=>SpreadCatalogue.full25 lo hi⟩
  · exact ⟨fun _=>SpreadCatalogue.partial28 lo hi,fun _=>SpreadCatalogue.full28 lo hi⟩
  · exact ⟨fun _=>SpreadCatalogue.partial33 lo hi,fun _=>SpreadCatalogue.full33 lo hi⟩
  · exact ⟨fun _=>SpreadCatalogue.partial41 lo hi,fun _=>SpreadCatalogue.full41 lo hi⟩
  · exact ⟨fun _=>SpreadCatalogue.partial50 lo hi,fun _=>SpreadCatalogue.full50 lo hi⟩
  · exact ⟨fun _=>SpreadCatalogue.partial64 lo hi,fun _=>SpreadCatalogue.full64 lo hi⟩

theorem classify {h:ℕ} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L)
    (lo:2314≤h) (hi:h≤2557) (b:Fin 8) (S:Finset Surface) (live:S.Nonempty)
    (geo:∀q∈S,Parent q) (pass:∀q∈S,TerminalBanks.Pass Crt word agreement SpreadCatalogue.shape q)
    {f:Equation} (whole:ProjectedProduct S f) (large:grade b≤f.natDegree) :
    ∃ G:Pade.Row SeedField, G.primitive ∧ G.graphDegree≤maxGraph b ∧
      Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets S) (content b) := by
  have fits:TerminalBanks.inside SpreadCatalogue.shape SpreadCatalogue.shape:=by unfold TerminalBanks.inside;decide
  have width:SpreadCatalogue.shape.B*(131071-h)≤SpreadCatalogue.shape.m*agreement:=
    (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left lo _)).trans (by decide)
  have ok:2≤grade b ∧ 2*content b<grade b:=by fin_cases b <;> decide
  obtain ⟨l,r⟩:=prices b lo hi
  obtain ⟨g,proj,small|graph⟩:=PadeCutoff.counted_packet (by omega) (hi.trans (by decide))
    (hi.trans_lt (by decide)) Crt word SpreadCatalogue.box fits (by decide) (by decide)
    (by decide) (by decide) width SpreadCatalogue.node_eq.le SpreadCatalogue.pole_cap S live geo pass ok.1 ok.2 l r
  · exact (Nat.not_lt_of_ge (large.trans_eq (Research6966.NearTerminal.same_degree whole proj)) small).elim
  · exact graph

def band (e:ℕ):Fin 8:=
  if e<23 then 0 else if e<25 then 1 else if e<28 then 2 else if e<33 then 3
  else if e<41 then 4 else if e<50 then 5 else if e<64 then 6 else 7

theorem lower_bound {e:ℕ} (large:22≤e) : grade (band e)≤e := by
  unfold band
  split_ifs <;> dsimp [grade] <;> omega

/-- The actual terminal union has an admissible native graph in the
grade band containing its own degree. -/
theorem graph_above_twenty_one {h:ℕ} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L)
    (lo:2314≤h) (hi:h≤2557) (S:Finset Surface) (live:S.Nonempty)
    (geo:∀q∈S,Parent q) (pass:∀q∈S,TerminalBanks.Pass Crt word agreement SpreadCatalogue.shape q)
    {f:Equation} (whole:ProjectedProduct S f) (large:22≤f.natDegree) :
    ∃ G:Pade.Row SeedField,G.primitive ∧ G.graphDegree≤maxGraph (band f.natDegree) ∧
      Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets S) (content (band f.natDegree)) :=
  classify Crt word lo hi (band f.natDegree) S live geo pass whole (lower_bound large)

end
end Research6969.TransitionClassification
end Z6969Source0769

-- Source: Research6969.PhysicalChecks000
section Z6969Source0770
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src629 : Request := ⟨⟨⟨1750,2442,527,164470⟩,161065121873920,975196209190⟩,0,2,1,308385,1⟩
theorem cover629 : PhysicalWindow.Cover (PhysicalWindow.Triangular src629) 2411 2314 [2315, 2321, 2338, 2387, 2411] := triangleCover (by decide +kernel)
def src630 : Request := ⟨⟨⟨1750,2442,527,182926⟩,161065121873920,975196209190⟩,1,2,1,308385,1⟩
theorem cover630 : PhysicalWindow.Cover (PhysicalWindow.Triangular src630) 2411 2314 [2315, 2321, 2338, 2387, 2411] := triangleCover (by decide +kernel)
def src631 : Request := ⟨⟨⟨1750,2442,527,206037⟩,161065121873920,975196209190⟩,2,2,1,308385,1⟩
theorem cover631 : PhysicalWindow.Cover (PhysicalWindow.Triangular src631) 2411 2314 [2315, 2321, 2338, 2387, 2411] := triangleCover (by decide +kernel)
def src632 : Request := ⟨⟨⟨2100,2930,622,220122⟩,274699477319680,1994139134137⟩,3,2,1,308385,1⟩
theorem cover632 : PhysicalWindow.Cover (PhysicalWindow.Triangular src632) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src633 : Request := ⟨⟨⟨2100,2930,632,234092⟩,278060332482560,2019119590628⟩,4,2,1,308385,1⟩
theorem cover633 : PhysicalWindow.Cover (PhysicalWindow.Triangular src633) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src634 : Request := ⟨⟨⟨2100,2930,632,292397⟩,278060332482560,2019119590628⟩,6,2,1,308385,1⟩
theorem cover634 : PhysicalWindow.Cover (PhysicalWindow.Triangular src634) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src635 : Request := ⟨⟨⟨2600,3628,783,364135⟩,527755772952576,4745819470168⟩,10,2,1,308385,1⟩
theorem cover635 : PhysicalWindow.Cover (PhysicalWindow.Triangular src635) 2411 2314 [2315, 2321, 2338, 2385, 2411] := triangleCover (by decide +kernel)
def src636 : Request := ⟨⟨⟨3200,4465,963,321892⟩,983050615259136,10877088344236⟩,10,2,1,308385,1⟩
theorem cover636 : PhysicalWindow.Cover (PhysicalWindow.Triangular src636) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src637 : Request := ⟨⟨⟨3200,4465,947,410737⟩,970564165959680,10735676910569⟩,13,2,1,308385,1⟩
theorem cover637 : PhysicalWindow.Cover (PhysicalWindow.Triangular src637) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src638 : Request := ⟨⟨⟨3950,5512,1189,365477⟩,1848744952463360,25255771038451⟩,13,2,1,308385,1⟩
theorem cover638 : PhysicalWindow.Cover (PhysicalWindow.Triangular src638) 2411 2314 [2315, 2320, 2334, 2373, 2411] := triangleCover (by decide +kernel)
def src639 : Request := ⟨⟨⟨3950,5512,1189,421074⟩,1848744952463360,25255771038451⟩,16,2,1,308385,1⟩
theorem cover639 : PhysicalWindow.Cover (PhysicalWindow.Triangular src639) 2411 2314 [2315, 2320, 2334, 2373, 2411] := triangleCover (by decide +kernel)
def src1205 : Request := ⟨⟨⟨556,772,170,8675⟩,5255817068544,9968090926⟩,10,3,2,437044,2⟩
theorem cover1205 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1205) 2411 2314 [2318, 2333, 2381, 2411] := triangleCover (by decide +kernel)
def src0 : Request := ⟨⟨⟨2800,3907,854,31300⟩,665461916958720,6445344460182⟩,4,1,1,128659,29⟩
theorem cover0 : PhysicalWindow.Cover (PhysicalWindow.Triangular src0) 2411 2314 [2315, 2321, 2338, 2385, 2411] := triangleCover (by decide +kernel)
def src1 : Request := ⟨⟨⟨2300,3209,702,25043⟩,369170633195520,2936492475204⟩,15,1,1,128659,33⟩
theorem cover1 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1) 2411 2314 [2318, 2332, 2371, 2411] := triangleCover (by decide +kernel)
def src2 : Request := ⟨⟨⟨2300,3209,724,22209⟩,377903408742400,3007761756493⟩,15,1,1,128659,33⟩
theorem cover2 : PhysicalWindow.Cover (PhysicalWindow.Triangular src2) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src3 : Request := ⟨⟨⟨2600,3627,793,28173⟩,532875289296896,4788739883894⟩,45,1,1,128659,41⟩
theorem cover3 : PhysicalWindow.Cover (PhysicalWindow.Triangular src3) 2411 2314 [2321, 2343, 2405, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source0770

-- Source: Research6969.PrefixSeedOneHelper
section Z6969Source0771
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000

namespace Lower6960.Prefix6969SeedOneHelper
noncomputable section

open K1_14 (Jet L Shape)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape evaluated_mono)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Research6969.PhysicalCatalogue (src1205 cover1205)
open Research6969.PhysicalWindow (covered)
open Research6969.TransitionBanks (rank154)
open Research6966
open Prefix6969KnownHelper (restricted restricted_nonzero common_of_le known_unique prepare_known)
open PrefixRows (Common Prepared)

abbrev bank : P1_7.Bank := src1205.bank
abbrev helperCutoff (h : ℕ) : ℕ := src1205.top h - 1

theorem width {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2411) :
    HelperSource.WidthGuard bank 179730 h 10 :=
  HelperSource.width_at_height bank 179730 2314 h 10 lo (hi.trans (by decide))
    (by decide) (by unfold HelperSource.WidthGuard; decide +kernel)

theorem nonzero {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2411)
    {D : PoleData h} (Crt : CRTLift D) (w : K1.I → L) :
    ∃ H ∈ evaluated Crt w bank.shape (helperCutoff h), H ≠ 0 := by
  obtain ⟨left, right, hlo, hhi, rmax, certified⟩ := covered cover1205 lo hi
  have narrow : bank.shape.J < 131071 - right :=
    (by decide : bank.shape.J < 131071 - 2411).trans_le (Nat.sub_le_sub_left rmax _)
  exact restricted_nonzero src1205 (by omega) (hi.trans (by decide)) hlo hhi
    narrow (by decide) certified (rank154 8675) (width lo hi) Crt w

theorem subspace {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : K1.I → L) :
    evaluated Crt w bank.shape (helperCutoff h) ≤
      evaluated Crt w Prefix6969Helper.helperBank.shape (Prefix6969Helper.helperCutoff h) := by
  intro P hp
  exact evaluated_mono Crt w (s := bank.shape) (s' := Prefix6969Helper.helperBank.shape)
    rfl rfl rfl (by decide) le_rfl hp

theorem unique {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2411)
    {D : PoleData h} (Crt : CRTLift D) (w : K1.I → L) {G : Jet}
    (phys : HelperPhysicalModel.Model Crt G)
    (outer : Common (evaluated Crt w Prefix6969Helper.helperBank.shape (Prefix6969Helper.helperCutoff h)) G)
    (degree : 2 ≤ jetDegree G) (seed : 1 ≤ seedDegree G)
    (physical : 308385 ≤ RawPhysicalDegree.weight (131071 - h) (131071 - h - 1) phys.raw) :
    ∀ Q₁ Q₂, Common (evaluated Crt w bank.shape (helperCutoff h)) Q₁ →
      Common (evaluated Crt w bank.shape (helperCutoff h)) Q₂ → IsRelPrime Q₁ Q₂ → False := by
  obtain ⟨left, right, hlo, hhi, rmax, certified⟩ := covered cover1205 lo hi
  have narrow : bank.shape.J < 131071 - right :=
    (by decide : bank.shape.J < 131071 - 2411).trans_le (Nat.sub_le_sub_left rmax _)
  exact known_unique bank 10 2 308385 1 128659 (by omega) (hi.trans (by decide)) hlo hhi
    narrow (rank154 8675) (by decide) (width lo hi) certified Crt w phys
    (common_of_le (subspace Crt w) outer) degree physical seed (by omega)

theorem produce {ι : Type*} [Fintype ι] (P : ι → Jet) (s : ι → Shape) (copies : ι → ℕ)
    {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2411) {D : PoleData h}
    (Crt : CRTLift D) (w : K1.I → L) {G : Jet}
    (phys : HelperPhysicalModel.Model Crt G)
    (outer : Common (evaluated Crt w Prefix6969Helper.helperBank.shape (Prefix6969Helper.helperCutoff h)) G)
    (degree : 2 ≤ jetDegree G) (seed : 1 ≤ seedDegree G)
    (physical : 308385 ≤ RawPhysicalDegree.weight (131071 - h) (131071 - h - 1) phys.raw)
    (nz : ∀ i, P i ≠ 0) (caps : ∀ i, RowCaps (P i) (s i)) :
    ∃ out : Prepared P s copies (evaluated Crt w bank.shape (helperCutoff h)) bank.shape,
      out.exception = G :=
  prepare_known P s copies _ _ (common_of_le (subspace Crt w) outer) nz caps
    (nonzero lo hi Crt w) (fun _ mem => evaluated_shape Crt w mem)
    (unique lo hi Crt w phys outer degree seed physical)

end
end Lower6960.Prefix6969SeedOneHelper
end Z6969Source0771

-- Source: Research6969.PrefixSeedOneMainSchedule
section Z6969Source0772
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000

namespace Lower6960.Prefix6969SeedOneMain

open Research6969
open Research6969.TransitionBanks
open K1_14 (L)
open K1_14_1 (PoleData CRTLift evaluated)
open Lower6960.HelperSource
open P1_7_4 (Mass)

abbrev count : ℕ := 18
abbrev firstHeight : ℕ := 2314
abbrev lastHeight : ℕ := 2411
abbrev agreement : ℕ := 179730

def reserve (i : Fin count) : ℕ := ![0, 1, 2, 3, 4, 5, 7, 10, 16, 21, 20, 30, 41, 41, 76, 76, 76, 76] i
def bank (i : Fin count) : P1_7.Bank :=
  ![bank4 1470, bank9 1624, bank17 1760, bank23 1898, bank26 2102, bank32 2243, bank44 2409, bank54 2755, bank74 3583, bank84 5564, bank112 3547, bank108 8100, bank120 36262, bank150 6517, bank210 11036, bank181 61748, bank174 148759, bank169 292467] i

theorem free_checked (i : Fin count) : TransitionSources.Free firstHeight (reserve i) (bank i) := by
  fin_cases i
  · exact free4_0
  · exact free9_0
  · exact free17_0
  · exact free23_0
  · exact free26_0
  · exact free32_0
  · exact free44_0
  · exact free54_0
  · exact free74_1
  · exact free84_0
  · exact free112_0
  · exact free108_1
  · exact free120_0
  · exact free150_0
  · exact free210_0
  · exact free181_0
  · exact free174_0
  · exact free169_0

def cutoff (h : ℕ) (i : Fin count) : ℕ :=
  cutoffCount (bank i).shape agreement h (reserve i) - 1

theorem cutoff_fit {h : ℕ} (lo : firstHeight ≤ h) (hi : h ≤ lastHeight) (i : Fin count) :
    cutoff h i + 2 * h * reserve i < (bank i).shape.m * agreement := by
  have cert := free_checked i
  have hw := width_at_height _ _ _ _ _ lo (hi.trans (by decide)) cert.reserve_fit cert.width
  exact Lower6960.FreeSource.buffered_fit (bank i) agreement h (reserve i) hw

theorem free_rows {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : firstHeight ≤ h) (hi : h ≤ lastHeight) (i : Fin count) :
    ∃ P ∈ evaluated Crt word (bank i).shape (cutoff h i), P ≠ 0 :=
  (free_checked i).row Crt word ((by decide : 0 < firstHeight).trans_le lo) lo (hi.trans (by decide))

def suppliedHistory : List Mass :=
  [![14801, 171537, 801201, 4074442],
   ![12303, 147095, 1329539/2, 3522050],
   ![53398/9, 637525/9, 619520, 3097600],
   ![3599, 343505/8, 3113506/9, 16465150/9],
   ![60658/25, 147808/5, 211251, 9117425/8],
   ![16211/9, 789035/36, 211251, 9117425/8],
   ![18775/16, 886655/64, 396682/3, 644809],
   ![89110/121, 1032225/121, 4677310/49, 7590025/16],
   ![89110/121, 1032225/121, 2000617/24, 31082525/72],
   ![63754/121, 1859179/242, 15374666/225, 31082525/72],
   ![63754/121, 1055510/147, 15374666/225, 2461618/9],
   ![24521/50, 1055510/147, 15374666/225, 2461618/9],
   ![667406/1681, 1055510/147, 15374666/225, 2461618/9],
   ![667406/1681, 10295860/1681, 46322996/841, 42471289/169],
   ![667406/1681, 7533960/1369, 1724375/36, 167540275/729],
   ![474397/1369, 7533960/1369, 1724375/36, 167540275/729],
   ![462882/1369, 7533960/1369, 1724375/36, 167540275/729],
   ![459151/1369, 7533960/1369, 1724375/36, 167540275/729]]

def suppliedDegreeRates : List ℕ := [367868119, 366604032, 367389972, 366835848, 366362383, 367250716, 367115638, 156881649, 157144991, 157199284, 115270357, 87300349, 86969492, 115465894, 115567675, 131740080, 179078930, 239214604]
def suppliedHeightRates : List ℕ := [938499, 941965, 939810, 941329, 942627, 940192, 940562, 2453002, 2448623, 2447720, 3396467, 4552469, 4569157, 3391000, 3388154, 2951688, 2123256, 1537212]
def retainedCredit (i : Fin 4) : ℕ := ![126979896095280, 1601383685396, 215293143600, 4034399880] i
abbrev prefixCap : ℕ := 205786607349302799

end Lower6960.Prefix6969SeedOneMain
end Z6969Source0772

end Merged_Z6969Pack0629

-- merged module Z6969Pack0630
section Merged_Z6969Pack0630

-- Source: Research6969.PrefixSeedOneMainGeometry
section Z6969Source0773
set_option autoImplicit true
set_option Elab.async false

section Merged_R6960MainGeometry

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000

namespace Lower6960.Prefix6969SeedOneMain
open Finset Polynomial
open K1 (I K)
open K1_14 (L Shape Jet jetAt seedHasse)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient toJet jetMarkHom)
open K1_14_2_2 (RowCaps Active dual orderOn FixedPart)
open K1_14_2_2R (chainCompatible)
open HelperPrefix (timesShape)
open Prefix6969SeedOneHelper (helperCutoff)

abbrev helperBank := Prefix6969SeedOneHelper.bank
open MainPrefixSource (hasse_at_mark)
open Far6969RescueGeometry (Model Family word OnMark contact_at_mark zero_of_contact)
open DifferentialContact (Native)
open PrefixRows (Prepared)
open P1_7_4 (ODEGuard degreeVector introJump introWeight)
open scoped Classical

def terminalShape : Shape := ⟨3000, 4184, 900, 530820⟩

def copies (i : Fin count) : ℕ := (reserve i + 11) / 11

theorem reserve_small (i : Fin count) : reserve i < K1.p := by
  fin_cases i <;> decide +kernel

def freeShape (i : Fin 18) : Shape := (bank i).shape

def movingShape (i : Fin 18) : Shape := timesShape (copies i) helperBank.shape

def stage (i : Fin 18) : P1_7.Stage := ⟨reserve i,bank i,⟨movingShape i,0,0⟩⟩

def cutShape (i : ℕ) : Shape :=
  if hi : i+1<18 then HighCore82258_3.envelope (stage ⟨i+1,hi⟩) else terminalShape

theorem cutShape_fit (i : ℕ) : (cutShape i).J≤(cutShape i).B := by
  unfold cutShape
  split
  · exact Nat.le_add_left _ _
  · decide

def introIndices : List (Fin 18) := [1,2,3,4,5,6,7,8,9,10,11]

def introAccount (k : Fin 4) : List (Fin 18) → (Fin 3→ℕ) → (Fin 3→ℕ) → ℕ
  | [], cap, old =>
      introJump cap old (movingShape 0) k +
        K1_14_2_2_2.ordinaryBudget (cap 2) (cap 0) k
  | i::rest, cap, old =>
      let s := freeShape i
      introJump cap old s k + introAccount k rest
        (fun j=>min (cap j) (degreeVector s j/(reserve i+1)))
        (fun j=>max (old j) (introWeight s k j))

def initialCap (k : Fin 4) : ℕ :=
  introAccount k introIndices (degreeVector (freeShape 0)) (fun _=>0)

theorem initial_small (k : Fin 4) : initialCap k < K1.p := by
  fin_cases k <;> decide +kernel

theorem free_ode_guard (i : Fin 18) : ODEGuard (freeShape i).B (freeShape i).J := by
  fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩

theorem moving_ode_guard (i : Fin 18) : ODEGuard (movingShape i).B (movingShape i).J := by
  fin_cases i <;> exact ⟨by decide,by decide,by decide,by decide +kernel⟩

theorem free_seed_small (i : Fin 18) : (freeShape i).U<K1.p := by
  fin_cases i <;> decide +kernel

theorem moving_seed_small (i : Fin 18) : (movingShape i).U<K1.p := by
  fin_cases i <;> decide +kernel

theorem reserve_pos {i : Fin 18} (hi : 0 < i.val) : 0<reserve i := by
  have checks (j : Fin 18) : (j.val=0) ∨ 0<reserve j := by
    fin_cases j <;> decide +kernel
  exact (checks i).resolve_left (by omega)

/-- The main branch retains the single preparation object, including the
original helper, its one possible exception, and the 18 stripped free rows. -/
structure Rows {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) where
  source : Fin 18→Jet
  out : Prepared source freeShape copies
    (evaluated Crt (word M) helperBank.shape (helperCutoff M.overhead.toNat)) helperBank.shape
  contact : ∀ i γ, γ∈Γ → jetAt out.exception (M.label γ) (F.scalar γ)≠0 →
    Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (reserve i+1) (out.free i) ∧
    Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (reserve i+1) (out.helper^copies i)
  fixedFree : ∀ i, FixedPart (out.free i) (freeShape i)
  fixedMoving : ∀ i, FixedPart (out.helper^copies i) (movingShape i)

theorem rows {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314≤M.overhead.toNat) (hi : M.overhead.toNat≤2411)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : Research6966.HelperPhysicalModel.Model Crt G)
    (outer : PrefixRows.Common
      (K1_14_1.evaluated Crt (word M) Prefix6969Helper.helperBank.shape
        (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ K1_14_2_2_2_1.jetDegree G)
    (seed : 1 ≤ K1_14_2_2_2_1.seedDegree G)
    (physical : 308385 ≤ Research6966.RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ R : Rows F Crt, R.out.exception = G := by
  choose P inside nz using free_rows Crt (word M) lo hi
  obtain ⟨out, identity⟩ := Prefix6969SeedOneHelper.produce P freeShape copies lo hi Crt (word M)
    phys outer degree seed physical nz (fun i => evaluated_shape Crt (word M) (inside i))
  refine ⟨⟨P,out,?_,?_,?_⟩, identity⟩
  · intro i γ mem regular
    have fit : reserve i+1 ≤ copies i*11 := by
      change reserve i+1≤((reserve i+11)/11)*11
      omega
    refine out.contacts i _ (RingHom.ker_isPrime _) ?_ (reserve i+1) 11 fit ?_ ?_
    · intro van
      apply regular
      simpa only [K1_14_2.eval_toJet] using RingHom.mem_ker.mp van
    · exact contact_at_mark F Crt noPole residues (inside i) (cutoff_fit lo hi i) γ mem
    · intro H hm
      have wh := Prefix6969SeedOneHelper.width lo hi
      have width : helperCutoff M.overhead.toNat+2*M.overhead.toNat*10 < helperBank.shape.m*179730 :=
        FreeSource.buffered_fit helperBank 179730 _ 10 wh
      exact contact_at_mark F Crt noPole residues hm width γ mem
  · intro i
    exact Classical.choice (K1_14_2_2_1.proof _ _ (out.free_ne i) (out.free_caps i))
  · intro i
    exact Classical.choice (K1_14_2_2_1.proof _ _ (pow_ne_zero _ out.helper_ne) (out.moving_caps i))

def Rows.marks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) : Finset K :=
  Γ.filter (fun γ=>jetAt R.out.exception (M.label γ) (F.scalar γ)≠0)

def Rows.family {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) : Family M R.marks :=
  ⟨F.scalar,fun γ hγ=>F.mark γ (mem_filter.mp hγ).1,F.distinct.mono (filter_subset _ _)⟩

theorem Rows.main_contact {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 18) (γ : K) (mem : γ∈R.marks) :
    Native (RingHom.ker (jetMarkHom (M.label γ) (R.family.scalar γ))) (reserve i+1) (R.out.free i) ∧
    Native (RingHom.ker (jetMarkHom (M.label γ) (R.family.scalar γ))) (reserve i+1) (R.out.helper^copies i) :=
  R.contact i γ (mem_filter.mp mem).1 (mem_filter.mp mem).2

theorem Rows.intro_tests {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 18) (j : Fin 2) (a : ℕ) (ha : a≤reserve i) (γ : K) (mem : γ∈R.marks) :
    jetAt (seedHasse j a (R.out.free i)) (M.label γ) (R.family.scalar γ)=0 :=
  hasse_at_mark (R.main_contact i γ mem).1 j a ha (ha.trans_lt (reserve_small i))

def Rows.Passes {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 18) (J : Ideal Ambient) : Prop :=
  orderOn J (R.out.free i) (reserve i+1) ∧
  orderOn J (R.out.helper^copies i) (reserve i+1) ∧ chainCompatible (R.out.free i) (R.out.helper^copies i) J

theorem Rows.failed_cut {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (i : Fin 18) {J : Ideal Ambient} (active : Active J) (dualJ : dual J) (fail : ¬R.Passes i J) :
    ∃ C : Jet,(RowCaps C (freeShape i) ∨ RowCaps C (movingShape i)) ∧ toJet C∉J ∧
      ∀ γ∈R.marks,OnMark R.family J γ → jetAt C (M.label γ) (R.family.scalar γ)=0 := by
  rcases PrefixStage.order_or_cut active dualJ (reserve_small i) (R.out.free_caps i) (R.out.moving_caps i)
    (pow_ne_zero _ R.out.helper_ne) (moving_ode_guard i).jpos with passes | ⟨C,cap,proper,zero⟩
  · exact (fail passes).elim
  · refine ⟨C,cap,proper,?_⟩
    intro γ hγ on
    obtain ⟨free,moving⟩ := R.main_contact i γ hγ
    exact zero _ _ on free moving

end Lower6960.Prefix6969SeedOneMain

end
end Merged_R6960MainGeometry

section Merged_R6960MainGeometryIntro

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.Prefix6969SeedOneMain
open Finset Polynomial
open K1 (K)
open K1_14 (Shape Jet Seeds FX jetAt graphEval seedHasse atX)
open K1_14_1 (PoleData CRTLift)
open K1_14_2 (Ambient OnJet ODE fixedAt)
open K1_14_2_2 (RowCaps Active dual Fits FixedPart fixedOn mass sectionDegree sum_union_le ordinateIncl ODECaps)
open K1_14_2_2_2 (ordinaryBudget ordinate_eq length_le_mass)
open K1_14_3 (NoMovingCommon SeedCover joinCovers joinCovers_covers joinCovers_degree joinCovers_points)
open P1_7_4 (degreeVector introJump introWeight)
open P1_7_4_1 (SectionGeometry IntroFactors factorDegree factorMass factorMass_mono factorTariff
  weightedDegree tariff_step ordinary_charge residual_tariff collect proper_cover own_J_le_B own_caps retained_mass
  Stripped initial_factors strip)
open Far6969RescueGeometry (Model Family OnMark label_injective zero_of_contact)
open P1_7_4_1 (irreducible_cut terminal_piece)
open P0_10R_1 (seed_projection)
open scoped Classical BigOperators

private theorem intro_components
    {P Q : Jet} (hQ : Q ≠ 0) (hnc : NoMovingCommon P Q)
    (hQc : RowCaps Q (movingShape 0)) (later : Fin 18 → Jet)
    (rows : ∀ i, later i ≠ 0 ∧ RowCaps (later i) (freeShape i)) :
    ∀ (is : List (Fin 18)),
    ∀ (D : Finset Jet) (cap : Fin 3 → ℕ), IntroFactors P D → (∀ j, factorMass D j ≤ cap j) →
    ∃ S : Finset (Ideal Ambient), SectionGeometry S ∧
      (∀ k old, mass S k ≤ introAccount k is cap old + weightedDegree old D) ∧
      ∀ z R, (∀ i ∈ is, ∀ j a, a ≤ reserve i →
        jetAt (seedHasse j a (later i)) z R = 0) →
        jetAt Q z R = 0 → (∃ f ∈ D, jetAt f z R = 0) → ∃ I ∈ S, OnJet I z R := by
  classical
  intro is
  induction is with
  | nil =>
    intro D cap hD hcap
    let t := movingShape 0
    have gt := moving_ode_guard 0
    obtain ⟨S, hG, hS, hC⟩ := collect D
      (fun f k => factorTariff t k f + ordinaryBudget (factorDegree f 2) (factorDegree f 0) k)
      (fun f z R => jetAt f z R = 0 ∧ jetAt Q z R = 0)
      (terminal_piece hD hnc hQc gt.jb gt.small hQ)
    refine ⟨S, hG, ?_, ?_⟩
    · intro k old
      have hstep := tariff_step (Finset.empty_subset D) cap old t k hcap
      simp only [Finset.sdiff_empty, weightedDegree, factorMass, Finset.sum_empty,
        mul_zero, Finset.sum_const_zero, Nat.add_zero] at hstep
      have hsum := Nat.add_le_add hstep (ordinary_charge D cap hcap k)
      calc
        _ ≤ ∑ f ∈ D, (factorTariff t k f +
            ordinaryBudget (factorDegree f 2) (factorDegree f 0) k) := hS k
        _ ≤ (weightedDegree old D + introJump cap old t k) +
            ordinaryBudget (cap 2) (cap 0) k := by
          rw [Finset.sum_add_distrib]
          exact hsum
        _ = _ := by
          simp only [introAccount]
          ac_rfl
    · intro z R _ hq ⟨f, hf, hz⟩
      exact hC f hf z R ⟨hz, hq⟩
  | cons i is ih =>
    intro D cap hD hcap
    let s := freeShape i
    let r := reserve i
    let T := D.filter fun f => ∀ j a, a ≤ r → f ∣ seedHasse j a (later i)
    have hT : T ⊆ D := Finset.filter_subset _ _
    have gt := free_ode_guard i
    obtain ⟨hrow, hc⟩ := rows i
    have hTcap (j : Fin 3) :
        factorMass T j ≤ min (cap j) (degreeVector s j / (r+1)) :=
      le_min ((factorMass_mono hT j).trans (hcap j))
        (retained_mass (hD.mono hT) hrow hc (free_seed_small i) r
          (fun f hf => (Finset.mem_filter.mp hf).2) j)
    obtain ⟨laterCover, hLaterGeom, hLaterCap, hLater⟩ :=
      ih T _ (hD.mono hT) hTcap
    obtain ⟨discard, hDiscardGeom, hDiscardCap, hDiscard⟩ :=
      collect (D \ T) (fun f k => factorTariff s k f)
        (fun f z R => jetAt f z R = 0 ∧
          ∀ j a, a ≤ r → jetAt (seedHasse j a (later i)) z R = 0) (by
        intro f hf
        obtain ⟨hfD, hfT⟩ := Finset.mem_sdiff.mp hf
        have hn : ¬ ∀ j a, a ≤ r → f ∣ seedHasse j a (later i) :=
          fun hall => hfT (Finset.mem_filter.mpr ⟨hfD, hall⟩)
        push Not at hn
        obtain ⟨j, a, ha, hd⟩ := hn
        have hirr := (hD.factors f hfD).1
        obtain ⟨S, hG, hF, hC⟩ := proper_cover (irreducible_cut hirr hd)
          (own_J_le_B hirr.ne_zero) gt.jb (own_caps f) (P1_7_4_1_2.proof s (later i) hc j a)
        exact ⟨S, hG, fun k => (hF k).trans_eq (residual_tariff f s gt.jb k),
          fun z R hr => hC z R hr.1 (hr.2 j a ha)⟩)
    refine ⟨discard ∪ laterCover, ?_, ?_, ?_⟩
    · intro I hI
      exact (Finset.mem_union.mp hI).elim (hDiscardGeom I) (hLaterGeom I)
    · intro k old
      let w := fun j => max (old j) (introWeight s k j)
      let newCap := fun j => min (cap j) (degreeVector s j / (r+1))
      have hstep := tariff_step hT cap old s k hcap
      calc
        _ ≤ mass discard k + mass laterCover k := sum_union_le (fun I => sectionDegree I k) _ _
        _ ≤ (∑ f ∈ D \ T, factorTariff s k f) +
            (introAccount k is newCap w + weightedDegree w T) :=
          Nat.add_le_add (hDiscardCap k) (hLaterCap k w)
        _ = introAccount k is newCap w +
            ((∑ f ∈ D \ T, factorTariff s k f) + weightedDegree w T) := by ac_rfl
        _ ≤ introAccount k is newCap w + (weightedDegree old D + introJump cap old s k) :=
          Nat.add_le_add_left hstep _
        _ = _ := by
          change _ = (introJump cap old s k + introAccount k is newCap w) + weightedDegree old D
          ac_rfl
    · intro z R hder hq ⟨f, hf, hz⟩
      by_cases h : f ∈ T
      · obtain ⟨I, hI, hMark⟩ := hLater z R
          (fun l hl => hder l (List.mem_cons_of_mem _ hl)) hq ⟨f, h, hz⟩
        exact ⟨I, Finset.mem_union_right _ hI, hMark⟩
      · obtain ⟨I, hI, hMark⟩ := hDiscard f (Finset.mem_sdiff.mpr ⟨hf, h⟩) z R
          ⟨hz, hder i (List.mem_cons_self ..)⟩
        exact ⟨I, Finset.mem_union_left _ hI, hMark⟩

def Rows.fixedMarksOf {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) (G : ODE) : Finset K :=
  R.marks.filter (fun γ=>fixedAt G (R.family.scalar γ)=0)

def Rows.fixedMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) : Finset K :=
  (univ : Finset (Fin 18)).biUnion (fun i=>
    R.fixedMarksOf (R.fixedFree i).equation ∪ R.fixedMarksOf (R.fixedMoving i).equation)

theorem Rows.mem_fixed_free {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    {γ : K} (mark : γ∈R.marks) (i : Fin 18)
    (root : fixedAt (R.fixedFree i).equation (R.family.scalar γ)=0) : γ∈R.fixedMarks :=
  mem_biUnion.mpr ⟨i,mem_univ _,mem_union_left _ (mem_filter.mpr ⟨mark,root⟩)⟩

theorem Rows.mem_fixed_moving {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    {γ : K} (mark : γ∈R.marks) (i : Fin 18)
    (root : fixedAt (R.fixedMoving i).equation (R.family.scalar γ)=0) : γ∈R.fixedMarks :=
  mem_biUnion.mpr ⟨i,mem_univ _,mem_union_right _ (mem_filter.mpr ⟨mark,root⟩)⟩

def Rows.Clean {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) (J : Ideal Ambient) : Prop :=
  ∀ i, ¬ fixedOn (R.fixedFree i).equation J ∧ ¬ fixedOn (R.fixedMoving i).equation J

private theorem Rows.fixed_of_not_clean {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    {J : Ideal Ambient} {γ : K} (mark : γ∈R.marks) (on : OnMark R.family J γ)
    (bad : ¬R.Clean J) : γ∈R.fixedMarks := by
  by_contra absent
  apply bad
  intro i
  constructor
  · intro h
    apply absent (R.mem_fixed_free mark i ?_)
    simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on h)
  · intro h
    apply absent (R.mem_fixed_moving mark i ?_)
    simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on h)

private theorem Rows.sections {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) :
    ∃ S : Finset (Ideal Ambient),SectionGeometry S ∧ Fits S initialCap ∧
      ∃ content : Seeds, content≠0 ∧ content.totalDegree≤(freeShape 0).U ∧
      ∀ γ∈R.marks,γ∈R.fixedMarks ∨ graphEval (M.label γ) content=0 ∨ ∃ J∈S,OnMark R.family J γ := by
  obtain ⟨a⟩ := strip (R.out.free_ne 0) (R.out.free_caps 0) (R.fixedFree 0)
  obtain ⟨A,hA,hcap,hroot⟩ := initial_factors a
  obtain ⟨S,geom,fit,cover⟩ := intro_components (pow_ne_zero _ R.out.helper_ne)
    (R.out.no_moving 0) (R.out.moving_caps 0) R.out.free
    (fun i=>⟨R.out.free_ne i,R.out.free_caps i⟩) introIndices A _ hA hcap
  refine ⟨S,geom,?_,a.content,a.content_ne,a.content_le,?_⟩
  · intro k
    simpa only [initialCap,weightedDegree,zero_mul,Finset.sum_const_zero,Nat.add_zero] using fit k (fun _=>0)
  · intro γ hγ
    obtain ⟨p,q⟩ := R.main_contact 0 γ hγ
    rcases a.covers _ _ (zero_of_contact p) with hs | hf | hp
    · exact Or.inr (Or.inl hs)
    · exact Or.inl (R.mem_fixed_free hγ 0 hf)
    · exact Or.inr (Or.inr (cover _ _ (fun i _ j r hr=>R.intro_tests i j r hr γ hγ)
        (zero_of_contact q) (hroot _ _ hp)))

structure Initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) where
  seed : SeedCover
  seed_cap : seed.curve.totalDegree ≤ initialCap 2
  seed_points : seed.points.card ≤ initialCap 3
  ordinates : Finset FX
  ordinate_cap : ordinates.card ≤ initialCap 0
  content : Seeds
  content_ne : content≠0
  content_cap : content.totalDegree≤(freeShape 0).U
  rankExit : Finset (Ideal Ambient)
  parents : Finset (Ideal Ambient)
  fits : Fits (rankExit∪parents) initialCap
  disjoint : Disjoint rankExit parents
  rank_geom : ∀ J∈rankExit,Active J ∧ ¬dual J
  parent_geom : ∀ J∈parents,Active J ∧ dual J ∧ J.height=2 ∧ R.Clean J
  covers : ∀ γ∈R.marks,γ∈R.fixedMarks ∨ graphEval (M.label γ) content=0 ∨
    seed.Covers (M.label γ) ∨ atX (R.family.scalar γ)∈ordinates ∨
      (∃ J∈rankExit,OnMark R.family J γ) ∨ ∃ J∈parents,OnMark R.family J γ

/-- Form the initial affine section cover, remove fixed-factor marks, and
split the remaining active parents at the actual rank-exit index zero. -/
theorem Rows.initial_cover {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) :
    Nonempty (Initial R) := by
  obtain ⟨S,geom,fit,content,cn,cc,cover⟩ := R.sections
  let noSeeds := S.filter (fun J=>sectionDegree J 0=0)
  let constY := S.filter (fun J=>0<sectionDegree J 0 ∧
    ¬Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl))
  let active := S.filter (fun J=>0<sectionDegree J 0 ∧
    Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl))
  let rank := active.filter (fun J=>R.Clean J ∧ ¬dual J)
  let parents := active.filter (fun J=>R.Clean J ∧ dual J)
  have geomActive (J : Ideal Ambient) (mem : J∈active) : Active J ∧ J.height=2 := by
    obtain ⟨hin,seedPos,ord⟩ := mem_filter.mp mem
    obtain ⟨prime,dim,height,finite⟩ := geom J hin
    have small (k : Fin 4) := (length_le_mass hin k).trans_lt ((fit k).trans_lt (initial_small k))
    exact ⟨⟨prime,dim,finite.seeds,finite.ordinate,finite.mixed,finite.jets,
      ⟨seedPos,small 0⟩,small 2,small 3,ord⟩,height⟩
  have seed_exists (J : Ideal Ambient) (mem : J∈noSeeds) :
      ∃ C : SeedCover,C.curve.totalDegree≤sectionDegree J 2 ∧ C.points.card≤sectionDegree J 3 ∧
        ∀ z T,OnJet J z T → C.Covers z := by
    obtain ⟨hin,zero⟩ := mem_filter.mp mem
    obtain ⟨prime,dim,_,finite⟩ := geom J hin
    exact seed_projection J prime dim finite zero
  let seedImage (J : Ideal Ambient) : SeedCover :=
    if mem : J∈noSeeds then Classical.choose (seed_exists J mem) else ⟨1,one_ne_zero,∅⟩
  have seed_spec (J : Ideal Ambient) (mem : J∈noSeeds) :
      (seedImage J).curve.totalDegree≤sectionDegree J 2 ∧
        (seedImage J).points.card≤sectionDegree J 3 ∧
        ∀ z T,OnJet J z T → (seedImage J).Covers z := by
    simpa only [seedImage,dite_eq_left mem] using Classical.choose_spec (seed_exists J mem)
  let onY (J : Ideal Ambient) :=
    (R.marks.filter (OnMark R.family J)).image fun γ=>atX (R.family.scalar γ)
  have ordinate_bound (J : Ideal Ambient) (mem : J∈constY) : (onY J).card≤sectionDegree J 0 := by
    obtain ⟨hin,seedPos,ord⟩ := mem_filter.mp mem
    apply le_trans (b:=1) _ seedPos
    apply card_le_one.mpr
    intro y hy z hz
    obtain ⟨γ,hγ,rfl⟩ := mem_image.mp hy
    obtain ⟨δ,hδ,rfl⟩ := mem_image.mp hz
    exact ordinate_eq (geom J hin).1 ord (mem_filter.mp hγ).2 (mem_filter.mp hδ).2
  refine ⟨⟨joinCovers noSeeds seedImage,?_,?_,constY.biUnion onY,?_,content,cn,cc,
    rank,parents,?_,?_,?_,?_,?_⟩⟩
  · exact (joinCovers_degree _ _).trans ((sum_le_sum fun J mem=>(seed_spec J mem).1).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 2).trans (fit 2)))
  · exact (joinCovers_points _ _).trans ((sum_le_sum fun J mem=>(seed_spec J mem).2.1).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 3).trans (fit 3)))
  · exact card_biUnion_le.trans ((sum_le_sum ordinate_bound).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 0).trans (fit 0)))
  · apply K1_14_2_2.fits_mono _ fit
    exact union_subset ((filter_subset _ _).trans (filter_subset _ _))
      ((filter_subset _ _).trans (filter_subset _ _))
  · exact disjoint_left.mpr fun _ a b=>(mem_filter.mp a).2.2 (mem_filter.mp b).2.2
  · intro J mem
    exact ⟨(geomActive J (mem_filter.mp mem).1).1,(mem_filter.mp mem).2.2⟩
  · intro J mem
    obtain ⟨hin,c,d⟩ := mem_filter.mp mem
    obtain ⟨act,ht⟩ := geomActive J hin
    exact ⟨act,d,ht,c⟩
  · intro γ hγ
    rcases cover γ hγ with fixed | seed | ⟨J,hin,on⟩
    · exact Or.inl fixed
    · exact Or.inr (Or.inl seed)
    · by_cases z : sectionDegree J 0=0
      · have mem : J∈noSeeds := mem_filter.mpr ⟨hin,z⟩
        exact Or.inr (Or.inr (Or.inl (joinCovers_covers mem ((seed_spec J mem).2.2 _ _ on))))
      · by_cases ord : Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl)
        · have mem : J∈active := mem_filter.mpr ⟨hin,Nat.pos_of_ne_zero z,ord⟩
          by_cases clean : R.Clean J
          · by_cases d : dual J
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨J,mem_filter.mpr ⟨mem,clean,d⟩,on⟩))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨J,mem_filter.mpr ⟨mem,clean,d⟩,on⟩))))
          · exact Or.inl (R.fixed_of_not_clean hγ on clean)
        · have mem : J∈constY := mem_filter.mpr ⟨hin,Nat.pos_of_ne_zero z,ord⟩
          exact Or.inr (Or.inr (Or.inr (Or.inl (mem_biUnion.mpr ⟨J,mem,
            mem_image.mpr ⟨γ,mem_filter.mpr ⟨hγ,on⟩,rfl⟩⟩))))

theorem Initial.rank_ode {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ∃ E : ODE, ODECaps E (mass ini.rankExit 2) (mass ini.rankExit 1) ∧
      ∀ γ∈R.marks,(∃ J∈ini.rankExit,OnMark R.family J γ) → fixedAt E (R.family.scalar γ)=0 := by
  obtain ⟨E,caps,roots⟩ := P1_7_4.rank_equation ini.rankExit ini.rank_geom le_rfl le_rfl
  refine ⟨E,caps,?_⟩
  rintro γ _ ⟨J,hJ,on⟩
  simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on (roots J hJ))

end Lower6960.Prefix6969SeedOneMain

end
end Merged_R6960MainGeometryIntro

section Merged_R6960MainGeometryProcess

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.Prefix6969SeedOneMain
open Finset Polynomial
open K1 (K I)
open K1_14 (L Shape Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues evaluated evaluated_shape nodeL)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 (RowCaps Active dual mass mass_mono sectionDegree CutCover weight dot
  emptyCut joinCuts joinCuts_cost sum_dot)
open K1_14_3 (Surface Parent)
open P0_10R.Bridge (surfaceOf parent_of_dual)
open P1_7_4 (Mass massQ massQ_mono pairedCap)
open Far6969RescueGeometry (Model Family OnMark OnSurface word contact_at_mark zero_of_contact)
open HighCore82258_3 (envelope_caps)
open Lower6960.Far6969RescueGeometry (proper_cut)
open scoped Classical BigOperators

def terminalCutoff : ℕ := terminalShape.m*179730-1
def TerminalFits (s : Shape) : Prop :=
  0<s.m ∧ s.B≤terminalShape.B ∧ s.J≤terminalShape.J ∧ s.U≤terminalShape.U
def TerminalPass {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : I→L) (J : Ideal Ambient) : Prop :=
  ∀ s, TerminalFits s → ∀ P∈evaluated Crt w s (s.m*179730-1),toJet P∈J

/-- A parent that fails any terminal bank provides a proper row inside
the single envelope used by the geometric cut bill. -/
theorem terminal_failure {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : I→L)
    {J : Ideal Ambient} (failed : ¬ TerminalPass Crt w J) :
    ∃ (s : Shape) (P : Jet), 0<s.m ∧ P∈evaluated Crt w s (s.m*179730-1) ∧
      RowCaps P terminalShape ∧ toJet P∉J := by
  classical
  unfold TerminalPass at failed
  push Not at failed
  obtain ⟨s,⟨sm,sb,sj,su⟩,P,inside,proper⟩ := failed
  refine ⟨s,P,sm,inside,?_,proper⟩
  intro j i nz
  obtain ⟨b,v,u⟩ := evaluated_shape Crt w inside j i nz
  exact ⟨b.trans sb,v.trans sj,u.trans su⟩

def SurfacePass {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : I→L) (q : Surface) : Prop :=
  ∀ s, TerminalFits s → ∀ P∈evaluated Crt w s (s.m*179730-1),P∈q.asIdeal

theorem SurfacePass.original {h : ℕ} {D : PoleData h} {Crt : CRTLift D} {w : I→L}
    {q : Surface} (pass : SurfacePass Crt w q) :
    ∀ P∈evaluated Crt w terminalShape terminalCutoff,P∈q.asIdeal :=
  pass terminalShape ⟨by decide,le_rfl,le_rfl,le_rfl⟩
def Initial.kept {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) : Finset (Ideal Ambient) :=
  ini.parents.filter (fun J=>∀ i : Fin 18,0 < i.val → i.val≤n → R.Passes i J)

theorem Initial.kept_zero {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ini.kept 0=ini.parents := by
  ext J
  constructor
  · exact fun h=>(mem_filter.mp h).1
  · intro h
    apply mem_filter.mpr
    refine ⟨h,fun i pos zero=>?_⟩
    omega

theorem Initial.kept_anti {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    Antitone ini.kept := by
  intro m n le J mem
  obtain ⟨p,pass⟩ := mem_filter.mp mem
  exact mem_filter.mpr ⟨p,fun i hi hm=>pass i hi (hm.trans le)⟩

theorem Initial.kept_geom {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {n : ℕ} {J : Ideal Ambient} (mem : J∈ini.kept n) :
    Active J ∧ dual J ∧ J.height=2 ∧ R.Clean J :=
  ini.parent_geom J (mem_filter.mp mem).1

def Initial.final {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    Finset (Ideal Ambient) :=
  (ini.kept 17).filter (TerminalPass Crt (word M))

def Initial.live {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) : Finset (Ideal Ambient) := if n<18 then ini.kept n else ini.final

def Initial.lost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) : Finset (Ideal Ambient) := ini.live n \ ini.live (n+1)

theorem Initial.live_zero {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ini.live 0=ini.parents := by
  rw [Initial.live,ite_eq_left (by decide : 0<18),ini.kept_zero]

theorem Initial.next_sub {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<18) : ini.live (i+1)⊆ini.live i := by
  by_cases hn : i+1<18
  · simp only [Initial.live,ite_eq_left hi,ite_eq_left hn]
    exact ini.kept_anti (Nat.le_succ _)
  · have eq : i=17 := by omega
    subst i
    exact filter_subset _ _

theorem Initial.stage_mass {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (i : Fin 18) (hi : 0 < i.val) {n : ℕ} (step : i.val≤n) (k : Fin 4) :
    massQ (ini.kept n) k≤pairedCap (freeShape i) (movingShape i) (reserve i) true k := by
  have s := free_ode_guard i
  have t := moving_ode_guard i
  apply P1_7_4_2.proof (freeShape i) (movingShape i) (reserve i) true (R.out.free i)
    (R.out.helper^copies i) (reserve_pos hi) (reserve_small i) s.small t.small
    (free_seed_small i) (moving_seed_small i) s.jb t.jb (R.out.free_ne i)
    (pow_ne_zero _ R.out.helper_ne) (R.out.free_caps i) (R.out.moving_caps i)
    (R.out.no_moving i) (R.fixedFree i) (R.fixedMoving i)
  · intro _ J mem
    exact (ini.kept_geom mem).2.1
  · intro J mem
    have geom := ini.kept_geom mem
    have pass := (mem_filter.mp mem).2 i hi step
    have clean := geom.2.2.2 i
    exact ⟨geom.1,pass.2.2,clean.1,clean.2,pass.1,pass.2.1⟩

/-- Every failing parent has a marked cutter with the exact stage envelope.
The terminal failure uses a row of the common full bank. -/
theorem Initial.marked_cutter {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {i : ℕ} {J : Ideal Ambient} (hi : i<18) (mem : J∈ini.lost i) :
    ∃ C : Jet,RowCaps C (cutShape i) ∧ toJet C∉J ∧
      ∀ γ∈R.marks,OnMark R.family J γ → jetAt C (M.label γ) (R.family.scalar γ)=0 := by
  obtain ⟨prev,lost⟩ := mem_sdiff.mp mem
  rw [Initial.live,ite_eq_left hi] at prev
  by_cases hn : i+1<18
  · let j : Fin 18 := ⟨i+1,hn⟩
    have hf : ¬R.Passes j J := by
      intro p
      apply lost
      rw [Initial.live,ite_eq_left hn]
      apply mem_filter.mpr
      refine ⟨(mem_filter.mp prev).1,?_⟩
      intro z hz ht
      by_cases same : z.val=i+1
      · exact (Fin.ext same : z=j) ▸ p
      · exact (mem_filter.mp prev).2 z hz (by omega)
    have geom := ini.kept_geom prev
    obtain ⟨C,cap,proper,zero⟩ := R.failed_cut j geom.1 geom.2.1 hf
    refine ⟨C,?_,proper,zero⟩
    rw [cutShape,dite_eq_left hn]
    exact envelope_caps (s:=stage j) (free_ode_guard j).jb (moving_ode_guard j).jb cap
  · have eq : i=17 := by omega
    subst i
    have hf : ¬ TerminalPass Crt (word M) J := fun p =>
      lost (mem_filter.mpr ⟨prev,p⟩)
    obtain ⟨s,C,sm,inside,cap,proper⟩ := terminal_failure Crt (word M) hf
    refine ⟨C,cap,proper,?_⟩
    intro γ hγ _
    apply zero_of_contact (r:=0)
    exact contact_at_mark R.family Crt noPole
      (fun δ hd=>residues δ (mem_filter.mp hd).1) inside
      (by simpa only [Nat.mul_zero,Nat.add_zero] using Nat.sub_lt (Nat.mul_pos sm (by decide : 0<179730)) (by decide : 0<1)) γ hγ

theorem Initial.cutCover {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {i : ℕ} (hi : i<18) :
    ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight (cutShape i) fee) (mass (ini.lost i))) ∧
      ∀ γ∈R.marks,(∃ J∈ini.lost i,OnMark R.family J γ) → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark R.family Q γ := by
  have oneCut (J : Ideal Ambient) (mem : J∈ini.lost i) :
      ∃ C : CutCover,(∀ fee,C.cost fee≤dot (weight (cutShape i) fee) (sectionDegree J)) ∧
        ∀ γ∈R.marks,OnMark R.family J γ → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark R.family Q γ := by
    obtain ⟨P,cap,proper,zero⟩ := ini.marked_cutter noPole residues hi mem
    have prev := (mem_sdiff.mp mem).1
    rw [Initial.live,ite_eq_left hi] at prev
    let sub := R.marks.filter (OnMark R.family J)
    let G : Family M sub :=
      ⟨R.family.scalar,fun γ hγ=>R.family.mark γ (mem_filter.mp hγ).1,
        R.family.distinct.mono (filter_subset _ _)⟩
    obtain ⟨C,cost,cover⟩ := proper_cut G (cutShape i) (cutShape_fit i)
      (ini.kept_geom prev).1 cap proper
      (fun γ hγ=>zero γ (mem_filter.mp hγ).1 (mem_filter.mp hγ).2)
    exact ⟨C,cost,fun γ hγ on=>cover γ (mem_filter.mpr ⟨hγ,on⟩) on⟩
  let C (J : Ideal Ambient) : CutCover :=
    if mem : J∈ini.lost i then Classical.choose (oneCut J mem) else emptyCut
  have spec (J : Ideal Ambient) (mem : J∈ini.lost i) :
      (∀ fee,(C J).cost fee≤dot (weight (cutShape i) fee) (sectionDegree J)) ∧
        ∀ γ∈R.marks,OnMark R.family J γ → γ∈(C J).direct ∨ ∃ Q∈(C J).curves,OnMark R.family Q γ := by
    simpa only [C,dite_eq_left mem] using Classical.choose_spec (oneCut J mem)
  refine ⟨joinCuts (ini.lost i) C,?_,?_⟩
  · intro fee
    exact (joinCuts_cost _ _ _).trans ((sum_le_sum fun J mem => (spec J mem).1 fee).trans_eq (sum_dot _ _))
  · rintro γ hγ ⟨J,mem,on⟩
    rcases (spec J mem).2 γ hγ on with point | ⟨Q,hQ,hmark⟩
    · exact Or.inl (mem_biUnion.mpr ⟨J,mem,point⟩)
    · exact Or.inr ⟨Q,mem_biUnion.mpr ⟨J,mem,hQ⟩,hmark⟩

theorem Initial.retained_or_lost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {J : Ideal Ambient} (mem : J∈ini.parents) :
    J∈ini.final ∨ ∃ i<18,J∈ini.lost i := by
  by_cases h : ∃ i<18,J∈ini.lost i
  · exact Or.inr h
  · have alive : ∀ n≤18,J∈ini.live n := by
      intro n hn
      induction n with
      | zero => exact ini.live_zero.symm ▸ mem
      | succ n ih =>
        by_contra absent
        exact h ⟨n,by omega,mem_sdiff.mpr ⟨ih (by omega),absent⟩⟩
    exact Or.inl (by simpa [Initial.live] using alive 18 le_rfl)

theorem Initial.terminal_surfaces_with_origins {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ∃ S : Finset Surface,(∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      (∀ q∈S,∃ J∈ini.final,q.asIdeal=J.comap K1_14_2.toJet) ∧
      ∀ γ∈R.marks,(∃ J∈ini.final,OnMark R.family J γ) → ∃ q∈S,OnSurface F q γ := by
  let geom (J : ini.final) := ini.kept_geom (mem_filter.mp J.property).1
  let surface (J : ini.final) := surfaceOf J.val (geom J).1.prime
  let S := ini.final.attach.image surface
  refine ⟨S,?_,?_,?_⟩
  · intro q hq
    obtain ⟨J,_,rfl⟩ := mem_image.mp hq
    have hJ := geom J
    exact ⟨parent_of_dual hJ.1 hJ.2.2.1 hJ.2.1,(mem_filter.mp J.property).2⟩
  · intro q hq
    obtain ⟨J,_,rfl⟩:=mem_image.mp hq
    exact ⟨J.val,J.property,rfl⟩
  · rintro γ _ ⟨J,hJ,on⟩
    let q : ini.final := ⟨J,hJ⟩
    refine ⟨surface q,mem_image.mpr ⟨q,mem_attach _ _,rfl⟩,?_⟩
    intro P mem
    rw [←K1_14_2.eval_toJet]
    exact RingHom.mem_ker.mp (on mem)

theorem Initial.terminal_surfaces {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ∃ S : Finset Surface,(∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈R.marks,(∃ J∈ini.final,OnMark R.family J γ) → ∃ q∈S,OnSurface F q γ := by
  obtain ⟨S,geom,_,marks⟩:=ini.terminal_surfaces_with_origins
  exact ⟨S,geom,marks⟩

end Lower6960.Prefix6969SeedOneMain

end
end Merged_R6960MainGeometryProcess

section Merged_R6960MainGeometryBills

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000

namespace Lower6960.Prefix6969SeedOneMain
open Finset Polynomial
open K1 (K)
open K1_14 (Jet atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient)
open K1_14_2_2 (mass mass_mono weight dot CutCover emptyCut)
open P1_7_4 (Mass massQ massQ_mono dotQ pairedCap weightedBill bill_bound)
open Far6969RescueGeometry (Model Family OnMark label_injective beforeCuts)
open Prefix6969Rates (fixedFee fixed_count)
open scoped Classical BigOperators

def initialMass : Mass := fun k=>initialCap k

private abbrev historyTable := suppliedHistory

def history (i : ℕ) : Mass := historyTable.getD i initialMass

theorem history_zero (k : Fin 4) : history 0 k=initialMass k := by
  fin_cases k <;> decide +kernel

theorem history_step (i : Fin 17) (k : Fin 4) :
    let j : Fin 18 := ⟨i.val+1,by have := i.isLt; omega⟩
    history (i.val+1) k =
      min (history i.val k) (pairedCap (freeShape j) (movingShape j) (reserve j) true k) := by
  fin_cases i <;> fin_cases k <;> decide +kernel

theorem Initial.cap_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (n : ℕ) (k : Fin 4) : massQ (ini.kept n) k ≤ initialMass k := by
  exact (Nat.cast_le (α:=ℚ)).mpr ((mass_mono
    ((filter_subset _ _).trans subset_union_right) k).trans (ini.fits k))

theorem Initial.cap_kept {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<18) (k : Fin 4) : massQ (ini.kept i) k≤history i k := by
  induction i with
  | zero => rw [history_zero]; exact ini.cap_initial _ _
  | succ i ih =>
    have hl : i<17 := by omega
    have hstep := history_step ⟨i,hl⟩ k
    dsimp only at hstep
    rw [hstep]
    exact le_min ((massQ_mono (ini.kept_anti (Nat.le_succ i)) k).trans (ih (by omega)))
      (ini.stage_mass ⟨i+1,hi⟩ (Nat.succ_pos _) le_rfl k)

theorem Initial.cap_live {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<18) (k : Fin 4) : massQ (ini.live i) k≤history i k := by
  rw [Initial.live,ite_eq_left hi]
  exact ini.cap_kept hi k

theorem Initial.live_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    {i : ℕ} (hi : i<18) (k : Fin 4) : massQ (ini.live i) k ≤ initialMass k := by
  rw [Initial.live,ite_eq_left hi]
  exact ini.cap_initial _ k

def cutWeight (fee : Fin 3) (i : ℕ) : Mass := fun k=>weight (cutShape i) fee k

def seedLimit : ℚ := weightedBill 18 (cutWeight 0) history

def pointLimit : ℚ := weightedBill 18 (cutWeight 2) (fun _=>initialMass)

def initialSeedLimit : ℕ := (K1.p+1)*initialCap 2+initialCap 3

def contentLimit : ℕ := (K1.p+1)*(freeShape 0).U

def fixedLimit : ℕ :=
  ∑ i : Fin 18, (fixedFee (freeShape i).B (freeShape i).J+fixedFee (movingShape i).B (movingShape i).J)

theorem seed_limit_small : seedLimit < (K1.p : ℚ) := by decide +kernel

theorem Initial.ordinary_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    (R.marks.filter (fun γ=>atX (R.family.scalar γ)∈ini.ordinates)).card ≤ initialCap 0 := by
  apply (card_le_card_of_injOn (fun γ=>atX (R.family.scalar γ))
    (fun _ hγ=>(mem_filter.mp hγ).2) ?_).trans ini.ordinate_cap
  intro γ hγ δ hδ eq
  exact R.family.distinct (mem_filter.mp hγ).1 (mem_filter.mp hδ).1
    (K1_14_3.scalar_atX_injective eq)

theorem Initial.seed_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    (R.marks.filter (fun γ=>ini.seed.Covers (M.label γ))).card ≤ initialSeedLimit := by
  have bound := K1_14_3.seed_count
    (T:=R.marks.filter (fun γ=>ini.seed.Covers (M.label γ))) (label_injective M).injOn ini.seed
    (ini.seed_cap.trans_lt (initial_small 2)) (fun _ hγ=>(mem_filter.mp hγ).2)
  exact bound.trans (Nat.add_le_add (Nat.mul_le_mul_left _ ini.seed_cap) ini.seed_points)

theorem Initial.content_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    (R.marks.filter (fun γ=>graphEval (M.label γ) ini.content=0)).card≤contentLimit := by
  let C : K1_14_3.SeedCover := ⟨ini.content,ini.content_ne,∅⟩
  have bound := K1_14_3.seed_count
    (T:=R.marks.filter (fun γ=>graphEval (M.label γ) ini.content=0)) (label_injective M).injOn C
    (ini.content_cap.trans_lt (free_seed_small 0)) (fun _ hγ=>Or.inl (mem_filter.mp hγ).2)
  exact (by simpa only [C,card_empty,Nat.add_zero] using bound :
    (R.marks.filter (fun γ=>graphEval (M.label γ) ini.content=0)).card≤(K1.p+1)*ini.content.totalDegree)
    |>.trans (Nat.mul_le_mul_left _ ini.content_cap)

theorem Rows.fixed_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt) (hi : M.overhead.toNat≤2411) :
    R.fixedMarks.card≤fixedLimit := by
  calc
    _ ≤ ∑ i : Fin 18, (R.fixedMarksOf (R.fixedFree i).equation ∪ R.fixedMarksOf (R.fixedMoving i).equation).card :=
      card_biUnion_le
    _ ≤ _ := sum_le_sum fun i _=>(card_union_le _ _).trans (Nat.add_le_add
      (Prefix6969Rates.fixed_count R.family hi (free_ode_guard i) _ (R.fixedFree i).equation_caps (filter_subset _ _)
        (fun _ hm=>(mem_filter.mp hm).2))
      (Prefix6969Rates.fixed_count R.family hi (moving_ode_guard i) _ (R.fixedMoving i).equation_caps (filter_subset _ _)
        (fun _ hm=>(mem_filter.mp hm).2)))

structure CutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) where
  cover : ℕ→CutCover
  cost : ∀ i<18,∀ fee,(cover i).cost fee ≤ dot (weight (cutShape i) fee) (mass (ini.lost i))
  covers : ∀ i<18,∀ γ∈R.marks,(∃ J∈ini.lost i,OnMark R.family J γ) →
    γ∈(cover i).direct ∨ ∃ Q∈(cover i).curves,OnMark R.family Q γ

theorem Initial.cutBooks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) : Nonempty (CutBooks ini) := by
  have pick (i : ℕ) : ∃ C : CutCover,i<18 →
      (∀ fee,C.cost fee ≤ dot (weight (cutShape i) fee) (mass (ini.lost i))) ∧
      ∀ γ∈R.marks,(∃ J∈ini.lost i,OnMark R.family J γ) → γ∈C.direct ∨ ∃ Q∈C.curves,OnMark R.family Q γ := by
    by_cases hi : i<18
    · obtain ⟨C,cap,cover⟩ := ini.cutCover noPole residues hi
      exact ⟨C,fun _=>⟨cap,cover⟩⟩
    · exact ⟨emptyCut,fun h=>(hi h).elim⟩
  choose C hC using pick
  exact ⟨⟨C,fun i h=>(hC i h).1,fun i h=>(hC i h).2⟩⟩

theorem CutBooks.costQ {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) {i : ℕ} (hi : i<18) (fee : Fin 3) :
    ((C.cover i).cost fee : ℚ)≤dotQ (cutWeight fee i) (massQ (ini.lost i)) := by
  have bound := (Nat.cast_le (α:=ℚ)).mpr (C.cost i hi fee)
  simpa only [cutWeight,dotQ,dot,massQ,Nat.cast_sum,Nat.cast_mul] using bound

theorem CutBooks.seed_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : (∑ i∈range 18,((C.cover i).cost 0 : ℚ))≤seedLimit :=
  (sum_le_sum fun _ h=>C.costQ (mem_range.mp h) 0).trans
    (bill_bound 18 _ _ ini.live ini.lost (fun _ hi=>ini.next_sub hi) (fun _ _=>subset_rfl)
      (fun _ hi=>ini.cap_live hi))

def CutBooks.pointMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : Finset K := (range 18).biUnion fun i=>(C.cover i).direct

theorem CutBooks.point_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : (C.pointMarks.card : ℚ) ≤ pointLimit := by
  calc
    _ ≤ ∑ i∈range 18,((C.cover i).cost 2 : ℚ) := by
      exact_mod_cast (show C.pointMarks.card ≤ ∑ i∈range 18,(C.cover i).direct.card from card_biUnion_le)
    _ ≤ ∑ i∈range 18,dotQ (cutWeight 2 i) (massQ (ini.lost i)) :=
      sum_le_sum fun i h=>C.costQ (mem_range.mp h) 2
    _ ≤ _ := bill_bound 18 _ _ ini.live ini.lost (fun _ hi=>ini.next_sub hi) (fun _ _=>subset_rfl)
      (fun _ hi=>ini.live_initial hi)

private def Initial.jointLive {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ℕ→Finset (Ideal Ambient)
  | 0 => ini.rankExit∪ini.parents
  | i+1 => ini.live i

private def Initial.jointLost {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) :
    ℕ→Finset (Ideal Ambient)
  | 0 => ini.rankExit
  | i+1 => ini.lost i

/-- The rank exit and the seventeen cut bins spend a single weighted
history, starting from the mass of the initial proper cover. -/
theorem Initial.joint_bill_with_final {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (rank : Mass) (cut : ℕ→Mass) :
    dotQ rank (massQ ini.rankExit) + (∑ i∈range 18,dotQ (cut i) (massQ (ini.lost i))) +
      dotQ (P1_7_4.running (beforeCuts rank cut) 19) (massQ ini.final) ≤
      weightedBill 19 (beforeCuts rank cut) (beforeCuts (initialMass) (history)) := by
  have bill := P1_7_4.bill_bound_with_final 19 (beforeCuts rank cut) (beforeCuts (initialMass) (history))
    ini.jointLive ini.jointLost ?_ ?_ ?_
  · rw [show 19=18+1 by decide,sum_range_succ'] at bill
    have final : ini.jointLive 19 = ini.final := by simp [Initial.jointLive,Initial.live]
    simpa only [beforeCuts,Initial.jointLost,final,add_comm] using bill
  · intro i hi
    cases i with
    | zero => simpa only [Initial.jointLive,ini.live_zero] using
        (subset_union_right : ini.parents⊆ ini.rankExit∪ini.parents)
    | succ i => exact ini.next_sub (by omega)
  · intro i hi
    cases i with
    | zero =>
      intro J mem
      apply mem_sdiff.mpr
      refine ⟨mem_union_left _ mem,?_⟩
      rw [Initial.jointLive,ini.live_zero]
      exact fun h=>(disjoint_left.mp ini.disjoint) mem h
    | succ i => exact subset_rfl
  · intro i hi k
    cases i with
    | zero => exact (Nat.cast_le (α:=ℚ)).mpr (ini.fits k)
    | succ i => exact ini.cap_live (by omega) k


theorem Initial.joint_bill {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R)
    (rank : Mass) (cut : ℕ→Mass) :
    dotQ rank (massQ ini.rankExit) + (∑ i∈range 18,dotQ (cut i) (massQ (ini.lost i))) ≤
      weightedBill 19 (beforeCuts rank cut) (beforeCuts initialMass history) :=
  (le_add_of_nonneg_right (P1_7_4.final_credit_nonneg 19 (beforeCuts rank cut) ini.final)).trans
    (ini.joint_bill_with_final rank cut)

end Lower6960.Prefix6969SeedOneMain

end
end Merged_R6960MainGeometryBills

section Merged_R6960MainGeometryInvoice

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6960.Prefix6969SeedOneMain
open Finset
open K1 (p)
open P1_7_4 (Mass dotQ weightedBill)
open Far6969RescueGeometry (beforeCuts)
open Prefix6969Rates (RateOK curveUnit endpointDegree)
open scoped Classical BigOperators

abbrev degreeRates := suppliedDegreeRates
abbrev heightRates := suppliedHeightRates

def lambda : ℚ := ((262144 : ℚ) / 179730) * endpointDegree
def mu : ℚ := ((262144 - endpointDegree : ℕ) : ℚ) / (179730 - endpointDegree : ℕ)
def tau : ℚ := 1 / 2

def degreeRate (i : ℕ) : ℕ := degreeRates.getD i 0

def heightRate (i : ℕ) : ℕ := heightRates.getD i 0

private def heightTerms (a : ℕ) : List ℚ :=
  (List.range 80).map (fun i : ℕ =>
    let g := i+1
    max 0 (1-(a : ℚ)*(g : ℚ)/((p+1 : ℕ) : ℚ))*curveUnit g)

def heightBound (a : ℕ) : ℚ := (heightTerms a).foldr max 0

private theorem le_max_fold {q : ℚ} {terms : List ℚ} (mem : q∈terms) :
    q ≤ terms.foldr max 0 := by
  induction terms with
  | nil => simp at mem
  | cons a rest ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp mem with eq | h
    · exact eq.symm ▸ le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem height_spec (a g : ℕ) (pos : 0<g) (small : g≤80) :
    max 0 (1-(a : ℚ)*g/((p+1 : ℕ) : ℚ))*curveUnit g≤heightBound a := by
  apply le_max_fold
  unfold heightTerms
  apply List.mem_map.mpr
  refine ⟨g-1,List.mem_range.mpr (by omega),?_⟩
  dsimp only
  rw [Nat.sub_add_cancel (by omega : 1≤g)]

private theorem checked_rates (i : Fin 18) :
    ((p+1 : ℕ) : ℚ)/81 ≤ (degreeRate i.val : ℚ) ∧
      min seedLimit (dotQ (cutWeight 0 i.val) (history i.val)) ≤ (degreeRate i.val : ℚ) ∧
      heightBound (degreeRate i.val) ≤ (heightRate i.val : ℚ) := by
  fin_cases i <;> decide +kernel

theorem rate_spec {i : ℕ} (hi : i<18) :
    RateOK (degreeRate i) (heightRate i) ∧
      min seedLimit (dotQ (cutWeight 0 i) (history i)) ≤ degreeRate i := by
  obtain ⟨base,degree,height⟩ := checked_rates ⟨i,hi⟩
  exact ⟨⟨base,Nat.cast_nonneg _,fun g hp hg=>(height_spec _ g hp hg).trans height⟩,degree⟩

def rankB : ℕ := initialCap 2+2

def rankJ : ℕ := initialCap 1+1

def pivot : ℚ := min ((3/5 : ℚ) * rankJ) (tau*rankB)

def rankWeight : Mass :=
  ![0,4*lambda*rankB*tau+mu-4*lambda*pivot,4*lambda*rankJ*(1-tau)+rankB,0]

def rankRound : ℚ := rankWeight 1+2*rankWeight 2+2*lambda*pivot^2+1

def lossWeight (i : ℕ) : Mass :=
  fun k=>(degreeRate i : ℚ)*cutWeight 0 i k+(heightRate i : ℚ)*cutWeight 1 i k

def lossLimit : ℚ :=
  weightedBill 19 (beforeCuts rankWeight lossWeight) (beforeCuts initialMass history)+seedLimit+rankRound

def mainFee : ℕ := lossLimit.ceil.toNat+pointLimit.ceil.toNat+initialSeedLimit+initialCap 0+
  fixedLimit+contentLimit

theorem main_fee_exact : mainFee = prefixCap := by decide +kernel

theorem retained_credit_guard (k : Fin 4) :
    (retainedCredit k : ℚ) ≤ P1_7_4.running (beforeCuts rankWeight lossWeight) 19 k := by
  fin_cases k <;> decide +kernel

theorem rank_guard : rankB<p ∧ 0≤rankWeight 1 ∧ 0≤rankWeight 2 := by decide +kernel

end Lower6960.Prefix6969SeedOneMain

end
end Merged_R6960MainGeometryInvoice
end Z6969Source0773

-- Source: Research6969.PrefixSeedOneMain
section Z6969Source0774
set_option autoImplicit true
set_option Elab.async false

section Merged_R6960MainGeometryFee
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 2200000
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false
namespace Lower6960.Prefix6969SeedOneMain
open Finset Polynomial
open K1 (K p)
open K1_14 (Jet jetAt atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient ODE)
open K1_14_2_2 (mass mass_mono ODECaps)
open K1_14_3 (Surface Parent)
open P1_7_4 (ODEGuard Mass massQ dotQ dotQ_mono_mass massQ_mono dotQ_scale_add)
open HighCore82268JointRank (fixed_fee_linear)
open Far6969RescueGeometry (Model Family OnMark OnSurface word beforeCuts)
open Prefix6969Rates (curveMarks mem_curveMarks curve_tariff rated_curve_count fixedFee fixed_count
  persistentTotal persistentTop siteRatio density endpointDegree)
open P1_7_4_3 (mix)
open scoped Classical BigOperators
theorem fixedFee_eq (B J : ℕ) :
    fixedFee B J = (mix B J (mu+2*lambda*(B-1 : ℕ))
      (min (mu+2*lambda*(B-1 : ℕ)) (lambda*(2*J-1 : ℕ)))).ceil.toNat+B^2 := by
  have he : 2*density*(endpointDegree : ℚ)=2*lambda := by unfold lambda density; ring
  have hl : density*(endpointDegree : ℚ)=lambda := rfl
  have hm : siteRatio endpointDegree=mu := rfl
  unfold fixedFee persistentTop persistentTotal
  rw [he,hl,hm]
def Initial.rankMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>∃ J∈ini.rankExit,OnMark R.family J γ)
theorem Initial.rank_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) (hi : M.overhead.toNat≤2411) :
    (ini.rankMarks.card : ℚ)≤dotQ rankWeight (massQ ini.rankExit)+rankRound := by
  let S := ini.rankExit
  let B := max 2 (mass S 2)
  let J := max 1 (min (mass S 1) B)
  obtain ⟨E,caps,roots⟩ := ini.rank_ode
  have mass_cap (k : Fin 4) : mass S k ≤ initialCap k :=
    (mass_mono (subset_union_left : S⊆ini.rankExit∪ini.parents) k).trans (ini.fits k)
  have hBm : B≤mass S 2+2 := max_le (by omega) (by omega)
  have hJm : J≤mass S 1+1 := max_le (by omega) ((min_le_left _ _).trans (by omega))
  have hB : B≤rankB := hBm.trans (Nat.add_le_add_right (mass_cap 2) 2)
  have hJ : J≤rankJ := hJm.trans (Nat.add_le_add_right (mass_cap 1) 1)
  have hB2 : 2≤B := le_max_left _ _
  have hJ1 : 1≤J := le_max_left _ _
  have hJB : J≤B := max_le (by omega) (min_le_right _ _)
  have degree : E.natDegree≤B := by
    have top : E.coeff E.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr caps.1
    have hn : (E.coeff E.natDegree).coeff (E.coeff E.natDegree).natDegree≠0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr top
    exact (Nat.le_add_left _ _).trans ((caps.2.2 _ _ hn).trans (le_max_right _ _))
  have ocaps : ODECaps E B J := ⟨caps.1,(le_min caps.2.1 degree).trans (le_max_right _ _),
    fun j i hz => (caps.2.2 j i hz).trans (le_max_right _ _)⟩
  obtain ⟨small,cJ,cB⟩ := rank_guard
  have guard : ODEGuard B J := ⟨hB2,hJ1,hJB,hB.trans_lt small⟩
  have count : ini.rankMarks.card≤fixedFee B J :=
    Prefix6969Rates.fixed_count R.family hi guard E ocaps (filter_subset _ _)
      (fun γ mem => roots γ (mem_filter.mp mem).1 (mem_filter.mp mem).2)
  have lin := fixed_fee_linear lambda mu tau pivot (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hJB hB hJ
  have fee : (fixedFee B J : ℚ) ≤
      rankWeight 1 * J + rankWeight 2 * B + 2*lambda*pivot^2+1 := by
    rw [fixedFee_eq]
    exact lin
  have hJq : (J : ℚ)≤(mass S 1 : ℚ)+1 := by exact_mod_cast hJm
  have hBq : (B : ℚ)≤(mass S 2 : ℚ)+2 := by exact_mod_cast hBm
  have hjfee := mul_le_mul_of_nonneg_left hJq cJ
  have hbfee := mul_le_mul_of_nonneg_left hBq cB
  have hdot : dotQ rankWeight (massQ ini.rankExit) =
      rankWeight 1 * (mass S 1 : ℚ)+rankWeight 2 * (mass S 2 : ℚ) := by
    simp [dotQ,rankWeight,massQ,Fin.sum_univ_succ,S]
  refine (Nat.cast_le.mpr count).trans (fee.trans ?_)
  rw [hdot,rankRound]
  linarith only [hjfee,hbfee]
private theorem card_round {a : ℕ} {q : ℚ} (bound : (a : ℚ)≤q) : a≤q.ceil.toNat := by
  have ceil_cast : (q.ceil : ℚ) ≤ (q.ceil.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat q.ceil
  exact_mod_cast bound.trans (Rat.le_ceil.trans ceil_cast)
theorem CutBooks.curve_bin_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) (hiM : M.overhead.toNat≤2411) {i : ℕ} (hi : i<18) :
    ((curveMarks R.family (C.cover i)).card : ℚ)≤
      dotQ (lossWeight i) (massQ (ini.lost i))+((C.cover i).cost 0 : ℚ) := by
  have global : ((C.cover i).cost 0 : ℚ)≤seedLimit :=
    (single_le_sum (fun j _=>Nat.cast_nonneg (α:=ℚ) ((C.cover j).cost 0))
      (mem_range.mpr hi)).trans C.seed_bill
  have localCap : ((C.cover i).cost 0 : ℚ)≤ dotQ (cutWeight 0 i) (history i) :=
    (C.costQ hi 0).trans (dotQ_mono_mass (fun _=>Nat.cast_nonneg _)
      (fun k=>(massQ_mono sdiff_subset k).trans (ini.cap_live hi k)))
  have prime : (C.cover i).cost 0 < p := by exact_mod_cast global.trans_lt seed_limit_small
  obtain ⟨ok,degree⟩ := rate_spec hi
  have count := rated_curve_count R.family (curve_tariff R.family hiM) ok (C.cover i)
    global ((min_le_min le_rfl localCap).trans degree) prime
  calc
    _ ≤ (degreeRate i : ℚ)*((C.cover i).cost 0 : ℚ) +
          (heightRate i : ℚ)*((C.cover i).cost 1 : ℚ)+((C.cover i).cost 0 : ℚ) := count
    _ ≤ (degreeRate i : ℚ)*dotQ (cutWeight 0 i) (massQ (ini.lost i)) +
          (heightRate i : ℚ)*dotQ (cutWeight 1 i) (massQ (ini.lost i)) +
          ((C.cover i).cost 0 : ℚ) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left (C.costQ hi 0) (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left (C.costQ hi 1) (Nat.cast_nonneg _))) le_rfl
    _ = _ := by rw [dotQ_scale_add]; rfl
def CutBooks.lossMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R} (C : CutBooks ini) :
    Finset K := ini.rankMarks ∪ (range 18).biUnion (fun i=>curveMarks R.family (C.cover i))
/-- The retained weight is charged on every component of the terminal parent mass. -/
def retainedCharge (S : Finset (Ideal Ambient)) : ℕ :=
  ∑ k : Fin 4, retainedCredit k * mass S k

theorem retainedCharge_cast_le (S : Finset (Ideal Ambient)) :
    (retainedCharge S : ℚ) ≤
      dotQ (P1_7_4.running (beforeCuts rankWeight lossWeight) 19) (massQ S) := by
  unfold retainedCharge dotQ massQ
  push_cast
  exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right
    (retained_credit_guard k) (Nat.cast_nonneg _))

theorem CutBooks.loss_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) (hi : M.overhead.toNat≤2411) : C.lossMarks.card + retainedCharge ini.final ≤ lossLimit.ceil.toNat := by
  apply card_round
  have cum : (C.lossMarks.card : ℚ) ≤ (ini.rankMarks.card : ℚ) +
      ∑ i∈range 18,((curveMarks R.family (C.cover i)).card : ℚ) := by
    exact_mod_cast (show C.lossMarks.card ≤ ini.rankMarks.card +
      ∑ i∈range 18,(curveMarks R.family (C.cover i)).card from
        (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  have sum_cuts := sum_le_sum (fun _ mem=>C.curve_bin_count hi (mem_range.mp mem))
    (s:=range 18)
  rw [sum_add_distrib] at sum_cuts
  have both := add_le_add (ini.rank_count hi) sum_cuts
  have joint := ini.joint_bill_with_final rankWeight lossWeight
  have seed := C.seed_bill
  have total := cum.trans both
  have retained := retainedCharge_cast_le ini.final
  push_cast
  unfold lossLimit
  linarith only [total, joint, seed, retained]
def Initial.seedMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>ini.seed.Covers (M.label γ))
def Initial.ordinateMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>atX (R.family.scalar γ)∈ini.ordinates)
def Initial.contentMarks {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} (ini : Initial R) : Finset K :=
  R.marks.filter (fun γ=>graphEval (M.label γ) ini.content=0)
def CutBooks.paid {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) : Finset K :=
  (C.lossMarks ∪ C.pointMarks) ∪ (ini.seedMarks ∪ ini.ordinateMarks) ∪ (R.fixedMarks ∪ ini.contentMarks)
theorem CutBooks.paid_count {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {R : Rows F Crt} {ini : Initial R}
    (C : CutBooks ini) (hi : M.overhead.toNat≤2411) : C.paid.card + retainedCharge ini.final ≤ mainFee := by
  have combined := card_union_le
    ((C.lossMarks ∪ C.pointMarks) ∪ (ini.seedMarks ∪ ini.ordinateMarks)) (R.fixedMarks ∪ ini.contentMarks)
  have left := card_union_le (C.lossMarks ∪ C.pointMarks) (ini.seedMarks ∪ ini.ordinateMarks)
  have cuts := card_union_le C.lossMarks C.pointMarks
  have low := card_union_le ini.seedMarks ini.ordinateMarks
  have fixed := card_union_le R.fixedMarks ini.contentMarks
  have loss := C.loss_count hi
  have points := card_round C.point_bill
  have seeds : ini.seedMarks.card ≤ initialSeedLimit := ini.seed_count
  have ordinates : ini.ordinateMarks.card ≤ initialCap 0 := ini.ordinary_count
  have content : ini.contentMarks.card ≤ contentLimit := ini.content_count
  have fixedCard := R.fixed_count hi
  unfold mainFee CutBooks.paid
  omega
theorem Rows.main_prefix {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (hi : M.overhead.toNat≤2411) (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ (ini : Initial R) (C : CutBooks ini) (S : Finset Surface),
      C.paid.card + retainedCharge ini.final ≤ prefixCap ∧
      (∀ k, massQ ini.final k ≤ history 17 k) ∧
      (∀ q∈S, Parent q ∧ SurfacePass Crt (word M) q) ∧
      (∀ q∈S, ∃ J∈ini.final, q.asIdeal = J.comap K1_14_2.toJet) ∧
      ∀ γ∈R.marks, γ∈C.paid ∨ ∃ q∈S, OnSurface F q γ := by
  obtain ⟨ini⟩ := R.initial_cover
  obtain ⟨C⟩ := ini.cutBooks noPole residues
  obtain ⟨S, geom, origin, surface⟩ := ini.terminal_surfaces_with_origins
  refine ⟨ini, C, S, main_fee_exact ▸ C.paid_count hi, ?_, geom, origin, ?_⟩
  intro k
  exact (massQ_mono (filter_subset _ _) k).trans (ini.cap_kept (by decide) k)
  intro γ hγ
  rcases ini.covers γ hγ with fixed | content | seed | ord | rank | ⟨J,mem,on⟩
  · exact Or.inl (mem_union_right _ (mem_union_left _ fixed))
  · exact Or.inl (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hγ,content⟩)))
  · exact Or.inl (mem_union_left _ (mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hγ,seed⟩))))
  · exact Or.inl (mem_union_left _ (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hγ,ord⟩))))
  · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _
      (mem_union_left _ (mem_filter.mpr ⟨hγ,rank⟩)))))
  · rcases ini.retained_or_lost mem with final | ⟨i,hi,lost⟩
    · exact Or.inr (surface γ hγ ⟨J,final,on⟩)
    · rcases C.covers i hi γ hγ ⟨J,lost,on⟩ with point | ⟨Q,hQ,hmark⟩
      · have mark : γ∈C.pointMarks := mem_biUnion.mpr ⟨i,mem_range.mpr hi,point⟩
        exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_right _ mark)))
      · have mark : γ∈(range 18).biUnion (fun i=>curveMarks R.family (C.cover i)) :=
          mem_biUnion.mpr ⟨i,mem_range.mpr hi,mem_curveMarks (F:=R.family) hγ hQ hmark⟩
        exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ mark))))
/-- Construct the actual wide prefix from the model's CRT data and the verified banks. -/
theorem main_prefix {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : Research6966.HelperPhysicalModel.Model Crt G)
    (outer : PrefixRows.Common
      (K1_14_1.evaluated Crt (word M) Prefix6969Helper.helperBank.shape
        (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ K1_14_2_2_2_1.jetDegree G)
    (seed : 1 ≤ K1_14_2_2_2_1.seedDegree G)
    (physical : 308385 ≤ Research6966.RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ (R : Rows F Crt) (ini : Initial R) (C : CutBooks ini) (S : Finset Surface),
      R.out.exception = G ∧ C.paid.card + retainedCharge ini.final ≤ prefixCap ∧
      (∀ k, massQ ini.final k ≤ history 17 k) ∧
      (∀ q∈S, Parent q ∧ SurfacePass Crt (word M) q) ∧
      (∀ q∈S, ∃ J∈ini.final, q.asIdeal = J.comap K1_14_2.toJet) ∧
      ∀ γ∈R.marks, γ∈C.paid ∨ ∃ q∈S, OnSurface F q γ := by
  obtain ⟨R, identity⟩ := rows F Crt lo hi noPole residues phys outer degree seed physical
  obtain ⟨ini, C, S, paid, massCap, regular, origins, covered⟩ :=
    R.main_prefix hi noPole residues
  exact ⟨R, ini, C, S, identity, paid, massCap, regular, origins, covered⟩

end Lower6960.Prefix6969SeedOneMain

end
end Merged_R6960MainGeometryFee
end Z6969Source0774

-- Source: Research6969.PrefixRescueSeedOneData
section Z6969Source0775
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000

namespace Lower6960.Prefix6969RescueSeedOne

open Research6969.TransitionBanks
open K1_14 (Shape)
open Lower6960.Prefix6969Rescue
open Lower6960.HelperSource (WidthGuard)

def bank (i : Fin 11) : P1_7.Bank := ![bank245 164470, bank245 182926, bank245 206037, bank251 220122, bank252 234092, bank252 292397, bank270 364135, bank303 321892, bank315 365477, bank315 421074, bank302 410737] i
def reserve (i : Fin 11) : ℕ := ![0, 1, 2, 3, 4, 6, 10, 10, 13, 16, 13] i

def plan : Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0, 2, 1, 1⟩
  bank := bank
  reserve := reserve
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 308385
  seedFloor := 1

def request (i : Fin 11) : Research6969.PhysicalWindow.Request :=
  ⟨bank i, reserve i, 2, 1, 308385, 1⟩

theorem rank_ok (i : Fin 11) : P3_7_1.BankOK (bank i) := by
  fin_cases i
  · exact rank245 164470
  · exact rank245 182926
  · exact rank245 206037
  · exact rank251 220122
  · exact rank252 234092
  · exact rank252 292397
  · exact rank270 364135
  · exact rank303 321892
  · exact rank315 365477
  · exact rank315 421074
  · exact rank302 410737

theorem reserve_fit (i : Fin 11) : 2 * reserve i ≤ (bank i).shape.B := by
  fin_cases i <;> decide +kernel

theorem seed_small (i : Fin 11) : (bank i).shape.U < K1.p := by
  fin_cases i <;> decide +kernel

theorem narrow (i : Fin 11) : (bank i).shape.J < 131071 - 2411 := by
  fin_cases i <;> decide +kernel

theorem width_first (i : Fin 11) : WidthGuard (bank i) 179730 2314 (reserve i) := by
  unfold WidthGuard
  fin_cases i <;> decide +kernel

end Lower6960.Prefix6969RescueSeedOne
end Z6969Source0775

-- Source: Research6969.PrefixRescueSeedOne
section Z6969Source0776
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000

namespace Lower6960.Prefix6969RescueSeedOne
noncomputable section

open Research6969.PhysicalWindow
open Research6969.PhysicalCatalogue
open Research6966
open Lower6960.Prefix6969Rescue
open Lower6960.Far6969RescueGeometry (Model Family)
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (UsesSeed)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)

theorem covers (i : Fin 11) : ∃ ends, Cover (Triangular (request i)) 2411 2314 ends := by
  fin_cases i
  · exact ⟨_, cover629⟩
  · exact ⟨_, cover630⟩
  · exact ⟨_, cover631⟩
  · exact ⟨_, cover632⟩
  · exact ⟨_, cover633⟩
  · exact ⟨_, cover634⟩
  · exact ⟨_, cover635⟩
  · exact ⟨_, cover636⟩
  · exact ⟨_, cover638⟩
  · exact ⟨_, cover639⟩
  · exact ⟨_, cover637⟩

theorem ready {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2411) : plan.Ready h := by
  refine ⟨by omega, hi.trans (by decide), rank_ok, seed_small, ?_, ?_⟩
  · intro i
    exact Lower6960.HelperSource.width_at_height (bank i) 179730 2314 h (reserve i)
      lo (hi.trans (by decide)) (reserve_fit i) (width_first i)
  · intro i
    obtain ⟨_, cover⟩ := covers i
    obtain ⟨left, right, hlo, hhi, rmax, check⟩ := covered cover lo hi
    have nr := (narrow i).trans_le (Nat.sub_le_sub_left rmax 131071)
    exact triangle_positive (request i) (by omega) hlo hhi nr (show 0 < (1 : ℕ) by decide) check

theorem prepare {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (irr : Irreducible G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G plan.primeShape)
    (degree : 2 ≤ jetDegree G) (seed : 1 ≤ seedDegree G)
    (physical : 308385 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (Run F Crt G plan) :=
  Prefix6969Rescue.prepare F Crt plan (ready lo hi) noPole residues phys irr
    (by omega) seeded caps degree (by change 1 ≤ G.natDegree; omega) physical seed

end
end Lower6960.Prefix6969RescueSeedOne
end Z6969Source0776

-- Source: Research6969.PrefixRescueSeedOneInvoice
section Z6969Source0777
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969RescueSeedOne
noncomputable section

open Lower6960.Prefix6969Rescue
open Lower6960.Prefix6969Rescue.Invoice
open Lower6960.Far6969RescueGeometry (Model Family OnMark beforeCuts)
open K1 (K p)
open K1_14 (Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2_2 (RowCaps)
open Finset

abbrev credit : Fin 4 → ℕ := ![206646633540,207926677348,462874133,462877700]

theorem exact_fee :
    eventFee plan plan.count plan.normalShape plan.history 2 1 1 (4/5) =
      34856458124440570 := by decide +kernel

theorem credit_fit (k : Fin 4) :
    (credit k : ℚ) ≤ eventRunning plan plan.count plan.normalShape 2 1 1 (4/5) k := by
  fin_cases k <;> decide +kernel

theorem rank_small : rankB plan < p := by decide +kernel

theorem invoice {u del} {M : Model u del} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet}
    (R : Run F Crt G plan)
    (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    (prime : Prime G) (slope : G.natDegree = 1) (caps : RowCaps G (graphShape 2 1))
    (roots : ∀ γ∈Γ, jetAt G (M.label γ) (F.scalar γ) = 0) :
    ∃ B : Book R, B.final = R.terminal ∧
      (paid B).card + charge B credit ≤ 34856458124440570 ∧
      ∀ γ∈Γ, γ∈paid B ∨ ∃ J∈B.final, OnMark F J γ := by
  obtain ⟨B, steps, final, shape, capacity⟩ := Book.normal R noPole residues
  have fee' := eventFee_eq B 2 1 1 (4/5)
  rw [steps, shape, capacity, exact_fee] at fee'
  have fit (k : Fin 4) : (credit k : ℚ) ≤
      P1_7_4.running (beforeCuts (rankWeight plan 1 (4/5)) (lossWeight B 2 1)) (B.steps+1) k := by
    rw [eventRunning_eq B 2 1 1 (4/5), steps, shape]
    exact credit_fit k
  refine ⟨B, final, ?_, fun γ mem => paid_cover B mem (roots γ mem)⟩
  rw [← fee']
  exact paid_count B (by decide : 2 ≤ 2) (by decide : 0 < 1) prime slope caps
    (by decide) hi roots (by decide) le_rfl rank_small credit fit

end
end Lower6960.Prefix6969RescueSeedOne
end Z6969Source0777

-- Source: Research6969.PrefixSeedOnePaired
section Z6969Source0778
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace Lower6960.Prefix6969SeedOnePaired
noncomputable section

open Finset Polynomial
open K1 (K)
open K1_14 (Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues evaluated nodeL)
open K1_14_2 (Ambient toJet UsesSeed)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (Surface Parent)
open P1_7_4 (massQ Mass)
open Far6969RescueGeometry (Model Family word OnSurface)
open Research6966
open scoped Classical

def zeroMarks {u del} {M : Model u del} {Γ} (F : Family M Γ) (G : Jet) : Finset K :=
  Γ.filter (fun γ => jetAt G (M.label γ) (F.scalar γ) = 0)

def zeroFamily {u del} {M : Model u del} {Γ} (F : Family M Γ) (G : Jet) :
    Family M (zeroMarks F G) :=
  ⟨F.scalar, fun γ hγ => F.mark γ (mem_filter.mp hγ).1, F.distinct.mono (filter_subset _ _)⟩

abbrev mainCap : Mass := ![459151/1369, 7533960/1369, 1724375/36, 167540275/729]
abbrev rescueCap : Mass := ![2706/7, 24839, 847660/17, 421074/17]

theorem main_cap (k : Fin 4) : Prefix6969SeedOneMain.history 17 k = mainCap k := by
  fin_cases k <;> decide +kernel

theorem rescue_cap (k : Fin 4) :
    Prefix6969RescueSeedOne.plan.history (Prefix6969RescueSeedOne.plan.count - 1) k = rescueCap k := by
  fin_cases k <;> decide +kernel

/-- The actual seed-one head and rescue partition the original marks and charge their two full credit vectors. -/
theorem paired {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G)
    (caps : RowCaps G (Prefix6969Rescue.graphShape 2 1))
    (outer : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 1 ≤ seedDegree G)
    (floor : 308385 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ (R : Prefix6969SeedOneMain.Rows F Crt) (I : Prefix6969SeedOneMain.Initial R)
      (Q : Prefix6969Rescue.Run (zeroFamily F G) Crt G Prefix6969RescueSeedOne.plan)
      (B : Prefix6969Rescue.Book Q) (paid : Finset K) (A S : Finset Surface),
      B.final = Q.terminal ∧
      paid.card + Prefix6969SeedOneMain.retainedCharge I.final +
        Prefix6969Rescue.Invoice.charge B Prefix6969RescueSeedOne.credit ≤ 240643065473743369 ∧
      (∀ k, massQ I.final k ≤ mainCap k) ∧
      (∀ k, massQ B.final k ≤ rescueCap k) ∧
      (∀ q∈A, Parent q ∧ Prefix6969SeedOneMain.SurfacePass Crt (word M) q) ∧
      (∀ q∈A, ∃ J∈I.final, q.asIdeal = J.comap toJet) ∧
      (∀ q∈S, Parent q ∧ Prefix6969Wide.SurfacePass Crt (word M) q ∧
        G∈q.asIdeal ∧ ∃ J∈B.final, q.asIdeal = J.comap toJet) ∧
      ∀ γ∈Γ, γ∈paid ∨ (jetAt G (M.label γ) (F.scalar γ) ≠ 0 ∧
        ∃ q∈A, OnSurface F q γ) ∨
        (jetAt G (M.label γ) (F.scalar γ) = 0 ∧
          Prefix6969Rescue.regular G (M.label γ) (F.scalar γ) ∧ ∃ q∈S, OnSurface F q γ) := by
  obtain ⟨R, I, C, A, identity, mainCount, mainMass, mainGeom, mainOrigin, mainCover⟩ :=
    Prefix6969SeedOneMain.main_prefix F Crt lo hi noPole residues phys outer degree seed floor
  have subRes : ∀ γ∈zeroMarks F G, MarkResidues D (M.label γ) ((zeroFamily F G).scalar γ) :=
    fun γ hγ => residues γ (mem_filter.mp hγ).1
  have roots : ∀ γ∈zeroMarks F G, jetAt G (M.label γ) ((zeroFamily F G).scalar γ) = 0 :=
    fun γ hγ => (mem_filter.mp hγ).2
  obtain ⟨Q⟩ := Prefix6969RescueSeedOne.prepare (zeroFamily F G) Crt lo hi noPole subRes
    phys prime.irreducible slope seeded caps degree seed floor
  obtain ⟨B, bend, rescueCount, _⟩ :=
    Prefix6969RescueSeedOne.invoice Q hi noPole subRes prime slope caps roots
  obtain ⟨S, rescueGeom, rescueSurface⟩ := Prefix6969Rescue.Invoice.Book.surfaces B
  refine ⟨R, I, Q, B, C.paid ∪ Prefix6969Rescue.Invoice.paid B, A, S, bend,
    ?_, ?_, ?_, mainGeom, mainOrigin, ?_, ?_⟩
  · have union := card_union_le C.paid (Prefix6969Rescue.Invoice.paid B)
    change C.paid.card + Prefix6969SeedOneMain.retainedCharge I.final ≤ 205786607349302799 at mainCount
    omega
  · intro k; rw [← main_cap]; exact mainMass k
  · intro k; rw [bend, ← rescue_cap]; exact Prefix6969Rescue.Invoice.Run.mass_terminal Q k
  · intro q hq
    obtain ⟨parent, J, mem, origin⟩ := rescueGeom q hq
    obtain ⟨pass, inIdeal⟩ := Prefix6969Rescue.Invoice.Book.terminal_parent B bend mem origin
    exact ⟨parent, pass, inIdeal, J, mem, origin⟩
  · intro γ hγ
    by_cases root : jetAt G (M.label γ) (F.scalar γ) = 0
    · have inZero : γ∈zeroMarks F G := mem_filter.mpr ⟨hγ, root⟩
      rcases Prefix6969Rescue.Invoice.Book.paid_or_regular B inZero (roots γ inZero) with paid | ⟨reg, on⟩
      · exact Or.inl (mem_union_right _ paid)
      · exact Or.inr (Or.inr ⟨root, reg, rescueSurface γ inZero on⟩)
    · have inMain : γ∈R.marks := mem_filter.mpr ⟨hγ, by simpa only [identity] using root⟩
      rcases mainCover γ inMain with paid | on
      · exact Or.inl (mem_union_left _ paid)
      · exact Or.inr (Or.inl ⟨root, on⟩)


end
end Lower6960.Prefix6969SeedOnePaired
end Z6969Source0778

-- Source: Research6969.TransitionPacket
section Z6969Source0779
set_option autoImplicit true
namespace Research6969.TransitionPacket
noncomputable section
open Finset Polynomial
open K1 (K I p)
open K1_14 (Jet Equation Seeds atX jetAt)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2 (Ambient toJet UsesSeed)
open K1_14_2_2 (Active RowCaps mass)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (Surface ProjectedProduct Parent SeedField)
open Lower6960
open Far6969RescueGeometry (Model Family word OnSurface)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open NonlinearMarkRows (evaluate)
open scoped Classical Differential
set_option maxRecDepth 10000
set_option maxHeartbeats 2300000

/-- The data shared by the conditioned main packet and the regular rescue
packet after paying both prefixes. The witnesses stay attached to their
actual parent surfaces and retain all four component masses. -/
structure Pair {u del} {M:Model u del} {Γ} (F:Family M Γ) {D:PoleData M.overhead.toNat}
    (Crt:CRTLift D) (H:Jet) (m r:JointLedger.Book) where
  paid:Finset K
  main:Finset Surface
  rescue:Finset Surface
  aSrc:Finset (Ideal Ambient)
  bSrc:Finset (Ideal Ambient)
  mainActive:∀Q∈aSrc,Active Q
  rescueActive:∀Q∈bSrc,Active Q
  mainGeo:∀q∈main,Parent q ∧ TerminalBanks.Pass Crt (word M) 179730 SpreadCatalogue.shape q ∧ H∉q.asIdeal
  rescueGeo:∀q∈rescue,Parent q ∧ TerminalBanks.Pass Crt (word M) 179730 SpreadCatalogue.shape q ∧ H∈q.asIdeal
  mainOrigin:∀q∈main,∃Q∈aSrc,q.asIdeal=Q.comap toJet
  rescueOrigin:∀q∈rescue,∃Q∈bSrc,q.asIdeal=Q.comap toJet
  wm:Fin 4→ℕ
  wr:Fin 4→ℕ
  mainOrd:m.ordinateCredit=wm 0
  mainSeed:m.seedCredit=wm 1+wm 2
  rescueOrd:r.ordinateCredit=wr 0
  rescueSeed:r.seedCredit=wr 1+wr 2
  bill:paid.card+(∑k,wm k*mass aSrc k)+(∑k,wr k*mass bSrc k)≤m.fee+r.fee
  boundsM:mass aSrc 1≤m.seedMass
  boundsR:mass bSrc 1≤r.seedMass
  mainGrade:ℕ
  rescueGrade:ℕ
  mainDegreeCap:mass aSrc 0≤mainGrade
  rescueDegreeCap:mass bSrc 0≤rescueGrade
  cover:∀z∈Γ,z∈paid ∨
    (jetAt H (M.label z) (F.scalar z)≠0 ∧ ∃q∈main,OnSurface F q z) ∨
    (jetAt H (M.label z) (F.scalar z)=0 ∧ Prefix6969Rescue.regular H (M.label z) (F.scalar z) ∧ ∃q∈rescue,OnSurface F q z)

theorem of_seed_one {u del} {M:Model u del} {Γ} (F:Family M Γ)
    {D:PoleData M.overhead.toNat} (Crt:CRTLift D)
    (lo:2314≤M.overhead.toNat) (hi:M.overhead.toNat≤2411)
    (noPole:∀j i,(D.block j).eval (nodeL i)≠0)
    (residues:∀ z∈Γ,MarkResidues D (M.label z) (F.scalar z))
    {H:Jet} (physical:HelperPhysicalModel.Model Crt H) (prime:Prime H)
    (slope:H.natDegree=1) (seeded:UsesSeed H) (caps:RowCaps H (Prefix6969Rescue.graphShape 2 1))
    (outer:PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) H) (degree:2≤jetDegree H) (seed:1≤seedDegree H)
    (floor:308385≤RawPhysicalDegree.weight (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) physical.raw) :
    Nonempty (Pair F Crt H SmallCertificates.primary1 SmallCertificates.rescue1) := by
  obtain ⟨R,J,Q,B,paid,S,T,_,pay,ms,rs,mg,mo,rg,covered⟩:=Prefix6969SeedOnePaired.paired F Crt lo hi noPole residues
    physical prime slope seeded caps outer degree seed floor
  have ma (P) (hp:P∈J.final):Active P:=(J.kept_geom (mem_filter.mp hp).1).1
  have ra (P) (hp:P∈B.final):Active P:=(Q.parent_geom (Prefix6969Rescue.Invoice.Book.final_initial B hp)).1
  have mc:=ms 1
  have rc:=rs 1
  change (mass J.final 1:ℚ)≤7533960/1369 at mc
  change (mass B.final 1:ℚ)≤24839 at rc
  have bound:mass J.final 1≤5503:=Nat.le_of_lt_succ (by exact_mod_cast mc.trans_lt (by norm_num: (7533960:ℚ)/1369<5504))
  have mgrade:=ms 0
  have rgrade:=rs 0
  change (mass J.final 0:ℚ)≤459151/1369 at mgrade
  change (mass B.final 0:ℚ)≤2706/7 at rgrade
  have cm:mass J.final 0≤335:=Nat.le_of_lt_succ (by exact_mod_cast mgrade.trans_lt (by norm_num:(459151:ℚ)/1369<336))
  have cr:mass B.final 0≤386:=Nat.le_of_lt_succ (by exact_mod_cast rgrade.trans_lt (by norm_num:(2706:ℚ)/7<387))
  classical
  let keep:=S.filter fun q=>H∉q.asIdeal
  have relevant q (h:q∈keep):Parent q ∧ TerminalBanks.Pass Crt (word M) 179730 SpreadCatalogue.shape q ∧ H∉q.asIdeal:=
    ⟨(mg q (mem_filter.mp h).1).1,(mg q (mem_filter.mp h).1).2,(mem_filter.mp h).2⟩
  refine ⟨⟨paid,keep,T,J.final,B.final,ma,ra,relevant,fun q h=>⟨(rg q h).1,(rg q h).2.1,(rg q h).2.2.1⟩,
    fun q h=>mo q (mem_filter.mp h).1,
    fun q h=>(rg q h).2.2.2,Prefix6969SeedOneMain.retainedCredit,Prefix6969RescueSeedOne.credit,
    rfl,rfl,rfl,rfl,pay,bound,?_,335,386,cm,cr,?_⟩⟩
  · exact_mod_cast rc
  · intro z hz
    rcases covered z hz with taken|⟨miss,q,sq,on⟩|other
    · exact Or.inl taken
    · exact Or.inr (Or.inl ⟨miss,q,mem_filter.mpr ⟨sq,fun owns=>miss (on _ owns)⟩,on⟩)
    · exact Or.inr (Or.inr other)

theorem Pair.reduce {u del} {M:Model u del} {Γ} {F:Family M Γ} {D:PoleData M.overhead.toNat}
    {Crt:CRTLift D} {H:Jet} {m r} (P:Pair F Crt H m r)
    (lo:2314≤M.overhead.toNat) (hi:M.overhead.toNat≤2557) {d U limit:ℕ}
    (prime:Prime H) (slope:H.natDegree=1) (nonlin:2≤jetDegree H) (pos:0<U)
    (width:∀ j i,((H.coeff j).coeff i).totalDegree≤U)
    (dp:0<d) (phys:131071+M.overhead≤(d:ℤ)) (gap:d<179730) (tame:d<p)
    (mg:41*m.seedMass<p) (rg:41*r.seedMass<p)
    (table:∀ i j:Fin 22,i.val+j.val≤21→JointLedger.Pass m r (JointRouted.seedWeight d U)
      (JointRouted.ordWeight d (jetDegree H-1)) limit i.val j.val) :
    Γ.card≤limit ∨ ∃ (f:Equation) (G:Pade.Row SeedField),
      ProjectedProduct (P.main∪P.rescue) f ∧ 22≤f.natDegree ∧ G.primitive ∧
      G.graphDegree≤TransitionClassification.maxGraph (TransitionClassification.band f.natDegree) ∧
      Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets (P.main∪P.rescue))
        (TransitionClassification.content (TransitionClassification.band f.natDegree)) := by
  classical
  have geom (q) (hq:q∈P.main∪P.rescue):Parent q:=((mem_union.mp hq).elim (fun h=>(P.mainGeo q h).1) (fun h=>(P.rescueGeo q h).1))
  obtain ⟨f,union⟩:=JointProjection.exists_product _ geom
  by_cases low:f.natDegree≤21
  · left
    obtain ⟨G,N,gp,eq,deg⟩:=HelperGraph.of_prime prime slope
    apply JointClosure.small F hi P.paid P.main P.rescue (fun q h=>(P.mainGeo q h).1)
      (fun q h=>(P.rescueGeo q h).1) P.aSrc P.bSrc P.mainActive P.rescueActive
      P.mainOrigin P.rescueOrigin m r P.wm P.wr P.mainOrd P.mainSeed P.rescueOrd P.rescueSeed
      P.bill P.boundsM P.boundsR N gp (deg ▸ nonlin) pos dp phys gap tame (eq ▸ width) _ union low mg rg (deg ▸ table)
    intro z hz
    rcases P.cover z hz with paid|⟨_,main⟩|⟨root,regular,rescue⟩
    · exact Or.inl paid
    · exact Or.inr (Or.inl main)
    · refine Or.inr (Or.inr ⟨?_,?_,rescue⟩)
      · simpa only [den,rhs,eq] using Prefix6969Rescue.graph_law slope root
      · simpa only [den,eq,Prefix6969Rescue.regular,Prefix6969Rescue.denominator,
          NativeLostCurve.seed] using regular
  · right
    rcases union with proj|⟨_,rfl⟩
    · have live:(P.main∪P.rescue).Nonempty:=by
        by_contra empty
        have unit:=Research6966.NativeOrdinateMass.divides_of_member (D:=1) proj (fun q h=>False.elim (empty ⟨q,h⟩))
        have small:=natDegree_le_of_dvd unit (one_ne_zero: (1:Equation)≠0)
        simp only [natDegree_one] at small
        omega
      have pass q (hq:q∈P.main∪P.rescue):TerminalBanks.Pass Crt (word M) 179730 SpreadCatalogue.shape q:=
        (mem_union.mp hq).elim (fun h=>(P.mainGeo q h).2.1) (fun h=>(P.rescueGeo q h).2.1)
      obtain ⟨G,gp,degree,control⟩:=TransitionClassification.graph_above_twenty_one Crt (word M) lo hi _ live geom pass proj (by omega)
      exact ⟨f,G,proj,by omega,gp,degree,control⟩
    · simp at low


/-- On the high-weight seed-one helper at the first transition, the
concrete prefix charges close the entire low-degree exit. A surviving
high-degree packet includes its actual selected graph and its sheets. -/
theorem seed_one_or_larger {u del} {M:Model u del} {Γ} (F:Family M Γ)
    {D:PoleData M.overhead.toNat} (Crt:CRTLift D)
    (lo:2314≤M.overhead.toNat) (hi:M.overhead.toNat≤2411)
    (noPole:∀j i,(D.block j).eval (nodeL i)≠0)
    (residues:∀ z∈Γ,MarkResidues D (M.label z) (F.scalar z))
    {H:Jet} (physical:HelperPhysicalModel.Model Crt H) (prime:Prime H)
    (slope:H.natDegree=1) (seeded:UsesSeed H) (caps:RowCaps H (Prefix6969Rescue.graphShape 2 1))
    (outer:PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) H) (degree:2≤jetDegree H) (seed:1≤seedDegree H)
    (floor:308385≤RawPhysicalDegree.weight (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) physical.raw) :
    Γ.card≤274779381266040419 ∨ ∃ (P:Pair F Crt H SmallCertificates.primary1 SmallCertificates.rescue1)
      (f:Equation) (G:Pade.Row SeedField),ProjectedProduct (P.main∪P.rescue) f ∧ 22≤f.natDegree ∧ G.primitive ∧
      G.graphDegree≤TransitionClassification.maxGraph (TransitionClassification.band f.natDegree) ∧
      Pade.Controls (G.map (algebraMap SeedField Pade.Native.Sep)) (Pade.Native.sheets (P.main∪P.rescue))
          (TransitionClassification.content (TransitionClassification.band f.natDegree)) := by
  obtain ⟨P⟩:=of_seed_one F Crt lo hi noPole residues physical prime slope seeded caps outer degree seed floor
  have equal:jetDegree H=2:=Nat.le_antisymm ((K1_14_2_2_2_1.jetDegree_le H 2).mpr (fun j i hn=>(caps j i hn).1)) degree
  have width (j i:ℕ):((H.coeff j).coeff i).totalDegree≤1:=by
    by_cases zero:(H.coeff j).coeff i=0
    · simp [zero]
    · exact (caps j i zero).2.2
  have ph:131071+M.overhead≤(133482:ℤ):=by omega
  have table:∀i j:Fin 22,i.val+j.val≤21→JointLedger.Pass SmallCertificates.primary1 SmallCertificates.rescue1
      (JointRouted.seedWeight 133482 1) (JointRouted.ordWeight 133482 (jetDegree H-1)) 274779381266040419 i.val j.val:=by
    rw [equal,SmallCertificates.seed_price1,show 2-1=1 by decide,SmallCertificates.ordinate_price]
    exact SmallCertificates.bill1
  rcases P.reduce lo (hi.trans (by decide)) prime slope degree (by decide:0<1) width (by decide:0<133482)
    ph (by decide) (by decide) (by decide) (by decide) table with complete|more
  · exact Or.inl complete
  · exact Or.inr ⟨P,more⟩

end
end Research6969.TransitionPacket
end Z6969Source0779

-- Source: Research6969.PrefixNormalPacket
section Z6969Source0780
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace Research6969.TransitionPacket
noncomputable section

open Finset Polynomial
open K1 (K)
open K1_14 (Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues evaluated nodeL)
open K1_14_2 (UsesSeed toJet)
open K1_14_2_2 (Active RowCaps mass)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (Parent)
open Lower6960
open Far6969RescueGeometry (Model Family word OnSurface)
open Prefix6969Main (Band)
open PrefixRows (Common)
open Research6966
open scoped Classical BigOperators

/-- The four price fields are matched against the public joint ledger, and
the actual rational history yields its integral seed and ordinate caps. -/
structure NormalBounds (main : Prefix6969Main.Plan) (mp : Prefix6969Main.Pricing)
    (rescue : Prefix6969Rescue.Plan) (rp : Prefix6969Rescue.NormalPrice)
    (m r : JointLedger.Book) where
  main_fee : mp.fee ≤ m.fee
  rescue_fee : rp.fee ≤ r.fee
  mainOrd : m.ordinateCredit = mp.retainedCredit 0
  mainSeed : m.seedCredit = mp.retainedCredit 1 + mp.retainedCredit 2
  rescueOrd : r.ordinateCredit = rp.credit 0
  rescueSeed : r.seedCredit = rp.credit 1 + rp.credit 2
  mainMass : main.history main.last 1 < (m.seedMass : ℚ)+1
  rescueMass : rescue.history (rescue.count-1) 1 < (r.seedMass : ℚ)+1
  mainGrade : ℕ
  rescueGrade : ℕ
  mainDegree : main.history main.last 0 < (mainGrade : ℚ)+1
  rescueDegree : rescue.history (rescue.count-1) 0 < (rescueGrade : ℚ)+1

private theorem cap_nat {n k : ℕ} {q : ℚ}
    (cap : (n : ℚ) ≤ q) (rounded : q < (k : ℚ)+1) : n ≤ k := by
  apply Nat.le_of_lt_succ
  exact_mod_cast cap.trans_lt rounded

/-- Produce the native normal pair, pay both real prefixes and filter the
main parent set by exclusion of the original exceptional jet. -/
theorem of_normal_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    {main : Prefix6969Main.Plan} {mp : Prefix6969Main.Pricing}
    (mainValid : main.Valid) (mainPrice : mp.Valid main Band.near)
    {extra low floor : ℕ}
    (mainSource : main.Sources 2314 2411 Prefix6969Helper.helperBank extra 2 low floor)
    {rescue : Prefix6969Rescue.Plan} {rp : Prefix6969Rescue.NormalPrice}
    (rescueSource : rescue.Sources 2314 2411) (rescuePrice : rp.Valid rescue)
    {m r : JointLedger.Book} (checked : NormalBounds main mp rescue rp m r)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G rescue.primeShape)
    (known : Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (mainDegree : 2 ≤ jetDegree G) (mainSeed : low ≤ seedDegree G)
    (mainFloor : floor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw)
    (rescueDegree : rescue.degree ≤ jetDegree G) (rescueSeed : rescue.seedFloor ≤ seedDegree G)
    (rescueFloor : rescue.physicalFloor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ P : Pair F Crt G m r, P.mainGrade=checked.mainGrade ∧ P.rescueGrade=checked.rescueGrade := by
  classical
  obtain ⟨R, I, C, A, identity, mainCount, mainMass, mainGeom, mainOrigin, mainCover⟩ :=
    Prefix6969Main.main_prefix F Crt main mainValid Band.near mp mainPrice mainSource (by decide) lo hi
      noPole residues phys known mainDegree mainSeed mainFloor
  have subRes : ∀ γ∈Prefix6969Pair.zeros F G,
      MarkResidues D (M.label γ) ((Prefix6969Pair.zeros_family F G).scalar γ) :=
    fun γ hγ => residues γ (mem_filter.mp hγ).1
  have roots : ∀ γ∈Prefix6969Pair.zeros F G,
      jetAt G (M.label γ) ((Prefix6969Pair.zeros_family F G).scalar γ) = 0 :=
    fun γ hγ => (mem_filter.mp hγ).2
  obtain ⟨Q, B, S, _, rescueCount, rescueMass, rescueGeom, rescueCover⟩ :=
    Prefix6969Rescue.normal_prefix (Prefix6969Pair.zeros_family F G) (Crt := Crt)
      rescueSource rescuePrice lo hi noPole subRes phys prime slope seeded caps
      rescueDegree rescueSeed rescueFloor roots
  let keep := A.filter (fun q => G∉q.asIdeal)
  have activeM (J) (mem : J∈I.final) : Active J := (I.kept_geom (mem_filter.mp mem).1).1
  have activeR (J) (mem : J∈B.final) : Active J :=
    (Q.parent_geom (Prefix6969Rescue.Invoice.Book.final_initial B mem)).1
  refine ⟨⟨C.paid ∪ Prefix6969Rescue.Invoice.paid B, keep, S, I.final, B.final, activeM, activeR,
    ?_, ?_, fun q h => mainOrigin q (mem_filter.mp h).1, fun q h => (rescueGeom q h).2.2.2,
    mp.retainedCredit, rp.credit, checked.mainOrd, checked.mainSeed, checked.rescueOrd, checked.rescueSeed,
    ?_, cap_nat (mainMass 1) checked.mainMass, cap_nat (rescueMass 1) checked.rescueMass,
    checked.mainGrade, checked.rescueGrade, cap_nat (mainMass 0) checked.mainDegree,
    cap_nat (rescueMass 0) checked.rescueDegree, ?_⟩, rfl, rfl⟩
  · intro q h
    have parent := mainGeom q (mem_filter.mp h).1
    exact ⟨parent.1, parent.2, (mem_filter.mp h).2⟩
  · intro q h
    have parent := rescueGeom q h
    exact ⟨parent.1, parent.2.1, parent.2.2.1⟩
  · have union := card_union_le C.paid (Prefix6969Rescue.Invoice.paid B)
    have mainPaid := mainCount.trans checked.main_fee
    have rescuePaid := rescueCount.trans checked.rescue_fee
    change (C.paid ∪ Prefix6969Rescue.Invoice.paid B).card +
      mp.charge I.final + Prefix6969Rescue.Invoice.charge B rp.credit ≤ m.fee+r.fee
    omega
  · intro γ hγ
    by_cases root : jetAt G (M.label γ) (F.scalar γ) = 0
    · rcases rescueCover γ (mem_filter.mpr ⟨hγ,root⟩) with paid | ⟨reg,on⟩
      · exact Or.inl (mem_union_right _ paid)
      · exact Or.inr (Or.inr ⟨root,reg,on⟩)
    · have inMain : γ∈R.marks := mem_filter.mpr ⟨hγ, by simpa only [identity] using root⟩
      rcases mainCover γ inMain with paid | ⟨q,mem,on⟩
      · exact Or.inl (mem_union_left _ paid)
      · exact Or.inr (Or.inl ⟨root,q,mem_filter.mpr ⟨mem,fun owns => root (on G owns)⟩,on⟩)

theorem of_normal {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    {main : Prefix6969Main.Plan} {mp : Prefix6969Main.Pricing}
    (mainValid : main.Valid) (mainPrice : mp.Valid main Band.near)
    {extra low floor : ℕ}
    (mainSource : main.Sources 2314 2411 Prefix6969Helper.helperBank extra 2 low floor)
    {rescue : Prefix6969Rescue.Plan} {rp : Prefix6969Rescue.NormalPrice}
    (rescueSource : rescue.Sources 2314 2411) (rescuePrice : rp.Valid rescue)
    {m r : JointLedger.Book} (checked : NormalBounds main mp rescue rp m r)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G rescue.primeShape)
    (known : Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (mainDegree : 2 ≤ jetDegree G) (mainSeed : low ≤ seedDegree G)
    (mainFloor : floor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw)
    (rescueDegree : rescue.degree ≤ jetDegree G) (rescueSeed : rescue.seedFloor ≤ seedDegree G)
    (rescueFloor : rescue.physicalFloor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (Pair F Crt G m r) := by
  obtain ⟨P,_,_⟩ := of_normal_with_grades F Crt mainValid mainPrice mainSource rescueSource rescuePrice
    checked lo hi noPole residues phys prime slope seeded caps known mainDegree mainSeed mainFloor
    rescueDegree rescueSeed rescueFloor
  exact ⟨P⟩

end
end Research6969.TransitionPacket
end Z6969Source0780

-- Source: Research6969.PrefixMainDataNormalSeedOne0
section Z6969Source0781
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.NormalSeedOne0
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 16, 21, 20, 30, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank4 1470, bank9 1624, bank17 1760, bank23 1898, bank26 2102, bank32 2243, bank44 2409, bank54 2755, bank74 3583, bank84 5564, bank112 3547, bank108 8100, bank120 36262, bank150 6517, bank210 11036, bank181 61748, bank174 148759, bank169 292467] i
  head := src1205
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![14801, 171537, 801201, 4074442],
    ![12303, 147095, 1329539/2, 3522050],
    ![53398/9, 637525/9, 619520, 3097600],
    ![3599, 343505/8, 3113506/9, 16465150/9],
    ![60658/25, 147808/5, 211251, 9117425/8],
    ![16211/9, 789035/36, 211251, 9117425/8],
    ![18775/16, 886655/64, 396682/3, 644809],
    ![89110/121, 1032225/121, 4677310/49, 7590025/16],
    ![89110/121, 1032225/121, 2000617/24, 31082525/72],
    ![63754/121, 1859179/242, 15374666/225, 31082525/72],
    ![63754/121, 1055510/147, 15374666/225, 2461618/9],
    ![24521/50, 1055510/147, 15374666/225, 2461618/9],
    ![667406/1681, 1055510/147, 15374666/225, 2461618/9],
    ![667406/1681, 10295860/1681, 46322996/841, 42471289/169],
    ![667406/1681, 7533960/1369, 1724375/36, 167540275/729],
    ![474397/1369, 7533960/1369, 1724375/36, 167540275/729],
    ![462882/1369, 7533960/1369, 1724375/36, 167540275/729],
    ![459151/1369, 7533960/1369, 1724375/36, 167540275/729]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 2 1 308385 := by
  refine ⟨?_, rank154 8675, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1205⟩⟩
  · intro i; fin_cases i
    · exact free4_0
    · exact free9_0
    · exact free17_0
    · exact free23_0
    · exact free26_0
    · exact free32_0
    · exact free44_0
    · exact free54_0
    · exact free74_1
    · exact free84_0
    · exact free112_0
    · exact free108_1
    · exact free120_0
    · exact free150_0
    · exact free210_0
    · exact free181_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨50/100, 60/100, [367868119, 366604032, 367389972, 366835848, 366362383, 367250716, 367115638, 156881649, 157144991, 157199284, 115270357, 87300349, 86969492, 115465894, 115567675, 131740080, 179078930, 239214604], [938499, 941965, 939810, 941329, 942627, 940192, 940562, 2453002, 2448623, 2447720, 3396467, 4552469, 4569157, 3391000, 3388154, 2951688, 2123256, 1537212],
  ![126979896095280, 1601383685396, 215293143600, 4034399880], 205786607349302799⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,3,3,7,7,7,9,12,12,9,9,8,6,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 7533960/1369, 1724375/36, 167540275/729] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.NormalSeedOne0
end Z6969Source0781

-- Source: Research6969.PrefixNormalDataSeed1
section Z6969Source0782
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Research6969.NormalPrefixData.Seed1
open Lower6960
open Prefix6969Rescue
open TransitionPacket
open PhysicalCatalogue TransitionBanks

def plan : Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,1⟩
  bank i := ![bank245 164470, bank245 182926, bank245 206037, bank251 220122, bank252 234092, bank252 292397, bank270 364135, bank303 321892, bank315 365477, bank315 421074, bank302 410737] i
  reserve i := ![0, 1, 2, 3, 4, 6, 10, 10, 13, 16, 13] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 308385
  seedFloor := 1

theorem sources : plan.Sources 2314 2411 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank245 164470
    · exact rank245 182926
    · exact rank245 206037
    · exact rank251 220122
    · exact rank252 234092
    · exact rank252 292397
    · exact rank270 364135
    · exact rank303 321892
    · exact rank315 365477
    · exact rank315 421074
    · exact rank302 410737
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover629⟩
    · exact ⟨_, cover630⟩
    · exact ⟨_, cover631⟩
    · exact ⟨_, cover632⟩
    · exact ⟨_, cover633⟩
    · exact ⟨_, cover634⟩
    · exact ⟨_, cover635⟩
    · exact ⟨_, cover636⟩
    · exact ⟨_, cover638⟩
    · exact ⟨_, cover639⟩
    · exact ⟨_, cover637⟩

def price : NormalPrice := ⟨1, 100/100, 80/100, ![206646633540, 207926677348, 462874133, 462877700], 34856458124440570⟩
theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

open Lower6960.Prefix6969MainCases.NormalSeedOne0 (plan price valid sources priced) in
def bounds : NormalBounds Lower6960.Prefix6969MainCases.NormalSeedOne0.plan Lower6960.Prefix6969MainCases.NormalSeedOne0.price
    plan price SmallCertificates.primary1 SmallCertificates.rescue1 where
  main_fee := by decide +kernel
  rescue_fee := by decide +kernel
  mainOrd := rfl
  mainSeed := rfl
  rescueOrd := rfl
  rescueSeed := rfl
  mainMass := by decide +kernel
  rescueMass := by decide +kernel
  mainGrade := 335
  rescueGrade := 386
  mainDegree := by decide +kernel
  rescueDegree := by decide +kernel


open Finset Polynomial
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2 (UsesSeed)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Far6969RescueGeometry (Model Family word)
open Research6966

theorem packet {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 1))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 1 ≤ seedDegree G)
    (floor : 308385 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (TransitionPacket.Pair F Crt G SmallCertificates.primary1 SmallCertificates.rescue1) :=
  TransitionPacket.of_normal F Crt
    Lower6960.Prefix6969MainCases.NormalSeedOne0.valid Lower6960.Prefix6969MainCases.NormalSeedOne0.priced Lower6960.Prefix6969MainCases.NormalSeedOne0.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor


theorem packet_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 1))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 1 ≤ seedDegree G)
    (floor : 308385 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ P : TransitionPacket.Pair F Crt G SmallCertificates.primary1 SmallCertificates.rescue1,
      P.mainGrade=335 ∧ P.rescueGrade=386 :=
  TransitionPacket.of_normal_with_grades F Crt
    Lower6960.Prefix6969MainCases.NormalSeedOne0.valid Lower6960.Prefix6969MainCases.NormalSeedOne0.priced Lower6960.Prefix6969MainCases.NormalSeedOne0.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor

end Research6969.NormalPrefixData.Seed1
end Z6969Source0782

-- Source: Research6969.PhysicalChecks088
section Z6969Source0783
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src1189 : Request := ⟨⟨⟨556,772,170,7034⟩,5255817068544,9968090926⟩,10,3,2,436225,18⟩
theorem cover1189 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1189) 2411 2314 [2318, 2333, 2381, 2411] := triangleCover (by decide +kernel)
def src1190 : Request := ⟨⟨⟨556,772,170,7131⟩,5255817068544,9968090926⟩,10,3,2,436323,17⟩
theorem cover1190 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1190) 2411 2314 [2318, 2334, 2384, 2411] := triangleCover (by decide +kernel)
def src1191 : Request := ⟨⟨⟨556,772,170,7228⟩,5255817068544,9968090926⟩,10,3,2,436413,16⟩
theorem cover1191 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1191) 2411 2314 [2318, 2334, 2384, 2411] := triangleCover (by decide +kernel)
def src1192 : Request := ⟨⟨⟨556,772,170,7326⟩,5255817068544,9968090926⟩,10,3,2,436495,15⟩
theorem cover1192 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1192) 2411 2314 [2318, 2333, 2381, 2411] := triangleCover (by decide +kernel)
def src1193 : Request := ⟨⟨⟨556,772,170,7426⟩,5255817068544,9968090926⟩,10,3,2,436571,14⟩
theorem cover1193 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1193) 2411 2314 [2318, 2334, 2384, 2411] := triangleCover (by decide +kernel)
def src1194 : Request := ⟨⟨⟨556,772,170,7526⟩,5255817068544,9968090926⟩,10,3,2,436642,13⟩
theorem cover1194 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1194) 2411 2314 [2318, 2334, 2384, 2411] := triangleCover (by decide +kernel)
def src1195 : Request := ⟨⟨⟨556,772,170,7627⟩,5255817068544,9968090926⟩,10,3,2,436707,12⟩
theorem cover1195 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1195) 2411 2314 [2318, 2333, 2381, 2411] := triangleCover (by decide +kernel)
def src1196 : Request := ⟨⟨⟨556,772,170,7728⟩,5255817068544,9968090926⟩,10,3,2,436766,11⟩
theorem cover1196 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1196) 2411 2314 [2318, 2333, 2381, 2411] := triangleCover (by decide +kernel)
def src1197 : Request := ⟨⟨⟨556,772,170,7830⟩,5255817068544,9968090926⟩,10,3,2,436820,10⟩
theorem cover1197 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1197) 2411 2314 [2318, 2333, 2381, 2411] := triangleCover (by decide +kernel)
def src1198 : Request := ⟨⟨⟨556,772,170,7933⟩,5255817068544,9968090926⟩,10,3,2,436868,9⟩
theorem cover1198 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1198) 2411 2314 [2318, 2333, 2381, 2411] := triangleCover (by decide +kernel)
def src1199 : Request := ⟨⟨⟨556,772,170,8037⟩,5255817068544,9968090926⟩,10,3,2,436910,8⟩
theorem cover1199 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1199) 2411 2314 [2318, 2333, 2381, 2411] := triangleCover (by decide +kernel)
def src1200 : Request := ⟨⟨⟨556,772,170,8141⟩,5255817068544,9968090926⟩,10,3,2,436947,7⟩
theorem cover1200 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1200) 2411 2314 [2318, 2333, 2381, 2411] := triangleCover (by decide +kernel)
def src1201 : Request := ⟨⟨⟨556,772,170,8247⟩,5255817068544,9968090926⟩,10,3,2,436978,6⟩
theorem cover1201 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1201) 2411 2314 [2318, 2333, 2381, 2411] := triangleCover (by decide +kernel)
def src1202 : Request := ⟨⟨⟨556,772,170,8353⟩,5255817068544,9968090926⟩,10,3,2,437003,5⟩
theorem cover1202 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1202) 2411 2314 [2318, 2333, 2381, 2411] := triangleCover (by decide +kernel)
def src1203 : Request := ⟨⟨⟨556,772,170,8460⟩,5255817068544,9968090926⟩,10,3,2,437023,4⟩
theorem cover1203 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1203) 2411 2314 [2318, 2333, 2381, 2411] := triangleCover (by decide +kernel)
def src1204 : Request := ⟨⟨⟨556,772,170,8567⟩,5255817068544,9968090926⟩,10,3,2,437037,3⟩
theorem cover1204 : PhysicalWindow.Cover (PhysicalWindow.Triangular src1204) 2411 2314 [2318, 2333, 2381, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source0783

-- Source: Research6969.PrefixMainDataHighQuadraticFinal0
section Z6969Source0784
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HighQuadraticFinal0
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 20, 14, 21, 20, 25, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank1 1559, bank8 1694, bank14 1831, bank21 1963, bank30 2315, bank41 2989, bank42 4552, bank48 2482, bank58 2557, bank73 5660, bank82 2965, bank74 6544, bank111 3583, bank140 3997, bank145 7920, bank119 41691, bank198 9780, bank208 11310, bank181 61748, bank174 148759, bank169 292467] i
  head := src1204
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![13905, 174874, 811280, 4552523],
    ![23965/2, 587825/4, 1330677/2, 7256249/2],
    ![17372/3, 212272/3, 629864, 3352561],
    ![7059/2, 684957/16, 346385, 16817021/9],
    ![15956/9, 796199/36, 3577683/16, 19832605/16],
    ![24292/27, 106909/9, 485795/4, 25606763/36],
    ![73478/121, 1236458/121, 5578791/49, 25606763/36],
    ![73478/121, 1236458/121, 5578791/49, 10631647/18],
    ![73478/121, 1034380/121, 663844/7, 6538249/16],
    ![77324/147, 3448402/441, 7565011/98, 6538249/16],
    ![77324/147, 3448402/441, 7565011/98, 6538249/16],
    ![61324/121, 3448402/441, 152557/2, 6538249/16],
    ![61324/121, 3120094/441, 1000963/14, 61391122/225],
    ![61324/121, 3120094/441, 1000963/14, 61391122/225],
    ![1640767/3362, 10582612/1681, 47416520/841, 61391122/225],
    ![1330489/3362, 10582612/1681, 47416520/841, 61391122/225],
    ![1330489/3362, 7471628/1323, 7035080/147, 125677890/529],
    ![1330489/3362, 14945203/2738, 7035080/147, 113041565/486],
    ![474397/1369, 14945203/2738, 7035080/147, 113041565/486],
    ![462882/1369, 14945203/2738, 7035080/147, 113041565/486],
    ![459151/1369, 14945203/2738, 7035080/147, 113041565/486]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 2 2 308378 := by
  refine ⟨?_, rank154 8567, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1204⟩⟩
  · intro i; fin_cases i
    · exact free1_0
    · exact free8_0
    · exact free14_0
    · exact free21_0
    · exact free30_1
    · exact free41_0
    · exact free42_2
    · exact free48_0
    · exact free58_0
    · exact free73_0
    · exact free82_0
    · exact free74_2
    · exact free111_0
    · exact free140_0
    · exact free145_0
    · exact free119_0
    · exact free198_0
    · exact free208_0
    · exact free181_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [362315883, 361774598, 361252498, 362222808, 361525171, 362313791, 362219968, 360452931, 159996443, 160297803, 160575178, 160052944, 70418531, 83022269, 73845132, 100589819, 112601354, 112501521, 131501682, 178840533, 239029959], [953719, 955203, 956634, 953974, 955887, 953725, 953982, 958826, 2401203, 2396192, 2391579, 2400264, 5694101, 4803576, 5421704, 3930625, 3488484, 3491950, 2956916, 2126131, 1538731],
  ![126881882836380, 1601583626796, 215126963100, 4154504200], 203627057392393535⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,3,3,3,7,7,7,7,15,13,15,11,10,10,8,6,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 14945203/2738, 7035080/147, 113041565/486] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HighQuadraticFinal0
end Z6969Source0784

end Merged_Z6969Pack0630

-- merged module Z6969Pack0631
section Merged_Z6969Pack0631

-- Source: Research6969.PhysicalChecks059
section Z6969Source0785
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src616 : Request := ⟨⟨⟨3950,5512,1189,384491⟩,1848744952463360,25255771038451⟩,16,2,1,308364,3⟩
theorem cover616 : PhysicalWindow.Cover (PhysicalWindow.Triangular src616) 2411 2314 [2315, 2320, 2334, 2373, 2411] := triangleCover (by decide +kernel)
def src617 : Request := ⟨⟨⟨4800,6698,1445,435816⟩,3317023033262080,55058665830093⟩,20,2,1,308364,3⟩
theorem cover617 : PhysicalWindow.Cover (PhysicalWindow.Triangular src617) 2411 2314 [2315, 2320, 2334, 2373, 2411] := triangleCover (by decide +kernel)
def src618 : Request := ⟨⟨⟨1750,2442,527,157294⟩,161065121873920,975196209190⟩,0,2,1,308378,2⟩
theorem cover618 : PhysicalWindow.Cover (PhysicalWindow.Triangular src618) 2411 2314 [2315, 2321, 2338, 2387, 2411] := triangleCover (by decide +kernel)
def src619 : Request := ⟨⟨⟨1750,2442,527,174944⟩,161065121873920,975196209190⟩,1,2,1,308378,2⟩
theorem cover619 : PhysicalWindow.Cover (PhysicalWindow.Triangular src619) 2411 2314 [2315, 2321, 2338, 2387, 2411] := triangleCover (by decide +kernel)
def src620 : Request := ⟨⟨⟨1750,2442,527,197050⟩,161065121873920,975196209190⟩,2,2,1,308378,2⟩
theorem cover620 : PhysicalWindow.Cover (PhysicalWindow.Triangular src620) 2411 2314 [2315, 2321, 2338, 2387, 2411] := triangleCover (by decide +kernel)
def src621 : Request := ⟨⟨⟨2100,2930,632,223889⟩,278060332482560,2019119590628⟩,4,2,1,308378,2⟩
theorem cover621 : PhysicalWindow.Cover (PhysicalWindow.Triangular src621) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src622 : Request := ⟨⟨⟨2100,2930,632,279658⟩,278060332482560,2019119590628⟩,6,2,1,308378,2⟩
theorem cover622 : PhysicalWindow.Cover (PhysicalWindow.Triangular src622) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src623 : Request := ⟨⟨⟨2600,3628,783,247902⟩,527755772952576,4745819470168⟩,6,2,1,308378,2⟩
theorem cover623 : PhysicalWindow.Cover (PhysicalWindow.Triangular src623) 2411 2314 [2315, 2321, 2338, 2385, 2411] := triangleCover (by decide +kernel)
def src624 : Request := ⟨⟨⟨2600,3628,783,348262⟩,527755772952576,4745819470168⟩,10,2,1,308378,2⟩
theorem cover624 : PhysicalWindow.Cover (PhysicalWindow.Triangular src624) 2411 2314 [2315, 2321, 2338, 2385, 2411] := triangleCover (by decide +kernel)
def src625 : Request := ⟨⟨⟨3200,4465,963,307875⟩,983050615259136,10877088344236⟩,10,2,1,308378,2⟩
theorem cover625 : PhysicalWindow.Cover (PhysicalWindow.Triangular src625) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src626 : Request := ⟨⟨⟨3950,5512,1189,349563⟩,1848744952463360,25255771038451⟩,13,2,1,308378,2⟩
theorem cover626 : PhysicalWindow.Cover (PhysicalWindow.Triangular src626) 2411 2314 [2315, 2320, 2334, 2373, 2411] := triangleCover (by decide +kernel)
def src627 : Request := ⟨⟨⟨3950,5512,1189,402741⟩,1848744952463360,25255771038451⟩,16,2,1,308378,2⟩
theorem cover627 : PhysicalWindow.Cover (PhysicalWindow.Triangular src627) 2411 2314 [2315, 2320, 2334, 2373, 2411] := triangleCover (by decide +kernel)
def src628 : Request := ⟨⟨⟨4800,6698,1445,456506⟩,3317023033262080,55058665830093⟩,20,2,1,308378,2⟩
theorem cover628 : PhysicalWindow.Cover (PhysicalWindow.Triangular src628) 2411 2314 [2315, 2320, 2334, 2373, 2411] := triangleCover (by decide +kernel)
def src640 : Request := ⟨⟨⟨1000,1395,301,64247⟩,30103476895744,104105680031⟩,0,3,1,385979,1⟩
theorem cover640 : PhysicalWindow.Cover (PhysicalWindow.Triangular src640) 2411 2314 [2320, 2340, 2400, 2411] := triangleCover (by decide +kernel)
def src641 : Request := ⟨⟨⟨1000,1395,301,72277⟩,30103476895744,104105680031⟩,1,3,1,385979,1⟩
theorem cover641 : PhysicalWindow.Cover (PhysicalWindow.Triangular src641) 2411 2314 [2318, 2333, 2378, 2411] := triangleCover (by decide +kernel)
def src642 : Request := ⟨⟨⟨1000,1395,296,91474⟩,29722184515584,102755930405⟩,2,3,1,385979,1⟩
theorem cover642 : PhysicalWindow.Cover (PhysicalWindow.Triangular src642) 2411 2314 [2321, 2345, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source0785

-- Source: Research6969.PrefixNormalDataSeed2
section Z6969Source0786
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Research6969.NormalPrefixData.Seed2
open Lower6960
open Prefix6969Rescue
open TransitionPacket
open PhysicalCatalogue TransitionBanks

def plan : Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,2⟩
  bank i := ![bank245 157294, bank245 174944, bank245 197050, bank252 223889, bank270 247902, bank252 279658, bank270 348262, bank303 307875, bank315 349563, bank315 402741, bank332 456506] i
  reserve i := ![0, 1, 2, 4, 6, 6, 10, 10, 13, 16, 20] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 308378
  seedFloor := 2

theorem sources : plan.Sources 2314 2411 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank245 157294
    · exact rank245 174944
    · exact rank245 197050
    · exact rank252 223889
    · exact rank270 247902
    · exact rank252 279658
    · exact rank270 348262
    · exact rank303 307875
    · exact rank315 349563
    · exact rank315 402741
    · exact rank332 456506
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover618⟩
    · exact ⟨_, cover619⟩
    · exact ⟨_, cover620⟩
    · exact ⟨_, cover621⟩
    · exact ⟨_, cover623⟩
    · exact ⟨_, cover622⟩
    · exact ⟨_, cover624⟩
    · exact ⟨_, cover625⟩
    · exact ⟨_, cover626⟩
    · exact ⟨_, cover627⟩
    · exact ⟨_, cover628⟩

def price : NormalPrice := ⟨2, 95/100, 80/100, ![413291143800, 209205115560, 6164731029, 562538500], 33043478944012779⟩
theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

open Lower6960.Prefix6969MainCases.HighQuadraticFinal0 (plan price valid sources priced) in
def bounds : NormalBounds Lower6960.Prefix6969MainCases.HighQuadraticFinal0.plan Lower6960.Prefix6969MainCases.HighQuadraticFinal0.price
    plan price SmallCertificates.primary2 SmallCertificates.rescue2 where
  main_fee := by decide +kernel
  rescue_fee := by decide +kernel
  mainOrd := rfl
  mainSeed := rfl
  rescueOrd := rfl
  rescueSeed := rfl
  mainMass := by decide +kernel
  rescueMass := by decide +kernel
  mainGrade := 335
  rescueGrade := 387
  mainDegree := by decide +kernel
  rescueDegree := by decide +kernel


open Finset Polynomial
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2 (UsesSeed)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Far6969RescueGeometry (Model Family word)
open Research6966

theorem packet {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 2))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 2 ≤ seedDegree G)
    (floor : 308378 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (TransitionPacket.Pair F Crt G SmallCertificates.primary2 SmallCertificates.rescue2) :=
  TransitionPacket.of_normal F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal0.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal0.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal0.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor


theorem packet_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 2))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 2 ≤ seedDegree G)
    (floor : 308378 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ P : TransitionPacket.Pair F Crt G SmallCertificates.primary2 SmallCertificates.rescue2,
      P.mainGrade=335 ∧ P.rescueGrade=387 :=
  TransitionPacket.of_normal_with_grades F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal0.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal0.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal0.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor

end Research6969.NormalPrefixData.Seed2
end Z6969Source0786

-- Source: Research6969.PrefixMainDataHighQuadraticFinal1
section Z6969Source0787
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HighQuadraticFinal1
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 20, 14, 21, 20, 25, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank1 1559, bank8 1694, bank14 1831, bank21 1963, bank31 2263, bank41 2989, bank42 4552, bank48 2482, bank58 2557, bank73 5660, bank82 2965, bank74 6544, bank111 3583, bank140 3997, bank145 7920, bank119 41691, bank199 9241, bank209 11249, bank181 61748, bank174 148759, bank169 292467] i
  head := src1203
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![13920, 174349, 809860, 4524884],
    ![23965/2, 146020, 661112, 3582810],
    ![17372/3, 632750/9, 629864, 3352561],
    ![7059/2, 340285/8, 3097456/9, 1845220],
    ![32167/18, 391165/18, 885139/4, 4786245/4],
    ![24292/27, 956510/81, 1086592/9, 702415],
    ![73478/121, 111880/11, 5553004/49, 702415],
    ![73478/121, 111880/11, 5553004/49, 583270],
    ![73478/121, 1026890/121, 4613524/49, 6538249/16],
    ![77324/147, 3430640/441, 3762550/49, 6538249/16],
    ![77324/147, 3430640/441, 3762550/49, 6538249/16],
    ![61324/121, 3430640/441, 152557/2, 6538249/16],
    ![61324/121, 3096340/441, 3476888/49, 1347208/5],
    ![61324/121, 3096340/441, 3476888/49, 1347208/5],
    ![1640767/3362, 10518840/1681, 47129760/841, 1347208/5],
    ![1330489/3362, 10518840/1681, 47129760/841, 1347208/5],
    ![1330489/3362, 1065220/189, 21050998/441, 85396081/400],
    ![1330489/3362, 14865515/2738, 133570976/2809, 85396081/400],
    ![474397/1369, 14865515/2738, 133570976/2809, 85396081/400],
    ![462882/1369, 14865515/2738, 133570976/2809, 85396081/400],
    ![459151/1369, 14865515/2738, 133570976/2809, 85396081/400]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 2 3 308364 := by
  refine ⟨?_, rank154 8460, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1203⟩⟩
  · intro i; fin_cases i
    · exact free1_0
    · exact free8_0
    · exact free14_0
    · exact free21_0
    · exact free31_1
    · exact free41_0
    · exact free42_2
    · exact free48_0
    · exact free58_0
    · exact free73_0
    · exact free82_0
    · exact free74_2
    · exact free111_0
    · exact free140_0
    · exact free145_0
    · exact free119_0
    · exact free199_0
    · exact free209_0
    · exact free181_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [360397498, 358725311, 359813645, 359184664, 359711941, 359170423, 360245536, 358607008, 163842506, 164274426, 164256911, 164260305, 61731104, 82308138, 73521917, 99850929, 112154437, 112061691, 131014171, 178353021, 238658431], [958978, 963562, 960578, 962303, 960857, 962342, 959394, 963886, 2337244, 2330061, 2330352, 2330296, 6521159, 4845990, 5447398, 3961817, 3504002, 3507222, 2967607, 2132011, 1541786],
  ![126684668343420, 1601984653124, 214792587900, 4172674310], 202030739200029160⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,3,3,3,7,7,7,7,18,13,15,11,10,10,8,6,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 14865515/2738, 133570976/2809, 85396081/400] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HighQuadraticFinal1
end Z6969Source0787

-- Source: Research6969.PhysicalChecks058
section Z6969Source0788
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src600 : Request := ⟨⟨⟨2100,2930,632,254356⟩,278060332482560,2019119590628⟩,6,2,1,308344,4⟩
theorem cover600 : PhysicalWindow.Cover (PhysicalWindow.Triangular src600) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src601 : Request := ⟨⟨⟨2600,3628,783,225437⟩,527755772952576,4745819470168⟩,6,2,1,308344,4⟩
theorem cover601 : PhysicalWindow.Cover (PhysicalWindow.Triangular src601) 2411 2314 [2315, 2321, 2338, 2385, 2411] := triangleCover (by decide +kernel)
def src602 : Request := ⟨⟨⟨3200,4465,963,280016⟩,983050615259136,10877088344236⟩,10,2,1,308344,4⟩
theorem cover602 : PhysicalWindow.Cover (PhysicalWindow.Triangular src602) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src603 : Request := ⟨⟨⟨2600,3628,783,454999⟩,527755772952576,4745819470168⟩,13,2,1,308344,4⟩
theorem cover603 : PhysicalWindow.Cover (PhysicalWindow.Triangular src603) 2411 2314 [2315, 2321, 2338, 2385, 2411] := triangleCover (by decide +kernel)
def src604 : Request := ⟨⟨⟨3950,5512,1189,317933⟩,1848744952463360,25255771038451⟩,13,2,1,308344,4⟩
theorem cover604 : PhysicalWindow.Cover (PhysicalWindow.Triangular src604) 2411 2314 [2315, 2320, 2334, 2373, 2411] := triangleCover (by decide +kernel)
def src605 : Request := ⟨⟨⟨3950,5512,1189,366307⟩,1848744952463360,25255771038451⟩,16,2,1,308344,4⟩
theorem cover605 : PhysicalWindow.Cover (PhysicalWindow.Triangular src605) 2411 2314 [2315, 2320, 2334, 2373, 2411] := triangleCover (by decide +kernel)
def src606 : Request := ⟨⟨⟨4800,6698,1445,415200⟩,3317023033262080,55058665830093⟩,20,2,1,308344,4⟩
theorem cover606 : PhysicalWindow.Cover (PhysicalWindow.Triangular src606) 2411 2314 [2315, 2320, 2334, 2373, 2411] := triangleCover (by decide +kernel)
def src607 : Request := ⟨⟨⟨1750,2442,527,150149⟩,161065121873920,975196209190⟩,0,2,1,308364,3⟩
theorem cover607 : PhysicalWindow.Cover (PhysicalWindow.Triangular src607) 2411 2314 [2315, 2321, 2338, 2387, 2411] := triangleCover (by decide +kernel)
def src608 : Request := ⟨⟨⟨1750,2442,527,166999⟩,161065121873920,975196209190⟩,1,2,1,308364,3⟩
theorem cover608 : PhysicalWindow.Cover (PhysicalWindow.Triangular src608) 2411 2314 [2315, 2321, 2338, 2387, 2411] := triangleCover (by decide +kernel)
def src609 : Request := ⟨⟨⟨1750,2442,527,188104⟩,161065121873920,975196209190⟩,2,2,1,308364,3⟩
theorem cover609 : PhysicalWindow.Cover (PhysicalWindow.Triangular src609) 2411 2314 [2315, 2321, 2338, 2387, 2411] := triangleCover (by decide +kernel)
def src610 : Request := ⟨⟨⟨2100,2930,632,213734⟩,278060332482560,2019119590628⟩,4,2,1,308364,3⟩
theorem cover610 : PhysicalWindow.Cover (PhysicalWindow.Triangular src610) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src611 : Request := ⟨⟨⟨2100,2930,632,266984⟩,278060332482560,2019119590628⟩,6,2,1,308364,3⟩
theorem cover611 : PhysicalWindow.Cover (PhysicalWindow.Triangular src611) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src612 : Request := ⟨⟨⟨2600,3628,783,236649⟩,527755772952576,4745819470168⟩,6,2,1,308364,3⟩
theorem cover612 : PhysicalWindow.Cover (PhysicalWindow.Triangular src612) 2411 2314 [2315, 2321, 2338, 2385, 2411] := triangleCover (by decide +kernel)
def src613 : Request := ⟨⟨⟨2600,3628,783,332472⟩,527755772952576,4745819470168⟩,10,2,1,308364,3⟩
theorem cover613 : PhysicalWindow.Cover (PhysicalWindow.Triangular src613) 2411 2314 [2315, 2321, 2338, 2385, 2411] := triangleCover (by decide +kernel)
def src614 : Request := ⟨⟨⟨3200,4465,963,293921⟩,983050615259136,10877088344236⟩,10,2,1,308364,3⟩
theorem cover614 : PhysicalWindow.Cover (PhysicalWindow.Triangular src614) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src615 : Request := ⟨⟨⟨3950,5512,1189,333719⟩,1848744952463360,25255771038451⟩,13,2,1,308364,3⟩
theorem cover615 : PhysicalWindow.Cover (PhysicalWindow.Triangular src615) 2411 2314 [2315, 2320, 2334, 2373, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source0788

-- Source: Research6969.PrefixNormalDataSeed3
section Z6969Source0789
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Research6969.NormalPrefixData.Seed3
open Lower6960
open Prefix6969Rescue
open TransitionPacket
open PhysicalCatalogue TransitionBanks

def plan : Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,3⟩
  bank i := ![bank245 150149, bank245 166999, bank245 188104, bank252 213734, bank270 236649, bank252 266984, bank270 332472, bank303 293921, bank315 333719, bank315 384491, bank332 435816] i
  reserve i := ![0, 1, 2, 4, 6, 6, 10, 10, 13, 16, 20] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 308364
  seedFloor := 3

theorem sources : plan.Sources 2314 2411 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank245 150149
    · exact rank245 166999
    · exact rank245 188104
    · exact rank252 213734
    · exact rank270 236649
    · exact rank252 266984
    · exact rank270 332472
    · exact rank303 293921
    · exact rank315 333719
    · exact rank315 384491
    · exact rank332 435816
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover607⟩
    · exact ⟨_, cover608⟩
    · exact ⟨_, cover609⟩
    · exact ⟨_, cover610⟩
    · exact ⟨_, cover612⟩
    · exact ⟨_, cover611⟩
    · exact ⟨_, cover613⟩
    · exact ⟨_, cover614⟩
    · exact ⟨_, cover615⟩
    · exact ⟨_, cover616⟩
    · exact ⟨_, cover617⟩

def price : NormalPrice := ⟨3, 95/100, 80/100, ![619935654060, 210483553772, 5907085248, 562538500], 31080831599657387⟩
theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

open Lower6960.Prefix6969MainCases.HighQuadraticFinal1 (plan price valid sources priced) in
def bounds : NormalBounds Lower6960.Prefix6969MainCases.HighQuadraticFinal1.plan Lower6960.Prefix6969MainCases.HighQuadraticFinal1.price
    plan price SmallCertificates.primary3 SmallCertificates.rescue3 where
  main_fee := by decide +kernel
  rescue_fee := by decide +kernel
  mainOrd := rfl
  mainSeed := rfl
  rescueOrd := rfl
  rescueSeed := rfl
  mainMass := by decide +kernel
  rescueMass := by decide +kernel
  mainGrade := 335
  rescueGrade := 387
  mainDegree := by decide +kernel
  rescueDegree := by decide +kernel


open Finset Polynomial
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2 (UsesSeed)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Far6969RescueGeometry (Model Family word)
open Research6966

theorem packet {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 3))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 3 ≤ seedDegree G)
    (floor : 308364 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (TransitionPacket.Pair F Crt G SmallCertificates.primary3 SmallCertificates.rescue3) :=
  TransitionPacket.of_normal F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal1.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal1.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal1.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor


theorem packet_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 3))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 3 ≤ seedDegree G)
    (floor : 308364 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ P : TransitionPacket.Pair F Crt G SmallCertificates.primary3 SmallCertificates.rescue3,
      P.mainGrade=335 ∧ P.rescueGrade=387 :=
  TransitionPacket.of_normal_with_grades F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal1.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal1.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal1.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor

end Research6969.NormalPrefixData.Seed3
end Z6969Source0789

-- Source: Research6969.PrefixMainDataHighQuadraticFinal2
section Z6969Source0790
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HighQuadraticFinal2
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 20, 14, 21, 20, 25, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank1 1559, bank8 1694, bank14 1831, bank22 1937, bank32 2243, bank41 2989, bank42 4552, bank48 2482, bank58 2557, bank73 5660, bank82 2965, bank74 6544, bank111 3583, bank140 3997, bank145 7920, bank120 36262, bank199 9241, bank210 11036, bank181 61748, bank174 148759, bank169 292467] i
  head := src1202
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![13938, 173982, 807816, 4498313],
    ![23965/2, 580335/4, 1313771/2, 7074991/2],
    ![17372/3, 628684/9, 629864, 3352561],
    ![28537/8, 170029/4, 1019125/3, 16179761/9],
    ![16211/9, 85989/4, 3527491/16, 18735779/16],
    ![24292/27, 950839/81, 4320581/36, 24967117/36],
    ![73478/121, 1224902/121, 5527217/49, 24967117/36],
    ![73478/121, 1224902/121, 5527217/49, 10366073/18],
    ![73478/121, 1019400/121, 4580140/49, 6538249/16],
    ![77324/147, 162518/21, 7485189/98, 6538249/16],
    ![77324/147, 162518/21, 7485189/98, 6538249/16],
    ![61324/121, 162518/21, 152557/2, 6538249/16],
    ![61324/121, 3072586/441, 6900811/98, 59857598/225],
    ![61324/121, 3072586/441, 6900811/98, 59857598/225],
    ![1640767/3362, 10455068/1681, 46843000/841, 59857598/225],
    ![667406/1681, 10455068/1681, 46843000/841, 59857598/225],
    ![667406/1681, 7401970/1323, 21050998/441, 85396081/400],
    ![667406/1681, 7376180/1369, 132727294/2809, 85396081/400],
    ![474397/1369, 7376180/1369, 132727294/2809, 85396081/400],
    ![462882/1369, 7376180/1369, 132727294/2809, 85396081/400],
    ![459151/1369, 7376180/1369, 132727294/2809, 85396081/400]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 2 4 308344 := by
  refine ⟨?_, rank154 8353, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1202⟩⟩
  · intro i; fin_cases i
    · exact free1_0
    · exact free8_0
    · exact free14_0
    · exact free22_0
    · exact free32_0
    · exact free41_0
    · exact free42_2
    · exact free48_0
    · exact free58_0
    · exact free73_0
    · exact free82_0
    · exact free74_2
    · exact free111_0
    · exact free140_0
    · exact free145_0
    · exact free120_0
    · exact free199_0
    · exact free210_0
    · exact free181_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [358489998, 355676025, 357955892, 356172665, 356029029, 357939930, 356287998, 357713066, 166117348, 166446147, 166492495, 166390769, 70820441, 81594007, 70549171, 99176483, 110921019, 110957263, 130482600, 177821451, 238252397], [964207, 971920, 965671, 970559, 970953, 965715, 970243, 966337, 2299413, 2293945, 2293174, 2294866, 5662152, 4888405, 5683716, 3990288, 3546828, 3545570, 2979264, 2138422, 1545125],
  ![126469137375540, 1602423114628, 214427157300, 4219794740], 200511084029632841⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,3,3,3,7,7,7,7,15,13,15,11,10,10,8,6,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 7376180/1369, 132727294/2809, 85396081/400] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HighQuadraticFinal2
end Z6969Source0790

-- Source: Research6969.PhysicalChecks057
section Z6969Source0791
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src584 : Request := ⟨⟨⟨5700,7954,1716,433858⟩,5553838907981824,109473260530676⟩,25,2,1,308288,6⟩
theorem cover584 : PhysicalWindow.Cover (PhysicalWindow.Triangular src584) 2411 2314 [2315, 2320, 2334, 2373, 2411] := triangleCover (by decide +kernel)
def src585 : Request := ⟨⟨⟨1750,2442,527,135936⟩,161065121873920,975196209190⟩,0,2,1,308319,5⟩
theorem cover585 : PhysicalWindow.Cover (PhysicalWindow.Triangular src585) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src586 : Request := ⟨⟨⟨1750,2442,527,151194⟩,161065121873920,975196209190⟩,1,2,1,308319,5⟩
theorem cover586 : PhysicalWindow.Cover (PhysicalWindow.Triangular src586) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src587 : Request := ⟨⟨⟨1750,2442,527,170307⟩,161065121873920,975196209190⟩,2,2,1,308319,5⟩
theorem cover587 : PhysicalWindow.Cover (PhysicalWindow.Triangular src587) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src588 : Request := ⟨⟨⟨1750,2442,527,194947⟩,161065121873920,975196209190⟩,3,2,1,308319,5⟩
theorem cover588 : PhysicalWindow.Cover (PhysicalWindow.Triangular src588) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src589 : Request := ⟨⟨⟨1750,2442,527,227933⟩,161065121873920,975196209190⟩,4,2,1,308319,5⟩
theorem cover589 : PhysicalWindow.Cover (PhysicalWindow.Triangular src589) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src590 : Request := ⟨⟨⟨2100,2930,632,241770⟩,278060332482560,2019119590628⟩,6,2,1,308319,5⟩
theorem cover590 : PhysicalWindow.Cover (PhysicalWindow.Triangular src590) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src591 : Request := ⟨⟨⟨2600,3628,783,250353⟩,527755772952576,4745819470168⟩,8,2,1,308319,5⟩
theorem cover591 : PhysicalWindow.Cover (PhysicalWindow.Triangular src591) 2411 2314 [2315, 2321, 2338, 2385, 2411] := triangleCover (by decide +kernel)
def src592 : Request := ⟨⟨⟨3200,4465,947,278889⟩,970564165959680,10735676910569⟩,10,2,1,308319,5⟩
theorem cover592 : PhysicalWindow.Cover (PhysicalWindow.Triangular src592) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src593 : Request := ⟨⟨⟨3200,4465,963,323516⟩,983050615259136,10877088344236⟩,13,2,1,308319,5⟩
theorem cover593 : PhysicalWindow.Cover (PhysicalWindow.Triangular src593) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src594 : Request := ⟨⟨⟨3950,5512,1189,436835⟩,1848744952463360,25255771038451⟩,20,2,1,308319,5⟩
theorem cover594 : PhysicalWindow.Cover (PhysicalWindow.Triangular src594) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src595 : Request := ⟨⟨⟨5700,7954,1716,457591⟩,5553838907981824,109473260530676⟩,25,2,1,308319,5⟩
theorem cover595 : PhysicalWindow.Cover (PhysicalWindow.Triangular src595) 2411 2314 [2315, 2320, 2334, 2373, 2411] := triangleCover (by decide +kernel)
def src596 : Request := ⟨⟨⟨1750,2442,527,143030⟩,161065121873920,975196209190⟩,0,2,1,308344,4⟩
theorem cover596 : PhysicalWindow.Cover (PhysicalWindow.Triangular src596) 2411 2314 [2315, 2321, 2338, 2387, 2411] := triangleCover (by decide +kernel)
def src597 : Request := ⟨⟨⟨1750,2442,527,159083⟩,161065121873920,975196209190⟩,1,2,1,308344,4⟩
theorem cover597 : PhysicalWindow.Cover (PhysicalWindow.Triangular src597) 2411 2314 [2315, 2321, 2338, 2387, 2411] := triangleCover (by decide +kernel)
def src598 : Request := ⟨⟨⟨1750,2442,527,179190⟩,161065121873920,975196209190⟩,2,2,1,308344,4⟩
theorem cover598 : PhysicalWindow.Cover (PhysicalWindow.Triangular src598) 2411 2314 [2315, 2321, 2338, 2387, 2411] := triangleCover (by decide +kernel)
def src599 : Request := ⟨⟨⟨2100,2930,632,203615⟩,278060332482560,2019119590628⟩,4,2,1,308344,4⟩
theorem cover599 : PhysicalWindow.Cover (PhysicalWindow.Triangular src599) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source0791

-- Source: Research6969.PrefixNormalDataSeed4
section Z6969Source0792
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Research6969.NormalPrefixData.Seed4
open Lower6960
open Prefix6969Rescue
open TransitionPacket
open PhysicalCatalogue TransitionBanks

def plan : Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,4⟩
  bank i := ![bank245 143030, bank245 159083, bank245 179190, bank252 203615, bank270 225437, bank252 254356, bank303 280016, bank315 317933, bank315 366307, bank270 454999, bank332 415200] i
  reserve i := ![0, 1, 2, 4, 6, 6, 10, 13, 16, 13, 20] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 308344
  seedFloor := 4

theorem sources : plan.Sources 2314 2411 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank245 143030
    · exact rank245 159083
    · exact rank245 179190
    · exact rank252 203615
    · exact rank270 225437
    · exact rank252 254356
    · exact rank303 280016
    · exact rank315 317933
    · exact rank315 366307
    · exact rank270 454999
    · exact rank332 415200
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover596⟩
    · exact ⟨_, cover597⟩
    · exact ⟨_, cover598⟩
    · exact ⟨_, cover599⟩
    · exact ⟨_, cover601⟩
    · exact ⟨_, cover600⟩
    · exact ⟨_, cover602⟩
    · exact ⟨_, cover604⟩
    · exact ⟨_, cover605⟩
    · exact ⟨_, cover603⟩
    · exact ⟨_, cover606⟩

def price : NormalPrice := ⟨4, 95/100, 80/100, ![826579633500, 211761988700, 5650451680, 562538500], 29203605066442791⟩
theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

open Lower6960.Prefix6969MainCases.HighQuadraticFinal2 (plan price valid sources priced) in
def bounds : NormalBounds Lower6960.Prefix6969MainCases.HighQuadraticFinal2.plan Lower6960.Prefix6969MainCases.HighQuadraticFinal2.price
    plan price SmallCertificates.primary4 SmallCertificates.rescue4 where
  main_fee := by decide +kernel
  rescue_fee := by decide +kernel
  mainOrd := rfl
  mainSeed := rfl
  rescueOrd := rfl
  rescueSeed := rfl
  mainMass := by decide +kernel
  rescueMass := by decide +kernel
  mainGrade := 335
  rescueGrade := 315
  mainDegree := by decide +kernel
  rescueDegree := by decide +kernel


open Finset Polynomial
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2 (UsesSeed)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Far6969RescueGeometry (Model Family word)
open Research6966

theorem packet {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 4))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 4 ≤ seedDegree G)
    (floor : 308344 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (TransitionPacket.Pair F Crt G SmallCertificates.primary4 SmallCertificates.rescue4) :=
  TransitionPacket.of_normal F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal2.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal2.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal2.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor


theorem packet_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 4))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 4 ≤ seedDegree G)
    (floor : 308344 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ P : TransitionPacket.Pair F Crt G SmallCertificates.primary4 SmallCertificates.rescue4,
      P.mainGrade=335 ∧ P.rescueGrade=315 :=
  TransitionPacket.of_normal_with_grades F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal2.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal2.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal2.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor

end Research6969.NormalPrefixData.Seed4
end Z6969Source0792

-- Source: Research6969.PrefixMainDataHighQuadraticFinal3
section Z6969Source0793
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HighQuadraticFinal3
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 20, 14, 21, 20, 25, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank1 1559, bank8 1694, bank14 1831, bank23 1898, bank32 2243, bank41 2989, bank42 4552, bank48 2482, bank58 2557, bank73 5660, bank82 2965, bank74 6544, bank111 3583, bank140 3997, bank145 7920, bank120 36262, bank199 9241, bank210 11036, bank182 57760, bank174 148759, bank169 292467] i
  head := src1201
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![13949, 173536, 806270, 4473731],
    ![23965/2, 576625/4, 1305397/2, 6985209/2],
    ![17372/3, 624656/9, 629864, 3352561],
    ![3599, 334517/8, 3032186/9, 5217602/3],
    ![16211/9, 768919/36, 3504701/16, 18498021/16],
    ![24292/27, 945221/81, 4295035/36, 8216761/12],
    ![73478/121, 1219178/121, 112279, 8216761/12],
    ![73478/121, 1219178/121, 112279, 3411509/6],
    ![73478/121, 1011980/121, 4547068/49, 6538249/16],
    ![77324/147, 3395282/441, 7445651/98, 6538249/16],
    ![77324/147, 3395282/441, 7445651/98, 48904710/121],
    ![61324/121, 3395282/441, 7445651/98, 48904710/121],
    ![61324/121, 3049054/441, 6848341/98, 19699334/75],
    ![61324/121, 3049054/441, 6848341/98, 19699334/75],
    ![1640767/3362, 10391892/1681, 1605480/29, 19699334/75],
    ![667406/1681, 10391892/1681, 1605480/29, 19699334/75],
    ![667406/1681, 7347910/1323, 21050998/441, 85396081/400],
    ![667406/1681, 7324240/1369, 131799794/2809, 85396081/400],
    ![476343/1369, 7324240/1369, 131799794/2809, 85396081/400],
    ![462882/1369, 7324240/1369, 131799794/2809, 85396081/400],
    ![459151/1369, 7324240/1369, 131799794/2809, 85396081/400]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 2 5 308319 := by
  refine ⟨?_, rank154 8247, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1201⟩⟩
  · intro i; fin_cases i
    · exact free1_0
    · exact free8_0
    · exact free14_0
    · exact free23_0
    · exact free32_0
    · exact free41_0
    · exact free42_2
    · exact free48_0
    · exact free58_0
    · exact free73_0
    · exact free82_0
    · exact free74_2
    · exact free111_0
    · exact free140_0
    · exact free145_0
    · exact free120_0
    · exact free199_0
    · exact free210_0
    · exact free182_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [356571975, 356083778, 356387930, 356304246, 355800186, 356402962, 356114145, 354792226, 164460333, 164925175, 164956607, 164792818, 82129874, 80886550, 74108143, 98443680, 111143564, 111138776, 130141253, 177268647, 237830632], [969464, 970803, 969969, 970198, 971580, 969928, 970719, 974343, 2326969, 2319239, 2318716, 2321440, 4856578, 4930422, 5400796, 4021223, 3539101, 3539267, 2986749, 2145090, 1548594],
  ![126245256078240, 1602878922128, 214047568800, 4210799530], 199176348375005480⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,3,3,3,7,7,7,7,13,13,15,11,10,10,8,6,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 7324240/1369, 131799794/2809, 85396081/400] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HighQuadraticFinal3
end Z6969Source0793

-- Source: Research6969.PrefixNormalDataSeed5
section Z6969Source0794
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Research6969.NormalPrefixData.Seed5
open Lower6960
open Prefix6969Rescue
open TransitionPacket
open PhysicalCatalogue TransitionBanks

def plan : Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,5⟩
  bank i := ![bank245 135936, bank245 151194, bank245 170307, bank245 194947, bank245 227933, bank252 241770, bank270 250353, bank302 278889, bank303 323516, bank315 436835, bank347 457591] i
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 10, 13, 20, 25] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 308319
  seedFloor := 5

theorem sources : plan.Sources 2314 2411 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank245 135936
    · exact rank245 151194
    · exact rank245 170307
    · exact rank245 194947
    · exact rank245 227933
    · exact rank252 241770
    · exact rank270 250353
    · exact rank302 278889
    · exact rank303 323516
    · exact rank315 436835
    · exact rank347 457591
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover585⟩
    · exact ⟨_, cover586⟩
    · exact ⟨_, cover587⟩
    · exact ⟨_, cover588⟩
    · exact ⟨_, cover589⟩
    · exact ⟨_, cover590⟩
    · exact ⟨_, cover591⟩
    · exact ⟨_, cover592⟩
    · exact ⟨_, cover593⟩
    · exact ⟨_, cover594⟩
    · exact ⟨_, cover595⟩

def price : NormalPrice := ⟨5, 95/100, 80/100, ![1033224143760, 213040426912, 5394791393, 668038800], 27507301354127021⟩
theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

open Lower6960.Prefix6969MainCases.HighQuadraticFinal3 (plan price valid sources priced) in
def bounds : NormalBounds Lower6960.Prefix6969MainCases.HighQuadraticFinal3.plan Lower6960.Prefix6969MainCases.HighQuadraticFinal3.price
    plan price SmallCertificates.primary5 SmallCertificates.rescue5 where
  main_fee := by decide +kernel
  rescue_fee := by decide +kernel
  mainOrd := rfl
  mainSeed := rfl
  rescueOrd := rfl
  rescueSeed := rfl
  mainMass := by decide +kernel
  rescueMass := by decide +kernel
  mainGrade := 335
  rescueGrade := 319
  mainDegree := by decide +kernel
  rescueDegree := by decide +kernel


open Finset Polynomial
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2 (UsesSeed)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Far6969RescueGeometry (Model Family word)
open Research6966

theorem packet {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 5))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 5 ≤ seedDegree G)
    (floor : 308319 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (TransitionPacket.Pair F Crt G SmallCertificates.primary5 SmallCertificates.rescue5) :=
  TransitionPacket.of_normal F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal3.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal3.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal3.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor


theorem packet_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 5))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 5 ≤ seedDegree G)
    (floor : 308319 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ P : TransitionPacket.Pair F Crt G SmallCertificates.primary5 SmallCertificates.rescue5,
      P.mainGrade=335 ∧ P.rescueGrade=319 :=
  TransitionPacket.of_normal_with_grades F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal3.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal3.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal3.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor

end Research6969.NormalPrefixData.Seed5
end Z6969Source0794

-- Source: Research6969.PrefixMainDataHighQuadraticFinal4
section Z6969Source0795
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HighQuadraticFinal4
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 19
  reserve i := ![0, 1, 2, 3, 4, 6, 9, 14, 20, 14, 21, 21, 30, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank1 1559, bank8 1694, bank14 1831, bank23 1898, bank26 2102, bank38 2327, bank49 2815, bank62 3617, bank73 5660, bank82 2965, bank74 6544, bank116 3644, bank168 4492, bank148 6656, bank120 36262, bank199 9241, bank210 11036, bank182 57760, bank174 148759, bank169 292467] i
  head := src1200
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![14197, 172468, 800423, 4333670],
    ![23965/2, 572915/4, 1297023/2, 6895427/2],
    ![17372/3, 206876/3, 629864, 3352561],
    ![3599, 332291/8, 3012046/9, 15451618/9],
    ![60658/25, 715544/25, 211251, 1104601],
    ![69802/49, 810781/49, 3668874/25, 18944107/25],
    ![40539/50, 958869/100, 188605/2, 7924225/16],
    ![40539/50, 958869/100, 188605/2, 7924225/16],
    ![77324/147, 3377686/441, 7406113/98, 7924225/16],
    ![77324/147, 3377686/441, 7406113/98, 48276130/121],
    ![61324/121, 3377686/441, 7406113/98, 48276130/121],
    ![61324/121, 813745/121, 4719368/75, 59331608/225],
    ![61324/121, 813745/121, 4719368/75, 27427029/121],
    ![61324/121, 9931704/1681, 44683652/841, 27427029/121],
    ![667406/1681, 9931704/1681, 44683652/841, 27427029/121],
    ![667406/1681, 7293850/1323, 21050998/441, 225692943/1058],
    ![667406/1681, 7272300/1369, 130872294/2809, 225692943/1058],
    ![476343/1369, 7272300/1369, 130872294/2809, 225692943/1058],
    ![462882/1369, 7272300/1369, 130872294/2809, 225692943/1058],
    ![459151/1369, 7272300/1369, 130872294/2809, 225692943/1058]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 2 6 308288 := by
  refine ⟨?_, rank154 8141, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1200⟩⟩
  · intro i; fin_cases i
    · exact free1_0
    · exact free8_0
    · exact free14_0
    · exact free23_0
    · exact free26_0
    · exact free38_0
    · exact free49_0
    · exact free62_0
    · exact free73_0
    · exact free82_0
    · exact free74_2
    · exact free116_1
    · exact free168_0
    · exact free148_0
    · exact free120_0
    · exact free199_0
    · exact free210_0
    · exact free182_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [355475423, 353033621, 354550622, 354276382, 355167953, 352599506, 160834122, 160834842, 161602193, 161438929, 161395733, 118291330, 75486893, 68734385, 94927951, 109791379, 109771412, 129588449, 176715842, 237408867], [972470, 979164, 975005, 975757, 973313, 980354, 2387273, 2387261, 2374500, 2377215, 2377933, 3312000, 5298748, 5840521, 4169638, 3586051, 3586745, 2998872, 2151758, 1552062],
  ![126021374780940, 1603334729628, 213667980300, 4267285260], 197589459237142777⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,3,7,7,7,7,7,9,14,16,11,10,10,8,6,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 7272300/1369, 130872294/2809, 225692943/1058] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HighQuadraticFinal4
end Z6969Source0795

-- Source: Research6969.PhysicalChecks056
section Z6969Source0796
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src568 : Request := ⟨⟨⟨2100,2930,622,185441⟩,274699477319680,1994139134137⟩,4,2,1,308251,7⟩
theorem cover568 : PhysicalWindow.Cover (PhysicalWindow.Triangular src568) 2411 2314 [2317, 2329, 2363, 2411] := triangleCover (by decide +kernel)
def src569 : Request := ⟨⟨⟨2600,3628,783,234698⟩,527755772952576,4745819470168⟩,8,2,1,308251,7⟩
theorem cover569 : PhysicalWindow.Cover (PhysicalWindow.Triangular src569) 2411 2314 [2319, 2335, 2380, 2411] := triangleCover (by decide +kernel)
def src570 : Request := ⟨⟨⟨3200,4465,947,264035⟩,970564165959680,10735676910569⟩,10,2,1,308251,7⟩
theorem cover570 : PhysicalWindow.Cover (PhysicalWindow.Triangular src570) 2411 2314 [2320, 2339, 2393, 2411] := triangleCover (by decide +kernel)
def src571 : Request := ⟨⟨⟨3200,4465,963,297039⟩,983050615259136,10877088344236⟩,13,2,1,308251,7⟩
theorem cover571 : PhysicalWindow.Cover (PhysicalWindow.Triangular src571) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src572 : Request := ⟨⟨⟨4800,6698,1421,375939⟩,3274891856707584,54342858960622⟩,20,2,1,308251,7⟩
theorem cover572 : PhysicalWindow.Cover (PhysicalWindow.Triangular src572) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src573 : Request := ⟨⟨⟨5700,7954,1716,422931⟩,5553838907981824,109473260530676⟩,25,2,1,308251,7⟩
theorem cover573 : PhysicalWindow.Cover (PhysicalWindow.Triangular src573) 2411 2314 [2318, 2331, 2367, 2411] := triangleCover (by decide +kernel)
def src574 : Request := ⟨⟨⟨1750,2442,527,128868⟩,161065121873920,975196209190⟩,0,2,1,308288,6⟩
theorem cover574 : PhysicalWindow.Cover (PhysicalWindow.Triangular src574) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src575 : Request := ⟨⟨⟨1750,2442,527,143332⟩,161065121873920,975196209190⟩,1,2,1,308288,6⟩
theorem cover575 : PhysicalWindow.Cover (PhysicalWindow.Triangular src575) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src576 : Request := ⟨⟨⟨1750,2442,527,161452⟩,161065121873920,975196209190⟩,2,2,1,308288,6⟩
theorem cover576 : PhysicalWindow.Cover (PhysicalWindow.Triangular src576) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src577 : Request := ⟨⟨⟨1750,2442,527,184812⟩,161065121873920,975196209190⟩,3,2,1,308288,6⟩
theorem cover577 : PhysicalWindow.Cover (PhysicalWindow.Triangular src577) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src578 : Request := ⟨⟨⟨1750,2442,527,216095⟩,161065121873920,975196209190⟩,4,2,1,308288,6⟩
theorem cover578 : PhysicalWindow.Cover (PhysicalWindow.Triangular src578) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src579 : Request := ⟨⟨⟨2100,2930,632,229220⟩,278060332482560,2019119590628⟩,6,2,1,308288,6⟩
theorem cover579 : PhysicalWindow.Cover (PhysicalWindow.Triangular src579) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src580 : Request := ⟨⟨⟨2600,3628,783,237343⟩,527755772952576,4745819470168⟩,8,2,1,308288,6⟩
theorem cover580 : PhysicalWindow.Cover (PhysicalWindow.Triangular src580) 2411 2314 [2315, 2321, 2338, 2385, 2411] := triangleCover (by decide +kernel)
def src581 : Request := ⟨⟨⟨3200,4465,947,264942⟩,970564165959680,10735676910569⟩,10,2,1,308288,6⟩
theorem cover581 : PhysicalWindow.Cover (PhysicalWindow.Triangular src581) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src582 : Request := ⟨⟨⟨3200,4465,963,306734⟩,983050615259136,10877088344236⟩,13,2,1,308288,6⟩
theorem cover582 : PhysicalWindow.Cover (PhysicalWindow.Triangular src582) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src583 : Request := ⟨⟨⟨3950,5512,1189,414185⟩,1848744952463360,25255771038451⟩,20,2,1,308288,6⟩
theorem cover583 : PhysicalWindow.Cover (PhysicalWindow.Triangular src583) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source0796

end Merged_Z6969Pack0631

-- merged module Z6969Pack0632
section Merged_Z6969Pack0632

-- Source: Research6969.PrefixNormalDataSeed6
section Z6969Source0797
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Research6969.NormalPrefixData.Seed6
open Lower6960
open Prefix6969Rescue
open TransitionPacket
open PhysicalCatalogue TransitionBanks

def plan : Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,6⟩
  bank i := ![bank245 128868, bank245 143332, bank245 161452, bank245 184812, bank245 216095, bank252 229220, bank270 237343, bank302 264942, bank303 306734, bank315 414185, bank347 433858] i
  reserve i := ![0, 1, 2, 3, 4, 6, 8, 10, 13, 20, 25] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 308288
  seedFloor := 6

theorem sources : plan.Sources 2314 2411 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank245 128868
    · exact rank245 143332
    · exact rank245 161452
    · exact rank245 184812
    · exact rank245 216095
    · exact rank252 229220
    · exact rank270 237343
    · exact rank302 264942
    · exact rank303 306734
    · exact rank315 414185
    · exact rank347 433858
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover574⟩
    · exact ⟨_, cover575⟩
    · exact ⟨_, cover576⟩
    · exact ⟨_, cover577⟩
    · exact ⟨_, cover578⟩
    · exact ⟨_, cover579⟩
    · exact ⟨_, cover580⟩
    · exact ⟨_, cover581⟩
    · exact ⟨_, cover582⟩
    · exact ⟨_, cover583⟩
    · exact ⟨_, cover584⟩

def price : NormalPrice := ⟨6, 95/100, 80/100, ![1239868654020, 214318865124, 5140143320, 668038800], 25709075698271047⟩
theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

open Lower6960.Prefix6969MainCases.HighQuadraticFinal4 (plan price valid sources priced) in
def bounds : NormalBounds Lower6960.Prefix6969MainCases.HighQuadraticFinal4.plan Lower6960.Prefix6969MainCases.HighQuadraticFinal4.price
    plan price SmallCertificates.primary6 SmallCertificates.rescue6 where
  main_fee := by decide +kernel
  rescue_fee := by decide +kernel
  mainOrd := rfl
  mainSeed := rfl
  rescueOrd := rfl
  rescueSeed := rfl
  mainMass := by decide +kernel
  rescueMass := by decide +kernel
  mainGrade := 335
  rescueGrade := 319
  mainDegree := by decide +kernel
  rescueDegree := by decide +kernel


open Finset Polynomial
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2 (UsesSeed)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Far6969RescueGeometry (Model Family word)
open Research6966

theorem packet {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 6))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 6 ≤ seedDegree G)
    (floor : 308288 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (TransitionPacket.Pair F Crt G SmallCertificates.primary6 SmallCertificates.rescue6) :=
  TransitionPacket.of_normal F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal4.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal4.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal4.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor


theorem packet_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 6))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 6 ≤ seedDegree G)
    (floor : 308288 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ P : TransitionPacket.Pair F Crt G SmallCertificates.primary6 SmallCertificates.rescue6,
      P.mainGrade=335 ∧ P.rescueGrade=319 :=
  TransitionPacket.of_normal_with_grades F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal4.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal4.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal4.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor

end Research6969.NormalPrefixData.Seed6
end Z6969Source0797

-- Source: Research6969.PrefixMainDataHighQuadraticFinal5
section Z6969Source0798
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HighQuadraticFinal5
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 17
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 14, 14, 21, 20, 41, 41, 76, 76, 76, 76] i
  bank i := ![bank1 1559, bank8 1694, bank14 1831, bank20 1970, bank25 2129, bank32 2243, bank44 2409, bank53 2871, bank62 3617, bank82 2965, bank84 5564, bank116 3482, bank121 32187, bank148 6656, bank210 11036, bank182 57760, bank174 148759, bank169 292467] i
  head := src1199
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![14261, 171509, 797702, 4182968],
    ![23965/2, 569275/4, 1288807/2, 6807339/2],
    ![17372/3, 616676/9, 629864, 3352561],
    ![28151/8, 664417/16, 3015722/9, 1759210],
    ![60148/25, 715558/25, 210771, 4532641/4],
    ![16211/9, 759049/36, 210771, 18026991/16],
    ![18775/16, 851565/64, 396682/3, 644809],
    ![86808/121, 1002438/121, 4498920/49, 23074227/49],
    ![86808/121, 1002438/121, 4498920/49, 23074227/49],
    ![86808/121, 1002438/121, 455424/5, 47659410/121],
    ![63754/121, 1803673/242, 543881/8, 47659410/121],
    ![63754/121, 3080612/441, 543881/8, 6218852/25],
    ![671521/1681, 3080612/441, 543881/8, 6218852/25],
    ![671521/1681, 9862648/1681, 44375396/841, 6218852/25],
    ![671521/1681, 7221340/1369, 129962294/2809, 17246509/81],
    ![476343/1369, 7221340/1369, 129962294/2809, 17246509/81],
    ![462882/1369, 7221340/1369, 129962294/2809, 17246509/81],
    ![459151/1369, 7221340/1369, 129962294/2809, 17246509/81]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 2 7 308251 := by
  refine ⟨?_, rank154 8037, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1199⟩⟩
  · intro i; fin_cases i
    · exact free1_0
    · exact free8_0
    · exact free14_0
    · exact free20_0
    · exact free25_0
    · exact free32_0
    · exact free44_0
    · exact free53_0
    · exact free62_0
    · exact free82_0
    · exact free84_0
    · exact free116_0
    · exact free121_0
    · exact free148_0
    · exact free210_0
    · exact free182_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [353473415, 352287920, 352911962, 351854640, 351964230, 352168777, 353062695, 183370907, 183338996, 182881533, 182944097, 80010096, 77453226, 109988668, 109875656, 129046075, 176173469, 236995059], [977958, 981208, 979497, 982396, 982095, 981535, 979084, 2071489, 2071874, 2077391, 2076637, 4986293, 5162917, 3579201, 3583125, 3011295, 2158299, 1555465],
  ![125801717218380, 1603781633796, 213295553100, 4262978650], 196411447952779468⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,3,3,6,6,6,6,14,14,10,10,9,6,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 7221340/1369, 129962294/2809, 17246509/81] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HighQuadraticFinal5
end Z6969Source0798

-- Source: Research6969.PhysicalChecks055
section Z6969Source0799
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src552 : Request := ⟨⟨⟨1750,2442,527,115771⟩,161065121873920,975196209190⟩,0,2,1,308209,8⟩
theorem cover552 : PhysicalWindow.Cover (PhysicalWindow.Triangular src552) 2411 2314 [2316, 2325, 2351, 2411] := triangleCover (by decide +kernel)
def src553 : Request := ⟨⟨⟨1750,2442,527,130242⟩,161065121873920,975196209190⟩,1,2,1,308209,8⟩
theorem cover553 : PhysicalWindow.Cover (PhysicalWindow.Triangular src553) 2411 2314 [2317, 2329, 2363, 2411] := triangleCover (by decide +kernel)
def src554 : Request := ⟨⟨⟨1750,2442,527,146522⟩,161065121873920,975196209190⟩,2,2,1,308209,8⟩
theorem cover554 : PhysicalWindow.Cover (PhysicalWindow.Triangular src554) 2411 2314 [2317, 2328, 2360, 2411] := triangleCover (by decide +kernel)
def src555 : Request := ⟨⟨⟨2100,2930,632,164837⟩,278060332482560,2019119590628⟩,4,2,1,308209,8⟩
theorem cover555 : PhysicalWindow.Cover (PhysicalWindow.Triangular src555) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src556 : Request := ⟨⟨⟨2100,2930,632,208621⟩,278060332482560,2019119590628⟩,6,2,1,308209,8⟩
theorem cover556 : PhysicalWindow.Cover (PhysicalWindow.Triangular src556) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src557 : Request := ⟨⟨⟨2600,3628,783,185441⟩,527755772952576,4745819470168⟩,6,2,1,308209,8⟩
theorem cover557 : PhysicalWindow.Cover (PhysicalWindow.Triangular src557) 2411 2314 [2317, 2329, 2362, 2411] := triangleCover (by decide +kernel)
def src558 : Request := ⟨⟨⟨2600,3628,783,264035⟩,527755772952576,4745819470168⟩,10,2,1,308209,8⟩
theorem cover558 : PhysicalWindow.Cover (PhysicalWindow.Triangular src558) 2411 2314 [2318, 2332, 2371, 2411] := triangleCover (by decide +kernel)
def src559 : Request := ⟨⟨⟨3200,4465,963,234698⟩,983050615259136,10877088344236⟩,10,2,1,308209,8⟩
theorem cover559 : PhysicalWindow.Cover (PhysicalWindow.Triangular src559) 2411 2314 [2319, 2336, 2383, 2411] := triangleCover (by decide +kernel)
def src560 : Request := ⟨⟨⟨3950,5512,1189,264035⟩,1848744952463360,25255771038451⟩,13,2,1,308209,8⟩
theorem cover560 : PhysicalWindow.Cover (PhysicalWindow.Triangular src560) 2411 2314 [2318, 2332, 2371, 2411] := triangleCover (by decide +kernel)
def src561 : Request := ⟨⟨⟨3950,5512,1189,297039⟩,1848744952463360,25255771038451⟩,16,2,1,308209,8⟩
theorem cover561 : PhysicalWindow.Cover (PhysicalWindow.Triangular src561) 2411 2314 [2316, 2324, 2346, 2408, 2411] := triangleCover (by decide +kernel)
def src562 : Request := ⟨⟨⟨4800,6698,1445,334168⟩,3317023033262080,55058665830093⟩,20,2,1,308209,8⟩
theorem cover562 : PhysicalWindow.Cover (PhysicalWindow.Triangular src562) 2411 2314 [2315, 2321, 2337, 2382, 2411] := triangleCover (by decide +kernel)
def src563 : Request := ⟨⟨⟨1450,2023,436,130242⟩,91566841790464,459151377566⟩,0,2,1,308251,7⟩
theorem cover563 : PhysicalWindow.Cover (PhysicalWindow.Triangular src563) 2411 2314 [2316, 2325, 2351, 2411] := triangleCover (by decide +kernel)
def src564 : Request := ⟨⟨⟨1750,2442,518,146522⟩,158964379549696,962176592398⟩,1,2,1,308251,7⟩
theorem cover564 : PhysicalWindow.Cover (PhysicalWindow.Triangular src564) 2411 2314 [2318, 2333, 2376, 2411] := triangleCover (by decide +kernel)
def src565 : Request := ⟨⟨⟨2100,2930,632,146522⟩,278060332482560,2019119590628⟩,2,2,1,308251,7⟩
theorem cover565 : PhysicalWindow.Cover (PhysicalWindow.Triangular src565) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src566 : Request := ⟨⟨⟨2100,2930,622,164837⟩,274699477319680,1994139134137⟩,3,2,1,308251,7⟩
theorem cover566 : PhysicalWindow.Cover (PhysicalWindow.Triangular src566) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
def src567 : Request := ⟨⟨⟨1750,2442,527,208621⟩,161065121873920,975196209190⟩,4,2,1,308251,7⟩
theorem cover567 : PhysicalWindow.Cover (PhysicalWindow.Triangular src567) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source0799

-- Source: Research6969.PrefixNormalDataSeed7
section Z6969Source0800
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Research6969.NormalPrefixData.Seed7
open Lower6960
open Prefix6969Rescue
open TransitionPacket
open PhysicalCatalogue TransitionBanks

def plan : Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,7⟩
  bank i := ![bank236 130242, bank244 146522, bank252 146522, bank251 164837, bank251 185441, bank245 208621, bank270 234698, bank302 264035, bank303 297039, bank331 375939, bank347 422931] i
  reserve i := ![0, 1, 2, 3, 4, 4, 8, 10, 13, 20, 25] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 308251
  seedFloor := 7

theorem sources : plan.Sources 2314 2411 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank236 130242
    · exact rank244 146522
    · exact rank252 146522
    · exact rank251 164837
    · exact rank251 185441
    · exact rank245 208621
    · exact rank270 234698
    · exact rank302 264035
    · exact rank303 297039
    · exact rank331 375939
    · exact rank347 422931
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover563⟩
    · exact ⟨_, cover564⟩
    · exact ⟨_, cover565⟩
    · exact ⟨_, cover566⟩
    · exact ⟨_, cover568⟩
    · exact ⟨_, cover567⟩
    · exact ⟨_, cover569⟩
    · exact ⟨_, cover570⟩
    · exact ⟨_, cover571⟩
    · exact ⟨_, cover572⟩
    · exact ⟨_, cover573⟩

def price : NormalPrice := ⟨7, 95/100, 80/100, ![1446513164280, 215597303336, 5189352179, 668038800], 26081428904694984⟩
theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

open Lower6960.Prefix6969MainCases.HighQuadraticFinal5 (plan price valid sources priced) in
def bounds : NormalBounds Lower6960.Prefix6969MainCases.HighQuadraticFinal5.plan Lower6960.Prefix6969MainCases.HighQuadraticFinal5.price
    plan price SmallCertificates.primary7 SmallCertificates.rescue7 where
  main_fee := by decide +kernel
  rescue_fee := by decide +kernel
  mainOrd := rfl
  mainSeed := rfl
  rescueOrd := rfl
  rescueSeed := rfl
  mainMass := by decide +kernel
  rescueMass := by decide +kernel
  mainGrade := 335
  rescueGrade := 371
  mainDegree := by decide +kernel
  rescueDegree := by decide +kernel


open Finset Polynomial
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2 (UsesSeed)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Far6969RescueGeometry (Model Family word)
open Research6966

theorem packet {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 7))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 7 ≤ seedDegree G)
    (floor : 308251 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (TransitionPacket.Pair F Crt G SmallCertificates.primary7 SmallCertificates.rescue7) :=
  TransitionPacket.of_normal F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal5.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal5.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal5.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor


theorem packet_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 7))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 7 ≤ seedDegree G)
    (floor : 308251 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ P : TransitionPacket.Pair F Crt G SmallCertificates.primary7 SmallCertificates.rescue7,
      P.mainGrade=335 ∧ P.rescueGrade=371 :=
  TransitionPacket.of_normal_with_grades F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal5.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal5.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal5.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor

end Research6969.NormalPrefixData.Seed7
end Z6969Source0800

-- Source: Research6969.PrefixMainDataHighQuadraticFinal6
section Z6969Source0801
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HighQuadraticFinal6
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 20
  reserve i := ![0, 1, 2, 3, 5, 8, 10, 8, 10, 21, 14, 21, 20, 30, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank4 1470, bank8 1694, bank14 1831, bank23 1898, bank32 2243, bank41 2989, bank42 4552, bank48 2482, bank61 2536, bank84 5564, bank85 2903, bank74 6544, bank115 3521, bank144 4704, bank148 6656, bank120 36262, bank198 9780, bank210 11036, bank183 54742, bank174 148759, bank169 292467] i
  head := src1198
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
  historyValues := [![14337, 171166, 797731, 4262233],
    ![23965/2, 565635/4, 1280591/2, 6719251/2],
    ![17372/3, 612724/9, 629864, 3352561],
    ![3599, 327923/8, 990842/3, 15056834/9],
    ![16211/9, 251387/12, 3437191/16, 17793719/16],
    ![24292/27, 928579/81, 4219361/36, 23711737/36],
    ![73478/121, 1202222/121, 5425997/49, 23711737/36],
    ![73478/121, 1202222/121, 5425997/49, 9844853/18],
    ![73478/121, 994363/121, 4456687/49, 401956],
    ![63754/121, 1794625/242, 543881/8, 401956],
    ![63754/121, 1794625/242, 543881/8, 46058998/121],
    ![61324/121, 1794625/242, 543881/8, 46058998/121],
    ![61324/121, 3021730/441, 543881/8, 253009],
    ![61324/121, 1981697/300, 1272419/21, 27987624/121],
    ![61324/121, 9793592/1681, 44067140/841, 27987624/121],
    ![667406/1681, 9793592/1681, 44067140/841, 27987624/121],
    ![667406/1681, 7164772/1323, 32219734/675, 116377110/529],
    ![667406/1681, 7170380/1369, 129052294/2809, 7612081/36],
    ![954471/2738, 7170380/1369, 129052294/2809, 7612081/36],
    ![462882/1369, 7170380/1369, 129052294/2809, 7612081/36],
    ![459151/1369, 7170380/1369, 129052294/2809, 7612081/36]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 2 8 308209 := by
  refine ⟨?_, rank154 7933, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1198⟩⟩
  · intro i; fin_cases i
    · exact free4_0
    · exact free8_0
    · exact free14_0
    · exact free23_0
    · exact free32_0
    · exact free41_0
    · exact free42_2
    · exact free48_0
    · exact free61_0
    · exact free84_0
    · exact free85_0
    · exact free74_2
    · exact free115_0
    · exact free144_0
    · exact free148_0
    · exact free120_0
    · exact free198_0
    · exact free210_0
    · exact free183_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [352391623, 350761234, 351017448, 350307991, 350891832, 351604621, 351720504, 350261632, 168561101, 169026130, 169192221, 168579809, 117248868, 74694934, 74594654, 93387963, 108370948, 108371601, 128600683, 175631095, 236581252], [980924, 985393, 984691, 986635, 985035, 983081, 982763, 986762, 2258774, 2251040, 2248278, 2258462, 3341148, 5354149, 5362121, 4245422, 3635371, 3635349, 3023748, 2164841, 1558868],
  ![125582060186640, 1604228541248, 212923126800, 4329375720], 195199211400478228⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,3,3,3,7,7,7,7,9,15,15,12,10,10,9,6,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 7170380/1369, 129052294/2809, 7612081/36] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HighQuadraticFinal6
end Z6969Source0801

-- Source: Research6969.PrefixNormalDataSeed8
section Z6969Source0802
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Research6969.NormalPrefixData.Seed8
open Lower6960
open Prefix6969Rescue
open TransitionPacket
open PhysicalCatalogue TransitionBanks

def plan : Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,8⟩
  bank i := ![bank245 115771, bank245 130242, bank245 146522, bank252 164837, bank270 185441, bank252 208621, bank270 264035, bank303 234698, bank315 264035, bank315 297039, bank332 334168] i
  reserve i := ![0, 1, 2, 4, 6, 6, 10, 10, 13, 16, 20] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 308209
  seedFloor := 8

theorem sources : plan.Sources 2314 2411 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank245 115771
    · exact rank245 130242
    · exact rank245 146522
    · exact rank252 164837
    · exact rank270 185441
    · exact rank252 208621
    · exact rank270 264035
    · exact rank303 234698
    · exact rank315 264035
    · exact rank315 297039
    · exact rank332 334168
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover552⟩
    · exact ⟨_, cover553⟩
    · exact ⟨_, cover554⟩
    · exact ⟨_, cover555⟩
    · exact ⟨_, cover557⟩
    · exact ⟨_, cover556⟩
    · exact ⟨_, cover558⟩
    · exact ⟨_, cover559⟩
    · exact ⟨_, cover560⟩
    · exact ⟨_, cover561⟩
    · exact ⟨_, cover562⟩

def price : NormalPrice := ⟨8, 95/100, 80/100, ![1653157143720, 216875738264, 4671296768, 562538500], 22562095260867864⟩
theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

open Lower6960.Prefix6969MainCases.HighQuadraticFinal6 (plan price valid sources priced) in
def bounds : NormalBounds Lower6960.Prefix6969MainCases.HighQuadraticFinal6.plan Lower6960.Prefix6969MainCases.HighQuadraticFinal6.price
    plan price SmallCertificates.primary8 SmallCertificates.rescue8 where
  main_fee := by decide +kernel
  rescue_fee := by decide +kernel
  mainOrd := rfl
  mainSeed := rfl
  rescueOrd := rfl
  rescueSeed := rfl
  mainMass := by decide +kernel
  rescueMass := by decide +kernel
  mainGrade := 335
  rescueGrade := 387
  mainDegree := by decide +kernel
  rescueDegree := by decide +kernel


open Finset Polynomial
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2 (UsesSeed)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Far6969RescueGeometry (Model Family word)
open Research6966

theorem packet {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 8))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 8 ≤ seedDegree G)
    (floor : 308209 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (TransitionPacket.Pair F Crt G SmallCertificates.primary8 SmallCertificates.rescue8) :=
  TransitionPacket.of_normal F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal6.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal6.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal6.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor


theorem packet_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 8))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 8 ≤ seedDegree G)
    (floor : 308209 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ P : TransitionPacket.Pair F Crt G SmallCertificates.primary8 SmallCertificates.rescue8,
      P.mainGrade=335 ∧ P.rescueGrade=387 :=
  TransitionPacket.of_normal_with_grades F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal6.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal6.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal6.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor

end Research6969.NormalPrefixData.Seed8
end Z6969Source0802

-- Source: Research6969.PrefixMainDataHighQuadraticFinal7
section Z6969Source0803
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HighQuadraticFinal7
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 20, 16, 21, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank2 1529, bank8 1694, bank14 1831, bank23 1898, bank25 2129, bank32 2243, bank44 2409, bank53 2871, bank65 3612, bank73 5660, bank95 3103, bank137 3540, bank121 32187, bank152 6378, bank198 9780, bank183 54742, bank210 11036, bank174 148759, bank169 292467] i
  head := src1197
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![14389, 169810, 794204, 4132960],
    ![23965/2, 281015/2, 636227, 3316005],
    ![17372/3, 608810/9, 629864, 3316005],
    ![3599, 40720, 2952956/9, 1651260],
    ![60148/25, 28258, 210771, 4532641/4],
    ![16211/9, 187330/9, 210771, 8781345/8],
    ![18775/16, 210045/16, 396682/3, 644809],
    ![86808/121, 989190/121, 4440132/49, 22479930/49],
    ![86808/121, 989190/121, 4440132/49, 22479930/49],
    ![77324/147, 3326060/441, 3645055/49, 22479930/49],
    ![77324/147, 3326060/441, 3645055/49, 1349805/4],
    ![77324/147, 816180/121, 959464/15, 246384],
    ![671521/1681, 816180/121, 959464/15, 246384],
    ![671521/1681, 9755400/1681, 43780344/841, 6888240/29],
    ![671521/1681, 2371640/441, 2133164/45, 114866100/529],
    ![954471/2738, 2371640/441, 2133164/45, 114866100/529],
    ![954471/2738, 192430/37, 128151044/2809, 7612081/36],
    ![462882/1369, 192430/37, 128151044/2809, 7612081/36],
    ![459151/1369, 192430/37, 128151044/2809, 7612081/36]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 2 9 308161 := by
  refine ⟨?_, rank154 7830, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1197⟩⟩
  · intro i; fin_cases i
    · exact free2_0
    · exact free8_0
    · exact free14_0
    · exact free23_0
    · exact free25_0
    · exact free32_0
    · exact free44_0
    · exact free53_0
    · exact free65_0
    · exact free73_0
    · exact free95_0
    · exact free137_0
    · exact free121_0
    · exact free152_0
    · exact free198_0
    · exact free183_0
    · exact free210_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [349906170, 348895978, 349103355, 349450810, 349584877, 349677924, 349559947, 159820211, 159389321, 159548261, 159570258, 80904054, 82992655, 92827701, 103561999, 103602567, 128063524, 175093936, 236171424], [987737, 990506, 989937, 988985, 988618, 988362, 988686, 2404134, 2411300, 2408657, 2408291, 4929383, 4805335, 4273680, 3805156, 3803443, 3038767, 2171320, 1562238],
  ![125364515287680, 1604671529496, 212554281600, 4527137230], 193333885834127928⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,3,3,7,7,7,7,13,13,12,11,11,9,6,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 192430/37, 128151044/2809, 7612081/36] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HighQuadraticFinal7
end Z6969Source0803

-- Source: Research6969.PhysicalChecks054
section Z6969Source0804
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src536 : Request := ⟨⟨⟨3200,4465,963,208621⟩,983050615259136,10877088344236⟩,10,2,1,308107,10⟩
theorem cover536 : PhysicalWindow.Cover (PhysicalWindow.Triangular src536) 2411 2314 [2320, 2339, 2392, 2411] := triangleCover (by decide +kernel)
def src537 : Request := ⟨⟨⟨2600,3628,783,334168⟩,527755772952576,4745819470168⟩,13,2,1,308107,10⟩
theorem cover537 : PhysicalWindow.Cover (PhysicalWindow.Triangular src537) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src538 : Request := ⟨⟨⟨3950,5512,1189,234698⟩,1848744952463360,25255771038451⟩,13,2,1,308107,10⟩
theorem cover538 : PhysicalWindow.Cover (PhysicalWindow.Triangular src538) 2411 2314 [2319, 2336, 2383, 2411] := triangleCover (by decide +kernel)
def src539 : Request := ⟨⟨⟨3950,5512,1189,264035⟩,1848744952463360,25255771038451⟩,16,2,1,308107,10⟩
theorem cover539 : PhysicalWindow.Cover (PhysicalWindow.Triangular src539) 2411 2314 [2317, 2328, 2358, 2411] := triangleCover (by decide +kernel)
def src540 : Request := ⟨⟨⟨4800,6698,1445,297039⟩,3317023033262080,55058665830093⟩,20,2,1,308107,10⟩
theorem cover540 : PhysicalWindow.Cover (PhysicalWindow.Triangular src540) 2411 2314 [2316, 2324, 2347, 2410, 2411] := triangleCover (by decide +kernel)
def src541 : Request := ⟨⟨⟨1450,2023,436,115771⟩,91566841790464,459151377566⟩,0,2,1,308161,9⟩
theorem cover541 : PhysicalWindow.Cover (PhysicalWindow.Triangular src541) 2411 2314 [2317, 2328, 2360, 2411] := triangleCover (by decide +kernel)
def src542 : Request := ⟨⟨⟨1750,2442,518,130242⟩,158964379549696,962176592398⟩,1,2,1,308161,9⟩
theorem cover542 : PhysicalWindow.Cover (PhysicalWindow.Triangular src542) 2411 2314 [2318, 2333, 2376, 2411] := triangleCover (by decide +kernel)
def src543 : Request := ⟨⟨⟨2100,2930,632,130242⟩,278060332482560,2019119590628⟩,2,2,1,308161,9⟩
theorem cover543 : PhysicalWindow.Cover (PhysicalWindow.Triangular src543) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src544 : Request := ⟨⟨⟨2100,2930,632,146522⟩,278060332482560,2019119590628⟩,3,2,1,308161,9⟩
theorem cover544 : PhysicalWindow.Cover (PhysicalWindow.Triangular src544) 2411 2314 [2320, 2339, 2393, 2411] := triangleCover (by decide +kernel)
def src545 : Request := ⟨⟨⟨1750,2442,527,185441⟩,161065121873920,975196209190⟩,4,2,1,308161,9⟩
theorem cover545 : PhysicalWindow.Cover (PhysicalWindow.Triangular src545) 2411 2314 [2317, 2328, 2360, 2411] := triangleCover (by decide +kernel)
def src546 : Request := ⟨⟨⟨2100,2930,622,164837⟩,274699477319680,1994139134137⟩,4,2,1,308161,9⟩
theorem cover546 : PhysicalWindow.Cover (PhysicalWindow.Triangular src546) 2411 2314 [2317, 2329, 2363, 2411] := triangleCover (by decide +kernel)
def src547 : Request := ⟨⟨⟨2600,3628,783,208621⟩,527755772952576,4745819470168⟩,8,2,1,308161,9⟩
theorem cover547 : PhysicalWindow.Cover (PhysicalWindow.Triangular src547) 2411 2314 [2319, 2336, 2384, 2411] := triangleCover (by decide +kernel)
def src548 : Request := ⟨⟨⟨3200,4465,947,234698⟩,970564165959680,10735676910569⟩,10,2,1,308161,9⟩
theorem cover548 : PhysicalWindow.Cover (PhysicalWindow.Triangular src548) 2411 2314 [2319, 2336, 2385, 2411] := triangleCover (by decide +kernel)
def src549 : Request := ⟨⟨⟨3200,4465,963,264035⟩,983050615259136,10877088344236⟩,13,2,1,308161,9⟩
theorem cover549 : PhysicalWindow.Cover (PhysicalWindow.Triangular src549) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src550 : Request := ⟨⟨⟨3200,4465,963,334168⟩,983050615259136,10877088344236⟩,16,2,1,308161,9⟩
theorem cover550 : PhysicalWindow.Cover (PhysicalWindow.Triangular src550) 2411 2314 [2316, 2325, 2350, 2411] := triangleCover (by decide +kernel)
def src551 : Request := ⟨⟨⟨4800,6698,1421,334168⟩,3274891856707584,54342858960622⟩,20,2,1,308161,9⟩
theorem cover551 : PhysicalWindow.Cover (PhysicalWindow.Triangular src551) 2411 2314 [2316, 2324, 2347, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source0804

-- Source: Research6969.PrefixNormalDataSeed9
section Z6969Source0805
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Research6969.NormalPrefixData.Seed9
open Lower6960
open Prefix6969Rescue
open TransitionPacket
open PhysicalCatalogue TransitionBanks

def plan : Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,9⟩
  bank i := ![bank236 115771, bank244 130242, bank252 130242, bank252 146522, bank251 164837, bank245 185441, bank270 208621, bank302 234698, bank303 264035, bank331 334168, bank303 334168] i
  reserve i := ![0, 1, 2, 3, 4, 4, 8, 10, 13, 20, 16] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 308161
  seedFloor := 9

theorem sources : plan.Sources 2314 2411 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank236 115771
    · exact rank244 130242
    · exact rank252 130242
    · exact rank252 146522
    · exact rank251 164837
    · exact rank245 185441
    · exact rank270 208621
    · exact rank302 234698
    · exact rank303 264035
    · exact rank331 334168
    · exact rank303 334168
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover541⟩
    · exact ⟨_, cover542⟩
    · exact ⟨_, cover543⟩
    · exact ⟨_, cover544⟩
    · exact ⟨_, cover546⟩
    · exact ⟨_, cover545⟩
    · exact ⟨_, cover547⟩
    · exact ⟨_, cover548⟩
    · exact ⟨_, cover549⟩
    · exact ⟨_, cover551⟩
    · exact ⟨_, cover550⟩

def price : NormalPrice := ⟨9, 95/100, 80/100, ![1859801653980, 218154176476, 4978671019, 553195300], 22436662858301116⟩
theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

open Lower6960.Prefix6969MainCases.HighQuadraticFinal7 (plan price valid sources priced) in
def bounds : NormalBounds Lower6960.Prefix6969MainCases.HighQuadraticFinal7.plan Lower6960.Prefix6969MainCases.HighQuadraticFinal7.price
    plan price SmallCertificates.primary9 SmallCertificates.rescue9 where
  main_fee := by decide +kernel
  rescue_fee := by decide +kernel
  mainOrd := rfl
  mainSeed := rfl
  rescueOrd := rfl
  rescueSeed := rfl
  mainMass := by decide +kernel
  rescueMass := by decide +kernel
  mainGrade := 335
  rescueGrade := 319
  mainDegree := by decide +kernel
  rescueDegree := by decide +kernel


open Finset Polynomial
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2 (UsesSeed)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Far6969RescueGeometry (Model Family word)
open Research6966

theorem packet {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 9))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 9 ≤ seedDegree G)
    (floor : 308161 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (TransitionPacket.Pair F Crt G SmallCertificates.primary9 SmallCertificates.rescue9) :=
  TransitionPacket.of_normal F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal7.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal7.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal7.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor


theorem packet_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 9))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 9 ≤ seedDegree G)
    (floor : 308161 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ P : TransitionPacket.Pair F Crt G SmallCertificates.primary9 SmallCertificates.rescue9,
      P.mainGrade=335 ∧ P.rescueGrade=319 :=
  TransitionPacket.of_normal_with_grades F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal7.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal7.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal7.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor

end Research6969.NormalPrefixData.Seed9
end Z6969Source0805

-- Source: Research6969.PrefixMainDataHighQuadraticFinal8
section Z6969Source0806
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Lower6960.Prefix6969MainCases.HighQuadraticFinal8
open Lower6960.Prefix6969Main
open Research6969.TransitionBanks
open Research6969.PhysicalCatalogue

def plan : Plan where
  last := 18
  reserve i := ![0, 1, 2, 3, 4, 5, 7, 10, 15, 21, 16, 21, 41, 41, 65, 76, 76, 76, 76] i
  bank i := ![bank2 1529, bank8 1694, bank14 1831, bank23 1898, bank26 2102, bank32 2243, bank44 2409, bank54 2755, bank65 3612, bank84 5564, bank95 3103, bank137 3540, bank121 32187, bank152 6378, bank198 9780, bank183 54742, bank210 11036, bank174 148759, bank169 292467] i
  head := src1196
  introIndices := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  historyValues := [![14455, 169120, 792149, 4094305],
    ![23965/2, 139615, 632198, 3272808],
    ![17372/3, 604934/9, 629864, 3272808],
    ![3599, 161809/4, 2933576/9, 4889248/3],
    ![60658/25, 697372/25, 211251, 1104601],
    ![16211/9, 372263/18, 211251, 1083369],
    ![18775/16, 417285/32, 396682/3, 644809],
    ![89110/121, 970670/121, 4398892/49, 3041520/7],
    ![89110/121, 970670/121, 4398892/49, 3041520/7],
    ![63754/121, 3236432/441, 543881/8, 3041520/7],
    ![63754/121, 3236432/441, 543881/8, 999166/3],
    ![63754/121, 809652/121, 951712/15, 1215872/5],
    ![671521/1681, 809652/121, 951712/15, 1215872/5],
    ![671521/1681, 9684816/1681, 1498848/29, 197156736/841],
    ![671521/1681, 2355184/441, 3530816/75, 10627600/49],
    ![954471/2738, 2355184/441, 3530816/75, 10627600/49],
    ![954471/2738, 7069930/1369, 127258544/2809, 7612081/36],
    ![462882/1369, 7069930/1369, 127258544/2809, 7612081/36],
    ![459151/1369, 7069930/1369, 127258544/2809, 7612081/36]]

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

theorem sources : plan.Sources 2314 (Band.near).last Prefix6969Helper.helperBank 128659 2 10 308107 := by
  refine ⟨?_, rank154 7728, ?_, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ⟨_, cover1196⟩⟩
  · intro i; fin_cases i
    · exact free2_0
    · exact free8_0
    · exact free14_0
    · exact free23_0
    · exact free26_0
    · exact free32_0
    · exact free44_0
    · exact free54_0
    · exact free65_0
    · exact free84_0
    · exact free95_0
    · exact free137_0
    · exact free121_0
    · exact free152_0
    · exact free198_0
    · exact free183_0
    · exact free210_0
    · exact free174_0
    · exact free169_0
  · unfold HelperSource.WidthGuard; decide +kernel

def price : Pricing := ⟨55/100, 90/100, [348183810, 347719013, 347551230, 348141871, 346713063, 347778152, 346748249, 150245683, 150587662, 150705137, 150447865, 80817601, 81784538, 92051024, 104780319, 104820144, 127531580, 174561992, 235765574], [992458, 993732, 994192, 992573, 996490, 993570, 996393, 2563358, 2557671, 2555717, 2559996, 4934517, 4877088, 4312854, 3760045, 3758662, 3053640, 2177736, 1565576],
  ![125149081990680, 1605110064436, 212189016600, 4473467040], 191993281415171292⟩

theorem priced : price.Valid plan Band.near := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_, ?_⟩
  · have hAB : Lower6960.Prefix6969Main.RatesAB price plan := by decide +kernel
    intro i
    exact ⟨(hAB i).1, (hAB i).2, Pricing.height_from_table Band.near price plan [3,3,3,3,3,3,3,7,7,7,7,13,13,12,10,10,9,6,5] (by decide +kernel) i⟩
  · intro k; fin_cases k <;> decide +kernel
  · decide +kernel

theorem final_cap : plan.history plan.last = ![459151/1369, 7069930/1369, 127258544/2809, 7612081/36] := by
  funext k; fin_cases k <;> decide +kernel

end Lower6960.Prefix6969MainCases.HighQuadraticFinal8
end Z6969Source0806

-- Source: Research6969.PhysicalChecks053
section Z6969Source0807
set_option autoImplicit true
namespace Research6969.PhysicalCatalogue
open Research6969.PhysicalWindow.Compact
open PhysicalWindow
set_option maxRecDepth 30000
set_option maxHeartbeats 0

def src520 : Request := ⟨⟨⟨1750,2442,518,115771⟩,158964379549696,962176592398⟩,1,2,1,308048,11⟩
theorem cover520 : PhysicalWindow.Cover (PhysicalWindow.Triangular src520) 2411 2314 [2319, 2337, 2389, 2411] := triangleCover (by decide +kernel)
def src521 : Request := ⟨⟨⟨1750,2442,518,146522⟩,158964379549696,962176592398⟩,3,2,1,308048,11⟩
theorem cover521 : PhysicalWindow.Cover (PhysicalWindow.Triangular src521) 2411 2314 [2317, 2328, 2360, 2411] := triangleCover (by decide +kernel)
def src522 : Request := ⟨⟨⟨2100,2930,622,130242⟩,274699477319680,1994139134137⟩,3,2,1,308048,11⟩
theorem cover522 : PhysicalWindow.Cover (PhysicalWindow.Triangular src522) 2411 2314 [2317, 2328, 2360, 2411] := triangleCover (by decide +kernel)
def src523 : Request := ⟨⟨⟨1750,2442,527,164837⟩,161065121873920,975196209190⟩,4,2,1,308048,11⟩
theorem cover523 : PhysicalWindow.Cover (PhysicalWindow.Triangular src523) 2411 2314 [2318, 2332, 2372, 2411] := triangleCover (by decide +kernel)
def src524 : Request := ⟨⟨⟨2600,3628,783,208621⟩,527755772952576,4745819470168⟩,10,2,1,308048,11⟩
theorem cover524 : PhysicalWindow.Cover (PhysicalWindow.Triangular src524) 2411 2314 [2315, 2321, 2338, 2386, 2411] := triangleCover (by decide +kernel)
def src525 : Request := ⟨⟨⟨3200,4465,963,185441⟩,983050615259136,10877088344236⟩,10,2,1,308048,11⟩
theorem cover525 : PhysicalWindow.Cover (PhysicalWindow.Triangular src525) 2411 2314 [2316, 2324, 2346, 2408, 2411] := triangleCover (by decide +kernel)
def src526 : Request := ⟨⟨⟨3200,4465,963,297039⟩,983050615259136,10877088344236⟩,16,2,1,308048,11⟩
theorem cover526 : PhysicalWindow.Cover (PhysicalWindow.Triangular src526) 2411 2314 [2317, 2329, 2362, 2411] := triangleCover (by decide +kernel)
def src527 : Request := ⟨⟨⟨3950,5512,1169,264035⟩,1824966114017280,24923274283249⟩,16,2,1,308048,11⟩
theorem cover527 : PhysicalWindow.Cover (PhysicalWindow.Triangular src527) 2411 2314 [2317, 2329, 2362, 2411] := triangleCover (by decide +kernel)
def src528 : Request := ⟨⟨⟨4800,6698,1421,297039⟩,3274891856707584,54342858960622⟩,20,2,1,308048,11⟩
theorem cover528 : PhysicalWindow.Cover (PhysicalWindow.Triangular src528) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src529 : Request := ⟨⟨⟨5700,7954,1716,334168⟩,5553838907981824,109473260530676⟩,25,2,1,308048,11⟩
theorem cover529 : PhysicalWindow.Cover (PhysicalWindow.Triangular src529) 2411 2314 [2320, 2339, 2392, 2411] := triangleCover (by decide +kernel)
def src530 : Request := ⟨⟨⟨1750,2442,527,102908⟩,161065121873920,975196209190⟩,0,2,1,308107,10⟩
theorem cover530 : PhysicalWindow.Cover (PhysicalWindow.Triangular src530) 2411 2314 [2317, 2329, 2363, 2411] := triangleCover (by decide +kernel)
def src531 : Request := ⟨⟨⟨1750,2442,527,115771⟩,161065121873920,975196209190⟩,1,2,1,308107,10⟩
theorem cover531 : PhysicalWindow.Cover (PhysicalWindow.Triangular src531) 2411 2314 [2318, 2332, 2372, 2411] := triangleCover (by decide +kernel)
def src532 : Request := ⟨⟨⟨1750,2442,527,130242⟩,161065121873920,975196209190⟩,2,2,1,308107,10⟩
theorem cover532 : PhysicalWindow.Cover (PhysicalWindow.Triangular src532) 2411 2314 [2318, 2332, 2372, 2411] := triangleCover (by decide +kernel)
def src533 : Request := ⟨⟨⟨2100,2930,632,146522⟩,278060332482560,2019119590628⟩,4,2,1,308107,10⟩
theorem cover533 : PhysicalWindow.Cover (PhysicalWindow.Triangular src533) 2411 2314 [2317, 2328, 2359, 2411] := triangleCover (by decide +kernel)
def src534 : Request := ⟨⟨⟨2100,2930,632,185441⟩,278060332482560,2019119590628⟩,6,2,1,308107,10⟩
theorem cover534 : PhysicalWindow.Cover (PhysicalWindow.Triangular src534) 2411 2314 [2317, 2329, 2363, 2411] := triangleCover (by decide +kernel)
def src535 : Request := ⟨⟨⟨2600,3628,783,164837⟩,527755772952576,4745819470168⟩,6,2,1,308107,10⟩
theorem cover535 : PhysicalWindow.Cover (PhysicalWindow.Triangular src535) 2411 2314 [2318, 2332, 2372, 2411] := triangleCover (by decide +kernel)
end Research6969.PhysicalCatalogue
end Z6969Source0807

-- Source: Research6969.PrefixNormalDataSeed10
section Z6969Source0808
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000

namespace Research6969.NormalPrefixData.Seed10
open Lower6960
open Prefix6969Rescue
open TransitionPacket
open PhysicalCatalogue TransitionBanks

def plan : Prefix6969Rescue.Plan where
  count := 11
  positive := by decide
  primeShape := ⟨0,2,1,10⟩
  bank i := ![bank245 102908, bank245 115771, bank245 130242, bank252 146522, bank270 164837, bank252 185441, bank303 208621, bank315 234698, bank315 264035, bank270 334168, bank332 297039] i
  reserve i := ![0, 1, 2, 4, 6, 6, 10, 13, 16, 13, 20] i
  reserve_zero := by decide +kernel
  reserve_small := by intro i; fin_cases i <;> decide +kernel
  prime_fit := by decide
  stage_fit := by intro i; fin_cases i <;> decide +kernel
  initial_small := by intro k; fin_cases k <;> decide +kernel
  degree := 2
  slopeFloor := 1
  physicalFloor := 308107
  seedFloor := 10

theorem sources : plan.Sources 2314 2411 := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact rank245 102908
    · exact rank245 115771
    · exact rank245 130242
    · exact rank252 146522
    · exact rank270 164837
    · exact rank252 185441
    · exact rank303 208621
    · exact rank315 234698
    · exact rank315 264035
    · exact rank270 334168
    · exact rank332 297039
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; fin_cases i <;> decide +kernel
  · intro i; unfold HelperSource.WidthGuard; fin_cases i <;> decide +kernel
  · intro i; fin_cases i
    · exact ⟨_, cover530⟩
    · exact ⟨_, cover531⟩
    · exact ⟨_, cover532⟩
    · exact ⟨_, cover533⟩
    · exact ⟨_, cover535⟩
    · exact ⟨_, cover534⟩
    · exact ⟨_, cover536⟩
    · exact ⟨_, cover538⟩
    · exact ⟨_, cover539⟩
    · exact ⟨_, cover537⟩
    · exact ⟨_, cover540⟩

def price : NormalPrice := ⟨10, 95/100, 80/100, ![2066446164240, 219432614688, 5625286740, 562538500], 19762041271603195⟩
theorem priced : price.Valid plan := by
  refine ⟨by decide, by decide, rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro k; fin_cases k <;> decide +kernel

open Lower6960.Prefix6969MainCases.HighQuadraticFinal8 (plan price valid sources priced) in
def bounds : NormalBounds Lower6960.Prefix6969MainCases.HighQuadraticFinal8.plan Lower6960.Prefix6969MainCases.HighQuadraticFinal8.price
    plan price SmallCertificates.primary10 SmallCertificates.rescue10 where
  main_fee := by decide +kernel
  rescue_fee := by decide +kernel
  mainOrd := rfl
  mainSeed := rfl
  rescueOrd := rfl
  rescueSeed := rfl
  mainMass := by decide +kernel
  rescueMass := by decide +kernel
  mainGrade := 335
  rescueGrade := 315
  mainDegree := by decide +kernel
  rescueDegree := by decide +kernel


open Finset Polynomial
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2 (UsesSeed)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Far6969RescueGeometry (Model Family word)
open Research6966

theorem packet {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 10))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 10 ≤ seedDegree G)
    (floor : 308107 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (TransitionPacket.Pair F Crt G SmallCertificates.primary10 SmallCertificates.rescue10) :=
  TransitionPacket.of_normal F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal8.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal8.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal8.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor


theorem packet_with_grades {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G (graphShape 2 10))
    (known : PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
      (Prefix6969Helper.helperCutoff M.overhead.toNat)) G)
    (degree : 2 ≤ jetDegree G) (seed : 10 ≤ seedDegree G)
    (floor : 308107 ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ P : TransitionPacket.Pair F Crt G SmallCertificates.primary10 SmallCertificates.rescue10,
      P.mainGrade=335 ∧ P.rescueGrade=315 :=
  TransitionPacket.of_normal_with_grades F Crt
    Lower6960.Prefix6969MainCases.HighQuadraticFinal8.valid Lower6960.Prefix6969MainCases.HighQuadraticFinal8.priced Lower6960.Prefix6969MainCases.HighQuadraticFinal8.sources sources priced bounds lo hi noPole residues
    phys prime slope seeded caps known degree seed floor degree seed floor

end Research6969.NormalPrefixData.Seed10
end Z6969Source0808

end Merged_Z6969Pack0632
